(**
  Relational algebra and set theoretic operations on lists
 *)

open Util

type 'a set = 'a list
[@@deriving show, eq]

type ('a, 'b) env = ('a -> 'b)

type ('a, 'b) edge = ('a * 'b)
[@@deriving show,eq]

type ('a, 'b) relation = (('a, 'b) edge) set
[@@deriving show, eq]

include PPRelation


let union a b =
  let ns = List.filter (fun x -> not (List.mem x a)) b in
  a @ ns
let (<|>) = union

let set_of_list xs = List.fold_left (fun acc x -> [x] <|> acc) [] xs

let big_union ss = List.fold_left (<|>) [] ss

let intersect a b =
  List.filter (fun x -> List.mem x a) b
let (<&>) = intersect

let difference a b =
  List.filter (fun x -> not(List.mem x b)) a
let (<->) = difference

let cross x y = BatList.cartesian_product x y

let rec powerset l =
    match l with
    | [] -> [[]]
    | x :: xs ->
      let l = powerset xs in 
      l @ (List.map (fun y -> x :: y) l)

let rm x xs = List.filter ((<>) x) xs

(** For a pair of sets A and B, find all possible ways those sets could overlap.
  A = {1, 2} B = {3, 4}      pairings A B = {{}, {(1, 3)} {(1,3), (2, 4)}, {(2,3)}, {(2,3), (1,4)}}
 *)
let rec pairings a b =
  match a with
    ah :: at -> 
    let possible_links = (ah, None) :: List.map (fun be -> ah, Some be) b in
    List.flatten @@ List.map (fun (al, bl) ->
      match bl with
        Some bl -> List.map (fun r -> (al, bl) :: r) (pairings at (rm bl b)) 
      | None -> pairings at b
    ) possible_links
  | [] -> [[]]

let rel_of_set xs = List.map (fun x -> (x, x)) xs

(* ^? operator, defined as (r ⋃ id) *)
let rel_option d r = rel_of_set d <|> r
let opt = rel_option

(* ; operator *)
let rel_sequence r1 r2 =
  List.fold_right (fun (a, b) acc ->
      let succs = List.fold_right (fun (b', c) acc -> if b = b' then c :: acc  else acc) r2 [] in
      List.map (fun c -> (a, c)) succs @ acc
    ) r1 []
let seq = rel_sequence

(* ^{-1} operator *)
let rel_invert r = List.map (fun (a, b) -> (b, a)) r
let inv = rel_invert

let injective d r =
  List.for_all (fun x ->
    List.length (List.filter (fun (x', _) -> x = x') r) <= 1
  ) d &&
  List.for_all (fun (_, b) ->
    List.length (List.filter (fun (_, b') -> b = b') r) <= 1
  ) r

let surjective cd r = 
  List.for_all (fun x ->
    List.exists (fun (_, x') -> x = x') r
  ) cd

let bijection d cd r = injective d r && surjective cd r

let subset eq a b =
  let cmp a b = if eq a b then 0 else 1 in
  List.for_all (fun y -> BatList.mem_cmp cmp y b) a

let equal_set eq a b = subset eq a b && subset eq b a

let reflexive d r = subset (=) (rel_of_set d) r

let antisymmetric r =
  List.for_all (fun (a, b) ->
    (List.mem (b, a) r) ==> (a = b)
  ) r

let transitive r =
  List.for_all (fun (a, b) ->
    List.for_all (fun (b', c) ->
      b = b' ==> List.mem (a, c) r
    ) r
  ) r

let total d r =
  List.for_all (fun a ->
    List.for_all (fun b ->
      List.mem (a, b) r || List.mem (b, a) r
    ) d
  ) d

let domain r = List.fold_left (fun acc (a, _) -> a :: acc) [] r
let codomain r = List.fold_left (fun acc (_, b) -> b :: acc) [] r
let field r = domain r <|> codomain r

(** Note: this definition extracts the field from the relation and does not require id inclusion *)
let partial_order r = reflexive (field r) r && antisymmetric r && transitive r

let total_order d r  = partial_order r && total d r

module EventGraph = Graph.Imperative.Digraph.Concrete(struct
  include Int 
  let hash = Hashtbl.hash
end)
module EventGraphOps = Graph.Oper.Make(Graph.Builder.I(EventGraph))

let edges_to_graph edges = 
  let g = EventGraph.create () in
  let _ = List.rev_map (fun (l, r) -> EventGraph.add_edge g l r) edges in
  g

let graph_to_edges g = EventGraph.fold_edges (fun l r acc -> (l, r)::acc) g []

let transitive_reduction edges =
  edges_to_graph edges |> EventGraphOps.transitive_reduction |> graph_to_edges

let transitive_closure ?refl:(r=false) edges =
  edges_to_graph edges |> EventGraphOps.transitive_closure ~reflexive:r |> graph_to_edges

let tc r = transitive_closure ~refl:false r
let rtc d r = transitive_closure ~refl:true r <|> rel_of_set d

let irreflexive r = not (List.exists (fun (a, b) -> a = b) r)
let acyclic r = irreflexive (tc r)

