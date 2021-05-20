open Util

type 'a set = 'a list
[@@deriving show, eq]

type ('a, 'b) env = ('a -> 'b)

type ('a, 'b) edge = ('a * 'b)
[@@deriving show,eq]

type ('a, 'b) relation = (('a, 'b) edge) set
[@@deriving show, eq]

let union a b =
  let ns = List.filter (fun x -> not(List.mem x a)) b in
  a @ ns
let (<|>) = union

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

let rel_option d r = rel_of_set d <|> r
let opt = rel_option

let rel_sequence r1 r2 =
  List.fold_right (fun (a, b) acc ->
      let succs = List.fold_right (fun (b', c) acc -> if b = b' then c :: acc  else acc) r2 [] in
      List.map (fun c -> (a, c)) succs @ acc
    ) r1 []
let seq = rel_sequence

let rel_invert r = List.map (fun (a, b) -> (b, a)) r
let inv = rel_invert

let injective d r =
  List.for_all (fun x ->
    List.length (List.filter (fun (x', _) -> x = x') r) = 1
  ) d

let surjective d r = 
  List.for_all (fun x ->
    List.exists (fun (x', _) -> x = x') r
  ) d

let bijection d r = injective d r && surjective d r

let subset eq a b =
  let cmp a b = if eq a b then 0 else 1 in
  List.for_all (fun y -> BatList.mem_cmp cmp y b) a

let equal_set eq a b = subset eq a b && subset eq b a

let reflexive d r = subset (=) r (rel_of_set d)

let antisymmetric r =
  List.for_all (fun (a, b) ->
    List.mem (b, a) r ==> a = b
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

let partial_order d r = reflexive d r && antisymmetric r && transitive r
let total_order d r  = partial_order d r && total d r

open Graph
module EventGraph = Imperative.Digraph.Concrete(struct
  type t = int
  let compare = Stdlib.compare
  let hash = Hashtbl.hash
  let equal = (=)
end)
module EventGraphBuilder = Builder.I(EventGraph)
module EventGraphOps = Oper.Make(EventGraphBuilder)

let transitive_reduction edges =
  let g = EventGraph.create () in
  let _ = List.rev_map (fun (l, r) -> EventGraph.add_edge g l r) edges in
  let g = EventGraphOps.transitive_reduction g in
  EventGraph.fold_edges (fun l r acc -> (l, r)::acc) g []

let transitive_closure ?reflexive:(refl=false) (edges: (int, int) relation) : (int, int) relation =
  let g = EventGraph.create () in
  let _ = List.rev_map (fun (l, r) -> EventGraph.add_edge g l r) edges in
  let g = EventGraphOps.transitive_closure ~reflexive:refl g in
  EventGraph.fold_edges (fun l r acc -> ((l: 'a), (r: 'b))::acc) g []

let tc r = transitive_closure ~reflexive:false r
let rtc d r = transitive_closure ~reflexive:true r <|> rel_of_set d

let irreflexive r = not (List.exists (fun (a, b) -> a = b) r)
let acyclic r = irreflexive (tc r)

