type 'a set = 'a list
[@@deriving show, eq, to_yojson]

type ('a, 'b) env = ('a -> 'b)

type ('a, 'b) edge = ('a * 'b)
[@@deriving show,eq, to_yojson]

type ('a, 'b) relation = (('a, 'b) edge) set
[@@deriving show, eq, to_yojson]

let union a b =
  let ns = List.filter (fun x -> not(List.mem x a)) b in
  a @ ns
let (<|>) = union

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
          
let pp_set pp_a fmt xs =
  if xs = []
  then Format.fprintf fmt (* "∅" *) "\\{\\}"
  else (
    Format.fprintf fmt "\\{";
    let rec inner xs = 
      match xs with
        [] -> failwith "invarient broken"
      | [x] ->
        Format.fprintf fmt "%a" pp_a x
      | (x::xs) ->
        Format.fprintf fmt "%a, " pp_a x;
        inner xs
    in
    inner xs;
    Format.fprintf fmt "\\}"
  )

let pp_edge pp_a pp_b fmt (a, b) = Format.fprintf fmt "(%a, %a)" pp_a a pp_b b

let pp_relation pp_a pp_b fmt xs = pp_set (pp_edge pp_a pp_b) fmt xs

let equal_set eq a b =
  let cmp a b = if eq a b then 0 else 1 in
  List.for_all (fun y -> BatList.mem_cmp cmp y b) a &&
  List.for_all (fun x -> BatList.mem_cmp cmp x a) b

let subset eq a b =
  let cmp a b = if eq a b then 0 else 1 in
  List.for_all (fun y -> BatList.mem_cmp cmp y b) a

let pp_pair pp_a fmt (a, b) =
  Format.fprintf fmt "(%a, %a)" pp_a a pp_a b
   
let pp_list pp_elem fmt xs =
  Format.fprintf fmt "{";
  let rec go = function
      [] -> Format.fprintf fmt "}"
    | [x] -> Format.fprintf fmt "%a}" pp_elem x
    | x::xs ->
       Format.fprintf fmt "%a, " pp_elem x;
       go xs
  in
  go xs

