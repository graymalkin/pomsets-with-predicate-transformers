open Relation
open Util

(** Def 1 - pomset *)
type location = string
type value = int
type label = 
  Write of location * value
| Read of location * value
type event = int
type pomset = event set * (event -> label) * (event, event) relation

(* Util *)
module Event_map = Map.Make (struct
  type t = event
  let compare = compare
end)

(** Def 2 - matches *)
let matches a b =
  match (a, b) with 
    (Write (x1, v), Read (x2, w)) -> x1 = x2 && v = w
  | _ -> false

(** Def 2 - blocks *)
let blocks a b =
  match (a, b) with 
    (Write (x1, _), Read (x2, _)) -> x1 = x2
  | _ -> false

(** Def 2 - read fulfilled *)
let read_fulfilled ps ((Read _) as e) =
  let (evs, lab, ord) = ps in
  List.exists (fun d ->
    List.mem (d, e) ord && matches e d &&
    List.for_all (fun c ->
      if (blocks (lab c) (lab e))
      then List.mem (c, d) ord || List.mem (e, c) ord
      else true
    ) evs
  ) evs

(** Def 2 - pomset fulfilled *)
let pomset_fulfilled ps =
  let (evs, lab, _) = ps in
  let reads = List.filter (fun e -> match lab e with Read _ -> true | _ -> false) evs in
  List.for_all (read_fulfilled ps) reads

(** Def 3 - independent events *)
let independent a b = 
  match (a, b) with
    Read _, Read _ -> true
  | Read (x, _), Write (x', _) 
  | Write (x, _), Read (x', _) 
  | Write (x, _), Write (x', _) 
    -> x <> x'


(** Def 4 - pomset compositions *)
let pomset_par p1 p2 =
  let evs1, lab1, ord1 = p1 in
  let evs2, lab2, ord2 = p2 in
  let lab e =
    if List.mem e evs1 then lab1 e
    else if List.mem e evs2 then lab2 e
    else raise Not_found
  in
  let ord = ord1 <|> ord2 in
  assert ((evs1 <&> evs2) = []);
  (evs1 <|> evs2, lab, ord)

let pomsets_par ps1 ps2 =
  List.map (curry pomset_par) (cross ps1 ps2)

let pomset_prefix action ps = raise (Invalid_argument "aaaa")