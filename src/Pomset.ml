open Relation
open Util

(** Def 1 - pomset *)
type location = string
type value = int
type label = 
  Write of location * value
| Read of location * value
type event = int
type pomset = {
  evs: event set;
  lab: (event -> label);
  ord: (event, event) relation
}

(* Util *)
module Event_map = Map.Make (struct
  type t = event
  let compare = compare
end)

let is_read ps e =
  match (ps.lab e) with 
    Read _ -> true
  | _ -> false

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
let read_fulfilled ps e =
  assert (is_read ps e);
  List.exists (fun d ->
    List.mem (d, e) ps.ord && matches (ps.lab e) (ps.lab d) &&
    List.for_all (fun c ->
      if (blocks (ps.lab c) (ps.lab e))
      then List.mem (c, d) ps.ord || List.mem (e, c) ps.ord
      else true
    ) ps.evs
  ) ps.evs

(** Def 2 - pomset fulfilled *)
let pomset_fulfilled ps =
  let reads = List.filter (fun e -> match ps.lab e with Read _ -> true | _ -> false) ps.evs in
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
  let lab e =
    if List.mem e p1.evs then p1.lab e
    else if List.mem e p2.evs then p2.lab e
    else raise Not_found
  in
  assert ((p1.evs <&> p2.evs) = []);
  {evs = p1.evs <|> p2.evs; lab = lab; ord = p1.ord <|> p2.ord}

let pomsets_par ps1 ps2 =
  List.map (curry pomset_par) (cross ps1 ps2)

let pomset_prefix action ps = raise (Invalid_argument "aaaa")
