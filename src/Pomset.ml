open AST
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
  lab: (event, label) environment;
  ord: (event, event) relation
}

let empty_pomset = { evs = []; lab = empty_env; ord = [] }

(* Util *)
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
    List.mem (d, e) ps.ord && matches (ps.lab d) (ps.lab e) &&
    List.for_all (fun c ->
      (blocks (ps.lab c) (ps.lab e)) ==> (List.mem (c, d) ps.ord || List.mem (e, c) ps.ord)
    ) ps.evs
  ) ps.evs

(** Def 2 - pomset fulfilled *)
let pomset_fulfilled ps =
  List.for_all (fun e -> is_read ps e ==> read_fulfilled ps e) ps.evs

(** Def 3 - independent events *)
let reorderable a b = 
  match (a, b) with
    Read _, Read _ -> true
  | Read (x, _), Write (x', _) 
  | Write (x, _), Read (x', _) 
  | Write (x, _), Write (x', _) 
    -> x <> x'

let conflict a b = not (reorderable a b)

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
  List.map (uncurry pomset_par) (cross ps1 ps2)

let pomset_prefix action pss =
  List.map (fun ps ->
    let d = fresh_id () in
    let lab' = bind d action ps.lab in
    let ord' = List.fold_right (fun e acc ->
        if reorderable (lab' d) (lab' e) then acc
        else (d, e) :: acc
      ) ps.evs []  
    in
    { evs = ps.evs <|> [d]; lab = lab'; ord = ps.ord <|> ord' }
  ) pss

let rec interp vs = function
  Sequence (Store (g, e, _o, _), ss) ->
  let new_action = Write (g, eval_expr (fun _ -> raise Not_found) e) in
  pomset_prefix new_action (interp vs ss)
| Sequence (Load (_r, g, _o, _), ss) ->
  big_union (List.map (fun v ->
    let new_action = Read (g, v) in
    pomset_prefix new_action (interp vs ss)
  ) vs)
| Parallel (g1, g2) ->
  pomsets_par (interp vs g1) (interp vs g2)
| Skip -> [empty_pomset]
| ast -> 
  Format.fprintf Format.err_formatter "No rules to interpret program:\n%a\n\n" pp_ast ast;
  raise (Invalid_argument "not implemented")

let pp_label fmt = function
  Read (g, v) -> Format.fprintf fmt "R (%s, %d)" g v
| Write (g, v) -> Format.fprintf fmt "W (%s, %d)" g v

let pp_pomset fmt { evs; lab; ord } =
  List.iter (fun e ->
    Format.fprintf fmt "%d: %a\n" e pp_label (lab e)
  ) evs;
  List.iter (fun (a, b) ->
    Format.fprintf fmt "%d -> %d\n" a b
  ) (Relation.transitive_reduction ord)
