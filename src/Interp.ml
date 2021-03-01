open AST
open Pomset

let interp ps = function
  Store (g, e, _, _) ->
  let new_action = Write (g, eval_expr (fun _ -> raise Not_found) e) in
  pomset_prefix new_action ps
| _ -> raise (Invalid_argument "not implemented")
