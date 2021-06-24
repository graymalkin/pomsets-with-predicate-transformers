let convert_expr = function
  AST.Number n -> Formula.V (Formula.Val n)
| AST.Register r -> Formula.R (Formula.Reg r)
| _ -> raise (Invalid_argument "expression construct not supported by PomsetPT (YnNjCW)")

(* TODO: this is probably too limitted even for MVP *)
let convert_bexpr = function
  AST.Equality (e1, e2) -> Formula.Eq (convert_expr e1, convert_expr e2)
| AST.Gt (e1, e2) -> Formula.Gt (convert_expr e1, convert_expr e2)
| AST.Gte (e1, e2) -> Formula.Gte (convert_expr e1, convert_expr e2)
| AST.Lt (e1, e2) -> Formula.Lt (convert_expr e1, convert_expr e2)
| AST.Lte (e1, e2) -> Formula.Lte (convert_expr e1, convert_expr e2)
| _ -> raise (Invalid_argument "binary expression not supported by PomsetPT (2Yk1PK)")

let convert_access_ordering = function
  AST.Relaxed -> PomsetPT.Rlx
| AST.Release -> PomsetPT.RA
| AST.Acquire -> PomsetPT.RA
| AST.SC -> PomsetPT.SC
| _ -> raise (Invalid_argument "access mode not supported by PomsetPT (gimne3)")

let convert_fence_ordering = function
  AST.Release -> PomsetPT.Rel
| AST.Acquire -> PomsetPT.Acq
| AST.SC -> PomsetPT.AR
| _ -> raise (Invalid_argument "fence mode not supported by PomsetPT (iZ7QX7)")

(** TODO: Restrict valid ordering annotations for loads/stores/fences to match James' definitions *)
let rec convert_program = function
  AST.Skip ->
  PomsetPT.Skip
| AST.Assign (r, e) ->
  PomsetPT.Assign (Formula.Reg r, convert_expr e)
| AST.Load (r, g, o, _e) ->
  PomsetPT.Load (Formula.Reg r, Formula.Ref g, convert_access_ordering o)
| AST.Store (g, e, o, _rmw) ->
  PomsetPT.Store (Formula.Ref g, convert_access_ordering o, convert_expr e)
| AST.Fence o -> PomsetPT.FenceStmt (convert_fence_ordering o)
| AST.Conditional (be, pt, pf) ->
  PomsetPT.Ite (convert_bexpr be, convert_program pt, convert_program pf)
| AST.Sequence (p1, p2) -> PomsetPT.Sequence (convert_program p1, convert_program p2)
| AST.Parallel (p1, p2) -> PomsetPT.LeftPar (convert_program p1, convert_program p2)
| _ -> raise Util.Not_implemented
