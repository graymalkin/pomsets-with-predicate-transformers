let convert_expr = function
  AST.Number n -> PomsetPT.V (PomsetPT.Val n)
| AST.Register r -> PomsetPT.R (PomsetPT.Reg r)
| _ -> raise (Invalid_argument "expression construct not supported by PomsetPT (YnNjCW)")

(* TODO: this is probably too limitted even for MVP *)
let convert_bexpr = function
  AST.Equality (e1, e2) -> PomsetPT.Eq (convert_expr e1, convert_expr e2)
| AST.Gt (e1, e2) -> PomsetPT.Gt (convert_expr e1, convert_expr e2)
| AST.Gte (e1, e2) -> PomsetPT.Gte (convert_expr e1, convert_expr e2)
| AST.Lt (e1, e2) -> PomsetPT.Lt (convert_expr e1, convert_expr e2)
| AST.Lte (e1, e2) -> PomsetPT.Lte (convert_expr e1, convert_expr e2)
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
| AST.SC -> PomsetPT.SC
| _ -> raise (Invalid_argument "fence mode not supported by PomsetPT (iZ7QX7)")

(** TODO: Restrict valid ordering annotations for loads/stores/fences to match James' definitions *)
let rec convert_program = function
  AST.Skip ->
  PomsetPT.Skip
| AST.Assign (r, e) ->
  PomsetPT.Assign (PomsetPT.Reg r, convert_expr e)
| AST.Load (r, g, o, _e) ->
  PomsetPT.Load (PomsetPT.Reg r, PomsetPT.Ref g, convert_access_ordering o, PomsetPT.Sys)
| AST.Store (g, e, o, _rmw) ->
  PomsetPT.Store (PomsetPT.Ref g, convert_access_ordering o, PomsetPT.Sys, convert_expr e)
| AST.Fence o -> PomsetPT.FenceStmt (convert_fence_ordering o, PomsetPT.Sys)
| AST.Conditional (be, pt, pf) ->
  PomsetPT.Ite (convert_bexpr be, convert_program pt, convert_program pf)
| AST.Sequence (p1, p2) -> PomsetPT.Sequence (convert_program p1, convert_program p2)
| AST.Parallel (p1, p2) -> PomsetPT.LeftPar (convert_program p1, PomsetPT.Tid 0, convert_program p2)
| AST.Cas (r, g, o1, o2, e1, e2) ->
  PomsetPT.CAS (PomsetPT.Reg r,
    convert_access_ordering o1,
    convert_access_ordering o2,
    PomsetPT.Sys,
    PomsetPT.Ref g,
    convert_expr e1,
    convert_expr e2
  )
| AST.Fadd (r, g, _rmw, o1, o2, e) ->
  PomsetPT.FADD (PomsetPT.Reg r,
    convert_access_ordering o1,
    convert_access_ordering o2,
    PomsetPT.Sys,
    PomsetPT.Ref g,
    convert_expr e
  )
| _ -> raise Util.Not_implemented
