open AST
open PomsetPT

open Util

let convert_expr = function
  Number n -> V (Val n)
| Register r -> R (Reg r)
| _ -> raise (Invalid_argument "expression construct not supported by PomsetPT (YnNjCW)")

(* TODO: this is probably too limitted even for MVP *)
let convert_bexpr = function
  Equality (e, Number 0) -> convert_expr e
| _ -> raise (Invalid_argument "only equality to 0 supported in boolean expressions (2Yk1PK)")

let convert_access_ordering = function
  AST.Relaxed -> PomsetPT.Rlx
| AST.Release -> PomsetPT.RA
| AST.Acquire -> PomsetPT.RA
| AST.SC -> PomsetPT.SC
| _ -> raise (Invalid_argument "access mode not supported by PomsetPT (gimne3)")

let convert_fence_ordering = function
  AST.Release -> PomsetPT.Rel
| AST.Acquire -> PomsetPT.Acq
| AST.SC ->
  warn "SC fence converted to AR fence for use in PomsetPT\n";
  PomsetPT.AR
| _ -> raise (Invalid_argument "fence mode not supported by PomsetPT (iZ7QX7)")

let rec convert_program = function
  AST.Skip -> PomsetPT.Skip
| AST.Assign (r, e) -> PomsetPT.Assign (Reg r, convert_expr e)
| AST.Load (r, g, o, _e) -> PomsetPT.Load (Reg r, Ref g, convert_access_ordering o, Sys)
| AST.Store (g, e, o, _rmw) -> PomsetPT.Store (Ref g, convert_access_ordering o, Sys, convert_expr e)
| AST.Fence o -> PomsetPT.FenceStmt (convert_fence_ordering o, Sys)
| AST.Conditional (be, pt, pf) -> PomsetPT.Ite (convert_bexpr be, convert_program pt, convert_program pf)
| AST.Sequence (p1, p2) -> PomsetPT.Sequence (convert_program p1, convert_program p2)
| AST.Parallel (p1, p2) -> PomsetPT.LeftPar (convert_program p1, Tid 0, convert_program p2)
| AST.Cas (r, g, o1, o2, e1, e2) -> PomsetPT.CAS (Reg r, convert_access_ordering o1, convert_access_ordering o2, Sys, Ref g, convert_expr e1, convert_expr e2)
| AST.Fadd (r, g, _rmw, o1, o2, e) -> PomsetPT.FADD (Reg r, convert_access_ordering o1, convert_access_ordering o2, Sys, Ref g, convert_expr e)
| _ -> failwith "panic"
