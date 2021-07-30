module Pre = Preliminaries
module P = PomsetPTSeq

let rec convert_expr = function
  AST.Number n -> Pre.V (Pre.Val n)
| AST.Register r -> Pre.R (Pre.Reg r)
| AST.Addition (e1, e2) -> Pre.Add (convert_expr e1, convert_expr e2)
| AST.Subtraction (e1, e2) -> Pre.Sub (convert_expr e1, convert_expr e2)
| AST.Multiplication (e1, e2) -> Pre.Mul (convert_expr e1, convert_expr e2)
| AST.Division (e1, e2) -> Pre.Div (convert_expr e1, convert_expr e2)

let rec convert_bexpr = function
  AST.Equality (e1, e2) -> Pre.Eq (convert_expr e1, convert_expr e2)
| AST.Gt (e1, e2) -> Pre.Gt (convert_expr e1, convert_expr e2)
| AST.Gte (e1, e2) -> Pre.Gte (convert_expr e1, convert_expr e2)
| AST.Lt (e1, e2) -> Pre.Lt (convert_expr e1, convert_expr e2)
| AST.Lte (e1, e2) -> Pre.Lte (convert_expr e1, convert_expr e2)
| AST.Negation e -> Pre.Neg (convert_bexpr e)
| _ -> raise (Invalid_argument "binary expression not supported by P (2Yk1PK)")

let convert_access_ordering = function
  AST.Relaxed -> P.Rlx
| AST.Release -> P.Rel
| AST.Acquire -> P.Acq
| AST.SC -> P.SC
| _ -> raise (Invalid_argument "access mode not supported by P (gimne3)")

let convert_fence_ordering = function
  AST.Release -> P.Rel
| AST.Acquire -> P.Acq
| AST.SC -> P.SC
| _ -> raise (Invalid_argument "fence mode not supported by P (iZ7QX7)")

(** TODO: Restrict valid ordering annotations for loads/stores/fences to match James' definitions *)
let rec convert_program = function
  AST.Skip ->
  P.Skip
| AST.Assign (r, e) ->
  P.Assign (Pre.Reg r, convert_expr e)
| AST.Load (r, g, o, _e) ->
  P.Load (Pre.Reg r, Pre.Ref g, convert_access_ordering o)
| AST.Store (g, e, o, _rmw) ->
  P.Store (Pre.Ref g, convert_access_ordering o, convert_expr e)
| AST.Conditional (be, pt, pf) ->
  P.Ite (convert_bexpr be, convert_program pt, convert_program pf)
| AST.Sequence (p1, p2) -> P.Sequence (convert_program p1, convert_program p2)
| AST.Parallel (p1, p2) -> P.Par (convert_program p1, convert_program p2)
| _ -> raise Util.Not_implemented
