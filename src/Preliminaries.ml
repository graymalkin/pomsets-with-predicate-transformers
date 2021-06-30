open Util
open Relation

type event = int

type value = Val of int
[@@deriving show { with_path = false }]

let pp_value fmt (Val v) = Format.fprintf fmt "%d" v

type register = Reg of string 
[@@deriving show { with_path = false }]

let pp_register fmt (Reg r) = Format.fprintf fmt "%s" r

let fresh_register =
  let reg_id = ref 0 in
  function () ->
    incr reg_id; Reg ("s_" ^ (string_of_int !reg_id))

type mem_ref = Ref of string
[@@deriving show { with_path = false }]

let pp_mem_ref fmt (Ref x) = Format.fprintf fmt "%s" x

type quiescence = Qui of mem_ref
[@@deriving show { with_path = false }]

let pp_quiescence fmt (Qui x) = Format.fprintf fmt "Q(%a)" pp_mem_ref x

type expr = 
  V of value
| R of register
| Eq of expr * expr
| Gt of expr * expr
| Gte of expr * expr
| Lt of expr * expr
| Lte of expr * expr
[@@deriving show { with_path = false }]

let rec pp_expr fmt = function
  V (Val v) -> Format.fprintf fmt "%d" v
| R (Reg r) -> Format.fprintf fmt "%s" r
| Eq (e1, e2) -> Format.fprintf fmt "(%a = %a)" pp_expr e1 pp_expr e2
| Gt (e1, e2) -> Format.fprintf fmt "(%a > %a)" pp_expr e1 pp_expr e2
| Gte (e1, e2) -> Format.fprintf fmt "(%a >= %a)" pp_expr e1 pp_expr e2
| Lt (e1, e2) -> Format.fprintf fmt "(%a < %a)" pp_expr e1 pp_expr e2
| Lte (e1, e2) -> Format.fprintf fmt "(%a <= %a)" pp_expr e1 pp_expr e2

type formula =
  Expr of expr
| EqExpr of expr * expr
| EqVar  of mem_ref * expr
| Not of formula
| And of formula * formula
| Or of formula * formula
| Implies of formula * formula
| Q of quiescence
| True
| False
[@@deriving show { with_path = false }]

let rec pp_formula fmt = function
  Expr e -> Format.fprintf fmt "%a" pp_expr e
| EqExpr (e1, e2) -> Format.fprintf fmt "(%a = %a)" pp_expr e1 pp_expr e2
| EqVar (x, e) -> Format.fprintf fmt "(%a = %a)" pp_mem_ref x pp_expr e
| Not f -> Format.fprintf fmt "~%a" pp_formula f
| And (f1, f2) -> Format.fprintf fmt "(%a) && (%a)" pp_formula f1 pp_formula f2
| Or (f1, f2) -> Format.fprintf fmt "(%a || %a)" pp_formula f1 pp_formula f2
| Implies (f1, f2) -> Format.fprintf fmt "(%a ==> %a)" pp_formula f1 pp_formula f2
| Q q -> Format.fprintf fmt "Q(%a)" pp_quiescence q
| True -> Format.fprintf fmt "tt"
| False -> Format.fprintf fmt "ff"


let rec formula_map fn = function
    Expr _ as leaf -> fn leaf
  | EqExpr _ as leaf -> fn leaf
  | EqVar _ as leaf -> fn leaf
  | Q _ as leaf -> fn leaf
  | True as leaf -> fn leaf
  | False as leaf -> fn leaf
  | Not f -> Not (formula_map fn f)
  | And (f1, f2) -> And (formula_map fn f1, formula_map fn f2)
  | Or (f1, f2) -> Or (formula_map fn f1, formula_map fn f2)
  | Implies (f1, f2) -> Implies (formula_map fn f1, formula_map fn f2)

(* TODO: examine implementation *)
let sub_reg e r = 
  formula_map (function
    | EqExpr (R r', e') when r = r' -> EqExpr (e,e')
    | f -> f
  )

let sub_loc e l =
  formula_map (function
    | EqVar (l',e') when l = l' -> EqExpr (e,e')
    | f -> f
  )

let sub_qui phi q =
  formula_map (function
    | Q q' when q = q' -> phi
    | f -> f
  )

let sub_quis phi =
  formula_map (function
    | Q _ -> phi
    | f -> f
  )

open Z3
open Z3.Solver
open Z3.Arithmetic
open Z3.Boolean

let rec expr_to_z3 ctx rmap = 
  function
    V (Val v) -> Integer.mk_numeral_i ctx v, rmap
  | R (Reg r) -> 
    (
      match List.assoc_opt r rmap with
        Some c -> c, rmap
      | None ->
        let rvar = Integer.mk_const_s ctx r in
        rvar, ((r, rvar) :: rmap)
    )
  | Eq (e1, e2) -> 
    let el, rmapl = expr_to_z3 ctx rmap e1 in
    let er, rmapr = expr_to_z3 ctx rmapl e2 in
    mk_eq ctx el er, rmapr
  | Gt (e1,e2) ->  
    let el, rmapl = expr_to_z3 ctx rmap e1 in
    let er, rmapr = expr_to_z3 ctx rmapl e2 in
    mk_gt ctx el er, rmapr
  | Gte (e1,e2) -> 
    let el, rmapl = expr_to_z3 ctx rmap e1 in
    let er, rmapr = expr_to_z3 ctx rmapl e2 in
    mk_ge ctx el er, rmapr
  | Lt (e1,e2) -> 
    let el, rmapl = expr_to_z3 ctx rmap e1 in
    let er, rmapr = expr_to_z3 ctx rmapl e2 in
    mk_lt ctx el er, rmapr
  | Lte (e1,e2) -> 
    let el, rmapl = expr_to_z3 ctx rmap e1 in
    let er, rmapr = expr_to_z3 ctx rmapl e2 in
    mk_le ctx el er, rmapr

let rec formula_to_z3 ctx rmap = function
  And (f1, f2) -> 
    let l, rmapl = formula_to_z3 ctx rmap f1 in
    let r, rmapr = formula_to_z3 ctx rmapl f2 in
    mk_and ctx [l; r], rmapr
| Or (f1, f2) -> 
    let l, rmapl = formula_to_z3 ctx rmap f1 in
    let r, rmapr = formula_to_z3 ctx rmapl f2 in
    mk_or ctx [l; r], rmapr
| Implies (f1, f2) -> 
    let l, rmapl = formula_to_z3 ctx rmap f1 in
    let r, rmapr = formula_to_z3 ctx rmapl f2 in
    mk_implies ctx l r, rmapr
| Expr (Eq (e1, e2))
| EqExpr (e1, e2) -> 
  let el, rmapl = expr_to_z3 ctx rmap e1 in
  let er, rmapr = expr_to_z3 ctx rmapl e2 in
  mk_eq ctx el er, rmapr
| True -> mk_true ctx, rmap
| False -> mk_false ctx, rmap
| Not f -> 
  let fr, rmapf = formula_to_z3 ctx rmap f in
  mk_not ctx fr, rmapf
| EqVar (Ref x, e) -> 
  (
      match List.assoc_opt x rmap with
        Some c -> c, rmap
      | None ->
        let rvar = Integer.mk_const_s ctx x in
        let ef,rmapr = expr_to_z3 ctx rmap e in
        mk_eq ctx rvar ef, ((x, rvar) :: rmapr)
  )
| Expr _ -> raise (Invalid_argument "Bare expr in formula (ryCwKF)")
| Q _ -> raise (Invalid_argument "Qx construction in formula (mV4WRJ)")

let valid ctx consts f =  
  let solver = mk_simple_solver ctx in
  let res = check solver (consts :: [mk_not ctx f])in
  match res with
  | SATISFIABLE -> false
  | UNSATISFIABLE -> true
  | UNKNOWN -> failwith "can not evaluate formula (H9k5JC)"

let eval_formula f =
  let ctx = mk_context [] in
  let z3f, rmap = formula_to_z3 ctx [] f in
  let consts = List.map snd rmap in
  valid ctx (mk_distinct ctx consts) z3f

let rec negate = function
    Not f -> f
  | And (f1,f2) -> Or (negate f1, negate f2)
  | Or (f1,f2) -> And (negate f1, negate f2)
  | Implies (f1, f2) -> And (f1, Not f2)
  | f -> Not f

let extract_conjunt_clauses = function
    And (f1, f2) -> [f1;f2]
  | Or _ -> raise (Invalid_argument "argument not in CNF (X4jLx0)")
  | f -> [f]

let extract_disjunt_clauses = function
    Or (f1, f2) -> [f1;f2]
  | And _ -> raise (Invalid_argument "argument not in DNF (Od97c0)")
  | f -> [f]

let rec convert_cnf = function
    And (f1, f2) -> And (convert_cnf f1, convert_cnf f2)
  | Or (f1, f2) -> 
    let ps = extract_conjunt_clauses (convert_cnf f1) in
    let qs = extract_conjunt_clauses (convert_cnf f2) in
    let ds = List.map (fun (p, q) -> Or (p, q)) (cross ps qs) in
    concat_nonempty (fun p q -> And (p,q)) ds
  | Implies (f1, f2) -> convert_cnf (Or (Not f1, f2))
  | Not (And (f1, f2)) -> convert_cnf (Or (Not f1, Not f2))
  | Not (Or (f1, f2)) -> convert_cnf (And (Not f1, Not f2))
  | f -> f

let rec convert_dnf = function
    Or (f1, f2) -> Or (convert_dnf f1, convert_dnf f2)
  | And (f1, f2) -> 
    let ps = extract_disjunt_clauses (convert_dnf f1) in
    let qs = extract_disjunt_clauses (convert_dnf f2) in
    let cs = List.map (fun (p,q) -> And (p, q)) (cross ps qs) in
    concat_nonempty (fun a b -> Or (a, b)) cs
  | Implies (f1, f2) -> convert_dnf (Or (Not f1, f2))
  | Not (And (f1, f2)) -> convert_dnf (Or (Not f1, Not f2))
  | Not (Or (f1, f2)) -> convert_dnf (And (Not f1, Not f2))
  | f -> f

exception Undecidable_formula of string

(* This is a simple solver that drops quite a bit of information. *)
(* f1 |= f2 *)
let eval_entails f1 f2 =
  let rec substitute f3 = function
      And (f,f') -> substitute (substitute f3 f) f'
    | EqVar  (l,e) -> sub_loc  e l f3
    | EqExpr (V v1, V v2) -> if v1 = v2 then f3 else True
    | EqExpr (V v, R r)
    | EqExpr (R r, V v) -> sub_reg (V v) r f3
    | False -> True
    | True -> f3
    | Not _ -> raise Not_implemented
    | EqExpr _ -> raise Not_implemented
    | Q _ -> raise (Undecidable_formula "formula contains Qx construciton (Bxmq05)")
    | Expr _ -> raise (Invalid_argument "bare expression in formula (x9zEsN)")
    | Or _ -> raise (Invalid_argument "argument has Or (DjytOl)")
    | Implies _ -> raise (Invalid_argument "argument has Implies (vQQNlT)")
  in
  let rec eval_dnf = function
      Or (f,f') -> (eval_dnf f) && (eval_dnf f')
    | f -> eval_formula (substitute f2 f)
  in
  eval_dnf (convert_dnf f1)

let tautology f = eval_entails True f
let unsatisfiable f = eval_entails f False
