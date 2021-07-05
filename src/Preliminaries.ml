open Z3
open Z3.Solver
open Z3.Arithmetic
open Z3.Boolean

open Util

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

let rec eval_expr env = function
  V (Val v) -> v
| R (Reg r) -> env r
| Eq (e1, e2) -> if eval_expr env e1 = eval_expr env e2 then 1 else 0
| Gt (e1, e2) -> if eval_expr env e1 > eval_expr env e2 then 1 else 0
| Gte (e1, e2) -> if eval_expr env e1 >= eval_expr env e2 then 1 else 0
| Lt (e1, e2) -> if eval_expr env e1 < eval_expr env e2 then 1 else 0
| Lte (e1, e2) -> if eval_expr env e1 <= eval_expr env e2 then 1 else 0

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
| Q q -> Format.fprintf fmt "%a" pp_quiescence q
| True -> Format.fprintf fmt "tt"
| False -> Format.fprintf fmt "ff"

let rec simp_formula f = 
  let go = function
      And (True, f) | And (f, True) -> simp_formula f
    | And (False, _) | And (_, False) -> False
    | And (f1, f2) -> And (simp_formula f1, simp_formula f2)
    | Or (False, f) | Or (f, False) -> simp_formula f
    | Or (True, _) | Or (_, True) -> True
    | Or (f1, f2) -> Or (simp_formula f1, simp_formula f2)
    | Implies (False, _) -> True
    | Implies (True, f) -> simp_formula f
    | Implies (f1, f2) -> Implies (simp_formula f1, simp_formula f2)
    | Not (Not f) -> simp_formula f
    | Not f -> Not (simp_formula f)
    | EqExpr (e1, e2)
    | Expr (Eq (e1, e2)) ->
      begin
        try
          let v1 = eval_expr empty_env e1 in 
          let v2 = eval_expr empty_env e1 in 
          if v1 = v2 then True else False
        with Not_found -> EqExpr (e1, e2)
      end
    | f -> f
  in
  fix go f

let simp_formulae = false
let pp_formula fmt f =
  let f = if simp_formulae then simp_formula f else f in
  pp_formula fmt f

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

let sub_locs e =
  formula_map (function
    | EqVar (_, e') -> EqExpr (e, e')
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

let rec expr_to_z3 ctx rmap = 
  function
    V (Val v) -> Integer.mk_numeral_i ctx v, rmap
  | R (Reg r) -> 
    (
      match List.assoc_opt r rmap with
        Some c -> c, rmap
      | None ->
        let rsym = Symbol.mk_string ctx r in
        let rvar = Integer.mk_const ctx rsym in
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
  let el, rmapl = (
    match List.assoc_opt x rmap with
      Some c -> c, rmap
    | None ->
      let rsym = Symbol.mk_string ctx x in
      let rvar = Integer.mk_const ctx rsym in
      rvar, ((x, rvar) :: rmap)
  ) in
  let er,rmapr = expr_to_z3 ctx rmapl e in
  mk_eq ctx el er, rmapr
| Expr _ -> raise (Invalid_argument "Bare expr in formula (ryCwKF)")
| Q _ -> raise (Invalid_argument "Qx construction in formula (mV4WRJ)")

let valid ctx f =  
  let solver = mk_simple_solver ctx in
  let res = check solver [mk_not ctx f] in
  match res with
  | SATISFIABLE -> false
  | UNSATISFIABLE -> true
  | UNKNOWN -> failwith "can not evaluate formula (H9k5JC)"

let eval_formula f =
  let ctx = mk_context [] in
  let z3f, _rmap = formula_to_z3 ctx [] f in
  valid ctx z3f

let eval_entails f1 f2 = eval_formula (Implies (f1, f2))
let tautology f = eval_entails True f
let unsatisfiable f = eval_entails f False
