open Relation

open Z3
open Z3.Solver
open Z3.Arithmetic
open Z3.Boolean

type event = int

type value = Val of int

let pp_value fmt (Val v) = Format.fprintf fmt "%d" v

type register = Reg of string 

let register_from_id i = Reg (Format.sprintf "s_{%d}" i)

let pp_register fmt (Reg r) = Format.fprintf fmt "%s" r

let fresh_register =
  let reg_id = ref 0 in
  function () ->
    incr reg_id; Reg (Format.sprintf "f_{%d}" !reg_id)

type mem_ref = Ref of string

let pp_mem_ref fmt (Ref x) = Format.fprintf fmt "%s" x

type quiescence = Qui of mem_ref

let pp_quiescence fmt (Qui x) = Format.fprintf fmt "Q(%a)" pp_mem_ref x

type expr = 
  V of value
| R of register
| Add of expr * expr
| Sub of expr * expr
| Mul of expr * expr
| Div of expr * expr
| Eq of expr * expr
| Gt of expr * expr
| Gte of expr * expr
| Lt of expr * expr
| Lte of expr * expr
| Neg of expr

let rec eval_expr env = function
  V (Val v) -> v
| R (Reg r) -> env r
| Add (e1, e2) -> eval_expr env e1 + eval_expr env e2
| Sub (e1, e2) -> eval_expr env e1 - eval_expr env e2
| Mul (e1, e2) -> eval_expr env e1 * eval_expr env e2
| Div (e1, e2) -> eval_expr env e1 / eval_expr env e2
| Eq (e1, e2) -> if eval_expr env e1 = eval_expr env e2 then 1 else 0
| Gt (e1, e2) -> if eval_expr env e1 > eval_expr env e2 then 1 else 0
| Gte (e1, e2) -> if eval_expr env e1 >= eval_expr env e2 then 1 else 0
| Lt (e1, e2) -> if eval_expr env e1 < eval_expr env e2 then 1 else 0
| Lte (e1, e2) -> if eval_expr env e1 <= eval_expr env e2 then 1 else 0
| Neg e -> if eval_expr env e = 0 then 1 else 0

let rec pp_expr fmt = function
  V (Val v) -> Format.fprintf fmt "%d" v
| R (Reg r) -> Format.fprintf fmt "%s" r
| Add (e1, e2) -> Format.fprintf fmt "%a + %a" pp_expr e1 pp_expr e2
| Sub (e1, e2) -> Format.fprintf fmt "%a - %a" pp_expr e1 pp_expr e2
| Mul (e1, e2) -> Format.fprintf fmt "(%a * %a)" pp_expr e1 pp_expr e2
| Div (e1, e2) -> Format.fprintf fmt "(%a / %a)" pp_expr e1 pp_expr e2
| Eq (e1, e2) -> Format.fprintf fmt "(%a = %a)" pp_expr e1 pp_expr e2
| Gt (e1, e2) -> Format.fprintf fmt "(%a > %a)" pp_expr e1 pp_expr e2
| Gte (e1, e2) -> Format.fprintf fmt "(%a >= %a)" pp_expr e1 pp_expr e2
| Lt (e1, e2) -> Format.fprintf fmt "(%a < %a)" pp_expr e1 pp_expr e2
| Lte (e1, e2) -> Format.fprintf fmt "(%a <= %a)" pp_expr e1 pp_expr e2
| Neg e -> Format.fprintf fmt "\\neg (%a)" pp_expr e

let rec expr_map fn = function
  V _ as leaf -> fn leaf
| R _ as leaf -> fn leaf
| Add (l,r) -> Add (expr_map fn l, expr_map fn r)
| Sub (l,r) -> Sub (expr_map fn l, expr_map fn r)
| Mul (l,r) -> Mul (expr_map fn l, expr_map fn r)
| Div (l,r) -> Div (expr_map fn l, expr_map fn r)
| Eq (l,r) -> Eq (expr_map fn l, expr_map fn r)
| Gt (l,r) -> Gt (expr_map fn l, expr_map fn r)
| Gte (l,r) -> Gte (expr_map fn l, expr_map fn r)
| Lt (l,r) -> Lt (expr_map fn l, expr_map fn r)
| Lte (l,r) -> Lte (expr_map fn l, expr_map fn r)
| Neg e -> Neg (expr_map fn e)

let registers_of_expr f =
  let acc = ref [] in
  ignore @@ expr_map (function R r -> acc := r :: !acc; R r | f -> f) f;
  !acc

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

let sub_reg_e e r = 
  expr_map (function
      R r' when r = r' -> e
    | ex -> ex
  )

let sub_reg e r = 
  formula_map (function
      Expr e' -> Expr (sub_reg_e e r e')
    | EqExpr (el, er) -> EqExpr (sub_reg_e e r el, sub_reg_e e r er)
    | EqVar (v, e') -> EqVar (v, sub_reg_e e r e')
    | f -> f
  )

let rec registers_of_formula = function
  Expr e -> registers_of_expr e
| EqExpr (e1, e2) -> registers_of_expr e1 <|> registers_of_expr e2
| EqVar (_, e) -> registers_of_expr e
| Q _ 
| True
| False -> []
| Not f -> registers_of_formula f
| And (f1, f2)
| Or (f1, f2)
| Implies (f1, f2) -> registers_of_formula f1 <|> registers_of_formula f2

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
  | Add (e1, e2) -> 
    let el, rmapl = expr_to_z3 ctx rmap e1 in
    let er, rmapr = expr_to_z3 ctx rmapl e2 in
    mk_add ctx [el; er], rmapr
  | Sub (e1, e2) -> 
    let el, rmapl = expr_to_z3 ctx rmap e1 in
    let er, rmapr = expr_to_z3 ctx rmapl e2 in
    mk_sub ctx [el; er], rmapr
  | Mul (e1, e2) -> 
    let el, rmapl = expr_to_z3 ctx rmap e1 in
    let er, rmapr = expr_to_z3 ctx rmapl e2 in
    mk_mul ctx [el; er], rmapr
  | Div (e1, e2) -> 
    let el, rmapl = expr_to_z3 ctx rmap e1 in
    let er, rmapr = expr_to_z3 ctx rmapl e2 in
    mk_div ctx el er, rmapr
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
  | Neg e ->
    let er, rmap = expr_to_z3 ctx rmap e in
    mk_not ctx er, rmap

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
| Expr (Eq _ as e)
| Expr (Gt _ as e)
| Expr (Gte _ as e)
| Expr (Lt _ as e)
| Expr (Lte _ as e) ->
  expr_to_z3 ctx rmap e
| Expr (Neg e) ->
  let e', rmap' = expr_to_z3 ctx rmap e in
  mk_not ctx e', rmap'
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
| Expr e -> 
  Debug.error "%a\n" pp_expr e;
  raise (Invalid_argument "Bare expr in formula (ryCwKF)")
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
let satisfiable f = not (unsatisfiable f)
