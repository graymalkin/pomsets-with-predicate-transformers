open Util
open Relation

type value = Val of int
[@@deriving show { with_path = false }]

type register = Reg of string 
[@@deriving show { with_path = false }]

let fresh_register =
  let reg_id = ref 0 in
  function () ->
    incr reg_id; Reg ("s_" ^ (string_of_int !reg_id))

type mem_ref = Ref of string
[@@deriving show { with_path = false }]

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
  | Eq (e1, e2) -> if (eval_expr env e1 = eval_expr env e2) then 1 else 0
  | Gte (e1, e2) -> if (eval_expr env e1 >= eval_expr env e2) then 1 else 0
  | Gt (e1, e2) -> if (eval_expr env e1 > eval_expr env e2) then 1 else 0
  | Lte (e1, e2) -> if (eval_expr env e1 <= eval_expr env e2) then 1 else 0
  | Lt (e1, e2) -> if (eval_expr env e1 < eval_expr env e2) then 1 else 0

type formula =
  Expr of expr
| EqExpr of expr * expr
| EqVar  of mem_ref * expr
| Not of formula
| And of formula * formula
| Or of formula * formula
| Implies of formula * formula
| True
| False
[@@deriving show { with_path = false }]

let rec formula_map fn = function
    Expr _ as leaf -> fn leaf
  | EqExpr _ as leaf -> fn leaf
  | EqVar _ as leaf -> fn leaf
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

let rec eval_formula = function
  | EqExpr (e,e') -> eval_expr empty_env e = eval_expr empty_env e'
  | Expr e -> eval_expr empty_env e <> 0
  | Not f -> not (eval_formula f)
  | And (f,f') -> (eval_formula f) && (eval_formula f')
  | Or (f,f') -> (eval_formula f) || (eval_formula f')
  | True -> true
  | _ -> false

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

(* This is a simple solver that drops quite a bit of information. *)
let eval_entails f1 f2 =
  let rec substitute f3 = function
      And (f,f') -> substitute (substitute f3 f) f'
    | EqVar  (l,e) -> sub_loc  e l f3
    | False -> True
    | True
    | Expr _
    | EqExpr _
    | Not _ -> f3 
    | Or _ -> raise (Invalid_argument "argument has Or (DjytOl)")
    | Implies _ -> raise (Invalid_argument "argument has Implies (vQQNlT)")
  in
  let rec eval_dnf = function
      Or (f,f') -> (eval_dnf f) && (eval_dnf f')
    | f -> eval_formula (substitute f2 f)
  in
  eval_dnf (convert_dnf f1)

