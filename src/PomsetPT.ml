open AST
open Relation
open Util

type value = int
type register = string [@@deriving show]
type location = string [@@deriving show]

type scope = CTA | GPU | SYS
type access_mode = Weak | Relaxed | RA | SC
type fence_mode = Release | Acquire | FSC
                                 
type event = int
type action =
  Write of access_mode * scope * location * value
| Read  of access_mode * scope * location * value
| Fence of fence_mode * scope

type symbol =
  Write_sym
| Downgrade of location
[@@deriving show]
         
type formula =
  EqExpr of expr * expr
| EqVar  of location * expr
| EqReg  of register * expr (* TODO: James does not have this. *)
| Symbol of symbol
| Not of formula
| And of formula * formula
| Or of formula * formula
| True
| False
[@@deriving show]


      
let rec sub_reg e r = function
  | EqReg (r', e') when r = r' -> EqExpr (e,e')
  | Not f -> Not (sub_reg e r f)
  | And (f,f') -> And (sub_reg e r f, sub_reg e r f')
  | Or  (f,f') -> Or  (sub_reg e r f, sub_reg e r f')
  | f -> f

let rec sub_loc e l = function
  | EqVar (l',e') when l = l' -> EqExpr (e,e')
  | Not f -> Not (sub_loc e l f)
  | And (f,f') -> And (sub_loc e l f, sub_loc e l f')
  | Or  (f,f') -> Or  (sub_loc e l f, sub_loc e l f')
  | f -> f

let rec sub_sym phi s = function
  | Symbol s' when s = s' -> phi
  | Not f -> Not (sub_sym phi s f)
  | And (f,f') -> And (sub_sym phi s f, sub_sym phi s f')
  | Or  (f,f') -> Or  (sub_sym phi s f, sub_sym phi s f')
  | f -> f

let rec sub_expr n e = function
    EqExpr (e',x) when e' = e -> EqExpr (n,x)
  | EqExpr (x,e') when e' = e -> EqExpr (x,n)
  | EqVar  (l,e') when e' = e -> EqVar  (l,n)
  | EqReg  (r,e') when e' = e -> EqReg  (r,n)
  | Not f -> Not (sub_expr n e f)
  | And (f,f') -> And (sub_expr n e f, sub_expr n e f')
  | Or  (f,f') -> Or  (sub_expr n e f, sub_expr n e f')
  | f -> f
      
let rec eval_formula = function
    EqExpr (e,e') -> eval_expr empty_env e = eval_expr empty_env e'
  | Not f -> not (eval_formula f)
  | And (f,f') -> (eval_formula f) && (eval_formula f')
  | Or (f,f') -> (eval_formula f) || (eval_formula f')
  | _ -> false

let rec negate = function
    And (f1,f2) -> Or (negate f1, negate f2)
  | Or (f1,f2) -> And (negate f1, negate f2)
  | Not f -> f
  | f -> Not f

let extract_conjunt_clauses = function
  And (f1, f2) -> [f1;f2]
| Or _ -> raise (Invalid_argument "argument not in DNF")
| f -> [f]

let extract_disjunt_clauses = function
  Or (f1, f2) -> [f1;f2]
| And _ -> raise (Invalid_argument "argument not in DNF")
| f -> [f]

let rec convert_cnf = function
    And (f1, f2) -> And (convert_cnf f1, convert_cnf f2)
  | Or (f1, f2) -> 
    let ps = extract_conjunt_clauses (convert_cnf f1) in
    let qs = extract_conjunt_clauses (convert_cnf f2) in
    let ds = List.map (fun (p, q) -> Or (p, q)) (cross ps qs) in
    concat_nonempty (fun p q -> And (p,q)) ds
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
  | Not (And (f1, f2)) -> convert_dnf (Or (Not f1, Not f2))
  | Not (Or (f1, f2)) -> convert_dnf (And (Not f1, Not f2))
  | f -> f


(* Strawman for chat with Simon. *)
let rec eval_entails _f1 _f2 =
  (* TODO: scrub contradictions from dnf? *)
  let rec substitute f2 = function
      And (f,f') -> substitute f' (substitute f f2)
    | True  -> f2
    | False -> True
    | EqVar  (l,e) -> sub_loc  e l f2
    | EqReg  (r,e) -> sub_reg  e r f2
    | EqExpr (n,e) -> sub_expr n e f2            
    | Not _ -> f2 (* TODO: this just drops negated formulae! *)
    | Or _ -> raise (Invalid_argument "argument has Or")
    | Symbol _ -> raise (Invalid_argument "argument has Symbol")
  in
  let rec eval_dnf = function
    Or (f,f') -> (eval_dnf f) && (eval_dnf f')
  | f -> eval_formula (substitute _f2 f)
  in
  eval_dnf (convert_dnf _f1)
