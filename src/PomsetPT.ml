open Relation
open Util

type value = int
type register = string [@@deriving show]
type location = string [@@deriving show]

type scope = CTA | GPU | SYS
type access_mode = Weak | Relaxed | RA | SC
type fence_mode = Release | Acquire | FSC
type mode = Amode of access_mode | Fmode of fence_mode
                                    
type event = int
type action =
  Write of access_mode * scope * location * value
| Read of access_mode * scope * location * value
| Fence of fence_mode * scope

type symbol =
  Write_sym
| Downgrade of location
[@@deriving show]
         
type formula =
  EqExpr of AST.expr * AST.expr
| EqVar  of location * AST.expr
| EqReg  of register * AST.expr (* TODO: James does not have this. *)
| Symbol of symbol
| Not of formula
| And of formula * formula
| Or of formula * formula
| True
| False
[@@deriving show]


type transformer = formula -> formula

type pomsetPT = {
    evs:  event set;
    dep:  (event, event) relation;
    hb:   (event, event) relation;
    co:   (event, event) relation;
    lab:  (event, action) environment;
    pre:  (event, formula) environment;
    pt:   event set -> formula -> formula;
    term: formula
  }
                 

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

let rec eval_formula = function
    EqExpr (e,e') -> AST.eval_expr empty_env e = AST.eval_expr empty_env e'
  | Not f -> not (eval_formula f)
  | And (f,f') -> (eval_formula f) && (eval_formula f')
  | Or (f,f') -> (eval_formula f) || (eval_formula f')
  | True -> true
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
let eval_entails f1 f2 =
  (* TODO: scrub contradictions from dnf? *)
  let rec substitute f3 = function
      And (f,f') -> substitute (substitute f3 f) f'
    | EqVar  (l,e) -> sub_loc  e l f3
    | EqReg  (r,e) -> sub_reg  e r f3
    | False -> True
    | True
    | EqExpr _
    | Not _ -> f3 (* TODO: this just drops negated formulae! *)
    | Or _ -> raise (Invalid_argument "argument has Or")
    | Symbol _ -> raise (Invalid_argument "argument has Symbol")
  in
  let rec eval_dnf = function
    Or (f,f') -> (eval_dnf f) && (eval_dnf f')
    | f -> Format.fprintf Format.std_formatter "%a\n" pp_formula (substitute f2 f);
           eval_formula (substitute f2 f)
  in
  eval_dnf (convert_dnf f1)

let mode_order m n = 
  match (m, n) with
    (m,n) when m=n -> true
  | (Amode Weak, _)
  | (Amode Relaxed, Amode RA)
  | (Amode Relaxed, Amode SC)
  | (Amode Relaxed, Fmode _)
  | (Amode RA, Amode SC)
  | (Amode RA, Fmode _)
  | (_, Fmode FSC) -> true
  | _ -> false

let mode_lub m n =
  match (mode_order m n, mode_order n m) with
    (true, false) -> n
  | (false,true)
  | (true, true)  -> m
  | (false,false) -> Fmode FSC

let access_mode_of_mode = function
  Amode m -> m
| _ -> raise (Invalid_argument "cannot get access mode of non access operations")

let fence_mode_of_mode = function
  Fmode m -> m
| _ -> raise (Invalid_argument "cannot get fence mode of non fence operations")

(* 
  Notes:
    why is the type of this 
      action -> action -> action list 
    and not
      action -> action -> action option

    consider defining same_location same_scope and same_value as predicates. Use these anywhere we're doing this guard syntax of "when s=s' && l=l'"
*)
let coalesce a b = 
  match (a, b) with
    (Read  (m, s, l, v), Read  (m', s', l', v')) when s=s' && l=l' && v=v' -> 
     let new_mode = access_mode_of_mode @@ mode_lub (Amode m) (Amode m') in
     [Read (new_mode, s, l, v)]
  | (Write (m, s, l, _v), Write (m', s', l', v')) when s=s' && l=l' ->
     let new_mode = access_mode_of_mode @@ mode_lub (Amode m) (Amode m') in
     [Write (new_mode, s, l, v')]
  | (Fence (m, s), Fence (m', s')) when s=s' -> 
     let new_mode = fence_mode_of_mode @@ mode_lub (Fmode m) (Fmode m') in
     [Fence (new_mode, s)]
  | _ -> []
       
let action_location = function
  Write (_, _, l, _)
| Read (_, _, l, _) -> l
| _ -> raise (Invalid_argument "cannot get location of non load/store actions")

let bowtie_co a1 a2 = 
  match (a1, a2) with
  | Read _, Read _ -> true
  | Read _, Write _
  | Write _, Read _ 
  | Write _, Write _ -> action_location a1 <> action_location a2
  | _ -> false

(*
let bowtie_sync = function
  | (Write m _ _ _, Read  n _ _ _) -> m<>SC || n<>sc
  | (Write _ _ _ _, Write n _ _ _) -> n=Relaxed
  | (Read  m _ _ _, Write n _ _ _) -> m=Relaxed && n=Relaxed
  | (Read  m _ _ _, Read  _ _ _ _) -> m=Relaxed
  | (Fence m _    , Fence n _    ) -> m=Release && n=Acquire
  | (Fence m _    , Read  _ _ _ _) -> m=Release
  | (Write _ _ _ _, Fence n _    ) -> n=Acquire
  | (Read  m _ _ _, Fence n _    ) -> m=Relaxed && n=Acquire (* TODO: Fence X not implemented. *)
  | _ -> false

let bowtie r = bowtie_co r && bowtie_sync r 
                              *)
(*
let refines = function
    ((),())
 *)
