open Relation
open Util

type value = Val of int [@@deriving show]
type register = Reg of string [@@deriving show]
type thread_id = Tid of int [@@deriving show]
type mem_ref = Ref of string [@@deriving show]

type access_mode = Wk | Rlx | RA | SC [@@deriving show]
type fence_mode = Acq | Rel | AR [@@deriving show]
type scope = Grp | Proc | Sys [@@deriving show]
type mode = Amode of access_mode | Fmode of fence_mode [@@deriving show]

type expr = 
  V of value
| R of register
[@@deriving show]

let eval_expr env = function
    V (Val v) -> v
  | R (Reg r) -> env r

type grammar = 
  Skip
| Assign of register * expr
| Load of register * mem_ref * access_mode * scope
| Store of mem_ref * access_mode * scope * expr
| FenceStmt of fence_mode * scope
| Ite of expr * grammar * grammar
| Sequence of grammar * grammar
| LeftPar of grammar * thread_id * grammar
| CAS of register * access_mode * access_mode * scope * mem_ref * expr * expr
| FADD of register * access_mode * access_mode * scope * mem_ref * expr
| EXCHG of register * access_mode * access_mode * scope * mem_ref * expr
[@@deriving show]

type event = int

type symbol =
  Write_sym
| Downgrade of mem_ref
[@@deriving show]
         
type formula =
  Expr of expr
| EqExpr of expr * expr
| EqVar  of mem_ref * expr
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

let rec eval_formula = function
  | EqExpr (e,e') -> eval_expr empty_env e = eval_expr empty_env e'
  | Expr e -> eval_expr empty_env e <> 0
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
  | Or _ -> raise (Invalid_argument "argument not in DNF (X4jLx0)")
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

(* This is a simple solver that drops quite a bit of information. *)
let eval_entails f1 f2 =
  let rec substitute f3 = function
      And (f,f') -> substitute (substitute f3 f) f'
    | EqVar  (l,e) -> sub_loc  e l f3
    | EqReg  (r,e) -> sub_reg  e r f3
    | False -> True
    | True
    | Expr _
    | EqExpr _
    | Not _ -> f3 
    | Or _ -> raise (Invalid_argument "argument has Or (DjytOl)")
    | Symbol _ -> raise (Invalid_argument "argument has Symbol (8z6kkd)")
  in
  let rec eval_dnf = function
    Or (f,f') -> (eval_dnf f) && (eval_dnf f')
    | f -> eval_formula (substitute f2 f)
  in
  eval_dnf (convert_dnf f1)

let access_mode_order m n = 
  match (m, n) with
    (m,n) when m=n -> true
  | (Wk, _)
  | (_, SC)
  | (Rlx, RA) -> true
  | _ -> false

let fence_mode_order m n = 
  match (m, n) with
    (m,n) when m=n -> true
  | (_, AR) -> true
  | _ -> false

let mode_order m n = 
  match (m, n) with
    (Amode x, Amode y) -> access_mode_order x y
  | (Fmode x, Fmode y) -> fence_mode_order x y
  | _ -> false

let lub f m n =
  match (f m n, f n m) with
    (true, false) -> Some n
  | (false,true)
  | (true, true)  -> Some m
  | (false,false) -> None

let mode_lub = lub mode_order
let access_mode_lub m n = Option.get @@ lub access_mode_order m n
let fence_mode_lub m n = Option.get @@ lub fence_mode_order m n

let access_mode_of_mode = function
  Amode m -> m
| _ -> raise (Invalid_argument "cannot get access mode of non access operations (AwlomK)")

let fence_mode_of_mode = function
  Fmode m -> m
| _ -> raise (Invalid_argument "cannot get fence mode of non fence operations (5OFcpC)")

type action =
  Write of thread_id * access_mode * scope * mem_ref * value
| Read of thread_id * access_mode * scope * mem_ref * value
| Fence of thread_id * fence_mode * scope

let tid_of = function
    Read (t, _, _, _, _)
  | Write (t, _, _, _, _)
  | Fence (t, _, _) -> t

let mode_of = function
    Write (_,m,_,_,_)
  | Read (_,m,_,_,_) -> Amode m
  | Fence (_,m,_) -> Fmode m

let scope_of = function
    Read (_, _, s, _, _)
  | Write (_, _, s, _, _)
  | Fence (_, _, s) -> s

let mem_ref_of = function
    Write (_,_,_,x,_)
  | Read (_,_,_,x,_) -> Some x
  | Fence _ -> None

let is_access = function Read _ | Write _ -> true | Fence _ -> false
let is_read   = function Read _ -> true | _ -> false

let matches a b =
  match (a,b) with
    Write (_,_,_,x,v), Read (_,_,_,x',v') -> x = x' && v = v' 
  | _ -> false

let blocks a b =
  match (a,b) with
    Write (_,_,_,x,_), Read (_,_,_,x',_) -> x = x'
  | _ -> false

let overlaps a b =
  match (mem_ref_of a, mem_ref_of b) with
    Some x, Some x' -> x = x'
  | _ -> false
       
let coherence_delays a b =
  match (a, b) with
    Write _, Write _
  | Read  _, Write _
  | Write _, Read  _ -> 
      mem_ref_of a = mem_ref_of b || (mode_of a = Amode SC && mode_of b = Amode SC)
  | Read  (_,SC,_,_,_), Read (_,SC,_,_,_) -> true
  | _ -> false

let synchronisation_delays a b =
  match (a, b) with
    _, Write (_,m,_,_,_) when access_mode_order RA m -> true
  | _, Fence (_,m,_) when fence_mode_order Rel m -> true
  | Read _, Fence (_,m,_) when fence_mode_order Acq m -> true
  | Read _, Read (_,m,_,_,_) when access_mode_order RA m && mem_ref_of a = mem_ref_of b -> true
  | Read (_,m,_,_,_), _ when access_mode_order RA m -> true
  | Fence (_,m,_),_ when fence_mode_order Acq m -> true
  | Fence (_,m,_), Write _ when fence_mode_order Rel m -> true
  | Write (_,m,_,_,_), Write _ when access_mode_order RA m && mem_ref_of a = mem_ref_of b -> true
  | _ -> false

let is_release = function
    Write (_,m,_,_,_) -> access_mode_order RA m
  | Fence (_,m,_) -> fence_mode_order Rel m
  | _ -> false

let merge a b =
  match (a, b) with
    Read (tid,m,s,x,v), Read (_,m',_,x',v') when x = x' && v = v' -> [Read (tid,access_mode_lub m m',s,x,v)]
  | Write (tid,m,s,x,_), Write (_,m',_,x',w) when x = x' -> [Write (tid,access_mode_lub m m',s,x,w)]
  | Write (tid,m,s,x,v), Read (_,Rlx,_,x',v') when x = x' && v = v' -> [Write (tid,m,s,x,v)]
  | Fence (tid,m,s), Fence(_,m',_) -> [Fence (tid,fence_mode_lub m m',s)]
  | _ -> []

(** Definition 1.1 *)
let imm_strongly_blocks _ _ = true (* TODO: investigate last email from James. *)

let imm_strongly_matches a b = overlaps a b && mode_of a <> Amode Rlx && mode_of b <> Amode Rlx

(** Definition 1.2 *)
let ptx_strongly_blocks eq_proc eq_grp a b =
  tid_of a = tid_of b
  || (
    mode_of a <> Amode Wk && mode_of b <> Amode Wk   (* 2a *)
    && (scope_of a = Grp || scope_of b = Grp) ==> eq_grp a b (* 2b *)
    && (scope_of a = Proc || scope_of b = Proc) ==> eq_proc a b (* 2c *)
    && (is_access a || is_access b) ==> overlaps a b (* 2d *)
  )

let ptx_strongly_matches = ptx_strongly_blocks

(** Definition 1.3 *)
type transformer = formula -> formula

(* Definition M1-M9 *)
type pomsetPT = {
  evs:  event set;                          (* M1 *)
  lab:  (event, action) environment;        (* M2 *)
  pre:  (event, formula) environment;       (* M3 *)
  
  (* TODO: definition 1.4 restricts these in a way that we cannot 
           implement because it universally quantifies formulae. *)
  pt:   event set -> transformer;           (* M4 *)
  
  term: formula;                            (* M5 *)
  dep:  (event, event) relation;            (* M6 *)
  hb:   (event, event) relation;            (* M7 *)
  psc:   (event, event) relation;           (* M8 *)
  rmw:  (event, event) relation;            (* M9 *)
}

(* M8a *)
let wf_psc p =
  List.iter (fun (d, e) ->
    if overlaps (p.lab d) (p.lab e)
    then assert (List.mem (d,e) p.psc)
  ) p.hb
  
let wf_rmw p =
  List.iter (fun (d, e) ->
    assert (blocks (p.lab d) (p.lab e)); (* M9a *)
    assert (List.mem (d, e) p.dep && List.mem (d, e) p.psc); (* M9b *)
    List.iter (fun c ->
      if overlaps (p.lab c) (p.lab d)
      then (
        (* M9c i *)
        assert (List.mem (c, e) p.dep ==> List.mem (c, d) p.dep);
        assert (List.mem (c, e) p.hb  ==> List.mem (c, d) p.hb);
        assert (List.mem (c, e) p.psc ==> List.mem (c, d) p.psc);

        (* M9c ii *)
        assert (List.mem (d, c) p.dep ==> List.mem (e, c) p.dep);
        assert (List.mem (d, c) p.hb  ==> List.mem (e, c) p.hb);
        assert (List.mem (d, c) p.psc ==> List.mem (e, c) p.psc)
      )
    ) p.evs
  ) p.rmw

let wf_pomset p = wf_psc p; wf_rmw p

let candidate strongly_blocks strongly_matches p rf =
  let weak_psc d' e' =
      (not (List.mem (d', e') p.psc) || d' = e') 
    && (strongly_blocks d' e' ==> List.mem (d', e') p.psc)
  in
  List.for_all (fun (d, e) ->
    matches (p.lab d) (p.lab e) (* C1 *)
    && List.for_all (fun c -> 
      blocks (p.lab c) (p.lab e) ==> weak_psc c d || weak_psc e c
      ) p.evs (* C2 *) 
    && List.mem (d, e) p.dep && List.mem (d, e) p.psc (* C3 *)
    && strongly_matches (p.lab d) (p.lab e) ==> List.mem (d, e) p.hb (* C4 *)
  ) rf

let top_level p rf =
  List.for_all (fun e ->
    eval_formula (p.pre e) (* T1 *)
    && (is_read (p.lab e) ==> List.exists (fun d -> List.mem (d, e) rf) p.evs) (* T2 *)
  ) p.evs

let refines p1 p2 = subset p1 p2

let empty_pomset = { 
  evs = [];
  lab = empty_env;
  pre = empty_env;
  pt = empty_env; (* ?? *)
  term = True; (* ?? *)
  dep = [];
  hb = [];
  psc = [];
  rmw = []
}

(** Semantics *)
let interp _vs = function
  Skip -> empty_pomset
| _ -> raise (Invalid_argument "not yet implemented (8aunvy)")
