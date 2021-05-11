open Relation
open Util

(** Preliminaries *)
type value = Val of int [@@deriving show]
type register = Reg of string [@@deriving show]
type expr = 
  V of value
| R of register
[@@deriving show]
type thread_id = Tid of int [@@deriving show]
type mem_ref = Ref of string [@@deriving show]

type mode = Wk | Rlx | Acq | Rel | RA | SC [@@deriving show]
type scope = Grp | Proc | Sys [@@deriving show]

let eval_expr env = function
    V (Val v) -> v
  | R (Reg r) -> env r

type grammar = 
  Skip
| Assign of register * expr
| Load of register * mem_ref * mode * scope
| Store of mem_ref * mode * scope * expr
| FenceStmt of mode * scope
| Ite of expr * grammar * grammar
| Sequence of grammar * grammar
| LeftPar of grammar * thread_id * grammar
| CAS of register * mode * mode * scope * mem_ref * expr * expr
| FADD of register * mode * mode * scope * mem_ref * expr
| EXCHG of register * mode * mode * scope * mem_ref * expr
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

let mode_order m n = 
  match (m, n) with
    Wk, _
  | Rlx, Rel | Rlx, Acq | Rlx, RA -> true
  | Rel, RA | Acq, RA -> true
  | _, SC -> true
  | _ -> false

let lub f m n =
  match (f m n, f n m) with
    (true, false) -> Some n
  | (false,true)
  | (true, true)  -> Some m
  | (false,false) -> None

let mode_lub a b = Option.get @@ lub mode_order a b

type action =
  Write of thread_id * mode * scope * mem_ref * value
| Read of thread_id * mode * scope * mem_ref * value
| Fence of thread_id * mode * scope

let tid_of = function
    Read (t, _, _, _, _)
  | Write (t, _, _, _, _)
  | Fence (t, _, _) -> t

let mode_of = function
    Write (_,m,_,_,_)
  | Read (_,m,_,_,_)
  | Fence (_,m,_) -> m

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
let is_write  = function Write _ -> true | _ -> false

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
      mem_ref_of a = mem_ref_of b || (mode_of a = SC && mode_of b = SC)
  | Read  _, Read _ -> mode_of a = SC && mode_of b = SC
  | _ -> false

let synchronisation_delays a b =
  match (a, b) with
    _, Write (_,m,_,_,_) when mode_order Rel m -> true
  | _, Fence (_,m,_) when mode_order Rel m -> true
  | Read _, Fence (_,m,_) when mode_order Acq m -> true
  | Read (_,m,_,_,_), _ when mode_order Acq m -> true
  | Fence (_,m,_),_ when mode_order Acq m -> true
  | Fence (_,m,_), Write _ when mode_order Rel m -> true
  | Write (_,m,_,_,_), Write _ when mode_order Rel m && mem_ref_of a = mem_ref_of b -> true
  | _ -> false

let is_release = function
    Write (_,m,_,_,_) -> mode_order Rel m
  | Fence (_,m,_) -> mode_order Rel m
  | _ -> false

let is_acquire = function
    Write (_,m,_,_,_) -> mode_order Acq m
  | Fence (_,m,_) -> mode_order Acq m
  | _ -> false

let merge a b =
  match (a, b) with
    Read (tid,m,s,x,v), Read (_,m',_,x',v') when x = x' && v = v' ->
    [Read (tid,mode_lub m m',s,x,v)]
  | Write (tid,m,s,x,_), Write (_,m',_,x',w) when x = x' ->
    [Write (tid,mode_lub m m',s,x,w)]
  | Write (tid,m,s,x,v), Read (_,m',_,x',v') when x = x' && v = v' && mode_order Rlx m' ->
    [Write (tid,mode_lub m m',s,x,v)]
  | Fence (tid,m,s), Fence(_,m',_) -> [Fence (tid,mode_lub m m',s)]
  | _ -> []

(** Definition 1.1 *)
let strongly_overlaps eq_grp eq_proc a b =
  is_access a && is_access b && (
    tid_of a = tid_of b
    || (
      mode_of a <> Wk && mode_of b <> Wk   (* 2a *)
      && (scope_of a = Grp || scope_of b = Grp) ==> eq_grp a b (* 2b *)
      && (scope_of a = Proc || scope_of b = Proc) ==> eq_proc a b (* 2c *)
    )
  )

let strongly_fences eq_grp eq_proc a b =
  match a, b with
    Fence _, Fence _ ->
    tid_of a = tid_of b
    || (
      mode_of a <> Wk && mode_of b <> Wk   (* 2a *)
      && (scope_of a = Grp || scope_of b = Grp) ==> eq_grp a b (* 2b *)
      && (scope_of a = Proc || scope_of b = Proc) ==> eq_proc a b (* 2c *)
    )
  | _ -> false

let strongly_matches eq_grp eq_proc a b =
  is_release a && is_acquire b && (
       strongly_overlaps eq_grp eq_proc a b 
    || strongly_fences eq_grp eq_proc a b
  )

(** Definition 1.2 *)
type transformer = formula -> formula

(** Definition 1.3 *)
type transformer_family = event set -> transformer

(* This is a point at which the tool is incomplete. Quantifying all possible 
   formulae f is uncomputable. *)
let wf_transformer_family p_univ e f tf =
  p_univ |> List.for_all (fun d ->
    p_univ |> List.for_all (fun c ->
      subset (=) (c <&> e) d ==> eval_entails (tf c f) (tf d f)
    )
  )

(* Definition M1-M9 *)
type pomsetPT = {
  evs: event set;                           (* M1 *)
  lab: (event, action) environment;         (* M2 *)
  pre: (event, formula) environment;        (* M3 *)
  
  (* TODO: definition 1.4 restricts these in a way that we cannot 
           implement because it universally quantifies formulae. *)
  pt:   transformer_family;                 (* M4 *)
  
  term: formula;                            (* M5 *)
  dep:  (event, event) relation;            (* M6 *)
  sync: (event, event) relation;            (* M7 *)
  plo:  (event, event) relation;            (* M8 *)
  rmw:  (event, event) relation             (* M9 *)
}

(* M8a *)
let wf_plo p =
  List.iter (fun (d, e) ->
    if overlaps (p.lab d) (p.lab e)
    then assert (List.mem (d,e) p.plo)
  ) p.sync
  
let wf_rmw p =
  List.iter (fun (d, e) ->
    assert (blocks (p.lab e) (p.lab d)); (* M9a *)
    assert (List.mem (d, e) p.sync && List.mem (d, e) p.plo); (* M9b *)
    List.iter (fun c ->
      if overlaps (p.lab c) (p.lab d)
      then (
        (* M9c i *)
        assert (List.mem (c, e) p.dep  ==> List.mem (c, d) p.dep);
        assert (List.mem (c, e) p.sync ==> List.mem (c, d) p.sync);
        assert (List.mem (c, e) p.plo  ==> List.mem (c, d) p.plo);

        (* M9c ii *)
        assert (List.mem (d, c) p.dep  ==> List.mem (e, c) p.dep);
        assert (List.mem (d, c) p.sync ==> List.mem (e, c) p.sync);
        assert (List.mem (d, c) p.plo  ==> List.mem (e, c) p.plo)
      )
    ) p.evs
  ) p.rmw

let wf_pomset p = wf_plo p; wf_rmw p

let candidate strongly_overlaps strongly_matches strongly_fences p rf =
  let weak_plo d' e' =
      ((List.mem (d', e') p.plo) ==> (d' = e'))
    && (strongly_overlaps d' e' ==> List.mem (d', e') p.plo)
  in
  List.for_all (fun (d, e) ->
    matches (p.lab d) (p.lab e) (* C1 *)
    && List.for_all (fun c -> 
      blocks (p.lab c) (p.lab e) ==> weak_plo c d || weak_plo e c
      ) p.evs (* C2 *) 
    && List.mem (d, e) p.dep (* C6 *)
    && List.for_all (fun d' ->
        List.for_all (fun e' ->
          (List.mem (d', d) p.sync 
            && List.mem (e, e') p.sync 
            && strongly_matches d' e'
          ) ==> (List.mem (d', e') p.sync)
        ) p.evs
      ) p.evs (* C7a *)
    && strongly_fences (p.lab d) (p.lab e) ==> (
      List.mem (d, e) p.sync || List.mem (e, d) p.sync
      ) (* C7b *)
    && List.mem (d, e) p.plo (* C8a *)
    && List.for_all (fun c ->
      blocks (p.lab c) (p.lab e) ==> (weak_plo c d || weak_plo e c)
    ) p.evs (* C8b *)
  ) rf

let top_level strongly_overlaps strongly_matches strongly_fences p rf =
  candidate strongly_overlaps strongly_matches strongly_fences p rf
  && List.for_all (fun e ->
      (is_read (p.lab e) ==> List.exists (fun d -> List.mem (d, e) rf) p.evs) (* T2 *)
      && eval_formula (p.pre e) (* T3 *)
    ) p.evs
  && eval_formula p.term (* T5 *)

let refines p1 p2 = subset (=) p1 p2

let empty_pomset = { 
  evs = [];
  lab = empty_env;
  pre = empty_env;
  pt = (fun _ps f -> f); (* ?? *)
  term = True; (* ?? *)
  dep = [];
  sync = [];
  plo = [];
  rmw = []
}

(** Semantics *)
let pomset_skip = [empty_pomset]

let pomsets_par ps1 ps2 =
  List.map (fun (p1, p2) ->
    {
      evs = p1.evs <|> p2.evs;
      lab = join_env p1.lab p2.lab;
      pre = join_env p1.pre p2.pre;
      pt = p1.pt;
      term = And (p1.term, p2.term);

      (* TODO: The rules say this should be find some superset of p1.dep <|> p2.dep, etc. *)
      dep = p1.dep <|> p2.dep;
      sync = p1.sync <|> p2.sync;
      plo = p1.plo <|> p2.plo;
      rmw = p1.rmw <|> p2.plo
    }
  ) (cross ps1 ps2)

let pomsets_seq ps1 ps2 =
  List.map (fun (p1, p2) ->
    let new_dep = p1.dep <|> p2.dep in
    let new_lab = fun e ->
      if (List.mem e (p1.evs <-> p2.evs)) 
      then p1.lab e
      else (if (List.mem e (p2.evs <-> p1.evs))
            then p2.lab e
            else (if (List.mem e (p1.evs <&> p2.evs))
                      (* TODO: This expression can be incomplete! *)
                  then List.nth (merge (p1.lab e) (p2.lab e)) 0 
                  else raise (Invalid_argument "no label available (hkRcjy)")
            )
        )
    in
    let pre2' e = 
      let down_e = 
        if is_write (new_lab e)
        then List.find_all (fun c -> 
            List.mem (c, e) new_dep && c <> e
          ) (p1.evs <|> p2.evs)
        else p1.evs
      in
      p1.pt down_e (p2.pre e)
    in
    {
      empty_pomset with
      evs = p1.evs <|> p2.evs;
      lab = new_lab;
      pre = (fun e ->
        if (List.mem e (p1.evs <-> p2.evs)) 
        then p1.pre e
        else (if (List.mem e (p2.evs <-> p1.evs))
              then pre2' e
              else (if (List.mem e (p1.evs <&> p2.evs))
                    then Or (p1.pre e, pre2' e)
                    else raise (Invalid_argument "no termination condition available (4yS6bo)")
              )
          )
      );
      dep = new_dep;
      sync = p1.sync <|> p2.sync;
      plo = p1.plo <|> p2.plo;
      rmw = p1.rmw <|> p2.plo
    }
  ) (cross ps1 ps2)

let interp _vs = function
  Skip -> empty_pomset
| _ -> raise (Invalid_argument "not yet implemented (8aunvy)")
