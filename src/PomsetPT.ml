(**
  Implementation of Pomsets with Predicate transformers.

  Definitions are labelled with their equivalents in from the paper. 
  Definitions are approximately in the order introduced from the paper.
 *)

open Relation
open Util

(** Preliminaries *)
type value = Val of int
[@@deriving show { with_path = false }]

type register = Reg of string 
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

type mem_ref = Ref of string
[@@deriving show { with_path = false }]

type amode = Rlx | RA | SC
[@@deriving show { with_path = false }]

type fmode = Acq | Rel | AR
[@@deriving show { with_path = false }]

let fresh_register =
  let reg_id = ref 0 in
  function () ->
    incr reg_id; Reg ("s_" ^ (string_of_int !reg_id))

let rec eval_expr env = function
    V (Val v) -> v
  | R (Reg r) -> env r
  | Eq (e1, e2) -> if (eval_expr env e1 = eval_expr env e2) then 1 else 0
  | Gte (e1, e2) -> if (eval_expr env e1 >= eval_expr env e2) then 1 else 0
  | Gt (e1, e2) -> if (eval_expr env e1 > eval_expr env e2) then 1 else 0
  | Lte (e1, e2) -> if (eval_expr env e1 <= eval_expr env e2) then 1 else 0
  | Lt (e1, e2) -> if (eval_expr env e1 < eval_expr env e2) then 1 else 0

type grammar = 
  Assign of register * expr
| Load of register * mem_ref * amode
| Store of mem_ref * amode * expr
| FenceStmt of fmode
| Skip
| Sequence of grammar * grammar
| Ite of expr * grammar * grammar
| LeftPar of grammar * grammar
[@@deriving show { with_path = false }]

type event = int

type symbol =
  Write_sym
| Downgrade of mem_ref
[@@deriving show { with_path = false }]
         
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

let tautology f = eval_entails True f
let unsatisfiable f = eval_entails f False

type action =
  Write of amode * mem_ref * value
| Read of amode * mem_ref * value
| Fence of fmode

let amode_of = function
    Write (am,_,_)
  | Read (am,_,_) -> Some am
  | Fence _ -> None

let fmode_of = function
    Write _
  | Read _ -> None
  | Fence fm -> Some fm

let mem_ref_of = function
    Write (_,x,_)
  | Read (_,x,_) -> Some x
  | Fence _ -> None

let value_of = function
    Write (_,_,v)
  | Read (_,_,v) -> Some v
  | Fence _ -> None

let is_access = function Read _ | Write _ -> true | Fence _ -> false
let is_read   = function Read _ -> true | _ -> false
let is_write  = function Write _ -> true | _ -> false
let is_release a = amode_of a = Some RA || amode_of a = Some SC

(** Definition 2.1 *)
let matches = curry @@ function
    Write (_,x,v), Read (_,x',v') -> x = x' && v = v' 
  | _ -> false

let blocks = curry @@ function
    Write (_,x,_), Read (_,x',_) -> x = x'
  | _ -> false

let co_delays = curry @@ function
    Write (_,x,_), Write (_,x', _)
  | Read (_,x,_), Read (_,x',_)
  | Write (_,x,_), Read (_,x',_) -> x = x'
  | _ -> false

let sync_delays = curry @@ function
    _, Write (RA,_,_) | _, Write (SC, _, _)
  | _, Fence Rel | _, Fence AR
  | Read _, Fence Acq -> true
  | Read (_,x,_), Read (RA,x',_) when x = x' -> true
  | Read (_,x,_), Read (SC,x',_) when x = x' -> true
  | Read (RA,_,_), _ | Read (SC,_,_), _ -> true
  | Fence Acq, _ | Fence AR, _ -> true
  | Fence Rel, Write _ -> true
  | Write (RA,x,_), Write (_,x',_) when x = x' -> true
  | Write (SC,x,_), Write (_,x',_) when x = x' -> true
  | _ -> false

let sc_delays = curry @@ function
    Write (SC,_,_), Write (SC,_,_)
  | Write (SC,_,_), Read (SC,_,_)
  | Read (SC,_,_), Write (SC,_,_)
  | Read (SC,_,_), Read (SC,_,_) -> true
  | _ -> false

let delays a b = co_delays a b || sync_delays a b || sc_delays a b

(** Definition 2.2 *)
type transformer = formula -> formula

(** Definition 2.3 *)
type transformer_family = event set -> transformer

(* This is a point at which the tool is incomplete. Quantifying all possible 
   formulae f is uncomputable. *)
let wf_transformer_family p_univ e f tf =
  p_univ |> List.for_all (fun d ->
    p_univ |> List.for_all (fun c ->
      subset (=) (c <&> e) d ==> eval_entails (tf c f) (tf d f)
    )
  )

(** Definition 2.4 *)
type pomsetPT = {
  evs: event set;                                                   (* M1  *)
  lab: (event, action) environment;                                 (* M2  *)
  pre: (event, formula) environment;                                (* M3  *)
  
  (* TODO: definition 1.4 restricts these in a way that we cannot implement 
     because it universally quantifies formulae.  *)
  pt:   transformer_family;                                         (* M4  *)
  
  term: formula;                                                    (* M5  *)
  rf:  (event, event) relation;                                     (* M6  *)
  ord: (event, event) relation;                                     (* M7  *)

  (* This is used to compute  *)
  smap: (register, value) environment;
}

let eq_pomset p1 p2 =
  (* Strategically ordered to hopefully reduce exec time *)
    equal_set (=) p1.evs p2.evs
  && p1.term = p2.term
  && equal_relation (=) (=) p1.rf p2.rf
  && equal_relation (=) (=) p1.ord p2.ord
  && List.for_all (fun e1 -> p1.lab e1 = p2.lab e1) p1.evs
  && List.for_all (fun e1 -> p1.pre e1 = p2.pre e1) p1.evs

let empty_pomset = { 
  evs = [];
  lab = empty_env;
  pre = empty_env;
  pt = (fun _ps f -> f);
  term = True;
  rf = [];
  ord = [];
  smap = empty_env_d (Val 0)
}

(* M2 *)
let wf_lab p = complete p.evs p.lab 

(* M3 *)
let wf_pre p = complete p.evs p.pre

(* M4 *)
(* Note: this is impractical to express, it requires quantifying all possible
   formulae *)
let wf_pt _p = true

(* M6 *)
let wf_rf p =
     injective p.evs p.rf
  && List.for_all (uncurry (matches <..> p.lab)) p.rf

(* M7 *)
let wf_ord p =
     partial_order p.ord
  && p.rf |> List.for_all (fun (d,e) ->
      p.evs |> List.exists (fun c ->
        (blocks <..> p.lab) c e ==> (
          List.mem (c,d) p.ord || List.mem (e,c) p.ord
        )
      )
    )

let wf_pomset p = 
     wf_lab p
  && wf_pre p
  && wf_pt p
  && wf_rf p
  && wf_ord p

let top_level p =
     tautology p.term                                               (* T1  *)
  && p.evs |> List.for_all (fun e ->                                (* T2  *)
         tautology (p.pre e)                                        (* T2a *)
      && is_read (p.lab e) ==> List.exists ((=) e <.> snd) p.rf     (* T2b *)
    )

(* We need to grow a candidate pomset such that with minimal changes to dep, 
   plo, etc. we have a candidate pomset as per definition C below. *)
let grow_candidate strongly_overlaps strongly_matches strongly_fences p rf =
  let strongly_overlaps = strongly_overlaps <..> p.lab in
  let strongly_matches = strongly_matches <..> p.lab in
  let _strongly_fences = strongly_fences <..> p.lab in

  (* d -> e ∈ rf => d -> e ∈ dep *)
  let c6_expand = { p with dep = p.dep <|> rf } in

  (* if d' <= d -rf-> e, and λ(d') strongly matches λ(e') then d' <= e' *)
  let c7a = map_default [c6_expand] (fun d' ->
      let new_dep_edges = List.fold_left (fun acc (d, e) ->
          if List.mem (d', d) c6_expand.dep && strongly_matches d e 
          then (d, e) :: acc
          else acc
        ) [] rf
      in
      { c6_expand with dep = c6_expand.dep <|> new_dep_edges }
    ) c6_expand.evs
  in

  let c7b = List.flatten @@ (c7a |> List.map (fun p ->
      let sync_choices = List.fold_left (fun acc (d, e) -> 
          if strongly_matches d e
          then [(d, e); (e, d)] :: acc
          else acc
        ) [] (cross p.evs p.evs)
      in
      map_default [p] (fun sync_ext -> { p with sync = p.sync <|> sync_ext }) (BatList.n_cartesian_product sync_choices)
    ))
  in

  (* d -> e ∈ rf => d -> e ∈ plo *)
  let c8a = List.map (fun p -> { p with plo = p.plo <|> rf }) c7b in

  let weak_plo_per_rf = rf |> List.map (fun (r, w) ->
      (
        (List.filter (strongly_overlaps w) p.evs) |> List.map (fun c ->
          (c, r)
        )
      ) @ (
        (List.filter (strongly_overlaps r) p.evs) |> List.map (fun c ->
          (w, c)
        )
      )
    )
  in

  let weak_plo_per_rf = 
    List.filter (List.for_all (fun (d, e) -> List.mem (e, d) p.plo ==> (d = e))) weak_plo_per_rf
  in

  let weak_plo_extensions = BatList.n_cartesian_product weak_plo_per_rf in
  let c8b = big_union @@ List.map (fun p ->
      List.map (fun plo_ext ->
        { p with plo = p.plo <|> plo_ext }
      ) weak_plo_extensions
    ) c8a
  in
  c8b

let candidate strongly_overlaps strongly_matches strongly_fences p rf =
  let strongly_overlaps = strongly_overlaps <..> p.lab in
  let strongly_matches = strongly_matches <..> p.lab in
  let strongly_fences = strongly_fences <..> p.lab in
  let weak_plo d' e' =
      ((List.mem (d', e') p.plo) ==> (d' = e'))
    && (strongly_overlaps d' e' ==> List.mem (d', e') p.plo)
  in
  injective (List.filter (is_read <.> p.lab) p.evs) rf              (* C1  *)
  && List.for_all (fun (d, e) ->
       matches (p.lab d) (p.lab e)                                  (* C2  *)
    && List.for_all (fun c -> 
      (blocks <..> p.lab) c e ==> weak_plo c d || weak_plo e c
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
    && strongly_fences d e ==> (
      List.mem (d, e) p.sync || List.mem (e, d) p.sync
      ) (* C7b *)
    && List.mem (d, e) p.plo (* C8a *)
    && List.for_all (fun c ->
      (blocks <..> p.lab) c e ==> (weak_plo c d || weak_plo e c)
    ) p.evs (* C8b *)
  ) rf

let top_level strongly_overlaps strongly_matches strongly_fences p rf =
  candidate strongly_overlaps strongly_matches strongly_fences p rf
  && List.for_all (fun e ->
      (is_read (p.lab e) ==> List.exists (fun d -> List.mem (d, e) rf) p.evs) (* T2 *)
      && eval_formula (p.pre e) (* T3 *)
    ) p.evs
  && eval_formula p.term (* T5 *)

(* TODO: This has changed (11-05-2021) *)
(* let refines p1 p2 = subset (=) p1 p2 *)

(** Pomset Utils *)
let eqr_to_mapping eqr =
  function e -> 
    try List.assoc e eqr
    with Not_found -> e

let relabel f ps =
  { 
    evs = List.map f ps.evs;
    lab = (fun e -> ps.lab (f e));
    pre = (fun e -> ps.pre (f e));
    pt = (fun d form -> ps.pt (List.map f d) form);
    term = ps.term;
    dep = List.map (fun (l, r) -> f l, f r) ps.dep;
    sync = List.map (fun (l, r) -> f l, f r) ps.sync;
    plo = List.map (fun (l, r) -> f l, f r) ps.plo;
    rmw = List.map (fun (l, r) -> f l, f r) ps.rmw;
    smap = ps.smap
  }

(** Semantics *)
let pomset_skip = [empty_pomset]


(* Note: that for P1 it is acceptable to use a normal union operator, as the IDs 
  in p1 and p2 are always unique - generated by fresh_id () - so disjointness is 
  always preserved. *)
let pomsets_par_gen ps1 ps2 =
  info "PAR(PS1, PS2)\n%!";
  List.map (fun (p1, p2) ->
    {
      evs = p1.evs <|> p2.evs;                                      (* P1  *)
      lab = join_env p1.lab p2.lab;                                 (* P2  *)
      pre = join_env p1.pre p2.pre;                                 (* P3a,b *)
      pt = p1.pt;                                                   (* P4  *)
      term = And (p1.term, p2.term);                                (* P5  *)

      dep = p1.dep <|> p2.dep;                                      (* P6  *)
      sync = p1.sync <|> p2.sync;                                   (* P7  *)
      plo = p1.plo <|> p2.plo;                                      (* P8  *)
      rmw = p1.rmw <|> p2.plo;                                      (* P9  *)
      smap = join_env p1.smap p2.smap;
    }
  ) (cross ps1 ps2)

let pomsets_par_filer ps = ps


(** TODO: we're using the minimal dep relation, rather than any subset -- is this safe? *)
(** We are now computing all the possible reads that could interfere, see note below. *)
let pomsets_seq_gen ps1 ps2 =
  info "SEQ(PS1, PS2)\n%!";
  List.flatten (
    (cross ps1 ps2) |> List.map (fun (p1, p2) ->
      let lab_new = join_env p1.lab p2.lab in

      (* Note: this is an over-approximation of the read sets. If we could inspect the predicate
      transformers then we could generate a precise set of reads which could "interfere" with c in
      the definition of down. *)
      let read_sets = powerset (List.filter (is_read <.> lab_new) (p1.evs <|> p2.evs)) in

      (* The overlap of E1 and E2 must satisfy some compatibility predicate *)
      (* TODO: is this choice of predicate actually correct? It has bad code-smell *)
      let eqrs = List.filter (fun eqr ->
          List.for_all (fun (a, b) -> 
            try merge (p1.lab a) (p2.lab b) <> []
            with Invalid_argument _ -> false (*  Events are un-mergable because of incompatible modes *)
          ) eqr
        ) (pairings p1.evs p2.evs)
      in

      (* TODO: This misses rules i3a-c, and might generate down-useful events which are     
          incompatible with dep. *)
      let down_useful = List.filter (is_write <.> lab_new) (p1.evs <|> p2.evs) in

      (* Build all possible relations from down-useful, and filter from compatibility with dep *)
      let down_useful = powerset down_useful 
        |> List.map (fun du -> cross du du)
        |> List.filter (fun du -> partial_order (p1.dep <|> p2.dep <|> du))
      in

      List.flatten @@ List.flatten @@ (
        read_sets |> List.map (fun rs -> 
          eqrs |> List.map (fun eqr ->
            down_useful |> List.map (fun du ->
              let f = eqr_to_mapping eqr in
              let down e = List.find_all (fun c -> List.mem (c, e) (p1.dep <|> p2.dep <|> du)) rs in
              let k2' e = 
                if is_read (lab_new e) 
                then p1.pt p1.evs (p2.pre e)
                else p1.pt (down e) (p2.pre e)
              in
              (* eqr is used to map ids from p1 into ids to p2 to generate merge opportunities *)
              let p1 = relabel f p1 in 
              let s7a = List.filter (fun (d, e) -> 
                     synchronisation_delays (p1.lab d) (p2.lab e) 
                  && satisfiable (And (p1.pre d, p2.pre e))
                ) (cross p1.evs p2.evs) 
              in
              let s8a = List.filter (fun (d, e) -> 
                     coherence_delays (p1.lab d) (p2.lab e) 
                  && satisfiable (And (p1.pre d, p2.pre e))
                ) (cross p1.evs p2.evs) 
              in
              {
                evs = p1.evs <|> p2.evs;
                lab = lab_new;                                              (* S2  *)

                pre = (fun e ->
                  let pre1 = 
                    if List.mem e p1.evs && List.mem e p2.evs
                    then And (Or (p1.pre e, k2' e), p1.term)                (* S3c  *)
                    else (
                      if List.mem e (p1.evs <-> p2.evs)
                      then p1.pre e                                         (* S3a *)
                      else And (p2.pre e, p1.term)                          (* S3b *)
                    )
                  in
                  if is_release (lab_new e)
                  then And (p1.term, pre1)                                  (* S3d *)
                  else pre1
                );

                pt = (fun d f -> p1.pt d (p2.pt d f));                      (* S4  *)
                term = And (p1.term, p1.pt p1.evs p2.term);                 (* S5  *)
                dep = p1.dep <|> p2.dep <|> du;                             (* S6  *)
                sync = p1.sync <|> p2.sync <|> s7a;                         (* S7,S7a *)
                plo = p1.plo <|> p2.plo <|> s8a;                            (* S8,S8a *)
                rmw = p1.rmw <|> p2.rmw;                                    (* S9  *)
                smap = join_env p1.smap p2.smap;
              }
            )
          )
        )
      )
    )
  )

let if_gen cond ps1 ps2 =
  List.flatten ((cross ps1 ps2) |> List.map (fun (p1, p2) -> 
    List.map (fun eqr ->
      let f = eqr_to_mapping eqr in
      let p1 = relabel f p1 in 
      {
        evs = p1.evs <|> p2.evs;                                    (* I1  *)
        lab = join_env p1.lab p2.lab;                               (* I2  *)

        pre = (fun e ->
            if List.mem e p1.evs && List.mem e p2.evs
            then Or (                                               (* I3c *)
              And (cond, p1.pre e),
              And (Not cond, p2.pre e)
            )
            else (
              if List.mem e p1.evs
              then And (cond, p1.pre e)                             (* I3a *)
              else And (Not cond, p2.pre e)                         (* I3b *)
            )
          ); 
        
        pt = (fun d f -> 
          Or (
            And (cond, p1.pt d f),
            And (Not cond, p2.pt d f)
          )
        );
        
        term = Or (And (cond, p1.term), And (Not cond, p2.term));   (* I5  *)
        dep = p1.dep <|> p2.dep;                                    (* I6  *)
        sync = p1.sync <|> p2.sync;                                 (* I7  *)
        plo = p1.plo <|> p2.plo;                                    (* I8  *)
        rmw = p1.rmw <|> p2.rmw;                                    (* I9  *)
        smap = join_env p1.smap p2.smap;
      }
    ) (pairings p1.evs p2.evs)
  ))

let assign_gen r m = 
  info "%a := %a\n%!" pp_register r pp_expr m;
  [
    {
      empty_pomset with 
      pt = (fun _d f -> sub_reg m r f)
    }
  ]

let assign_filter ps = ps

let fence_gen mode = 
  info "fence(%a)\n%!" pp_fmode mode;
  let id = fresh_id () in
  [
    {
      empty_pomset with
      evs = [id];                                                   (* F1  *)
      lab = bind id (Fence (mode)) empty_env;                       (* F2  *)
      pre = bind id True empty_env;                                 (* F3  *)
      pt = (fun _d f -> f);                                         (* F4  *)
      term = True;                                                  (* F5a *)
    }
  ] <|> [{empty_pomset with term = False}]                          (* F5b *)

let fence_filter ps = ps

let read_gen vs r x mode = 
  info "%a := %a\n%!" pp_register r pp_mem_ref x;
  vs |> List.map (fun v ->
    let id = fresh_id () in
    let v = Val v in
    let se = fresh_register () in
    {
      empty_pomset with
      evs = [id];                                                   (* R1  *)
      lab = bind id (Read (mode, x, v)) empty_env;                  (* R2  *)
      pre = (fun _ -> True);                                        (* R3  *)
      pt = (fun d f ->
        if List.mem id d (* E n D <> empty *)
        then Implies (EqExpr (V v, R se), rename_reg se r f)        (* R4a *)
        else Implies (                                              (* R4b *)
            Or (EqExpr (V v, R se), EqVar (x, R se)), 
            rename_reg se r f
          )
      );
      term = True;                                                  (* R5a *)
      smap = bind se v empty_pomset.smap;
    }
  ) <|> [
    { 
      empty_pomset with
      term = if mode_order mode Acq then False else True;           (* R5b *)
      (* R4c does not need to be implemented, as we do not re-use registers. *)
    }
  ]

let read_filter ps = ps

let write_gen vs x mode m = 
  info "%a := %a\n%!" pp_mem_ref x pp_expr m;
  vs |> List.map (fun v ->
    let v = Val v in
    let id = fresh_id () in
    { 
      empty_pomset with
      evs = [id];                                                   (* W1  *)
      lab = bind id (Write (mode, x, v)) empty_env;                 (* W2  *)
      pre = bind id (EqExpr (m, V v)) empty_env;                    (* W3  *)
      pt = (fun _d f -> sub_loc m x f);                             (* W4  *)
      term = EqExpr (m, V v);                                       (* W5b *)
    }
  ) <|> [
    {
      empty_pomset with 
      pt = (fun _d f -> sub_loc m x f);                             (* W4  *)
      term = False                                                  (* W5a *)
    }
  ]

let write_filter ps = ps

let gen_rf_candidates p =
  let reads = List.filter (is_read <.> p.lab) p.evs in
  let writes = List.filter (is_write <.> p.lab) p.evs in
  let is_some = function None -> false | Some _ -> true in
  let same_location a b = mem_ref_of a = mem_ref_of b && is_some (mem_ref_of a) in
  let same_value a b = value_of a = value_of b && is_some (value_of a) in
  let wr_sloc_sval = List.fold_left (fun acc r ->
      let sloc_sval_writes = List.filter (fun w -> 
           (same_location <..> p.lab) r w 
        && (same_value <..> p.lab) r w) 
        writes 
      in
      (List.map (fun w -> w, r) sloc_sval_writes) :: acc
    ) [] reads
  in
  big_union (List.map powerset (BatList.n_cartesian_product wr_sloc_sval))

let grow_and_filter ps =
  let fences _ _ = false in
  let grow = 
    List.flatten @@ List.flatten (
      ps |> List.map (fun p ->
        gen_rf_candidates p |> List.map (grow_candidate overlaps matches fences p)
      )
    )
  in

  grow 
  (* |> List.filter (fun p ->
    List.exists (candidate overlaps matches fences p) (gen_rf_candidates p)
  ) *)

(* Is it important to reject non-pomsets (according to M1-9) at each interpretation step, or can it 
   all be done at the end, as we currently do here? *)
let interp vs prog = 
  let rec go = function
    Assign (r, e) -> assign_gen r e
  | Skip -> [empty_pomset]
  | Load (r, x, mode) -> read_gen vs r x mode
  | LeftPar (p1, p2) -> pomsets_par_gen (go p1) (go p2)
  | Store (x, mode, e) -> write_gen vs x mode e
  | Sequence (p1, p2) -> pomsets_seq_gen (go p1) (go p2)
  | FenceStmt (mode) -> fence_gen mode
  | Ite (e, p1, p2) -> if_gen (EqExpr (e, V (Val 0))) (go p1) (go p2)
  in
  grow_and_filter (go prog)
