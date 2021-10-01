(**
  Implementation of Pomsets with Predicate transformers.

  Definitions are labelled with their equivalents in from the paper. 
  Definitions are approximately in the order introduced from the paper.
 *)

open Preliminaries
open Relation
open Util

type amode = Rlx | RA | SC
let show_amode = function Rlx -> "rlx" | RA -> "ra" | SC -> "sc"
let pp_amode fmt m = Format.fprintf fmt "%s" (show_amode m)

type fmode = Acq | Rel | AR
let show_fmode = function Acq -> "acq" | Rel -> "rel" | AR -> "ar"
let pp_fmode fmt m = Format.fprintf fmt "%s" (show_fmode m)

type grammar = 
  Assign of register * expr
| Load of register * mem_ref * amode
| Store of mem_ref * amode * expr
| FenceStmt of fmode
| Skip
| Sequence of grammar * grammar
| Ite of expr * grammar * grammar
| LeftPar of grammar * grammar

let rec pp_grammar fmt = function
    Assign (Reg r, e) -> Format.fprintf fmt "%s := %a" r pp_expr e
  | Load (Reg r, Ref x, am) -> Format.fprintf fmt "%s := %s.load(%a)" r x pp_amode am
  | Store (Ref x, am, e) -> Format.fprintf fmt "%s.store(%a, %a)" x pp_amode am pp_expr e
  | FenceStmt fm -> Format.fprintf fmt "fence(%a)" pp_fmode fm
  | Skip -> Format.fprintf fmt "skip"
  | Sequence (p1, p2) -> Format.fprintf fmt "%a; %a" pp_grammar p1 pp_grammar p2
  | Ite (e, p1, p2) -> Format.fprintf fmt "if(%a) { %a } else { %a }" pp_expr e pp_grammar p1 pp_grammar p2
  | LeftPar (p1, p2) -> Format.fprintf fmt "(%a) || (%a)" pp_grammar p1 pp_grammar p2

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

let eq_action = curry @@ function
  Read (m,x,v), Read (m',x',v')
| Write (m,x,v), Write (m',x',v') -> m = m' && x = x' && v = v'
| Fence m, Fence m' -> m = m'
| _ -> false

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

  (* This is used to compute final state *)
  smap: (register, value) environment;
}

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
    rf = List.map (fun (l, r) -> f l, f r) ps.rf;
    ord = List.map (fun (l, r) -> f l, f r) ps.ord;
    smap = ps.smap
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
  smap = empty_env
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
     injective p.rf
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


let build_extensions r1 r2 e1 e2 =
  let e1r = e1 <-> e2 in
  let e2r = e2 <-> e1 in
  powerset (
    (cross e1r e2r) <|> (cross e2r e1r)
  ) |> List.map (fun ext -> ext <|> r1 <|> r2)

(** Semantics *)
let pomset_skip = [empty_pomset]


(* Note: that for P1 it is acceptable to use a normal union operator, as the IDs 
  in p1 and p2 are always unique - generated by fresh_id () - so disjointness is 
  always preserved. *)
let pomsets_par_gen ps1 ps2 =
  info "PAR(PS1, PS2)\n%!";
  let extended_ps = List.flatten @@ List.flatten @@ List.map (fun (p1, p2) ->
      let rf_extensions = build_extensions p1.rf p2.rf p1.evs p2.evs in
      let ord_extensions = build_extensions p1.ord p2.ord p1.evs p2.evs in
      rf_extensions |> List.map (fun rf_ext ->
        (* This generation might yield some duplicate pomsets, this could be optimised. *)
        let rf_ord_ext = rf_ext |> List.filter (fun (d,e) -> 
               List.mem d p1.evs 
            && List.mem e p2.evs
          )
        in
        ord_extensions |> List.map (fun ord_ext ->
          {
            evs = p1.evs <|> p2.evs;                                      (* P1  *)
            lab = join_env p1.lab p2.lab;                                 (* P2  *)
            pre = join_env p1.pre p2.pre;                                 (* P3a,b *)
            pt = p1.pt;                                                   (* P4  *)
            term = And (p1.term, p2.term);                                (* P5  *)

            rf =  rf_ext;                                                 (* P6 *)
            ord = ord_ext <|> rf_ord_ext;                                 (* P7a,b *)

            smap = join_env p1.smap p2.smap;
          }
        )
      )
    ) (cross ps1 ps2)
  in
  List.filter wf_pomset extended_ps

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
      let eqrs = List.filter (
          List.for_all (fun (a, b) -> eq_action (p1.lab a) (p2.lab b))
        ) (pairings p1.evs p2.evs) 
      in

      let rf_extensions = build_extensions p1.rf p2.rf p1.evs p2.evs in
      let ord_extensions = build_extensions p1.ord p2.ord p1.evs p2.evs in

      List.flatten @@ List.flatten @@ List.flatten @@ (
        read_sets |> List.map (fun rs -> 
          eqrs |> List.map (fun eqr ->
            rf_extensions |> List.map (fun rf_ext ->
              let rf_ord_ext = rf_ext |> List.filter (fun (d,e) -> 
                     List.mem d p1.evs 
                  && List.mem e p2.evs
                )
              in
              let delays_ord_ext = (cross p1.evs p2.evs) |> List.filter (fun (a,b) ->
                  delays (p1.lab a) (p2.lab b)
                )
              in
              ord_extensions |> List.map (fun ord_ext ->
                let f = eqr_to_mapping eqr in
                let down e = List.find_all (fun c -> List.mem (c, e) ord_ext) rs in
                let k2' e = p1.pt (down e) (p2.pre e) in

                (* eqr is used to map ids from p1 into ids to p2 to generate merge opportunities *)
                let p1 = relabel f p1 in 
                {
                  evs = p1.evs <|> p2.evs;
                  lab = lab_new;                                              (* S2  *)

                  pre = (fun e ->
                    let pre1 = 
                      if List.mem e p1.evs && List.mem e p2.evs
                      then Or (p1.pre e, k2' e)                               (* S3c  *)
                      else (
                        if List.mem e (p1.evs <-> p2.evs)
                        then p1.pre e                                         (* S3a *)
                        else k2' e                                            (* S3b *)
                      )
                    in
                    if is_release (lab_new e)
                    then And (p1.term, pre1)                                  (* S3d *)
                    else pre1
                  );

                  pt = (fun d f -> p1.pt d (p2.pt d f));                      (* S4  *)
                  term = And (p1.term, p1.pt p1.evs p2.term);                 (* S5  *)
                  rf = rf_ext;                                                (* S6  *)
                  ord = ord_ext <|> rf_ord_ext <|> delays_ord_ext;            (* S7a,b,c *)

                  smap = join_env p1.smap p2.smap;
                }
              )
            )
          )
        )
      )
    )
  )

let if_gen cond ps1 ps2 =
  List.flatten ((cross ps1 ps2) |> List.map (fun (p1, p2) -> 
    let eqrs = pairings p1.evs p2.evs in
    let eqrs_compatible = List.filter (
        List.for_all (fun (a, b) -> eq_action (p1.lab a) (p2.lab b))
      ) eqrs 
    in

    eqrs_compatible |> List.map (fun eqr ->
      let f = eqr_to_mapping eqr in
      let p1 = relabel f p1 in 
      {
        evs = p1.evs <|> p2.evs;                                    (* C1  *)
        lab = join_env p1.lab p2.lab;                               (* C2  *)

        pre = (fun e ->
            if List.mem e p1.evs && List.mem e p2.evs
            then Or (                                               (* C3c *)
              And (cond, p1.pre e),
              And (Not cond, p2.pre e)
            )
            else (
              if List.mem e p1.evs
              then And (cond, p1.pre e)                             (* C3a *)
              else And (Not cond, p2.pre e)                         (* C3b *)
            )
          ); 
        
        pt = (fun d f -> 
          Or (
            And (cond, p1.pt d f),
            And (Not cond, p2.pt d f)
          )
        );
        
        term = Or (And (cond, p1.term), And (Not cond, p2.term));   (* C5  *)
        (* TODO: The rules say rf extends rf1 and rf2, and also says rf <= (rf1 + rf2). This seems contradictory and leaves only rf = rf1 + rf2. This is fishy. *)
        rf = p1.rf <|> p2.rf;                                       (* C6a,b *)
        ord = p1.ord <|> p2.ord;                                    (* C7a,b *)

        smap = join_env p1.smap p2.smap;
      }
    ) 
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
      pre = bind id True empty_env;                                 (* unconstrained *)
      pt = (fun _d f -> f);                                         (* F4  *)
      term = True;                                                  (* unconstrained *)
    }
  ] <|> [{empty_pomset with term = False}]                          (* F5 *)

let fence_filter ps = ps

let read_gen vs r x mode = 
  info "%a := %a\n%!" pp_register r pp_mem_ref x;
  vs |> List.map (fun v ->
    let id = fresh_id () in
    let v = Val v in
    {
      empty_pomset with
      evs = [id];                                                   (* R1  *)
      lab = bind id (Read (mode, x, v)) empty_env;                  (* R2  *)
      pre = (fun _ -> True);                                        (* unconstrained  *)
      pt = (fun d f ->
        if List.mem id d (* E n D != empty *)
        then Implies (EqExpr (V v, R r), f)                         (* R4a *)
        else Implies (Or (EqExpr (V v, R r), EqVar (x, R r)), f)    (* R4b *)
      );
      term = True;                                                  (* unconstrained *)
      smap = bind r v empty_pomset.smap;
    }
  ) <|> [
    {
      empty_pomset with
      pt = (fun _d f -> f);                                         (* R4c *)
      term = if mode <> Rlx then False else True;                   (* R5 *)
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
      term = EqExpr (m, V v);                                       (* W5a *)
    }
  ) <|> [
    {
      empty_pomset with 
      pt = (fun _d f -> sub_loc m x f);                             (* W4  *)
      term = False                                                  (* W5b *)
    }
  ]

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

let rec interp vs = function
    Assign (r, e) -> assign_gen r e
  | Skip -> [empty_pomset]
  | Load (r, x, mode) -> read_gen vs r x mode
  | LeftPar (p1, p2) -> pomsets_par_gen (interp vs p1) (interp vs p2)
  | Store (x, mode, e) -> write_gen vs x mode e
  | Sequence (p1, p2) -> pomsets_seq_gen (interp vs p1) (interp vs p2)
  | FenceStmt (mode) -> fence_gen mode
  | Ite (e, p1, p2) -> if_gen (EqExpr (e, V (Val 0))) (interp vs p1) (interp vs p2)
  
