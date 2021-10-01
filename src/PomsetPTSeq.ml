(**
  Implementation of Pomsets with Predicate transformers.

  Definitions are labelled with their equivalents in from the paper. 
  Definitions are approximately in the order introduced from the paper.
 *)

open Preliminaries
open Relation
open Util

exception Unbound

(** Preliminaries *)
(* These prelims are specialised for the sequential version of the semantics. *)
type mode = Rlx | Rel | Acq | SC

let pp_mode fmt = function
  Rlx -> Format.fprintf fmt "rlx"
| Rel -> Format.fprintf fmt "rel"
| Acq -> Format.fprintf fmt "acq"
| SC -> Format.fprintf fmt "sc"

type grammar = 
  Initialisation
| Assign of register * expr
| Load of register * mem_ref * mode
| Store of mem_ref * mode * expr
| Skip
| Sequence of grammar * grammar
| Ite of expr * grammar * grammar
| Par of grammar * grammar

let rec pp_grammar fmt = function
    Initialisation -> Format.fprintf fmt "init"
  | Assign (Reg r, e) -> Format.fprintf fmt "%s := %a" r pp_expr e
  | Load (Reg r, Ref x, am) -> Format.fprintf fmt "%s := %s.load(%a)" r x pp_mode am
  | Store (Ref x, am, e) -> Format.fprintf fmt "%s.store(%a, %a)" x pp_mode am pp_expr e
  | Skip -> Format.fprintf fmt "skip"
  | Sequence (p1, p2) -> Format.fprintf fmt "%a; %a" pp_grammar p1 pp_grammar p2
  | Ite (e, p1, p2) -> 
    Format.fprintf fmt "if(%a) { %a } else { %a }" pp_expr e pp_grammar p1 pp_grammar p2
  | Par (p1, p2) -> Format.fprintf fmt "{ %a } || { %a }" pp_grammar p1 pp_grammar p2

type action =
  Init
| Write of mode * mem_ref * value
| Read of mode * mem_ref * value
| Fence of mode

let mode_of = function
    Init -> Rlx
  | Write (m,_,_)
  | Read (m,_,_)
  | Fence m -> m

let mem_ref_of = function
    Write (_,x,_)
  | Read (_,x,_) -> Some x
  | Fence _ -> None
  | Init -> None (* weird *)

let same_location = curry @@ function
  Init, _ -> true
| _, Init -> true
| Fence _, _ -> false
| _, Fence _ -> false
| a, b -> mem_ref_of a = mem_ref_of b

let value_of = function
    Init -> Some (Val 0)
  | Write (_,_,v)
  | Read (_,_,v) -> Some v
  | Fence _ -> None

let eq_action = curry @@ function
  Read (m,x,v), Read (m',x',v')
| Write (m,x,v), Write (m',x',v') -> m = m' && x = x' && v = v'
| Fence m, Fence m' -> m = m'
| _ -> false

let is_read   = function Read _ -> true | _ -> false
let is_write  = function Init | Write _ -> true | _ -> false
let is_fence  = function Fence _ -> true | _ -> false
let is_release a = List.mem (mode_of a) [Rel; SC]

let mode_order = [
  (Rlx, Rlx); (Rlx, Acq); (Rlx, Rel); (Rlx,SC)
; (Rel, Rel); (Rel, SC)
; (Acq, SC)
; (SC, SC)
] 

(* mord a b = a [= b *)
let mord a b = List.mem (a,b) mode_order

(** Definition 2.1 *)
let matches = curry @@ function
    Write (_,x,v), Read (_,x',v') -> x = x' && v = v' 
  | Init, Read (_, _, Val 0) -> true
  | _ -> false

let blocks = curry @@ function
    Write (_,x,_), Read (_,x',_) -> x = x'
  | Init, Read _ -> true
  | _ -> false

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

(** Definition 3.4 *)
type pomsetPT = {
  evs: event set;                                                   (* M1  *)
  lab: (event, action) environment;                                 (* M2  *)
  pre: (event, formula) environment;                                (* M3  *)
  
  (* TODO: definition 1.4 restricts these in a way that we cannot implement 
     because it universally quantifies formulae.  *)
  pt:   transformer_family;                                         (* M4  *)
  
  term: formula;                                                    (* M5  *)
  ord: (event, event) relation;                                     (* M6  *)

  po: (event, event) relation;
  pi: (event, event) relation;

  (* This is used to compute final state *)
  smap: (register, value) environment;

  (* For a given register, track which events might influence its value *)
  reg_involved: (register, event set) environment;
}

(* Helpers for reg_involved *)
let empty_ri = fun _ -> []
let ri_union ri1 ri2 r = ri1 r <|> ri2 r

let real_events p = List.map fst (List.filter (uncurry (=)) p.pi)
let phantom_events p = (domain p.pi) <-> (real_events p)

let simple_events p = 
  List.map fst (List.filter (fun (_,e) ->
    List.length (List.filter (fun (_, e') -> e = e') p.pi) = 1
  ) p.pi)

let compound_events evs p = evs <-> (simple_events p)

(** Pomset Utils *)
let eq_pomset p1 p2 =
  (* Strategically ordered to hopefully reduce exec time *)
     equal_set (=) p1.evs p2.evs
  && p1.term = p2.term
  && equal_relation (=) (=) p1.ord p2.ord
  && List.for_all (fun e1 -> p1.lab e1 = p2.lab e1) p1.evs
  && List.for_all (fun e1 -> p1.pre e1 = p2.pre e1) p1.evs

let empty_pomset = { 
  evs = [];
  lab = empty_env;
  pre = empty_env;
  pt = (fun _d f -> f);
  term = True;
  ord = [];
  po = [];
  pi = [];
  smap = empty_env;
  reg_involved = empty_ri;
}

let init_pomset = 
  let id = fresh_id () in
  {
    evs = [id];
    lab = bind id Init empty_env;
    pre = bind id True empty_env;
    pt = (fun _d f -> sub_locs (V (Val 0)) f |> sub_quis True);
    term = True;
    ord = [];
    po = [(id, id)];
    pi = [(id, id)];
    smap = empty_env;
    reg_involved = empty_ri; (* TODO: should this be (fun _ -> [id]) ? *)
  }

let pp_action fmt = function
  Init -> Format.fprintf fmt "Init"
| Read (m,x,v) -> Format.fprintf fmt "R(%a,%a,%a)" pp_mode m pp_mem_ref x pp_value v
| Write (m,x,v) -> Format.fprintf fmt "W(%a,%a,%a)" pp_mode m pp_mem_ref x pp_value v
| Fence m -> Format.fprintf fmt "F(%a)" pp_mode m

let pp_pomset fmt p = 
  Format.fprintf fmt "Events (%d): %a\n" (List.length p.evs) (pp_set pp_int) p.evs;
  List.iter (fun e ->
    Format.fprintf fmt "%d : [%a | %a]\n" e 
      pp_formula (try p.pre e with Not_found -> debug "can't pre %d (zCg7xg)\n" e; False) 
      pp_action (p.lab e)
  ) p.evs;
  Format.fprintf fmt "term: %a\n" pp_formula p.term;
  Format.fprintf fmt "ord: %a\n" (PPRelation.pp_relation pp_int pp_int) p.ord;
  Format.fprintf fmt "pi:  %a\n" (PPRelation.pp_relation pp_int pp_int) p.pi;
  Format.fprintf fmt "po:  %a\n" (PPRelation.pp_relation pp_int pp_int) p.po

(* M2 *)
let wf_lab p = complete p.evs p.lab

(* M3 *)
let wf_pre p = complete p.evs p.pre

(* M4 *)
(* Note: this is impractical to express, it requires quantifying all possible
   formulae *)
let wf_pt _p = true

(* M5a *)
let wf_term p = 
  try 
    eval_entails p.term (p.pt p.evs True)
  with e ->
   debug "%a |= %a\n%!" pp_formula p.term pp_formula (p.pt p.evs True);
   raise e


(* M6 *)
let wf_ord p = partial_order p.ord

let wf_pomset p =
     wf_lab p
  && wf_pre p
  && wf_pt p
  && wf_term p
  && wf_ord p

let build_extensions r1 r2 e1 e2 =
  let e1r = e1 <-> e2 in
  let e2r = e2 <-> e1 in
  powerset (
    (cross e1r e2r) <|> (cross e2r e1r)
  ) |> List.map (fun ext -> ext <|> r1 <|> r2)

(** Semantics *)
let pomset_skip = [empty_pomset]

(** We are now computing all the possible reads that could interfere, see note below. *)
let sequence_rule ps1 ps2 =
  info "SEQ(PS1, PS2)\n%!";
  List.flatten @@ List.flatten @@ List.flatten (
    (cross ps1 ps2) |> List.rev_map (fun (p1, p2) ->
      (* The overlap of E1 and E2 must satisfy some compatibility predicate *)
      let eqrs = List.filter (
          List.for_all (fun (a, b) -> eq_action (p1.lab a) (p2.lab b))
        ) (pairings p1.evs p2.evs) 
      in

      eqrs |> List.rev_map (fun eqr ->
        let freshened_eqr = List.map (fun eq -> (fresh_id (), eq)) eqr in
        let merge_registers = List.fold_left (fun acc (c, (a, b)) ->
          let sa, sb, sc = register_from_id a, register_from_id b, register_from_id c in
          (fun f -> f |> sub_reg (R sc) sa |> sub_reg (R sc) sb |> acc)
        ) Util.id freshened_eqr 
        in
        let pi' = List.fold_left (fun pi (c, (a, b)) -> 
          (c, c) :: List.map (fun (e1, e2) -> 
            if e2 = a || e2 = b 
            then e1, c
            else e1, e2
          ) pi
        ) (p1.pi <|> p2.pi) freshened_eqr in

        let pi_inv x = List.map fst (List.filter (fun (_, e) -> e = x) pi') in
        let pi_po_ext = cross 
          (List.flatten (List.map pi_inv p1.evs))
          (List.flatten (List.map pi_inv p2.evs))
        in
        let phantom_ext = List.map snd freshened_eqr in
        let po' = p1.po <|> p2.po <|> pi_po_ext <|> phantom_ext in

        let evs_p1 = List.fold_left (fun acc (c, (a,b)) ->
            c :: (acc <-> [a;b])
          ) p1.evs freshened_eqr
        in
        let evs_p2 = List.fold_left (fun acc (c, (a,b)) ->
            c :: (acc <-> [a;b])
          ) p2.evs freshened_eqr
        in

        let evs_new = evs_p1 <|> evs_p2 in
        let lab_new c = 
          if (List.exists (fun (c', _) -> c=c') freshened_eqr)
          then (fun (a, _) -> p1.lab a) (List.assoc c freshened_eqr) 
          else (
            (* Check for belt and braces, this labelling funciton should never be 
               called with old event ids *)
            if (List.exists (fun (_, (a, b)) -> a = c || b = c) freshened_eqr)
            then raise (Invalid_argument ("panic (HAPtst)" ^ (string_of_int c)))
            else join_env p1.lab p2.lab c
          )
        in

        let ord_new = List.fold_left (fun acc (c,(a,b)) ->
            List.map (fun (l, r) ->
              let nl = if a = l || b = l then c else l in
              let nr = if a = r || b = r then c else r in
              (nl, nr)
            ) acc
          ) (p1.ord <|> p2.ord) freshened_eqr 
        in

        let pt_map1 e = try fst (List.assoc e freshened_eqr) with Not_found -> e in
        let pt_map2 e = try snd (List.assoc e freshened_eqr) with Not_found -> e in

        (* TODO: this is a bit hairbrained. James suggests it would be better to keep track of
        registers in the pomset foreach precondition (k) and predicate transformer (T) such that we
        cna be really precise about which choices of ord extention are actually useful. *)
        let down_set_r1 = List.filter (is_read <.> lab_new) evs_p1 in
        let down_set_w1 = List.filter (is_write <.> lab_new) evs_p2 in
        let down_set_r2 = List.filter (is_read <.> lab_new) evs_p2 in
        let down_set_w2 = List.filter (fun e -> is_write (lab_new e) && lab_new e <> Init) evs_p1 in
        let down_useful = ((cross down_set_r1 down_set_w1) <|> (cross down_set_r2 down_set_w2))
          |> powerset
          |> List.map (fun du -> transitive_closure ~refl:true (ord_new <|> du))
          |> List.filter partial_order
        in

        let p1pt d f = merge_registers (p1.pt d f) in
        let p2pt d f = merge_registers (p2.pt d f) in
        let p1pre e = merge_registers (p1.pre e) in
        let p2pre e = merge_registers (p2.pre e) in
        let p1term = merge_registers p1.term in
        let p2term = merge_registers p2.term in

        down_useful |> List.map (fun du -> 
          (* Note: this is an over-approximation of the read sets. If we could inspect the predicate
          transformers then we could generate a precise set of reads which could "interfere" with c 
          in the definition of down. *)
          let read_sets = powerset (List.filter (is_read <.> lab_new) evs_p1) in
          read_sets |> List.map (fun rs ->
            let down e = List.find_all (fun c -> List.mem (c, e) du && c <> e) rs in
            (* We have confirmed with James that p1.evs is a good index for the use of the predicate
               transformer *)
            let k2' e =
              if is_read (lab_new e) 
              then p1pt (List.map pt_map1 p1.evs) (p2pre (pt_map2 e))
              else p1pt (down e) (p2pre (pt_map2 e))
            in

            (* eqr is used to map ids from p1 into ids to p2 to generate merge opportunities *)
            {
              evs = evs_new;                                        (* S1  *)
              lab = lab_new;                                        (* S2  *)

              pre = (fun e ->
                assert (not (List.exists (fun (_, (a, b)) -> a = e || b = e) freshened_eqr));
                if List.mem e (List.map fst freshened_eqr)
                then Or (p1pre (pt_map1 e), k2' e)                 (* S3c *)
                else (
                  if List.mem e p1.evs
                  then p1pre e                                     (* S3a *)
                  else k2' e                                       (* S3b *)
                )
              );

              pt = (fun d f ->                                      (* S4  *)
                p1pt (List.map pt_map1 d) (p2pt (List.map pt_map2 d) f)
              );

              (* We have confirmed with James that this is E_1 is a good index *)
              (* TODO: check whether the D on p1pt should be passed through pt_map1 *)
              term = And (p1term, p1pt (List.map pt_map1 p1.evs) p2term);              (* S5  *)
              ord = du;                                             (* S6  *)

              po = po';
              pi = pi';

              (* It is important that we look in the second environment first *)
              smap = join_env p2.smap p1.smap;
              reg_involved = ri_union p2.reg_involved p1.reg_involved;
            }
          )
        )
      )
    )
  )

let if_rule cond ps1 ps2 =
  info "IF(%a,PS1, PS2)\n%!" pp_formula cond;
  List.flatten ((cross ps1 ps2) |> List.rev_map (fun (p1, p2) -> 
    let eqrs = List.filter (
        List.for_all (fun (a, b) -> eq_action (p1.lab a) (p2.lab b))
      ) (pairings p1.evs p2.evs) 
    in
    eqrs |> List.map (fun eqr ->
      let freshened_eqr = List.map (fun eq -> (fresh_id (), eq)) eqr in
      let merge_registers = List.fold_left (fun acc (c, (a, b)) ->
        let sa, sb, sc = register_from_id a, register_from_id b, register_from_id c in
        (fun f -> f |> sub_reg (R sc) sa |> sub_reg (R sc) sb |> acc)
      ) Util.id freshened_eqr 
      in

      (* TODO: check what happens in the case of a double merge. Does the correct pi get built? *)
      let pi' = List.fold_left (fun pi (c, (a, b)) -> 
        (c, c) :: List.map (fun (e1, e2) -> 
          if e2 = a || e2 = b 
          then e1, c
          else e1, e2
        ) pi
      ) (p1.pi <|> p2.pi) freshened_eqr in

      let evs_new = List.fold_left (fun acc (c, (a,b)) ->
          c :: (acc <-> [a;b])
        ) (p1.evs <|> p2.evs) freshened_eqr
      in
      let lab_new c = 
        if (List.exists (fun (c', _) -> c=c') freshened_eqr)
        then (fun (a, _) -> p1.lab a) (List.assoc c freshened_eqr) 
        else (
          (* Check for belt and braces, this labelling funciton should never be 
              called with old event ids *)
          if (List.exists (fun (_, (a, b)) -> a = c || b = c) freshened_eqr)
          then raise (Invalid_argument "panic (HAPtst)")
          else join_env p1.lab p2.lab c
        )
      in

      let ord_new = List.fold_left (fun acc (c,(a,b)) ->
          List.map (fun (l, r) ->
            let nl = if a = l || b = l then c else l in
            let nr = if a = r || b = r then c else r in
            (nl, nr)
          ) acc
        ) (p1.ord <|> p2.ord) freshened_eqr 
      in

      let pt_map1 e = try fst (List.assoc e freshened_eqr) with Not_found -> e in
      let pt_map2 e = try snd (List.assoc e freshened_eqr) with Not_found -> e in

      let p1pt d f = merge_registers (p1.pt d f) in
      let p2pt d f = merge_registers (p2.pt d f) in
      let p1pre e = merge_registers (p1.pre e) in
      let p2pre e = merge_registers (p2.pre e) in
      let p1term = merge_registers p1.term in
      let p2term = merge_registers p2.term in

      {
        evs = evs_new;                                              (* I1  *)
        lab = lab_new;                                              (* I2  *)

        pre = (fun e ->
          assert (not (List.exists (fun (_, (a, b)) -> a = e || b = e) freshened_eqr));
          if List.mem e (List.map fst freshened_eqr)
          then Or (                                                 (* I3c *)
            And (cond, p1pre (pt_map1 e)),
            And (Not cond, p2pre (pt_map2 e))
          )
          else (
            (* We don't need to use the pt_map because we know we're not in eqr *)
            if List.mem e p1.evs
            then And (cond, p1pre e)                               (* I3a *)
            else And (Not cond, p2pre e)                           (* I3b *)
          )
        ); 
      
        pt = (fun d f ->                                            (* I4  *)
          Or (
            And (cond, p1pt (List.map pt_map1 d) f),
            And (Not cond, p2pt (List.map pt_map2 d) f)
          )
        );
        
        term = Or (And (cond, p1term), And (Not cond, p2term));     (* I5  *)
        ord = ord_new;                                              (* I6  *)

        po = p1.po <|> p2.po;
        pi = pi';
        (* It is important that we look in the second environment first *)
        smap = join_env p2.smap p1.smap;
        reg_involved = ri_union p2.reg_involved p1.reg_involved;
      }
    ) 
  ))

(* This is for top level parallel only, not intended for use with code 
   sequenced after the parallel.  *)
let paralell_rule ps1 ps2 = 
  info "PAR(PS1, PS2) %d\n%!" ((List.length ps1) * (List.length ps2));
  (* We assume p1 and p2 to be disjoint *)
  (cross ps1 ps2) |> List.map (fun (p1, p2) -> 
    {
      evs = p1.evs <|> p2.evs;
      lab = join_env p1.lab p2.lab;
      pre = (fun e ->
        if List.mem e p1.evs
        then p1.pre e
        else p2.pre e
      );

      (* This distinguisishes this par from left par *)
      pt = (fun _d f -> f);
      term = And (p1.term, p2.term);
      ord = p1.ord <|> p2.ord;

      po = p1.po <|> p2.po;
      pi = p1.pi <|> p2.pi;

      smap = join_env p1.smap p2.smap;
      reg_involved = ri_union p2.reg_involved p1.reg_involved;
    }
  )

let assign_rule r m = 
  info "%a := %a\n%!" pp_register r pp_expr m;
  [ { empty_pomset with pt = (fun _d f -> sub_reg m r f) } ]        (* LET *)

let read_rule vs r x mode = 
  info "%a := %a\n%!" pp_register r pp_mem_ref x;
  vs |> List.map (fun v ->
    let id = fresh_id () in
    let se = register_from_id id in
    let v = Val v in
    {
      empty_pomset with
      evs = [id];                                                   (* R1  *)
      lab = bind id (Read (mode, x, v)) empty_env;                  (* R2  *)
      pre = bind id (Q (Qui x)) empty_env;                          (* R3  *)
      pt = (fun d f ->
        if List.mem id d (* E n D != empty *)
        then sub_reg (R se) r (Implies (EqExpr (V v, R r), f))                         (* R4a *)
        else sub_reg (R se) r (Implies (Or (EqVar (x, R r), EqExpr (R r, V v)), f))    (* R4b *)
      );
      term = True;                                                  (* R5a *)
      smap = bind r v empty_pomset.smap;
      po = [(id, id)];
      pi = [(id, id)]
    }
  ) <|> [
    let se = fresh_register () in
    {
      empty_pomset with
      pt = (fun _d f -> sub_reg (R se) r f);                        (* R4c *)
             (* if mode =] Acq then term = ff *)
      term = if mord Acq mode then False else True;                 (* R5a,b *)
      smap = (fun r' -> if r = r' then raise Unbound else raise Not_found)
    }
  ]

let write_rule vs x mode m = 
  info "%a := %a\n%!" pp_mem_ref x pp_expr m;
  vs |> List.map (fun v ->
    let v = Val v in
    let id = fresh_id () in
    {
      empty_pomset with
      evs = [id];                                                   (* W1  *)
      lab = bind id (Write (mode, x, v)) empty_env;                 (* W2  *)
      pre = bind id (EqExpr (m, V v)) empty_env;                    (* W3  *)
      pt = (fun _d f ->                                             (* W4a  *)
           sub_loc m x f
        |> sub_qui (EqExpr (m, V v)) (Qui x)
      );
      term = EqExpr (m, V v);                                       (* W5a *)
      po = [(id, id)];
      pi = [(id, id)]
    }
  ) <|> [
    {
      empty_pomset with 
      pt = (fun _d f -> sub_loc m x f |> sub_qui False (Qui x));    (* W4b *)
      term = False                                                  (* W5b *)
    }
  ]

let complete p =
  List.for_all (fun e ->
    tautology (p.pre e)                                             (* C3  *)
  ) p.evs
  && tautology p.term                                               (* C5  *)

let gen_rf_candidates p =
  let reads = List.filter (is_read <.> p.lab) p.evs in
  let writes = List.filter (is_write <.> p.lab) p.evs in
  let is_some = function None -> false | Some _ -> true in
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

let grow_pomset (rf : (event * event) list) p =
  (* M7 *)
  (* M7a holds by construction of rf *)
  let m7b = List.fold_left (fun ps (d,e) -> 
      let blockers = List.filter (fun c -> blocks (p.lab c) (p.lab e)) p.evs in
      let ord_choice = List.map (fun c -> (c,d), (e,c)) blockers in
      List.fold_left (fun ps (lord, rord) -> 
        List.flatten @@ List.map (fun p ->
          [{ p with ord = lord :: p.ord }; { p with ord = rord :: p.ord }]
        ) ps
      ) ps ord_choice
    ) [p] rf
  in
  let m7c = List.map (fun p -> { p with ord = rtc p.evs (rf @ p.ord) }) m7b in
  m7c

let interp vs check_complete prog = 
  let filter ps = List.filter (fun p -> satisfiable p.term) ps in
  let rec go vs = function
    Initialisation -> [init_pomset]
  | Skip -> [empty_pomset]
  | Assign (r, e) -> assign_rule r e
  | Load (r, x, mode) -> read_rule vs r x mode
  | Store (x, mode, e) -> write_rule vs x mode e
  (* TODO: We can probably specialise Sequence (Initialisation, p1) to improve performance *)
  | Sequence (p1, p2) -> 
    sequence_rule 
      (filter (go vs p1))
      (filter (go vs p2))
  (* Note: we expect e to be a binary expr. We do not coerce as is expected in the paper. *)
  | Ite (e, p1, p2) ->
    if_rule (Expr e)
      (filter (go vs p1))
      (filter (go vs p2))
  | Par (p1, p2) ->
    paralell_rule 
      (filter (go vs p1))
      (filter (go vs p2))
  in
  let prog = if check_complete then Sequence (Initialisation, prog) else prog in
  let ps = go vs prog in
  let good_pomsets = List.filter wf_pomset ps in
  if check_complete
  then List.filter complete good_pomsets
  else good_pomsets
