(**
  Implementation of Pomsets with Predicate transformers.

  Definitions are labelled with their equivalents in from the paper. 
  Definitions are approximately in the order introduced from the paper.
 *)

open Preliminaries
open Relation
open Util

(** Preliminaries *)
(* These prelims are specialised for the sequential version of the semantics. *)
type mode = Rlx | Rel | Acq | SC
[@@deriving show { with_path = false }]

let pp_mode fmt = function
  Rlx -> Format.fprintf fmt "rlx"
| Rel -> Format.fprintf fmt "rel"
| Acq -> Format.fprintf fmt "acq"
| SC -> Format.fprintf fmt "sc"

type grammar = 
  Assign of register * expr
| Load of register * mem_ref * mode
| Store of mem_ref * mode * expr
| Skip
| Sequence of grammar * grammar
| Ite of expr * grammar * grammar

let rec pp_grammar fmt = function
    Assign (Reg r, e) -> Format.fprintf fmt "%s := %a" r pp_expr e
  | Load (Reg r, Ref x, am) -> Format.fprintf fmt "%s := %s.load(%a)" r x pp_mode am
  | Store (Ref x, am, e) -> Format.fprintf fmt "%s.store(%a, %a)" x pp_mode am pp_expr e
  | Skip -> Format.fprintf fmt "skip"
  | Sequence (p1, p2) -> Format.fprintf fmt "%a; %a" pp_grammar p1 pp_grammar p2
  | Ite (e, p1, p2) -> Format.fprintf fmt "if(%a) { %a } else { %a }" pp_expr e pp_grammar p1 pp_grammar p2

type action =
  Write of mode * mem_ref * value
| Read of mode * mem_ref * value
| Fence of mode
[@@deriving show { with_path = false }]

let mode_of = function
    Write (m,_,_)
  | Read (m,_,_)
  | Fence m -> m

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
    _, Write (m,_,_) when mord Rel m -> true
  | _, Fence m when mord Rel m -> true
  | Read _, Fence m when mord Acq m -> true
  | Read (m,_,_), _ when mord Acq m -> true
  | Fence m, _ when mord Acq m -> true 
  | Fence m, Write _ when mord Rel m -> true 
  | Write (m,x,_), Write(_,x',_) when mord Rel m && x = x' -> true
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
    ord = List.map (fun (l, r) -> f l, f r) ps.ord;
    smap =  ps.smap
  }

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
  pt = (fun _ps f -> f);
  term = (True "empty pomset term (yjbyyi)");
  ord = [];
  smap = empty_env
}

let pp_action fmt = function
  Read (m,x,v) -> Format.fprintf fmt "R(%a,%a,%a)" pp_mode m pp_mem_ref x pp_value v
| Write (m,x,v) -> Format.fprintf fmt "W(%a,%a,%a)" pp_mode m pp_mem_ref x pp_value v
| Fence m -> Format.fprintf fmt "F(%a)" pp_mode m

let pp_pomset fmt p = 
  List.iter (fun e ->
    Format.fprintf fmt "%d : [%a | %a]\n" e pp_formula (p.pre e) pp_action (p.lab e)
  ) p.evs;
  Format.fprintf fmt "ord: %a\n" (PPRelation.pp_relation pp_int pp_int) p.ord;
  Format.fprintf fmt "\n"

(* M2 *)
let wf_lab p = complete p.evs p.lab

(* M3 *)
let wf_pre p = complete p.evs p.pre

(* M4 *)
(* Note: this is impractical to express, it requires quantifying all possible
   formulae *)
let wf_pt _p = true

(* M6 *)
let wf_rf rf p =
     injective rf
  && List.for_all (uncurry (matches <..> p.lab)) rf

(* M7 *)
let wf_ord rf p =
     partial_order p.ord
  && rf |> List.for_all (fun (d,e) ->
      p.evs |> List.exists (fun c ->
        (blocks <..> p.lab) c e ==> (
          List.mem (c,d) p.ord || List.mem (e,c) p.ord
        )
      )
    )

let wf_pomset rf p =
  let wf = wf_lab p
  && wf_pre p
  && wf_pt p
  && wf_rf rf p
  && wf_ord rf p in
  (* debug "%s %a\n" (if wf then "good" else "bad") pp_pomset p; *)
  wf

let top_level rf p =
     wf_pomset rf p
  && tautology p.term                                               (* T1  *)
  && p.evs |> List.for_all (fun e ->                                (* T2  *)
         tautology (p.pre e)                                        (* T2a *)
      && is_read (p.lab e) ==> List.exists ((=) e <.> snd) rf       (* T2b *)
    )

let build_extensions r1 r2 e1 e2 =
  let e1r = e1 <-> e2 in
  let e2r = e2 <-> e1 in
  powerset (
    (cross e1r e2r) <|> (cross e2r e1r)
  ) |> List.map (fun ext -> ext <|> r1 <|> r2)

(** Semantics *)
let pomset_skip = [empty_pomset]

(** TODO: we're using the minimal dep relation, rather than any subset -- is this safe? *)
(** We are now computing all the possible reads that could interfere, see note below. *)
let pomsets_seq_gen ps1 ps2 =
  info "SEQ(PS1, PS2)\n%!";
  List.flatten @@ List.flatten @@ List.flatten (
    (cross ps1 ps2) |> List.map (fun (p1, p2) ->
      (* The overlap of E1 and E2 must satisfy some compatibility predicate *)
      let eqrs = List.filter (
          List.for_all (fun (a, b) -> eq_action (p1.lab a) (p2.lab b))
        ) (pairings p1.evs p2.evs) 
      in

      eqrs |> List.map (fun eqr ->
        let p1 = relabel (eqr_to_mapping eqr) p1 in 
        let lab_new = join_env p1.lab p2.lab in

        (* TODO: This misses rules i3a-c, and might generate down-useful events which are
            incompatible with dep. *)
        let down_useful = List.filter (is_write <.> lab_new) (p1.evs <|> p2.evs) in

        let down_useful = powerset down_useful 
          |> List.map (fun du -> cross du du)
          |> List.filter (fun du -> partial_order (p1.ord <|> p2.ord <|> du))
        in

        down_useful |> List.map (fun du -> 
          (* Note: this is an over-approximation of the read sets. If we could inspect the predicate
          transformers then we could generate a precise set of reads which could "interfere" with c 
          in the definition of down. *)
          let read_sets = powerset (List.filter (is_read <.> lab_new) (p1.evs <|> p2.evs)) in
          read_sets |> List.map (fun rs ->
            let ord' = p1.ord <|> p2.ord <|> du in
            let down e = List.find_all (fun c -> List.mem (c, e) ord' && c <> e) rs in
            (* TODO: Confirm with James that p1.evs is a good index for the use of the predicate
               transformer *)
            let k2' e =
              if is_read (lab_new e) 
              then p1.pt p1.evs (p2.pre e)
              else p1.pt (down e) (p2.pre e)
            in
            let pre1 e = if is_release (lab_new e) then p1.term else (True "pre1 (PjcvHT)") in

            (* eqr is used to map ids from p1 into ids to p2 to generate merge opportunities *)
            {
              evs = p1.evs <|> p2.evs;                              (* S1  *)
              lab = lab_new;                                        (* S2  *)

              pre = (fun e ->
                if List.mem e p1.evs && List.mem e p2.evs
                then And (Or (p1.pre e, k2' e), pre1 e)             (* S3c *)
                else (
                  if List.mem e (p1.evs <-> p2.evs)
                  then p1.pre e                                     (* S3a *)
                  else And (k2' e, pre1 e)                          (* S3b *)
                )
              );

              pt = (fun d f -> p1.pt d (p2.pt d f));                (* S4  *)
              term = And (p1.term, p1.pt p1.evs p2.term);           (* S5  *)
              ord = ord';                                           (* S6  *)

              (* It is important that we look in the second environment first *)
              smap = join_env p2.smap p1.smap;
            }
          )
        )
      )
    )
  )

let if_gen cond ps1 ps2 =
  List.flatten ((cross ps1 ps2) |> List.map (fun (p1, p2) -> 
    let eqrs = List.filter (
        List.for_all (fun (a, b) -> eq_action (p1.lab a) (p2.lab b))
      ) (pairings p1.evs p2.evs) 
    in
    eqrs |> List.map (fun eqr ->
      let p1 = relabel (eqr_to_mapping eqr) p1 in 
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
        
        pt = (fun d f ->                                            (* I4  *)
          Or (
            And (cond, p1.pt d f),
            And (Not cond, p2.pt d f)
          )
        );
        
        term = Or (And (cond, p1.term), And (Not cond, p2.term));   (* I5  *)
        ord = p1.ord <|> p2.ord;                                    (* I6  *)

        (* It is important that we look in the second environment first *)
        smap = join_env p2.smap p1.smap;
      }
    ) 
  ))

let assign_gen r m = 
  info "%a := %a\n%!" pp_register r pp_expr m;
  [ { empty_pomset with pt = (fun _d f -> sub_reg m r f) } ]        (* LET *)

let read_gen vs r x mode = 
  info "%a := %a\n%!" pp_register r pp_mem_ref x;
  vs |> List.map (fun v ->
    let id = fresh_id () in
    let v = Val v in
    {
      empty_pomset with
      evs = [id];                                                   (* R1  *)
      lab = bind id (Read (mode, x, v)) empty_env;                  (* R2  *)
      pre = bind id (Q (Qui x)) empty_env;                          (* R3  *)
      pt = (fun d f ->
        if List.mem id d (* E n D != empty *)
        then Implies (EqExpr (V v, R r), f)                         (* R4a *)
        else Implies (Or (EqExpr (V v, R r), EqVar (x, R r)), f)    (* R4b *)
      );
      term = True "read term (VDhm12)";                                                  (* R5a *)
      smap = bind r v empty_pomset.smap;
    }
  ) <|> [
    {
      empty_pomset with
      pt = (fun _d f -> f);                                         (* R4c *)
             (* if mode =] Acq then term = ff *)
      term = if mord Acq mode then (False "R5a,b (kz29dg)") else (True "R5a,b (WOtE7l)");                 (* R5a,b *)
    }
  ]

let write_gen vs x mode m = 
  info "%a := %a\n%!" pp_mem_ref x pp_expr m;
  vs |> List.map (fun v ->
    let v = Val v in
    let id = fresh_id () in
    info "Building pomset with %a... \n" pp_action (Write (mode, x, v));
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
    }
  ) <|> [
    {
      empty_pomset with 
      pt = (fun _d f -> sub_loc m x f |> sub_qui (False "W4b (SDGy8S)") (Qui x));    (* W4b *)
      (* W5b *)
      term = (False (Format.sprintf "W5b (4Ksziv) W(%s,%s,_) " (show_mode mode) (show_mem_ref x)))
    }
  ]

let complete rf p =
  let r = List.for_all (fun e ->
    let ea = try p.lab e with Not_found -> failwith "p.lab e (OuL8Qi)" in
    let ep = try p.pre e with Not_found -> failwith "p.pre e (ehFYkc)" in
    
       is_read ea ==> List.exists (fun (_,e') -> e = e') rf       (* C2  *)
    && try tautology (sub_quis (True "C3 (YewLUb)") ep)                         (* C3  *)
    with Not_found -> Debug.debug "offending formula: %a\n" pp_formula (sub_quis (True "C3 (YewLUb)") ep ); failwith "panic"
  ) p.evs
  in
  if r then Debug.debug "%a\n" pp_formula p.term;
  r
  && tautology p.term                                               (* C5  *)

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

let grow_pomset rf p =
  (* M7 *)
  let ps = List.fold_left (fun acc (d,e) ->
    let blockers = List.filter (fun c -> (blocks <..> p.lab) c e) p.evs in
    let blockers = List.map (fun c -> (c,d), (e,c)) blockers in
    let blockers_l, blockers_r = List.split blockers in
    let block_choices = BatList.n_cartesian_product [blockers_l;blockers_r] in
    { p with ord = (d,e) :: p.ord @ rf } :: { p with ord = (e,d) :: p.ord @ rf } ::
    (List.fold_left (fun acc bc -> 
      { p with ord = (d,e) :: bc @ p.ord @ rf } :: { p with ord = (e,d) :: bc @ p.ord @ rf } :: acc
    ) [] block_choices) 
    @ acc
  ) [] rf
  in
  List.map (fun p ->
    { p with ord = rtc p.evs p.ord }
  ) ps

let interp vs prog = 
  let rec go vs = function
    Assign (r, e) -> assign_gen r e
  | Skip -> [empty_pomset]
  | Load (r, x, mode) -> read_gen vs r x mode
  | Store (x, mode, e) -> write_gen vs x mode e
  | Sequence (p1, p2) -> pomsets_seq_gen (go vs p1) (go vs p2)
  (* Note: we expect e to be a binary expr. We do not coerce as is expected in the paper. *)
  | Ite (e, p1, p2) -> if_gen (Expr e) (go vs p1) (go vs p2)
  in
  let ps = List.fold_left (fun acc p ->
      let rfs = gen_rf_candidates p in
      List.fold_left (fun acc rf ->
        let new_ps = grow_pomset rf p in
        List.map (fun p -> rf, p) new_ps @ acc
      ) [] rfs @ acc
    ) [] (go vs prog)
  in
  let good_pomsets = List.filter (uncurry wf_pomset) ps in
  let good_pomsets = List.filter (uncurry complete) good_pomsets in
  List.map snd good_pomsets
