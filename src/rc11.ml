open PomsetPTSeq
open Preliminaries
open Relation
open Util

let filter_by_ordering p orderings events =
  List.filter (fun e ->
    List.mem (mode_of (p.lab e)) orderings
  ) events

let extern po rel = rel <-> (po <|> inv po)

let imm_po_loc p po = 
  List.filter (fun (a, b) -> same_location (p.lab a) (p.lab b)) po

let rs_rc11 p ids write_rel po rf rmw =
  let rs_a = seq write_rel (opt ids (imm_po_loc p po)) in
  let rs_b = rtc ids (seq rf rmw) in
  seq rs_a rs_b

let release_rc11 p ids po rf rmw =
  let write_rel = rel_of_set (List.filter (is_write <.> p.lab) ids) in
  let release_write_ids = List.filter (fun e ->
      mode_of (p.lab e) = Rel
    && is_write (p.lab e)
    ) ids 
  in
  let rel_sc_fence_ids = List.filter (fun e ->
      (mode_of (p.lab e) = Rel || mode_of (p.lab e) = SC)
    && is_fence (p.lab e)
    ) ids
  in
  let release_a = (rel_of_set release_write_ids) <|> seq (rel_of_set rel_sc_fence_ids) po in
  seq release_a (rs_rc11 p ids write_rel po rf rmw)

let sw_rc11 p ids po rf rmw =
  let fences = List.filter (is_fence <.> p.lab) ids in
  let acq_sc_fence_ids = filter_by_ordering p [Acq; SC] fences in
  let reads = List.filter (is_read <.> p.lab) ids in
  let r_acq_ids = filter_by_ordering p [Acq] reads in
  let sw_a = seq (release_rc11 p ids po rf rmw) rf in
  let sw_b = (rel_of_set r_acq_ids) <|> seq po (rel_of_set acq_sc_fence_ids) in
  seq sw_a sw_b

let imm_hb_rc11 p ids po rf rmw =
    let sw = sw_rc11 p ids po rf rmw in
    tc (po <|> sw)

let imm_fr rf co = seq (inv rf) co

let imm_eco ids rf co =
  let eco_a = rf in
  let eco_b = seq co (opt ids rf) in
  let eco_c = seq (imm_fr rf co) (opt ids rf) in
  eco_a <|> eco_b <|> eco_c    

let imm_psc_rc11 p ids po rf co rmw =
  let fences = List.filter (is_fence <.> p.lab) ids in
  let sc_fence_ids = List.filter (fun f -> mode_of (p.lab f) = SC) fences in
  let f = rel_of_set sc_fence_ids in
  let hb = imm_hb_rc11 p ids po rf rmw in
  let psc_a = f in
  let psc_b = hb <|> (seq hb (seq (imm_eco ids rf co) hb)) in
  let psc_c = f in
  seq psc_a (seq psc_b psc_c)

let rf_completeness p ids rf =
  let reads = List.filter (is_read <.> p.lab) ids in
  equal_set (=) (List.map (fun (_, r) -> r) rf) reads

let coherence p ids po co rf rmw =
  let hb = imm_hb_rc11 p ids po rf rmw in
  let eco = imm_eco ids rf co in
  irreflexive (seq hb (opt ids eco))

let atomiciy po rf co rmw =
  let fre = extern po (imm_fr rf co) in
  let coe = extern po co in
  equal_set (=) (rmw <&> (seq fre coe)) []

let no_thin_air po rf =
  acyclic (po <|> rf)

let rc11_sc p ids po rf co rmw =
  acyclic (imm_psc_rc11 p ids po rf co rmw)

let check_axiomatic_consistency p ids po co rf rmw dep =
     rf_completeness p ids rf
  && coherence p ids po co rf rmw
  && atomiciy po rf co rmw
  && no_thin_air dep rf
  && rc11_sc p ids po rf co rmw


let pomset_locations p events = 
  let lab' = fun e ->
    let e' = snd (List.find (fun (x, _) -> x = e) p.pi) in
    p.lab e'
  in
  List.sort_uniq compare (List.map (mem_ref_of <.> lab') events) |>
  List.fold_left (fun acc -> function None -> acc | Some l -> l :: acc) []

let subsititute_init p =
  let events = phantom_events p <|> simple_events p in
  let locations = pomset_locations p events in
  let new_events = List.map (fun l ->
      fresh_id (), Write (Rlx, l, Val 0)
    ) locations
  in
  let lab' = fun e ->
    let e' = snd (List.find (fun (x, _) -> x = e) p.pi) in
    p.lab e'
  in

  let id_of_init = List.find (fun i -> lab' i = Init) events in
  let evs' = p.evs <-> [id_of_init] in
  let po' = List.fold_left (fun acc new_ev ->
      (cross [new_ev] (field acc)) <|> acc
    ) (List.filter (fun (a,_) -> a <> id_of_init) p.po) (List.map fst new_events)
  in
  let lab' = List.fold_left (fun labf (i,l) ->
      bind i l labf
    ) lab' new_events
  in
  {
    p with
    evs = evs';
    lab = lab';
    po = po'
  }, List.map fst new_events

let gen_cos p events =
  let writes = List.filter (is_write <.> p.lab) events in
  let write_labels = List.map p.lab writes in
  let locations = BatList.unique ~eq:(=) @@ List.map mem_ref_of write_labels in
  let sloc_writes : event list list =
    List.map (fun loc ->
        List.filter (fun i -> mem_ref_of (p.lab i) = loc) writes
      ) locations
  in
  let sloc_write_orders =
    List.map (fun (sloc_writes : event list) ->
        List.map order_of_list (permutations sloc_writes)
      ) sloc_writes
  in
  let co_tuple = BatList.n_cartesian_product sloc_write_orders in
  List.map List.flatten co_tuple

let gen_rfs p events : (event * event) list list =
  let reads = List.filter (is_read <.> p.lab) events in
  let writes = List.filter (is_write <.> p.lab) events in
  let wr_sloc_sval = List.fold_right (fun r acc ->
        let sloc_sval_writes = List.filter (fun w -> 
               matches (p.lab w) (p.lab r)
          ) writes 
        in
        let res = List.map (fun id' -> (id', r)) sloc_sval_writes in
        res :: acc
      ) reads []
  in
  List.fold_right
    (<|>) 
    (List.map (fun rf -> powerset rf) (BatList.n_cartesian_product wr_sloc_sval))
    [[]]

let gen_rc11_exns p =
  let p, inits = subsititute_init p in
  (* HACK: unioning in the new init event ids, and subtracting the old. This could be made less 
           fragile!*)
  let events = (phantom_events p <|> simple_events p <|> inits) <-> [1] in
  let po = List.filter (uncurry (<>)) p.po in (* remove reflexive edges... *)
  let cos = gen_cos p events in
  let rfs = gen_rfs p events in
  let dep = List.filter (uncurry (<>)) p.ord in

  let rf_co_pairs = cross cos rfs in
  List.filter (fun (co, rf) ->
    check_axiomatic_consistency p events po co rf (* rmw *)[] dep
  ) rf_co_pairs |>
  List.map (fun (co, rf) -> p, co, rf)
