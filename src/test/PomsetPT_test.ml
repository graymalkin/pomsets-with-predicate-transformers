open OUnit2

open PomsetPT
open Relation
open Util

let p = True
let q = True
let r = True
let s = True

let input1 = And (Or (p, q), Or (r, s))
let expect1 = Or (
      And (p, r),
      Or (
        And (p, s),
        Or ( 
          And (q, r),
          And (q, s)
        )
      )
    )

let input2 = Or ( And (p, q), And (r, s) )

(** Some base cases *)
let test_convert_dnf_simple _ =
  assert_equal (Or (p, q)) (convert_dnf (Or (p, q)));
  assert_equal p (convert_dnf p)

(** Idempotent cases *)
let test_convert_dnf1 _ =
  assert_equal expect1 (convert_dnf input1)

(** Real conversion cases *)
let test_convert_dnf2 _ =
  assert_equal input2 (convert_dnf input2)


let false_f = False
let some_f = EqExpr (V (Val 1), V (Val 2))

let test_eval_entails_lhs_false _ = assert_equal true (eval_entails false_f some_f)

let x_is_one = EqVar (Ref "x", V (Val 1))

let test_eval_entails_one_is_one _ = assert_equal true (eval_entails x_is_one x_is_one)

let x_is n = EqVar (Ref "x", V (Val n))
let x_is_one_or_two = Or (x_is 1, x_is 2)

let test_eval_entails_one_or_two_is_one _ = assert_equal false (eval_entails x_is_one_or_two x_is_one)

let y_is n = EqVar (Ref "y", V (Val n))
let x_is_one_and_y_is_one = And (x_is 1, y_is 1)
                          
let test_eval_entails_xy_one_is_one _ = assert_equal true (eval_entails x_is_one_and_y_is_one x_is_one)
                                          
let pomset_pt_formula_suite =
  "PomsetPT formula operations" >::: [
    "test_convert_dnf (base cases)" >:: test_convert_dnf_simple
  ; "test_convert_dnf (idempotent cases)" >:: test_convert_dnf1
  ; "test_convert_dnf" >:: test_convert_dnf2
  ; "test_eval_entails_lhs_false" >:: test_eval_entails_lhs_false
  ; "test_eval_entails_one_is_one" >:: test_eval_entails_one_is_one
  ; "test_eval_entails_one_or_two_is_one" >:: test_eval_entails_one_or_two_is_one
  ; "test_eval_entails_xy_one_is_one" >:: test_eval_entails_xy_one_is_one
  ]

let test_gen_rf_candidates_empty _ =
  assert_equal [[]] (gen_rf_candidates empty_pomset)

let test_gen_rf_one_edge _ =
  let p = {
      empty_pomset with
      evs = [1;2];
      lab = empty_pomset.lab |> 
        Util.bind 1 (Read (Rlx, Ref "x", Val 0)) |>
        Util.bind 2 (Write (Rlx, Ref "x", Val 0));
    }
  in
  let rfs = (gen_rf_candidates p) in
  assert_bool "cannot find empty rf" (List.mem [] rfs);
  assert_bool "bad edge in rf" (not @@ List.exists (fun rf ->
    List.mem (1,2) rf || List.mem (1,1) rf || List.mem (2,2) rf
  ) rfs);
  assert_bool "cannot find expected rf" (List.exists (fun rf ->
    List.mem (2,1) rf
  ) rfs) 

let test_gen_rf_choice _ =
  let p = {
      empty_pomset with
      evs = [1;2;3];
      lab = empty_pomset.lab |> 
           Util.bind 1 (Read (Rlx, Ref "x", Val 0))
        |> Util.bind 2 (Write (Rlx, Ref "x", Val 0))
        |> Util.bind 3 (Write (Rlx, Ref "x", Val 0));
    }
  in
  let rfs = (gen_rf_candidates p) in
  assert_bool "cannot find empty rf" (List.mem [] rfs);
  assert_bool "bad edge in rf" (not @@ List.exists (fun rf ->
       List.mem (1,2) rf || List.mem (1,3) rf (* read-write edges *)
    || List.mem (1,1) rf || List.mem (2,2) rf || List.mem (3,3) rf  (* refl edges *)
    || List.mem (2,3) rf || List.mem (3,2) rf (* write-write edges *)
  ) rfs);
  assert_bool "cannot find expected rf" (List.exists (fun rf ->
    List.mem (2,1) rf
  ) rfs);
  assert_bool "cannot find expected rf" (List.exists (fun rf ->
    List.mem (3,1) rf
  ) rfs) 

let pomset_pt_utility_definitions = 
  "PomsetPT Utility Definitions" >::: [
    "empty pomset generates empty rf" >:: test_gen_rf_candidates_empty
  ; "generate trivial rf" >:: test_gen_rf_one_edge
  ; "generate multiple choices of rf" >:: test_gen_rf_choice
  ]

(* let test_grow_and_filter_empty _ =
  assert_equal ~cmp:(equal_set eq_pomset) [empty_pomset] (grow_and_filter [empty_pomset]) *)


let pomset_pt_candidacy =
  "PomsetPT Candidate Pomset" >::: [
    (* "empty is candidate" >:: test_empty_is_candidate
  ; "grow and filter empty" >:: test_grow_and_filter_empty
  ; "grow empty pomset generates empty pomset" >:: test_grow_candidate_empty *)
  ]

(* [[skip]] = empty *)
let test_interp_skip _ =
  assert_equal ~cmp:(equal_set eq_pomset) [empty_pomset] (interp [0;1] Skip) 

let test_singleton_write _ =
  assert_bool "cannot find pomset with write" (
    (interp [0;1] (Store (Ref "x", Rlx, V (Val 0))))
    |> List.exists (fun p ->
      List.exists (is_write <.> p.lab) p.evs
    )
  )

(* [[x := 1; r1 := x]] contains a pomset with a read event *)
let test_singleton_read _ =
  assert_bool "cannot find pomset with read" (
    (interp [0;1] (
      Sequence (
        Sequence (
          Store (Ref "x", Rlx, V (Val 0)),
          Load (Reg "1", Ref "x", Rlx)
        ), Skip)
      )
    ) |> List.exists (fun p ->
      List.exists (is_read <.> p.lab) p.evs
    )
  )

let pomset_pt_composiotions =
  "PomsetPT compositions" >::: [
    "interpret 'skip'" >:: test_interp_skip
  ; "single write" >:: test_singleton_write
  ; "single load" >:: test_singleton_read
  ]
