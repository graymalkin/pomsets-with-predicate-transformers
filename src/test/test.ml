open OUnit2

open Preliminaries_test
open Relation_test
open PomsetPT_test

let () =
  (* Debug.set_log_level "all"; *)
  run_test_tt_main relation_operator_basic;

  run_test_tt_main pomset_pt_formula_suite;
  run_test_tt_main pomset_pt_utility_definitions;
  run_test_tt_main pomset_pt_candidacy;
  run_test_tt_main pomset_pt_composiotions
