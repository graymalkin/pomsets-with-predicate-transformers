open OUnit2

open Relation_test
open PomsetPT_test

let () =
  run_test_tt_main relation_operator_idempotence;
  run_test_tt_main relation_operator_basic;

  run_test_tt_main pomset_pt_formula_suite;
  run_test_tt_main pomset_pt_candidacy;
  run_test_tt_main pomset_pt_composiotions