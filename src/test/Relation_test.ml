open OUnit2

open Relation

let test_union_idempotent _ =
  assert_equal ([1;2;3] <|> [3;4;5]) ([1;2;3] <|> [3;4;5] <|> [3;4;5]);
  assert_equal ([1;2;3] <|> [3;4;5] <|> [3;4;5]) ([1;2;3] <|> [3;4;5])

let test_disjunction_idempotent _ =
  assert_equal ([1;2;3] <&> [3;4;5]) ([1;2;3] <&> [3;4;5] <&> [3;4;5]);
  assert_equal ([1;2;3] <&> [3;4;5] <&> [3;4;5]) ([1;2;3] <&> [3;4;5])

let test_difference_idempotent _ =
  assert_equal ([1;2;3] <-> [1;2] <-> [1]) ([3]);
  assert_equal ([1;2;3] <-> [2] <-> [2]) ([1;3])

let relation_operator_idempotence = 
  "Relation operators are idempotent" >::: [
    "union idempotent" >:: test_union_idempotent
  ; "disjunction idempotent" >:: test_disjunction_idempotent
  ; "difference idempotent" >:: test_difference_idempotent
  ]

let test_rm _ =
  assert_equal ([1;2;3]) (rm 4 [1;2;3;4]);
  assert_equal ([1;2;3]) ([1;2;3;4;5] |> rm 4 |> rm 5)

let test_pairings _ =
  assert_bool "2x2" (equal_set (equal_set (=)) ([
    []
  ; [(1,3)]; [(1,3); (2,4)]; [(2,4)]
  ; [(2,3)]; [(2,3); (1,4)]; [(1,4)]
  ]) (pairings [1;2] [3;4]));
  assert_bool "2x3" (equal_set (equal_set (=)) [
    []
  ; [(1,3)]; [(1,3); (2,4)]; [(1,3); (2,5)]
  ; [(1,4)]; [(1,4); (2,3)]; [(1,4); (2,5)] 
  ; [(1,5)]; [(1,5); (2,3)]; [(1,5); (2,4)]
  ; [(2,3)]; [(2,4)]; [(2,5)]
  ] (pairings [1;2] [3;4;5]))

let relation_operator_basic =
  "Relation operators basic tests" >::: [
    "rm" >:: test_rm
  ; "pairings" >:: test_pairings
  ]
