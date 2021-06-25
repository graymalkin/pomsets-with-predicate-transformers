open OUnit2

open Relation

let test_union_idempotent _ =
  assert_equal ([1;2;3] <|> [3;4;5]) ([1;2;3] <|> [3;4;5] <|> [3;4;5]);
  assert_equal ([1;2;3] <|> [3;4;5] <|> [3;4;5]) ([1;2;3] <|> [3;4;5])

let test_union_associative _ =
  assert_equal (([1;2;3] <|> [3;4;5]) <|> [5;6;7]) ([1;2;3] <|> ([3;4;5] <|> [5;6;7]))

let test_disjunction_idempotent _ =
  assert_equal ([1;2;3] <&> [3;4;5]) ([1;2;3] <&> [3;4;5] <&> [3;4;5]);
  assert_equal ([1;2;3] <&> [3;4;5] <&> [3;4;5]) ([1;2;3] <&> [3;4;5])

let test_disjunction_associative _ =
  assert_equal (([1;2;3] <&> [3;4;5]) <&> [5;6;7]) ([1;2;3] <&> ([3;4;5] <&> [5;6;7]))

let test_difference_idempotent _ =
  assert_equal ([1;2;3] <-> [1;2] <-> [1]) ([3]);
  assert_equal ([1;2;3] <-> [2] <-> [2]) ([1;3])

let test_distribution _ =
  assert_equal ([1;3] <&> ([1;2;3] <|> [3;4;5])) (([1;3] <|> [1;2;3]) <&> ([1;3] <|> [3;4;5]))

let test_powerset _ =
  assert_bool "empty not in powerset" (List.mem [] (powerset [1;2;3]));
  assert_bool "not equal" (equal_set (equal_set (=)) [[]; [1]; [2]; [3]; [1;2]; [2;3]; [1;3]; [1;2;3]] (powerset [1;2;3]))

let test_cross _ =
  assert_equal [] (cross [1;2;3] []);
  assert_equal [] (cross [] [1;2;3]);
  assert_bool "not equal" (equal_set (=) [(1,3); (1,4); (2,3); (2,4)] (cross [1;2] [3;4]))

let test_rm _ =
  assert_equal ([1;2;3]) (rm 4 [1;2;3;4]);
  assert_equal ([1;2;3]) ([1;2;3;4;5] |> rm 4 |> rm 5)

let test_rel_of_set _ =
  assert_equal [] (rel_of_set []);
  assert_bool "not equal" (equal_set (=) [(1,1); (2,2); (3,3)] (rel_of_set [1;2;3]))

let test_pairings _ =
  assert_bool "not equal" (equal_set (equal_set (=)) ([
    []
  ; [(1,3)]; [(1,3); (2,4)]; [(2,4)]
  ; [(2,3)]; [(2,3); (1,4)]; [(1,4)]
  ]) (pairings [1;2] [3;4]));
  assert_bool "not equal" (equal_set (equal_set (=)) [
    []
  ; [(1,3)]; [(1,3); (2,4)]; [(1,3); (2,5)]
  ; [(1,4)]; [(1,4); (2,3)]; [(1,4); (2,5)] 
  ; [(1,5)]; [(1,5); (2,3)]; [(1,5); (2,4)]
  ; [(2,3)]; [(2,4)]; [(2,5)]
  ] (pairings [1;2] [3;4;5]))


type test_rel = A | B | C | D

let test_sequence _ =
  assert_bool "" (List.mem (1,3) (rel_sequence [(1,2)] [(2,3)]));
  assert_bool "" (not (List.mem (1,4) (rel_sequence [(1,2)] [(2,3); (3,4)])))

let test_injective _ =
  assert_bool "a" (injective [(1,D); (2, B); (3, A)]);
  assert_bool "b" (injective [(1,D); (2, B); (3, C); (4, A)]);
  assert_bool "c" (not @@ injective [(1,D); (2, B); (3, C); (4, C)])

let test_surjective _ =
  assert_bool "d" (surjective [A; B; C; D] [(1,D); (2, B); (3, C); (4, A)]);
  assert_bool "e" (surjective [A; B; C] [(1,A); (2, B); (3, C); (4, C)]);
  assert_bool "f" (not @@ surjective [A; B; C; D] [(1,D); (2, B); (3, C); (4, C)])

let test_bijection _ =
  assert_bool "g" (bijection [1;2;3;4] [A;B;C;D] [(1,D); (2,B); (3,C); (4, A)]);
  assert_bool "h" (not @@ bijection [1;2;3;4] [A;B;C;D] [(2,B); (3,C); (4, A)]);
  assert_bool "i" (not @@ bijection [1;2;3;4] [A;B;C;D] [(1,A); (2,B); (3,C); (4, A)]);
  assert_bool "j" (not @@ bijection [1;2;3;4] [A;B;C;D] [(1,D); (1,B); (2,B); (3,C); (4, A)])

let test_subset _ =
  assert_bool "k" (subset (=) [1;2;3] [1;5;2;3;4]);
  assert_bool "l" (subset (equal_set (=)) [[1;2;3]] (powerset [1;2;3;4]));
  assert_bool "m" (not @@ subset (=) [1;2;3] [1;5;3;4])

let test_equal_set _ =
  let shuffle d =
      let nd = List.map (fun c -> (Random.bits (), c)) d in
      let sond = List.sort compare nd in
      List.map snd sond
  in
  assert_bool "n" (equal_set (=) [A;B;C] [C;B;A]);
  assert_bool "o" (equal_set (=) [1;2;3] [2;3;1]);
  assert_bool "p" (not @@ equal_set (=) [A;B;C;D] [C;B;A]);
  assert_bool "q" (not @@ equal_set (=) [C;B;A] [A;B;C;D]);
  assert_bool "r" (equal_set (equal_set (=)) (powerset [A;B;C;D]) (shuffle @@ powerset [A;B;C;D]))

let test_reflexive _ =
  assert_bool "s" (reflexive [A;B;C] [(A,A); (B,B); (C,C)]);
  assert_bool "t" (reflexive [A;B;C] [(A,A); (B,C); (B,B); (C,B); (C,C)]);
  assert_bool "u" (not @@ reflexive [A;B;C] []);
  assert_bool "v" (not @@ reflexive [A;B;C] [(A,A)])

let test_antisymmetric _ =
  assert_bool "w" (antisymmetric []);
  assert_bool "x" (antisymmetric [(A, B); (B, C); (D, D)]);
  assert_bool "y" (not @@ antisymmetric @@ tc [(1, 2); (2, 3); (3, 1)])

let test_transitive _ =
  assert_bool "z" (transitive []);
  assert_bool "aa" (transitive [(A,A)]);
  assert_bool "ab" (transitive [(A,B); (C,D)]);
  assert_bool "ac" (transitive [(A,B); (B,C); (A,C)]);
  assert_bool "ad" (not @@ transitive [(A,B); (B,C)])

let test_transitve_closure _ =
  assert_bool "ae" (transitive @@ tc [(1,2); (2,3)]);
  assert_bool "af" (transitive @@ tc [(1,2); (2,3); (3,3)]);
  assert_bool "ag" (reflexive [1;2;3] @@ rtc [1;2;3] [(1,2); (2,3)]);
  assert_bool "ah" (transitive @@ tc []);
  assert_bool "ai" (reflexive [1;2;3] @@ rtc [1;2;3] []);
  assert_bool "aj" (transitive @@ tc [(1,2); (2,3); (3,1)])

let test_total _ =
  assert_bool "ak" (total_order [A;B;C] [(A,A); (B,B); (C,C); (A,B); (B,C); (A,C)]);
  assert_bool "al" (total_order [A] [(A,A)]);
  assert_bool "am" (total_order [] []);
  assert_bool "an" (not @@ total_order [A] []);
  assert_bool "ao" (not @@ total_order [A;B;C] [(A,B); (B,C); (A,C)]);
  assert_bool "ap" (not @@ total_order [A;B;C] [(A,A); (B,B); (C,C); (A,B); (B,C)]);
  assert_bool "aq" (not @@ total_order [A;B;C;D] [(A,A); (B,B); (C,C); (D,D); (A,B); (A,C); (C,D); (B, D)]);
  assert_bool "ar" (not @@ total_order [A;B;C;D] [(A,A); (B,B); (C,C); (D,D); (B, A); (B, C); (C,D)])

let test_acyclic _ =
  assert_bool "as" (acyclic [(1,2); (2,3)]);
  assert_bool "at" (not @@ acyclic [(1,2); (2,1)])

let relation_operator_basic =
  "Relation operators basic tests" >::: [
    "union idempotent" >:: test_union_idempotent
  ; "union assoicative" >:: test_union_associative
  ; "disjunction idempotent" >:: test_disjunction_idempotent
  ; "disjunction associative" >:: test_disjunction_associative
  ; "distribution" >:: test_distribution
  ; "difference idempotent" >:: test_difference_idempotent
  ; "powerset" >:: test_powerset
  ; "cross" >:: test_cross
  ; "rm" >:: test_rm
  ; "pairings" >:: test_pairings
  ; "rel_of_set" >:: test_rel_of_set
  ; "rel_sequence" >:: test_sequence
  ; "injective" >:: test_injective
  ; "surjective" >:: test_surjective
  ; "bijective" >:: test_bijection
  ; "subset" >:: test_subset
  ; "equal" >:: test_equal_set
  ; "reflexive" >:: test_reflexive
  ; "antisymmetric" >:: test_antisymmetric
  ; "transitive" >:: test_transitive
  ; "transitive_closure" >:: test_transitve_closure
  ; "total" >:: test_total
  ; "acyclic" >:: test_acyclic
]
