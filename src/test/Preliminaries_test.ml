open OUnit2

open Preliminaries

let false_f = False
let some_f = EqExpr (V (Val 1), V (Val 2))

let test_eval_entails_lhs_false _ = assert_equal true (eval_entails false_f some_f)

let x_is_one = EqVar (Ref "x", V (Val 1))

let test_eval_entails_one_is_one _ = assert_equal true (eval_entails x_is_one x_is_one)

let x_is n = EqVar (Ref "x", V (Val n))
let x_is_one_or_two = Or (x_is 1, x_is 2)

let test_eval_entails_one_or_two_is_one _ = assert_equal false (eval_entails x_is_one_or_two x_is_one)

let test_eval_entails_true_true _ = assert_equal true (eval_entails True True)

let y_is n = EqVar (Ref "y", V (Val n))
let x_is_one_and_y_is_one = And (x_is 1, y_is 1)

let test_reg_one_is_one _ = 
  let f1 =
      And (
        EqExpr (R (Reg "r1"), V (Val 1)),
        EqExpr (R (Reg "r2"), V (Val 1))
      )
  in
  let f2 = 
      EqExpr (R (Reg "r1"), V (Val 1))
  in
  assert_equal true (eval_entails f1 f2)

                          
let test_eval_entails_xy_one_is_one _ = 
  assert_equal true (eval_entails x_is_one_and_y_is_one x_is_one)

let test_eq_expr _ = assert_equal true (eval_entails (EqExpr ((V (Val 1), (V (Val 1))))) True)

let test_example_term _ =
  (*  tt && ((r = 0) && ff) || (~(r = 0) && tt)  *)
  let f = Or (
    And (True, And (EqExpr (R (Reg "r"), V (Val 0)), False)),
    And (Not (EqExpr (R (Reg "r"), V (Val 0))), True)
  )
  in
  assert_equal false (tautology f)

let test_eval_simple_formula _ = 
  (* (r = 0) => (r != 1) *)
  let f = Implies (
    EqExpr (R (Reg "r"), V (Val 0)),
    Not (EqExpr (R (Reg  "r"), V (Val 1)))
  ) in
  assert_equal true (eval_formula f)

let test_eval_formula_eq_expr _ =
  let f = EqExpr (V (Val 0), V (Val 0)) in
  assert_equal true (eval_formula f)

let test_eval_formula_and _ =
  let f = And (True, True) in
  assert_equal true (eval_formula f)

let test_eval_formula_or _ =
  let f = Or (False, True) in
  assert_equal true (eval_formula f)

let test_eval_formula_impl _ =
  let f = Implies (False, True) in
  assert_equal true (eval_formula f)

let test_eval_formula_neg _ =
  let f = Not False in
  assert_equal true (eval_formula f)

let test_not_taut _ =
  let f =
    Implies (EqExpr (R (Reg "r1"), R (Reg "r2")), False)
  in
  assert_equal false (tautology f)

let test_expr_not_taut _ =
  let f = EqExpr (R (Reg "r1"), V (Val 0)) in
  assert_equal false (tautology f)

let test_negative_int _ =
  let f = EqExpr (V (Val (-1)), V (Val (-1))) in
  assert_equal true (tautology f)

let test_merge_precond _ = 
  let f = 
    Implies (
      Or (EqExpr (R (Reg "r1"), V (Val 1)), EqVar (Ref "x", R (Reg "r1"))),
      Implies (
        Or (EqExpr (R (Reg "r2"), V (Val 1)), EqVar (Ref "x", R (Reg "r2"))),
        And (EqExpr (R (Reg "r1"), R (Reg "r2")), EqExpr (V (Val 1), V (Val 1)))
      )
    )
  in
  assert_equal false (tautology f)

let pomset_pt_formula_suite =
  "PomsetPT formula operations" >::: [
    "test_eval_entails_lhs_false" >:: test_eval_entails_lhs_false
  ; "test_eval_entails_one_is_one" >:: test_eval_entails_one_is_one
  ; "test_eval_entails_one_or_two_is_one" >:: test_eval_entails_one_or_two_is_one
  ; "test_reg_one_is_one" >::test_reg_one_is_one
  ; "test_eval_entails_xy_one_is_one" >:: test_eval_entails_xy_one_is_one
  ; "test_eval_entails_true_true" >:: test_eval_entails_true_true
  ; "test_eq_expr" >:: test_eq_expr
  ; "test_example_term" >:: test_example_term
  ; "test_eval_simple_formula" >:: test_eval_simple_formula
  ; "test_eval_formula_eq_expr" >:: test_eval_formula_eq_expr
  ; "test_eval_formula_and" >:: test_eval_formula_and
  ; "test_eval_formula_or" >:: test_eval_formula_or
  ; "test_eval_formula_impl" >:: test_eval_formula_impl
  ; "test_eval_formula_neg" >:: test_eval_formula_neg
  ; "test_not_taut" >:: test_not_taut
  ; "test_expr_not_taut" >:: test_expr_not_taut
  ; "test_negative_int" >:: test_negative_int
  ; "test_merge_precond" >:: test_merge_precond
  ]

