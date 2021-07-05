open OUnit2

open Preliminaries

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
  Debug.debug "%a : %b\n%!" pp_formula f (tautology f);
  assert_equal false (tautology f)

let pomset_pt_formula_suite =
  "PomsetPT formula operations" >::: [
    "test_convert_dnf (base cases)" >:: test_convert_dnf_simple
  ; "test_convert_dnf (idempotent cases)" >:: test_convert_dnf1
  ; "test_convert_dnf" >:: test_convert_dnf2
  ; "test_eval_entails_lhs_false" >:: test_eval_entails_lhs_false
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
  ]

