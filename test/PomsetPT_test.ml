open OUnit2

open PomsetPT

let p = Symbol Write_sym
let q = Symbol Write_sym
let r = Symbol Write_sym
let s = Symbol Write_sym

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

let pomsetpt_suite =
  "PomsetPT formula operations" >::: [
    "test_convert_dnf (base cases)" >:: test_convert_dnf_simple
  ; "test_convert_dnf (idempotent cases)" >:: test_convert_dnf1
  ; "test_convert_dnf" >:: test_convert_dnf2
  ]
