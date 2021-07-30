open OUnit2

open Pomsets

type result = Pass | Fail

let run_test filename =
  let (config, ast, outcomes) = Parse.parse_file filename in
  let config = Option.value ~default:RunConfig.default_configuration config in
  let vs = config.RunConfig.values in
  let ps = PomsetPTSeq.interp vs true (ASTToPomsetPTSeq.convert_program ast) in
  let rc11_consistent = List.flatten @@ List.map Rc11.gen_rc11_exns (dedup ps) in
  let results = Option.map (List.map (function
    (AST.Allowed (_b,_os,_c) as o)
  | (AST.Forbidden (_b,_os,_c) as o) -> 
    if check o (List.map (fun (p,_,_) -> p) rc11_consistent)
    then Pass
    else Fail
  )) outcomes
  in
  if List.for_all ((=) Pass) (Option.get results)
  then Pass
  else Fail

let test_file f _ = assert_equal Pass (run_test f)

let jctc_short_tests = 
  "PomsetPT Short Java Causality Tests" >::: [
    "jctc1" >:: test_file "../data/tests/jctc/jctc1.lit"
  ; "jctc2" >:: test_file "../data/tests/jctc/jctc2.lit"
  (* ; "jctc3" >:: test_file "../data/tests/jctc/jctc3.lit" *)
  ; "jctc4" >:: test_file "../data/tests/jctc/jctc4.lit"
  (* ; "jctc5" >:: test_file "../data/tests/jctc/jctc5.lit" *)
  ; "jctc6" >:: test_file "../data/tests/jctc/jctc6.lit"
  (* ; "jctc7" >:: test_file "../data/tests/jctc/jctc7.lit" *)
  (* ; "jctc8" >:: test_file "../data/tests/jctc/jctc8b.lit" *)
  (* ; "jctc9" >:: test_file "../data/tests/jctc/jctc9b.lit" *)
  (* ; "jctc10" >:: test_file "../data/tests/jctc/jctc10.lit" *)
  (* ; "jctc11" >:: test_file "../data/tests/jctc/jctc11.lit" *)
  ]
