(** === Program entry point. ===
  Arguments are intepretted using the standard OCaml Args module, args set ref cell flags listed at the top of this file.
  pomsetpt takes the output of the parser and runs the pomsetpt semantics over it.
 *)

open PomsetPT

let print_latex = ref false
let print_size = ref false
let print_time = ref false

let check_outcome env = 
  let trans_env r = let Val v = env (Reg r) in v in
  function
    AST.Allowed (bexpr, _, _) -> AST.eval_bexpr (trans_env) bexpr
  | AST.Forbidden (bexpr, _, _) -> not (AST.eval_bexpr (trans_env) bexpr)

let pomsetpt (config, ast, outcomes) = 
  let config = Util.default RunConfig.default_configuration config in
  let vs = config.RunConfig.values in
  let ps = interp vs (ASTToPomsetPT.convert_program ast) in
  ignore @@ Util.maybe (List.iter (fun o ->
    if not @@ List.exists (fun p -> check_outcome p.smap o) ps
    then Printf.printf "F"
    else Printf.printf "."
  )) outcomes;
  if !print_size
  then Printf.printf "%d pomsets\n" (List.length ps);
  if !print_latex
  then PrintLatexDoc.pp_document Format.std_formatter config ast [];
  if !print_time
  then Printf.printf "Execution time: %fs\n" (Sys.time ());
  ()

let run_f f = pomsetpt (Parse.parse_file f)

let run_s s = pomsetpt (Parse.parse_string s)

let args = Arg.align [
  ("--log", Arg.String Util.set_log_level, "  Set the log level as one of {all, debug, warn, error, none} [default: none]")
; ("--log-time", Arg.Set Util.log_times, "  Include time stamps in log output [default: false]")
; ("--program", Arg.Rest run_s, "  Interpret a program from the command line.")
; ("--size", Arg.Set print_size, "  Print the number of completed pomsets [default: false]")
; ("--tex", Arg.Set print_latex, "  Use LaTeX output [default: false]")
; ("--time", Arg.Set print_time, "  Show execution time [default: false]")
]

let usage () =
  Format.sprintf "%s [OPTIONS] <FILENAME>" (Array.get Sys.argv 0)

let () = Arg.parse args run_f (usage ())
