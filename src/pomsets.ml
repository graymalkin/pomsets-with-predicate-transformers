(** === Program entry point. ===
  Arguments are intepretted using the standard OCaml Args module, args set ref cell flags listed at the top of this file.
  pomsetpt takes the output of the parser and runs the pomsetpt semantics over it.
 *)

let print_latex = ref false
let print_size = ref false
let print_time = ref false

let pomsetpt (config, ast, _outcomes) = 
  let config = Util.default RunConfig.default_configuration config in
  let vs = config.RunConfig.values in
  let ps = PomsetPT.interp vs (PomsetPT.Tid 0) (ASTToPomsetPT.convert_program ast) in
  if !print_size
  then Printf.printf "%d pomsets\n" (List.length ps);
  if !print_latex
  then PrintLatexDoc.pp_document Format.std_formatter config ast [];
  if !print_time
  then Printf.printf "Execution time: %fs\n" (Sys.time ());
  ()

let check_outcomes p = function
  AST.Allowed (bexpr, expcts, comment) ->
  ()
  | _ -> raise Util.Not_implemented

let run_f f = pomsetpt (Parse.parse_file f)

let run_s s = pomsetpt (Parse.parse_string s)

let args = Arg.align [
  ("--log", Arg.String Util.set_log_level, "  Set the log level as one of {all, debug, warn, error, none} [default: none]")
; ("--size", Arg.Set print_size, "  Print the number of completed pomsets [default: false]")
; ("--tex", Arg.Set print_latex, "  Use LaTeX output [default: false]")
; ("--time", Arg.Set print_time, "  Show execution time [default: false]")
; ("--program", Arg.Rest run_s, "  Interpret a program from the command line.")
]

let usage () =
  Format.sprintf "%s [OPTIONS] <FILENAME>" (Array.get Sys.argv 0)

let () = Arg.parse args run_f (usage ())
