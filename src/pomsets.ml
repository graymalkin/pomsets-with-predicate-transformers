open ASTToPomsetPT

let print_latex = ref false
let print_size = ref false
let print_time = ref false

(** Entry point *)
let run filename =
  let config, ast, _outcomes = Parse.parse filename in
  let config = Util.default RunConfig.default_configuration config in
  let vs = config.RunConfig.values in
  let ps = PomsetPT.interp vs (PomsetPT.Tid 0) (convert_program ast) in
  if !print_size
  then Printf.printf "%d pomsets\n" (List.length ps);
  if !print_latex
  then PrintLatexDoc.pp_document Format.std_formatter config ast [];
  if !print_time
  then Printf.printf "Execution time: %fs\n" (Sys.time ());
  ()

let args = Arg.align [
  ("--size", Arg.Set print_size, "  Print the number of completed pomsets [default: false]")
; ("--tex", Arg.Set print_latex, "  Use LaTeX output [default: false]")
; ("--time", Arg.Set print_time, "  Show execution time [default: false]")
]

let usage () =
  Format.sprintf "%s [OPTIONS] <FILENAME>" (Array.get Sys.argv 0)

let () = Arg.parse args run (usage ())
