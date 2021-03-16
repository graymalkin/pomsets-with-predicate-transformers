open PomsetPreconditions

let print_latex = ref false

(** Entry point *)
let run filename =
  let config, ast, _outcomes = Parse.parse filename in
  let config = Util.default RunConfig.default_configuration config in
  let vs = config.RunConfig.values in
  let ps = Pomset.interp vs ast in
  PrintLatexDoc.pp_document Format.std_formatter config ast ps

let args = Arg.align [
  ("--tex", Arg.Set print_latex, "  Use LaTeX output [default: false]")
]

let usage () =
  Format.sprintf "%s [OPTIONS] <FILENAME>" (Array.get Sys.argv 0)

let () = Arg.parse args run (usage ())
