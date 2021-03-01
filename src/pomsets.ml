(** Entry point *)
let run filename =
  let _config, ast, _outcomes = Parse.parse filename in
  Format.fprintf Format.std_formatter "%a\n" AST.pp_ast ast;
  ignore @@ Interp.interp ast;
  ()

let args = Arg.align []

let usage () =
  Format.sprintf "%s [OPTIONS] <FILENAME>" (Array.get Sys.argv 0)

let () = Arg.parse args run (usage ())
