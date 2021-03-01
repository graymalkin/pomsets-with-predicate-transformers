let show_position lexbuf =
  let {
      Lexing.pos_lnum=line;
      Lexing.pos_bol=c0;
      Lexing.pos_fname=filename;
      Lexing.pos_cnum=c1
    } = Lexing.lexeme_start_p lexbuf
  in
  Format.sprintf "%s:%d:%d" filename line (c1-c0+1)
 
let parse filename =
  let f = open_in filename in
  let lexbuf = Lexing.from_channel f in
  match Parser.top Lex.token lexbuf with
  | r ->
    close_in_noerr f; r
  | exception (Lex.Syntax_error s) ->
    failwith (Printf.sprintf "%s: parse error\nUnexpected token: %s" (show_position lexbuf) s)
  | exception Parser.Error ->
    failwith (Printf.sprintf "%s: parse error" (show_position lexbuf))
