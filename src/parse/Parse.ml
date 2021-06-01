(**
  Utilities for interfacing with the Menhir generated parser. See Parser.mly for the grammar, and Lex.mll for the list of tokens.
 *)

let show_position lexbuf =
  let {
      Lexing.pos_lnum=line;
      Lexing.pos_bol=c0;
      Lexing.pos_fname=filename;
      Lexing.pos_cnum=c1
    } = Lexing.lexeme_start_p lexbuf
  in
  Format.sprintf "%s:%d:%d" filename line (c1-c0+1)

let parse lexbuf =
  match Parser.top Lex.token lexbuf with
  | r -> r
  | exception (Lex.Syntax_error s) ->
    failwith (Printf.sprintf "%s: parse error\nUnexpected token: %s" (show_position lexbuf) s)
  | exception Parser.Error ->
    failwith (Printf.sprintf "%s: parse error" (show_position lexbuf))

let parse_file filename =
  let f = open_in filename in
  Util.defer_close_in_noerr f parse (Lexing.from_channel f) 

let parse_string s = parse (Lexing.from_string s)
