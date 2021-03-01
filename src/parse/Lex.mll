{
open Scanf
open Parser
module B = Buffer
exception Syntax_error of string
exception Lexing_error of string

let position lexbuf =
    let open Lexing in
    let p = lexbuf.lex_curr_p in
        Format.sprintf "%s:%d:%d" 
        p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol)

let error lexbuf fmt = 
    Printf.kprintf (fun msg -> 
        raise (Lexing_error ((position lexbuf)^" "^msg))) fmt

}

let register = 'r'['a'-'z' 'A'-'Z' '0'-'9']*
let global_ptr = 'p'['0'-'9']*
let global = ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '0'-'9']*
let ws = [' ' '\t' '\r']+
let num = ['0'-'9']+

rule token = parse
  | ws { token lexbuf }
  | "//" [^ '\n']* { token lexbuf }
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '[' { LSPAREN }
  | ']' { RSPAREN }
  | '{' { LBRACE }
  | '}' { RBRACE }
  | ":=" { ASSIGN }
  | "=" { EQUAL }
  | "≡" { EQUAL }
  | "&&" { AND }
  | "∧" { AND }
  | "||" { OR }
  | "∨" { OR }
  | "!" { NOT }
  | "¬" { NOT }
  | "*" { TIMES }
  | "/" { DIVIDE }
  | "+" { PLUS }
  | "-" { MINUS }
  | ">" { GT }
  | "<" { LT }
  | ">=" { GTE }
  | "≥" { GTE }
  | "<=" { LTE }
  | "≤" { LTE }
  | ';' { SEMICOLON }
  | "|||" { PARALLEL }
  | "." { DOT }
  | '"' { QUOTED_STRING (string (B.create 100) lexbuf) }
  | "if" { IF }
  | "else" { ELSE }
  | "do" { DO }
  | "while" { WHILE }
  | "load" { LD }
  | "store" { ST }
  | "FADD" { FADD }
  | "fence" { FENCE }
  | "na" { NONATOMIC }
  | "nonatomic" { NONATOMIC }
  | "rlx" { RELAXED }
  | "relaxed" { RELAXED }
  | "acq" { ACQUIRE }
  | "acquire" { ACQUIRE }
  | "rel" { RELEASE }
  | "release" { RELEASE }
  | "sc" { SC }
  | "sequentially_consistent" { SC }
  | "white-picket" { WHITEPICKET }
  | "rel" { RELEASE }
  | "exclusive" { EXCLUSIVE }
  | "ex" { EXCLUSIVE }
  | "not-exclusive" { NOT_EXCLUSIVE }
  | "not-ex" { NOT_EXCLUSIVE }
  | "strong" { STRONG }
  | "normal" { NORMAL }
  | "lock" { LOCK }
  | "unlock" { UNLOCK }
  | "skip" { SKIP }
  | "print" { PRINT }
  | "%%" { CONF_SEP }
  | "," { COMMA }
  | "name" { NAME }
  | "values" { VALUES }
  | "comment" { COMMENT }
  | "allow" { ALLOW }
  | "forbid" { FORBID }
  | num as x { INT (sscanf x "%d" (fun x->x)) }
  | register as x { REGISTER x }
  | global as x { GLOBAL x }
  | eof { EOF }
  | _ { raise (Syntax_error (Lexing.lexeme lexbuf)) }
and string buf = parse
| [^'"' '\n' '\\']+ 
            { B.add_string buf @@ Lexing.lexeme lexbuf
            ; string buf lexbuf 
            }
| '\n'      { B.add_string buf @@ Lexing.lexeme lexbuf
            ; Lexing.new_line lexbuf
            ; string buf lexbuf
            }
| '\\' '"'  { B.add_char buf '"'
            ; string buf lexbuf
            }
| '\\'      { B.add_char buf '\\'
            ; string buf lexbuf
            }
| '"'       { B.contents buf } (* return *)
| eof       { error lexbuf "end of input inside of a string" }
| _         { error lexbuf 
                "found '%s' - don't know how to handle" @@ Lexing.lexeme lexbuf }
