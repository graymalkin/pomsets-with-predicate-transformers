(**
  Record for the run config. This is filled in from the .lit file by the parser.
 *)

open AST
open Relation

type t = {
  name : string
; values : value set
; comment : string option
}

let default_configuration = {
  name = "(litmus test)";
  values = [0; 1];
  comment = Some "default configuration"
}
