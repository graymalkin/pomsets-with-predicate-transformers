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
