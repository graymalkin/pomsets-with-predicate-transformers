open AST
open Relation

type t = {
  name : string
; values : value set
; comment : string option
}

type solver =
    SolveQbf
  | SolveSO

let solver_of_string = function
    "qbf" -> Some SolveQbf
  | "so" -> Some SolveSO
  | "none" -> None
  | s -> raise (Invalid_argument s)

let show_solver = function
    Some SolveQbf -> "qbf"
  | Some SolveSO -> "so"
  | None -> "none"

module type Configuration = sig
  val name : string
  val values : value set
  val comment : string option
  val go : bool

  val check : bool
  val enumerate : bool
  val closed_program : bool
  val verbose : bool
  val max_steps : int
  
  val pp_ast : bool
  val pp_denotion : bool
  val pp_tex : bool
  val json_output : bool

  val filename : string
end
