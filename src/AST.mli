type register = string
type global = string
type value = int
type comment = string

module Satisfaction_map : Map.S with type key = int

type ordering =
    NonAtomic
  | Relaxed
  | Acquire
  | Release
  | SC

type expr =
    Number of int
  | Register of register
  | Multiplication of expr * expr
  | Division of expr * expr
  | Addition of expr * expr
  | Subtraction of expr * expr

type boolean_expr =
    Equality of expr * expr
  | Gt of expr * expr
  | Lt of expr * expr
  | Gte of expr * expr
  | Lte of expr * expr
  | Conjunction of boolean_expr * boolean_expr
  | Disjunction of boolean_expr * boolean_expr
  | Negation of boolean_expr

(* Required for IMM *)
type exclusivity = Exclusive | NotExclusive
type rmw_strength = Normal | Strong

type ast =
    Skip
  | Assign of register * expr
  | Load of register * global * ordering * exclusivity
  | Store of global * expr * ordering * rmw_strength
  | Fadd of register * global * rmw_strength * ordering * ordering * expr
  | Cas of register * global * ordering * ordering * expr * expr
  | Sequence of ast * ast
  | Parallel of ast * ast
  | Conditional of boolean_expr * ast * ast
  | While of boolean_expr * ast
  | Fence of ordering
  | Print of expr
  | Lock
  | Unlock

type expected_outcome =
    Allow of string
  | Forbid of string

type outcome =
    Allowed of boolean_expr * expected_outcome list * comment option
  | Forbidden of boolean_expr * expected_outcome list * comment option

val eval_bexpr : (register -> value) -> boolean_expr -> bool
val registers_of_bexpr : boolean_expr -> register list
val eval_expr : (register -> value) -> expr -> value
val registers_of_expr : expr -> register list

val equal_value : value -> value -> bool
val equal_register : register -> register -> bool
val equal_global : global -> global -> bool
val equal_ordering : ordering -> ordering -> bool
val equal_exclusivity : exclusivity -> exclusivity -> bool
val equal_rmw_strength : rmw_strength -> rmw_strength -> bool

val pp_value: Format.formatter -> value -> unit
val pp_register: Format.formatter -> register -> unit
val pp_global: Format.formatter -> global -> unit
val pp_exclusivity : Format.formatter -> exclusivity -> unit
val pp_rmw_strength : Format.formatter -> rmw_strength -> unit
val pp_ordering: Format.formatter -> ordering -> unit
val pp_boolean_expr: Format.formatter -> boolean_expr -> unit
val pp_outcome : Format.formatter -> outcome -> unit
val pp_expr: Format.formatter -> expr -> unit
val pp_ast : Format.formatter -> ast -> unit

val list_of_pars : ast -> ast list

val satisfies : int list -> (register * value) Satisfaction_map.t -> boolean_expr -> bool
