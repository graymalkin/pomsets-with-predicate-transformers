open AST

let rec pp_latex_expr fmt = function
    Number n -> Format.fprintf fmt "%d" n
  | Register r -> Format.fprintf fmt "\\texttt{%s}" r
  | Multiplication (l, r) -> Format.fprintf fmt "%a * %a" pp_latex_expr l pp_latex_expr r
  | Division (l, r) -> Format.fprintf fmt "%a / %a" pp_latex_expr l pp_latex_expr r
  | Addition (l, r) -> Format.fprintf fmt "(%a + %a)" pp_latex_expr l pp_latex_expr r
  | Subtraction (l, r) -> Format.fprintf fmt "(%a - %a)" pp_latex_expr l pp_latex_expr r

let rec pp_latex_bexpr fmt = function
    Equality (e1, e2) ->
    Format.fprintf fmt "%a = %a" pp_latex_expr e1 pp_latex_expr e2
  | Gt (e1, e2) ->
    Format.fprintf fmt "%a > %a" pp_latex_expr e1 pp_latex_expr e2
  | Lt (e1, e2) ->
    Format.fprintf fmt "%a < %a" pp_latex_expr e1 pp_latex_expr e2
  | Gte (e1, e2) ->
    Format.fprintf fmt "%a \\geq %a" pp_latex_expr e1 pp_latex_expr e2
  | Lte (e1, e2) ->
    Format.fprintf fmt "%a \\leq %a" pp_latex_expr e1 pp_latex_expr e2
  | Conjunction (b1, b2) ->
    Format.fprintf fmt "(%a \\wedge %a)" pp_latex_bexpr b1 pp_latex_bexpr b2
  | Disjunction (b1, b2) ->
    Format.fprintf fmt "(%a \\vee %a)" pp_latex_bexpr b1 pp_latex_bexpr b2
  | Negation b ->
    Format.fprintf fmt "\\neg (%a)" pp_latex_bexpr b
