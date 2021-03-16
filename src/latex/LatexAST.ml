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

let pp_tex_ast fmt ast =
  let rec go fmt = function
    Skip -> Format.fprintf fmt "\\done"
  | Assign (r, e) -> Format.fprintf fmt "\\assign[]{%a}{%a}" pp_register r pp_expr e
  (* TODO : Print rmw_strength / exclusivity *)
  | Load (r, g, a, _) -> Format.fprintf fmt "\\assign[%a]{%s}{%s}" pp_ordering a r (show_global g)
  | Store (g, e, a, _) -> Format.fprintf fmt "\\assign[%a]{%s}{%a}" pp_ordering a (show_global g) pp_expr e
  | Fadd (r, g, rs, o_r, o_w, e) ->
     Format.fprintf fmt "\\assign[]{%a}\\texttt{FADD}(%a, %a, %a, %a, %a)"
                                       pp_register r
                                       pp_global g
                                       pp_rmw_strength rs
                                       pp_ordering o_r
                                       pp_ordering o_w
                                       pp_expr e
  | Cas (r, g, o_r, o_w, e1, e2) ->
     Format.fprintf fmt "\\assign[]{%a}\\texttt{CAS}(%a, %a, %a, %a, %a)"
                    pp_register r
                    pp_global g
                    pp_ordering o_r
                    pp_ordering o_w
                    pp_expr e1
                    pp_expr e2

  | Sequence (p1, p2) ->
     Format.fprintf fmt "%a \\sequencing \\\\ \n %a" go p1 go p2

  | Parallel _ as prog ->
     let ps = list_of_pars prog in
     let cols = (List.length ps * 2) - 1 in
     let cols_spec = String.concat "" (Util.repeat "c" cols) in
     Format.fprintf fmt "\\begin{array}{%s}\n" cols_spec;
     let pp_colsep fmt () = Format.fprintf fmt "\n& || &\n  " in
     Fmt.list ~sep:pp_colsep go fmt ps;
     Format.fprintf fmt "\n\\end{array}"
  | Conditional (c, p1, p2) -> (
    match p2 with
        Skip -> Format.fprintf fmt "\\ifthen{%a}{%a}" pp_boolean_expr c go p1
      | _ -> Format.fprintf fmt "\\ifthenelse{%a}{%a}{%a}" pp_boolean_expr c go p1 go p2)
  | While (c, p1) ->
    Format.fprintf fmt "\\while{%a}{%a}" pp_boolean_expr c go p1
  | Fence o -> Format.fprintf fmt "\\fencecmd{\\textsc{%a}}" pp_ordering o
  | Print e -> Format.fprintf fmt "print\ %a" pp_expr e
  | Lock -> Format.fprintf fmt "\\texttt{lock}"
  | Unlock -> Format.fprintf fmt "\\texttt{unlock}"
  in
  Format.fprintf fmt "%a" go ast