open AST

let pp_latex_ordering fmt = function
  Relaxed -> Format.fprintf fmt "\\mRLX"
| Release -> Format.fprintf fmt "\\mREL"
| Acquire -> Format.fprintf fmt "\\mACQ"
| SC -> Format.fprintf fmt "\\mSC"
| NonAtomic -> ()


let rec pp_latex_expr fmt = function
    Number n -> Format.fprintf fmt "%d" n
  | Register r -> Format.fprintf fmt "%s" r
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
  | Assign (r, e) -> Format.fprintf fmt "\\LET{%a}{%a}" pp_register r pp_expr e
  (* TODO : Print rmw_strength / exclusivity *)
  | Load (r, g, a, _) -> Format.fprintf fmt "\\PR[%a]{%s}{%s}" pp_latex_ordering a g r
  | Store (g, e, a, _) -> Format.fprintf fmt "\\PW[%a]{%s}{%a}" pp_latex_ordering a g pp_expr e
  | Sequence (p1, p2) -> Format.fprintf fmt "%a \\SEMI %a" go p1 go p2
  | Conditional (c, p1, p2) -> (
    match p2 with
        Skip -> Format.fprintf fmt "\\IF{%a} \\THEN{%a} \\FI" pp_latex_bexpr c go p1
      | _ -> Format.fprintf fmt "\\IF{%a} \\THEN{%a} \\ELSE{%a} \\FI" pp_latex_bexpr c go p1 go p2)
  | Fence o -> Format.fprintf fmt "\\fencecmd{\\textsc{%a}}" pp_ordering o
  | Parallel (p1, p2) -> Format.fprintf fmt "(%a) \\; \\; || \\; \\; (%a)" go p1 go p2
  | _ -> raise Util.Not_implemented
  in
  Format.fprintf fmt "%a" go ast
