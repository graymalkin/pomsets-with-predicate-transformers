open Preliminaries
open PomsetPTSeq

open LatexCommon

let rec pp_latex_expr fmt = function
  V (Val v) -> Format.fprintf fmt "%d" v
| R (Reg r) -> Format.fprintf fmt "%s" r
| Eq (e1, e2) -> Format.fprintf fmt "(%a = %a)" pp_latex_expr e1 pp_latex_expr e2
| Gt (e1, e2) -> Format.fprintf fmt "(%a \\gt %a)" pp_latex_expr e1 pp_latex_expr e2
| Gte (e1, e2) -> Format.fprintf fmt "(%a \\geq %a)" pp_latex_expr e1 pp_latex_expr e2
| Lt (e1, e2) -> Format.fprintf fmt "(%a \\lt %a)" pp_latex_expr e1 pp_latex_expr e2
| Lte (e1, e2) -> Format.fprintf fmt "(%a \\leq %a)" pp_latex_expr e1 pp_latex_expr e2

let pp_latex_formula fmt f =
  let rec go fmt = function
    And (f1, f2) -> Format.fprintf fmt "%a \\wedge %a" go f1 go f2
  | Or (f1, f2) -> Format.fprintf fmt "%a \\vee %a" go f1 go f2
  | Implies (f1, f2) -> Format.fprintf fmt "%a \\implies %a" go f1 go f2
  | Not f -> Format.fprintf fmt "\\neg (%a)" go f
  | True -> Format.fprintf fmt "\\TRUE"
  | False -> Format.fprintf fmt "\\FALSE"
  | EqExpr (e1, e2) -> Format.fprintf fmt "(%a = %a)" pp_latex_expr e1 pp_latex_expr e2
  | _ -> ()
  in
  let f = simp_formula f in
  go fmt f

let pp_latex_mem_ref fmt (Ref x) = Format.fprintf fmt "%s" x

let pp_latex_val fmt (Val v) = Format.fprintf fmt "%d" v

let pp_latex_mode fmt = function
  Rlx -> Format.fprintf fmt "\\mRLX"
| Rel -> Format.fprintf fmt "\\mREL"
| Acq -> Format.fprintf fmt "\\mACQ"
| SC -> Format.fprintf fmt "\\mSC"

let pp_latex_label fmt = function
  Read (o, g, v) -> 
  Format.fprintf fmt "\\DR[%a]{%a}[]{%a}[]" pp_latex_mode o pp_latex_mem_ref g pp_latex_val v
| Write (o, g, v) -> 
  Format.fprintf fmt "\\DW[%a]{%a}[]{%a}[]" pp_latex_mode o pp_latex_mem_ref g pp_latex_val v
| Fence (o) ->
  Format.fprintf fmt "\\DR[]{%a}[]" pp_latex_mode o

let pp_pomset_node lab pre fmt e = 
  if simp_formula (pre e) = True
  then Format.fprintf fmt "\\node (%d) [style=event] {$%a$};" e pp_latex_label (lab e)
  else Format.fprintf fmt "\\node (%d) [style=event] {$%a \\mid  %a$};" e pp_latex_formula (pre e) pp_latex_label (lab e)
  
(* prints inner part of pomset tikz picture. *)
let pp_tikz_pomset fmt p = 
  List.iter (fun e ->
    Format.fprintf fmt "%a\n" (pp_pomset_node p.lab p.pre) e
  ) p.evs;
  List.iter (fun (a, b) ->
    Format.fprintf fmt "\\draw (%d) edge[style=sync] (%d);\n" a b
  ) (display_order p.ord)

let pp_pomset fmt p = 
  Format.fprintf fmt "%a\n" (pp_tikz_diagram pp_tikz_pomset ~options:[
      "sibling distance=1.5em"
    ; "binary tree layout"
    ; "grow=right"
    ]) p;
  Format.fprintf fmt "\\aTerm = $ %a $\n\n" pp_latex_formula p.term;
  Format.fprintf fmt "\\noindent\\rule{6cm}{0.4pt}\n\n"