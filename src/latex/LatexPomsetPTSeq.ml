open Preliminaries
open PomsetPTSeq

open LatexCommon

let rec pp_latex_expr fmt = function
  V (Val v) -> Format.fprintf fmt "%d" v
| R (Reg r) -> Format.fprintf fmt "%s" r
| Add (e1, e2) -> Format.fprintf fmt "%a + %a" pp_latex_expr e1 pp_latex_expr e2
| Sub (e1, e2) -> Format.fprintf fmt "%a - %a" pp_latex_expr e1 pp_latex_expr e2
| Mul (e1, e2) -> Format.fprintf fmt "(%a * %a)" pp_latex_expr e1 pp_latex_expr e2
| Div (e1, e2) -> Format.fprintf fmt "(%a / %a)" pp_latex_expr e1 pp_latex_expr e2
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
  | Expr (Eq (e1, e2))
  | EqExpr (e1, e2) -> Format.fprintf fmt "(%a = %a)" pp_latex_expr e1 pp_latex_expr e2
  | f -> Debug.debug "unknown latex print"; Format.fprintf fmt "%a" pp_formula f
  in
  (* let f = simp_formula f in *)
  go fmt f

let pp_latex_mem_ref fmt (Ref x) = Format.fprintf fmt "%s" x

let pp_latex_val fmt (Val v) = Format.fprintf fmt "%d" v

let pp_latex_mode fmt = function
  Rlx -> Format.fprintf fmt "\\mRLX"
| Rel -> Format.fprintf fmt "\\mREL"
| Acq -> Format.fprintf fmt "\\mACQ"
| SC -> Format.fprintf fmt "\\mSC"

let pp_latex_label fmt = function
  Init ->
  Format.fprintf fmt "\\texttt{init}"
| Read (o, g, v) -> 
  Format.fprintf fmt "\\DR[%a]{%a}[]{%a}[]" pp_latex_mode o pp_latex_mem_ref g pp_latex_val v
| Write (o, g, v) -> 
  Format.fprintf fmt "\\DW[%a]{%a}[]{%a}[]" pp_latex_mode o pp_latex_mem_ref g pp_latex_val v
| Fence (o) ->
  Format.fprintf fmt "\\DR[]{%a}[]" pp_latex_mode o

let pp_pomset_node ?style:(s="event") lab pre fmt e = 
  if tautology (sub_quis True pre)
  then Format.fprintf fmt "\\node[label={[style=lableft]%d}] (%d) [style=%s] {$%a$};" e e s pp_latex_label lab
  else Format.fprintf fmt "\\node[label={[style=lableft]%d}] (%d) [style=%s] {$%a \\mid  %a$};" e e s pp_latex_formula pre pp_latex_label lab
  
(* prints inner part of pomset tikz picture. *)
let pp_tikz_pomset fmt p = 
  Format.fprintf fmt "%% Real events\n";
  List.iter (fun e ->
    Format.fprintf fmt "%a\n" (pp_pomset_node (p.lab e) (p.pre e)) e
  ) (real_events p);

  Format.fprintf fmt "%% Phantom events\n";
  List.iter (fun e ->
    let e' = snd (List.find (fun (x, _) -> x = e) p.pi) in
    Format.fprintf fmt "%a\n" (pp_pomset_node ~style:"phevent" (p.lab e') (p.pre e')) e
  ) (List.sort_uniq (-) (phantom_events p));

  Format.fprintf fmt "%% Dependency order\n";
  List.iter (fun (a, b) ->
    Format.fprintf fmt "\\draw (%d) edge[style=sync] (%d);\n" a b
  ) (display_order p.ord);

  Format.fprintf fmt "%% Program order\n";
  List.iter (fun (a, b) ->
    let edge_type =
      if (List.mem a (phantom_events p) && List.mem b (phantom_events p)) || List.mem a (real_events p) && List.mem b (real_events p)
      then "draw"
      else "path"
    in
    Format.fprintf fmt "\\%s (%d) edge[style=pox, bend left] (%d);\n" edge_type a b
  ) (display_order p.po);

  Format.fprintf fmt "%% pi\n";
  List.iter (fun (a, b) ->
    Format.fprintf fmt "\\path (%d) edge[style=xo] (%d);\n" a b
  ) (display_order p.pi)

let pp_pomset fmt p = 
  Format.fprintf fmt "\\begin{verbatim}\n";
  Format.fprintf fmt "%a" pp_pomset p;
  Format.fprintf fmt "\\end{verbatim}\n";
  Format.fprintf fmt "%a\n" (pp_tikz_diagram pp_tikz_pomset ~options:[
      "sibling distance=1.5em"
    ; "scale=1.5" 
    ; "binary tree layout"
    ; "grow=right"
    ]) p;
  Format.fprintf fmt "\\aTerm = $ %a $\n\n" pp_latex_formula p.term;
  Format.fprintf fmt "Complete: %b\n\n" (complete { p with pre = (fun e -> sub_quis True (p.pre e)); } );
  Format.fprintf fmt "\\noindent\\rule{6cm}{0.4pt}\n\n"
