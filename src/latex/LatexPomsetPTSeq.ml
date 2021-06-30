open Preliminaries
open PomsetPTSeq

open LatexCommon

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

let pp_pomset_node lab fmt e = 
  Format.fprintf fmt "\\node (%d) [style=event] {$\\mathstrut %a$};" e pp_latex_label (lab e)
  
(* prints inner part of pomset tikz picture. *)
let pp_tikz_pomset fmt p = 
  List.iter (fun e ->
    Format.fprintf fmt "%a\n" (pp_pomset_node p.lab) e
  ) p.evs;
  List.iter (fun (a, b) ->
    Format.fprintf fmt "\\draw (%d) edge[style=sync] (%d);\n" a b
  ) (display_order p.ord)

let pp_pomset fmt = 
  Format.fprintf fmt "%a\n" (pp_tikz_diagram pp_tikz_pomset ~options:[
      "sibling distance=1.5em"
    ; "binary tree layout"
    ; "grow=right"
    ])