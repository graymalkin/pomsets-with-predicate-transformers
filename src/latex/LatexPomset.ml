open Pomset

open LatexCommon

let pp_latex_label fmt = function
  Read (g, v) -> Format.fprintf fmt "R (%s, %d)" g v
| Write (g, v) -> Format.fprintf fmt "W (%s, %d)" g v

let pp_pomset_node lab fmt e =
  lab e |> function
    Read (l, v) -> Format.fprintf fmt "\\node [style=basic] (%d) {\\readcmd{%s}{%d}};" e l v
  | Write (l, v) -> Format.fprintf fmt "\\node [style=basic] (%d) {\\writecmd{%s}{%d}};" e l v

(* prints inner part of pomset tikz picture. *)
let pp_tikz_pomset fmt {evs; lab; ord} = 
  List.iter (fun e ->
    Format.fprintf fmt "%a\n" (pp_pomset_node lab) e
  ) (List.rev evs);
  List.iter (fun (a, b) ->
    Format.fprintf fmt "\\draw (%d) edge[style=po] (%d);\n" a b
  ) (display_order ord)

let pp_pomset fmt ps = 
  Format.fprintf fmt "%a\n" (pp_tikz_diagram pp_tikz_pomset ~options:["tree layout"; "grow=0"] ) ps
