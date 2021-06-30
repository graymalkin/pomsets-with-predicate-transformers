open Relation

let pp_tikz_diagram pp_diagram ?options:(opts=["node distance=1.5em"; "binary tree layout"]) fmt d =
  Format.fprintf fmt "\\begin{center}\n";
  Format.fprintf fmt "\\begin{tikzpicture}[%s]\n" (String.concat "," opts);
  Format.fprintf fmt "%a" pp_diagram d;
  Format.fprintf fmt "\\end{tikzpicture}\n";
  Format.fprintf fmt "\\end{center}\n"

let display_order r = 
  r |> List.filter (fun (a, b) -> a <> b) 
    |> List.sort compare
    |> transitive_reduction
    |> List.rev
