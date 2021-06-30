let pp_document fmt config _ast pomset_printer ps =
  Format.fprintf fmt "\\title{%s}\n" config.RunConfig.name;
  Format.fprintf fmt "\\begin{document}\n";
  Format.fprintf fmt "\\maketitle\n";
  (* Format.fprintf fmt "\\section{Program}\n";
  Format.fprintf fmt "\\[ %a\n \\] \n\n" LatexAST.pp_tex_ast ast; *)
  Format.fprintf fmt "\\section{Completed Pomsets}\n";
  List.iter (Format.fprintf Format.std_formatter "%a \n\n" pomset_printer) ps;
  Format.fprintf fmt "\\end{document}\n";
