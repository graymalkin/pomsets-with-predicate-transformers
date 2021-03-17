let pp_document fmt config ast ps =
  Format.fprintf fmt "\\title{%s}\n" config.RunConfig.name;
  Format.fprintf fmt "\\begin{document}\n";
  Format.fprintf fmt "\\maketitle\n";
  Format.fprintf fmt "\\section{Program}\n";
  Format.fprintf fmt "\\[ %a\n \\] \n\n" LatexAST.pp_tex_ast ast;
  List.iter (Format.fprintf Format.std_formatter "%a \n\n" LatexPomset.pp_pomset) ps;
  Format.fprintf fmt "\\end{document}\n";
