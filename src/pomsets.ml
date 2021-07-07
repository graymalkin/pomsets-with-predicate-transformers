(** === Program entry point. ===
  Arguments are intepretted using the standard OCaml Args module, args set ref cell flags listed at the top of this file.
  pomsetpt takes the output of the parser and runs the pomsetpt semantics over it.
 *)

open Preliminaries
open PomsetPTSeq
open PPRelation

open Util

let check_outcomes = ref false
let check_complete = ref false
let print_latex = ref false
let print_pomsets = ref false
let print_size = ref false
let print_time = ref false

let check_outcome env bexpr = 
  let trans_env r = let Val v = env (Reg r) in v in
  AST.eval_bexpr (trans_env) bexpr

let check = function 
  AST.Allowed (bexpr, _, _) -> List.exists (fun p -> check_outcome p.smap bexpr)
| AST.Forbidden (bexpr, _, _) -> List.for_all (fun p -> 
  let r = not (check_outcome p.smap bexpr) in
  if not r then (
    List.iter (fun e ->
      Debug.debug "Event: [%d : %a], pre e = %a, tautology (pre e) = %b\n%!"
        e
        pp_action (p.lab e)
        pp_formula (p.pre e)
        (tautology (sub_quis True (p.pre e)))
    ) p.evs;
    Debug.debug "term = %a, tautology (term) = %b\n%!"
      pp_formula p.term
      (tautology p.term);
    Debug.debug "%a\n" PomsetPTSeq.pp_pomset p
  );
  r
)

let dedup ps = 
  List.sort_uniq (fun p1 p2 -> 
    let phlab p e = 
      let e' = snd (List.find (fun (x, _) -> x = e) p.pi) in
      p.lab e'
    in
    let lcmp = compare 
      ((List.map (phlab p1) (phantom_events p1)) @ (List.map p1.lab (simple_events p1))) 
      ((List.map (phlab p2) (phantom_events p2)) @ (List.map p2.lab (simple_events p2))) 
    in
    if lcmp = 0
    then compare p1.ord p2.ord
    else lcmp
  ) ps

let pomsetpt (config, ast, outcomes) = 
  let config = Option.value ~default:RunConfig.default_configuration config in
  let vs = config.RunConfig.values in
  info "Setup complete\n%!";
  let ps = interp vs !check_complete (ASTToPomsetPTSeq.convert_program ast) in
  info "Interpretation complete\n%!";
  if !print_size then Format.printf "%d pomsets (%d after deduping)\n" (List.length ps) (List.length (dedup ps));
  if !print_latex then 
    PrintLatexDoc.pp_document Format.std_formatter config ast LatexPomsetPTSeq.pp_pomset (dedup ps);
  info "Checking RC11 consistency\n%!";
  if !check_complete
  then
  begin
    let rc11_consistent = List.flatten @@ List.map Rc11.gen_rc11_exns (dedup ps) in
    info "RC11 consistency complete\n%!";
    if !print_size then Format.printf "%d RC11 Consistent Pomsets\n" (List.length rc11_consistent);
    if (not !print_latex) && !print_pomsets then
      List.iter (fun (p, co, rf) -> 
        Format.fprintf Format.std_formatter "%a" PomsetPTSeq.pp_pomset p;
        Format.fprintf Format.std_formatter "rf:  %a\n" (pp_relation pp_int pp_int) rf;
        Format.fprintf Format.std_formatter "co:  %a\n\n" (pp_relation pp_int pp_int) co
      ) rc11_consistent;
    if !check_outcomes then 
      ignore @@ Option.map (List.iter (function
        (AST.Allowed (_b,_os,c) as o)
      | (AST.Forbidden (_b,_os,c) as o) -> 
        ignore @@ Option.map (Format.printf "%s ") c;
        if check o (List.map (fun (p,_,_) -> p) rc11_consistent)
        then Format.printf "(pass)\n"
        else Format.printf "(fail)\n"
      )) outcomes;
  end;
  if !print_time then Format.printf "Execution time: %fs\n" (Sys.time ());
  ()

let run_f f = pomsetpt (Parse.parse_file f)

let run_s s = pomsetpt (Parse.parse_string s)

let args = Arg.align [
  ("--check", Arg.Set check_outcomes, "  Check that pomsets generated satisfy the litmus assertion [default: false]")
; ("--complete", Arg.Set check_complete, "  Print only completed pomsets [default: false]")
; ("--log", Arg.String Util.set_log_level, "  Set the log level as one of {all, info, debug, warn, error, none} [default: none]")
; ("--log-time", Arg.Set Util.log_times, "  Include time stamps in log output [default: false]")
; ("--program", Arg.Rest run_s, "  Interpret a program from the command line.")
; ("--print", Arg.Set print_pomsets, "  Pretty print pomsets [default: false]")
; ("--size", Arg.Set print_size, "  Print the number of completed pomsets [default: false]")
; ("--tex", Arg.Set print_latex, "  Use LaTeX output [default: false]")
; ("--time", Arg.Set print_time, "  Show execution time [default: false]")
]

let usage () =
  Format.sprintf "%s [OPTIONS] <FILENAME>" (Array.get Sys.argv 0)

let () = Arg.parse args run_f (usage ())
