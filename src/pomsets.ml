(** === Program entry point. ===
  Arguments are intepretted using the standard OCaml Args module, args set ref cell flags listed at the top of this file.
  pomsetpt takes the output of the parser and runs the pomsetpt semantics over it.
 *)

open Preliminaries
open PomsetPTSeq
open PPRelation

open Util

type model = PwT | RC11 | MCA1

let check_outcomes = ref false
let check_complete = ref false
let use_model = ref PwT
let print_latex = ref false
let print_pomsets = ref false
let print_size = ref false
let print_time = ref false

let model_of_string = function
  "pwt" | "PwT" -> PwT
| "rc11" | "RC11" -> RC11
| "mca" | "MCA" | "mca1" | "MCA1" -> MCA1 
| _ -> failwith "invalid model name. (1idyKA)"
let set_model s = use_model := model_of_string s

let check_outcome env bexpr = 
  let trans_env r = try
    let Val v = env (Reg r) in v 
    with Unbound -> 0 | Not_found -> failwith ("can't find " ^ r)
  in
  AST.eval_bexpr (trans_env) bexpr

let check_one = function 
  AST.Allowed (bexpr, _, _) -> fun p -> check_outcome p.smap bexpr
| AST.Forbidden (bexpr, _, _) -> fun p -> not (check_outcome p.smap bexpr)

let check = function 
  AST.Allowed _ as o -> List.exists (check_one o)
| AST.Forbidden _ as o -> List.for_all (check_one o)

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

let pass = if Unix.isatty Unix.stdout then "\x1b[1;32mpass\x1b[0m" else "pass"
let fail = if Unix.isatty Unix.stdout then "\x1b[1;31mfail\x1b[0m" else "fail"
let pp_result fmt b = Format.fprintf fmt "%s" (if b then pass else fail)

let pp_rc11_ps fmt (p, co, rf) =
  Format.fprintf fmt "%a" PomsetPTSeq.pp_pomset p;
  Format.fprintf fmt "rf:  %a\n" (pp_relation pp_int pp_int) rf;
  Format.fprintf fmt "co:  %a\n\n" (pp_relation pp_int pp_int) co

let check_ps outcomes ps =
  ignore @@ Option.map (List.iter (function
    (AST.Allowed (b,_os,c) as o)
  | (AST.Forbidden (b,_os,c) as o) -> 
    ignore @@ Option.map (Format.printf "%s ") c;
    Format.printf "%a (%a)\n\n" AST.pp_boolean_expr b pp_result (check o ps)
  )) outcomes

let check_rc11 outcomes ps =
  let rc11_consistent = List.flatten @@ List.map Rc11.gen_rc11_exns (dedup ps) in
  info "RC11 consistency complete\n%!";
  if !print_size then Format.printf "%d RC11 Consistent Pomsets\n" (List.length rc11_consistent);
  if (not !print_latex) && !print_pomsets then List.iter (pp_rc11_ps Format.std_formatter) rc11_consistent;
  if !check_outcomes then check_ps outcomes (List.map (fun (p,_,_) -> p) rc11_consistent)

let check_pwt outcomes ps = 
  let pwt_consistent = dedup ps in
  if !print_size then Format.printf "%d PwT Consistent Pomsets\n" (List.length pwt_consistent);
  if (not !print_latex) && !print_pomsets then List.iter (Format.printf "%a" PomsetPTSeq.pp_pomset) pwt_consistent;
  if !check_outcomes then check_ps outcomes pwt_consistent

let pomsetpt (config, ast, outcomes) = 
  if !use_model = RC11 && not !check_complete then failwith "RC11 only supports completed pomsets, run with --complete";
  let config = Option.value ~default:RunConfig.default_configuration config in
  let vs = config.RunConfig.values in
  info "Setup complete\n%!";
  let ps = interp vs !check_complete (ASTToPomsetPTSeq.convert_program ast) in
  info "Interpretation complete\n%!";
  if !print_size then Format.printf "%d pomsets (%d after deduping)\n" (List.length ps) (List.length (dedup ps));
  if !print_latex then 
    PrintLatexDoc.pp_document Format.std_formatter config ast LatexPomsetPTSeq.pp_pomset (dedup ps);
  info "Checking RC11 consistency\n%!";
  if not !check_complete && not !print_latex && !print_pomsets then
    List.iter (Format.printf "%a\n" pp_pomset) (dedup ps);
  match !use_model with
    RC11 -> check_rc11 outcomes ps 
  | PwT -> check_pwt outcomes ps 
  | MCA1 -> ignore @@ failwith "todo (6BnJPF)";
  if !print_time then Format.printf "Execution time: %fs\n" (Sys.time ());
  ()

let run_f f = pomsetpt (Parse.parse_file f)

let run_s s = pomsetpt (Parse.parse_string s)

let args = Arg.align [
  ("--check", Arg.Set check_outcomes, "  Check that pomsets generated satisfy the litmus assertion")
; ("--complete", Arg.Set check_complete, "  Print only completed pomsets")
; ("--log", Arg.String Util.set_log_level, "<level>  Set the log level as one of {all, info, debug, warn, error, none} [default: none]")
; ("--log-time", Arg.Set Util.log_times, "  Include time stamps in log output")
; ("--model", Arg.String set_model, "<model>  Select a version of the model from {PwT, RC11, MCA1} [default: PwT]")
; ("--program", Arg.Rest run_s, "<program>  Interpret a program from the command line.")
; ("--print", Arg.Set print_pomsets, "  Pretty print pomsets")
; ("--size", Arg.Set print_size, "  Print the number of completed pomsets")
; ("--tex", Arg.Set print_latex, "  Use LaTeX output")
; ("--time", Arg.Set print_time, "  Show execution time")
]

let usage () =
  Format.sprintf "%s [OPTIONS] <FILENAME>" (Array.get Sys.argv 0)

let () = Arg.parse args run_f (usage ())
