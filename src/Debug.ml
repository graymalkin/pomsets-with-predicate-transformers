(**
  Debug printing utilities.
 *)

let discard_fmt = 
  Format.make_formatter (fun _ _ _ -> ()) (fun () -> ())

let debug_fmt = ref discard_fmt
let warn_fmt = ref discard_fmt
let error_fmt = ref discard_fmt

let log level fmt fmt_spec =
  Format.fprintf fmt "[%-5s] " level;
  Format.fprintf fmt fmt_spec

let debug fmt_spec = log "DEBUG" !debug_fmt fmt_spec
let warn  fmt_spec = log "WARN" !warn_fmt fmt_spec
let error fmt_spec = log "ERROR" !error_fmt fmt_spec

let set_log_level = function
  "all" 
| "debug" -> 
    debug_fmt := Format.err_formatter;
    warn_fmt := Format.err_formatter;
    error_fmt := Format.err_formatter

| "warn" -> 
    debug_fmt := discard_fmt;
    warn_fmt := Format.err_formatter;
    error_fmt := Format.err_formatter

| "error" -> 
    debug_fmt := discard_fmt;
    warn_fmt := discard_fmt;
    error_fmt := Format.err_formatter

| "nolog" -> 
    debug_fmt := discard_fmt;
    warn_fmt := discard_fmt;
    error_fmt := discard_fmt

| s -> warn "%s is an invalid log level" s
