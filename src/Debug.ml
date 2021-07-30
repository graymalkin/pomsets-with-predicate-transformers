(**
  Debug printing utilities.
 *)

let discard_fmt = 
  Format.make_formatter (fun _ _ _ -> ()) (fun () -> ())

let log_times = ref false
let info_fmt = ref discard_fmt
let debug_fmt = ref discard_fmt
let warn_fmt = ref discard_fmt
let error_fmt = ref Format.err_formatter

let log level fmt fmt_spec =
  Format.fprintf fmt "[%-5s] " level;
  if !log_times then Format.fprintf fmt "[%.6f] " (Sys.time ());
  Format.fprintf fmt fmt_spec

let info  fmt_spec = log "INFO" !info_fmt fmt_spec
let debug fmt_spec = log "DEBUG" !debug_fmt fmt_spec
let warn  fmt_spec = log "WARN" !warn_fmt fmt_spec
let error fmt_spec = log "ERROR" !error_fmt fmt_spec

let set_log_level = function
  "all" 
| "info" -> 
    info_fmt := Format.err_formatter;
    debug_fmt := Format.err_formatter;
    warn_fmt := Format.err_formatter;
    error_fmt := Format.err_formatter

| "debug" ->
    info_fmt := discard_fmt;
    debug_fmt := Format.err_formatter;
    warn_fmt := Format.err_formatter;
    error_fmt := Format.err_formatter

| "warn" -> 
    info_fmt := discard_fmt;
    debug_fmt := discard_fmt;
    warn_fmt := Format.err_formatter;
    error_fmt := Format.err_formatter

| "error" -> 
    info_fmt := discard_fmt;
    debug_fmt := discard_fmt;
    warn_fmt := discard_fmt;
    error_fmt := Format.err_formatter

| "nolog" -> 
    info_fmt := discard_fmt;
    debug_fmt := discard_fmt;
    warn_fmt := discard_fmt;
    error_fmt := discard_fmt

| s -> warn "%s is an invalid log level" s
