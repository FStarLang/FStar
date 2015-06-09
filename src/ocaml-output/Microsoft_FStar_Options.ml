
type debug_level_t =
| Low
| Medium
| High
| Extreme
| Other of string

let show_signatures = (Support.Microsoft.FStar.Util.mk_ref [])

let norm_then_print = (Support.Microsoft.FStar.Util.mk_ref true)

let z3_exe = (Support.Microsoft.FStar.Util.mk_ref (Support.Microsoft.FStar.Platform.exe "z3"))

let silent = (Support.Microsoft.FStar.Util.mk_ref false)

let debug = (Support.Microsoft.FStar.Util.mk_ref [])

let debug_level = (Support.Microsoft.FStar.Util.mk_ref [])

let dlevel = (fun _23561 -> (match (_23561) with
| "Low" -> begin
Low
end
| "Medium" -> begin
Medium
end
| "High" -> begin
High
end
| "Extreme" -> begin
Extreme
end
| s -> begin
Other (s)
end))

let one_debug_level_geq = (fun l1 l2 -> (match (l1) with
| (Other (_)) | (Low) -> begin
(l1 = l2)
end
| Medium -> begin
((l2 = Low) || (l2 = Medium))
end
| High -> begin
(((l2 = Low) || (l2 = Medium)) || (l2 = High))
end
| Extreme -> begin
((((l2 = Low) || (l2 = Medium)) || (l2 = High)) || (l2 = Extreme))
end))

let debug_level_geq = (fun l2 -> ((Support.Microsoft.FStar.Util.for_some (fun l1 -> (one_debug_level_geq l1 l2))) (! (debug_level))))

let log_types = (Support.Microsoft.FStar.Util.mk_ref false)

let print_effect_args = (Support.Microsoft.FStar.Util.mk_ref false)

let print_real_names = (Support.Microsoft.FStar.Util.mk_ref false)

let dump_module = (Support.Microsoft.FStar.Util.mk_ref None)

let should_dump = (fun l -> (match ((! (dump_module))) with
| None -> begin
false
end
| Some (m) -> begin
(m = l)
end))

let logQueries = (Support.Microsoft.FStar.Util.mk_ref false)

let z3exe = (Support.Microsoft.FStar.Util.mk_ref true)

let outputDir = (Support.Microsoft.FStar.Util.mk_ref (Some (".")))

let fstar_home_opt = (Support.Microsoft.FStar.Util.mk_ref None)

let _fstar_home = (Support.Microsoft.FStar.Util.mk_ref "")

let prims_ref = (Support.Microsoft.FStar.Util.mk_ref None)

let z3timeout = (Support.Microsoft.FStar.Util.mk_ref 5)

let admit_smt_queries = (Support.Microsoft.FStar.Util.mk_ref false)

let pretype = (Support.Microsoft.FStar.Util.mk_ref true)

let codegen = (Support.Microsoft.FStar.Util.mk_ref None)

let admit_fsi = (Support.Microsoft.FStar.Util.mk_ref [])

let codegen_libs = (Support.Microsoft.FStar.Util.mk_ref [])

let trace_error = (Support.Microsoft.FStar.Util.mk_ref false)

let verify = (Support.Microsoft.FStar.Util.mk_ref true)

let full_context_dependency = (Support.Microsoft.FStar.Util.mk_ref true)

let print_implicits = (Support.Microsoft.FStar.Util.mk_ref false)

let hide_uvar_nums = (Support.Microsoft.FStar.Util.mk_ref false)

let hide_genident_nums = (Support.Microsoft.FStar.Util.mk_ref false)

let serialize_mods = (Support.Microsoft.FStar.Util.mk_ref false)

let initial_fuel = (Support.Microsoft.FStar.Util.mk_ref 2)

let initial_ifuel = (Support.Microsoft.FStar.Util.mk_ref 1)

let max_fuel = (Support.Microsoft.FStar.Util.mk_ref 8)

let min_fuel = (Support.Microsoft.FStar.Util.mk_ref 1)

let max_ifuel = (Support.Microsoft.FStar.Util.mk_ref 2)

let warn_top_level_effects = (Support.Microsoft.FStar.Util.mk_ref false)

let no_slack = (Support.Microsoft.FStar.Util.mk_ref false)

let eager_inference = (Support.Microsoft.FStar.Util.mk_ref false)

let unthrottle_inductives = (Support.Microsoft.FStar.Util.mk_ref false)

let use_eq_at_higher_order = (Support.Microsoft.FStar.Util.mk_ref false)

let fs_typ_app = (Support.Microsoft.FStar.Util.mk_ref false)

let n_cores = (Support.Microsoft.FStar.Util.mk_ref 1)

let verify_module = (Support.Microsoft.FStar.Util.mk_ref [])

let use_build_config = (Support.Microsoft.FStar.Util.mk_ref false)

let interactive = (Support.Microsoft.FStar.Util.mk_ref false)

let init_options = (fun _23585 -> (match (_23585) with
| () -> begin
(let _23586 = (show_signatures := [])
in (let _23588 = (norm_then_print := true)
in (let _23590 = (z3_exe := (Support.Microsoft.FStar.Platform.exe "z3"))
in (let _23592 = (silent := false)
in (let _23594 = (debug := [])
in (let _23596 = (debug_level := [])
in (let _23598 = (log_types := false)
in (let _23600 = (print_effect_args := false)
in (let _23602 = (print_real_names := false)
in (let _23604 = (dump_module := None)
in (let _23606 = (logQueries := false)
in (let _23608 = (z3exe := true)
in (let _23610 = (outputDir := Some ("."))
in (let _23612 = (fstar_home_opt := None)
in (let _23614 = (_fstar_home := "")
in (let _23616 = (prims_ref := None)
in (let _23618 = (z3timeout := 5)
in (let _23620 = (admit_smt_queries := false)
in (let _23622 = (pretype := true)
in (let _23624 = (codegen := None)
in (let _23626 = (codegen_libs := [])
in (let _23628 = (admit_fsi := [])
in (let _23630 = (trace_error := false)
in (let _23632 = (verify := true)
in (let _23634 = (full_context_dependency := true)
in (let _23636 = (print_implicits := false)
in (let _23638 = (hide_uvar_nums := false)
in (let _23640 = (hide_genident_nums := false)
in (let _23642 = (serialize_mods := false)
in (let _23644 = (initial_fuel := 2)
in (let _23646 = (initial_ifuel := 1)
in (let _23648 = (max_fuel := 8)
in (let _23650 = (min_fuel := 1)
in (let _23652 = (max_ifuel := 2)
in (let _23654 = (warn_top_level_effects := false)
in (let _23656 = (no_slack := false)
in (let _23658 = (eager_inference := false)
in (let _23660 = (unthrottle_inductives := false)
in (let _23662 = (use_eq_at_higher_order := false)
in (let _23664 = (fs_typ_app := false)
in (let _23666 = (n_cores := 1)
in (verify_module := []))))))))))))))))))))))))))))))))))))))))))
end))

let set_fstar_home = (fun _23668 -> (match (_23668) with
| () -> begin
(let fh = (match ((! (fstar_home_opt))) with
| None -> begin
(let x = (Support.Microsoft.FStar.Util.get_exec_dir ())
in (let x = (Support.String.strcat x "/..")
in (let _23672 = (_fstar_home := x)
in (let _23674 = (fstar_home_opt := Some (x))
in x))))
end
| Some (x) -> begin
(let _23678 = (_fstar_home := x)
in x)
end)
in fh)
end))

let get_fstar_home = (fun _23681 -> (match (_23681) with
| () -> begin
(match ((! (fstar_home_opt))) with
| None -> begin
(let _23683 = ((Support.Prims.ignore) (set_fstar_home ()))
in (! (_fstar_home)))
end
| Some (x) -> begin
x
end)
end))

let prims = (fun _23687 -> (match (_23687) with
| () -> begin
(match ((! (prims_ref))) with
| None -> begin
(Support.String.strcat (get_fstar_home ()) "/lib/prims.fst")
end
| Some (x) -> begin
x
end)
end))

let prependOutputDir = (fun fname -> (match ((! (outputDir))) with
| None -> begin
fname
end
| Some (x) -> begin
(Support.String.strcat (Support.String.strcat x "/") fname)
end))

let cache_dir = "cache"

let display_usage = (fun specs -> (let _23696 = (Support.Microsoft.FStar.Util.print_string "fstar [option] infile...")
in (Support.List.iter (fun _23703 -> (match (_23703) with
| (_, flag, p, doc) -> begin
(match (p) with
| Support.Microsoft.FStar.Getopt.ZeroArgs (ig) -> begin
if (doc = "") then begin
(Support.Microsoft.FStar.Util.print_string (Support.Microsoft.FStar.Util.format1 "  --%s\n" flag))
end else begin
(Support.Microsoft.FStar.Util.print_string (Support.Microsoft.FStar.Util.format2 "  --%s  %s\n" flag doc))
end
end
| Support.Microsoft.FStar.Getopt.OneArg ((_, argname)) -> begin
if (doc = "") then begin
(Support.Microsoft.FStar.Util.print_string (Support.Microsoft.FStar.Util.format2 "  --%s %s\n" flag argname))
end else begin
(Support.Microsoft.FStar.Util.print_string (Support.Microsoft.FStar.Util.format3 "  --%s %s  %s\n" flag argname doc))
end
end)
end)) specs)))

let rec specs = (fun _23711 -> (match (_23711) with
| () -> begin
(let specs = ((Support.Microsoft.FStar.Getopt.noshort, "trace_error", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23712 -> (match (_23712) with
| () -> begin
(trace_error := true)
end))), "Don\'t print an error message; show an exception trace instead"))::((Support.Microsoft.FStar.Getopt.noshort, "codegen", Support.Microsoft.FStar.Getopt.OneArg (((fun s -> (let _23714 = (codegen := (parse_codegen s))
in (verify := false))), "OCaml|F#|JavaScript")), "Generate code for execution"))::((Support.Microsoft.FStar.Getopt.noshort, "codegen-lib", Support.Microsoft.FStar.Getopt.OneArg (((fun s -> (codegen_libs := ((Support.Microsoft.FStar.Util.split s "."))::(! (codegen_libs)))), "namespace")), "External runtime library library"))::((Support.Microsoft.FStar.Getopt.noshort, "lax", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23717 -> (match (_23717) with
| () -> begin
(let _23718 = (pretype := true)
in (verify := false))
end))), "Run the lax-type checker only (admit all verification conditions)"))::((Support.Microsoft.FStar.Getopt.noshort, "fstar_home", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (fstar_home_opt := Some (x))), "dir")), "Set the FSTAR_HOME variable to dir"))::((Support.Microsoft.FStar.Getopt.noshort, "silent", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23721 -> (match (_23721) with
| () -> begin
(silent := true)
end))), ""))::((Support.Microsoft.FStar.Getopt.noshort, "prims", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (prims_ref := Some (x))), "file")), ""))::((Support.Microsoft.FStar.Getopt.noshort, "prn", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23723 -> (match (_23723) with
| () -> begin
(print_real_names := true)
end))), "Print real names---you may want to use this in conjunction with logQueries"))::((Support.Microsoft.FStar.Getopt.noshort, "debug", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (debug := (x)::(! (debug)))), "module name")), "Print LOTS of debugging information while checking module [arg]"))::((Support.Microsoft.FStar.Getopt.noshort, "debug_level", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (debug_level := ((dlevel x))::(! (debug_level)))), "Low|Medium|High|Extreme")), "Control the verbosity of debugging info"))::((Support.Microsoft.FStar.Getopt.noshort, "log_types", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23726 -> (match (_23726) with
| () -> begin
(log_types := true)
end))), "Print types computed for data/val/let-bindings"))::((Support.Microsoft.FStar.Getopt.noshort, "print_effect_args", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23727 -> (match (_23727) with
| () -> begin
(print_effect_args := true)
end))), "Print inferred predicate transformers for all computation types"))::((Support.Microsoft.FStar.Getopt.noshort, "dump_module", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (dump_module := Some (x))), "module name")), ""))::((Support.Microsoft.FStar.Getopt.noshort, "z3timeout", Support.Microsoft.FStar.Getopt.OneArg (((fun s -> (z3timeout := (Support.Microsoft.FStar.Util.int_of_string s))), "t")), "Set the Z3 per-query (soft) timeout to t seconds (default 5)"))::((Support.Microsoft.FStar.Getopt.noshort, "admit_smt_queries", Support.Microsoft.FStar.Getopt.OneArg (((fun s -> (admit_smt_queries := if (s = "true") then begin
true
end else begin
if (s = "false") then begin
false
end else begin
(failwith "Invalid argument to --admit_smt_queries")
end
end)), "true|false")), "Admit SMT queries (UNSAFE! But, useful during development); default: \'false\'"))::((Support.Microsoft.FStar.Getopt.noshort, "logQueries", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23731 -> (match (_23731) with
| () -> begin
(logQueries := true)
end))), "Log the Z3 queries in queries.smt2"))::((Support.Microsoft.FStar.Getopt.noshort, "admit_fsi", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (admit_fsi := (x)::(! (admit_fsi)))), "module name")), "Treat .fsi as a .fst"))::((Support.Microsoft.FStar.Getopt.noshort, "odir", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (outputDir := Some (x))), "dir")), "Place output in directory dir"))::((Support.Microsoft.FStar.Getopt.noshort, "smt", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (z3_exe := x)), "path")), "Path to the SMT solver (usually Z3, but could be any SMT2-compatible solver)"))::((Support.Microsoft.FStar.Getopt.noshort, "print_before_norm", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23735 -> (match (_23735) with
| () -> begin
(norm_then_print := false)
end))), "Do not normalize types before printing (for debugging)"))::((Support.Microsoft.FStar.Getopt.noshort, "show_signatures", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (show_signatures := (x)::(! (show_signatures)))), "module name")), "Show the checked signatures for all top-level symbols in the module"))::((Support.Microsoft.FStar.Getopt.noshort, "full_context_dependency", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23737 -> (match (_23737) with
| () -> begin
(full_context_dependency := true)
end))), "Introduce unification variables that are dependent on the entire context (possibly expensive, but better for type inference (on, by default)"))::((Support.Microsoft.FStar.Getopt.noshort, "MLish", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23738 -> (match (_23738) with
| () -> begin
(full_context_dependency := false)
end))), "Introduce unification variables that are only dependent on the type variables in the context"))::((Support.Microsoft.FStar.Getopt.noshort, "print_implicits", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23739 -> (match (_23739) with
| () -> begin
(print_implicits := true)
end))), "Print implicit arguments"))::((Support.Microsoft.FStar.Getopt.noshort, "hide_uvar_nums", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23740 -> (match (_23740) with
| () -> begin
(hide_uvar_nums := true)
end))), "Don\'t print unification variable numbers"))::((Support.Microsoft.FStar.Getopt.noshort, "hide_genident_nums", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23741 -> (match (_23741) with
| () -> begin
(hide_genident_nums := true)
end))), "Don\'t print generated identifier numbers"))::((Support.Microsoft.FStar.Getopt.noshort, "serialize_mods", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23742 -> (match (_23742) with
| () -> begin
(serialize_mods := true)
end))), "Serialize compiled modules"))::((Support.Microsoft.FStar.Getopt.noshort, "initial_fuel", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (initial_fuel := (Support.Microsoft.FStar.Util.int_of_string x))), "non-negative integer")), "Number of unrolling of recursive functions to try initially (default 2)"))::((Support.Microsoft.FStar.Getopt.noshort, "max_fuel", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (max_fuel := (Support.Microsoft.FStar.Util.int_of_string x))), "non-negative integer")), "Number of unrolling of recursive functions to try at most (default 8)"))::((Support.Microsoft.FStar.Getopt.noshort, "min_fuel", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (min_fuel := (Support.Microsoft.FStar.Util.int_of_string x))), "non-negative integer")), "Minimum number of unrolling of recursive functions to try (default 1)"))::((Support.Microsoft.FStar.Getopt.noshort, "initial_ifuel", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (initial_ifuel := (Support.Microsoft.FStar.Util.int_of_string x))), "non-negative integer")), "Number of unrolling of inductive datatypes to try at first (default 1)"))::((Support.Microsoft.FStar.Getopt.noshort, "max_ifuel", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (max_ifuel := (Support.Microsoft.FStar.Util.int_of_string x))), "non-negative integer")), "Number of unrolling of inductive datatypes to try at most (default 1)"))::((Support.Microsoft.FStar.Getopt.noshort, "warn_top_level_effects", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23748 -> (match (_23748) with
| () -> begin
(warn_top_level_effects := true)
end))), "Top-level effects are ignored, by default; turn this flag on to be warned when this happens"))::((Support.Microsoft.FStar.Getopt.noshort, "no_slack", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23749 -> (match (_23749) with
| () -> begin
(no_slack := true)
end))), "Use the partially flow-insensitive variant of --rel2 (experimental)"))::((Support.Microsoft.FStar.Getopt.noshort, "eager_inference", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23750 -> (match (_23750) with
| () -> begin
(eager_inference := true)
end))), "Solve all type-inference constraints eagerly; more efficient but at the cost of generality"))::((Support.Microsoft.FStar.Getopt.noshort, "unthrottle_inductives", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23751 -> (match (_23751) with
| () -> begin
(unthrottle_inductives := true)
end))), "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)"))::((Support.Microsoft.FStar.Getopt.noshort, "use_eq_at_higher_order", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23752 -> (match (_23752) with
| () -> begin
(use_eq_at_higher_order := true)
end))), "Use equality constraints when comparing higher-order types; temporary"))::((Support.Microsoft.FStar.Getopt.noshort, "fs_typ_app", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23753 -> (match (_23753) with
| () -> begin
(fs_typ_app := true)
end))), "Allow the use of t<t1,...,tn> syntax for type applications; brittle since it clashes with the integer less-than operator"))::((Support.Microsoft.FStar.Getopt.noshort, "no_fs_typ_app", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23754 -> (match (_23754) with
| () -> begin
(fs_typ_app := false)
end))), "Do not allow the use of t<t1,...,tn> syntax for type applications"))::((Support.Microsoft.FStar.Getopt.noshort, "n_cores", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (n_cores := (Support.Microsoft.FStar.Util.int_of_string x))), "positive integer")), "Maximum number of cores to use for the solver (default 1)"))::((Support.Microsoft.FStar.Getopt.noshort, "verify_module", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (verify_module := (x)::(! (verify_module)))), "string")), "Name of the module to verify"))::((Support.Microsoft.FStar.Getopt.noshort, "use_build_config", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23757 -> (match (_23757) with
| () -> begin
(use_build_config := true)
end))), "Expect just a single file on the command line and no options; will read the \'build-config\' prelude from the file"))::((Support.Microsoft.FStar.Getopt.noshort, "in", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23758 -> (match (_23758) with
| () -> begin
(interactive := true)
end))), "Interactive mode; reads input from stdin"))::[]
in (('h', "help", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun x -> (let _23761 = (display_usage specs)
in (exit (0))))), "Display this information"))::specs)
end))
and parse_codegen = (fun s -> (match (s) with
| ("OCaml") | ("F#") | ("JavaScript") -> begin
Some (s)
end
| _ -> begin
(let _23769 = (Support.Microsoft.FStar.Util.print_string "Wrong argument to codegen flag\n")
in (let _23771 = (display_usage (specs ()))
in (exit (1))))
end))

let should_verify = (fun m -> ((! (verify)) && (match ((! (verify_module))) with
| [] -> begin
true
end
| l -> begin
(Support.List.contains m l)
end)))

let set_options = (fun s -> (Support.Microsoft.FStar.Getopt.parse_string (specs ()) (fun _23777 -> ()) s))

let reset_options_string = (ref None)

let reset_options = (fun _23779 -> (match (_23779) with
| () -> begin
(let _23780 = (init_options ())
in (match ((! (reset_options_string))) with
| Some (x) -> begin
(set_options x)
end
| _ -> begin
(Support.Microsoft.FStar.Getopt.parse_cmdline (specs ()) (fun x -> ()))
end))
end))




