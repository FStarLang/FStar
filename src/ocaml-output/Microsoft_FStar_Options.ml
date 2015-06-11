
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

let dlevel = (fun _23618 -> (match (_23618) with
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

let init_options = (fun _23642 -> (match (_23642) with
| () -> begin
(let _23643 = (show_signatures := [])
in (let _23645 = (norm_then_print := true)
in (let _23647 = (z3_exe := (Support.Microsoft.FStar.Platform.exe "z3"))
in (let _23649 = (silent := false)
in (let _23651 = (debug := [])
in (let _23653 = (debug_level := [])
in (let _23655 = (log_types := false)
in (let _23657 = (print_effect_args := false)
in (let _23659 = (print_real_names := false)
in (let _23661 = (dump_module := None)
in (let _23663 = (logQueries := false)
in (let _23665 = (z3exe := true)
in (let _23667 = (outputDir := Some ("."))
in (let _23669 = (fstar_home_opt := None)
in (let _23671 = (_fstar_home := "")
in (let _23673 = (prims_ref := None)
in (let _23675 = (z3timeout := 5)
in (let _23677 = (admit_smt_queries := false)
in (let _23679 = (pretype := true)
in (let _23681 = (codegen := None)
in (let _23683 = (codegen_libs := [])
in (let _23685 = (admit_fsi := [])
in (let _23687 = (trace_error := false)
in (let _23689 = (verify := true)
in (let _23691 = (full_context_dependency := true)
in (let _23693 = (print_implicits := false)
in (let _23695 = (hide_uvar_nums := false)
in (let _23697 = (hide_genident_nums := false)
in (let _23699 = (serialize_mods := false)
in (let _23701 = (initial_fuel := 2)
in (let _23703 = (initial_ifuel := 1)
in (let _23705 = (max_fuel := 8)
in (let _23707 = (min_fuel := 1)
in (let _23709 = (max_ifuel := 2)
in (let _23711 = (warn_top_level_effects := false)
in (let _23713 = (no_slack := false)
in (let _23715 = (eager_inference := false)
in (let _23717 = (unthrottle_inductives := false)
in (let _23719 = (use_eq_at_higher_order := false)
in (let _23721 = (fs_typ_app := false)
in (let _23723 = (n_cores := 1)
in (verify_module := []))))))))))))))))))))))))))))))))))))))))))
end))

let set_fstar_home = (fun _23725 -> (match (_23725) with
| () -> begin
(let fh = (match ((! (fstar_home_opt))) with
| None -> begin
(let x = (Support.Microsoft.FStar.Util.get_exec_dir ())
in (let x = (Support.String.strcat x "/..")
in (let _23729 = (_fstar_home := x)
in (let _23731 = (fstar_home_opt := Some (x))
in x))))
end
| Some (x) -> begin
(let _23735 = (_fstar_home := x)
in x)
end)
in fh)
end))

let get_fstar_home = (fun _23738 -> (match (_23738) with
| () -> begin
(match ((! (fstar_home_opt))) with
| None -> begin
(let _23740 = ((Support.Prims.ignore) (set_fstar_home ()))
in (! (_fstar_home)))
end
| Some (x) -> begin
x
end)
end))

let prims = (fun _23744 -> (match (_23744) with
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

let display_usage = (fun specs -> (let _23753 = (Support.Microsoft.FStar.Util.print_string "fstar [option] infile...")
in (Support.List.iter (fun _23760 -> (match (_23760) with
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

let rec specs = (fun _23768 -> (match (_23768) with
| () -> begin
(let specs = ((Support.Microsoft.FStar.Getopt.noshort, "trace_error", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23769 -> (match (_23769) with
| () -> begin
(trace_error := true)
end))), "Don\'t print an error message; show an exception trace instead"))::((Support.Microsoft.FStar.Getopt.noshort, "codegen", Support.Microsoft.FStar.Getopt.OneArg (((fun s -> (let _23771 = (codegen := (parse_codegen s))
in (verify := false))), "OCaml|F#|JavaScript")), "Generate code for execution"))::((Support.Microsoft.FStar.Getopt.noshort, "codegen-lib", Support.Microsoft.FStar.Getopt.OneArg (((fun s -> (codegen_libs := ((Support.Microsoft.FStar.Util.split s "."))::(! (codegen_libs)))), "namespace")), "External runtime library library"))::((Support.Microsoft.FStar.Getopt.noshort, "lax", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23774 -> (match (_23774) with
| () -> begin
(let _23775 = (pretype := true)
in (verify := false))
end))), "Run the lax-type checker only (admit all verification conditions)"))::((Support.Microsoft.FStar.Getopt.noshort, "fstar_home", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (fstar_home_opt := Some (x))), "dir")), "Set the FSTAR_HOME variable to dir"))::((Support.Microsoft.FStar.Getopt.noshort, "silent", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23778 -> (match (_23778) with
| () -> begin
(silent := true)
end))), ""))::((Support.Microsoft.FStar.Getopt.noshort, "prims", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (prims_ref := Some (x))), "file")), ""))::((Support.Microsoft.FStar.Getopt.noshort, "prn", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23780 -> (match (_23780) with
| () -> begin
(print_real_names := true)
end))), "Print real names---you may want to use this in conjunction with logQueries"))::((Support.Microsoft.FStar.Getopt.noshort, "debug", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (debug := (x)::(! (debug)))), "module name")), "Print LOTS of debugging information while checking module [arg]"))::((Support.Microsoft.FStar.Getopt.noshort, "debug_level", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (debug_level := ((dlevel x))::(! (debug_level)))), "Low|Medium|High|Extreme")), "Control the verbosity of debugging info"))::((Support.Microsoft.FStar.Getopt.noshort, "log_types", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23783 -> (match (_23783) with
| () -> begin
(log_types := true)
end))), "Print types computed for data/val/let-bindings"))::((Support.Microsoft.FStar.Getopt.noshort, "print_effect_args", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23784 -> (match (_23784) with
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
end)), "true|false")), "Admit SMT queries (UNSAFE! But, useful during development); default: \'false\'"))::((Support.Microsoft.FStar.Getopt.noshort, "logQueries", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23788 -> (match (_23788) with
| () -> begin
(logQueries := true)
end))), "Log the Z3 queries in queries.smt2"))::((Support.Microsoft.FStar.Getopt.noshort, "admit_fsi", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (admit_fsi := (x)::(! (admit_fsi)))), "module name")), "Treat .fsi as a .fst"))::((Support.Microsoft.FStar.Getopt.noshort, "odir", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (outputDir := Some (x))), "dir")), "Place output in directory dir"))::((Support.Microsoft.FStar.Getopt.noshort, "smt", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (z3_exe := x)), "path")), "Path to the SMT solver (usually Z3, but could be any SMT2-compatible solver)"))::((Support.Microsoft.FStar.Getopt.noshort, "print_before_norm", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23792 -> (match (_23792) with
| () -> begin
(norm_then_print := false)
end))), "Do not normalize types before printing (for debugging)"))::((Support.Microsoft.FStar.Getopt.noshort, "show_signatures", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (show_signatures := (x)::(! (show_signatures)))), "module name")), "Show the checked signatures for all top-level symbols in the module"))::((Support.Microsoft.FStar.Getopt.noshort, "full_context_dependency", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23794 -> (match (_23794) with
| () -> begin
(full_context_dependency := true)
end))), "Introduce unification variables that are dependent on the entire context (possibly expensive, but better for type inference (on, by default)"))::((Support.Microsoft.FStar.Getopt.noshort, "MLish", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23795 -> (match (_23795) with
| () -> begin
(full_context_dependency := false)
end))), "Introduce unification variables that are only dependent on the type variables in the context"))::((Support.Microsoft.FStar.Getopt.noshort, "print_implicits", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23796 -> (match (_23796) with
| () -> begin
(print_implicits := true)
end))), "Print implicit arguments"))::((Support.Microsoft.FStar.Getopt.noshort, "hide_uvar_nums", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23797 -> (match (_23797) with
| () -> begin
(hide_uvar_nums := true)
end))), "Don\'t print unification variable numbers"))::((Support.Microsoft.FStar.Getopt.noshort, "hide_genident_nums", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23798 -> (match (_23798) with
| () -> begin
(hide_genident_nums := true)
end))), "Don\'t print generated identifier numbers"))::((Support.Microsoft.FStar.Getopt.noshort, "serialize_mods", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23799 -> (match (_23799) with
| () -> begin
(serialize_mods := true)
end))), "Serialize compiled modules"))::((Support.Microsoft.FStar.Getopt.noshort, "initial_fuel", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (initial_fuel := (Support.Microsoft.FStar.Util.int_of_string x))), "non-negative integer")), "Number of unrolling of recursive functions to try initially (default 2)"))::((Support.Microsoft.FStar.Getopt.noshort, "max_fuel", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (max_fuel := (Support.Microsoft.FStar.Util.int_of_string x))), "non-negative integer")), "Number of unrolling of recursive functions to try at most (default 8)"))::((Support.Microsoft.FStar.Getopt.noshort, "min_fuel", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (min_fuel := (Support.Microsoft.FStar.Util.int_of_string x))), "non-negative integer")), "Minimum number of unrolling of recursive functions to try (default 1)"))::((Support.Microsoft.FStar.Getopt.noshort, "initial_ifuel", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (initial_ifuel := (Support.Microsoft.FStar.Util.int_of_string x))), "non-negative integer")), "Number of unrolling of inductive datatypes to try at first (default 1)"))::((Support.Microsoft.FStar.Getopt.noshort, "max_ifuel", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (max_ifuel := (Support.Microsoft.FStar.Util.int_of_string x))), "non-negative integer")), "Number of unrolling of inductive datatypes to try at most (default 1)"))::((Support.Microsoft.FStar.Getopt.noshort, "warn_top_level_effects", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23805 -> (match (_23805) with
| () -> begin
(warn_top_level_effects := true)
end))), "Top-level effects are ignored, by default; turn this flag on to be warned when this happens"))::((Support.Microsoft.FStar.Getopt.noshort, "no_slack", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23806 -> (match (_23806) with
| () -> begin
(no_slack := true)
end))), "Use the partially flow-insensitive variant of --rel2 (experimental)"))::((Support.Microsoft.FStar.Getopt.noshort, "eager_inference", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23807 -> (match (_23807) with
| () -> begin
(eager_inference := true)
end))), "Solve all type-inference constraints eagerly; more efficient but at the cost of generality"))::((Support.Microsoft.FStar.Getopt.noshort, "unthrottle_inductives", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23808 -> (match (_23808) with
| () -> begin
(unthrottle_inductives := true)
end))), "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)"))::((Support.Microsoft.FStar.Getopt.noshort, "use_eq_at_higher_order", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23809 -> (match (_23809) with
| () -> begin
(use_eq_at_higher_order := true)
end))), "Use equality constraints when comparing higher-order types; temporary"))::((Support.Microsoft.FStar.Getopt.noshort, "fs_typ_app", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23810 -> (match (_23810) with
| () -> begin
(fs_typ_app := true)
end))), "Allow the use of t<t1,...,tn> syntax for type applications; brittle since it clashes with the integer less-than operator"))::((Support.Microsoft.FStar.Getopt.noshort, "no_fs_typ_app", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23811 -> (match (_23811) with
| () -> begin
(fs_typ_app := false)
end))), "Do not allow the use of t<t1,...,tn> syntax for type applications"))::((Support.Microsoft.FStar.Getopt.noshort, "n_cores", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (n_cores := (Support.Microsoft.FStar.Util.int_of_string x))), "positive integer")), "Maximum number of cores to use for the solver (default 1)"))::((Support.Microsoft.FStar.Getopt.noshort, "verify_module", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (verify_module := (x)::(! (verify_module)))), "string")), "Name of the module to verify"))::((Support.Microsoft.FStar.Getopt.noshort, "use_build_config", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23814 -> (match (_23814) with
| () -> begin
(use_build_config := true)
end))), "Expect just a single file on the command line and no options; will read the \'build-config\' prelude from the file"))::((Support.Microsoft.FStar.Getopt.noshort, "in", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _23815 -> (match (_23815) with
| () -> begin
(interactive := true)
end))), "Interactive mode; reads input from stdin"))::[]
in (('h', "help", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun x -> (let _23818 = (display_usage specs)
in (exit (0))))), "Display this information"))::specs)
end))
and parse_codegen = (fun s -> (match (s) with
| ("OCaml") | ("F#") | ("JavaScript") -> begin
Some (s)
end
| _ -> begin
(let _23826 = (Support.Microsoft.FStar.Util.print_string "Wrong argument to codegen flag\n")
in (let _23828 = (display_usage (specs ()))
in (exit (1))))
end))

let should_verify = (fun m -> ((! (verify)) && (match ((! (verify_module))) with
| [] -> begin
true
end
| l -> begin
(Support.List.contains m l)
end)))

let set_options = (fun s -> (Support.Microsoft.FStar.Getopt.parse_string (specs ()) (fun _23834 -> ()) s))

let reset_options_string = (ref None)

let reset_options = (fun _23836 -> (match (_23836) with
| () -> begin
(let _23837 = (init_options ())
in (match ((! (reset_options_string))) with
| Some (x) -> begin
(set_options x)
end
| _ -> begin
(Support.Microsoft.FStar.Getopt.parse_cmdline (specs ()) (fun x -> ()))
end))
end))




