
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

let dlevel = (fun _23865 -> (match (_23865) with
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

let split_cases = (Support.Microsoft.FStar.Util.mk_ref 0)

let init_options = (fun _23889 -> (match (_23889) with
| () -> begin
(let _23890 = (show_signatures := [])
in (let _23892 = (norm_then_print := true)
in (let _23894 = (z3_exe := (Support.Microsoft.FStar.Platform.exe "z3"))
in (let _23896 = (silent := false)
in (let _23898 = (debug := [])
in (let _23900 = (debug_level := [])
in (let _23902 = (log_types := false)
in (let _23904 = (print_effect_args := false)
in (let _23906 = (print_real_names := false)
in (let _23908 = (dump_module := None)
in (let _23910 = (logQueries := false)
in (let _23912 = (z3exe := true)
in (let _23914 = (outputDir := Some ("."))
in (let _23916 = (fstar_home_opt := None)
in (let _23918 = (_fstar_home := "")
in (let _23920 = (prims_ref := None)
in (let _23922 = (z3timeout := 5)
in (let _23924 = (admit_smt_queries := false)
in (let _23926 = (pretype := true)
in (let _23928 = (codegen := None)
in (let _23930 = (codegen_libs := [])
in (let _23932 = (admit_fsi := [])
in (let _23934 = (trace_error := false)
in (let _23936 = (verify := true)
in (let _23938 = (full_context_dependency := true)
in (let _23940 = (print_implicits := false)
in (let _23942 = (hide_uvar_nums := false)
in (let _23944 = (hide_genident_nums := false)
in (let _23946 = (serialize_mods := false)
in (let _23948 = (initial_fuel := 2)
in (let _23950 = (initial_ifuel := 1)
in (let _23952 = (max_fuel := 8)
in (let _23954 = (min_fuel := 1)
in (let _23956 = (max_ifuel := 2)
in (let _23958 = (warn_top_level_effects := false)
in (let _23960 = (no_slack := false)
in (let _23962 = (eager_inference := false)
in (let _23964 = (unthrottle_inductives := false)
in (let _23966 = (use_eq_at_higher_order := false)
in (let _23968 = (fs_typ_app := false)
in (let _23970 = (n_cores := 1)
in (let _23972 = (split_cases := 0)
in (verify_module := [])))))))))))))))))))))))))))))))))))))))))))
end))

let set_fstar_home = (fun _23974 -> (match (_23974) with
| () -> begin
(let fh = (match ((! (fstar_home_opt))) with
| None -> begin
(let x = (Support.Microsoft.FStar.Util.get_exec_dir ())
in (let x = (Support.String.strcat x "/..")
in (let _23978 = (_fstar_home := x)
in (let _23980 = (fstar_home_opt := Some (x))
in x))))
end
| Some (x) -> begin
(let _23984 = (_fstar_home := x)
in x)
end)
in fh)
end))

let get_fstar_home = (fun _23987 -> (match (_23987) with
| () -> begin
(match ((! (fstar_home_opt))) with
| None -> begin
(let _23989 = ((Support.Prims.ignore) (set_fstar_home ()))
in (! (_fstar_home)))
end
| Some (x) -> begin
x
end)
end))

let prims = (fun _23993 -> (match (_23993) with
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

let display_usage = (fun specs -> (let _24002 = (Support.Microsoft.FStar.Util.print_string "fstar [option] infile...")
in (Support.List.iter (fun _24009 -> (match (_24009) with
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

let rec specs = (fun _24017 -> (match (_24017) with
| () -> begin
(let specs = ((Support.Microsoft.FStar.Getopt.noshort, "trace_error", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _24018 -> (match (_24018) with
| () -> begin
(trace_error := true)
end))), "Don\'t print an error message; show an exception trace instead"))::((Support.Microsoft.FStar.Getopt.noshort, "codegen", Support.Microsoft.FStar.Getopt.OneArg (((fun s -> (let _24020 = (codegen := (parse_codegen s))
in (verify := false))), "OCaml|F#|JavaScript")), "Generate code for execution"))::((Support.Microsoft.FStar.Getopt.noshort, "codegen-lib", Support.Microsoft.FStar.Getopt.OneArg (((fun s -> (codegen_libs := ((Support.Microsoft.FStar.Util.split s "."))::(! (codegen_libs)))), "namespace")), "External runtime library library"))::((Support.Microsoft.FStar.Getopt.noshort, "lax", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _24023 -> (match (_24023) with
| () -> begin
(let _24024 = (pretype := true)
in (verify := false))
end))), "Run the lax-type checker only (admit all verification conditions)"))::((Support.Microsoft.FStar.Getopt.noshort, "fstar_home", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (fstar_home_opt := Some (x))), "dir")), "Set the FSTAR_HOME variable to dir"))::((Support.Microsoft.FStar.Getopt.noshort, "silent", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _24027 -> (match (_24027) with
| () -> begin
(silent := true)
end))), ""))::((Support.Microsoft.FStar.Getopt.noshort, "prims", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (prims_ref := Some (x))), "file")), ""))::((Support.Microsoft.FStar.Getopt.noshort, "prn", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _24029 -> (match (_24029) with
| () -> begin
(print_real_names := true)
end))), "Print real names---you may want to use this in conjunction with logQueries"))::((Support.Microsoft.FStar.Getopt.noshort, "debug", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (debug := (x)::(! (debug)))), "module name")), "Print LOTS of debugging information while checking module [arg]"))::((Support.Microsoft.FStar.Getopt.noshort, "debug_level", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (debug_level := ((dlevel x))::(! (debug_level)))), "Low|Medium|High|Extreme")), "Control the verbosity of debugging info"))::((Support.Microsoft.FStar.Getopt.noshort, "log_types", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _24032 -> (match (_24032) with
| () -> begin
(log_types := true)
end))), "Print types computed for data/val/let-bindings"))::((Support.Microsoft.FStar.Getopt.noshort, "print_effect_args", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _24033 -> (match (_24033) with
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
end)), "true|false")), "Admit SMT queries (UNSAFE! But, useful during development); default: \'false\'"))::((Support.Microsoft.FStar.Getopt.noshort, "logQueries", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _24037 -> (match (_24037) with
| () -> begin
(logQueries := true)
end))), "Log the Z3 queries in queries.smt2"))::((Support.Microsoft.FStar.Getopt.noshort, "admit_fsi", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (admit_fsi := (x)::(! (admit_fsi)))), "module name")), "Treat .fsi as a .fst"))::((Support.Microsoft.FStar.Getopt.noshort, "odir", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (outputDir := Some (x))), "dir")), "Place output in directory dir"))::((Support.Microsoft.FStar.Getopt.noshort, "smt", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (z3_exe := x)), "path")), "Path to the SMT solver (usually Z3, but could be any SMT2-compatible solver)"))::((Support.Microsoft.FStar.Getopt.noshort, "print_before_norm", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _24041 -> (match (_24041) with
| () -> begin
(norm_then_print := false)
end))), "Do not normalize types before printing (for debugging)"))::((Support.Microsoft.FStar.Getopt.noshort, "show_signatures", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (show_signatures := (x)::(! (show_signatures)))), "module name")), "Show the checked signatures for all top-level symbols in the module"))::((Support.Microsoft.FStar.Getopt.noshort, "full_context_dependency", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _24043 -> (match (_24043) with
| () -> begin
(full_context_dependency := true)
end))), "Introduce unification variables that are dependent on the entire context (possibly expensive, but better for type inference (on, by default)"))::((Support.Microsoft.FStar.Getopt.noshort, "MLish", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _24044 -> (match (_24044) with
| () -> begin
(full_context_dependency := false)
end))), "Introduce unification variables that are only dependent on the type variables in the context"))::((Support.Microsoft.FStar.Getopt.noshort, "print_implicits", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _24045 -> (match (_24045) with
| () -> begin
(print_implicits := true)
end))), "Print implicit arguments"))::((Support.Microsoft.FStar.Getopt.noshort, "hide_uvar_nums", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _24046 -> (match (_24046) with
| () -> begin
(hide_uvar_nums := true)
end))), "Don\'t print unification variable numbers"))::((Support.Microsoft.FStar.Getopt.noshort, "hide_genident_nums", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _24047 -> (match (_24047) with
| () -> begin
(hide_genident_nums := true)
end))), "Don\'t print generated identifier numbers"))::((Support.Microsoft.FStar.Getopt.noshort, "serialize_mods", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _24048 -> (match (_24048) with
| () -> begin
(serialize_mods := true)
end))), "Serialize compiled modules"))::((Support.Microsoft.FStar.Getopt.noshort, "initial_fuel", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (initial_fuel := (Support.Microsoft.FStar.Util.int_of_string x))), "non-negative integer")), "Number of unrolling of recursive functions to try initially (default 2)"))::((Support.Microsoft.FStar.Getopt.noshort, "max_fuel", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (max_fuel := (Support.Microsoft.FStar.Util.int_of_string x))), "non-negative integer")), "Number of unrolling of recursive functions to try at most (default 8)"))::((Support.Microsoft.FStar.Getopt.noshort, "min_fuel", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (min_fuel := (Support.Microsoft.FStar.Util.int_of_string x))), "non-negative integer")), "Minimum number of unrolling of recursive functions to try (default 1)"))::((Support.Microsoft.FStar.Getopt.noshort, "initial_ifuel", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (initial_ifuel := (Support.Microsoft.FStar.Util.int_of_string x))), "non-negative integer")), "Number of unrolling of inductive datatypes to try at first (default 1)"))::((Support.Microsoft.FStar.Getopt.noshort, "max_ifuel", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (max_ifuel := (Support.Microsoft.FStar.Util.int_of_string x))), "non-negative integer")), "Number of unrolling of inductive datatypes to try at most (default 1)"))::((Support.Microsoft.FStar.Getopt.noshort, "warn_top_level_effects", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _24054 -> (match (_24054) with
| () -> begin
(warn_top_level_effects := true)
end))), "Top-level effects are ignored, by default; turn this flag on to be warned when this happens"))::((Support.Microsoft.FStar.Getopt.noshort, "no_slack", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _24055 -> (match (_24055) with
| () -> begin
(no_slack := true)
end))), "Use the partially flow-insensitive variant of --rel2 (experimental)"))::((Support.Microsoft.FStar.Getopt.noshort, "eager_inference", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _24056 -> (match (_24056) with
| () -> begin
(eager_inference := true)
end))), "Solve all type-inference constraints eagerly; more efficient but at the cost of generality"))::((Support.Microsoft.FStar.Getopt.noshort, "unthrottle_inductives", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _24057 -> (match (_24057) with
| () -> begin
(unthrottle_inductives := true)
end))), "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)"))::((Support.Microsoft.FStar.Getopt.noshort, "use_eq_at_higher_order", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _24058 -> (match (_24058) with
| () -> begin
(use_eq_at_higher_order := true)
end))), "Use equality constraints when comparing higher-order types; temporary"))::((Support.Microsoft.FStar.Getopt.noshort, "fs_typ_app", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _24059 -> (match (_24059) with
| () -> begin
(fs_typ_app := true)
end))), "Allow the use of t<t1,...,tn> syntax for type applications; brittle since it clashes with the integer less-than operator"))::((Support.Microsoft.FStar.Getopt.noshort, "no_fs_typ_app", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _24060 -> (match (_24060) with
| () -> begin
(fs_typ_app := false)
end))), "Do not allow the use of t<t1,...,tn> syntax for type applications"))::((Support.Microsoft.FStar.Getopt.noshort, "n_cores", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (n_cores := (Support.Microsoft.FStar.Util.int_of_string x))), "positive integer")), "Maximum number of cores to use for the solver (default 1)"))::((Support.Microsoft.FStar.Getopt.noshort, "verify_module", Support.Microsoft.FStar.Getopt.OneArg (((fun x -> (verify_module := (x)::(! (verify_module)))), "string")), "Name of the module to verify"))::((Support.Microsoft.FStar.Getopt.noshort, "use_build_config", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _24063 -> (match (_24063) with
| () -> begin
(use_build_config := true)
end))), "Expect just a single file on the command line and no options; will read the \'build-config\' prelude from the file"))::((Support.Microsoft.FStar.Getopt.noshort, "split_cases", Support.Microsoft.FStar.Getopt.OneArg (((fun n -> (split_cases := (Support.Microsoft.FStar.Util.int_of_string n))), "t")), "Partition VC of a match into groups of n cases"))::((Support.Microsoft.FStar.Getopt.noshort, "in", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun _24065 -> (match (_24065) with
| () -> begin
(interactive := true)
end))), "Interactive mode; reads input from stdin"))::[]
in (('h', "help", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun x -> (let _24068 = (display_usage specs)
in (exit (0))))), "Display this information"))::specs)
end))
and parse_codegen = (fun s -> (match (s) with
| ("OCaml") | ("F#") | ("JavaScript") -> begin
Some (s)
end
| _ -> begin
(let _24076 = (Support.Microsoft.FStar.Util.print_string "Wrong argument to codegen flag\n")
in (let _24078 = (display_usage (specs ()))
in (exit (1))))
end))

let should_verify = (fun m -> ((! (verify)) && (match ((! (verify_module))) with
| [] -> begin
true
end
| l -> begin
(Support.List.contains m l)
end)))

let set_options = (fun s -> (Support.Microsoft.FStar.Getopt.parse_string (specs ()) (fun _24084 -> ()) s))

let reset_options_string = (ref None)

let reset_options = (fun _24086 -> (match (_24086) with
| () -> begin
(let _24087 = (init_options ())
in (match ((! (reset_options_string))) with
| Some (x) -> begin
(set_options x)
end
| _ -> begin
(Support.Microsoft.FStar.Getopt.parse_cmdline (specs ()) (fun x -> ()))
end))
end))




