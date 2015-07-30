
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

let dlevel = (fun ( _11_1 ) -> (match (_11_1) with
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

let one_debug_level_geq = (fun ( l1 ) ( l2 ) -> (match (l1) with
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

let debug_level_geq = (fun ( l2 ) -> ((Support.Microsoft.FStar.Util.for_some (fun ( l1 ) -> (one_debug_level_geq l1 l2))) (! (debug_level))))

let log_types = (Support.Microsoft.FStar.Util.mk_ref false)

let print_effect_args = (Support.Microsoft.FStar.Util.mk_ref false)

let print_real_names = (Support.Microsoft.FStar.Util.mk_ref false)

let dump_module = (Support.Microsoft.FStar.Util.mk_ref None)

let should_dump = (fun ( l ) -> (match ((! (dump_module))) with
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

let _include_path = (Support.Microsoft.FStar.Util.mk_ref [])

let interactive_fsi = (Support.Microsoft.FStar.Util.mk_ref false)

let init_options = (fun ( _11_25 ) -> (match (_11_25) with
| () -> begin
(let _11_26 = (Support.ST.op_Colon_Equals show_signatures [])
in (let _11_28 = (Support.ST.op_Colon_Equals norm_then_print true)
in (let _11_30 = (Support.ST.op_Colon_Equals z3_exe (Support.Microsoft.FStar.Platform.exe "z3"))
in (let _11_32 = (Support.ST.op_Colon_Equals silent false)
in (let _11_34 = (Support.ST.op_Colon_Equals debug [])
in (let _11_36 = (Support.ST.op_Colon_Equals debug_level [])
in (let _11_38 = (Support.ST.op_Colon_Equals log_types false)
in (let _11_40 = (Support.ST.op_Colon_Equals print_effect_args false)
in (let _11_42 = (Support.ST.op_Colon_Equals print_real_names false)
in (let _11_44 = (Support.ST.op_Colon_Equals dump_module None)
in (let _11_46 = (Support.ST.op_Colon_Equals logQueries false)
in (let _11_48 = (Support.ST.op_Colon_Equals z3exe true)
in (let _11_50 = (Support.ST.op_Colon_Equals outputDir (Some (".")))
in (let _11_52 = (Support.ST.op_Colon_Equals fstar_home_opt None)
in (let _11_54 = (Support.ST.op_Colon_Equals _fstar_home "")
in (let _11_56 = (Support.ST.op_Colon_Equals prims_ref None)
in (let _11_58 = (Support.ST.op_Colon_Equals z3timeout 5)
in (let _11_60 = (Support.ST.op_Colon_Equals admit_smt_queries false)
in (let _11_62 = (Support.ST.op_Colon_Equals pretype true)
in (let _11_64 = (Support.ST.op_Colon_Equals codegen None)
in (let _11_66 = (Support.ST.op_Colon_Equals codegen_libs [])
in (let _11_68 = (Support.ST.op_Colon_Equals admit_fsi [])
in (let _11_70 = (Support.ST.op_Colon_Equals trace_error false)
in (let _11_72 = (Support.ST.op_Colon_Equals verify true)
in (let _11_74 = (Support.ST.op_Colon_Equals full_context_dependency true)
in (let _11_76 = (Support.ST.op_Colon_Equals print_implicits false)
in (let _11_78 = (Support.ST.op_Colon_Equals hide_uvar_nums false)
in (let _11_80 = (Support.ST.op_Colon_Equals hide_genident_nums false)
in (let _11_82 = (Support.ST.op_Colon_Equals serialize_mods false)
in (let _11_84 = (Support.ST.op_Colon_Equals initial_fuel 2)
in (let _11_86 = (Support.ST.op_Colon_Equals initial_ifuel 1)
in (let _11_88 = (Support.ST.op_Colon_Equals max_fuel 8)
in (let _11_90 = (Support.ST.op_Colon_Equals min_fuel 1)
in (let _11_92 = (Support.ST.op_Colon_Equals max_ifuel 2)
in (let _11_94 = (Support.ST.op_Colon_Equals warn_top_level_effects false)
in (let _11_96 = (Support.ST.op_Colon_Equals no_slack false)
in (let _11_98 = (Support.ST.op_Colon_Equals eager_inference false)
in (let _11_100 = (Support.ST.op_Colon_Equals unthrottle_inductives false)
in (let _11_102 = (Support.ST.op_Colon_Equals use_eq_at_higher_order false)
in (let _11_104 = (Support.ST.op_Colon_Equals fs_typ_app false)
in (let _11_106 = (Support.ST.op_Colon_Equals n_cores 1)
in (let _11_108 = (Support.ST.op_Colon_Equals split_cases 0)
in (let _11_110 = (Support.ST.op_Colon_Equals verify_module [])
in (Support.ST.op_Colon_Equals _include_path []))))))))))))))))))))))))))))))))))))))))))))
end))

let set_fstar_home = (fun ( _11_112 ) -> (match (_11_112) with
| () -> begin
(let fh = (match ((! (fstar_home_opt))) with
| None -> begin
(let x = (Support.Microsoft.FStar.Util.get_exec_dir ())
in (let x = (Support.String.strcat x "/..")
in (let _11_116 = (Support.ST.op_Colon_Equals _fstar_home x)
in (let _11_118 = (Support.ST.op_Colon_Equals fstar_home_opt (Some (x)))
in x))))
end
| Some (x) -> begin
(let _11_122 = (Support.ST.op_Colon_Equals _fstar_home x)
in x)
end)
in fh)
end))

let get_fstar_home = (fun ( _11_125 ) -> (match (_11_125) with
| () -> begin
(match ((! (fstar_home_opt))) with
| None -> begin
(let _11_127 = ((Support.Prims.ignore) (set_fstar_home ()))
in (! (_fstar_home)))
end
| Some (x) -> begin
x
end)
end))

let get_include_path = (fun ( _11_131 ) -> (match (_11_131) with
| () -> begin
(Support.List.append (! (_include_path)) ((".")::((Support.String.strcat (get_fstar_home ()) "/lib"))::[]))
end))

let prims = (fun ( _11_132 ) -> (match (_11_132) with
| () -> begin
(match ((! (prims_ref))) with
| None -> begin
"prims.fst"
end
| Some (x) -> begin
x
end)
end))

let prependOutputDir = (fun ( fname ) -> (match ((! (outputDir))) with
| None -> begin
fname
end
| Some (x) -> begin
(Support.String.strcat (Support.String.strcat x "/") fname)
end))

let cache_dir = "cache"

let display_usage = (fun ( specs ) -> (let _11_141 = (Support.Microsoft.FStar.Util.print_string "fstar [option] infile...")
in (Support.List.iter (fun ( _11_148 ) -> (match (_11_148) with
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

let rec specs = (fun ( _11_156 ) -> (match (_11_156) with
| () -> begin
(let specs = ((Support.Microsoft.FStar.Getopt.noshort, "trace_error", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_157 ) -> (match (_11_157) with
| () -> begin
(Support.ST.op_Colon_Equals trace_error true)
end))), "Don\'t print an error message; show an exception trace instead"))::((Support.Microsoft.FStar.Getopt.noshort, "codegen", Support.Microsoft.FStar.Getopt.OneArg (((fun ( s ) -> (let _11_159 = (Support.ST.op_Colon_Equals codegen (parse_codegen s))
in (Support.ST.op_Colon_Equals verify false))), "OCaml")), "Generate code for execution"))::((Support.Microsoft.FStar.Getopt.noshort, "codegen-lib", Support.Microsoft.FStar.Getopt.OneArg (((fun ( s ) -> (Support.ST.op_Colon_Equals codegen_libs (((Support.Microsoft.FStar.Util.split s "."))::(! (codegen_libs))))), "namespace")), "External runtime library library"))::((Support.Microsoft.FStar.Getopt.noshort, "lax", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_162 ) -> (match (_11_162) with
| () -> begin
(let _11_163 = (Support.ST.op_Colon_Equals pretype true)
in (Support.ST.op_Colon_Equals verify false))
end))), "Run the lax-type checker only (admit all verification conditions)"))::((Support.Microsoft.FStar.Getopt.noshort, "fstar_home", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (Support.ST.op_Colon_Equals fstar_home_opt (Some (x)))), "dir")), "Set the FSTAR_HOME variable to dir"))::((Support.Microsoft.FStar.Getopt.noshort, "silent", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_166 ) -> (match (_11_166) with
| () -> begin
(Support.ST.op_Colon_Equals silent true)
end))), ""))::((Support.Microsoft.FStar.Getopt.noshort, "prims", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (Support.ST.op_Colon_Equals prims_ref (Some (x)))), "file")), ""))::((Support.Microsoft.FStar.Getopt.noshort, "prn", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_168 ) -> (match (_11_168) with
| () -> begin
(Support.ST.op_Colon_Equals print_real_names true)
end))), "Print real names---you may want to use this in conjunction with logQueries"))::((Support.Microsoft.FStar.Getopt.noshort, "debug", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (Support.ST.op_Colon_Equals debug ((x)::(! (debug))))), "module name")), "Print LOTS of debugging information while checking module [arg]"))::((Support.Microsoft.FStar.Getopt.noshort, "debug_level", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (Support.ST.op_Colon_Equals debug_level (((dlevel x))::(! (debug_level))))), "Low|Medium|High|Extreme")), "Control the verbosity of debugging info"))::((Support.Microsoft.FStar.Getopt.noshort, "log_types", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_171 ) -> (match (_11_171) with
| () -> begin
(Support.ST.op_Colon_Equals log_types true)
end))), "Print types computed for data/val/let-bindings"))::((Support.Microsoft.FStar.Getopt.noshort, "print_effect_args", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_172 ) -> (match (_11_172) with
| () -> begin
(Support.ST.op_Colon_Equals print_effect_args true)
end))), "Print inferred predicate transformers for all computation types"))::((Support.Microsoft.FStar.Getopt.noshort, "dump_module", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (Support.ST.op_Colon_Equals dump_module (Some (x)))), "module name")), ""))::((Support.Microsoft.FStar.Getopt.noshort, "z3timeout", Support.Microsoft.FStar.Getopt.OneArg (((fun ( s ) -> (Support.ST.op_Colon_Equals z3timeout (Support.Microsoft.FStar.Util.int_of_string s))), "t")), "Set the Z3 per-query (soft) timeout to t seconds (default 5)"))::((Support.Microsoft.FStar.Getopt.noshort, "admit_smt_queries", Support.Microsoft.FStar.Getopt.OneArg (((fun ( s ) -> (Support.ST.op_Colon_Equals admit_smt_queries (if (s = "true") then begin
true
end else begin
if (s = "false") then begin
false
end else begin
(failwith "Invalid argument to --admit_smt_queries")
end
end))), "true|false")), "Admit SMT queries (UNSAFE! But, useful during development); default: \'false\'"))::((Support.Microsoft.FStar.Getopt.noshort, "logQueries", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_176 ) -> (match (_11_176) with
| () -> begin
(Support.ST.op_Colon_Equals logQueries true)
end))), "Log the Z3 queries in queries.smt2"))::((Support.Microsoft.FStar.Getopt.noshort, "admit_fsi", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (Support.ST.op_Colon_Equals admit_fsi ((x)::(! (admit_fsi))))), "module name")), "Treat .fsi as a .fst"))::((Support.Microsoft.FStar.Getopt.noshort, "odir", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (Support.ST.op_Colon_Equals outputDir (Some (x)))), "dir")), "Place output in directory dir"))::((Support.Microsoft.FStar.Getopt.noshort, "smt", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (Support.ST.op_Colon_Equals z3_exe x)), "path")), "Path to the SMT solver (usually Z3, but could be any SMT2-compatible solver)"))::((Support.Microsoft.FStar.Getopt.noshort, "print_before_norm", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_180 ) -> (match (_11_180) with
| () -> begin
(Support.ST.op_Colon_Equals norm_then_print false)
end))), "Do not normalize types before printing (for debugging)"))::((Support.Microsoft.FStar.Getopt.noshort, "show_signatures", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (Support.ST.op_Colon_Equals show_signatures ((x)::(! (show_signatures))))), "module name")), "Show the checked signatures for all top-level symbols in the module"))::((Support.Microsoft.FStar.Getopt.noshort, "full_context_dependency", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_182 ) -> (match (_11_182) with
| () -> begin
(Support.ST.op_Colon_Equals full_context_dependency true)
end))), "Introduce unification variables that are dependent on the entire context (possibly expensive, but better for type inference (on, by default)"))::((Support.Microsoft.FStar.Getopt.noshort, "MLish", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_183 ) -> (match (_11_183) with
| () -> begin
(Support.ST.op_Colon_Equals full_context_dependency false)
end))), "Introduce unification variables that are only dependent on the type variables in the context"))::((Support.Microsoft.FStar.Getopt.noshort, "print_implicits", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_184 ) -> (match (_11_184) with
| () -> begin
(Support.ST.op_Colon_Equals print_implicits true)
end))), "Print implicit arguments"))::((Support.Microsoft.FStar.Getopt.noshort, "hide_uvar_nums", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_185 ) -> (match (_11_185) with
| () -> begin
(Support.ST.op_Colon_Equals hide_uvar_nums true)
end))), "Don\'t print unification variable numbers"))::((Support.Microsoft.FStar.Getopt.noshort, "hide_genident_nums", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_186 ) -> (match (_11_186) with
| () -> begin
(Support.ST.op_Colon_Equals hide_genident_nums true)
end))), "Don\'t print generated identifier numbers"))::((Support.Microsoft.FStar.Getopt.noshort, "serialize_mods", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_187 ) -> (match (_11_187) with
| () -> begin
(Support.ST.op_Colon_Equals serialize_mods true)
end))), "Serialize compiled modules"))::((Support.Microsoft.FStar.Getopt.noshort, "initial_fuel", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (Support.ST.op_Colon_Equals initial_fuel (Support.Microsoft.FStar.Util.int_of_string x))), "non-negative integer")), "Number of unrolling of recursive functions to try initially (default 2)"))::((Support.Microsoft.FStar.Getopt.noshort, "max_fuel", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (Support.ST.op_Colon_Equals max_fuel (Support.Microsoft.FStar.Util.int_of_string x))), "non-negative integer")), "Number of unrolling of recursive functions to try at most (default 8)"))::((Support.Microsoft.FStar.Getopt.noshort, "min_fuel", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (Support.ST.op_Colon_Equals min_fuel (Support.Microsoft.FStar.Util.int_of_string x))), "non-negative integer")), "Minimum number of unrolling of recursive functions to try (default 1)"))::((Support.Microsoft.FStar.Getopt.noshort, "initial_ifuel", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (Support.ST.op_Colon_Equals initial_ifuel (Support.Microsoft.FStar.Util.int_of_string x))), "non-negative integer")), "Number of unrolling of inductive datatypes to try at first (default 1)"))::((Support.Microsoft.FStar.Getopt.noshort, "max_ifuel", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (Support.ST.op_Colon_Equals max_ifuel (Support.Microsoft.FStar.Util.int_of_string x))), "non-negative integer")), "Number of unrolling of inductive datatypes to try at most (default 1)"))::((Support.Microsoft.FStar.Getopt.noshort, "warn_top_level_effects", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_193 ) -> (match (_11_193) with
| () -> begin
(Support.ST.op_Colon_Equals warn_top_level_effects true)
end))), "Top-level effects are ignored, by default; turn this flag on to be warned when this happens"))::((Support.Microsoft.FStar.Getopt.noshort, "no_slack", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_194 ) -> (match (_11_194) with
| () -> begin
(Support.ST.op_Colon_Equals no_slack true)
end))), "Use the partially flow-insensitive variant of --rel2 (experimental)"))::((Support.Microsoft.FStar.Getopt.noshort, "eager_inference", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_195 ) -> (match (_11_195) with
| () -> begin
(Support.ST.op_Colon_Equals eager_inference true)
end))), "Solve all type-inference constraints eagerly; more efficient but at the cost of generality"))::((Support.Microsoft.FStar.Getopt.noshort, "unthrottle_inductives", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_196 ) -> (match (_11_196) with
| () -> begin
(Support.ST.op_Colon_Equals unthrottle_inductives true)
end))), "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)"))::((Support.Microsoft.FStar.Getopt.noshort, "use_eq_at_higher_order", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_197 ) -> (match (_11_197) with
| () -> begin
(Support.ST.op_Colon_Equals use_eq_at_higher_order true)
end))), "Use equality constraints when comparing higher-order types; temporary"))::((Support.Microsoft.FStar.Getopt.noshort, "fs_typ_app", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_198 ) -> (match (_11_198) with
| () -> begin
(Support.ST.op_Colon_Equals fs_typ_app true)
end))), "Allow the use of t<t1,...,tn> syntax for type applications; brittle since it clashes with the integer less-than operator"))::((Support.Microsoft.FStar.Getopt.noshort, "no_fs_typ_app", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_199 ) -> (match (_11_199) with
| () -> begin
(Support.ST.op_Colon_Equals fs_typ_app false)
end))), "Do not allow the use of t<t1,...,tn> syntax for type applications"))::((Support.Microsoft.FStar.Getopt.noshort, "n_cores", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (Support.ST.op_Colon_Equals n_cores (Support.Microsoft.FStar.Util.int_of_string x))), "positive integer")), "Maximum number of cores to use for the solver (default 1)"))::((Support.Microsoft.FStar.Getopt.noshort, "verify_module", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (Support.ST.op_Colon_Equals verify_module ((x)::(! (verify_module))))), "string")), "Name of the module to verify"))::((Support.Microsoft.FStar.Getopt.noshort, "use_build_config", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_202 ) -> (match (_11_202) with
| () -> begin
(Support.ST.op_Colon_Equals use_build_config true)
end))), "Expect just a single file on the command line and no options; will read the \'build-config\' prelude from the file"))::((Support.Microsoft.FStar.Getopt.noshort, "split_cases", Support.Microsoft.FStar.Getopt.OneArg (((fun ( n ) -> (Support.ST.op_Colon_Equals split_cases (Support.Microsoft.FStar.Util.int_of_string n))), "t")), "Partition VC of a match into groups of n cases"))::((Support.Microsoft.FStar.Getopt.noshort, "in", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_204 ) -> (match (_11_204) with
| () -> begin
(Support.ST.op_Colon_Equals interactive true)
end))), "Interactive mode; reads input from stdin"))::((Support.Microsoft.FStar.Getopt.noshort, "include", Support.Microsoft.FStar.Getopt.OneArg (((fun ( s ) -> (Support.ST.op_Colon_Equals _include_path (Support.List.append (! (_include_path)) ((s)::[])))), "path")), "A directory in which to search for files included on the command line"))::((Support.Microsoft.FStar.Getopt.noshort, "fsi", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_206 ) -> (match (_11_206) with
| () -> begin
(set_interactive_fsi ())
end))), "fsi flag; A flag to indicate if type checking a fsi in the interactive mode"))::[]
in (('h', "help", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( x ) -> (let _11_209 = (display_usage specs)
in (exit (0))))), "Display this information"))::specs)
end))
and parse_codegen = (fun ( s ) -> (match (s) with
| ("OCaml-experimental") | ("OCaml") -> begin
Some (s)
end
| _ -> begin
(let _11_216 = (Support.Microsoft.FStar.Util.print_string "Wrong argument to codegen flag\n")
in (let _11_218 = (display_usage (specs ()))
in (exit (1))))
end))
and set_interactive_fsi = (fun ( _11_220 ) -> if (! (interactive)) then begin
(Support.ST.op_Colon_Equals interactive_fsi true)
end else begin
(let _11_222 = (Support.Microsoft.FStar.Util.print_string "Set interactive flag first before setting interactive fsi flag\n")
in (let _11_224 = (display_usage (specs ()))
in (exit (1))))
end)

let should_verify = (fun ( m ) -> ((! (verify)) && (match ((! (verify_module))) with
| [] -> begin
true
end
| l -> begin
(Support.List.contains m l)
end)))

let set_options = (fun ( s ) -> (Support.Microsoft.FStar.Getopt.parse_string (specs ()) (fun ( _11_230 ) -> ()) s))

let reset_options_string = (ref None)

let reset_options = (fun ( _11_232 ) -> (match (_11_232) with
| () -> begin
(let _11_233 = (init_options ())
in (match ((! (reset_options_string))) with
| Some (x) -> begin
(set_options x)
end
| _ -> begin
(Support.Microsoft.FStar.Getopt.parse_cmdline (specs ()) (fun ( x ) -> ()))
end))
end))




