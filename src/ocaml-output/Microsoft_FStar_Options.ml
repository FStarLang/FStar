
type debug_level_t =
| Low
| Medium
| High
| Extreme
| Other of Prims.string

let is_Low = (fun _discr_ -> (match (_discr_) with
| Low -> begin
true
end
| _ -> begin
false
end))

let is_Medium = (fun _discr_ -> (match (_discr_) with
| Medium -> begin
true
end
| _ -> begin
false
end))

let is_High = (fun _discr_ -> (match (_discr_) with
| High -> begin
true
end
| _ -> begin
false
end))

let is_Extreme = (fun _discr_ -> (match (_discr_) with
| Extreme -> begin
true
end
| _ -> begin
false
end))

let is_Other = (fun _discr_ -> (match (_discr_) with
| Other (_) -> begin
true
end
| _ -> begin
false
end))

let ___Other____0 = (fun projectee -> (match (projectee) with
| Other (_20_4) -> begin
_20_4
end))

let show_signatures = (Microsoft_FStar_Util.mk_ref [])

let norm_then_print = (Microsoft_FStar_Util.mk_ref true)

let z3_exe = (let _86_19 = (Microsoft_FStar_Platform.exe "z3")
in (Microsoft_FStar_Util.mk_ref _86_19))

let silent = (Microsoft_FStar_Util.mk_ref false)

let debug = (Microsoft_FStar_Util.mk_ref [])

let debug_level = (Microsoft_FStar_Util.mk_ref [])

let dlevel = (fun _20_1 -> (match (_20_1) with
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

let debug_level_geq = (fun l2 -> (let _86_29 = (ST.read debug_level)
in (All.pipe_right _86_29 (Microsoft_FStar_Util.for_some (fun l1 -> (one_debug_level_geq l1 l2))))))

let log_types = (Microsoft_FStar_Util.mk_ref false)

let print_effect_args = (Microsoft_FStar_Util.mk_ref false)

let print_real_names = (Microsoft_FStar_Util.mk_ref false)

let dump_module = (Microsoft_FStar_Util.mk_ref None)

let should_dump = (fun l -> (match ((ST.read dump_module)) with
| None -> begin
false
end
| Some (m) -> begin
(m = l)
end))

let logQueries = (Microsoft_FStar_Util.mk_ref false)

let z3exe = (Microsoft_FStar_Util.mk_ref true)

let outputDir = (Microsoft_FStar_Util.mk_ref (Some (".")))

let fstar_home_opt = (Microsoft_FStar_Util.mk_ref None)

let _fstar_home = (Microsoft_FStar_Util.mk_ref "")

let prims_ref = (Microsoft_FStar_Util.mk_ref None)

let z3timeout = (Microsoft_FStar_Util.mk_ref 5)

let admit_smt_queries = (Microsoft_FStar_Util.mk_ref false)

let pretype = (Microsoft_FStar_Util.mk_ref true)

let codegen = (Microsoft_FStar_Util.mk_ref None)

let admit_fsi = (Microsoft_FStar_Util.mk_ref [])

let codegen_libs = (Microsoft_FStar_Util.mk_ref [])

let trace_error = (Microsoft_FStar_Util.mk_ref false)

let verify = (Microsoft_FStar_Util.mk_ref true)

let full_context_dependency = (Microsoft_FStar_Util.mk_ref true)

let print_implicits = (Microsoft_FStar_Util.mk_ref false)

let hide_uvar_nums = (Microsoft_FStar_Util.mk_ref false)

let hide_genident_nums = (Microsoft_FStar_Util.mk_ref false)

let serialize_mods = (Microsoft_FStar_Util.mk_ref false)

let initial_fuel = (Microsoft_FStar_Util.mk_ref 2)

let initial_ifuel = (Microsoft_FStar_Util.mk_ref 1)

let max_fuel = (Microsoft_FStar_Util.mk_ref 8)

let min_fuel = (Microsoft_FStar_Util.mk_ref 1)

let max_ifuel = (Microsoft_FStar_Util.mk_ref 2)

let warn_top_level_effects = (Microsoft_FStar_Util.mk_ref false)

let no_slack = (Microsoft_FStar_Util.mk_ref false)

let eager_inference = (Microsoft_FStar_Util.mk_ref false)

let unthrottle_inductives = (Microsoft_FStar_Util.mk_ref false)

let use_eq_at_higher_order = (Microsoft_FStar_Util.mk_ref false)

let fs_typ_app = (Microsoft_FStar_Util.mk_ref false)

let n_cores = (Microsoft_FStar_Util.mk_ref 1)

let verify_module = (Microsoft_FStar_Util.mk_ref [])

let use_build_config = (Microsoft_FStar_Util.mk_ref false)

let interactive = (Microsoft_FStar_Util.mk_ref false)

let split_cases = (Microsoft_FStar_Util.mk_ref 0)

let _include_path = (Microsoft_FStar_Util.mk_ref [])

let interactive_fsi = (Microsoft_FStar_Util.mk_ref false)

let print_fuels = (Microsoft_FStar_Util.mk_ref false)

let __temp_no_proj = (Microsoft_FStar_Util.mk_ref false)

let init_options = (fun _20_26 -> (match (()) with
| () -> begin
(let _20_27 = (ST.op_Colon_Equals show_signatures [])
in (let _20_29 = (ST.op_Colon_Equals norm_then_print true)
in (let _20_31 = (let _86_34 = (Microsoft_FStar_Platform.exe "z3")
in (ST.op_Colon_Equals z3_exe _86_34))
in (let _20_33 = (ST.op_Colon_Equals silent false)
in (let _20_35 = (ST.op_Colon_Equals debug [])
in (let _20_37 = (ST.op_Colon_Equals debug_level [])
in (let _20_39 = (ST.op_Colon_Equals log_types false)
in (let _20_41 = (ST.op_Colon_Equals print_effect_args false)
in (let _20_43 = (ST.op_Colon_Equals print_real_names false)
in (let _20_45 = (ST.op_Colon_Equals dump_module None)
in (let _20_47 = (ST.op_Colon_Equals logQueries false)
in (let _20_49 = (ST.op_Colon_Equals z3exe true)
in (let _20_51 = (ST.op_Colon_Equals outputDir (Some (".")))
in (let _20_53 = (ST.op_Colon_Equals fstar_home_opt None)
in (let _20_55 = (ST.op_Colon_Equals _fstar_home "")
in (let _20_57 = (ST.op_Colon_Equals prims_ref None)
in (let _20_59 = (ST.op_Colon_Equals z3timeout 5)
in (let _20_61 = (ST.op_Colon_Equals admit_smt_queries false)
in (let _20_63 = (ST.op_Colon_Equals pretype true)
in (let _20_65 = (ST.op_Colon_Equals codegen None)
in (let _20_67 = (ST.op_Colon_Equals codegen_libs [])
in (let _20_69 = (ST.op_Colon_Equals admit_fsi [])
in (let _20_71 = (ST.op_Colon_Equals trace_error false)
in (let _20_73 = (ST.op_Colon_Equals verify true)
in (let _20_75 = (ST.op_Colon_Equals full_context_dependency true)
in (let _20_77 = (ST.op_Colon_Equals print_implicits false)
in (let _20_79 = (ST.op_Colon_Equals hide_uvar_nums false)
in (let _20_81 = (ST.op_Colon_Equals hide_genident_nums false)
in (let _20_83 = (ST.op_Colon_Equals serialize_mods false)
in (let _20_85 = (ST.op_Colon_Equals initial_fuel 2)
in (let _20_87 = (ST.op_Colon_Equals initial_ifuel 1)
in (let _20_89 = (ST.op_Colon_Equals max_fuel 8)
in (let _20_91 = (ST.op_Colon_Equals min_fuel 1)
in (let _20_93 = (ST.op_Colon_Equals max_ifuel 2)
in (let _20_95 = (ST.op_Colon_Equals warn_top_level_effects false)
in (let _20_97 = (ST.op_Colon_Equals no_slack false)
in (let _20_99 = (ST.op_Colon_Equals eager_inference false)
in (let _20_101 = (ST.op_Colon_Equals unthrottle_inductives false)
in (let _20_103 = (ST.op_Colon_Equals use_eq_at_higher_order false)
in (let _20_105 = (ST.op_Colon_Equals fs_typ_app false)
in (let _20_107 = (ST.op_Colon_Equals n_cores 1)
in (let _20_109 = (ST.op_Colon_Equals split_cases 0)
in (let _20_111 = (ST.op_Colon_Equals verify_module [])
in (let _20_113 = (ST.op_Colon_Equals _include_path [])
in (ST.op_Colon_Equals print_fuels false)))))))))))))))))))))))))))))))))))))))))))))
end))

let set_fstar_home = (fun _20_115 -> (match (()) with
| () -> begin
(let fh = (match ((ST.read fstar_home_opt)) with
| None -> begin
(let x = (Microsoft_FStar_Util.get_exec_dir ())
in (let x = (Prims.strcat x "/..")
in (let _20_119 = (ST.op_Colon_Equals _fstar_home x)
in (let _20_121 = (ST.op_Colon_Equals fstar_home_opt (Some (x)))
in x))))
end
| Some (x) -> begin
(let _20_125 = (ST.op_Colon_Equals _fstar_home x)
in x)
end)
in fh)
end))

let get_fstar_home = (fun _20_128 -> (match (()) with
| () -> begin
(match ((ST.read fstar_home_opt)) with
| None -> begin
(let _20_130 = (let _86_39 = (set_fstar_home ())
in (All.pipe_left Prims.ignore _86_39))
in (ST.read _fstar_home))
end
| Some (x) -> begin
x
end)
end))

let get_include_path = (fun _20_134 -> (match (()) with
| () -> begin
(let _86_46 = (ST.read _include_path)
in (let _86_45 = (let _86_44 = (let _86_43 = (let _86_42 = (get_fstar_home ())
in (Prims.strcat _86_42 "/lib"))
in (_86_43)::[])
in (".")::_86_44)
in (Microsoft_FStar_List.append _86_46 _86_45)))
end))

let prims = (fun _20_135 -> (match (()) with
| () -> begin
(match ((ST.read prims_ref)) with
| None -> begin
"prims.fst"
end
| Some (x) -> begin
x
end)
end))

let prependOutputDir = (fun fname -> (match ((ST.read outputDir)) with
| None -> begin
fname
end
| Some (x) -> begin
(Prims.strcat (Prims.strcat x "/") fname)
end))

let cache_dir = "cache"

let display_usage = (fun specs -> (let _20_144 = (Microsoft_FStar_Util.print_string "fstar [option] infile...")
in (Microsoft_FStar_List.iter (fun _20_151 -> (match (_20_151) with
| (_20_147, flag, p, doc) -> begin
(match (p) with
| Microsoft_FStar_Getopt.ZeroArgs (ig) -> begin
(match ((doc = "")) with
| true -> begin
(let _86_54 = (Microsoft_FStar_Util.format1 "  --%s\n" flag)
in (Microsoft_FStar_Util.print_string _86_54))
end
| false -> begin
(let _86_55 = (Microsoft_FStar_Util.format2 "  --%s  %s\n" flag doc)
in (Microsoft_FStar_Util.print_string _86_55))
end)
end
| Microsoft_FStar_Getopt.OneArg (_20_155, argname) -> begin
(match ((doc = "")) with
| true -> begin
(let _86_57 = (Microsoft_FStar_Util.format2 "  --%s %s\n" flag argname)
in (Microsoft_FStar_Util.print_string _86_57))
end
| false -> begin
(let _86_58 = (Microsoft_FStar_Util.format3 "  --%s %s  %s\n" flag argname doc)
in (Microsoft_FStar_Util.print_string _86_58))
end)
end)
end)) specs)))

let rec specs = (fun _20_159 -> (match (()) with
| () -> begin
(let specs = ((Microsoft_FStar_Getopt.noshort, "trace_error", Microsoft_FStar_Getopt.ZeroArgs ((fun _20_160 -> (match (()) with
| () -> begin
(ST.op_Colon_Equals trace_error true)
end))), "Don\'t print an error message; show an exception trace instead"))::((Microsoft_FStar_Getopt.noshort, "codegen", Microsoft_FStar_Getopt.OneArg (((fun s -> (let _86_67 = (parse_codegen s)
in (ST.op_Colon_Equals codegen _86_67))), "OCaml|FSharp")), "Generate code for execution"))::((Microsoft_FStar_Getopt.noshort, "codegen-lib", Microsoft_FStar_Getopt.OneArg (((fun s -> (let _86_72 = (let _86_71 = (ST.read codegen_libs)
in ((Microsoft_FStar_Util.split s "."))::_86_71)
in (ST.op_Colon_Equals codegen_libs _86_72))), "namespace")), "External runtime library library"))::((Microsoft_FStar_Getopt.noshort, "lax", Microsoft_FStar_Getopt.ZeroArgs ((fun _20_163 -> (match (()) with
| () -> begin
(let _20_164 = (ST.op_Colon_Equals pretype true)
in (ST.op_Colon_Equals verify false))
end))), "Run the lax-type checker only (admit all verification conditions)"))::((Microsoft_FStar_Getopt.noshort, "fstar_home", Microsoft_FStar_Getopt.OneArg (((fun x -> (ST.op_Colon_Equals fstar_home_opt (Some (x)))), "dir")), "Set the FSTAR_HOME variable to dir"))::((Microsoft_FStar_Getopt.noshort, "silent", Microsoft_FStar_Getopt.ZeroArgs ((fun _20_167 -> (match (()) with
| () -> begin
(ST.op_Colon_Equals silent true)
end))), ""))::((Microsoft_FStar_Getopt.noshort, "prims", Microsoft_FStar_Getopt.OneArg (((fun x -> (ST.op_Colon_Equals prims_ref (Some (x)))), "file")), ""))::((Microsoft_FStar_Getopt.noshort, "prn", Microsoft_FStar_Getopt.ZeroArgs ((fun _20_169 -> (match (()) with
| () -> begin
(ST.op_Colon_Equals print_real_names true)
end))), "Print real names---you may want to use this in conjunction with logQueries"))::((Microsoft_FStar_Getopt.noshort, "debug", Microsoft_FStar_Getopt.OneArg (((fun x -> (let _86_86 = (let _86_85 = (ST.read debug)
in (x)::_86_85)
in (ST.op_Colon_Equals debug _86_86))), "module name")), "Print LOTS of debugging information while checking module [arg]"))::((Microsoft_FStar_Getopt.noshort, "debug_level", Microsoft_FStar_Getopt.OneArg (((fun x -> (let _86_91 = (let _86_90 = (ST.read debug_level)
in ((dlevel x))::_86_90)
in (ST.op_Colon_Equals debug_level _86_91))), "Low|Medium|High|Extreme")), "Control the verbosity of debugging info"))::((Microsoft_FStar_Getopt.noshort, "log_types", Microsoft_FStar_Getopt.ZeroArgs ((fun _20_172 -> (match (()) with
| () -> begin
(ST.op_Colon_Equals log_types true)
end))), "Print types computed for data/val/let-bindings"))::((Microsoft_FStar_Getopt.noshort, "print_effect_args", Microsoft_FStar_Getopt.ZeroArgs ((fun _20_173 -> (match (()) with
| () -> begin
(ST.op_Colon_Equals print_effect_args true)
end))), "Print inferred predicate transformers for all computation types"))::((Microsoft_FStar_Getopt.noshort, "dump_module", Microsoft_FStar_Getopt.OneArg (((fun x -> (ST.op_Colon_Equals dump_module (Some (x)))), "module name")), ""))::((Microsoft_FStar_Getopt.noshort, "z3timeout", Microsoft_FStar_Getopt.OneArg (((fun s -> (let _86_100 = (Microsoft_FStar_Util.int_of_string s)
in (ST.op_Colon_Equals z3timeout _86_100))), "t")), "Set the Z3 per-query (soft) timeout to t seconds (default 5)"))::((Microsoft_FStar_Getopt.noshort, "admit_smt_queries", Microsoft_FStar_Getopt.OneArg (((fun s -> (let _86_104 = (match ((s = "true")) with
| true -> begin
true
end
| false -> begin
(match ((s = "false")) with
| true -> begin
false
end
| false -> begin
(All.failwith "Invalid argument to --admit_smt_queries")
end)
end)
in (ST.op_Colon_Equals admit_smt_queries _86_104))), "true|false")), "Admit SMT queries (UNSAFE! But, useful during development); default: \'false\'"))::((Microsoft_FStar_Getopt.noshort, "logQueries", Microsoft_FStar_Getopt.ZeroArgs ((fun _20_177 -> (match (()) with
| () -> begin
(ST.op_Colon_Equals logQueries true)
end))), "Log the Z3 queries in queries.smt2"))::((Microsoft_FStar_Getopt.noshort, "admit_fsi", Microsoft_FStar_Getopt.OneArg (((fun x -> (let _86_110 = (let _86_109 = (ST.read admit_fsi)
in (x)::_86_109)
in (ST.op_Colon_Equals admit_fsi _86_110))), "module name")), "Treat .fsi as a .fst"))::((Microsoft_FStar_Getopt.noshort, "odir", Microsoft_FStar_Getopt.OneArg (((fun x -> (ST.op_Colon_Equals outputDir (Some (x)))), "dir")), "Place output in directory dir"))::((Microsoft_FStar_Getopt.noshort, "smt", Microsoft_FStar_Getopt.OneArg (((fun x -> (ST.op_Colon_Equals z3_exe x)), "path")), "Path to the SMT solver (usually Z3, but could be any SMT2-compatible solver)"))::((Microsoft_FStar_Getopt.noshort, "print_before_norm", Microsoft_FStar_Getopt.ZeroArgs ((fun _20_181 -> (match (()) with
| () -> begin
(ST.op_Colon_Equals norm_then_print false)
end))), "Do not normalize types before printing (for debugging)"))::((Microsoft_FStar_Getopt.noshort, "show_signatures", Microsoft_FStar_Getopt.OneArg (((fun x -> (let _86_122 = (let _86_121 = (ST.read show_signatures)
in (x)::_86_121)
in (ST.op_Colon_Equals show_signatures _86_122))), "module name")), "Show the checked signatures for all top-level symbols in the module"))::((Microsoft_FStar_Getopt.noshort, "full_context_dependency", Microsoft_FStar_Getopt.ZeroArgs ((fun _20_183 -> (match (()) with
| () -> begin
(ST.op_Colon_Equals full_context_dependency true)
end))), "Introduce unification variables that are dependent on the entire context (possibly expensive, but better for type inference (on, by default)"))::((Microsoft_FStar_Getopt.noshort, "MLish", Microsoft_FStar_Getopt.ZeroArgs ((fun _20_184 -> (match (()) with
| () -> begin
(ST.op_Colon_Equals full_context_dependency false)
end))), "Introduce unification variables that are only dependent on the type variables in the context"))::((Microsoft_FStar_Getopt.noshort, "print_implicits", Microsoft_FStar_Getopt.ZeroArgs ((fun _20_185 -> (match (()) with
| () -> begin
(ST.op_Colon_Equals print_implicits true)
end))), "Print implicit arguments"))::((Microsoft_FStar_Getopt.noshort, "hide_uvar_nums", Microsoft_FStar_Getopt.ZeroArgs ((fun _20_186 -> (match (()) with
| () -> begin
(ST.op_Colon_Equals hide_uvar_nums true)
end))), "Don\'t print unification variable numbers"))::((Microsoft_FStar_Getopt.noshort, "hide_genident_nums", Microsoft_FStar_Getopt.ZeroArgs ((fun _20_187 -> (match (()) with
| () -> begin
(ST.op_Colon_Equals hide_genident_nums true)
end))), "Don\'t print generated identifier numbers"))::((Microsoft_FStar_Getopt.noshort, "serialize_mods", Microsoft_FStar_Getopt.ZeroArgs ((fun _20_188 -> (match (()) with
| () -> begin
(ST.op_Colon_Equals serialize_mods true)
end))), "Serialize compiled modules"))::((Microsoft_FStar_Getopt.noshort, "initial_fuel", Microsoft_FStar_Getopt.OneArg (((fun x -> (let _86_132 = (Microsoft_FStar_Util.int_of_string x)
in (ST.op_Colon_Equals initial_fuel _86_132))), "non-negative integer")), "Number of unrolling of recursive functions to try initially (default 2)"))::((Microsoft_FStar_Getopt.noshort, "max_fuel", Microsoft_FStar_Getopt.OneArg (((fun x -> (let _86_136 = (Microsoft_FStar_Util.int_of_string x)
in (ST.op_Colon_Equals max_fuel _86_136))), "non-negative integer")), "Number of unrolling of recursive functions to try at most (default 8)"))::((Microsoft_FStar_Getopt.noshort, "min_fuel", Microsoft_FStar_Getopt.OneArg (((fun x -> (let _86_140 = (Microsoft_FStar_Util.int_of_string x)
in (ST.op_Colon_Equals min_fuel _86_140))), "non-negative integer")), "Minimum number of unrolling of recursive functions to try (default 1)"))::((Microsoft_FStar_Getopt.noshort, "initial_ifuel", Microsoft_FStar_Getopt.OneArg (((fun x -> (let _86_144 = (Microsoft_FStar_Util.int_of_string x)
in (ST.op_Colon_Equals initial_ifuel _86_144))), "non-negative integer")), "Number of unrolling of inductive datatypes to try at first (default 1)"))::((Microsoft_FStar_Getopt.noshort, "max_ifuel", Microsoft_FStar_Getopt.OneArg (((fun x -> (let _86_148 = (Microsoft_FStar_Util.int_of_string x)
in (ST.op_Colon_Equals max_ifuel _86_148))), "non-negative integer")), "Number of unrolling of inductive datatypes to try at most (default 1)"))::((Microsoft_FStar_Getopt.noshort, "warn_top_level_effects", Microsoft_FStar_Getopt.ZeroArgs ((fun _20_194 -> (match (()) with
| () -> begin
(ST.op_Colon_Equals warn_top_level_effects true)
end))), "Top-level effects are ignored, by default; turn this flag on to be warned when this happens"))::((Microsoft_FStar_Getopt.noshort, "no_slack", Microsoft_FStar_Getopt.ZeroArgs ((fun _20_195 -> (match (()) with
| () -> begin
(ST.op_Colon_Equals no_slack true)
end))), "Use the partially flow-insensitive variant of --rel2 (experimental)"))::((Microsoft_FStar_Getopt.noshort, "eager_inference", Microsoft_FStar_Getopt.ZeroArgs ((fun _20_196 -> (match (()) with
| () -> begin
(ST.op_Colon_Equals eager_inference true)
end))), "Solve all type-inference constraints eagerly; more efficient but at the cost of generality"))::((Microsoft_FStar_Getopt.noshort, "unthrottle_inductives", Microsoft_FStar_Getopt.ZeroArgs ((fun _20_197 -> (match (()) with
| () -> begin
(ST.op_Colon_Equals unthrottle_inductives true)
end))), "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)"))::((Microsoft_FStar_Getopt.noshort, "use_eq_at_higher_order", Microsoft_FStar_Getopt.ZeroArgs ((fun _20_198 -> (match (()) with
| () -> begin
(ST.op_Colon_Equals use_eq_at_higher_order true)
end))), "Use equality constraints when comparing higher-order types; temporary"))::((Microsoft_FStar_Getopt.noshort, "fs_typ_app", Microsoft_FStar_Getopt.ZeroArgs ((fun _20_199 -> (match (()) with
| () -> begin
(ST.op_Colon_Equals fs_typ_app true)
end))), "Allow the use of t<t1,...,tn> syntax for type applications; brittle since it clashes with the integer less-than operator"))::((Microsoft_FStar_Getopt.noshort, "no_fs_typ_app", Microsoft_FStar_Getopt.ZeroArgs ((fun _20_200 -> (match (()) with
| () -> begin
(ST.op_Colon_Equals fs_typ_app false)
end))), "Do not allow the use of t<t1,...,tn> syntax for type applications"))::((Microsoft_FStar_Getopt.noshort, "n_cores", Microsoft_FStar_Getopt.OneArg (((fun x -> (let _86_159 = (Microsoft_FStar_Util.int_of_string x)
in (ST.op_Colon_Equals n_cores _86_159))), "positive integer")), "Maximum number of cores to use for the solver (default 1)"))::((Microsoft_FStar_Getopt.noshort, "verify_module", Microsoft_FStar_Getopt.OneArg (((fun x -> (let _86_164 = (let _86_163 = (ST.read verify_module)
in (x)::_86_163)
in (ST.op_Colon_Equals verify_module _86_164))), "string")), "Name of the module to verify"))::((Microsoft_FStar_Getopt.noshort, "use_build_config", Microsoft_FStar_Getopt.ZeroArgs ((fun _20_203 -> (match (()) with
| () -> begin
(ST.op_Colon_Equals use_build_config true)
end))), "Expect just a single file on the command line and no options; will read the \'build-config\' prelude from the file"))::((Microsoft_FStar_Getopt.noshort, "split_cases", Microsoft_FStar_Getopt.OneArg (((fun n -> (let _86_169 = (Microsoft_FStar_Util.int_of_string n)
in (ST.op_Colon_Equals split_cases _86_169))), "t")), "Partition VC of a match into groups of n cases"))::((Microsoft_FStar_Getopt.noshort, "in", Microsoft_FStar_Getopt.ZeroArgs ((fun _20_205 -> (match (()) with
| () -> begin
(ST.op_Colon_Equals interactive true)
end))), "Interactive mode; reads input from stdin"))::((Microsoft_FStar_Getopt.noshort, "include", Microsoft_FStar_Getopt.OneArg (((fun s -> (let _86_175 = (let _86_174 = (ST.read _include_path)
in (Microsoft_FStar_List.append _86_174 ((s)::[])))
in (ST.op_Colon_Equals _include_path _86_175))), "path")), "A directory in which to search for files included on the command line"))::((Microsoft_FStar_Getopt.noshort, "fsi", Microsoft_FStar_Getopt.ZeroArgs ((fun _20_207 -> (match (()) with
| () -> begin
(set_interactive_fsi ())
end))), "fsi flag; A flag to indicate if type checking a fsi in the interactive mode"))::((Microsoft_FStar_Getopt.noshort, "print_fuels", Microsoft_FStar_Getopt.ZeroArgs ((fun _20_208 -> (match (()) with
| () -> begin
(ST.op_Colon_Equals print_fuels true)
end))), "Print the fuel amounts used for each successful query"))::((Microsoft_FStar_Getopt.noshort, "__temp_no_proj", Microsoft_FStar_Getopt.ZeroArgs ((fun _20_209 -> (match (()) with
| () -> begin
(ST.op_Colon_Equals __temp_no_proj true)
end))), "A temporary flag to disable code generation for projectors"))::[]
in (('h', "help", Microsoft_FStar_Getopt.ZeroArgs ((fun x -> (let _20_212 = (display_usage specs)
in (All.exit 0)))), "Display this information"))::specs)
end))
and parse_codegen = (fun s -> (match (s) with
| ("OCaml-experimental") | ("OCaml") | ("FSharp") -> begin
Some (s)
end
| _20_219 -> begin
(let _20_220 = (Microsoft_FStar_Util.print_string "Wrong argument to codegen flag\n")
in (let _20_222 = (let _86_181 = (specs ())
in (display_usage _86_181))
in (All.exit 1)))
end))
and set_interactive_fsi = (fun _20_224 -> (match ((ST.read interactive)) with
| true -> begin
(ST.op_Colon_Equals interactive_fsi true)
end
| false -> begin
(let _20_226 = (Microsoft_FStar_Util.print_string "Set interactive flag first before setting interactive fsi flag\n")
in (let _20_228 = (let _86_183 = (specs ())
in (display_usage _86_183))
in (All.exit 1)))
end))

let should_verify = (fun m -> ((ST.read verify) && (match ((ST.read verify_module)) with
| [] -> begin
true
end
| l -> begin
(Microsoft_FStar_List.contains m l)
end)))

let set_options = (fun s -> (let _86_189 = (specs ())
in (Microsoft_FStar_Getopt.parse_string _86_189 (fun _20_234 -> ()) s)))

let reset_options_string = (ST.alloc None)

let reset_options = (fun _20_236 -> (match (()) with
| () -> begin
(let _20_237 = (init_options ())
in (match ((ST.read reset_options_string)) with
| Some (x) -> begin
(set_options x)
end
| _20_242 -> begin
(let _86_193 = (specs ())
in (Microsoft_FStar_Getopt.parse_cmdline _86_193 (fun x -> ())))
end))
end))




