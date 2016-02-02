
open Prims
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
| Other (_19_4) -> begin
_19_4
end))

let show_signatures = (FStar_Util.mk_ref [])

let norm_then_print = (FStar_Util.mk_ref true)

let z3_exe = (let _72_19 = (FStar_Platform.exe "z3")
in (FStar_Util.mk_ref _72_19))

let silent = (FStar_Util.mk_ref false)

let debug = (FStar_Util.mk_ref [])

let debug_level = (FStar_Util.mk_ref [])

let dlevel = (fun _19_1 -> (match (_19_1) with
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

let debug_level_geq = (fun l2 -> (let _72_29 = (FStar_ST.read debug_level)
in (FStar_All.pipe_right _72_29 (FStar_Util.for_some (fun l1 -> (one_debug_level_geq l1 l2))))))

let log_types = (FStar_Util.mk_ref false)

let print_effect_args = (FStar_Util.mk_ref false)

let print_real_names = (FStar_Util.mk_ref false)

let dump_module = (FStar_Util.mk_ref None)

let should_dump = (fun l -> (match ((FStar_ST.read dump_module)) with
| None -> begin
false
end
| Some (m) -> begin
(m = l)
end))

let logQueries = (FStar_Util.mk_ref false)

let z3exe = (FStar_Util.mk_ref true)

let outputDir = (FStar_Util.mk_ref (Some (".")))

let fstar_home_opt = (FStar_Util.mk_ref None)

let _fstar_home = (FStar_Util.mk_ref "")

let prims_ref = (FStar_Util.mk_ref None)

let z3timeout = (FStar_Util.mk_ref 5)

let admit_smt_queries = (FStar_Util.mk_ref false)

let pretype = (FStar_Util.mk_ref true)

let codegen = (FStar_Util.mk_ref None)

let admit_fsi = (FStar_Util.mk_ref [])

let codegen_libs = (FStar_Util.mk_ref [])

let trace_error = (FStar_Util.mk_ref false)

let verify = (FStar_Util.mk_ref true)

let full_context_dependency = (FStar_Util.mk_ref true)

let print_implicits = (FStar_Util.mk_ref false)

let print_bound_var_types = (FStar_Util.mk_ref false)

let print_universes = (FStar_Util.mk_ref false)

let hide_uvar_nums = (FStar_Util.mk_ref false)

let hide_genident_nums = (FStar_Util.mk_ref false)

let serialize_mods = (FStar_Util.mk_ref false)

let initial_fuel = (FStar_Util.mk_ref 2)

let initial_ifuel = (FStar_Util.mk_ref 1)

let max_fuel = (FStar_Util.mk_ref 8)

let min_fuel = (FStar_Util.mk_ref 1)

let max_ifuel = (FStar_Util.mk_ref 2)

let warn_top_level_effects = (FStar_Util.mk_ref false)

let no_slack = (FStar_Util.mk_ref false)

let eager_inference = (FStar_Util.mk_ref false)

let universes = (FStar_Util.mk_ref false)

let unthrottle_inductives = (FStar_Util.mk_ref false)

let use_eq_at_higher_order = (FStar_Util.mk_ref false)

let use_native_int = (FStar_Util.mk_ref false)

let fs_typ_app = (FStar_Util.mk_ref false)

let n_cores = (FStar_Util.mk_ref 1)

let verify_module = (FStar_Util.mk_ref [])

let __temp_no_proj = (FStar_Util.mk_ref [])

let use_build_config = (FStar_Util.mk_ref false)

let interactive = (FStar_Util.mk_ref false)

let interactive_context = (FStar_Util.mk_ref None)

let split_cases = (FStar_Util.mk_ref 0)

let _include_path = (FStar_Util.mk_ref [])

let interactive_fsi = (FStar_Util.mk_ref false)

let print_fuels = (FStar_Util.mk_ref false)

let cardinality = (FStar_Util.mk_ref "off")

let timing = (FStar_Util.mk_ref false)

let warn_cardinality = (fun _19_26 -> (match (()) with
| () -> begin
(match ((FStar_ST.read cardinality)) with
| "warn" -> begin
true
end
| _19_29 -> begin
false
end)
end))

let check_cardinality = (fun _19_30 -> (match (()) with
| () -> begin
(match ((FStar_ST.read cardinality)) with
| "check" -> begin
true
end
| _19_33 -> begin
false
end)
end))

let dep = (FStar_ST.alloc None)

let auto_deps = (FStar_Util.mk_ref false)

let find_deps = (FStar_Util.mk_ref false)

let init_options = (fun _19_34 -> (match (()) with
| () -> begin
(let _19_35 = (FStar_ST.op_Colon_Equals show_signatures [])
in (let _19_37 = (FStar_ST.op_Colon_Equals norm_then_print true)
in (let _19_39 = (let _72_38 = (FStar_Platform.exe "z3")
in (FStar_ST.op_Colon_Equals z3_exe _72_38))
in (let _19_41 = (FStar_ST.op_Colon_Equals silent false)
in (let _19_43 = (FStar_ST.op_Colon_Equals debug [])
in (let _19_45 = (FStar_ST.op_Colon_Equals debug_level [])
in (let _19_47 = (FStar_ST.op_Colon_Equals log_types false)
in (let _19_49 = (FStar_ST.op_Colon_Equals print_effect_args false)
in (let _19_51 = (FStar_ST.op_Colon_Equals print_real_names false)
in (let _19_53 = (FStar_ST.op_Colon_Equals dump_module None)
in (let _19_55 = (FStar_ST.op_Colon_Equals logQueries false)
in (let _19_57 = (FStar_ST.op_Colon_Equals z3exe true)
in (let _19_59 = (FStar_ST.op_Colon_Equals outputDir (Some (".")))
in (let _19_61 = (FStar_ST.op_Colon_Equals fstar_home_opt None)
in (let _19_63 = (FStar_ST.op_Colon_Equals _fstar_home "")
in (let _19_65 = (FStar_ST.op_Colon_Equals prims_ref None)
in (let _19_67 = (FStar_ST.op_Colon_Equals z3timeout 5)
in (let _19_69 = (FStar_ST.op_Colon_Equals admit_smt_queries false)
in (let _19_71 = (FStar_ST.op_Colon_Equals pretype true)
in (let _19_73 = (FStar_ST.op_Colon_Equals codegen None)
in (let _19_75 = (FStar_ST.op_Colon_Equals codegen_libs [])
in (let _19_77 = (FStar_ST.op_Colon_Equals admit_fsi [])
in (let _19_79 = (FStar_ST.op_Colon_Equals trace_error false)
in (let _19_81 = (FStar_ST.op_Colon_Equals verify true)
in (let _19_83 = (FStar_ST.op_Colon_Equals full_context_dependency true)
in (let _19_85 = (FStar_ST.op_Colon_Equals print_implicits false)
in (let _19_87 = (FStar_ST.op_Colon_Equals print_bound_var_types false)
in (let _19_89 = (FStar_ST.op_Colon_Equals print_universes false)
in (let _19_91 = (FStar_ST.op_Colon_Equals hide_uvar_nums false)
in (let _19_93 = (FStar_ST.op_Colon_Equals hide_genident_nums false)
in (let _19_95 = (FStar_ST.op_Colon_Equals serialize_mods false)
in (let _19_97 = (FStar_ST.op_Colon_Equals initial_fuel 2)
in (let _19_99 = (FStar_ST.op_Colon_Equals initial_ifuel 1)
in (let _19_101 = (FStar_ST.op_Colon_Equals max_fuel 8)
in (let _19_103 = (FStar_ST.op_Colon_Equals min_fuel 1)
in (let _19_105 = (FStar_ST.op_Colon_Equals max_ifuel 2)
in (let _19_107 = (FStar_ST.op_Colon_Equals warn_top_level_effects false)
in (let _19_109 = (FStar_ST.op_Colon_Equals no_slack false)
in (let _19_111 = (FStar_ST.op_Colon_Equals eager_inference false)
in (let _19_113 = (FStar_ST.op_Colon_Equals unthrottle_inductives false)
in (let _19_115 = (FStar_ST.op_Colon_Equals use_eq_at_higher_order false)
in (let _19_117 = (FStar_ST.op_Colon_Equals fs_typ_app false)
in (let _19_119 = (FStar_ST.op_Colon_Equals n_cores 1)
in (let _19_121 = (FStar_ST.op_Colon_Equals split_cases 0)
in (let _19_123 = (FStar_ST.op_Colon_Equals verify_module [])
in (let _19_125 = (FStar_ST.op_Colon_Equals __temp_no_proj [])
in (let _19_127 = (FStar_ST.op_Colon_Equals _include_path [])
in (let _19_129 = (FStar_ST.op_Colon_Equals print_fuels false)
in (let _19_131 = (FStar_ST.op_Colon_Equals use_native_int false)
in (let _19_133 = (FStar_ST.op_Colon_Equals auto_deps false)
in (let _19_135 = (FStar_ST.op_Colon_Equals find_deps false)
in (let _19_137 = (FStar_ST.op_Colon_Equals dep None)
in (FStar_ST.op_Colon_Equals timing false)))))))))))))))))))))))))))))))))))))))))))))))))))))
end))

let set_fstar_home = (fun _19_139 -> (match (()) with
| () -> begin
(let fh = (match ((FStar_ST.read fstar_home_opt)) with
| None -> begin
(let x = (FStar_Util.get_exec_dir ())
in (let x = (Prims.strcat x "/..")
in (let _19_143 = (FStar_ST.op_Colon_Equals _fstar_home x)
in (let _19_145 = (FStar_ST.op_Colon_Equals fstar_home_opt (Some (x)))
in x))))
end
| Some (x) -> begin
(let _19_149 = (FStar_ST.op_Colon_Equals _fstar_home x)
in x)
end)
in fh)
end))

let get_fstar_home = (fun _19_152 -> (match (()) with
| () -> begin
(match ((FStar_ST.read fstar_home_opt)) with
| None -> begin
(let _19_154 = (let _72_43 = (set_fstar_home ())
in (FStar_All.pipe_left Prims.ignore _72_43))
in (FStar_ST.read _fstar_home))
end
| Some (x) -> begin
x
end)
end))

let get_include_path = (fun dirname -> (let _72_48 = (let h = (get_fstar_home ())
in (let _72_47 = (FStar_ST.read _include_path)
in (FStar_List.append _72_47 ((".")::((Prims.strcat h "/lib"))::((Prims.strcat h "/lib/fstar"))::[]))))
in (FStar_List.map (fun p -> if (FStar_Util.is_path_absolute p) then begin
(FStar_Util.normalize_file_path p)
end else begin
(FStar_Util.join_paths dirname p)
end) _72_48)))

let prims = (fun _19_161 -> (match (()) with
| () -> begin
(match ((FStar_ST.read prims_ref)) with
| None -> begin
(let filen = "prims.fst"
in (match ((let _72_51 = (get_include_path ".")
in (FStar_Util.find_file filen _72_51))) with
| Some (result) -> begin
result
end
| None -> begin
filen
end))
end
| Some (x) -> begin
x
end)
end))

let prependOutputDir = (fun fname -> (match ((FStar_ST.read outputDir)) with
| None -> begin
fname
end
| Some (x) -> begin
(Prims.strcat (Prims.strcat x "/") fname)
end))

let cache_dir = "cache"

let display_version = (fun _19_173 -> (match (()) with
| () -> begin
(let _72_56 = (FStar_Util.format5 "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" FStar_Version.version FStar_Version.platform FStar_Version.compiler FStar_Version.date FStar_Version.commit)
in (FStar_Util.print_string _72_56))
end))

let display_usage = (fun specs -> (let _19_175 = (FStar_Util.print_string "fstar [option] infile...")
in (FStar_List.iter (fun _19_182 -> (match (_19_182) with
| (_19_178, flag, p, doc) -> begin
(match (p) with
| FStar_Getopt.ZeroArgs (ig) -> begin
if (doc = "") then begin
(let _72_60 = (FStar_Util.format1 "  --%s\n" flag)
in (FStar_Util.print_string _72_60))
end else begin
(let _72_61 = (FStar_Util.format2 "  --%s  %s\n" flag doc)
in (FStar_Util.print_string _72_61))
end
end
| FStar_Getopt.OneArg (_19_186, argname) -> begin
if (doc = "") then begin
(let _72_63 = (FStar_Util.format2 "  --%s %s\n" flag argname)
in (FStar_Util.print_string _72_63))
end else begin
(let _72_64 = (FStar_Util.format3 "  --%s %s  %s\n" flag argname doc)
in (FStar_Util.print_string _72_64))
end
end)
end)) specs)))

let rec specs = (fun _19_190 -> (match (()) with
| () -> begin
(let specs = ((FStar_Getopt.noshort, "admit_fsi", FStar_Getopt.OneArg (((fun x -> (let _72_74 = (let _72_73 = (FStar_ST.read admit_fsi)
in (x)::_72_73)
in (FStar_ST.op_Colon_Equals admit_fsi _72_74))), "module name")), "Treat .fsi as a .fst"))::((FStar_Getopt.noshort, "auto_deps", FStar_Getopt.ZeroArgs ((fun _19_192 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals auto_deps true)
end))), "automatically treat files discovered by --find_deps as dependencies."))::((FStar_Getopt.noshort, "admit_smt_queries", FStar_Getopt.OneArg (((fun s -> (let _72_79 = if (s = "true") then begin
true
end else begin
if (s = "false") then begin
false
end else begin
(FStar_All.failwith "Invalid argument to --admit_smt_queries")
end
end
in (FStar_ST.op_Colon_Equals admit_smt_queries _72_79))), "true|false")), "Admit SMT queries (UNSAFE! But, useful during development); default: \'false\'"))::((FStar_Getopt.noshort, "auto_deps", FStar_Getopt.ZeroArgs ((fun _19_194 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals auto_deps true)
end))), "automatically treat files discovered by --find_deps as dependencies."))::((FStar_Getopt.noshort, "codegen", FStar_Getopt.OneArg (((fun s -> (let _72_84 = (parse_codegen s)
in (FStar_ST.op_Colon_Equals codegen _72_84))), "OCaml|FSharp")), "Generate code for execution"))::((FStar_Getopt.noshort, "codegen-lib", FStar_Getopt.OneArg (((fun s -> (let _72_89 = (let _72_88 = (FStar_ST.read codegen_libs)
in ((FStar_Util.split s "."))::_72_88)
in (FStar_ST.op_Colon_Equals codegen_libs _72_89))), "namespace")), "External runtime library library"))::((FStar_Getopt.noshort, "debug", FStar_Getopt.OneArg (((fun x -> (let _72_94 = (let _72_93 = (FStar_ST.read debug)
in (x)::_72_93)
in (FStar_ST.op_Colon_Equals debug _72_94))), "module name")), "Print LOTS of debugging information while checking module [arg]"))::((FStar_Getopt.noshort, "debug_level", FStar_Getopt.OneArg (((fun x -> (let _72_99 = (let _72_98 = (FStar_ST.read debug_level)
in ((dlevel x))::_72_98)
in (FStar_ST.op_Colon_Equals debug_level _72_99))), "Low|Medium|High|Extreme")), "Control the verbosity of debugging info"))::((FStar_Getopt.noshort, "dep", FStar_Getopt.OneArg (((fun x -> (FStar_ST.op_Colon_Equals dep (Some (x)))), "make|nubuild")), "Output the transitive closure of the dependency graph in a format suitable for the given tool"))::((FStar_Getopt.noshort, "dump_module", FStar_Getopt.OneArg (((fun x -> (FStar_ST.op_Colon_Equals dump_module (Some (x)))), "module name")), ""))::((FStar_Getopt.noshort, "eager_inference", FStar_Getopt.ZeroArgs ((fun _19_201 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals eager_inference true)
end))), "Solve all type-inference constraints eagerly; more efficient but at the cost of generality"))::((FStar_Getopt.noshort, "find_deps", FStar_Getopt.ZeroArgs ((fun _19_202 -> (match (()) with
| () -> begin
(let _19_203 = (FStar_ST.op_Colon_Equals find_deps true)
in (FStar_ST.op_Colon_Equals auto_deps true))
end))), "find transitive dependencies given build-config other-files specifications."))::((FStar_Getopt.noshort, "fs_typ_app", FStar_Getopt.ZeroArgs ((fun _19_205 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals fs_typ_app true)
end))), "Allow the use of t<t1,...,tn> syntax for type applications; brittle since it clashes with the integer less-than operator"))::((FStar_Getopt.noshort, "fsi", FStar_Getopt.ZeroArgs ((fun _19_206 -> (match (()) with
| () -> begin
(set_interactive_fsi ())
end))), "fsi flag; A flag to indicate if type checking a fsi in the interactive mode"))::((FStar_Getopt.noshort, "fstar_home", FStar_Getopt.OneArg (((fun x -> (FStar_ST.op_Colon_Equals fstar_home_opt (Some (x)))), "dir")), "Set the FSTAR_HOME variable to dir"))::((FStar_Getopt.noshort, "hide_genident_nums", FStar_Getopt.ZeroArgs ((fun _19_208 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals hide_genident_nums true)
end))), "Don\'t print generated identifier numbers"))::((FStar_Getopt.noshort, "hide_uvar_nums", FStar_Getopt.ZeroArgs ((fun _19_209 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals hide_uvar_nums true)
end))), "Don\'t print unification variable numbers"))::((FStar_Getopt.noshort, "in", FStar_Getopt.ZeroArgs ((fun _19_210 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals interactive true)
end))), "Interactive mode; reads input from stdin"))::((FStar_Getopt.noshort, "in_context", FStar_Getopt.OneArg (((fun s -> (let _19_212 = (FStar_ST.op_Colon_Equals interactive true)
in (FStar_ST.op_Colon_Equals interactive_context (Some (s))))), "name")), "Specify the context of an interactive session; needed for --auto_deps to work with interactive mode."))::((FStar_Getopt.noshort, "include", FStar_Getopt.OneArg (((fun s -> (let _72_123 = (let _72_122 = (FStar_ST.read _include_path)
in (FStar_List.append _72_122 ((s)::[])))
in (FStar_ST.op_Colon_Equals _include_path _72_123))), "path")), "A directory in which to search for files included on the command line"))::((FStar_Getopt.noshort, "initial_fuel", FStar_Getopt.OneArg (((fun x -> (let _72_127 = (FStar_Util.int_of_string x)
in (FStar_ST.op_Colon_Equals initial_fuel _72_127))), "non-negative integer")), "Number of unrolling of recursive functions to try initially (default 2)"))::((FStar_Getopt.noshort, "initial_ifuel", FStar_Getopt.OneArg (((fun x -> (let _72_131 = (FStar_Util.int_of_string x)
in (FStar_ST.op_Colon_Equals initial_ifuel _72_131))), "non-negative integer")), "Number of unrolling of inductive datatypes to try at first (default 1)"))::((FStar_Getopt.noshort, "lax", FStar_Getopt.ZeroArgs ((fun _19_217 -> (match (()) with
| () -> begin
(let _19_218 = (FStar_ST.op_Colon_Equals pretype true)
in (FStar_ST.op_Colon_Equals verify false))
end))), "Run the lax-type checker only (admit all verification conditions)"))::((FStar_Getopt.noshort, "log_types", FStar_Getopt.ZeroArgs ((fun _19_220 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals log_types true)
end))), "Print types computed for data/val/let-bindings"))::((FStar_Getopt.noshort, "log_queries", FStar_Getopt.ZeroArgs ((fun _19_221 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals logQueries true)
end))), "Log the Z3 queries in queries.smt2"))::((FStar_Getopt.noshort, "max_fuel", FStar_Getopt.OneArg (((fun x -> (let _72_138 = (FStar_Util.int_of_string x)
in (FStar_ST.op_Colon_Equals max_fuel _72_138))), "non-negative integer")), "Number of unrolling of recursive functions to try at most (default 8)"))::((FStar_Getopt.noshort, "max_ifuel", FStar_Getopt.OneArg (((fun x -> (let _72_142 = (FStar_Util.int_of_string x)
in (FStar_ST.op_Colon_Equals max_ifuel _72_142))), "non-negative integer")), "Number of unrolling of inductive datatypes to try at most (default 2)"))::((FStar_Getopt.noshort, "min_fuel", FStar_Getopt.OneArg (((fun x -> (let _72_146 = (FStar_Util.int_of_string x)
in (FStar_ST.op_Colon_Equals min_fuel _72_146))), "non-negative integer")), "Minimum number of unrolling of recursive functions to try (default 1)"))::((FStar_Getopt.noshort, "MLish", FStar_Getopt.ZeroArgs ((fun _19_225 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals full_context_dependency false)
end))), "Introduce unification variables that are only dependent on the type variables in the context"))::((FStar_Getopt.noshort, "n_cores", FStar_Getopt.OneArg (((fun x -> (let _72_151 = (FStar_Util.int_of_string x)
in (FStar_ST.op_Colon_Equals n_cores _72_151))), "positive integer")), "Maximum number of cores to use for the solver (default 1)"))::((FStar_Getopt.noshort, "no_fs_typ_app", FStar_Getopt.ZeroArgs ((fun _19_227 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals fs_typ_app false)
end))), "Do not allow the use of t<t1,...,tn> syntax for type applications"))::((FStar_Getopt.noshort, "odir", FStar_Getopt.OneArg (((fun x -> (FStar_ST.op_Colon_Equals outputDir (Some (x)))), "dir")), "Place output in directory dir"))::((FStar_Getopt.noshort, "prims", FStar_Getopt.OneArg (((fun x -> (FStar_ST.op_Colon_Equals prims_ref (Some (x)))), "file")), ""))::((FStar_Getopt.noshort, "print_before_norm", FStar_Getopt.ZeroArgs ((fun _19_230 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals norm_then_print false)
end))), "Do not normalize types before printing (for debugging)"))::((FStar_Getopt.noshort, "print_bound_var_types", FStar_Getopt.ZeroArgs ((fun _19_231 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals print_bound_var_types true)
end))), "Print the types of bound variables"))::((FStar_Getopt.noshort, "print_effect_args", FStar_Getopt.ZeroArgs ((fun _19_232 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals print_effect_args true)
end))), "Print inferred predicate transformers for all computation types"))::((FStar_Getopt.noshort, "print_fuels", FStar_Getopt.ZeroArgs ((fun _19_233 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals print_fuels true)
end))), "Print the fuel amounts used for each successful query"))::((FStar_Getopt.noshort, "print_implicits", FStar_Getopt.ZeroArgs ((fun _19_234 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals print_implicits true)
end))), "Print implicit arguments"))::((FStar_Getopt.noshort, "print_universes", FStar_Getopt.ZeroArgs ((fun _19_235 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals print_universes true)
end))), "Print universes"))::((FStar_Getopt.noshort, "prn", FStar_Getopt.ZeroArgs ((fun _19_236 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals print_real_names true)
end))), "Print real names---you may want to use this in conjunction with log_queries"))::((FStar_Getopt.noshort, "show_signatures", FStar_Getopt.OneArg (((fun x -> (let _72_170 = (let _72_169 = (FStar_ST.read show_signatures)
in (x)::_72_169)
in (FStar_ST.op_Colon_Equals show_signatures _72_170))), "module name")), "Show the checked signatures for all top-level symbols in the module"))::((FStar_Getopt.noshort, "silent", FStar_Getopt.ZeroArgs ((fun _19_238 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals silent true)
end))), ""))::((FStar_Getopt.noshort, "smt", FStar_Getopt.OneArg (((fun x -> (FStar_ST.op_Colon_Equals z3_exe x)), "path")), "Path to the SMT solver (usually Z3, but could be any SMT2-compatible solver)"))::((FStar_Getopt.noshort, "split_cases", FStar_Getopt.OneArg (((fun n -> (let _72_178 = (FStar_Util.int_of_string n)
in (FStar_ST.op_Colon_Equals split_cases _72_178))), "t")), "Partition VC of a match into groups of n cases"))::((FStar_Getopt.noshort, "timing", FStar_Getopt.ZeroArgs ((fun _19_241 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals timing true)
end))), "Print the time it takes to verify each top-level definition"))::((FStar_Getopt.noshort, "trace_error", FStar_Getopt.ZeroArgs ((fun _19_242 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals trace_error true)
end))), "Don\'t print an error message; show an exception trace instead"))::((FStar_Getopt.noshort, "universes", FStar_Getopt.ZeroArgs ((fun _19_243 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals universes true)
end))), "Use the (experimental) support for universes"))::((FStar_Getopt.noshort, "use_build_config", FStar_Getopt.ZeroArgs ((fun _19_244 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals use_build_config true)
end))), "Expect just a single file on the command line and no options; will read the \'build-config\' prelude from the file"))::((FStar_Getopt.noshort, "use_native_int", FStar_Getopt.ZeroArgs ((fun _19_245 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals use_native_int true)
end))), "Extract the \'int\' type to platform-specific native int; you will need to link the generated code with the appropriate version of the prims library"))::((FStar_Getopt.noshort, "verify_module", FStar_Getopt.OneArg (((fun x -> (let _72_188 = (let _72_187 = (FStar_ST.read verify_module)
in (x)::_72_187)
in (FStar_ST.op_Colon_Equals verify_module _72_188))), "string")), "Name of the module to verify"))::((FStar_Getopt.noshort, "__temp_no_proj", FStar_Getopt.OneArg (((fun x -> (let _72_193 = (let _72_192 = (FStar_ST.read __temp_no_proj)
in (x)::_72_192)
in (FStar_ST.op_Colon_Equals __temp_no_proj _72_193))), "string")), "Don\'t generate projectors for this module"))::(('v', "version", FStar_Getopt.ZeroArgs ((fun _19_248 -> (let _19_250 = (display_version ())
in (FStar_All.exit 0)))), "Display version number"))::((FStar_Getopt.noshort, "warn_top_level_effects", FStar_Getopt.ZeroArgs ((fun _19_252 -> (match (()) with
| () -> begin
(FStar_ST.op_Colon_Equals warn_top_level_effects true)
end))), "Top-level effects are ignored, by default; turn this flag on to be warned when this happens"))::((FStar_Getopt.noshort, "z3timeout", FStar_Getopt.OneArg (((fun s -> (let _72_199 = (FStar_Util.int_of_string s)
in (FStar_ST.op_Colon_Equals z3timeout _72_199))), "t")), "Set the Z3 per-query (soft) timeout to t seconds (default 5)"))::[]
in (('h', "help", FStar_Getopt.ZeroArgs ((fun x -> (let _19_256 = (display_usage specs)
in (FStar_All.exit 0)))), "Display this information"))::specs)
end))
and parse_codegen = (fun s -> (match (s) with
| ("OCaml") | ("FSharp") -> begin
Some (s)
end
| _19_262 -> begin
(let _19_263 = (FStar_Util.print_string "Wrong argument to codegen flag\n")
in (let _19_265 = (let _72_202 = (specs ())
in (display_usage _72_202))
in (FStar_All.exit 1)))
end))
and validate_cardinality = (fun x -> (match (x) with
| ("warn") | ("check") | ("off") -> begin
x
end
| _19_272 -> begin
(let _19_273 = (FStar_Util.print_string "Wrong argument to cardinality flag\n")
in (let _19_275 = (let _72_204 = (specs ())
in (display_usage _72_204))
in (FStar_All.exit 1)))
end))
and set_interactive_fsi = (fun _19_277 -> if (FStar_ST.read interactive) then begin
(FStar_ST.op_Colon_Equals interactive_fsi true)
end else begin
(let _19_279 = (FStar_Util.print_string "Set interactive flag first before setting interactive fsi flag\n")
in (let _19_281 = (let _72_206 = (specs ())
in (display_usage _72_206))
in (FStar_All.exit 1)))
end)

let should_verify = (fun m -> ((FStar_ST.read verify) && (match ((FStar_ST.read verify_module)) with
| [] -> begin
true
end
| l -> begin
(FStar_List.contains m l)
end)))

let dont_gen_projectors = (fun m -> (let _72_211 = (FStar_ST.read __temp_no_proj)
in (FStar_List.contains m _72_211)))

let should_print_message = (fun m -> (((should_verify m) && (not ((let _72_214 = (FStar_ST.read admit_fsi)
in (FStar_List.contains m _72_214))))) && (m <> "Prims")))

let set_options = (let no_smt_specs = (let _72_217 = (specs ())
in (FStar_All.pipe_right _72_217 (FStar_List.filter (fun _19_295 -> (match (_19_295) with
| (_19_289, name, _19_292, _19_294) -> begin
(name <> "smt")
end)))))
in (fun s -> (FStar_Getopt.parse_string no_smt_specs (fun _19_298 -> ()) s)))

let reset_options_string = (FStar_ST.alloc None)

let reset_options = (fun _19_300 -> (match (()) with
| () -> begin
(let _19_301 = (init_options ())
in (let res = (let _72_223 = (specs ())
in (FStar_Getopt.parse_cmdline _72_223 (fun x -> ())))
in (match ((FStar_ST.read reset_options_string)) with
| Some (x) -> begin
(set_options x)
end
| _19_308 -> begin
res
end)))
end))




