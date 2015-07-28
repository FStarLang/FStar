
type debug_level_t =
| Low
| Medium
| High
| Extreme
| Other of string

let is_Low = (fun ( _discr_ ) -> (match (_discr_) with
| Low (_) -> begin
true
end
| _ -> begin
false
end))

let is_Medium = (fun ( _discr_ ) -> (match (_discr_) with
| Medium (_) -> begin
true
end
| _ -> begin
false
end))

let is_High = (fun ( _discr_ ) -> (match (_discr_) with
| High (_) -> begin
true
end
| _ -> begin
false
end))

let is_Extreme = (fun ( _discr_ ) -> (match (_discr_) with
| Extreme (_) -> begin
true
end
| _ -> begin
false
end))

let is_Other = (fun ( _discr_ ) -> (match (_discr_) with
| Other (_) -> begin
true
end
| _ -> begin
false
end))

let show_signatures = (Support.Microsoft.FStar.Util.mk_ref [])

let norm_then_print = (Support.Microsoft.FStar.Util.mk_ref true)

let z3_exe = (let _13_2176 = (Support.Microsoft.FStar.Platform.exe "z3")
in (Support.Microsoft.FStar.Util.mk_ref _13_2176))

let silent = (Support.Microsoft.FStar.Util.mk_ref false)

let debug = (Support.Microsoft.FStar.Util.mk_ref [])

let debug_level = (Support.Microsoft.FStar.Util.mk_ref [])

let dlevel = (fun ( _11_1  :  string ) -> (match (_11_1) with
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

let one_debug_level_geq = (fun ( l1  :  debug_level_t ) ( l2  :  debug_level_t ) -> (match (l1) with
| (Low) -> begin
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

let debug_level_geq = (fun ( l2  :  debug_level_t ) -> (let _13_2186 = (Support.Prims.op_Bang debug_level)
in (Support.Prims.pipe_right _13_2186 (Support.Microsoft.FStar.Util.for_some (fun ( l1  :  debug_level_t ) -> (one_debug_level_geq l1 l2))))))

let log_types = (Support.Microsoft.FStar.Util.mk_ref false)

let print_effect_args = (Support.Microsoft.FStar.Util.mk_ref false)

let print_real_names = (Support.Microsoft.FStar.Util.mk_ref false)

let dump_module = (Support.Microsoft.FStar.Util.mk_ref None)

let should_dump = (fun ( l  :  string ) -> (match ((Support.Prims.op_Bang dump_module)) with
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

let init_options = (fun ( _11_25  :  unit ) -> (match (()) with
| () -> begin
(let _11_26 = (Support.ST.op_Colon_Equals show_signatures [])
in (let _11_28 = (Support.ST.op_Colon_Equals norm_then_print true)
in (let _11_30 = (let _13_2191 = (Support.Microsoft.FStar.Platform.exe "z3")
in (Support.ST.op_Colon_Equals z3_exe _13_2191))
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

let set_fstar_home = (fun ( _11_112  :  unit ) -> (match (()) with
| () -> begin
(let fh = (match ((Support.Prims.op_Bang fstar_home_opt)) with
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

let get_fstar_home = (fun ( _11_125  :  unit ) -> (match (()) with
| () -> begin
(match ((Support.Prims.op_Bang fstar_home_opt)) with
| None -> begin
(let _11_127 = (let _13_2196 = (set_fstar_home ())
in (Support.Prims.pipe_left Support.Prims.ignore _13_2196))
in (Support.Prims.op_Bang _fstar_home))
end
| Some (x) -> begin
x
end)
end))

let get_include_path = (fun ( _11_131  :  unit ) -> (match (()) with
| () -> begin
(let _13_2203 = (Support.Prims.op_Bang _include_path)
in (let _13_2202 = (let _13_2201 = (let _13_2200 = (let _13_2199 = (get_fstar_home ())
in (Support.String.strcat _13_2199 "/lib"))
in (_13_2200)::[])
in (".")::_13_2201)
in (List.append _13_2203 _13_2202)))
end))

let prims = (fun ( _11_132  :  unit ) -> (match (()) with
| () -> begin
(match ((Support.Prims.op_Bang prims_ref)) with
| None -> begin
"prims.fst"
end
| Some (x) -> begin
x
end)
end))

let prependOutputDir = (fun ( fname  :  string ) -> (match ((Support.Prims.op_Bang outputDir)) with
| None -> begin
fname
end
| Some (x) -> begin
(Support.String.strcat (Support.String.strcat x "/") fname)
end))

let cache_dir = "cache"

let display_usage = (fun ( _13_1010  :  unit ) -> (fun ( specs  :  ('u11u1074 * string * Support.Microsoft.FStar.Getopt.opt_variant * string) list ) -> (let _11_141 = (Support.Microsoft.FStar.Util.print_string "fstar [option] infile...")
in (List.iter (fun ( _11_148  :  ('u11u1074 * string * Support.Microsoft.FStar.Getopt.opt_variant * string) ) -> (match (_11_148) with
| (_, flag, p, doc) -> begin
(match (p) with
| Support.Microsoft.FStar.Getopt.ZeroArgs (ig) -> begin
(match ((doc = "")) with
| true -> begin
(let _13_2212 = (Support.Microsoft.FStar.Util.format1 "  --%s\n" flag)
in (Support.Microsoft.FStar.Util.print_string _13_2212))
end
| false -> begin
(let _13_2213 = (Support.Microsoft.FStar.Util.format2 "  --%s  %s\n" flag doc)
in (Support.Microsoft.FStar.Util.print_string _13_2213))
end)
end
| Support.Microsoft.FStar.Getopt.OneArg ((_, argname)) -> begin
(match ((doc = "")) with
| true -> begin
(let _13_2214 = (Support.Microsoft.FStar.Util.format2 "  --%s %s\n" flag argname)
in (Support.Microsoft.FStar.Util.print_string _13_2214))
end
| false -> begin
(let _13_2215 = (Support.Microsoft.FStar.Util.format3 "  --%s %s  %s\n" flag argname doc)
in (Support.Microsoft.FStar.Util.print_string _13_2215))
end)
end)
end)) specs))))

let rec specs = (fun ( _11_156  :  unit ) -> (match (()) with
| () -> begin
(let specs = ((Support.Microsoft.FStar.Getopt.noshort, "trace_error", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_157  :  unit ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals trace_error true)
end))), "Don\'t print an error message; show an exception trace instead"))::((Support.Microsoft.FStar.Getopt.noshort, "codegen", Support.Microsoft.FStar.Getopt.OneArg (((fun ( s  :  string ) -> (let _11_159 = (let _13_2223 = (parse_codegen s)
in (Support.ST.op_Colon_Equals codegen _13_2223))
in (Support.ST.op_Colon_Equals verify false))), "OCaml")), "Generate code for execution"))::((Support.Microsoft.FStar.Getopt.noshort, "codegen-lib", Support.Microsoft.FStar.Getopt.OneArg (((fun ( s  :  string ) -> (let _13_2228 = (let _13_2227 = (Support.Prims.op_Bang codegen_libs)
in ((Support.Microsoft.FStar.Util.split s "."))::_13_2227)
in (Support.ST.op_Colon_Equals codegen_libs _13_2228))), "namespace")), "External runtime library library"))::((Support.Microsoft.FStar.Getopt.noshort, "lax", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_162  :  unit ) -> (match (()) with
| () -> begin
(let _11_163 = (Support.ST.op_Colon_Equals pretype true)
in (Support.ST.op_Colon_Equals verify false))
end))), "Run the lax-type checker only (admit all verification conditions)"))::((Support.Microsoft.FStar.Getopt.noshort, "fstar_home", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x  :  string ) -> (Support.ST.op_Colon_Equals fstar_home_opt (Some (x)))), "dir")), "Set the FSTAR_HOME variable to dir"))::((Support.Microsoft.FStar.Getopt.noshort, "silent", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_166  :  unit ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals silent true)
end))), ""))::((Support.Microsoft.FStar.Getopt.noshort, "prims", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x  :  string ) -> (Support.ST.op_Colon_Equals prims_ref (Some (x)))), "file")), ""))::((Support.Microsoft.FStar.Getopt.noshort, "prn", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_168  :  unit ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals print_real_names true)
end))), "Print real names---you may want to use this in conjunction with logQueries"))::((Support.Microsoft.FStar.Getopt.noshort, "debug", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x  :  string ) -> (let _13_2242 = (let _13_2241 = (Support.Prims.op_Bang debug)
in (x)::_13_2241)
in (Support.ST.op_Colon_Equals debug _13_2242))), "module name")), "Print LOTS of debugging information while checking module [arg]"))::((Support.Microsoft.FStar.Getopt.noshort, "debug_level", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x  :  string ) -> (let _13_2247 = (let _13_2246 = (Support.Prims.op_Bang debug_level)
in ((dlevel x))::_13_2246)
in (Support.ST.op_Colon_Equals debug_level _13_2247))), "Low|Medium|High|Extreme")), "Control the verbosity of debugging info"))::((Support.Microsoft.FStar.Getopt.noshort, "log_types", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_171  :  unit ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals log_types true)
end))), "Print types computed for data/val/let-bindings"))::((Support.Microsoft.FStar.Getopt.noshort, "print_effect_args", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_172  :  unit ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals print_effect_args true)
end))), "Print inferred predicate transformers for all computation types"))::((Support.Microsoft.FStar.Getopt.noshort, "dump_module", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x  :  string ) -> (Support.ST.op_Colon_Equals dump_module (Some (x)))), "module name")), ""))::((Support.Microsoft.FStar.Getopt.noshort, "z3timeout", Support.Microsoft.FStar.Getopt.OneArg (((fun ( s  :  string ) -> (let _13_2256 = (Support.Microsoft.FStar.Util.int_of_string s)
in (Support.ST.op_Colon_Equals z3timeout _13_2256))), "t")), "Set the Z3 per-query (soft) timeout to t seconds (default 5)"))::((Support.Microsoft.FStar.Getopt.noshort, "admit_smt_queries", Support.Microsoft.FStar.Getopt.OneArg (((fun ( s  :  string ) -> (let _13_2260 = (match ((s = "true")) with
| true -> begin
true
end
| false -> begin
(match ((s = "false")) with
| true -> begin
false
end
| false -> begin
(failwith ("Invalid argument to --admit_smt_queries"))
end)
end)
in (Support.ST.op_Colon_Equals admit_smt_queries _13_2260))), "true|false")), "Admit SMT queries (UNSAFE! But, useful during development); default: \'false\'"))::((Support.Microsoft.FStar.Getopt.noshort, "logQueries", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_176  :  unit ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals logQueries true)
end))), "Log the Z3 queries in queries.smt2"))::((Support.Microsoft.FStar.Getopt.noshort, "admit_fsi", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x  :  string ) -> (let _13_2266 = (let _13_2265 = (Support.Prims.op_Bang admit_fsi)
in (x)::_13_2265)
in (Support.ST.op_Colon_Equals admit_fsi _13_2266))), "module name")), "Treat .fsi as a .fst"))::((Support.Microsoft.FStar.Getopt.noshort, "odir", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x  :  string ) -> (Support.ST.op_Colon_Equals outputDir (Some (x)))), "dir")), "Place output in directory dir"))::((Support.Microsoft.FStar.Getopt.noshort, "smt", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x  :  string ) -> (Support.ST.op_Colon_Equals z3_exe x)), "path")), "Path to the SMT solver (usually Z3, but could be any SMT2-compatible solver)"))::((Support.Microsoft.FStar.Getopt.noshort, "print_before_norm", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_180  :  unit ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals norm_then_print false)
end))), "Do not normalize types before printing (for debugging)"))::((Support.Microsoft.FStar.Getopt.noshort, "show_signatures", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x  :  string ) -> (let _13_2278 = (let _13_2277 = (Support.Prims.op_Bang show_signatures)
in (x)::_13_2277)
in (Support.ST.op_Colon_Equals show_signatures _13_2278))), "module name")), "Show the checked signatures for all top-level symbols in the module"))::((Support.Microsoft.FStar.Getopt.noshort, "full_context_dependency", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_182  :  unit ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals full_context_dependency true)
end))), "Introduce unification variables that are dependent on the entire context (possibly expensive, but better for type inference (on, by default)"))::((Support.Microsoft.FStar.Getopt.noshort, "MLish", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_183  :  unit ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals full_context_dependency false)
end))), "Introduce unification variables that are only dependent on the type variables in the context"))::((Support.Microsoft.FStar.Getopt.noshort, "print_implicits", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_184  :  unit ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals print_implicits true)
end))), "Print implicit arguments"))::((Support.Microsoft.FStar.Getopt.noshort, "hide_uvar_nums", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_185  :  unit ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals hide_uvar_nums true)
end))), "Don\'t print unification variable numbers"))::((Support.Microsoft.FStar.Getopt.noshort, "hide_genident_nums", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_186  :  unit ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals hide_genident_nums true)
end))), "Don\'t print generated identifier numbers"))::((Support.Microsoft.FStar.Getopt.noshort, "serialize_mods", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_187  :  unit ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals serialize_mods true)
end))), "Serialize compiled modules"))::((Support.Microsoft.FStar.Getopt.noshort, "initial_fuel", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x  :  string ) -> (let _13_2288 = (Support.Microsoft.FStar.Util.int_of_string x)
in (Support.ST.op_Colon_Equals initial_fuel _13_2288))), "non-negative integer")), "Number of unrolling of recursive functions to try initially (default 2)"))::((Support.Microsoft.FStar.Getopt.noshort, "max_fuel", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x  :  string ) -> (let _13_2292 = (Support.Microsoft.FStar.Util.int_of_string x)
in (Support.ST.op_Colon_Equals max_fuel _13_2292))), "non-negative integer")), "Number of unrolling of recursive functions to try at most (default 8)"))::((Support.Microsoft.FStar.Getopt.noshort, "min_fuel", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x  :  string ) -> (let _13_2296 = (Support.Microsoft.FStar.Util.int_of_string x)
in (Support.ST.op_Colon_Equals min_fuel _13_2296))), "non-negative integer")), "Minimum number of unrolling of recursive functions to try (default 1)"))::((Support.Microsoft.FStar.Getopt.noshort, "initial_ifuel", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x  :  string ) -> (let _13_2300 = (Support.Microsoft.FStar.Util.int_of_string x)
in (Support.ST.op_Colon_Equals initial_ifuel _13_2300))), "non-negative integer")), "Number of unrolling of inductive datatypes to try at first (default 1)"))::((Support.Microsoft.FStar.Getopt.noshort, "max_ifuel", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x  :  string ) -> (let _13_2304 = (Support.Microsoft.FStar.Util.int_of_string x)
in (Support.ST.op_Colon_Equals max_ifuel _13_2304))), "non-negative integer")), "Number of unrolling of inductive datatypes to try at most (default 1)"))::((Support.Microsoft.FStar.Getopt.noshort, "warn_top_level_effects", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_193  :  unit ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals warn_top_level_effects true)
end))), "Top-level effects are ignored, by default; turn this flag on to be warned when this happens"))::((Support.Microsoft.FStar.Getopt.noshort, "no_slack", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_194  :  unit ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals no_slack true)
end))), "Use the partially flow-insensitive variant of --rel2 (experimental)"))::((Support.Microsoft.FStar.Getopt.noshort, "eager_inference", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_195  :  unit ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals eager_inference true)
end))), "Solve all type-inference constraints eagerly; more efficient but at the cost of generality"))::((Support.Microsoft.FStar.Getopt.noshort, "unthrottle_inductives", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_196  :  unit ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals unthrottle_inductives true)
end))), "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)"))::((Support.Microsoft.FStar.Getopt.noshort, "use_eq_at_higher_order", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_197  :  unit ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals use_eq_at_higher_order true)
end))), "Use equality constraints when comparing higher-order types; temporary"))::((Support.Microsoft.FStar.Getopt.noshort, "fs_typ_app", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_198  :  unit ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals fs_typ_app true)
end))), "Allow the use of t<t1,...,tn> syntax for type applications; brittle since it clashes with the integer less-than operator"))::((Support.Microsoft.FStar.Getopt.noshort, "no_fs_typ_app", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_199  :  unit ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals fs_typ_app false)
end))), "Do not allow the use of t<t1,...,tn> syntax for type applications"))::((Support.Microsoft.FStar.Getopt.noshort, "n_cores", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x  :  string ) -> (let _13_2315 = (Support.Microsoft.FStar.Util.int_of_string x)
in (Support.ST.op_Colon_Equals n_cores _13_2315))), "positive integer")), "Maximum number of cores to use for the solver (default 1)"))::((Support.Microsoft.FStar.Getopt.noshort, "verify_module", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x  :  string ) -> (let _13_2320 = (let _13_2319 = (Support.Prims.op_Bang verify_module)
in (x)::_13_2319)
in (Support.ST.op_Colon_Equals verify_module _13_2320))), "string")), "Name of the module to verify"))::((Support.Microsoft.FStar.Getopt.noshort, "use_build_config", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_202  :  unit ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals use_build_config true)
end))), "Expect just a single file on the command line and no options; will read the \'build-config\' prelude from the file"))::((Support.Microsoft.FStar.Getopt.noshort, "split_cases", Support.Microsoft.FStar.Getopt.OneArg (((fun ( n  :  string ) -> (let _13_2325 = (Support.Microsoft.FStar.Util.int_of_string n)
in (Support.ST.op_Colon_Equals split_cases _13_2325))), "t")), "Partition VC of a match into groups of n cases"))::((Support.Microsoft.FStar.Getopt.noshort, "in", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _11_204  :  unit ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals interactive true)
end))), "Interactive mode; reads input from stdin"))::((Support.Microsoft.FStar.Getopt.noshort, "include", Support.Microsoft.FStar.Getopt.OneArg (((fun ( s  :  string ) -> (let _13_2331 = (let _13_2330 = (Support.Prims.op_Bang _include_path)
in (List.append _13_2330 ((s)::[])))
in (Support.ST.op_Colon_Equals _include_path _13_2331))), "path")), "A directory in which to search for files included on the command line"))::[]
in (('h', "help", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( x  :  unit ) -> (let _11_208 = ((display_usage ()) specs)
in (exit (0))))), "Display this information"))::specs)
end))
and parse_codegen = (fun ( s  :  string ) -> (match (s) with
| ("OCaml") -> begin
Some (s)
end
| _ -> begin
(let _11_215 = (Support.Microsoft.FStar.Util.print_string "Wrong argument to codegen flag\n")
in (let _11_217 = (let _13_2334 = (specs ())
in ((display_usage ()) _13_2334))
in (exit (1))))
end))

let should_verify = (fun ( m  :  string ) -> (let _13_2338 = (Support.Prims.op_Bang verify)
in (let _13_2337 = (match ((Support.Prims.op_Bang verify_module)) with
| [] -> begin
true
end
| l -> begin
((List.contains ()) m l)
end)
in (_13_2338 && _13_2337))))

let set_options = (fun ( s  :  string ) -> (let _13_2342 = (specs ())
in (Support.Microsoft.FStar.Getopt.parse_string _13_2342 (fun ( _11_223  :  string ) -> ()) s)))

let reset_options_string = (ref None)

let reset_options = (fun ( _11_225  :  unit ) -> (match (()) with
| () -> begin
(let _11_226 = (init_options ())
in (match ((Support.Prims.op_Bang reset_options_string)) with
| Some (x) -> begin
(set_options x)
end
| _ -> begin
(let _13_2346 = (specs ())
in (Support.Microsoft.FStar.Getopt.parse_cmdline _13_2346 (fun ( x  :  string ) -> ())))
end))
end))




