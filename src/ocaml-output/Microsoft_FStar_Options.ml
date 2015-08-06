
type debug_level_t =
| Low
| Medium
| High
| Extreme
| Other of string

let is_Low = (fun ( _discr_ ) -> (match (_discr_) with
| Low -> begin
true
end
| _ -> begin
false
end))

let is_Medium = (fun ( _discr_ ) -> (match (_discr_) with
| Medium -> begin
true
end
| _ -> begin
false
end))

let is_High = (fun ( _discr_ ) -> (match (_discr_) with
| High -> begin
true
end
| _ -> begin
false
end))

let is_Extreme = (fun ( _discr_ ) -> (match (_discr_) with
| Extreme -> begin
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

let z3_exe = (let _70_6117 = (Support.Microsoft.FStar.Platform.exe "z3")
in (Support.Microsoft.FStar.Util.mk_ref _70_6117))

let silent = (Support.Microsoft.FStar.Util.mk_ref false)

let debug = (Support.Microsoft.FStar.Util.mk_ref [])

let debug_level = (Support.Microsoft.FStar.Util.mk_ref [])

let dlevel = (fun ( _20_1 ) -> (match (_20_1) with
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

let debug_level_geq = (fun ( l2 ) -> (let _70_6127 = (Support.ST.read debug_level)
in (Support.All.pipe_right _70_6127 (Support.Microsoft.FStar.Util.for_some (fun ( l1 ) -> (one_debug_level_geq l1 l2))))))

let log_types = (Support.Microsoft.FStar.Util.mk_ref false)

let print_effect_args = (Support.Microsoft.FStar.Util.mk_ref false)

let print_real_names = (Support.Microsoft.FStar.Util.mk_ref false)

let dump_module = (Support.Microsoft.FStar.Util.mk_ref None)

let should_dump = (fun ( l ) -> (match ((Support.ST.read dump_module)) with
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

let init_options = (fun ( _20_25 ) -> (match (()) with
| () -> begin
(let _20_26 = (Support.ST.op_Colon_Equals show_signatures [])
in (let _20_28 = (Support.ST.op_Colon_Equals norm_then_print true)
in (let _20_30 = (let _70_6132 = (Support.Microsoft.FStar.Platform.exe "z3")
in (Support.ST.op_Colon_Equals z3_exe _70_6132))
in (let _20_32 = (Support.ST.op_Colon_Equals silent false)
in (let _20_34 = (Support.ST.op_Colon_Equals debug [])
in (let _20_36 = (Support.ST.op_Colon_Equals debug_level [])
in (let _20_38 = (Support.ST.op_Colon_Equals log_types false)
in (let _20_40 = (Support.ST.op_Colon_Equals print_effect_args false)
in (let _20_42 = (Support.ST.op_Colon_Equals print_real_names false)
in (let _20_44 = (Support.ST.op_Colon_Equals dump_module None)
in (let _20_46 = (Support.ST.op_Colon_Equals logQueries false)
in (let _20_48 = (Support.ST.op_Colon_Equals z3exe true)
in (let _20_50 = (Support.ST.op_Colon_Equals outputDir (Some (".")))
in (let _20_52 = (Support.ST.op_Colon_Equals fstar_home_opt None)
in (let _20_54 = (Support.ST.op_Colon_Equals _fstar_home "")
in (let _20_56 = (Support.ST.op_Colon_Equals prims_ref None)
in (let _20_58 = (Support.ST.op_Colon_Equals z3timeout 5)
in (let _20_60 = (Support.ST.op_Colon_Equals admit_smt_queries false)
in (let _20_62 = (Support.ST.op_Colon_Equals pretype true)
in (let _20_64 = (Support.ST.op_Colon_Equals codegen None)
in (let _20_66 = (Support.ST.op_Colon_Equals codegen_libs [])
in (let _20_68 = (Support.ST.op_Colon_Equals admit_fsi [])
in (let _20_70 = (Support.ST.op_Colon_Equals trace_error false)
in (let _20_72 = (Support.ST.op_Colon_Equals verify true)
in (let _20_74 = (Support.ST.op_Colon_Equals full_context_dependency true)
in (let _20_76 = (Support.ST.op_Colon_Equals print_implicits false)
in (let _20_78 = (Support.ST.op_Colon_Equals hide_uvar_nums false)
in (let _20_80 = (Support.ST.op_Colon_Equals hide_genident_nums false)
in (let _20_82 = (Support.ST.op_Colon_Equals serialize_mods false)
in (let _20_84 = (Support.ST.op_Colon_Equals initial_fuel 2)
in (let _20_86 = (Support.ST.op_Colon_Equals initial_ifuel 1)
in (let _20_88 = (Support.ST.op_Colon_Equals max_fuel 8)
in (let _20_90 = (Support.ST.op_Colon_Equals min_fuel 1)
in (let _20_92 = (Support.ST.op_Colon_Equals max_ifuel 2)
in (let _20_94 = (Support.ST.op_Colon_Equals warn_top_level_effects false)
in (let _20_96 = (Support.ST.op_Colon_Equals no_slack false)
in (let _20_98 = (Support.ST.op_Colon_Equals eager_inference false)
in (let _20_100 = (Support.ST.op_Colon_Equals unthrottle_inductives false)
in (let _20_102 = (Support.ST.op_Colon_Equals use_eq_at_higher_order false)
in (let _20_104 = (Support.ST.op_Colon_Equals fs_typ_app false)
in (let _20_106 = (Support.ST.op_Colon_Equals n_cores 1)
in (let _20_108 = (Support.ST.op_Colon_Equals split_cases 0)
in (let _20_110 = (Support.ST.op_Colon_Equals verify_module [])
in (Support.ST.op_Colon_Equals _include_path []))))))))))))))))))))))))))))))))))))))))))))
end))

let set_fstar_home = (fun ( _20_112 ) -> (match (()) with
| () -> begin
(let fh = (match ((Support.ST.read fstar_home_opt)) with
| None -> begin
(let x = (Support.Microsoft.FStar.Util.get_exec_dir ())
in (let x = (Support.String.strcat x "/..")
in (let _20_116 = (Support.ST.op_Colon_Equals _fstar_home x)
in (let _20_118 = (Support.ST.op_Colon_Equals fstar_home_opt (Some (x)))
in x))))
end
| Some (x) -> begin
(let _20_122 = (Support.ST.op_Colon_Equals _fstar_home x)
in x)
end)
in fh)
end))

let get_fstar_home = (fun ( _20_125 ) -> (match (()) with
| () -> begin
(match ((Support.ST.read fstar_home_opt)) with
| None -> begin
(let _20_127 = (let _70_6137 = (set_fstar_home ())
in (Support.All.pipe_left Support.Prims.ignore _70_6137))
in (Support.ST.read _fstar_home))
end
| Some (x) -> begin
x
end)
end))

let get_include_path = (fun ( _20_131 ) -> (match (()) with
| () -> begin
(let _70_6144 = (Support.ST.read _include_path)
in (let _70_6143 = (let _70_6142 = (let _70_6141 = (let _70_6140 = (get_fstar_home ())
in (Support.String.strcat _70_6140 "/lib"))
in (_70_6141)::[])
in (".")::_70_6142)
in (Support.List.append _70_6144 _70_6143)))
end))

let prims = (fun ( _20_132 ) -> (match (()) with
| () -> begin
(match ((Support.ST.read prims_ref)) with
| None -> begin
"prims.fst"
end
| Some (x) -> begin
x
end)
end))

let prependOutputDir = (fun ( fname ) -> (match ((Support.ST.read outputDir)) with
| None -> begin
fname
end
| Some (x) -> begin
(Support.String.strcat (Support.String.strcat x "/") fname)
end))

let cache_dir = "cache"

let display_usage = (fun ( specs ) -> (let _20_141 = (Support.Microsoft.FStar.Util.print_string "fstar [option] infile...")
in (Support.List.iter (fun ( _20_148 ) -> (match (_20_148) with
| (_20_144, flag, p, doc) -> begin
(match (p) with
| Support.Microsoft.FStar.Getopt.ZeroArgs (ig) -> begin
(match ((doc = "")) with
| true -> begin
(let _70_6152 = (Support.Microsoft.FStar.Util.format1 "  --%s\n" flag)
in (Support.Microsoft.FStar.Util.print_string _70_6152))
end
| false -> begin
(let _70_6153 = (Support.Microsoft.FStar.Util.format2 "  --%s  %s\n" flag doc)
in (Support.Microsoft.FStar.Util.print_string _70_6153))
end)
end
| Support.Microsoft.FStar.Getopt.OneArg ((_20_152, argname)) -> begin
(match ((doc = "")) with
| true -> begin
(let _70_6155 = (Support.Microsoft.FStar.Util.format2 "  --%s %s\n" flag argname)
in (Support.Microsoft.FStar.Util.print_string _70_6155))
end
| false -> begin
(let _70_6156 = (Support.Microsoft.FStar.Util.format3 "  --%s %s  %s\n" flag argname doc)
in (Support.Microsoft.FStar.Util.print_string _70_6156))
end)
end)
end)) specs)))

let rec specs = (fun ( _20_156 ) -> (match (()) with
| () -> begin
(let specs = ((Support.Microsoft.FStar.Getopt.noshort, "trace_error", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _20_157 ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals trace_error true)
end))), "Don\'t print an error message; show an exception trace instead"))::((Support.Microsoft.FStar.Getopt.noshort, "codegen", Support.Microsoft.FStar.Getopt.OneArg (((fun ( s ) -> (let _20_159 = (let _70_6165 = (parse_codegen s)
in (Support.ST.op_Colon_Equals codegen _70_6165))
in (Support.ST.op_Colon_Equals verify false))), "OCaml")), "Generate code for execution"))::((Support.Microsoft.FStar.Getopt.noshort, "codegen-lib", Support.Microsoft.FStar.Getopt.OneArg (((fun ( s ) -> (let _70_6170 = (let _70_6169 = (Support.ST.read codegen_libs)
in ((Support.Microsoft.FStar.Util.split s "."))::_70_6169)
in (Support.ST.op_Colon_Equals codegen_libs _70_6170))), "namespace")), "External runtime library library"))::((Support.Microsoft.FStar.Getopt.noshort, "lax", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _20_162 ) -> (match (()) with
| () -> begin
(let _20_163 = (Support.ST.op_Colon_Equals pretype true)
in (Support.ST.op_Colon_Equals verify false))
end))), "Run the lax-type checker only (admit all verification conditions)"))::((Support.Microsoft.FStar.Getopt.noshort, "fstar_home", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (Support.ST.op_Colon_Equals fstar_home_opt (Some (x)))), "dir")), "Set the FSTAR_HOME variable to dir"))::((Support.Microsoft.FStar.Getopt.noshort, "silent", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _20_166 ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals silent true)
end))), ""))::((Support.Microsoft.FStar.Getopt.noshort, "prims", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (Support.ST.op_Colon_Equals prims_ref (Some (x)))), "file")), ""))::((Support.Microsoft.FStar.Getopt.noshort, "prn", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _20_168 ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals print_real_names true)
end))), "Print real names---you may want to use this in conjunction with logQueries"))::((Support.Microsoft.FStar.Getopt.noshort, "debug", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (let _70_6184 = (let _70_6183 = (Support.ST.read debug)
in (x)::_70_6183)
in (Support.ST.op_Colon_Equals debug _70_6184))), "module name")), "Print LOTS of debugging information while checking module [arg]"))::((Support.Microsoft.FStar.Getopt.noshort, "debug_level", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (let _70_6189 = (let _70_6188 = (Support.ST.read debug_level)
in ((dlevel x))::_70_6188)
in (Support.ST.op_Colon_Equals debug_level _70_6189))), "Low|Medium|High|Extreme")), "Control the verbosity of debugging info"))::((Support.Microsoft.FStar.Getopt.noshort, "log_types", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _20_171 ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals log_types true)
end))), "Print types computed for data/val/let-bindings"))::((Support.Microsoft.FStar.Getopt.noshort, "print_effect_args", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _20_172 ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals print_effect_args true)
end))), "Print inferred predicate transformers for all computation types"))::((Support.Microsoft.FStar.Getopt.noshort, "dump_module", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (Support.ST.op_Colon_Equals dump_module (Some (x)))), "module name")), ""))::((Support.Microsoft.FStar.Getopt.noshort, "z3timeout", Support.Microsoft.FStar.Getopt.OneArg (((fun ( s ) -> (let _70_6198 = (Support.Microsoft.FStar.Util.int_of_string s)
in (Support.ST.op_Colon_Equals z3timeout _70_6198))), "t")), "Set the Z3 per-query (soft) timeout to t seconds (default 5)"))::((Support.Microsoft.FStar.Getopt.noshort, "admit_smt_queries", Support.Microsoft.FStar.Getopt.OneArg (((fun ( s ) -> (let _70_6202 = (match ((s = "true")) with
| true -> begin
true
end
| false -> begin
(match ((s = "false")) with
| true -> begin
false
end
| false -> begin
(Support.All.failwith "Invalid argument to --admit_smt_queries")
end)
end)
in (Support.ST.op_Colon_Equals admit_smt_queries _70_6202))), "true|false")), "Admit SMT queries (UNSAFE! But, useful during development); default: \'false\'"))::((Support.Microsoft.FStar.Getopt.noshort, "logQueries", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _20_176 ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals logQueries true)
end))), "Log the Z3 queries in queries.smt2"))::((Support.Microsoft.FStar.Getopt.noshort, "admit_fsi", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (let _70_6208 = (let _70_6207 = (Support.ST.read admit_fsi)
in (x)::_70_6207)
in (Support.ST.op_Colon_Equals admit_fsi _70_6208))), "module name")), "Treat .fsi as a .fst"))::((Support.Microsoft.FStar.Getopt.noshort, "odir", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (Support.ST.op_Colon_Equals outputDir (Some (x)))), "dir")), "Place output in directory dir"))::((Support.Microsoft.FStar.Getopt.noshort, "smt", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (Support.ST.op_Colon_Equals z3_exe x)), "path")), "Path to the SMT solver (usually Z3, but could be any SMT2-compatible solver)"))::((Support.Microsoft.FStar.Getopt.noshort, "print_before_norm", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _20_180 ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals norm_then_print false)
end))), "Do not normalize types before printing (for debugging)"))::((Support.Microsoft.FStar.Getopt.noshort, "show_signatures", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (let _70_6220 = (let _70_6219 = (Support.ST.read show_signatures)
in (x)::_70_6219)
in (Support.ST.op_Colon_Equals show_signatures _70_6220))), "module name")), "Show the checked signatures for all top-level symbols in the module"))::((Support.Microsoft.FStar.Getopt.noshort, "full_context_dependency", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _20_182 ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals full_context_dependency true)
end))), "Introduce unification variables that are dependent on the entire context (possibly expensive, but better for type inference (on, by default)"))::((Support.Microsoft.FStar.Getopt.noshort, "MLish", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _20_183 ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals full_context_dependency false)
end))), "Introduce unification variables that are only dependent on the type variables in the context"))::((Support.Microsoft.FStar.Getopt.noshort, "print_implicits", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _20_184 ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals print_implicits true)
end))), "Print implicit arguments"))::((Support.Microsoft.FStar.Getopt.noshort, "hide_uvar_nums", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _20_185 ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals hide_uvar_nums true)
end))), "Don\'t print unification variable numbers"))::((Support.Microsoft.FStar.Getopt.noshort, "hide_genident_nums", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _20_186 ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals hide_genident_nums true)
end))), "Don\'t print generated identifier numbers"))::((Support.Microsoft.FStar.Getopt.noshort, "serialize_mods", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _20_187 ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals serialize_mods true)
end))), "Serialize compiled modules"))::((Support.Microsoft.FStar.Getopt.noshort, "initial_fuel", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (let _70_6230 = (Support.Microsoft.FStar.Util.int_of_string x)
in (Support.ST.op_Colon_Equals initial_fuel _70_6230))), "non-negative integer")), "Number of unrolling of recursive functions to try initially (default 2)"))::((Support.Microsoft.FStar.Getopt.noshort, "max_fuel", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (let _70_6234 = (Support.Microsoft.FStar.Util.int_of_string x)
in (Support.ST.op_Colon_Equals max_fuel _70_6234))), "non-negative integer")), "Number of unrolling of recursive functions to try at most (default 8)"))::((Support.Microsoft.FStar.Getopt.noshort, "min_fuel", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (let _70_6238 = (Support.Microsoft.FStar.Util.int_of_string x)
in (Support.ST.op_Colon_Equals min_fuel _70_6238))), "non-negative integer")), "Minimum number of unrolling of recursive functions to try (default 1)"))::((Support.Microsoft.FStar.Getopt.noshort, "initial_ifuel", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (let _70_6242 = (Support.Microsoft.FStar.Util.int_of_string x)
in (Support.ST.op_Colon_Equals initial_ifuel _70_6242))), "non-negative integer")), "Number of unrolling of inductive datatypes to try at first (default 1)"))::((Support.Microsoft.FStar.Getopt.noshort, "max_ifuel", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (let _70_6246 = (Support.Microsoft.FStar.Util.int_of_string x)
in (Support.ST.op_Colon_Equals max_ifuel _70_6246))), "non-negative integer")), "Number of unrolling of inductive datatypes to try at most (default 1)"))::((Support.Microsoft.FStar.Getopt.noshort, "warn_top_level_effects", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _20_193 ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals warn_top_level_effects true)
end))), "Top-level effects are ignored, by default; turn this flag on to be warned when this happens"))::((Support.Microsoft.FStar.Getopt.noshort, "no_slack", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _20_194 ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals no_slack true)
end))), "Use the partially flow-insensitive variant of --rel2 (experimental)"))::((Support.Microsoft.FStar.Getopt.noshort, "eager_inference", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _20_195 ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals eager_inference true)
end))), "Solve all type-inference constraints eagerly; more efficient but at the cost of generality"))::((Support.Microsoft.FStar.Getopt.noshort, "unthrottle_inductives", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _20_196 ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals unthrottle_inductives true)
end))), "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)"))::((Support.Microsoft.FStar.Getopt.noshort, "use_eq_at_higher_order", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _20_197 ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals use_eq_at_higher_order true)
end))), "Use equality constraints when comparing higher-order types; temporary"))::((Support.Microsoft.FStar.Getopt.noshort, "fs_typ_app", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _20_198 ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals fs_typ_app true)
end))), "Allow the use of t<t1,...,tn> syntax for type applications; brittle since it clashes with the integer less-than operator"))::((Support.Microsoft.FStar.Getopt.noshort, "no_fs_typ_app", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _20_199 ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals fs_typ_app false)
end))), "Do not allow the use of t<t1,...,tn> syntax for type applications"))::((Support.Microsoft.FStar.Getopt.noshort, "n_cores", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (let _70_6257 = (Support.Microsoft.FStar.Util.int_of_string x)
in (Support.ST.op_Colon_Equals n_cores _70_6257))), "positive integer")), "Maximum number of cores to use for the solver (default 1)"))::((Support.Microsoft.FStar.Getopt.noshort, "verify_module", Support.Microsoft.FStar.Getopt.OneArg (((fun ( x ) -> (let _70_6262 = (let _70_6261 = (Support.ST.read verify_module)
in (x)::_70_6261)
in (Support.ST.op_Colon_Equals verify_module _70_6262))), "string")), "Name of the module to verify"))::((Support.Microsoft.FStar.Getopt.noshort, "use_build_config", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _20_202 ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals use_build_config true)
end))), "Expect just a single file on the command line and no options; will read the \'build-config\' prelude from the file"))::((Support.Microsoft.FStar.Getopt.noshort, "split_cases", Support.Microsoft.FStar.Getopt.OneArg (((fun ( n ) -> (let _70_6267 = (Support.Microsoft.FStar.Util.int_of_string n)
in (Support.ST.op_Colon_Equals split_cases _70_6267))), "t")), "Partition VC of a match into groups of n cases"))::((Support.Microsoft.FStar.Getopt.noshort, "in", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _20_204 ) -> (match (()) with
| () -> begin
(Support.ST.op_Colon_Equals interactive true)
end))), "Interactive mode; reads input from stdin"))::((Support.Microsoft.FStar.Getopt.noshort, "include", Support.Microsoft.FStar.Getopt.OneArg (((fun ( s ) -> (let _70_6273 = (let _70_6272 = (Support.ST.read _include_path)
in (Support.List.append _70_6272 ((s)::[])))
in (Support.ST.op_Colon_Equals _include_path _70_6273))), "path")), "A directory in which to search for files included on the command line"))::((Support.Microsoft.FStar.Getopt.noshort, "fsi", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( _20_206 ) -> (match (()) with
| () -> begin
(set_interactive_fsi ())
end))), "fsi flag; A flag to indicate if type checking a fsi in the interactive mode"))::[]
in (('h', "help", Support.Microsoft.FStar.Getopt.ZeroArgs ((fun ( x ) -> (let _20_209 = (display_usage specs)
in (Support.All.exit 0)))), "Display this information"))::specs)
end))
and parse_codegen = (fun ( s ) -> (match (s) with
| ("OCaml-experimental") | ("OCaml") -> begin
Some (s)
end
| _20_215 -> begin
(let _20_216 = (Support.Microsoft.FStar.Util.print_string "Wrong argument to codegen flag\n")
in (let _20_218 = (let _70_6277 = (specs ())
in (display_usage _70_6277))
in (Support.All.exit 1)))
end))
and set_interactive_fsi = (fun ( _20_220 ) -> (match ((Support.ST.read interactive)) with
| true -> begin
(Support.ST.op_Colon_Equals interactive_fsi true)
end
| false -> begin
(let _20_222 = (Support.Microsoft.FStar.Util.print_string "Set interactive flag first before setting interactive fsi flag\n")
in (let _20_224 = (let _70_6279 = (specs ())
in (display_usage _70_6279))
in (Support.All.exit 1)))
end))

let should_verify = (fun ( m ) -> ((Support.ST.read verify) && (match ((Support.ST.read verify_module)) with
| [] -> begin
true
end
| l -> begin
(Support.List.contains m l)
end)))

let set_options = (fun ( s ) -> (let _70_6285 = (specs ())
in (Support.Microsoft.FStar.Getopt.parse_string _70_6285 (fun ( _20_230 ) -> ()) s)))

let reset_options_string = (ref None)

let reset_options = (fun ( _20_232 ) -> (match (()) with
| () -> begin
(let _20_233 = (init_options ())
in (match ((Support.ST.read reset_options_string)) with
| Some (x) -> begin
(set_options x)
end
| _20_238 -> begin
(let _70_6289 = (specs ())
in (Support.Microsoft.FStar.Getopt.parse_cmdline _70_6289 (fun ( x ) -> ())))
end))
end))




