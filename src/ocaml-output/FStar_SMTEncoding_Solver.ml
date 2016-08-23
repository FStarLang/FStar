
open Prims
# 27 "FStar.SMTEncoding.Solver.fst"
type z3_result =
(FStar_SMTEncoding_Z3.unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either

# 36 "FStar.SMTEncoding.Solver.fst"
type hint_stat =
{hint : FStar_Util.hint Prims.option; replay_result : z3_result; elapsed_time : Prims.int; source_location : FStar_Range.range}

# 37 "FStar.SMTEncoding.Solver.fst"
let is_Mkhint_stat : hint_stat  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkhint_stat"))))

# 42 "FStar.SMTEncoding.Solver.fst"
type hint_stats_t =
hint_stat Prims.list

# 43 "FStar.SMTEncoding.Solver.fst"
let recorded_hints : FStar_Util.hints Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)

# 44 "FStar.SMTEncoding.Solver.fst"
let replaying_hints : FStar_Util.hints Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)

# 45 "FStar.SMTEncoding.Solver.fst"
let hint_stats : hint_stat Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 46 "FStar.SMTEncoding.Solver.fst"
let format_hints_file_name : Prims.string  ->  Prims.string = (fun src_filename -> (FStar_Util.format1 "%s.hints" src_filename))

# 49 "FStar.SMTEncoding.Solver.fst"
let initialize_hints_db = (fun src_filename force_record -> (
# 55 "FStar.SMTEncoding.Solver.fst"
let _87_11 = (FStar_ST.op_Colon_Equals hint_stats [])
in (
# 56 "FStar.SMTEncoding.Solver.fst"
let _87_13 = if (FStar_Options.record_hints ()) then begin
(FStar_ST.op_Colon_Equals recorded_hints (Some ([])))
end else begin
()
end
in if (FStar_Options.use_hints ()) then begin
(
# 58 "FStar.SMTEncoding.Solver.fst"
let norm_src_filename = (FStar_Util.normalize_file_path src_filename)
in (
# 59 "FStar.SMTEncoding.Solver.fst"
let val_filename = (format_hints_file_name norm_src_filename)
in (match ((FStar_Util.read_hints val_filename)) with
| Some (hints) -> begin
(
# 62 "FStar.SMTEncoding.Solver.fst"
let expected_digest = (FStar_Util.digest_of_file norm_src_filename)
in (
# 63 "FStar.SMTEncoding.Solver.fst"
let _87_20 = if (FStar_Options.hint_info ()) then begin
if (hints.FStar_Util.module_digest = expected_digest) then begin
(FStar_Util.print1 "(%s) digest is valid; using hints db.\n" norm_src_filename)
end else begin
(FStar_Util.print1 "(%s) digest is invalid; using potentially stale hints\n" norm_src_filename)
end
end else begin
()
end
in (FStar_ST.op_Colon_Equals replaying_hints (Some (hints.FStar_Util.hints)))))
end
| None -> begin
if (FStar_Options.hint_info ()) then begin
(FStar_Util.print1 "(%s) Unable to read hints db.\n" norm_src_filename)
end else begin
()
end
end)))
end else begin
()
end)))

# 73 "FStar.SMTEncoding.Solver.fst"
let finalize_hints_db : Prims.string  ->  Prims.unit = (fun src_filename -> (
# 76 "FStar.SMTEncoding.Solver.fst"
let _87_27 = if (FStar_Options.record_hints ()) then begin
(
# 77 "FStar.SMTEncoding.Solver.fst"
let hints = (let _180_20 = (FStar_ST.read recorded_hints)
in (FStar_Option.get _180_20))
in (
# 78 "FStar.SMTEncoding.Solver.fst"
let hints_db = (let _180_21 = (FStar_Util.digest_of_file src_filename)
in {FStar_Util.module_digest = _180_21; FStar_Util.hints = hints})
in (
# 82 "FStar.SMTEncoding.Solver.fst"
let hints_file_name = (format_hints_file_name src_filename)
in (FStar_Util.write_hints hints_file_name hints_db))))
end else begin
()
end
in (
# 85 "FStar.SMTEncoding.Solver.fst"
let _87_35 = if (FStar_Options.hint_info ()) then begin
(
# 86 "FStar.SMTEncoding.Solver.fst"
let stats = (let _180_22 = (FStar_ST.read hint_stats)
in (FStar_All.pipe_right _180_22 FStar_List.rev))
in (FStar_All.pipe_right stats (FStar_List.iter (fun s -> (match (s.replay_result) with
| FStar_Util.Inl (_unsat_core) -> begin
(let _180_25 = (FStar_Range.string_of_range s.source_location)
in (let _180_24 = (FStar_Util.string_of_int s.elapsed_time)
in (FStar_Util.print2 "Hint-info (%s): Replay succeeded in %s milliseconds\n" _180_25 _180_24)))
end
| FStar_Util.Inr (_error) -> begin
(let _180_27 = (FStar_Range.string_of_range s.source_location)
in (let _180_26 = (FStar_Util.string_of_int s.elapsed_time)
in (FStar_Util.print2 "Hint-info (%s): Replay failed in %s milliseconds\n" _180_27 _180_26)))
end)))))
end else begin
()
end
in (
# 97 "FStar.SMTEncoding.Solver.fst"
let _87_37 = (FStar_ST.op_Colon_Equals recorded_hints None)
in (
# 98 "FStar.SMTEncoding.Solver.fst"
let _87_39 = (FStar_ST.op_Colon_Equals replaying_hints None)
in (FStar_ST.op_Colon_Equals hint_stats []))))))

# 99 "FStar.SMTEncoding.Solver.fst"
let with_hints_db = (fun fname f -> (
# 102 "FStar.SMTEncoding.Solver.fst"
let _87_43 = (initialize_hints_db fname false)
in (
# 103 "FStar.SMTEncoding.Solver.fst"
let result = (f ())
in (
# 106 "FStar.SMTEncoding.Solver.fst"
let _87_46 = (finalize_hints_db fname)
in result))))

# 107 "FStar.SMTEncoding.Solver.fst"
let next_hint : Prims.string  ->  Prims.int  ->  FStar_Util.hint Prims.option = (fun qname qindex -> (match ((FStar_ST.read replaying_hints)) with
| Some (hints) -> begin
(FStar_Util.find_map hints (fun _87_1 -> (match (_87_1) with
| Some (hint) when ((hint.FStar_Util.hint_name = qname) && (hint.FStar_Util.hint_index = qindex)) -> begin
Some (hint)
end
| _87_56 -> begin
None
end)))
end
| _87_58 -> begin
None
end))

# 115 "FStar.SMTEncoding.Solver.fst"
let record_hint : FStar_Util.hint Prims.option  ->  Prims.unit = (fun hint -> (
# 118 "FStar.SMTEncoding.Solver.fst"
let hint = (match (hint) with
| None -> begin
None
end
| Some (h) -> begin
Some ((
# 120 "FStar.SMTEncoding.Solver.fst"
let _87_63 = h
in {FStar_Util.hint_name = _87_63.FStar_Util.hint_name; FStar_Util.hint_index = _87_63.FStar_Util.hint_index; FStar_Util.fuel = _87_63.FStar_Util.fuel; FStar_Util.ifuel = _87_63.FStar_Util.ifuel; FStar_Util.unsat_core = _87_63.FStar_Util.unsat_core; FStar_Util.query_elapsed_time = 0}))
end)
in (match ((FStar_ST.read recorded_hints)) with
| Some (l) -> begin
(FStar_ST.op_Colon_Equals recorded_hints (Some ((FStar_List.append l ((hint)::[])))))
end
| _87_69 -> begin
()
end)))

# 123 "FStar.SMTEncoding.Solver.fst"
let record_hint_stat : FStar_Util.hint Prims.option  ->  z3_result  ->  Prims.int  ->  FStar_Range.range  ->  Prims.unit = (fun h res time r -> (
# 126 "FStar.SMTEncoding.Solver.fst"
let s = {hint = h; replay_result = res; elapsed_time = time; source_location = r}
in (let _180_49 = (let _180_48 = (FStar_ST.read hint_stats)
in (s)::_180_48)
in (FStar_ST.op_Colon_Equals hint_stats _180_49))))

# 132 "FStar.SMTEncoding.Solver.fst"
let ask_and_report_errors : FStar_TypeChecker_Env.env  ->  ((FStar_SMTEncoding_Z3.label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun env all_labels prefix query suffix -> (
# 138 "FStar.SMTEncoding.Solver.fst"
let _87_80 = (FStar_SMTEncoding_Z3.giveZ3 prefix)
in (
# 139 "FStar.SMTEncoding.Solver.fst"
let _87_89 = (match (env.FStar_TypeChecker_Env.qname_and_index) with
| None -> begin
(FStar_All.failwith "No query name set!")
end
| Some (q, n) -> begin
(((FStar_Ident.text_of_lid q)), (n))
end)
in (match (_87_89) with
| (query_name, query_index) -> begin
(
# 142 "FStar.SMTEncoding.Solver.fst"
let minimum_workable_fuel = (FStar_Util.mk_ref None)
in (
# 143 "FStar.SMTEncoding.Solver.fst"
let set_minimum_workable_fuel = (fun f _87_2 -> (match (_87_2) with
| [] -> begin
()
end
| errs -> begin
(match ((FStar_ST.read minimum_workable_fuel)) with
| Some (_87_97) -> begin
()
end
| None -> begin
(FStar_ST.op_Colon_Equals minimum_workable_fuel (Some (((f), (errs)))))
end)
end))
in (
# 149 "FStar.SMTEncoding.Solver.fst"
let with_fuel = (fun label_assumptions p _87_106 -> (match (_87_106) with
| (n, i, timeout_ms) -> begin
(let _180_97 = (let _180_87 = (let _180_72 = (let _180_71 = (FStar_Util.string_of_int n)
in (let _180_70 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _180_71 _180_70)))
in FStar_SMTEncoding_Term.Caption (_180_72))
in (let _180_86 = (let _180_85 = (let _180_77 = (let _180_76 = (let _180_75 = (let _180_74 = (FStar_SMTEncoding_Term.mkApp (("MaxFuel"), ([])))
in (let _180_73 = (FStar_SMTEncoding_Term.n_fuel n)
in ((_180_74), (_180_73))))
in (FStar_SMTEncoding_Term.mkEq _180_75))
in ((_180_76), (None), (None)))
in FStar_SMTEncoding_Term.Assume (_180_77))
in (let _180_84 = (let _180_83 = (let _180_82 = (let _180_81 = (let _180_80 = (let _180_79 = (FStar_SMTEncoding_Term.mkApp (("MaxIFuel"), ([])))
in (let _180_78 = (FStar_SMTEncoding_Term.n_fuel i)
in ((_180_79), (_180_78))))
in (FStar_SMTEncoding_Term.mkEq _180_80))
in ((_180_81), (None), (None)))
in FStar_SMTEncoding_Term.Assume (_180_82))
in (_180_83)::(p)::[])
in (_180_85)::_180_84))
in (_180_87)::_180_86))
in (let _180_96 = (let _180_95 = (let _180_94 = (let _180_90 = (let _180_89 = (let _180_88 = (FStar_Util.string_of_int timeout_ms)
in (("timeout"), (_180_88)))
in FStar_SMTEncoding_Term.SetOption (_180_89))
in (_180_90)::[])
in (let _180_93 = (let _180_92 = (let _180_91 = if (FStar_Options.record_hints ()) then begin
(FStar_SMTEncoding_Term.GetUnsatCore)::[]
end else begin
[]
end
in (FStar_List.append _180_91 suffix))
in (FStar_List.append ((FStar_SMTEncoding_Term.CheckSat)::[]) _180_92))
in (FStar_List.append _180_94 _180_93)))
in (FStar_List.append label_assumptions _180_95))
in (FStar_List.append _180_97 _180_96)))
end))
in (
# 160 "FStar.SMTEncoding.Solver.fst"
let check = (fun p -> (
# 161 "FStar.SMTEncoding.Solver.fst"
let default_timeout = ((FStar_Options.z3_timeout ()) * 1000)
in (
# 162 "FStar.SMTEncoding.Solver.fst"
let default_initial_config = (let _180_101 = (FStar_Options.initial_fuel ())
in (let _180_100 = (FStar_Options.initial_ifuel ())
in ((_180_101), (_180_100), (default_timeout))))
in (
# 163 "FStar.SMTEncoding.Solver.fst"
let hint_opt = (next_hint query_name query_index)
in (
# 164 "FStar.SMTEncoding.Solver.fst"
let _87_120 = (match (hint_opt) with
| None -> begin
((None), (default_initial_config))
end
| Some (hint) -> begin
(
# 168 "FStar.SMTEncoding.Solver.fst"
let _87_117 = if (FStar_Option.isSome hint.FStar_Util.unsat_core) then begin
((hint.FStar_Util.unsat_core), (default_timeout))
end else begin
((None), ((60 * 1000)))
end
in (match (_87_117) with
| (core, timeout) -> begin
((core), (((hint.FStar_Util.fuel), (hint.FStar_Util.ifuel), (timeout))))
end))
end)
in (match (_87_120) with
| (unsat_core, initial_config) -> begin
(
# 174 "FStar.SMTEncoding.Solver.fst"
let alt_configs = (let _180_122 = (let _180_121 = if ((default_initial_config <> initial_config) || (FStar_Option.isSome unsat_core)) then begin
(default_initial_config)::[]
end else begin
[]
end
in (let _180_120 = (let _180_119 = if ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ())) then begin
(let _180_104 = (let _180_103 = (FStar_Options.initial_fuel ())
in (let _180_102 = (FStar_Options.max_ifuel ())
in ((_180_103), (_180_102), (default_timeout))))
in (_180_104)::[])
end else begin
[]
end
in (let _180_118 = (let _180_117 = if (((FStar_Options.max_fuel ()) / 2) > (FStar_Options.initial_fuel ())) then begin
(let _180_107 = (let _180_106 = ((FStar_Options.max_fuel ()) / 2)
in (let _180_105 = (FStar_Options.max_ifuel ())
in ((_180_106), (_180_105), (default_timeout))))
in (_180_107)::[])
end else begin
[]
end
in (let _180_116 = (let _180_115 = if (((FStar_Options.max_fuel ()) > (FStar_Options.initial_fuel ())) && ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ()))) then begin
(let _180_110 = (let _180_109 = (FStar_Options.max_fuel ())
in (let _180_108 = (FStar_Options.max_ifuel ())
in ((_180_109), (_180_108), (default_timeout))))
in (_180_110)::[])
end else begin
[]
end
in (let _180_114 = (let _180_113 = if ((FStar_Options.min_fuel ()) < (FStar_Options.initial_fuel ())) then begin
(let _180_112 = (let _180_111 = (FStar_Options.min_fuel ())
in ((_180_111), (1), (default_timeout)))
in (_180_112)::[])
end else begin
[]
end
in (_180_113)::[])
in (_180_115)::_180_114))
in (_180_117)::_180_116))
in (_180_119)::_180_118))
in (_180_121)::_180_120))
in (FStar_List.flatten _180_122))
in (
# 182 "FStar.SMTEncoding.Solver.fst"
let report = (fun p errs -> (
# 183 "FStar.SMTEncoding.Solver.fst"
let errs = if ((FStar_Options.detail_errors ()) && ((FStar_Options.n_cores ()) = 1)) then begin
(
# 184 "FStar.SMTEncoding.Solver.fst"
let _87_132 = (match ((FStar_ST.read minimum_workable_fuel)) with
| Some (f, errs) -> begin
((f), (errs))
end
| None -> begin
(let _180_128 = (let _180_127 = (FStar_Options.min_fuel ())
in ((_180_127), (1), (default_timeout)))
in ((_180_128), (errs)))
end)
in (match (_87_132) with
| (min_fuel, potential_errors) -> begin
(
# 187 "FStar.SMTEncoding.Solver.fst"
let ask_z3 = (fun label_assumptions -> (
# 188 "FStar.SMTEncoding.Solver.fst"
let res = (FStar_Util.mk_ref None)
in (
# 189 "FStar.SMTEncoding.Solver.fst"
let _87_137 = (let _180_132 = (with_fuel label_assumptions p min_fuel)
in (FStar_SMTEncoding_Z3.ask None all_labels _180_132 (fun r -> (FStar_ST.op_Colon_Equals res (Some (r))))))
in (let _180_133 = (FStar_ST.read res)
in (FStar_Option.get _180_133)))))
in (FStar_SMTEncoding_ErrorReporting.detail_errors all_labels errs ask_z3))
end))
end else begin
errs
end
in (
# 194 "FStar.SMTEncoding.Solver.fst"
let errs = (match (errs) with
| [] -> begin
(((((""), (FStar_SMTEncoding_Term.Term_sort))), ("Unknown assertion failed"), (FStar_Range.dummyRange)))::[]
end
| _87_142 -> begin
errs
end)
in (
# 198 "FStar.SMTEncoding.Solver.fst"
let _87_144 = (record_hint None)
in (
# 199 "FStar.SMTEncoding.Solver.fst"
let _87_146 = if (FStar_Options.print_fuels ()) then begin
(let _180_139 = (let _180_134 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _180_134))
in (let _180_138 = (let _180_135 = (FStar_Options.max_fuel ())
in (FStar_All.pipe_right _180_135 FStar_Util.string_of_int))
in (let _180_137 = (let _180_136 = (FStar_Options.max_ifuel ())
in (FStar_All.pipe_right _180_136 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _180_139 _180_138 _180_137))))
end else begin
()
end
in (
# 204 "FStar.SMTEncoding.Solver.fst"
let _87_153 = (let _180_141 = (FStar_All.pipe_right errs (FStar_List.map (fun _87_152 -> (match (_87_152) with
| (_87_149, x, y) -> begin
((x), (y))
end))))
in (FStar_TypeChecker_Errors.add_errors env _180_141))
in if (FStar_Options.detail_errors ()) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Detailed error report follows\n")))
end else begin
()
end))))))
in (
# 208 "FStar.SMTEncoding.Solver.fst"
let use_errors = (fun errs result -> (match (((errs), (result))) with
| (([], _)) | ((_, FStar_Util.Inl (_))) -> begin
result
end
| (_87_169, FStar_Util.Inr (_87_171)) -> begin
FStar_Util.Inr (errs)
end))
in (
# 213 "FStar.SMTEncoding.Solver.fst"
let rec try_alt_configs = (fun prev_f p errs cfgs -> (
# 214 "FStar.SMTEncoding.Solver.fst"
let _87_180 = (set_minimum_workable_fuel prev_f errs)
in (match (cfgs) with
| [] -> begin
(report p errs)
end
| (mi)::[] -> begin
(match (errs) with
| [] -> begin
(let _180_159 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask None all_labels _180_159 (cb false mi p [])))
end
| _87_187 -> begin
(
# 220 "FStar.SMTEncoding.Solver.fst"
let _87_188 = (set_minimum_workable_fuel prev_f errs)
in (report p errs))
end)
end
| (mi)::tl -> begin
(let _180_161 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask None all_labels _180_161 (fun _87_195 -> (match (_87_195) with
| (result, elapsed_time) -> begin
(cb false mi p tl (((use_errors errs result)), (elapsed_time)))
end))))
end)))
and cb = (fun used_hint _87_200 p alt _87_205 -> (match (((_87_200), (_87_205))) with
| ((prev_fuel, prev_ifuel, timeout), (result, elapsed_time)) -> begin
(
# 229 "FStar.SMTEncoding.Solver.fst"
let _87_208 = if used_hint then begin
(
# 229 "FStar.SMTEncoding.Solver.fst"
let _87_206 = (FStar_SMTEncoding_Z3.refresh ())
in (let _180_167 = (FStar_TypeChecker_Env.get_range env)
in (record_hint_stat hint_opt result elapsed_time _180_167)))
end else begin
()
end
in (
# 230 "FStar.SMTEncoding.Solver.fst"
let at_log_file = (fun _87_211 -> (match (()) with
| () -> begin
if (FStar_Options.log_queries ()) then begin
(let _180_170 = (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.log_file_name ())
in (Prims.strcat "@" _180_170))
end else begin
""
end
end))
in (
# 234 "FStar.SMTEncoding.Solver.fst"
let query_info = (fun tag -> (let _180_188 = (let _180_187 = (let _180_173 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _180_173))
in (let _180_186 = (let _180_185 = (at_log_file ())
in (let _180_184 = (let _180_183 = (let _180_182 = (FStar_Util.string_of_int query_index)
in (let _180_181 = (let _180_180 = (let _180_179 = (let _180_178 = (FStar_Util.string_of_int elapsed_time)
in (let _180_177 = (let _180_176 = (FStar_Util.string_of_int prev_fuel)
in (let _180_175 = (let _180_174 = (FStar_Util.string_of_int prev_ifuel)
in (_180_174)::[])
in (_180_176)::_180_175))
in (_180_178)::_180_177))
in (if used_hint then begin
" (with hint)"
end else begin
""
end)::_180_179)
in (tag)::_180_180)
in (_180_182)::_180_181))
in (query_name)::_180_183)
in (_180_185)::_180_184))
in (_180_187)::_180_186))
in (FStar_Util.print "(%s%s)\n\tQuery (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s\n" _180_188)))
in (match (result) with
| FStar_Util.Inl (unsat_core) -> begin
(
# 248 "FStar.SMTEncoding.Solver.fst"
let _87_217 = if (not (used_hint)) then begin
(
# 249 "FStar.SMTEncoding.Solver.fst"
let hint = {FStar_Util.hint_name = query_name; FStar_Util.hint_index = query_index; FStar_Util.fuel = prev_fuel; FStar_Util.ifuel = prev_ifuel; FStar_Util.unsat_core = unsat_core; FStar_Util.query_elapsed_time = elapsed_time}
in (record_hint (Some (hint))))
end else begin
(record_hint hint_opt)
end
in if ((FStar_Options.print_fuels ()) || (FStar_Options.hint_info ())) then begin
(query_info "succeeded")
end else begin
()
end)
end
| FStar_Util.Inr (errs) -> begin
(
# 261 "FStar.SMTEncoding.Solver.fst"
let _87_221 = if ((FStar_Options.print_fuels ()) || (FStar_Options.hint_info ())) then begin
(query_info "failed")
end else begin
()
end
in (try_alt_configs ((prev_fuel), (prev_ifuel), (timeout)) p errs alt))
end))))
end))
in (
# 266 "FStar.SMTEncoding.Solver.fst"
let _87_223 = if (FStar_Option.isSome unsat_core) then begin
(FStar_SMTEncoding_Z3.refresh ())
end else begin
()
end
in (let _180_191 = (with_fuel [] p initial_config)
in (let _180_190 = (let _180_189 = (FStar_Option.isSome unsat_core)
in (cb _180_189 initial_config p alt_configs))
in (FStar_SMTEncoding_Z3.ask unsat_core all_labels _180_191 _180_190))))))))
end))))))
in (
# 272 "FStar.SMTEncoding.Solver.fst"
let process_query = (fun q -> if ((FStar_Options.split_cases ()) > 0) then begin
(
# 274 "FStar.SMTEncoding.Solver.fst"
let _87_229 = (let _180_197 = (FStar_Options.split_cases ())
in (FStar_SMTEncoding_SplitQueryCases.can_handle_query _180_197 q))
in (match (_87_229) with
| (b, cb) -> begin
if b then begin
(FStar_SMTEncoding_SplitQueryCases.handle_query cb check)
end else begin
(check q)
end
end))
end else begin
(check q)
end)
in if (FStar_Options.admit_smt_queries ()) then begin
()
end else begin
(process_query query)
end)))))
end))))

# 279 "FStar.SMTEncoding.Solver.fst"
let solve : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun use_env_msg tcenv q -> (
# 283 "FStar.SMTEncoding.Solver.fst"
let _87_233 = (let _180_216 = (let _180_215 = (let _180_214 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _180_214))
in (FStar_Util.format1 "Starting query at %s" _180_215))
in (FStar_SMTEncoding_Encode.push _180_216))
in (
# 284 "FStar.SMTEncoding.Solver.fst"
let tcenv = (FStar_TypeChecker_Env.incr_query_index tcenv)
in (
# 285 "FStar.SMTEncoding.Solver.fst"
let _87_240 = (FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv q)
in (match (_87_240) with
| (prefix, labels, qry, suffix) -> begin
(
# 286 "FStar.SMTEncoding.Solver.fst"
let pop = (fun _87_242 -> (match (()) with
| () -> begin
(let _180_221 = (let _180_220 = (let _180_219 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _180_219))
in (FStar_Util.format1 "Ending query at %s" _180_220))
in (FStar_SMTEncoding_Encode.pop _180_221))
end))
in (match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _87_249); FStar_SMTEncoding_Term.hash = _87_246; FStar_SMTEncoding_Term.freevars = _87_244}, _87_254, _87_256) -> begin
(
# 288 "FStar.SMTEncoding.Solver.fst"
let _87_259 = (pop ())
in ())
end
| _87_262 when tcenv.FStar_TypeChecker_Env.admit -> begin
(
# 289 "FStar.SMTEncoding.Solver.fst"
let _87_263 = (pop ())
in ())
end
| FStar_SMTEncoding_Term.Assume (q, _87_267, _87_269) -> begin
(
# 291 "FStar.SMTEncoding.Solver.fst"
let _87_272 = (ask_and_report_errors tcenv labels prefix qry suffix)
in (pop ()))
end
| _87_275 -> begin
(FStar_All.failwith "Impossible")
end))
end)))))

# 294 "FStar.SMTEncoding.Solver.fst"
let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = FStar_SMTEncoding_Encode.init; FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push; FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop; FStar_TypeChecker_Env.mark = FStar_SMTEncoding_Encode.mark; FStar_TypeChecker_Env.reset_mark = FStar_SMTEncoding_Encode.reset_mark; FStar_TypeChecker_Env.commit_mark = FStar_SMTEncoding_Encode.commit_mark; FStar_TypeChecker_Env.encode_modul = FStar_SMTEncoding_Encode.encode_modul; FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig; FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.is_trivial = FStar_SMTEncoding_Encode.is_trivial; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}

# 312 "FStar.SMTEncoding.Solver.fst"
let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun _87_276 -> ()); FStar_TypeChecker_Env.push = (fun _87_278 -> ()); FStar_TypeChecker_Env.pop = (fun _87_280 -> ()); FStar_TypeChecker_Env.mark = (fun _87_282 -> ()); FStar_TypeChecker_Env.reset_mark = (fun _87_284 -> ()); FStar_TypeChecker_Env.commit_mark = (fun _87_286 -> ()); FStar_TypeChecker_Env.encode_modul = (fun _87_288 _87_290 -> ()); FStar_TypeChecker_Env.encode_sig = (fun _87_292 _87_294 -> ()); FStar_TypeChecker_Env.solve = (fun _87_296 _87_298 _87_300 -> ()); FStar_TypeChecker_Env.is_trivial = (fun _87_302 _87_304 -> false); FStar_TypeChecker_Env.finish = (fun _87_306 -> ()); FStar_TypeChecker_Env.refresh = (fun _87_307 -> ())}




