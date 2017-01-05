
open Prims

type z3_err =
(FStar_SMTEncoding_Term.error_labels * FStar_SMTEncoding_Z3.error_kind)


type z3_result =
(FStar_SMTEncoding_Z3.unsat_core, z3_err) FStar_Util.either


type z3_replay_result =
(FStar_SMTEncoding_Z3.unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either


let z3_result_as_replay_result = (fun _92_1 -> (match (_92_1) with
| FStar_Util.Inl (l) -> begin
FStar_Util.Inl (l)
end
| FStar_Util.Inr (r, _92_9) -> begin
FStar_Util.Inr (r)
end))


type hint_stat =
{hint : FStar_Util.hint Prims.option; replay_result : z3_replay_result; elapsed_time : Prims.int; source_location : FStar_Range.range}


let is_Mkhint_stat : hint_stat  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkhint_stat"))))


type hint_stats_t =
hint_stat Prims.list


let recorded_hints : FStar_Util.hints Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)


let replaying_hints : FStar_Util.hints Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)


let hint_stats : hint_stat Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let format_hints_file_name : Prims.string  ->  Prims.string = (fun src_filename -> (FStar_Util.format1 "%s.hints" src_filename))


let initialize_hints_db = (fun src_filename force_record -> (

let _92_20 = (FStar_ST.op_Colon_Equals hint_stats [])
in (

let _92_22 = if (FStar_Options.record_hints ()) then begin
(FStar_ST.op_Colon_Equals recorded_hints (Some ([])))
end else begin
()
end
in if (FStar_Options.use_hints ()) then begin
(

let norm_src_filename = (FStar_Util.normalize_file_path src_filename)
in (

let val_filename = (format_hints_file_name norm_src_filename)
in (match ((FStar_Util.read_hints val_filename)) with
| Some (hints) -> begin
(

let expected_digest = (FStar_Util.digest_of_file norm_src_filename)
in (

let _92_29 = if (FStar_Options.hint_info ()) then begin
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


let finalize_hints_db : Prims.string  ->  Prims.unit = (fun src_filename -> (

let _92_36 = if (FStar_Options.record_hints ()) then begin
(

let hints = (let _191_21 = (FStar_ST.read recorded_hints)
in (FStar_Option.get _191_21))
in (

let hints_db = (let _191_22 = (FStar_Util.digest_of_file src_filename)
in {FStar_Util.module_digest = _191_22; FStar_Util.hints = hints})
in (

let hints_file_name = (format_hints_file_name src_filename)
in (FStar_Util.write_hints hints_file_name hints_db))))
end else begin
()
end
in (

let _92_44 = if (FStar_Options.hint_info ()) then begin
(

let stats = (let _191_23 = (FStar_ST.read hint_stats)
in (FStar_All.pipe_right _191_23 FStar_List.rev))
in (FStar_All.pipe_right stats (FStar_List.iter (fun s -> (match (s.replay_result) with
| FStar_Util.Inl (_unsat_core) -> begin
(let _191_26 = (FStar_Range.string_of_range s.source_location)
in (let _191_25 = (FStar_Util.string_of_int s.elapsed_time)
in (FStar_Util.print2 "Hint-info (%s): Replay succeeded in %s milliseconds\n" _191_26 _191_25)))
end
| FStar_Util.Inr (_error) -> begin
(let _191_28 = (FStar_Range.string_of_range s.source_location)
in (let _191_27 = (FStar_Util.string_of_int s.elapsed_time)
in (FStar_Util.print2 "Hint-info (%s): Replay failed in %s milliseconds\n" _191_28 _191_27)))
end)))))
end else begin
()
end
in (

let _92_46 = (FStar_ST.op_Colon_Equals recorded_hints None)
in (

let _92_48 = (FStar_ST.op_Colon_Equals replaying_hints None)
in (FStar_ST.op_Colon_Equals hint_stats []))))))


let with_hints_db = (fun fname f -> (

let _92_52 = (initialize_hints_db fname false)
in (

let result = (f ())
in (

let _92_55 = (finalize_hints_db fname)
in result))))


let next_hint : Prims.string  ->  Prims.int  ->  FStar_Util.hint Prims.option = (fun qname qindex -> (match ((FStar_ST.read replaying_hints)) with
| Some (hints) -> begin
(FStar_Util.find_map hints (fun _92_2 -> (match (_92_2) with
| Some (hint) when ((hint.FStar_Util.hint_name = qname) && (hint.FStar_Util.hint_index = qindex)) -> begin
Some (hint)
end
| _92_65 -> begin
None
end)))
end
| _92_67 -> begin
None
end))


let record_hint : FStar_Util.hint Prims.option  ->  Prims.unit = (fun hint -> (

let hint = (match (hint) with
| None -> begin
None
end
| Some (h) -> begin
Some ((

let _92_72 = h
in {FStar_Util.hint_name = _92_72.FStar_Util.hint_name; FStar_Util.hint_index = _92_72.FStar_Util.hint_index; FStar_Util.fuel = _92_72.FStar_Util.fuel; FStar_Util.ifuel = _92_72.FStar_Util.ifuel; FStar_Util.unsat_core = _92_72.FStar_Util.unsat_core; FStar_Util.query_elapsed_time = (Prims.parse_int "0")}))
end)
in (match ((FStar_ST.read recorded_hints)) with
| Some (l) -> begin
(FStar_ST.op_Colon_Equals recorded_hints (Some ((FStar_List.append l ((hint)::[])))))
end
| _92_78 -> begin
()
end)))


let record_hint_stat : FStar_Util.hint Prims.option  ->  z3_result  ->  Prims.int  ->  FStar_Range.range  ->  Prims.unit = (fun h res time r -> (

let s = {hint = h; replay_result = (z3_result_as_replay_result res); elapsed_time = time; source_location = r}
in (let _191_50 = (let _191_49 = (FStar_ST.read hint_stats)
in (s)::_191_49)
in (FStar_ST.op_Colon_Equals hint_stats _191_50))))


let ask_and_report_errors : FStar_TypeChecker_Env.env  ->  ((FStar_SMTEncoding_Z3.label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun env all_labels prefix query suffix -> (

let _92_89 = (FStar_SMTEncoding_Z3.giveZ3 prefix)
in (

let _92_98 = (match (env.FStar_TypeChecker_Env.qname_and_index) with
| None -> begin
(failwith "No query name set!")
end
| Some (q, n) -> begin
(((FStar_Ident.text_of_lid q)), (n))
end)
in (match (_92_98) with
| (query_name, query_index) -> begin
(

let minimum_workable_fuel = (FStar_Util.mk_ref None)
in (

let set_minimum_workable_fuel = (fun f _92_3 -> (match (_92_3) with
| ([], _92_105) -> begin
()
end
| errs -> begin
(match ((FStar_ST.read minimum_workable_fuel)) with
| Some (_92_109) -> begin
()
end
| None -> begin
(FStar_ST.op_Colon_Equals minimum_workable_fuel (Some (((f), (errs)))))
end)
end))
in (

let with_fuel = (fun label_assumptions p _92_118 -> (match (_92_118) with
| (n, i, rlimit) -> begin
(let _191_98 = (let _191_88 = (let _191_73 = (let _191_72 = (FStar_Util.string_of_int n)
in (let _191_71 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _191_72 _191_71)))
in FStar_SMTEncoding_Term.Caption (_191_73))
in (let _191_87 = (let _191_86 = (let _191_78 = (let _191_77 = (let _191_76 = (let _191_75 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (let _191_74 = (FStar_SMTEncoding_Term.n_fuel n)
in ((_191_75), (_191_74))))
in (FStar_SMTEncoding_Util.mkEq _191_76))
in ((_191_77), (None), (None)))
in FStar_SMTEncoding_Term.Assume (_191_78))
in (let _191_85 = (let _191_84 = (let _191_83 = (let _191_82 = (let _191_81 = (let _191_80 = (FStar_SMTEncoding_Util.mkApp (("MaxIFuel"), ([])))
in (let _191_79 = (FStar_SMTEncoding_Term.n_fuel i)
in ((_191_80), (_191_79))))
in (FStar_SMTEncoding_Util.mkEq _191_81))
in ((_191_82), (None), (None)))
in FStar_SMTEncoding_Term.Assume (_191_83))
in (_191_84)::(p)::[])
in (_191_86)::_191_85))
in (_191_88)::_191_87))
in (let _191_97 = (let _191_96 = (let _191_95 = (let _191_91 = (let _191_90 = (let _191_89 = (FStar_Util.string_of_int rlimit)
in (("rlimit"), (_191_89)))
in FStar_SMTEncoding_Term.SetOption (_191_90))
in (_191_91)::[])
in (let _191_94 = (let _191_93 = (let _191_92 = if (FStar_Options.record_hints ()) then begin
(FStar_SMTEncoding_Term.GetUnsatCore)::[]
end else begin
[]
end
in (FStar_List.append _191_92 suffix))
in (FStar_List.append ((FStar_SMTEncoding_Term.CheckSat)::[]) _191_93))
in (FStar_List.append _191_95 _191_94)))
in (FStar_List.append label_assumptions _191_96))
in (FStar_List.append _191_98 _191_97)))
end))
in (

let check = (fun p -> (

let rlimit = ((FStar_Options.z3_rlimit ()) * (Prims.parse_int "544656"))
in (

let default_initial_config = (let _191_102 = (FStar_Options.initial_fuel ())
in (let _191_101 = (FStar_Options.initial_ifuel ())
in ((_191_102), (_191_101), (rlimit))))
in (

let hint_opt = (next_hint query_name query_index)
in (

let _92_132 = (match (hint_opt) with
| None -> begin
((None), (default_initial_config))
end
| Some (hint) -> begin
(

let _92_129 = if (FStar_Option.isSome hint.FStar_Util.unsat_core) then begin
((hint.FStar_Util.unsat_core), (rlimit))
end else begin
((None), (((Prims.parse_int "60") * (Prims.parse_int "544656"))))
end
in (match (_92_129) with
| (core, timeout) -> begin
((core), (((hint.FStar_Util.fuel), (hint.FStar_Util.ifuel), (timeout))))
end))
end)
in (match (_92_132) with
| (unsat_core, initial_config) -> begin
(

let alt_configs = (let _191_123 = (let _191_122 = if ((default_initial_config <> initial_config) || (FStar_Option.isSome unsat_core)) then begin
(default_initial_config)::[]
end else begin
[]
end
in (let _191_121 = (let _191_120 = if ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ())) then begin
(let _191_105 = (let _191_104 = (FStar_Options.initial_fuel ())
in (let _191_103 = (FStar_Options.max_ifuel ())
in ((_191_104), (_191_103), (rlimit))))
in (_191_105)::[])
end else begin
[]
end
in (let _191_119 = (let _191_118 = if (((FStar_Options.max_fuel ()) / (Prims.parse_int "2")) > (FStar_Options.initial_fuel ())) then begin
(let _191_108 = (let _191_107 = ((FStar_Options.max_fuel ()) / (Prims.parse_int "2"))
in (let _191_106 = (FStar_Options.max_ifuel ())
in ((_191_107), (_191_106), (rlimit))))
in (_191_108)::[])
end else begin
[]
end
in (let _191_117 = (let _191_116 = if (((FStar_Options.max_fuel ()) > (FStar_Options.initial_fuel ())) && ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ()))) then begin
(let _191_111 = (let _191_110 = (FStar_Options.max_fuel ())
in (let _191_109 = (FStar_Options.max_ifuel ())
in ((_191_110), (_191_109), (rlimit))))
in (_191_111)::[])
end else begin
[]
end
in (let _191_115 = (let _191_114 = if ((FStar_Options.min_fuel ()) < (FStar_Options.initial_fuel ())) then begin
(let _191_113 = (let _191_112 = (FStar_Options.min_fuel ())
in ((_191_112), ((Prims.parse_int "1")), (rlimit)))
in (_191_113)::[])
end else begin
[]
end
in (_191_114)::[])
in (_191_116)::_191_115))
in (_191_118)::_191_117))
in (_191_120)::_191_119))
in (_191_122)::_191_121))
in (FStar_List.flatten _191_123))
in (

let report = (fun p errs -> (

let errs = if ((FStar_Options.detail_errors ()) && ((FStar_Options.n_cores ()) = (Prims.parse_int "1"))) then begin
(

let _92_144 = (match ((FStar_ST.read minimum_workable_fuel)) with
| Some (f, errs) -> begin
((f), (errs))
end
| None -> begin
(let _191_129 = (let _191_128 = (FStar_Options.min_fuel ())
in ((_191_128), ((Prims.parse_int "1")), (rlimit)))
in ((_191_129), (errs)))
end)
in (match (_92_144) with
| (min_fuel, potential_errors) -> begin
(

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref None)
in (

let _92_149 = (let _191_133 = (with_fuel label_assumptions p min_fuel)
in (FStar_SMTEncoding_Z3.ask None all_labels _191_133 (fun r -> (FStar_ST.op_Colon_Equals res (Some (r))))))
in (let _191_134 = (FStar_ST.read res)
in (FStar_Option.get _191_134)))))
in (let _191_135 = (FStar_SMTEncoding_ErrorReporting.detail_errors env all_labels ask_z3)
in ((_191_135), (FStar_SMTEncoding_Z3.Default))))
end))
end else begin
(match (errs) with
| ([], FStar_SMTEncoding_Z3.Timeout) -> begin
(((((((""), (FStar_SMTEncoding_Term.Term_sort))), ("Timeout: Unknown assertion failed"), (FStar_Range.dummyRange)))::[]), ((Prims.snd errs)))
end
| ([], FStar_SMTEncoding_Z3.Default) -> begin
(((((((""), (FStar_SMTEncoding_Term.Term_sort))), ("Unknown assertion failed"), (FStar_Range.dummyRange)))::[]), ((Prims.snd errs)))
end
| (_92_158, FStar_SMTEncoding_Z3.Kill) -> begin
(((((((""), (FStar_SMTEncoding_Term.Term_sort))), ("Killed: Unknown assertion failed"), (FStar_Range.dummyRange)))::[]), ((Prims.snd errs)))
end
| _92_162 -> begin
errs
end)
end
in (

let _92_164 = (record_hint None)
in (

let _92_166 = if (FStar_Options.print_fuels ()) then begin
(let _191_141 = (let _191_136 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _191_136))
in (let _191_140 = (let _191_137 = (FStar_Options.max_fuel ())
in (FStar_All.pipe_right _191_137 FStar_Util.string_of_int))
in (let _191_139 = (let _191_138 = (FStar_Options.max_ifuel ())
in (FStar_All.pipe_right _191_138 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _191_141 _191_140 _191_139))))
end else begin
()
end
in (let _191_143 = (FStar_All.pipe_right (Prims.fst errs) (FStar_List.map (fun _92_172 -> (match (_92_172) with
| (_92_169, x, y) -> begin
((x), (y))
end))))
in (FStar_TypeChecker_Errors.add_errors env _191_143))))))
in (

let use_errors = (fun errs result -> (match (((errs), (result))) with
| ((([], _), _)) | ((_, FStar_Util.Inl (_))) -> begin
result
end
| (_92_190, FStar_Util.Inr (_92_192)) -> begin
FStar_Util.Inr (errs)
end))
in (

let rec try_alt_configs = (fun prev_f p errs cfgs -> (

let _92_201 = (set_minimum_workable_fuel prev_f errs)
in (match (((cfgs), ((Prims.snd errs)))) with
| (([], _)) | ((_, FStar_SMTEncoding_Z3.Kill)) -> begin
(report p errs)
end
| ((mi)::[], _92_214) -> begin
(match (errs) with
| ([], _92_218) -> begin
(let _191_161 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask None all_labels _191_161 (cb false mi p [])))
end
| _92_221 -> begin
(

let _92_222 = (set_minimum_workable_fuel prev_f errs)
in (report p errs))
end)
end
| ((mi)::tl, _92_228) -> begin
(let _191_163 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask None all_labels _191_163 (fun _92_232 -> (match (_92_232) with
| (result, elapsed_time) -> begin
(cb false mi p tl (((use_errors errs result)), (elapsed_time)))
end))))
end)))
and cb = (fun used_hint _92_237 p alt _92_242 -> (match (((_92_237), (_92_242))) with
| ((prev_fuel, prev_ifuel, timeout), (result, elapsed_time)) -> begin
(

let _92_245 = if used_hint then begin
(

let _92_243 = (FStar_SMTEncoding_Z3.refresh ())
in (let _191_169 = (FStar_TypeChecker_Env.get_range env)
in (record_hint_stat hint_opt result elapsed_time _191_169)))
end else begin
()
end
in (

let _92_247 = if ((FStar_Options.z3_refresh ()) || (FStar_Options.print_z3_statistics ())) then begin
(FStar_SMTEncoding_Z3.refresh ())
end else begin
()
end
in (

let query_info = (fun tag -> (let _191_187 = (let _191_186 = (let _191_172 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _191_172))
in (let _191_185 = (let _191_184 = (FStar_SMTEncoding_Z3.at_log_file ())
in (let _191_183 = (let _191_182 = (let _191_181 = (FStar_Util.string_of_int query_index)
in (let _191_180 = (let _191_179 = (let _191_178 = (let _191_177 = (FStar_Util.string_of_int elapsed_time)
in (let _191_176 = (let _191_175 = (FStar_Util.string_of_int prev_fuel)
in (let _191_174 = (let _191_173 = (FStar_Util.string_of_int prev_ifuel)
in (_191_173)::[])
in (_191_175)::_191_174))
in (_191_177)::_191_176))
in (if used_hint then begin
" (with hint)"
end else begin
""
end)::_191_178)
in (tag)::_191_179)
in (_191_181)::_191_180))
in (query_name)::_191_182)
in (_191_184)::_191_183))
in (_191_186)::_191_185))
in (FStar_Util.print "(%s%s)\n\tQuery (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s\n" _191_187)))
in (match (result) with
| FStar_Util.Inl (unsat_core) -> begin
(

let _92_254 = if (not (used_hint)) then begin
(

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

let _92_258 = if ((FStar_Options.print_fuels ()) || (FStar_Options.hint_info ())) then begin
(query_info "failed")
end else begin
()
end
in (try_alt_configs ((prev_fuel), (prev_ifuel), (timeout)) p errs alt))
end))))
end))
in (

let _92_260 = if (FStar_Option.isSome unsat_core) then begin
(FStar_SMTEncoding_Z3.refresh ())
end else begin
()
end
in (let _191_190 = (with_fuel [] p initial_config)
in (let _191_189 = (let _191_188 = (FStar_Option.isSome unsat_core)
in (cb _191_188 initial_config p alt_configs))
in (FStar_SMTEncoding_Z3.ask unsat_core all_labels _191_190 _191_189))))))))
end))))))
in (

let process_query = (fun q -> if ((FStar_Options.split_cases ()) > (Prims.parse_int "0")) then begin
(

let _92_266 = (let _191_196 = (FStar_Options.split_cases ())
in (FStar_SMTEncoding_SplitQueryCases.can_handle_query _191_196 q))
in (match (_92_266) with
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


let solve : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun use_env_msg tcenv q -> (

let _92_270 = (let _191_215 = (let _191_214 = (let _191_213 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _191_213))
in (FStar_Util.format1 "Starting query at %s" _191_214))
in (FStar_SMTEncoding_Encode.push _191_215))
in (

let tcenv = (FStar_TypeChecker_Env.incr_query_index tcenv)
in (

let _92_277 = (FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv q)
in (match (_92_277) with
| (prefix, labels, qry, suffix) -> begin
(

let pop = (fun _92_279 -> (match (()) with
| () -> begin
(let _191_220 = (let _191_219 = (let _191_218 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _191_218))
in (FStar_Util.format1 "Ending query at %s" _191_219))
in (FStar_SMTEncoding_Encode.pop _191_220))
end))
in (match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _92_286); FStar_SMTEncoding_Term.freevars = _92_283; FStar_SMTEncoding_Term.rng = _92_281}, _92_291, _92_293) -> begin
(

let _92_296 = (pop ())
in ())
end
| _92_299 when tcenv.FStar_TypeChecker_Env.admit -> begin
(

let _92_300 = (pop ())
in ())
end
| FStar_SMTEncoding_Term.Assume (q, _92_304, _92_306) -> begin
(

let _92_309 = (ask_and_report_errors tcenv labels prefix qry suffix)
in (pop ()))
end
| _92_312 -> begin
(failwith "Impossible")
end))
end)))))


let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = FStar_SMTEncoding_Encode.init; FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push; FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop; FStar_TypeChecker_Env.mark = FStar_SMTEncoding_Encode.mark; FStar_TypeChecker_Env.reset_mark = FStar_SMTEncoding_Encode.reset_mark; FStar_TypeChecker_Env.commit_mark = FStar_SMTEncoding_Encode.commit_mark; FStar_TypeChecker_Env.encode_modul = FStar_SMTEncoding_Encode.encode_modul; FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig; FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.is_trivial = FStar_SMTEncoding_Encode.is_trivial; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}


let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun _92_313 -> ()); FStar_TypeChecker_Env.push = (fun _92_315 -> ()); FStar_TypeChecker_Env.pop = (fun _92_317 -> ()); FStar_TypeChecker_Env.mark = (fun _92_319 -> ()); FStar_TypeChecker_Env.reset_mark = (fun _92_321 -> ()); FStar_TypeChecker_Env.commit_mark = (fun _92_323 -> ()); FStar_TypeChecker_Env.encode_modul = (fun _92_325 _92_327 -> ()); FStar_TypeChecker_Env.encode_sig = (fun _92_329 _92_331 -> ()); FStar_TypeChecker_Env.solve = (fun _92_333 _92_335 _92_337 -> ()); FStar_TypeChecker_Env.is_trivial = (fun _92_339 _92_341 -> false); FStar_TypeChecker_Env.finish = (fun _92_343 -> ()); FStar_TypeChecker_Env.refresh = (fun _92_344 -> ())}




