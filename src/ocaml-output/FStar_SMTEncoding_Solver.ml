
open Prims

type z3_err =
(FStar_SMTEncoding_Term.error_labels * Prims.bool)


type z3_result =
(FStar_SMTEncoding_Z3.unsat_core, z3_err) FStar_Util.either


type z3_replay_result =
(FStar_SMTEncoding_Z3.unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either


let z3_result_as_replay_result = (fun _91_1 -> (match (_91_1) with
| FStar_Util.Inl (l) -> begin
FStar_Util.Inl (l)
end
| FStar_Util.Inr (r, _91_9) -> begin
FStar_Util.Inr (r)
end))


type hint_stat =
{hint : FStar_Util.hint Prims.option; replay_result : z3_replay_result; elapsed_time : Prims.int; source_location : FStar_Range.range}


let is_Mkhint_stat : hint_stat  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkhint_stat"))))


type hint_stats_t =
hint_stat Prims.list


let recorded_hints : FStar_Util.hints Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)


let replaying_hints : FStar_Util.hints Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)


let hint_stats : hint_stat Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let format_hints_file_name : Prims.string  ->  Prims.string = (fun src_filename -> (FStar_Util.format1 "%s.hints" src_filename))


let initialize_hints_db = (fun src_filename force_record -> (

let _91_20 = (FStar_ST.op_Colon_Equals hint_stats [])
in (

let _91_22 = if (FStar_Options.record_hints ()) then begin
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

let _91_29 = if (FStar_Options.hint_info ()) then begin
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

let _91_36 = if (FStar_Options.record_hints ()) then begin
(

let hints = (let _188_21 = (FStar_ST.read recorded_hints)
in (FStar_Option.get _188_21))
in (

let hints_db = (let _188_22 = (FStar_Util.digest_of_file src_filename)
in {FStar_Util.module_digest = _188_22; FStar_Util.hints = hints})
in (

let hints_file_name = (format_hints_file_name src_filename)
in (FStar_Util.write_hints hints_file_name hints_db))))
end else begin
()
end
in (

let _91_44 = if (FStar_Options.hint_info ()) then begin
(

let stats = (let _188_23 = (FStar_ST.read hint_stats)
in (FStar_All.pipe_right _188_23 FStar_List.rev))
in (FStar_All.pipe_right stats (FStar_List.iter (fun s -> (match (s.replay_result) with
| FStar_Util.Inl (_unsat_core) -> begin
(let _188_26 = (FStar_Range.string_of_range s.source_location)
in (let _188_25 = (FStar_Util.string_of_int s.elapsed_time)
in (FStar_Util.print2 "Hint-info (%s): Replay succeeded in %s milliseconds\n" _188_26 _188_25)))
end
| FStar_Util.Inr (_error) -> begin
(let _188_28 = (FStar_Range.string_of_range s.source_location)
in (let _188_27 = (FStar_Util.string_of_int s.elapsed_time)
in (FStar_Util.print2 "Hint-info (%s): Replay failed in %s milliseconds\n" _188_28 _188_27)))
end)))))
end else begin
()
end
in (

let _91_46 = (FStar_ST.op_Colon_Equals recorded_hints None)
in (

let _91_48 = (FStar_ST.op_Colon_Equals replaying_hints None)
in (FStar_ST.op_Colon_Equals hint_stats []))))))


let with_hints_db = (fun fname f -> (

let _91_52 = (initialize_hints_db fname false)
in (

let result = (f ())
in (

let _91_55 = (finalize_hints_db fname)
in result))))


let next_hint : Prims.string  ->  Prims.int  ->  FStar_Util.hint Prims.option = (fun qname qindex -> (match ((FStar_ST.read replaying_hints)) with
| Some (hints) -> begin
(FStar_Util.find_map hints (fun _91_2 -> (match (_91_2) with
| Some (hint) when ((hint.FStar_Util.hint_name = qname) && (hint.FStar_Util.hint_index = qindex)) -> begin
Some (hint)
end
| _91_65 -> begin
None
end)))
end
| _91_67 -> begin
None
end))


let record_hint : FStar_Util.hint Prims.option  ->  Prims.unit = (fun hint -> (

let hint = (match (hint) with
| None -> begin
None
end
| Some (h) -> begin
Some ((

let _91_72 = h
in {FStar_Util.hint_name = _91_72.FStar_Util.hint_name; FStar_Util.hint_index = _91_72.FStar_Util.hint_index; FStar_Util.fuel = _91_72.FStar_Util.fuel; FStar_Util.ifuel = _91_72.FStar_Util.ifuel; FStar_Util.unsat_core = _91_72.FStar_Util.unsat_core; FStar_Util.query_elapsed_time = (Prims.parse_int "0")}))
end)
in (match ((FStar_ST.read recorded_hints)) with
| Some (l) -> begin
(FStar_ST.op_Colon_Equals recorded_hints (Some ((FStar_List.append l ((hint)::[])))))
end
| _91_78 -> begin
()
end)))


let record_hint_stat : FStar_Util.hint Prims.option  ->  z3_result  ->  Prims.int  ->  FStar_Range.range  ->  Prims.unit = (fun h res time r -> (

let s = {hint = h; replay_result = (z3_result_as_replay_result res); elapsed_time = time; source_location = r}
in (let _188_50 = (let _188_49 = (FStar_ST.read hint_stats)
in (s)::_188_49)
in (FStar_ST.op_Colon_Equals hint_stats _188_50))))


let ask_and_report_errors : FStar_TypeChecker_Env.env  ->  ((FStar_SMTEncoding_Z3.label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun env all_labels prefix query suffix -> (

let _91_89 = (FStar_SMTEncoding_Z3.giveZ3 prefix)
in (

let _91_98 = (match (env.FStar_TypeChecker_Env.qname_and_index) with
| None -> begin
(FStar_All.failwith "No query name set!")
end
| Some (q, n) -> begin
(((FStar_Ident.text_of_lid q)), (n))
end)
in (match (_91_98) with
| (query_name, query_index) -> begin
(

let minimum_workable_fuel = (FStar_Util.mk_ref None)
in (

let set_minimum_workable_fuel = (fun f _91_3 -> (match (_91_3) with
| ([], _91_105) -> begin
()
end
| errs -> begin
(match ((FStar_ST.read minimum_workable_fuel)) with
| Some (_91_109) -> begin
()
end
| None -> begin
(FStar_ST.op_Colon_Equals minimum_workable_fuel (Some (((f), (errs)))))
end)
end))
in (

let with_fuel = (fun label_assumptions p _91_118 -> (match (_91_118) with
| (n, i, timeout_ms) -> begin
(let _188_98 = (let _188_88 = (let _188_73 = (let _188_72 = (FStar_Util.string_of_int n)
in (let _188_71 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _188_72 _188_71)))
in FStar_SMTEncoding_Term.Caption (_188_73))
in (let _188_87 = (let _188_86 = (let _188_78 = (let _188_77 = (let _188_76 = (let _188_75 = (FStar_SMTEncoding_Term.mkApp (("MaxFuel"), ([])))
in (let _188_74 = (FStar_SMTEncoding_Term.n_fuel n)
in ((_188_75), (_188_74))))
in (FStar_SMTEncoding_Term.mkEq _188_76))
in ((_188_77), (None), (None)))
in FStar_SMTEncoding_Term.Assume (_188_78))
in (let _188_85 = (let _188_84 = (let _188_83 = (let _188_82 = (let _188_81 = (let _188_80 = (FStar_SMTEncoding_Term.mkApp (("MaxIFuel"), ([])))
in (let _188_79 = (FStar_SMTEncoding_Term.n_fuel i)
in ((_188_80), (_188_79))))
in (FStar_SMTEncoding_Term.mkEq _188_81))
in ((_188_82), (None), (None)))
in FStar_SMTEncoding_Term.Assume (_188_83))
in (_188_84)::(p)::[])
in (_188_86)::_188_85))
in (_188_88)::_188_87))
in (let _188_97 = (let _188_96 = (let _188_95 = (let _188_91 = (let _188_90 = (let _188_89 = (FStar_Util.string_of_int timeout_ms)
in (("timeout"), (_188_89)))
in FStar_SMTEncoding_Term.SetOption (_188_90))
in (_188_91)::[])
in (let _188_94 = (let _188_93 = (let _188_92 = if (FStar_Options.record_hints ()) then begin
(FStar_SMTEncoding_Term.GetUnsatCore)::[]
end else begin
[]
end
in (FStar_List.append _188_92 suffix))
in (FStar_List.append ((FStar_SMTEncoding_Term.CheckSat)::[]) _188_93))
in (FStar_List.append _188_95 _188_94)))
in (FStar_List.append label_assumptions _188_96))
in (FStar_List.append _188_98 _188_97)))
end))
in (

let check = (fun p -> (

let default_timeout = ((FStar_Options.z3_timeout ()) * (Prims.parse_int "1000"))
in (

let default_initial_config = (let _188_102 = (FStar_Options.initial_fuel ())
in (let _188_101 = (FStar_Options.initial_ifuel ())
in ((_188_102), (_188_101), (default_timeout))))
in (

let hint_opt = (next_hint query_name query_index)
in (

let _91_132 = (match (hint_opt) with
| None -> begin
((None), (default_initial_config))
end
| Some (hint) -> begin
(

let _91_129 = if (FStar_Option.isSome hint.FStar_Util.unsat_core) then begin
((hint.FStar_Util.unsat_core), (default_timeout))
end else begin
((None), (((Prims.parse_int "60") * (Prims.parse_int "1000"))))
end
in (match (_91_129) with
| (core, timeout) -> begin
((core), (((hint.FStar_Util.fuel), (hint.FStar_Util.ifuel), (timeout))))
end))
end)
in (match (_91_132) with
| (unsat_core, initial_config) -> begin
(

let alt_configs = (let _188_123 = (let _188_122 = if ((default_initial_config <> initial_config) || (FStar_Option.isSome unsat_core)) then begin
(default_initial_config)::[]
end else begin
[]
end
in (let _188_121 = (let _188_120 = if ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ())) then begin
(let _188_105 = (let _188_104 = (FStar_Options.initial_fuel ())
in (let _188_103 = (FStar_Options.max_ifuel ())
in ((_188_104), (_188_103), (default_timeout))))
in (_188_105)::[])
end else begin
[]
end
in (let _188_119 = (let _188_118 = if (((FStar_Options.max_fuel ()) / (Prims.parse_int "2")) > (FStar_Options.initial_fuel ())) then begin
(let _188_108 = (let _188_107 = ((FStar_Options.max_fuel ()) / (Prims.parse_int "2"))
in (let _188_106 = (FStar_Options.max_ifuel ())
in ((_188_107), (_188_106), (default_timeout))))
in (_188_108)::[])
end else begin
[]
end
in (let _188_117 = (let _188_116 = if (((FStar_Options.max_fuel ()) > (FStar_Options.initial_fuel ())) && ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ()))) then begin
(let _188_111 = (let _188_110 = (FStar_Options.max_fuel ())
in (let _188_109 = (FStar_Options.max_ifuel ())
in ((_188_110), (_188_109), (default_timeout))))
in (_188_111)::[])
end else begin
[]
end
in (let _188_115 = (let _188_114 = if ((FStar_Options.min_fuel ()) < (FStar_Options.initial_fuel ())) then begin
(let _188_113 = (let _188_112 = (FStar_Options.min_fuel ())
in ((_188_112), ((Prims.parse_int "1")), (default_timeout)))
in (_188_113)::[])
end else begin
[]
end
in (_188_114)::[])
in (_188_116)::_188_115))
in (_188_118)::_188_117))
in (_188_120)::_188_119))
in (_188_122)::_188_121))
in (FStar_List.flatten _188_123))
in (

let report = (fun p errs -> (

let errs = if ((FStar_Options.detail_errors ()) && ((FStar_Options.n_cores ()) = (Prims.parse_int "1"))) then begin
(

let _91_144 = (match ((FStar_ST.read minimum_workable_fuel)) with
| Some (f, errs) -> begin
((f), (errs))
end
| None -> begin
(let _188_129 = (let _188_128 = (FStar_Options.min_fuel ())
in ((_188_128), ((Prims.parse_int "1")), (default_timeout)))
in ((_188_129), (errs)))
end)
in (match (_91_144) with
| (min_fuel, potential_errors) -> begin
(

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref None)
in (

let _91_149 = (let _188_133 = (with_fuel label_assumptions p min_fuel)
in (FStar_SMTEncoding_Z3.ask None all_labels _188_133 (fun r -> (FStar_ST.op_Colon_Equals res (Some (r))))))
in (let _188_134 = (FStar_ST.read res)
in (FStar_Option.get _188_134)))))
in (let _188_135 = (FStar_SMTEncoding_ErrorReporting.detail_errors all_labels (Prims.fst errs) ask_z3)
in ((_188_135), (false))))
end))
end else begin
errs
end
in (

let errs = (match (errs) with
| ([], true) -> begin
(((((((""), (FStar_SMTEncoding_Term.Term_sort))), ("Timeout: Unknown assertion failed"), (FStar_Range.dummyRange)))::[]), (true))
end
| ([], false) -> begin
(((((((""), (FStar_SMTEncoding_Term.Term_sort))), ("Unknown assertion failed"), (FStar_Range.dummyRange)))::[]), (false))
end
| _91_159 -> begin
errs
end)
in (

let _91_161 = (record_hint None)
in (

let _91_163 = if (FStar_Options.print_fuels ()) then begin
(let _188_141 = (let _188_136 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _188_136))
in (let _188_140 = (let _188_137 = (FStar_Options.max_fuel ())
in (FStar_All.pipe_right _188_137 FStar_Util.string_of_int))
in (let _188_139 = (let _188_138 = (FStar_Options.max_ifuel ())
in (FStar_All.pipe_right _188_138 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _188_141 _188_140 _188_139))))
end else begin
()
end
in (

let _91_170 = (let _188_143 = (FStar_All.pipe_right (Prims.fst errs) (FStar_List.map (fun _91_169 -> (match (_91_169) with
| (_91_166, x, y) -> begin
((x), (y))
end))))
in (FStar_TypeChecker_Errors.add_errors env _188_143))
in if (FStar_Options.detail_errors ()) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Detailed error report follows\n")))
end else begin
()
end))))))
in (

let use_errors = (fun errs result -> (match (((errs), (result))) with
| ((([], _), _)) | ((_, FStar_Util.Inl (_))) -> begin
result
end
| (_91_189, FStar_Util.Inr (_91_191)) -> begin
FStar_Util.Inr (errs)
end))
in (

let rec try_alt_configs = (fun prev_f p errs cfgs -> (

let _91_200 = (set_minimum_workable_fuel prev_f errs)
in (match (cfgs) with
| [] -> begin
(report p errs)
end
| (mi)::[] -> begin
(match (errs) with
| ([], _91_207) -> begin
(let _188_161 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask None all_labels _188_161 (cb false mi p [])))
end
| _91_210 -> begin
(

let _91_211 = (set_minimum_workable_fuel prev_f errs)
in (report p errs))
end)
end
| (mi)::tl -> begin
(let _188_163 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask None all_labels _188_163 (fun _91_218 -> (match (_91_218) with
| (result, elapsed_time) -> begin
(cb false mi p tl (((use_errors errs result)), (elapsed_time)))
end))))
end)))
and cb = (fun used_hint _91_223 p alt _91_228 -> (match (((_91_223), (_91_228))) with
| ((prev_fuel, prev_ifuel, timeout), (result, elapsed_time)) -> begin
(

let _91_231 = if used_hint then begin
(

let _91_229 = (FStar_SMTEncoding_Z3.refresh ())
in (let _188_169 = (FStar_TypeChecker_Env.get_range env)
in (record_hint_stat hint_opt result elapsed_time _188_169)))
end else begin
()
end
in (

let at_log_file = (fun _91_234 -> (match (()) with
| () -> begin
if (FStar_Options.log_queries ()) then begin
(let _188_172 = (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.log_file_name ())
in (Prims.strcat "@" _188_172))
end else begin
""
end
end))
in (

let query_info = (fun tag -> (let _188_190 = (let _188_189 = (let _188_175 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _188_175))
in (let _188_188 = (let _188_187 = (at_log_file ())
in (let _188_186 = (let _188_185 = (let _188_184 = (FStar_Util.string_of_int query_index)
in (let _188_183 = (let _188_182 = (let _188_181 = (let _188_180 = (FStar_Util.string_of_int elapsed_time)
in (let _188_179 = (let _188_178 = (FStar_Util.string_of_int prev_fuel)
in (let _188_177 = (let _188_176 = (FStar_Util.string_of_int prev_ifuel)
in (_188_176)::[])
in (_188_178)::_188_177))
in (_188_180)::_188_179))
in (if used_hint then begin
" (with hint)"
end else begin
""
end)::_188_181)
in (tag)::_188_182)
in (_188_184)::_188_183))
in (query_name)::_188_185)
in (_188_187)::_188_186))
in (_188_189)::_188_188))
in (FStar_Util.print "(%s%s)\n\tQuery (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s\n" _188_190)))
in (match (result) with
| FStar_Util.Inl (unsat_core) -> begin
(

let _91_240 = if (not (used_hint)) then begin
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

let _91_244 = if ((FStar_Options.print_fuels ()) || (FStar_Options.hint_info ())) then begin
(query_info "failed")
end else begin
()
end
in (try_alt_configs ((prev_fuel), (prev_ifuel), (timeout)) p errs alt))
end))))
end))
in (

let _91_246 = if (FStar_Option.isSome unsat_core) then begin
(FStar_SMTEncoding_Z3.refresh ())
end else begin
()
end
in (let _188_193 = (with_fuel [] p initial_config)
in (let _188_192 = (let _188_191 = (FStar_Option.isSome unsat_core)
in (cb _188_191 initial_config p alt_configs))
in (FStar_SMTEncoding_Z3.ask unsat_core all_labels _188_193 _188_192))))))))
end))))))
in (

let process_query = (fun q -> if ((FStar_Options.split_cases ()) > (Prims.parse_int "0")) then begin
(

let _91_252 = (let _188_199 = (FStar_Options.split_cases ())
in (FStar_SMTEncoding_SplitQueryCases.can_handle_query _188_199 q))
in (match (_91_252) with
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

let _91_256 = (let _188_218 = (let _188_217 = (let _188_216 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _188_216))
in (FStar_Util.format1 "Starting query at %s" _188_217))
in (FStar_SMTEncoding_Encode.push _188_218))
in (

let tcenv = (FStar_TypeChecker_Env.incr_query_index tcenv)
in (

let _91_263 = (FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv q)
in (match (_91_263) with
| (prefix, labels, qry, suffix) -> begin
(

let pop = (fun _91_265 -> (match (()) with
| () -> begin
(let _188_223 = (let _188_222 = (let _188_221 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _188_221))
in (FStar_Util.format1 "Ending query at %s" _188_222))
in (FStar_SMTEncoding_Encode.pop _188_223))
end))
in (match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _91_272); FStar_SMTEncoding_Term.hash = _91_269; FStar_SMTEncoding_Term.freevars = _91_267}, _91_277, _91_279) -> begin
(

let _91_282 = (pop ())
in ())
end
| _91_285 when tcenv.FStar_TypeChecker_Env.admit -> begin
(

let _91_286 = (pop ())
in ())
end
| FStar_SMTEncoding_Term.Assume (q, _91_290, _91_292) -> begin
(

let _91_295 = (ask_and_report_errors tcenv labels prefix qry suffix)
in (pop ()))
end
| _91_298 -> begin
(FStar_All.failwith "Impossible")
end))
end)))))


let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = FStar_SMTEncoding_Encode.init; FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push; FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop; FStar_TypeChecker_Env.mark = FStar_SMTEncoding_Encode.mark; FStar_TypeChecker_Env.reset_mark = FStar_SMTEncoding_Encode.reset_mark; FStar_TypeChecker_Env.commit_mark = FStar_SMTEncoding_Encode.commit_mark; FStar_TypeChecker_Env.encode_modul = FStar_SMTEncoding_Encode.encode_modul; FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig; FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.is_trivial = FStar_SMTEncoding_Encode.is_trivial; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}


let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun _91_299 -> ()); FStar_TypeChecker_Env.push = (fun _91_301 -> ()); FStar_TypeChecker_Env.pop = (fun _91_303 -> ()); FStar_TypeChecker_Env.mark = (fun _91_305 -> ()); FStar_TypeChecker_Env.reset_mark = (fun _91_307 -> ()); FStar_TypeChecker_Env.commit_mark = (fun _91_309 -> ()); FStar_TypeChecker_Env.encode_modul = (fun _91_311 _91_313 -> ()); FStar_TypeChecker_Env.encode_sig = (fun _91_315 _91_317 -> ()); FStar_TypeChecker_Env.solve = (fun _91_319 _91_321 _91_323 -> ()); FStar_TypeChecker_Env.is_trivial = (fun _91_325 _91_327 -> false); FStar_TypeChecker_Env.finish = (fun _91_329 -> ()); FStar_TypeChecker_Env.refresh = (fun _91_330 -> ())}




