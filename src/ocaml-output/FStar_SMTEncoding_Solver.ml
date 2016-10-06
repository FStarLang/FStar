
open Prims

type z3_err =
(FStar_SMTEncoding_Term.error_labels * Prims.bool)


type z3_result =
(FStar_SMTEncoding_Z3.unsat_core, z3_err) FStar_Util.either


type z3_replay_result =
(FStar_SMTEncoding_Z3.unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either


let z3_result_as_replay_result = (fun _88_1 -> (match (_88_1) with
| FStar_Util.Inl (l) -> begin
FStar_Util.Inl (l)
end
| FStar_Util.Inr (r, _88_9) -> begin
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

let _88_20 = (FStar_ST.op_Colon_Equals hint_stats [])
in (

let _88_22 = if (FStar_Options.record_hints ()) then begin
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

let _88_29 = if (FStar_Options.hint_info ()) then begin
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

let _88_36 = if (FStar_Options.record_hints ()) then begin
(

let hints = (let _182_21 = (FStar_ST.read recorded_hints)
in (FStar_Option.get _182_21))
in (

let hints_db = (let _182_22 = (FStar_Util.digest_of_file src_filename)
in {FStar_Util.module_digest = _182_22; FStar_Util.hints = hints})
in (

let hints_file_name = (format_hints_file_name src_filename)
in (FStar_Util.write_hints hints_file_name hints_db))))
end else begin
()
end
in (

let _88_44 = if (FStar_Options.hint_info ()) then begin
(

let stats = (let _182_23 = (FStar_ST.read hint_stats)
in (FStar_All.pipe_right _182_23 FStar_List.rev))
in (FStar_All.pipe_right stats (FStar_List.iter (fun s -> (match (s.replay_result) with
| FStar_Util.Inl (_unsat_core) -> begin
(let _182_26 = (FStar_Range.string_of_range s.source_location)
in (let _182_25 = (FStar_Util.string_of_int s.elapsed_time)
in (FStar_Util.print2 "Hint-info (%s): Replay succeeded in %s milliseconds\n" _182_26 _182_25)))
end
| FStar_Util.Inr (_error) -> begin
(let _182_28 = (FStar_Range.string_of_range s.source_location)
in (let _182_27 = (FStar_Util.string_of_int s.elapsed_time)
in (FStar_Util.print2 "Hint-info (%s): Replay failed in %s milliseconds\n" _182_28 _182_27)))
end)))))
end else begin
()
end
in (

let _88_46 = (FStar_ST.op_Colon_Equals recorded_hints None)
in (

let _88_48 = (FStar_ST.op_Colon_Equals replaying_hints None)
in (FStar_ST.op_Colon_Equals hint_stats []))))))


let with_hints_db = (fun fname f -> (

let _88_52 = (initialize_hints_db fname false)
in (

let result = (f ())
in (

let _88_55 = (finalize_hints_db fname)
in result))))


let next_hint : Prims.string  ->  Prims.int  ->  FStar_Util.hint Prims.option = (fun qname qindex -> (match ((FStar_ST.read replaying_hints)) with
| Some (hints) -> begin
(FStar_Util.find_map hints (fun _88_2 -> (match (_88_2) with
| Some (hint) when ((hint.FStar_Util.hint_name = qname) && (hint.FStar_Util.hint_index = qindex)) -> begin
Some (hint)
end
| _88_65 -> begin
None
end)))
end
| _88_67 -> begin
None
end))


let record_hint : FStar_Util.hint Prims.option  ->  Prims.unit = (fun hint -> (

let hint = (match (hint) with
| None -> begin
None
end
| Some (h) -> begin
Some ((

let _88_72 = h
in {FStar_Util.hint_name = _88_72.FStar_Util.hint_name; FStar_Util.hint_index = _88_72.FStar_Util.hint_index; FStar_Util.fuel = _88_72.FStar_Util.fuel; FStar_Util.ifuel = _88_72.FStar_Util.ifuel; FStar_Util.unsat_core = _88_72.FStar_Util.unsat_core; FStar_Util.query_elapsed_time = (Prims.parse_int "0")}))
end)
in (match ((FStar_ST.read recorded_hints)) with
| Some (l) -> begin
(FStar_ST.op_Colon_Equals recorded_hints (Some ((FStar_List.append l ((hint)::[])))))
end
| _88_78 -> begin
()
end)))


let record_hint_stat : FStar_Util.hint Prims.option  ->  z3_result  ->  Prims.int  ->  FStar_Range.range  ->  Prims.unit = (fun h res time r -> (

let s = {hint = h; replay_result = (z3_result_as_replay_result res); elapsed_time = time; source_location = r}
in (let _182_50 = (let _182_49 = (FStar_ST.read hint_stats)
in (s)::_182_49)
in (FStar_ST.op_Colon_Equals hint_stats _182_50))))


let ask_and_report_errors : FStar_TypeChecker_Env.env  ->  ((FStar_SMTEncoding_Z3.label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun env all_labels prefix query suffix -> (

let _88_89 = (FStar_SMTEncoding_Z3.giveZ3 prefix)
in (

let _88_98 = (match (env.FStar_TypeChecker_Env.qname_and_index) with
| None -> begin
(FStar_All.failwith "No query name set!")
end
| Some (q, n) -> begin
(((FStar_Ident.text_of_lid q)), (n))
end)
in (match (_88_98) with
| (query_name, query_index) -> begin
(

let minimum_workable_fuel = (FStar_Util.mk_ref None)
in (

let set_minimum_workable_fuel = (fun f _88_3 -> (match (_88_3) with
| ([], _88_105) -> begin
()
end
| errs -> begin
(match ((FStar_ST.read minimum_workable_fuel)) with
| Some (_88_109) -> begin
()
end
| None -> begin
(FStar_ST.op_Colon_Equals minimum_workable_fuel (Some (((f), (errs)))))
end)
end))
in (

let with_fuel = (fun label_assumptions p _88_118 -> (match (_88_118) with
| (n, i, timeout_ms) -> begin
(let _182_98 = (let _182_88 = (let _182_73 = (let _182_72 = (FStar_Util.string_of_int n)
in (let _182_71 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _182_72 _182_71)))
in FStar_SMTEncoding_Term.Caption (_182_73))
in (let _182_87 = (let _182_86 = (let _182_78 = (let _182_77 = (let _182_76 = (let _182_75 = (FStar_SMTEncoding_Term.mkApp (("MaxFuel"), ([])))
in (let _182_74 = (FStar_SMTEncoding_Term.n_fuel n)
in ((_182_75), (_182_74))))
in (FStar_SMTEncoding_Term.mkEq _182_76))
in ((_182_77), (None), (None)))
in FStar_SMTEncoding_Term.Assume (_182_78))
in (let _182_85 = (let _182_84 = (let _182_83 = (let _182_82 = (let _182_81 = (let _182_80 = (FStar_SMTEncoding_Term.mkApp (("MaxIFuel"), ([])))
in (let _182_79 = (FStar_SMTEncoding_Term.n_fuel i)
in ((_182_80), (_182_79))))
in (FStar_SMTEncoding_Term.mkEq _182_81))
in ((_182_82), (None), (None)))
in FStar_SMTEncoding_Term.Assume (_182_83))
in (_182_84)::(p)::[])
in (_182_86)::_182_85))
in (_182_88)::_182_87))
in (let _182_97 = (let _182_96 = (let _182_95 = (let _182_91 = (let _182_90 = (let _182_89 = (FStar_Util.string_of_int timeout_ms)
in (("timeout"), (_182_89)))
in FStar_SMTEncoding_Term.SetOption (_182_90))
in (_182_91)::[])
in (let _182_94 = (let _182_93 = (let _182_92 = if (FStar_Options.record_hints ()) then begin
(FStar_SMTEncoding_Term.GetUnsatCore)::[]
end else begin
[]
end
in (FStar_List.append _182_92 suffix))
in (FStar_List.append ((FStar_SMTEncoding_Term.CheckSat)::[]) _182_93))
in (FStar_List.append _182_95 _182_94)))
in (FStar_List.append label_assumptions _182_96))
in (FStar_List.append _182_98 _182_97)))
end))
in (

let check = (fun p -> (

let default_timeout = ((FStar_Options.z3_timeout ()) * (Prims.parse_int "1000"))
in (

let default_initial_config = (let _182_102 = (FStar_Options.initial_fuel ())
in (let _182_101 = (FStar_Options.initial_ifuel ())
in ((_182_102), (_182_101), (default_timeout))))
in (

let hint_opt = (next_hint query_name query_index)
in (

let _88_132 = (match (hint_opt) with
| None -> begin
((None), (default_initial_config))
end
| Some (hint) -> begin
(

let _88_129 = if (FStar_Option.isSome hint.FStar_Util.unsat_core) then begin
((hint.FStar_Util.unsat_core), (default_timeout))
end else begin
((None), (((Prims.parse_int "60") * (Prims.parse_int "1000"))))
end
in (match (_88_129) with
| (core, timeout) -> begin
((core), (((hint.FStar_Util.fuel), (hint.FStar_Util.ifuel), (timeout))))
end))
end)
in (match (_88_132) with
| (unsat_core, initial_config) -> begin
(

let alt_configs = (let _182_123 = (let _182_122 = if ((default_initial_config <> initial_config) || (FStar_Option.isSome unsat_core)) then begin
(default_initial_config)::[]
end else begin
[]
end
in (let _182_121 = (let _182_120 = if ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ())) then begin
(let _182_105 = (let _182_104 = (FStar_Options.initial_fuel ())
in (let _182_103 = (FStar_Options.max_ifuel ())
in ((_182_104), (_182_103), (default_timeout))))
in (_182_105)::[])
end else begin
[]
end
in (let _182_119 = (let _182_118 = if (((FStar_Options.max_fuel ()) / (Prims.parse_int "2")) > (FStar_Options.initial_fuel ())) then begin
(let _182_108 = (let _182_107 = ((FStar_Options.max_fuel ()) / (Prims.parse_int "2"))
in (let _182_106 = (FStar_Options.max_ifuel ())
in ((_182_107), (_182_106), (default_timeout))))
in (_182_108)::[])
end else begin
[]
end
in (let _182_117 = (let _182_116 = if (((FStar_Options.max_fuel ()) > (FStar_Options.initial_fuel ())) && ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ()))) then begin
(let _182_111 = (let _182_110 = (FStar_Options.max_fuel ())
in (let _182_109 = (FStar_Options.max_ifuel ())
in ((_182_110), (_182_109), (default_timeout))))
in (_182_111)::[])
end else begin
[]
end
in (let _182_115 = (let _182_114 = if ((FStar_Options.min_fuel ()) < (FStar_Options.initial_fuel ())) then begin
(let _182_113 = (let _182_112 = (FStar_Options.min_fuel ())
in ((_182_112), ((Prims.parse_int "1")), (default_timeout)))
in (_182_113)::[])
end else begin
[]
end
in (_182_114)::[])
in (_182_116)::_182_115))
in (_182_118)::_182_117))
in (_182_120)::_182_119))
in (_182_122)::_182_121))
in (FStar_List.flatten _182_123))
in (

let report = (fun p errs -> (

let errs = if ((FStar_Options.detail_errors ()) && ((FStar_Options.n_cores ()) = (Prims.parse_int "1"))) then begin
(

let _88_144 = (match ((FStar_ST.read minimum_workable_fuel)) with
| Some (f, errs) -> begin
((f), (errs))
end
| None -> begin
(let _182_129 = (let _182_128 = (FStar_Options.min_fuel ())
in ((_182_128), ((Prims.parse_int "1")), (default_timeout)))
in ((_182_129), (errs)))
end)
in (match (_88_144) with
| (min_fuel, potential_errors) -> begin
(

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref None)
in (

let _88_149 = (let _182_133 = (with_fuel label_assumptions p min_fuel)
in (FStar_SMTEncoding_Z3.ask None all_labels _182_133 (fun r -> (FStar_ST.op_Colon_Equals res (Some (r))))))
in (let _182_134 = (FStar_ST.read res)
in (FStar_Option.get _182_134)))))
in (let _182_135 = (FStar_SMTEncoding_ErrorReporting.detail_errors all_labels (Prims.fst errs) ask_z3)
in ((_182_135), (false))))
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
| _88_159 -> begin
errs
end)
in (

let _88_161 = (record_hint None)
in (

let _88_163 = if (FStar_Options.print_fuels ()) then begin
(let _182_141 = (let _182_136 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _182_136))
in (let _182_140 = (let _182_137 = (FStar_Options.max_fuel ())
in (FStar_All.pipe_right _182_137 FStar_Util.string_of_int))
in (let _182_139 = (let _182_138 = (FStar_Options.max_ifuel ())
in (FStar_All.pipe_right _182_138 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _182_141 _182_140 _182_139))))
end else begin
()
end
in (

let _88_170 = (let _182_143 = (FStar_All.pipe_right (Prims.fst errs) (FStar_List.map (fun _88_169 -> (match (_88_169) with
| (_88_166, x, y) -> begin
((x), (y))
end))))
in (FStar_TypeChecker_Errors.add_errors env _182_143))
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
| (_88_189, FStar_Util.Inr (_88_191)) -> begin
FStar_Util.Inr (errs)
end))
in (

let rec try_alt_configs = (fun prev_f p errs cfgs -> (

let _88_200 = (set_minimum_workable_fuel prev_f errs)
in (match (cfgs) with
| [] -> begin
(report p errs)
end
| (mi)::[] -> begin
(match (errs) with
| ([], _88_207) -> begin
(let _182_161 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask None all_labels _182_161 (cb false mi p [])))
end
| _88_210 -> begin
(

let _88_211 = (set_minimum_workable_fuel prev_f errs)
in (report p errs))
end)
end
| (mi)::tl -> begin
(let _182_163 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask None all_labels _182_163 (fun _88_218 -> (match (_88_218) with
| (result, elapsed_time) -> begin
(cb false mi p tl (((use_errors errs result)), (elapsed_time)))
end))))
end)))
and cb = (fun used_hint _88_223 p alt _88_228 -> (match (((_88_223), (_88_228))) with
| ((prev_fuel, prev_ifuel, timeout), (result, elapsed_time)) -> begin
(

let _88_231 = if used_hint then begin
(

let _88_229 = (FStar_SMTEncoding_Z3.refresh ())
in (let _182_169 = (FStar_TypeChecker_Env.get_range env)
in (record_hint_stat hint_opt result elapsed_time _182_169)))
end else begin
()
end
in (

let at_log_file = (fun _88_234 -> (match (()) with
| () -> begin
if (FStar_Options.log_queries ()) then begin
(let _182_172 = (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.log_file_name ())
in (Prims.strcat "@" _182_172))
end else begin
""
end
end))
in (

let query_info = (fun tag -> (let _182_190 = (let _182_189 = (let _182_175 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _182_175))
in (let _182_188 = (let _182_187 = (at_log_file ())
in (let _182_186 = (let _182_185 = (let _182_184 = (FStar_Util.string_of_int query_index)
in (let _182_183 = (let _182_182 = (let _182_181 = (let _182_180 = (FStar_Util.string_of_int elapsed_time)
in (let _182_179 = (let _182_178 = (FStar_Util.string_of_int prev_fuel)
in (let _182_177 = (let _182_176 = (FStar_Util.string_of_int prev_ifuel)
in (_182_176)::[])
in (_182_178)::_182_177))
in (_182_180)::_182_179))
in (if used_hint then begin
" (with hint)"
end else begin
""
end)::_182_181)
in (tag)::_182_182)
in (_182_184)::_182_183))
in (query_name)::_182_185)
in (_182_187)::_182_186))
in (_182_189)::_182_188))
in (FStar_Util.print "(%s%s)\n\tQuery (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s\n" _182_190)))
in (match (result) with
| FStar_Util.Inl (unsat_core) -> begin
(

let _88_240 = if (not (used_hint)) then begin
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

let _88_244 = if ((FStar_Options.print_fuels ()) || (FStar_Options.hint_info ())) then begin
(query_info "failed")
end else begin
()
end
in (try_alt_configs ((prev_fuel), (prev_ifuel), (timeout)) p errs alt))
end))))
end))
in (

let _88_246 = if (FStar_Option.isSome unsat_core) then begin
(FStar_SMTEncoding_Z3.refresh ())
end else begin
()
end
in (let _182_193 = (with_fuel [] p initial_config)
in (let _182_192 = (let _182_191 = (FStar_Option.isSome unsat_core)
in (cb _182_191 initial_config p alt_configs))
in (FStar_SMTEncoding_Z3.ask unsat_core all_labels _182_193 _182_192))))))))
end))))))
in (

let process_query = (fun q -> if ((FStar_Options.split_cases ()) > (Prims.parse_int "0")) then begin
(

let _88_252 = (let _182_199 = (FStar_Options.split_cases ())
in (FStar_SMTEncoding_SplitQueryCases.can_handle_query _182_199 q))
in (match (_88_252) with
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

let _88_256 = (let _182_218 = (let _182_217 = (let _182_216 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _182_216))
in (FStar_Util.format1 "Starting query at %s" _182_217))
in (FStar_SMTEncoding_Encode.push _182_218))
in (

let tcenv = (FStar_TypeChecker_Env.incr_query_index tcenv)
in (

let _88_259 = (FStar_SMTEncoding_Term.use_query_table ())
in (

let _88_265 = (FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv q)
in (match (_88_265) with
| (prefix, labels, qry, suffix) -> begin
(

let _88_266 = (FStar_SMTEncoding_Term.drop_query_table ())
in (

let pop = (fun _88_269 -> (match (()) with
| () -> begin
(let _182_223 = (let _182_222 = (let _182_221 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _182_221))
in (FStar_Util.format1 "Ending query at %s" _182_222))
in (FStar_SMTEncoding_Encode.pop _182_223))
end))
in (match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _88_276); FStar_SMTEncoding_Term.hash = _88_273; FStar_SMTEncoding_Term.freevars = _88_271}, _88_281, _88_283) -> begin
(

let _88_286 = (pop ())
in ())
end
| _88_289 when tcenv.FStar_TypeChecker_Env.admit -> begin
(

let _88_290 = (pop ())
in ())
end
| FStar_SMTEncoding_Term.Assume (q, _88_294, _88_296) -> begin
(

let _88_299 = (ask_and_report_errors tcenv labels prefix qry suffix)
in (pop ()))
end
| _88_302 -> begin
(FStar_All.failwith "Impossible")
end)))
end))))))


let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = FStar_SMTEncoding_Encode.init; FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push; FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop; FStar_TypeChecker_Env.mark = FStar_SMTEncoding_Encode.mark; FStar_TypeChecker_Env.reset_mark = FStar_SMTEncoding_Encode.reset_mark; FStar_TypeChecker_Env.commit_mark = FStar_SMTEncoding_Encode.commit_mark; FStar_TypeChecker_Env.encode_modul = FStar_SMTEncoding_Encode.encode_modul; FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig; FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.is_trivial = FStar_SMTEncoding_Encode.is_trivial; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}


let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun _88_303 -> ()); FStar_TypeChecker_Env.push = (fun _88_305 -> ()); FStar_TypeChecker_Env.pop = (fun _88_307 -> ()); FStar_TypeChecker_Env.mark = (fun _88_309 -> ()); FStar_TypeChecker_Env.reset_mark = (fun _88_311 -> ()); FStar_TypeChecker_Env.commit_mark = (fun _88_313 -> ()); FStar_TypeChecker_Env.encode_modul = (fun _88_315 _88_317 -> ()); FStar_TypeChecker_Env.encode_sig = (fun _88_319 _88_321 -> ()); FStar_TypeChecker_Env.solve = (fun _88_323 _88_325 _88_327 -> ()); FStar_TypeChecker_Env.is_trivial = (fun _88_329 _88_331 -> false); FStar_TypeChecker_Env.finish = (fun _88_333 -> ()); FStar_TypeChecker_Env.refresh = (fun _88_334 -> ())}




