
open Prims

type hint =
{fuel : Prims.int; ifuel : Prims.int; unsat_core : FStar_SMTEncoding_Z3.unsat_core; query_elapsed_time : Prims.int}


let is_Mkhint : hint  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkhint"))))


type hints =
hint Prims.option Prims.list


type hints_db =
{module_digest : Prims.string; hints : hints}


let is_Mkhints_db : hints_db  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkhints_db"))))


type z3_result =
(FStar_SMTEncoding_Z3.unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either


type hint_stat =
{hint : hint Prims.option; replay_result : z3_result; elapsed_time : Prims.int; source_location : FStar_Range.range}


let is_Mkhint_stat : hint_stat  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkhint_stat"))))


type hint_stats_t =
hint_stat Prims.list


let recorded_hints : hints Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)


let replaying_hints : hints Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)


let hint_stats : hint_stat Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let format_hints_file_name : Prims.string  ->  Prims.string = (fun src_filename -> (let _174_36 = (FStar_Util.format1 "%s.hints" src_filename)
in (FStar_All.pipe_left FStar_Util.format_value_file_name _174_36)))


let initialize_hints_db = (fun src_filename force_record -> (

let _84_18 = (FStar_ST.op_Colon_Equals hint_stats [])
in (

let _84_20 = if (FStar_Options.record_hints ()) then begin
(FStar_ST.op_Colon_Equals recorded_hints (Some ([])))
end else begin
()
end
in if (FStar_Options.use_hints ()) then begin
(

let norm_src_filename = (FStar_Util.normalize_file_path src_filename)
in (

let val_filename = (format_hints_file_name norm_src_filename)
in (match ((FStar_Util.load_value_from_file val_filename)) with
| Some (hints) -> begin
(

let expected_digest = (FStar_Util.digest_of_file norm_src_filename)
in (

let _84_27 = if (FStar_Options.hint_info ()) then begin
if (hints.module_digest = expected_digest) then begin
(FStar_Util.print1 "(%s) digest is valid; using hints db.\n" norm_src_filename)
end else begin
(FStar_Util.print1 "(%s) digest is invalid; using potentially stale hints\n" norm_src_filename)
end
end else begin
()
end
in (FStar_ST.op_Colon_Equals replaying_hints (Some (hints.hints)))))
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

let _84_34 = if (FStar_Options.record_hints ()) then begin
(

let hints = (let _174_41 = (FStar_ST.read recorded_hints)
in (FStar_Option.get _174_41))
in (

let hints_db = (let _174_42 = (FStar_Util.digest_of_file src_filename)
in {module_digest = _174_42; hints = hints})
in (

let hints_file_name = (format_hints_file_name src_filename)
in (FStar_Util.save_value_to_file hints_file_name hints_db))))
end else begin
()
end
in (

let _84_42 = if (FStar_Options.hint_info ()) then begin
(

let stats = (let _174_43 = (FStar_ST.read hint_stats)
in (FStar_All.pipe_right _174_43 FStar_List.rev))
in (FStar_All.pipe_right stats (FStar_List.iter (fun s -> (match (s.replay_result) with
| FStar_Util.Inl (_unsat_core) -> begin
(let _174_46 = (FStar_Range.string_of_range s.source_location)
in (let _174_45 = (FStar_Util.string_of_int s.elapsed_time)
in (FStar_Util.print2 "Hint-info (%s): Replay succeeded in %s milliseconds\n" _174_46 _174_45)))
end
| FStar_Util.Inr (_error) -> begin
(let _174_48 = (FStar_Range.string_of_range s.source_location)
in (let _174_47 = (FStar_Util.string_of_int s.elapsed_time)
in (FStar_Util.print2 "Hint-info (%s): Replay failed in %s milliseconds\n" _174_48 _174_47)))
end)))))
end else begin
()
end
in (

let _84_44 = (FStar_ST.op_Colon_Equals recorded_hints None)
in (

let _84_46 = (FStar_ST.op_Colon_Equals replaying_hints None)
in (FStar_ST.op_Colon_Equals hint_stats []))))))


let with_hints_db = (fun fname f -> (

let _84_50 = (initialize_hints_db fname false)
in (

let result = (f ())
in (

let _84_53 = (finalize_hints_db fname)
in result))))


let next_hint : Prims.unit  ->  hint Prims.option = (fun _84_55 -> (match (()) with
| () -> begin
(match ((FStar_ST.read replaying_hints)) with
| Some ((hd)::tl) -> begin
(

let _84_60 = (FStar_ST.op_Colon_Equals replaying_hints (Some (tl)))
in hd)
end
| _84_63 -> begin
None
end)
end))


let record_hint : hint Prims.option  ->  Prims.unit = (fun hint -> (match ((FStar_ST.read recorded_hints)) with
| Some (l) -> begin
(FStar_ST.op_Colon_Equals recorded_hints (Some ((FStar_List.append l ((hint)::[])))))
end
| _84_68 -> begin
()
end))


let record_hint_stat : hint Prims.option  ->  z3_result  ->  Prims.int  ->  FStar_Range.range  ->  Prims.unit = (fun h res time r -> (

let s = {hint = h; replay_result = res; elapsed_time = time; source_location = r}
in (let _174_67 = (let _174_66 = (FStar_ST.read hint_stats)
in (s)::_174_66)
in (FStar_ST.op_Colon_Equals hint_stats _174_67))))


let ask_and_report_errors : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  ((FStar_SMTEncoding_Z3.label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun env use_fresh_z3_context all_labels prefix query suffix -> (

let _84_80 = (FStar_SMTEncoding_Z3.giveZ3 prefix)
in (

let minimum_workable_fuel = (FStar_Util.mk_ref None)
in (

let set_minimum_workable_fuel = (fun f _84_1 -> (match (_84_1) with
| [] -> begin
()
end
| errs -> begin
(match ((FStar_ST.read minimum_workable_fuel)) with
| Some (_84_89) -> begin
()
end
| None -> begin
(FStar_ST.op_Colon_Equals minimum_workable_fuel (Some ((f, errs))))
end)
end))
in (

let with_fuel = (fun label_assumptions p _84_98 -> (match (_84_98) with
| (n, i, timeout_ms) -> begin
(let _174_117 = (let _174_116 = (let _174_114 = (let _174_113 = (let _174_108 = (let _174_107 = (let _174_92 = (let _174_91 = (FStar_Util.string_of_int n)
in (let _174_90 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _174_91 _174_90)))
in FStar_SMTEncoding_Term.Caption (_174_92))
in (let _174_106 = (let _174_105 = (let _174_97 = (let _174_96 = (let _174_95 = (let _174_94 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (let _174_93 = (FStar_SMTEncoding_Term.n_fuel n)
in (_174_94, _174_93)))
in (FStar_SMTEncoding_Term.mkEq _174_95))
in (_174_96, None, None))
in FStar_SMTEncoding_Term.Assume (_174_97))
in (let _174_104 = (let _174_103 = (let _174_102 = (let _174_101 = (let _174_100 = (let _174_99 = (FStar_SMTEncoding_Term.mkApp ("MaxIFuel", []))
in (let _174_98 = (FStar_SMTEncoding_Term.n_fuel i)
in (_174_99, _174_98)))
in (FStar_SMTEncoding_Term.mkEq _174_100))
in (_174_101, None, None))
in FStar_SMTEncoding_Term.Assume (_174_102))
in (_174_103)::(p)::[])
in (_174_105)::_174_104))
in (_174_107)::_174_106))
in (FStar_List.append _174_108 label_assumptions))
in (let _174_112 = (let _174_111 = (let _174_110 = (let _174_109 = (FStar_Util.string_of_int timeout_ms)
in ("timeout", _174_109))
in FStar_SMTEncoding_Term.SetOption (_174_110))
in (_174_111)::[])
in (FStar_List.append _174_113 _174_112)))
in (FStar_List.append _174_114 ((FStar_SMTEncoding_Term.CheckSat)::[])))
in (let _174_115 = if (FStar_Options.record_hints ()) then begin
(FStar_SMTEncoding_Term.GetUnsatCore)::[]
end else begin
[]
end
in (FStar_List.append _174_116 _174_115)))
in (FStar_List.append _174_117 suffix))
end))
in (

let check = (fun p -> (

let default_timeout = ((FStar_Options.z3_timeout ()) * 1000)
in (

let default_initial_config = (let _174_121 = (FStar_Options.initial_fuel ())
in (let _174_120 = (FStar_Options.initial_ifuel ())
in (_174_121, _174_120, default_timeout)))
in (

let _84_111 = (match ((next_hint ())) with
| None -> begin
(None, default_initial_config)
end
| Some (hint) -> begin
(

let _84_108 = if (FStar_Option.isSome hint.unsat_core) then begin
(hint.unsat_core, (3 * 1000))
end else begin
(None, (60 * 1000))
end
in (match (_84_108) with
| (core, timeout) -> begin
(core, (hint.fuel, hint.ifuel, timeout))
end))
end)
in (match (_84_111) with
| (unsat_core, initial_config) -> begin
(

let alt_configs = (let _174_142 = (let _174_141 = if ((default_initial_config <> initial_config) || (FStar_Option.isSome unsat_core)) then begin
(default_initial_config)::[]
end else begin
[]
end
in (let _174_140 = (let _174_139 = if ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ())) then begin
(let _174_124 = (let _174_123 = (FStar_Options.initial_fuel ())
in (let _174_122 = (FStar_Options.max_ifuel ())
in (_174_123, _174_122, default_timeout)))
in (_174_124)::[])
end else begin
[]
end
in (let _174_138 = (let _174_137 = if (((FStar_Options.max_fuel ()) / 2) > (FStar_Options.initial_fuel ())) then begin
(let _174_127 = (let _174_126 = ((FStar_Options.max_fuel ()) / 2)
in (let _174_125 = (FStar_Options.max_ifuel ())
in (_174_126, _174_125, default_timeout)))
in (_174_127)::[])
end else begin
[]
end
in (let _174_136 = (let _174_135 = if (((FStar_Options.max_fuel ()) > (FStar_Options.initial_fuel ())) && ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ()))) then begin
(let _174_130 = (let _174_129 = (FStar_Options.max_fuel ())
in (let _174_128 = (FStar_Options.max_ifuel ())
in (_174_129, _174_128, default_timeout)))
in (_174_130)::[])
end else begin
[]
end
in (let _174_134 = (let _174_133 = if ((FStar_Options.min_fuel ()) < (FStar_Options.initial_fuel ())) then begin
(let _174_132 = (let _174_131 = (FStar_Options.min_fuel ())
in (_174_131, 1, default_timeout))
in (_174_132)::[])
end else begin
[]
end
in (_174_133)::[])
in (_174_135)::_174_134))
in (_174_137)::_174_136))
in (_174_139)::_174_138))
in (_174_141)::_174_140))
in (FStar_List.flatten _174_142))
in (

let report = (fun p errs -> (

let errs = if ((FStar_Options.detail_errors ()) && ((FStar_Options.n_cores ()) = 1)) then begin
(

let _84_123 = (match ((FStar_ST.read minimum_workable_fuel)) with
| Some (f, errs) -> begin
(f, errs)
end
| None -> begin
(let _174_148 = (let _174_147 = (FStar_Options.min_fuel ())
in (_174_147, 1, default_timeout))
in (_174_148, errs))
end)
in (match (_84_123) with
| (min_fuel, potential_errors) -> begin
(

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref None)
in (

let _84_128 = (let _174_152 = (with_fuel label_assumptions p min_fuel)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context None all_labels _174_152 (fun r -> (FStar_ST.op_Colon_Equals res (Some (r))))))
in (let _174_153 = (FStar_ST.read res)
in (FStar_Option.get _174_153)))))
in (FStar_SMTEncoding_ErrorReporting.detail_errors all_labels errs ask_z3))
end))
end else begin
errs
end
in (

let errs = (match (errs) with
| [] -> begin
((("", FStar_SMTEncoding_Term.Term_sort), "Unknown assertion failed", FStar_Range.dummyRange))::[]
end
| _84_133 -> begin
errs
end)
in (

let _84_135 = (record_hint None)
in (

let _84_137 = if (FStar_Options.print_fuels ()) then begin
(let _174_159 = (let _174_154 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _174_154))
in (let _174_158 = (let _174_155 = (FStar_Options.max_fuel ())
in (FStar_All.pipe_right _174_155 FStar_Util.string_of_int))
in (let _174_157 = (let _174_156 = (FStar_Options.max_ifuel ())
in (FStar_All.pipe_right _174_156 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _174_159 _174_158 _174_157))))
end else begin
()
end
in (

let _84_144 = (let _174_161 = (FStar_All.pipe_right errs (FStar_List.map (fun _84_143 -> (match (_84_143) with
| (_84_140, x, y) -> begin
(x, y)
end))))
in (FStar_TypeChecker_Errors.add_errors env _174_161))
in if (FStar_Options.detail_errors ()) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Detailed error report follows\n")))
end else begin
()
end))))))
in (

let use_errors = (fun errs result -> (match ((errs, result)) with
| (([], _)) | ((_, FStar_Util.Inl (_))) -> begin
result
end
| (_84_160, FStar_Util.Inr (_84_162)) -> begin
FStar_Util.Inr (errs)
end))
in (

let rec try_alt_configs = (fun prev_f p errs cfgs -> (

let _84_171 = (set_minimum_workable_fuel prev_f errs)
in (match (cfgs) with
| [] -> begin
(report p errs)
end
| (mi)::[] -> begin
(match (errs) with
| [] -> begin
(let _174_179 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context None all_labels _174_179 (cb false mi p [])))
end
| _84_178 -> begin
(

let _84_179 = (set_minimum_workable_fuel prev_f errs)
in (report p errs))
end)
end
| (mi)::tl -> begin
(let _174_181 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context None all_labels _174_181 (fun _84_186 -> (match (_84_186) with
| (result, elapsed_time) -> begin
(cb false mi p tl ((use_errors errs result), elapsed_time))
end))))
end)))
and cb = (fun used_hint _84_191 p alt _84_196 -> (match ((_84_191, _84_196)) with
| ((prev_fuel, prev_ifuel, timeout), (result, elapsed_time)) -> begin
(

let _84_199 = if used_hint then begin
(

let _84_197 = (FStar_SMTEncoding_Z3.refresh ())
in (let _174_187 = (FStar_TypeChecker_Env.get_range env)
in (record_hint_stat None result elapsed_time _174_187)))
end else begin
()
end
in (match (result) with
| FStar_Util.Inl (unsat_core) -> begin
(

let hint = {fuel = prev_fuel; ifuel = prev_ifuel; unsat_core = unsat_core; query_elapsed_time = elapsed_time}
in (

let _84_204 = (record_hint (Some (hint)))
in if (FStar_Options.print_fuels ()) then begin
(let _174_192 = (let _174_188 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _174_188))
in (let _174_191 = (FStar_Util.string_of_int elapsed_time)
in (let _174_190 = (FStar_Util.string_of_int prev_fuel)
in (let _174_189 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print4 "(%s) Query succeeded in %s milliseconds with fuel %s and ifuel %s\n" _174_192 _174_191 _174_190 _174_189)))))
end else begin
()
end))
end
| FStar_Util.Inr (errs) -> begin
(

let _84_208 = if (FStar_Options.print_fuels ()) then begin
(let _174_197 = (let _174_193 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _174_193))
in (let _174_196 = (FStar_Util.string_of_int elapsed_time)
in (let _174_195 = (FStar_Util.string_of_int prev_fuel)
in (let _174_194 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print4 "(%s) Query failed in %s milliseconds with fuel %s and ifuel %s ... retrying \n" _174_197 _174_196 _174_195 _174_194)))))
end else begin
()
end
in (try_alt_configs (prev_fuel, prev_ifuel, timeout) p errs alt))
end))
end))
in (

let _84_210 = if (FStar_Option.isSome unsat_core) then begin
(FStar_SMTEncoding_Z3.refresh ())
end else begin
()
end
in (let _174_200 = (with_fuel [] p initial_config)
in (let _174_199 = (let _174_198 = (FStar_Option.isSome unsat_core)
in (cb _174_198 initial_config p alt_configs))
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context unsat_core all_labels _174_200 _174_199))))))))
end)))))
in (

let process_query = (fun q -> if ((FStar_Options.split_cases ()) > 0) then begin
(

let _84_216 = (let _174_206 = (FStar_Options.split_cases ())
in (FStar_SMTEncoding_SplitQueryCases.can_handle_query _174_206 q))
in (match (_84_216) with
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
end)))))))


let solve : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun use_env_msg tcenv q -> (

let _84_220 = (let _174_225 = (let _174_224 = (let _174_223 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _174_223))
in (FStar_Util.format1 "Starting query at %s" _174_224))
in (FStar_SMTEncoding_Encode.push _174_225))
in (

let _84_226 = (FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv q)
in (match (_84_226) with
| (prefix, labels, qry, suffix) -> begin
(

let pop = (fun _84_228 -> (match (()) with
| () -> begin
(let _174_230 = (let _174_229 = (let _174_228 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _174_228))
in (FStar_Util.format1 "Ending query at %s" _174_229))
in (FStar_SMTEncoding_Encode.pop _174_230))
end))
in (match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _84_235); FStar_SMTEncoding_Term.hash = _84_232; FStar_SMTEncoding_Term.freevars = _84_230}, _84_240, _84_242) -> begin
(

let _84_245 = (pop ())
in ())
end
| _84_248 when tcenv.FStar_TypeChecker_Env.admit -> begin
(

let _84_249 = (pop ())
in ())
end
| FStar_SMTEncoding_Term.Assume (q, _84_253, _84_255) -> begin
(

let _84_258 = (ask_and_report_errors tcenv false labels prefix qry suffix)
in (pop ()))
end
| _84_261 -> begin
(FStar_All.failwith "Impossible")
end))
end))))


let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = FStar_SMTEncoding_Encode.init; FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push; FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop; FStar_TypeChecker_Env.mark = FStar_SMTEncoding_Encode.mark; FStar_TypeChecker_Env.reset_mark = FStar_SMTEncoding_Encode.reset_mark; FStar_TypeChecker_Env.commit_mark = FStar_SMTEncoding_Encode.commit_mark; FStar_TypeChecker_Env.encode_modul = FStar_SMTEncoding_Encode.encode_modul; FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig; FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.is_trivial = FStar_SMTEncoding_Encode.is_trivial; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}


let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun _84_262 -> ()); FStar_TypeChecker_Env.push = (fun _84_264 -> ()); FStar_TypeChecker_Env.pop = (fun _84_266 -> ()); FStar_TypeChecker_Env.mark = (fun _84_268 -> ()); FStar_TypeChecker_Env.reset_mark = (fun _84_270 -> ()); FStar_TypeChecker_Env.commit_mark = (fun _84_272 -> ()); FStar_TypeChecker_Env.encode_modul = (fun _84_274 _84_276 -> ()); FStar_TypeChecker_Env.encode_sig = (fun _84_278 _84_280 -> ()); FStar_TypeChecker_Env.solve = (fun _84_282 _84_284 _84_286 -> ()); FStar_TypeChecker_Env.is_trivial = (fun _84_288 _84_290 -> false); FStar_TypeChecker_Env.finish = (fun _84_292 -> ()); FStar_TypeChecker_Env.refresh = (fun _84_293 -> ())}




