
open Prims

type z3_result =
(FStar_SMTEncoding_Z3.unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either


type hint_stat =
{hint : FStar_Util.hint Prims.option; replay_result : z3_result; elapsed_time : Prims.int; source_location : FStar_Range.range}


let is_Mkhint_stat : hint_stat  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkhint_stat"))))


type hint_stats_t =
hint_stat Prims.list


let recorded_hints : FStar_Util.hints Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)


let replaying_hints : FStar_Util.hints Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)


let hint_stats : hint_stat Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let format_hints_file_name : Prims.string  ->  Prims.string = (fun src_filename -> (FStar_Util.format1 "%s.hints" src_filename))


let initialize_hints_db = (fun src_filename force_record -> (

let _85_10 = (FStar_ST.op_Colon_Equals hint_stats [])
in (

let _85_12 = if (FStar_Options.record_hints ()) then begin
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

let _85_19 = if (FStar_Options.hint_info ()) then begin
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

let _85_26 = if (FStar_Options.record_hints ()) then begin
(

let hints = (let _176_20 = (FStar_ST.read recorded_hints)
in (FStar_Option.get _176_20))
in (

let hints_db = (let _176_21 = (FStar_Util.digest_of_file src_filename)
in {FStar_Util.module_digest = _176_21; FStar_Util.hints = hints})
in (

let hints_file_name = (format_hints_file_name src_filename)
in (FStar_Util.write_hints hints_file_name hints_db))))
end else begin
()
end
in (

let _85_34 = if (FStar_Options.hint_info ()) then begin
(

let stats = (let _176_22 = (FStar_ST.read hint_stats)
in (FStar_All.pipe_right _176_22 FStar_List.rev))
in (FStar_All.pipe_right stats (FStar_List.iter (fun s -> (match (s.replay_result) with
| FStar_Util.Inl (_unsat_core) -> begin
(let _176_25 = (FStar_Range.string_of_range s.source_location)
in (let _176_24 = (FStar_Util.string_of_int s.elapsed_time)
in (FStar_Util.print2 "Hint-info (%s): Replay succeeded in %s milliseconds\n" _176_25 _176_24)))
end
| FStar_Util.Inr (_error) -> begin
(let _176_27 = (FStar_Range.string_of_range s.source_location)
in (let _176_26 = (FStar_Util.string_of_int s.elapsed_time)
in (FStar_Util.print2 "Hint-info (%s): Replay failed in %s milliseconds\n" _176_27 _176_26)))
end)))))
end else begin
()
end
in (

let _85_36 = (FStar_ST.op_Colon_Equals recorded_hints None)
in (

let _85_38 = (FStar_ST.op_Colon_Equals replaying_hints None)
in (FStar_ST.op_Colon_Equals hint_stats []))))))


let with_hints_db = (fun fname f -> (

let _85_42 = (initialize_hints_db fname false)
in (

let result = (f ())
in (

let _85_45 = (finalize_hints_db fname)
in result))))


let next_hint : Prims.unit  ->  FStar_Util.hint Prims.option = (fun _85_47 -> (match (()) with
| () -> begin
(match ((FStar_ST.read replaying_hints)) with
| Some ((hd)::tl) -> begin
(

let _85_52 = (FStar_ST.op_Colon_Equals replaying_hints (Some (tl)))
in hd)
end
| _85_55 -> begin
None
end)
end))


let record_hint : FStar_Util.hint Prims.option  ->  Prims.unit = (fun hint -> (

let hint = (match (hint) with
| None -> begin
None
end
| Some (h) -> begin
Some ((

let _85_60 = h
in {FStar_Util.fuel = _85_60.FStar_Util.fuel; FStar_Util.ifuel = _85_60.FStar_Util.ifuel; FStar_Util.unsat_core = _85_60.FStar_Util.unsat_core; FStar_Util.query_elapsed_time = 0}))
end)
in (match ((FStar_ST.read recorded_hints)) with
| Some (l) -> begin
(FStar_ST.op_Colon_Equals recorded_hints (Some ((FStar_List.append l ((hint)::[])))))
end
| _85_66 -> begin
()
end)))


let record_hint_stat : FStar_Util.hint Prims.option  ->  z3_result  ->  Prims.int  ->  FStar_Range.range  ->  Prims.unit = (fun h res time r -> (

let s = {hint = h; replay_result = res; elapsed_time = time; source_location = r}
in (let _176_46 = (let _176_45 = (FStar_ST.read hint_stats)
in (s)::_176_45)
in (FStar_ST.op_Colon_Equals hint_stats _176_46))))


let ask_and_report_errors : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  ((FStar_SMTEncoding_Z3.label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun env use_fresh_z3_context all_labels prefix query suffix -> (

let _85_78 = (FStar_SMTEncoding_Z3.giveZ3 prefix)
in (

let minimum_workable_fuel = (FStar_Util.mk_ref None)
in (

let set_minimum_workable_fuel = (fun f _85_1 -> (match (_85_1) with
| [] -> begin
()
end
| errs -> begin
(match ((FStar_ST.read minimum_workable_fuel)) with
| Some (_85_87) -> begin
()
end
| None -> begin
(FStar_ST.op_Colon_Equals minimum_workable_fuel (Some ((f, errs))))
end)
end))
in (

let with_fuel = (fun label_assumptions p _85_96 -> (match (_85_96) with
| (n, i, timeout_ms) -> begin
(let _176_96 = (let _176_95 = (let _176_93 = (let _176_92 = (let _176_87 = (let _176_86 = (let _176_71 = (let _176_70 = (FStar_Util.string_of_int n)
in (let _176_69 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _176_70 _176_69)))
in FStar_SMTEncoding_Term.Caption (_176_71))
in (let _176_85 = (let _176_84 = (let _176_76 = (let _176_75 = (let _176_74 = (let _176_73 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (let _176_72 = (FStar_SMTEncoding_Term.n_fuel n)
in (_176_73, _176_72)))
in (FStar_SMTEncoding_Term.mkEq _176_74))
in (_176_75, None, None))
in FStar_SMTEncoding_Term.Assume (_176_76))
in (let _176_83 = (let _176_82 = (let _176_81 = (let _176_80 = (let _176_79 = (let _176_78 = (FStar_SMTEncoding_Term.mkApp ("MaxIFuel", []))
in (let _176_77 = (FStar_SMTEncoding_Term.n_fuel i)
in (_176_78, _176_77)))
in (FStar_SMTEncoding_Term.mkEq _176_79))
in (_176_80, None, None))
in FStar_SMTEncoding_Term.Assume (_176_81))
in (_176_82)::(p)::[])
in (_176_84)::_176_83))
in (_176_86)::_176_85))
in (FStar_List.append _176_87 label_assumptions))
in (let _176_91 = (let _176_90 = (let _176_89 = (let _176_88 = (FStar_Util.string_of_int timeout_ms)
in ("timeout", _176_88))
in FStar_SMTEncoding_Term.SetOption (_176_89))
in (_176_90)::[])
in (FStar_List.append _176_92 _176_91)))
in (FStar_List.append _176_93 ((FStar_SMTEncoding_Term.CheckSat)::[])))
in (let _176_94 = if (FStar_Options.record_hints ()) then begin
(FStar_SMTEncoding_Term.GetUnsatCore)::[]
end else begin
[]
end
in (FStar_List.append _176_95 _176_94)))
in (FStar_List.append _176_96 suffix))
end))
in (

let check = (fun p -> (

let default_timeout = ((FStar_Options.z3_timeout ()) * 1000)
in (

let default_initial_config = (let _176_100 = (FStar_Options.initial_fuel ())
in (let _176_99 = (FStar_Options.initial_ifuel ())
in (_176_100, _176_99, default_timeout)))
in (

let hint_opt = (next_hint ())
in (

let _85_110 = (match (hint_opt) with
| None -> begin
(None, default_initial_config)
end
| Some (hint) -> begin
(

let _85_107 = if (FStar_Option.isSome hint.FStar_Util.unsat_core) then begin
(hint.FStar_Util.unsat_core, default_timeout)
end else begin
(None, (60 * 1000))
end
in (match (_85_107) with
| (core, timeout) -> begin
(core, (hint.FStar_Util.fuel, hint.FStar_Util.ifuel, timeout))
end))
end)
in (match (_85_110) with
| (unsat_core, initial_config) -> begin
(

let alt_configs = (let _176_121 = (let _176_120 = if ((default_initial_config <> initial_config) || (FStar_Option.isSome unsat_core)) then begin
(default_initial_config)::[]
end else begin
[]
end
in (let _176_119 = (let _176_118 = if ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ())) then begin
(let _176_103 = (let _176_102 = (FStar_Options.initial_fuel ())
in (let _176_101 = (FStar_Options.max_ifuel ())
in (_176_102, _176_101, default_timeout)))
in (_176_103)::[])
end else begin
[]
end
in (let _176_117 = (let _176_116 = if (((FStar_Options.max_fuel ()) / 2) > (FStar_Options.initial_fuel ())) then begin
(let _176_106 = (let _176_105 = ((FStar_Options.max_fuel ()) / 2)
in (let _176_104 = (FStar_Options.max_ifuel ())
in (_176_105, _176_104, default_timeout)))
in (_176_106)::[])
end else begin
[]
end
in (let _176_115 = (let _176_114 = if (((FStar_Options.max_fuel ()) > (FStar_Options.initial_fuel ())) && ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ()))) then begin
(let _176_109 = (let _176_108 = (FStar_Options.max_fuel ())
in (let _176_107 = (FStar_Options.max_ifuel ())
in (_176_108, _176_107, default_timeout)))
in (_176_109)::[])
end else begin
[]
end
in (let _176_113 = (let _176_112 = if ((FStar_Options.min_fuel ()) < (FStar_Options.initial_fuel ())) then begin
(let _176_111 = (let _176_110 = (FStar_Options.min_fuel ())
in (_176_110, 1, default_timeout))
in (_176_111)::[])
end else begin
[]
end
in (_176_112)::[])
in (_176_114)::_176_113))
in (_176_116)::_176_115))
in (_176_118)::_176_117))
in (_176_120)::_176_119))
in (FStar_List.flatten _176_121))
in (

let report = (fun p errs -> (

let errs = if ((FStar_Options.detail_errors ()) && ((FStar_Options.n_cores ()) = 1)) then begin
(

let _85_122 = (match ((FStar_ST.read minimum_workable_fuel)) with
| Some (f, errs) -> begin
(f, errs)
end
| None -> begin
(let _176_127 = (let _176_126 = (FStar_Options.min_fuel ())
in (_176_126, 1, default_timeout))
in (_176_127, errs))
end)
in (match (_85_122) with
| (min_fuel, potential_errors) -> begin
(

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref None)
in (

let _85_127 = (let _176_131 = (with_fuel label_assumptions p min_fuel)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context None all_labels _176_131 (fun r -> (FStar_ST.op_Colon_Equals res (Some (r))))))
in (let _176_132 = (FStar_ST.read res)
in (FStar_Option.get _176_132)))))
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
| _85_132 -> begin
errs
end)
in (

let _85_134 = (record_hint None)
in (

let _85_136 = if (FStar_Options.print_fuels ()) then begin
(let _176_138 = (let _176_133 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _176_133))
in (let _176_137 = (let _176_134 = (FStar_Options.max_fuel ())
in (FStar_All.pipe_right _176_134 FStar_Util.string_of_int))
in (let _176_136 = (let _176_135 = (FStar_Options.max_ifuel ())
in (FStar_All.pipe_right _176_135 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _176_138 _176_137 _176_136))))
end else begin
()
end
in (

let _85_143 = (let _176_140 = (FStar_All.pipe_right errs (FStar_List.map (fun _85_142 -> (match (_85_142) with
| (_85_139, x, y) -> begin
(x, y)
end))))
in (FStar_TypeChecker_Errors.add_errors env _176_140))
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
| (_85_159, FStar_Util.Inr (_85_161)) -> begin
FStar_Util.Inr (errs)
end))
in (

let rec try_alt_configs = (fun prev_f p errs cfgs -> (

let _85_170 = (set_minimum_workable_fuel prev_f errs)
in (match (cfgs) with
| [] -> begin
(report p errs)
end
| (mi)::[] -> begin
(match (errs) with
| [] -> begin
(let _176_158 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context None all_labels _176_158 (cb false mi p [])))
end
| _85_177 -> begin
(

let _85_178 = (set_minimum_workable_fuel prev_f errs)
in (report p errs))
end)
end
| (mi)::tl -> begin
(let _176_160 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context None all_labels _176_160 (fun _85_185 -> (match (_85_185) with
| (result, elapsed_time) -> begin
(cb false mi p tl ((use_errors errs result), elapsed_time))
end))))
end)))
and cb = (fun used_hint _85_190 p alt _85_195 -> (match ((_85_190, _85_195)) with
| ((prev_fuel, prev_ifuel, timeout), (result, elapsed_time)) -> begin
(

let _85_198 = if used_hint then begin
(

let _85_196 = (FStar_SMTEncoding_Z3.refresh ())
in (let _176_166 = (FStar_TypeChecker_Env.get_range env)
in (record_hint_stat hint_opt result elapsed_time _176_166)))
end else begin
()
end
in (match (result) with
| FStar_Util.Inl (unsat_core) -> begin
(

let hint = {FStar_Util.fuel = prev_fuel; FStar_Util.ifuel = prev_ifuel; FStar_Util.unsat_core = unsat_core; FStar_Util.query_elapsed_time = elapsed_time}
in (

let _85_203 = (record_hint (Some (hint)))
in if (FStar_Options.print_fuels ()) then begin
(let _176_171 = (let _176_167 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _176_167))
in (let _176_170 = (FStar_Util.string_of_int elapsed_time)
in (let _176_169 = (FStar_Util.string_of_int prev_fuel)
in (let _176_168 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print4 "(%s) Query succeeded in %s milliseconds with fuel %s and ifuel %s\n" _176_171 _176_170 _176_169 _176_168)))))
end else begin
()
end))
end
| FStar_Util.Inr (errs) -> begin
(

let _85_207 = if (FStar_Options.print_fuels ()) then begin
(let _176_176 = (let _176_172 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _176_172))
in (let _176_175 = (FStar_Util.string_of_int elapsed_time)
in (let _176_174 = (FStar_Util.string_of_int prev_fuel)
in (let _176_173 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print4 "(%s) Query failed in %s milliseconds with fuel %s and ifuel %s ... retrying \n" _176_176 _176_175 _176_174 _176_173)))))
end else begin
()
end
in (try_alt_configs (prev_fuel, prev_ifuel, timeout) p errs alt))
end))
end))
in (

let _85_209 = if (FStar_Option.isSome unsat_core) then begin
(FStar_SMTEncoding_Z3.refresh ())
end else begin
()
end
in (let _176_179 = (with_fuel [] p initial_config)
in (let _176_178 = (let _176_177 = (FStar_Option.isSome unsat_core)
in (cb _176_177 initial_config p alt_configs))
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context unsat_core all_labels _176_179 _176_178))))))))
end))))))
in (

let process_query = (fun q -> if ((FStar_Options.split_cases ()) > 0) then begin
(

let _85_215 = (let _176_185 = (FStar_Options.split_cases ())
in (FStar_SMTEncoding_SplitQueryCases.can_handle_query _176_185 q))
in (match (_85_215) with
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

let _85_219 = (let _176_204 = (let _176_203 = (let _176_202 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _176_202))
in (FStar_Util.format1 "Starting query at %s" _176_203))
in (FStar_SMTEncoding_Encode.push _176_204))
in (

let _85_225 = (FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv q)
in (match (_85_225) with
| (prefix, labels, qry, suffix) -> begin
(

let pop = (fun _85_227 -> (match (()) with
| () -> begin
(let _176_209 = (let _176_208 = (let _176_207 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _176_207))
in (FStar_Util.format1 "Ending query at %s" _176_208))
in (FStar_SMTEncoding_Encode.pop _176_209))
end))
in (match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _85_234); FStar_SMTEncoding_Term.hash = _85_231; FStar_SMTEncoding_Term.freevars = _85_229}, _85_239, _85_241) -> begin
(

let _85_244 = (pop ())
in ())
end
| _85_247 when tcenv.FStar_TypeChecker_Env.admit -> begin
(

let _85_248 = (pop ())
in ())
end
| FStar_SMTEncoding_Term.Assume (q, _85_252, _85_254) -> begin
(

let _85_257 = (ask_and_report_errors tcenv false labels prefix qry suffix)
in (pop ()))
end
| _85_260 -> begin
(FStar_All.failwith "Impossible")
end))
end))))


let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = FStar_SMTEncoding_Encode.init; FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push; FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop; FStar_TypeChecker_Env.mark = FStar_SMTEncoding_Encode.mark; FStar_TypeChecker_Env.reset_mark = FStar_SMTEncoding_Encode.reset_mark; FStar_TypeChecker_Env.commit_mark = FStar_SMTEncoding_Encode.commit_mark; FStar_TypeChecker_Env.encode_modul = FStar_SMTEncoding_Encode.encode_modul; FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig; FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.is_trivial = FStar_SMTEncoding_Encode.is_trivial; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}


let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun _85_261 -> ()); FStar_TypeChecker_Env.push = (fun _85_263 -> ()); FStar_TypeChecker_Env.pop = (fun _85_265 -> ()); FStar_TypeChecker_Env.mark = (fun _85_267 -> ()); FStar_TypeChecker_Env.reset_mark = (fun _85_269 -> ()); FStar_TypeChecker_Env.commit_mark = (fun _85_271 -> ()); FStar_TypeChecker_Env.encode_modul = (fun _85_273 _85_275 -> ()); FStar_TypeChecker_Env.encode_sig = (fun _85_277 _85_279 -> ()); FStar_TypeChecker_Env.solve = (fun _85_281 _85_283 _85_285 -> ()); FStar_TypeChecker_Env.is_trivial = (fun _85_287 _85_289 -> false); FStar_TypeChecker_Env.finish = (fun _85_291 -> ()); FStar_TypeChecker_Env.refresh = (fun _85_292 -> ())}




