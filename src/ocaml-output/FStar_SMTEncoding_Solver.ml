
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

let _84_10 = (FStar_ST.op_Colon_Equals hint_stats [])
in (

let _84_12 = if (FStar_Options.record_hints ()) then begin
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

let _84_19 = if (FStar_Options.hint_info ()) then begin
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

let _84_26 = if (FStar_Options.record_hints ()) then begin
(

let hints = (let _174_20 = (FStar_ST.read recorded_hints)
in (FStar_Option.get _174_20))
in (

let hints_db = (let _174_21 = (FStar_Util.digest_of_file src_filename)
in {FStar_Util.module_digest = _174_21; FStar_Util.hints = hints})
in (

let hints_file_name = (format_hints_file_name src_filename)
in (FStar_Util.save_value_to_file hints_file_name hints_db))))
end else begin
()
end
in (

let _84_34 = if (FStar_Options.hint_info ()) then begin
(

let stats = (let _174_22 = (FStar_ST.read hint_stats)
in (FStar_All.pipe_right _174_22 FStar_List.rev))
in (FStar_All.pipe_right stats (FStar_List.iter (fun s -> (match (s.replay_result) with
| FStar_Util.Inl (_unsat_core) -> begin
(let _174_25 = (FStar_Range.string_of_range s.source_location)
in (let _174_24 = (FStar_Util.string_of_int s.elapsed_time)
in (FStar_Util.print2 "Hint-info (%s): Replay succeeded in %s milliseconds\n" _174_25 _174_24)))
end
| FStar_Util.Inr (_error) -> begin
(let _174_27 = (FStar_Range.string_of_range s.source_location)
in (let _174_26 = (FStar_Util.string_of_int s.elapsed_time)
in (FStar_Util.print2 "Hint-info (%s): Replay failed in %s milliseconds\n" _174_27 _174_26)))
end)))))
end else begin
()
end
in (

let _84_36 = (FStar_ST.op_Colon_Equals recorded_hints None)
in (

let _84_38 = (FStar_ST.op_Colon_Equals replaying_hints None)
in (FStar_ST.op_Colon_Equals hint_stats []))))))


let with_hints_db = (fun fname f -> (

let _84_42 = (initialize_hints_db fname false)
in (

let result = (f ())
in (

let _84_45 = (finalize_hints_db fname)
in result))))


let next_hint : Prims.unit  ->  FStar_Util.hint Prims.option = (fun _84_47 -> (match (()) with
| () -> begin
(match ((FStar_ST.read replaying_hints)) with
| Some ((hd)::tl) -> begin
(

let _84_52 = (FStar_ST.op_Colon_Equals replaying_hints (Some (tl)))
in hd)
end
| _84_55 -> begin
None
end)
end))


let record_hint : FStar_Util.hint Prims.option  ->  Prims.unit = (fun hint -> (match ((FStar_ST.read recorded_hints)) with
| Some (l) -> begin
(FStar_ST.op_Colon_Equals recorded_hints (Some ((FStar_List.append l ((hint)::[])))))
end
| _84_60 -> begin
()
end))


let record_hint_stat : FStar_Util.hint Prims.option  ->  z3_result  ->  Prims.int  ->  FStar_Range.range  ->  Prims.unit = (fun h res time r -> (

let s = {hint = h; replay_result = res; elapsed_time = time; source_location = r}
in (let _174_46 = (let _174_45 = (FStar_ST.read hint_stats)
in (s)::_174_45)
in (FStar_ST.op_Colon_Equals hint_stats _174_46))))


let ask_and_report_errors : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  ((FStar_SMTEncoding_Z3.label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun env use_fresh_z3_context all_labels prefix query suffix -> (

let _84_72 = (FStar_SMTEncoding_Z3.giveZ3 prefix)
in (

let minimum_workable_fuel = (FStar_Util.mk_ref None)
in (

let set_minimum_workable_fuel = (fun f _84_1 -> (match (_84_1) with
| [] -> begin
()
end
| errs -> begin
(match ((FStar_ST.read minimum_workable_fuel)) with
| Some (_84_81) -> begin
()
end
| None -> begin
(FStar_ST.op_Colon_Equals minimum_workable_fuel (Some ((f, errs))))
end)
end))
in (

let with_fuel = (fun label_assumptions p _84_90 -> (match (_84_90) with
| (n, i, timeout_ms) -> begin
(let _174_96 = (let _174_95 = (let _174_93 = (let _174_92 = (let _174_87 = (let _174_86 = (let _174_71 = (let _174_70 = (FStar_Util.string_of_int n)
in (let _174_69 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _174_70 _174_69)))
in FStar_SMTEncoding_Term.Caption (_174_71))
in (let _174_85 = (let _174_84 = (let _174_76 = (let _174_75 = (let _174_74 = (let _174_73 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (let _174_72 = (FStar_SMTEncoding_Term.n_fuel n)
in (_174_73, _174_72)))
in (FStar_SMTEncoding_Term.mkEq _174_74))
in (_174_75, None, None))
in FStar_SMTEncoding_Term.Assume (_174_76))
in (let _174_83 = (let _174_82 = (let _174_81 = (let _174_80 = (let _174_79 = (let _174_78 = (FStar_SMTEncoding_Term.mkApp ("MaxIFuel", []))
in (let _174_77 = (FStar_SMTEncoding_Term.n_fuel i)
in (_174_78, _174_77)))
in (FStar_SMTEncoding_Term.mkEq _174_79))
in (_174_80, None, None))
in FStar_SMTEncoding_Term.Assume (_174_81))
in (_174_82)::(p)::[])
in (_174_84)::_174_83))
in (_174_86)::_174_85))
in (FStar_List.append _174_87 label_assumptions))
in (let _174_91 = (let _174_90 = (let _174_89 = (let _174_88 = (FStar_Util.string_of_int timeout_ms)
in ("timeout", _174_88))
in FStar_SMTEncoding_Term.SetOption (_174_89))
in (_174_90)::[])
in (FStar_List.append _174_92 _174_91)))
in (FStar_List.append _174_93 ((FStar_SMTEncoding_Term.CheckSat)::[])))
in (let _174_94 = if (FStar_Options.record_hints ()) then begin
(FStar_SMTEncoding_Term.GetUnsatCore)::[]
end else begin
[]
end
in (FStar_List.append _174_95 _174_94)))
in (FStar_List.append _174_96 suffix))
end))
in (

let check = (fun p -> (

let default_timeout = ((FStar_Options.z3_timeout ()) * 1000)
in (

let default_initial_config = (let _174_100 = (FStar_Options.initial_fuel ())
in (let _174_99 = (FStar_Options.initial_ifuel ())
in (_174_100, _174_99, default_timeout)))
in (

let hint_opt = (next_hint ())
in (

let _84_104 = (match (hint_opt) with
| None -> begin
(None, default_initial_config)
end
| Some (hint) -> begin
(

let _84_101 = if (FStar_Option.isSome hint.FStar_Util.unsat_core) then begin
(hint.FStar_Util.unsat_core, (3 * 1000))
end else begin
(None, (60 * 1000))
end
in (match (_84_101) with
| (core, timeout) -> begin
(core, (hint.FStar_Util.fuel, hint.FStar_Util.ifuel, timeout))
end))
end)
in (match (_84_104) with
| (unsat_core, initial_config) -> begin
(

let alt_configs = (let _174_121 = (let _174_120 = if ((default_initial_config <> initial_config) || (FStar_Option.isSome unsat_core)) then begin
(default_initial_config)::[]
end else begin
[]
end
in (let _174_119 = (let _174_118 = if ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ())) then begin
(let _174_103 = (let _174_102 = (FStar_Options.initial_fuel ())
in (let _174_101 = (FStar_Options.max_ifuel ())
in (_174_102, _174_101, default_timeout)))
in (_174_103)::[])
end else begin
[]
end
in (let _174_117 = (let _174_116 = if (((FStar_Options.max_fuel ()) / 2) > (FStar_Options.initial_fuel ())) then begin
(let _174_106 = (let _174_105 = ((FStar_Options.max_fuel ()) / 2)
in (let _174_104 = (FStar_Options.max_ifuel ())
in (_174_105, _174_104, default_timeout)))
in (_174_106)::[])
end else begin
[]
end
in (let _174_115 = (let _174_114 = if (((FStar_Options.max_fuel ()) > (FStar_Options.initial_fuel ())) && ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ()))) then begin
(let _174_109 = (let _174_108 = (FStar_Options.max_fuel ())
in (let _174_107 = (FStar_Options.max_ifuel ())
in (_174_108, _174_107, default_timeout)))
in (_174_109)::[])
end else begin
[]
end
in (let _174_113 = (let _174_112 = if ((FStar_Options.min_fuel ()) < (FStar_Options.initial_fuel ())) then begin
(let _174_111 = (let _174_110 = (FStar_Options.min_fuel ())
in (_174_110, 1, default_timeout))
in (_174_111)::[])
end else begin
[]
end
in (_174_112)::[])
in (_174_114)::_174_113))
in (_174_116)::_174_115))
in (_174_118)::_174_117))
in (_174_120)::_174_119))
in (FStar_List.flatten _174_121))
in (

let report = (fun p errs -> (

let errs = if ((FStar_Options.detail_errors ()) && ((FStar_Options.n_cores ()) = 1)) then begin
(

let _84_116 = (match ((FStar_ST.read minimum_workable_fuel)) with
| Some (f, errs) -> begin
(f, errs)
end
| None -> begin
(let _174_127 = (let _174_126 = (FStar_Options.min_fuel ())
in (_174_126, 1, default_timeout))
in (_174_127, errs))
end)
in (match (_84_116) with
| (min_fuel, potential_errors) -> begin
(

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref None)
in (

let _84_121 = (let _174_131 = (with_fuel label_assumptions p min_fuel)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context None all_labels _174_131 (fun r -> (FStar_ST.op_Colon_Equals res (Some (r))))))
in (let _174_132 = (FStar_ST.read res)
in (FStar_Option.get _174_132)))))
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
| _84_126 -> begin
errs
end)
in (

let _84_128 = (record_hint None)
in (

let _84_130 = if (FStar_Options.print_fuels ()) then begin
(let _174_138 = (let _174_133 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _174_133))
in (let _174_137 = (let _174_134 = (FStar_Options.max_fuel ())
in (FStar_All.pipe_right _174_134 FStar_Util.string_of_int))
in (let _174_136 = (let _174_135 = (FStar_Options.max_ifuel ())
in (FStar_All.pipe_right _174_135 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _174_138 _174_137 _174_136))))
end else begin
()
end
in (

let _84_137 = (let _174_140 = (FStar_All.pipe_right errs (FStar_List.map (fun _84_136 -> (match (_84_136) with
| (_84_133, x, y) -> begin
(x, y)
end))))
in (FStar_TypeChecker_Errors.add_errors env _174_140))
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
| (_84_153, FStar_Util.Inr (_84_155)) -> begin
FStar_Util.Inr (errs)
end))
in (

let rec try_alt_configs = (fun prev_f p errs cfgs -> (

let _84_164 = (set_minimum_workable_fuel prev_f errs)
in (match (cfgs) with
| [] -> begin
(report p errs)
end
| (mi)::[] -> begin
(match (errs) with
| [] -> begin
(let _174_158 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context None all_labels _174_158 (cb false mi p [])))
end
| _84_171 -> begin
(

let _84_172 = (set_minimum_workable_fuel prev_f errs)
in (report p errs))
end)
end
| (mi)::tl -> begin
(let _174_160 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context None all_labels _174_160 (fun _84_179 -> (match (_84_179) with
| (result, elapsed_time) -> begin
(cb false mi p tl ((use_errors errs result), elapsed_time))
end))))
end)))
and cb = (fun used_hint _84_184 p alt _84_189 -> (match ((_84_184, _84_189)) with
| ((prev_fuel, prev_ifuel, timeout), (result, elapsed_time)) -> begin
(

let _84_192 = if used_hint then begin
(

let _84_190 = (FStar_SMTEncoding_Z3.refresh ())
in (let _174_166 = (FStar_TypeChecker_Env.get_range env)
in (record_hint_stat hint_opt result elapsed_time _174_166)))
end else begin
()
end
in (match (result) with
| FStar_Util.Inl (unsat_core) -> begin
(

let hint = {FStar_Util.fuel = prev_fuel; FStar_Util.ifuel = prev_ifuel; FStar_Util.unsat_core = unsat_core; FStar_Util.query_elapsed_time = elapsed_time}
in (

let _84_197 = (record_hint (Some (hint)))
in if (FStar_Options.print_fuels ()) then begin
(let _174_171 = (let _174_167 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _174_167))
in (let _174_170 = (FStar_Util.string_of_int elapsed_time)
in (let _174_169 = (FStar_Util.string_of_int prev_fuel)
in (let _174_168 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print4 "(%s) Query succeeded in %s milliseconds with fuel %s and ifuel %s\n" _174_171 _174_170 _174_169 _174_168)))))
end else begin
()
end))
end
| FStar_Util.Inr (errs) -> begin
(

let _84_201 = if (FStar_Options.print_fuels ()) then begin
(let _174_176 = (let _174_172 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _174_172))
in (let _174_175 = (FStar_Util.string_of_int elapsed_time)
in (let _174_174 = (FStar_Util.string_of_int prev_fuel)
in (let _174_173 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print4 "(%s) Query failed in %s milliseconds with fuel %s and ifuel %s ... retrying \n" _174_176 _174_175 _174_174 _174_173)))))
end else begin
()
end
in (try_alt_configs (prev_fuel, prev_ifuel, timeout) p errs alt))
end))
end))
in (

let _84_203 = if (FStar_Option.isSome unsat_core) then begin
(FStar_SMTEncoding_Z3.refresh ())
end else begin
()
end
in (let _174_179 = (with_fuel [] p initial_config)
in (let _174_178 = (let _174_177 = (FStar_Option.isSome unsat_core)
in (cb _174_177 initial_config p alt_configs))
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context unsat_core all_labels _174_179 _174_178))))))))
end))))))
in (

let process_query = (fun q -> if ((FStar_Options.split_cases ()) > 0) then begin
(

let _84_209 = (let _174_185 = (FStar_Options.split_cases ())
in (FStar_SMTEncoding_SplitQueryCases.can_handle_query _174_185 q))
in (match (_84_209) with
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

let _84_213 = (let _174_204 = (let _174_203 = (let _174_202 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _174_202))
in (FStar_Util.format1 "Starting query at %s" _174_203))
in (FStar_SMTEncoding_Encode.push _174_204))
in (

let _84_219 = (FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv q)
in (match (_84_219) with
| (prefix, labels, qry, suffix) -> begin
(

let pop = (fun _84_221 -> (match (()) with
| () -> begin
(let _174_209 = (let _174_208 = (let _174_207 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _174_207))
in (FStar_Util.format1 "Ending query at %s" _174_208))
in (FStar_SMTEncoding_Encode.pop _174_209))
end))
in (match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _84_228); FStar_SMTEncoding_Term.hash = _84_225; FStar_SMTEncoding_Term.freevars = _84_223}, _84_233, _84_235) -> begin
(

let _84_238 = (pop ())
in ())
end
| _84_241 when tcenv.FStar_TypeChecker_Env.admit -> begin
(

let _84_242 = (pop ())
in ())
end
| FStar_SMTEncoding_Term.Assume (q, _84_246, _84_248) -> begin
(

let _84_251 = (ask_and_report_errors tcenv false labels prefix qry suffix)
in (pop ()))
end
| _84_254 -> begin
(FStar_All.failwith "Impossible")
end))
end))))


let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = FStar_SMTEncoding_Encode.init; FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push; FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop; FStar_TypeChecker_Env.mark = FStar_SMTEncoding_Encode.mark; FStar_TypeChecker_Env.reset_mark = FStar_SMTEncoding_Encode.reset_mark; FStar_TypeChecker_Env.commit_mark = FStar_SMTEncoding_Encode.commit_mark; FStar_TypeChecker_Env.encode_modul = FStar_SMTEncoding_Encode.encode_modul; FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig; FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.is_trivial = FStar_SMTEncoding_Encode.is_trivial; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}


let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun _84_255 -> ()); FStar_TypeChecker_Env.push = (fun _84_257 -> ()); FStar_TypeChecker_Env.pop = (fun _84_259 -> ()); FStar_TypeChecker_Env.mark = (fun _84_261 -> ()); FStar_TypeChecker_Env.reset_mark = (fun _84_263 -> ()); FStar_TypeChecker_Env.commit_mark = (fun _84_265 -> ()); FStar_TypeChecker_Env.encode_modul = (fun _84_267 _84_269 -> ()); FStar_TypeChecker_Env.encode_sig = (fun _84_271 _84_273 -> ()); FStar_TypeChecker_Env.solve = (fun _84_275 _84_277 _84_279 -> ()); FStar_TypeChecker_Env.is_trivial = (fun _84_281 _84_283 -> false); FStar_TypeChecker_Env.finish = (fun _84_285 -> ()); FStar_TypeChecker_Env.refresh = (fun _84_286 -> ())}




