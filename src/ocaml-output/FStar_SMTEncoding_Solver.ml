
open Prims

type hint =
{fuel : Prims.int; ifuel : Prims.int; unsat_core : Prims.string Prims.list Prims.option; query_elapsed_time : Prims.int}


let is_Mkhint : hint  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkhint"))))


type hints =
hint Prims.option Prims.list


type hints_db =
{module_digest : Prims.string; hints : hints}


let is_Mkhints_db : hints_db  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkhints_db"))))


let recorded_hints : hints Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)


let replaying_hints : hints Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)


let format_hints_file_name : Prims.string  ->  Prims.string = (fun src_fn -> (let _174_23 = (FStar_Util.format1 "%s.hints" src_fn)
in (FStar_All.pipe_left FStar_Util.format_value_file_name _174_23)))


let initialize_hints_db = (fun src_fn force_record -> (

let _84_13 = if (FStar_Options.record_hints ()) then begin
(FStar_ST.op_Colon_Equals recorded_hints (Some ([])))
end else begin
()
end
in if (FStar_Options.use_hints ()) then begin
(

let norm_src_fn = (FStar_Util.normalize_file_path src_fn)
in (

let val_fn = (format_hints_file_name norm_src_fn)
in (match ((FStar_Util.load_value_from_file val_fn)) with
| Some (hints) -> begin
(

let expected_digest = (FStar_Util.digest_of_file norm_src_fn)
in (

let _84_20 = if (FStar_Options.hint_info ()) then begin
if (hints.module_digest = expected_digest) then begin
(FStar_Util.print1 "(%s) digest is valid; using hints db.\n" norm_src_fn)
end else begin
(FStar_Util.print1 "(%s) digest is invalid; using potentially stale hints\n" norm_src_fn)
end
end else begin
()
end
in (FStar_ST.op_Colon_Equals replaying_hints (Some (hints.hints)))))
end
| None -> begin
if (FStar_Options.hint_info ()) then begin
(FStar_Util.print1 "(%s) Unable to read hints db.\n" norm_src_fn)
end else begin
()
end
end)))
end else begin
()
end))


let finalize_hints_db : Prims.string  ->  Prims.unit = (fun src_fn -> (

let _84_27 = if (FStar_Options.record_hints ()) then begin
(

let hints = (let _174_28 = (FStar_ST.read recorded_hints)
in (FStar_Option.get _174_28))
in (

let hints_db = (let _174_29 = (FStar_Util.digest_of_file src_fn)
in {module_digest = _174_29; hints = hints})
in (

let hints_file_name = (format_hints_file_name src_fn)
in (FStar_Util.save_value_to_file hints_file_name hints_db))))
end else begin
()
end
in (

let _84_29 = (FStar_ST.op_Colon_Equals recorded_hints None)
in (FStar_ST.op_Colon_Equals replaying_hints None))))


let with_hints_db = (fun fname f -> (

let _84_33 = (initialize_hints_db fname false)
in (

let result = (f ())
in (

let _84_36 = (finalize_hints_db fname)
in result))))


let next_hint : Prims.unit  ->  hint Prims.option = (fun _84_38 -> (match (()) with
| () -> begin
(match ((FStar_ST.read replaying_hints)) with
| Some ((hd)::tl) -> begin
(

let _84_43 = (FStar_ST.op_Colon_Equals replaying_hints (Some (tl)))
in hd)
end
| _84_46 -> begin
None
end)
end))


let record_hint : hint Prims.option  ->  Prims.unit = (fun hint -> (match ((FStar_ST.read recorded_hints)) with
| Some (l) -> begin
(FStar_ST.op_Colon_Equals recorded_hints (Some ((FStar_List.append l ((hint)::[])))))
end
| _84_51 -> begin
()
end))


let ask_and_report_errors : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  ((FStar_SMTEncoding_Z3.label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun env use_fresh_z3_context all_labels prefix query suffix -> (

let _84_58 = (FStar_SMTEncoding_Z3.giveZ3 prefix)
in (

let minimum_workable_fuel = (FStar_Util.mk_ref None)
in (

let set_minimum_workable_fuel = (fun f _84_1 -> (match (_84_1) with
| [] -> begin
()
end
| errs -> begin
(match ((FStar_ST.read minimum_workable_fuel)) with
| Some (_84_67) -> begin
()
end
| None -> begin
(FStar_ST.op_Colon_Equals minimum_workable_fuel (Some ((f, errs))))
end)
end))
in (

let with_fuel = (fun label_assumptions p _84_76 -> (match (_84_76) with
| (n, i, timeout_ms) -> begin
(let _174_88 = (let _174_87 = (let _174_85 = (let _174_84 = (let _174_79 = (let _174_78 = (let _174_63 = (let _174_62 = (FStar_Util.string_of_int n)
in (let _174_61 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _174_62 _174_61)))
in FStar_SMTEncoding_Term.Caption (_174_63))
in (let _174_77 = (let _174_76 = (let _174_68 = (let _174_67 = (let _174_66 = (let _174_65 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (let _174_64 = (FStar_SMTEncoding_Term.n_fuel n)
in (_174_65, _174_64)))
in (FStar_SMTEncoding_Term.mkEq _174_66))
in (_174_67, None, None))
in FStar_SMTEncoding_Term.Assume (_174_68))
in (let _174_75 = (let _174_74 = (let _174_73 = (let _174_72 = (let _174_71 = (let _174_70 = (FStar_SMTEncoding_Term.mkApp ("MaxIFuel", []))
in (let _174_69 = (FStar_SMTEncoding_Term.n_fuel i)
in (_174_70, _174_69)))
in (FStar_SMTEncoding_Term.mkEq _174_71))
in (_174_72, None, None))
in FStar_SMTEncoding_Term.Assume (_174_73))
in (_174_74)::(p)::[])
in (_174_76)::_174_75))
in (_174_78)::_174_77))
in (FStar_List.append _174_79 label_assumptions))
in (let _174_83 = (let _174_82 = (let _174_81 = (let _174_80 = (FStar_Util.string_of_int timeout_ms)
in ("timeout", _174_80))
in FStar_SMTEncoding_Term.SetOption (_174_81))
in (_174_82)::[])
in (FStar_List.append _174_84 _174_83)))
in (FStar_List.append _174_85 ((FStar_SMTEncoding_Term.CheckSat)::[])))
in (let _174_86 = if (FStar_Options.record_hints ()) then begin
(FStar_SMTEncoding_Term.GetUnsatCore)::[]
end else begin
[]
end
in (FStar_List.append _174_87 _174_86)))
in (FStar_List.append _174_88 suffix))
end))
in (

let check = (fun p -> (

let default_timeout = ((FStar_Options.z3_timeout ()) * 1000)
in (

let default_initial_config = (let _174_92 = (FStar_Options.initial_fuel ())
in (let _174_91 = (FStar_Options.initial_ifuel ())
in (_174_92, _174_91, default_timeout)))
in (

let _84_89 = (match ((next_hint ())) with
| None -> begin
(None, default_initial_config)
end
| Some (hint) -> begin
(

let _84_86 = if (FStar_Option.isSome hint.unsat_core) then begin
(hint.unsat_core, (3 * 1000))
end else begin
(None, (60 * 1000))
end
in (match (_84_86) with
| (core, timeout) -> begin
(core, (hint.fuel, hint.ifuel, timeout))
end))
end)
in (match (_84_89) with
| (unsat_core, initial_config) -> begin
(

let alt_configs = (let _174_113 = (let _174_112 = if ((default_initial_config <> initial_config) || (FStar_Option.isSome unsat_core)) then begin
(default_initial_config)::[]
end else begin
[]
end
in (let _174_111 = (let _174_110 = if ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ())) then begin
(let _174_95 = (let _174_94 = (FStar_Options.initial_fuel ())
in (let _174_93 = (FStar_Options.max_ifuel ())
in (_174_94, _174_93, default_timeout)))
in (_174_95)::[])
end else begin
[]
end
in (let _174_109 = (let _174_108 = if (((FStar_Options.max_fuel ()) / 2) > (FStar_Options.initial_fuel ())) then begin
(let _174_98 = (let _174_97 = ((FStar_Options.max_fuel ()) / 2)
in (let _174_96 = (FStar_Options.max_ifuel ())
in (_174_97, _174_96, default_timeout)))
in (_174_98)::[])
end else begin
[]
end
in (let _174_107 = (let _174_106 = if (((FStar_Options.max_fuel ()) > (FStar_Options.initial_fuel ())) && ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ()))) then begin
(let _174_101 = (let _174_100 = (FStar_Options.max_fuel ())
in (let _174_99 = (FStar_Options.max_ifuel ())
in (_174_100, _174_99, default_timeout)))
in (_174_101)::[])
end else begin
[]
end
in (let _174_105 = (let _174_104 = if ((FStar_Options.min_fuel ()) < (FStar_Options.initial_fuel ())) then begin
(let _174_103 = (let _174_102 = (FStar_Options.min_fuel ())
in (_174_102, 1, default_timeout))
in (_174_103)::[])
end else begin
[]
end
in (_174_104)::[])
in (_174_106)::_174_105))
in (_174_108)::_174_107))
in (_174_110)::_174_109))
in (_174_112)::_174_111))
in (FStar_List.flatten _174_113))
in (

let report = (fun p errs -> (

let errs = if ((FStar_Options.detail_errors ()) && ((FStar_Options.n_cores ()) = 1)) then begin
(

let _84_101 = (match ((FStar_ST.read minimum_workable_fuel)) with
| Some (f, errs) -> begin
(f, errs)
end
| None -> begin
(let _174_119 = (let _174_118 = (FStar_Options.min_fuel ())
in (_174_118, 1, default_timeout))
in (_174_119, errs))
end)
in (match (_84_101) with
| (min_fuel, potential_errors) -> begin
(

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref None)
in (

let _84_106 = (let _174_123 = (with_fuel label_assumptions p min_fuel)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context None all_labels _174_123 (fun r -> (FStar_ST.op_Colon_Equals res (Some (r))))))
in (let _174_124 = (FStar_ST.read res)
in (FStar_Option.get _174_124)))))
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
| _84_111 -> begin
errs
end)
in (

let _84_113 = (record_hint None)
in (

let _84_115 = if ((FStar_Options.print_fuels ()) || (FStar_Options.hint_info ())) then begin
(let _174_130 = (let _174_125 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _174_125))
in (let _174_129 = (let _174_126 = (FStar_Options.max_fuel ())
in (FStar_All.pipe_right _174_126 FStar_Util.string_of_int))
in (let _174_128 = (let _174_127 = (FStar_Options.max_ifuel ())
in (FStar_All.pipe_right _174_127 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _174_130 _174_129 _174_128))))
end else begin
()
end
in (

let _84_122 = (let _174_132 = (FStar_All.pipe_right errs (FStar_List.map (fun _84_121 -> (match (_84_121) with
| (_84_118, x, y) -> begin
(x, y)
end))))
in (FStar_TypeChecker_Errors.add_errors env _174_132))
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
| (_84_138, FStar_Util.Inr (_84_140)) -> begin
FStar_Util.Inr (errs)
end))
in (

let rec try_alt_configs = (fun prev_f p errs cfgs -> (

let _84_149 = (set_minimum_workable_fuel prev_f errs)
in (match (cfgs) with
| [] -> begin
(report p errs)
end
| (mi)::[] -> begin
(match (errs) with
| [] -> begin
(let _174_150 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context None all_labels _174_150 (cb false mi p [])))
end
| _84_156 -> begin
(

let _84_157 = (set_minimum_workable_fuel prev_f errs)
in (report p errs))
end)
end
| (mi)::tl -> begin
(let _174_152 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context None all_labels _174_152 (fun _84_164 -> (match (_84_164) with
| (result, elapsed_time) -> begin
(cb false mi p tl ((use_errors errs result), elapsed_time))
end))))
end)))
and cb = (fun refresh _84_169 p alt _84_174 -> (match ((_84_169, _84_174)) with
| ((prev_fuel, prev_ifuel, timeout), (result, elapsed_time)) -> begin
(

let _84_175 = if refresh then begin
(FStar_SMTEncoding_Z3.refresh ())
end else begin
()
end
in (match (result) with
| FStar_Util.Inl (unsat_core) -> begin
(

let hint = {fuel = prev_fuel; ifuel = prev_ifuel; unsat_core = unsat_core; query_elapsed_time = elapsed_time}
in (

let _84_180 = (record_hint (Some (hint)))
in if ((FStar_Options.print_fuels ()) || (FStar_Options.hint_info ())) then begin
(let _174_162 = (let _174_158 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _174_158))
in (let _174_161 = (FStar_Util.string_of_int elapsed_time)
in (let _174_160 = (FStar_Util.string_of_int prev_fuel)
in (let _174_159 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print4 "(%s) Query succeeded in %s milliseconds with fuel %s and ifuel %s\n" _174_162 _174_161 _174_160 _174_159)))))
end else begin
()
end))
end
| FStar_Util.Inr (errs) -> begin
(

let _84_184 = if ((FStar_Options.print_fuels ()) || (FStar_Options.hint_info ())) then begin
(let _174_167 = (let _174_163 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _174_163))
in (let _174_166 = (FStar_Util.string_of_int elapsed_time)
in (let _174_165 = (FStar_Util.string_of_int prev_fuel)
in (let _174_164 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print4 "(%s) Query failed in %s milliseconds with fuel %s and ifuel %s ... retrying \n" _174_167 _174_166 _174_165 _174_164)))))
end else begin
()
end
in (try_alt_configs (prev_fuel, prev_ifuel, timeout) p errs alt))
end))
end))
in (

let _84_186 = if (FStar_Option.isSome unsat_core) then begin
(FStar_SMTEncoding_Z3.refresh ())
end else begin
()
end
in (let _174_170 = (with_fuel [] p initial_config)
in (let _174_169 = (let _174_168 = (FStar_Option.isSome unsat_core)
in (cb _174_168 initial_config p alt_configs))
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context unsat_core all_labels _174_170 _174_169))))))))
end)))))
in (

let process_query = (fun q -> if ((FStar_Options.split_cases ()) > 0) then begin
(

let _84_192 = (let _174_176 = (FStar_Options.split_cases ())
in (FStar_SMTEncoding_SplitQueryCases.can_handle_query _174_176 q))
in (match (_84_192) with
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

let _84_196 = (let _174_195 = (let _174_194 = (let _174_193 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _174_193))
in (FStar_Util.format1 "Starting query at %s" _174_194))
in (FStar_SMTEncoding_Encode.push _174_195))
in (

let _84_202 = (FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv q)
in (match (_84_202) with
| (prefix, labels, qry, suffix) -> begin
(

let pop = (fun _84_204 -> (match (()) with
| () -> begin
(let _174_200 = (let _174_199 = (let _174_198 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _174_198))
in (FStar_Util.format1 "Ending query at %s" _174_199))
in (FStar_SMTEncoding_Encode.pop _174_200))
end))
in (match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _84_211); FStar_SMTEncoding_Term.hash = _84_208; FStar_SMTEncoding_Term.freevars = _84_206}, _84_216, _84_218) -> begin
(

let _84_221 = (pop ())
in ())
end
| _84_224 when tcenv.FStar_TypeChecker_Env.admit -> begin
(

let _84_225 = (pop ())
in ())
end
| FStar_SMTEncoding_Term.Assume (q, _84_229, _84_231) -> begin
(

let _84_234 = (ask_and_report_errors tcenv false labels prefix qry suffix)
in (pop ()))
end
| _84_237 -> begin
(FStar_All.failwith "Impossible")
end))
end))))


let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = FStar_SMTEncoding_Encode.init; FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push; FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop; FStar_TypeChecker_Env.mark = FStar_SMTEncoding_Encode.mark; FStar_TypeChecker_Env.reset_mark = FStar_SMTEncoding_Encode.reset_mark; FStar_TypeChecker_Env.commit_mark = FStar_SMTEncoding_Encode.commit_mark; FStar_TypeChecker_Env.encode_modul = FStar_SMTEncoding_Encode.encode_modul; FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig; FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.is_trivial = FStar_SMTEncoding_Encode.is_trivial; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}


let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun _84_238 -> ()); FStar_TypeChecker_Env.push = (fun _84_240 -> ()); FStar_TypeChecker_Env.pop = (fun _84_242 -> ()); FStar_TypeChecker_Env.mark = (fun _84_244 -> ()); FStar_TypeChecker_Env.reset_mark = (fun _84_246 -> ()); FStar_TypeChecker_Env.commit_mark = (fun _84_248 -> ()); FStar_TypeChecker_Env.encode_modul = (fun _84_250 _84_252 -> ()); FStar_TypeChecker_Env.encode_sig = (fun _84_254 _84_256 -> ()); FStar_TypeChecker_Env.solve = (fun _84_258 _84_260 _84_262 -> ()); FStar_TypeChecker_Env.is_trivial = (fun _84_264 _84_266 -> false); FStar_TypeChecker_Env.finish = (fun _84_268 -> ()); FStar_TypeChecker_Env.refresh = (fun _84_269 -> ())}




