
let process_args = (fun _65_1 -> (match (()) with
| () -> begin
(let file_list = (Microsoft_FStar_Util.mk_ref [])
in (let res = (let _131_6 = (Microsoft_FStar_Options.specs ())
in (Microsoft_FStar_Getopt.parse_cmdline _131_6 (fun i -> (let _131_5 = (let _131_4 = (ST.read file_list)
in (Microsoft_FStar_List.append _131_4 ((i)::[])))
in (ST.op_Colon_Equals file_list _131_5)))))
in (let _65_8 = (match (res) with
| Microsoft_FStar_Getopt.GoOn -> begin
(let _131_7 = (Microsoft_FStar_Options.set_fstar_home ())
in (Prims.ignore _131_7))
end
| _65_7 -> begin
()
end)
in (let _131_8 = (ST.read file_list)
in (res, _131_8)))))
end))

let cleanup = (fun _65_10 -> (match (()) with
| () -> begin
(Microsoft_FStar_Util.kill_all ())
end))

let has_prims_cache = (fun l -> (Microsoft_FStar_List.mem "Prims.cache" l))

let tc_prims = (fun _65_12 -> (match (()) with
| () -> begin
(let solver = (match ((ST.read Microsoft_FStar_Options.verify)) with
| true -> begin
Microsoft_FStar_ToSMT_Encode.solver
end
| false -> begin
Microsoft_FStar_ToSMT_Encode.dummy
end)
in (let env = (Microsoft_FStar_Tc_Env.initial_env solver Microsoft_FStar_Absyn_Const.prims_lid)
in (let _65_15 = (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.init env)
in (let p = (Microsoft_FStar_Options.prims ())
in (let _65_20 = (let _131_15 = (Microsoft_FStar_Parser_DesugarEnv.empty_env ())
in (Microsoft_FStar_Parser_Driver.parse_file _131_15 p))
in (match (_65_20) with
| (dsenv, prims_mod) -> begin
(let _65_23 = (let _131_16 = (Microsoft_FStar_List.hd prims_mod)
in (Microsoft_FStar_Tc_Tc.check_module env _131_16))
in (match (_65_23) with
| (prims_mod, env) -> begin
(prims_mod, dsenv, env)
end))
end))))))
end))

let report_errors = (fun nopt -> (let errs = (match (nopt) with
| None -> begin
(Microsoft_FStar_Tc_Errors.get_err_count ())
end
| Some (n) -> begin
n
end)
in (match ((errs > 0)) with
| true -> begin
(let _65_29 = (let _131_19 = (Microsoft_FStar_Util.string_of_int errs)
in (Microsoft_FStar_Util.fprint1 "Error: %s errors were reported (see above)\n" _131_19))
in (All.exit 1))
end
| false -> begin
()
end)))

let tc_one_file = (fun dsenv env fn -> (let _65_36 = (Microsoft_FStar_Parser_Driver.parse_file dsenv fn)
in (match (_65_36) with
| (dsenv, fmods) -> begin
(let _65_46 = (All.pipe_right fmods (Microsoft_FStar_List.fold_left (fun _65_39 m -> (match (_65_39) with
| (env, all_mods) -> begin
(let _65_43 = (Microsoft_FStar_Tc_Tc.check_module env m)
in (match (_65_43) with
| (ms, env) -> begin
(env, (Microsoft_FStar_List.append ms all_mods))
end))
end)) (env, [])))
in (match (_65_46) with
| (env, all_mods) -> begin
(dsenv, env, (Microsoft_FStar_List.rev all_mods))
end))
end)))

let tc_one_fragment = (fun curmod dsenv env frag -> (All.try_with (fun _65_52 -> (match (()) with
| () -> begin
(match ((Microsoft_FStar_Parser_Driver.parse_fragment curmod dsenv frag)) with
| Microsoft_FStar_Util.Inl (dsenv, modul) -> begin
(let env = (match (curmod) with
| None -> begin
env
end
| Some (_65_73) -> begin
(Prims.raise (Microsoft_FStar_Absyn_Syntax.Err ("Interactive mode only supports a single module at the top-level")))
end)
in (let _65_79 = (Microsoft_FStar_Tc_Tc.tc_partial_modul env modul)
in (match (_65_79) with
| (modul, npds, env) -> begin
Some ((Some ((modul, npds)), dsenv, env))
end)))
end
| Microsoft_FStar_Util.Inr (dsenv, decls) -> begin
(match (curmod) with
| None -> begin
(All.failwith "Fragment without an enclosing module")
end
| Some (modul, npds) -> begin
(let _65_92 = (Microsoft_FStar_Tc_Tc.tc_more_partial_modul env modul decls)
in (match (_65_92) with
| (modul, npds', env) -> begin
Some ((Some ((modul, (Microsoft_FStar_List.append npds npds'))), dsenv, env))
end))
end)
end)
end)) (fun _65_51 -> (match (_65_51) with
| Microsoft_FStar_Absyn_Syntax.Error (msg, r) -> begin
(let _65_58 = (Microsoft_FStar_Tc_Errors.add_errors env (((msg, r))::[]))
in None)
end
| Microsoft_FStar_Absyn_Syntax.Err (msg) -> begin
(let _65_62 = (Microsoft_FStar_Tc_Errors.add_errors env (((msg, Microsoft_FStar_Absyn_Syntax.dummyRange))::[]))
in None)
end
| e -> begin
(Prims.raise e)
end))))

type input_chunks =
| Push of Prims.string
| Pop of Prims.string
| Code of (Prims.string * (Prims.string * Prims.string))

let is_Push = (fun _discr_ -> (match (_discr_) with
| Push (_) -> begin
true
end
| _ -> begin
false
end))

let is_Pop = (fun _discr_ -> (match (_discr_) with
| Pop (_) -> begin
true
end
| _ -> begin
false
end))

let is_Code = (fun _discr_ -> (match (_discr_) with
| Code (_) -> begin
true
end
| _ -> begin
false
end))

let ___Push____0 = (fun projectee -> (match (projectee) with
| Push (_65_95) -> begin
_65_95
end))

let ___Pop____0 = (fun projectee -> (match (projectee) with
| Pop (_65_98) -> begin
_65_98
end))

let ___Code____0 = (fun projectee -> (match (projectee) with
| Code (_65_101) -> begin
_65_101
end))

type stack_elt =
((Microsoft_FStar_Absyn_Syntax.modul * Microsoft_FStar_Absyn_Syntax.sigelt Prims.list) Prims.option * Microsoft_FStar_Parser_DesugarEnv.env * Microsoft_FStar_Tc_Env.env)

type stack =
stack_elt Prims.list

let interactive_mode = (fun dsenv env -> (let should_log = ((ST.read Microsoft_FStar_Options.debug) <> [])
in (let log = (match (should_log) with
| true -> begin
(let transcript = (Microsoft_FStar_Util.open_file_for_writing "transcript")
in (fun line -> (let _65_107 = (Microsoft_FStar_Util.append_to_file transcript line)
in (Microsoft_FStar_Util.flush_file transcript))))
end
| false -> begin
(fun line -> ())
end)
in (let _65_111 = (match ((let _131_87 = (ST.read Microsoft_FStar_Options.codegen)
in (Option.isSome _131_87))) with
| true -> begin
(Microsoft_FStar_Util.print_string "Warning: Code-generation is not supported in interactive mode, ignoring the codegen flag")
end
| false -> begin
()
end)
in (let chunk = (Microsoft_FStar_Util.new_string_builder ())
in (let stdin = (Microsoft_FStar_Util.open_stdin ())
in (let rec fill_chunk = (fun _65_116 -> (match (()) with
| () -> begin
(let line = (match ((Microsoft_FStar_Util.read_line stdin)) with
| None -> begin
(All.exit 0)
end
| Some (l) -> begin
l
end)
in (let _65_121 = (log line)
in (let l = (Microsoft_FStar_Util.trim_string line)
in (match ((Microsoft_FStar_Util.starts_with l "#end")) with
| true -> begin
(let responses = (match ((Microsoft_FStar_Util.split l " ")) with
| _65_127::ok::fail::[] -> begin
(ok, fail)
end
| _65_130 -> begin
("ok", "fail")
end)
in (let str = (Microsoft_FStar_Util.string_of_string_builder chunk)
in (let _65_133 = (Microsoft_FStar_Util.clear_string_builder chunk)
in Code ((str, responses)))))
end
| false -> begin
(match ((Microsoft_FStar_Util.starts_with l "#pop")) with
| true -> begin
(let _65_135 = (Microsoft_FStar_Util.clear_string_builder chunk)
in Pop (l))
end
| false -> begin
(match ((Microsoft_FStar_Util.starts_with l "#push")) with
| true -> begin
(let _65_137 = (Microsoft_FStar_Util.clear_string_builder chunk)
in Push (l))
end
| false -> begin
(match ((l = "#finish")) with
| true -> begin
(All.exit 0)
end
| false -> begin
(let _65_139 = (Microsoft_FStar_Util.string_builder_append chunk line)
in (let _65_141 = (Microsoft_FStar_Util.string_builder_append chunk "\n")
in (fill_chunk ())))
end)
end)
end)
end))))
end))
in (let rec go = (fun stack curmod dsenv env -> (match ((fill_chunk ())) with
| Pop (msg) -> begin
(let _65_150 = (let _131_98 = (Microsoft_FStar_Tc_Env.pop env msg)
in (All.pipe_right _131_98 Prims.ignore))
in (let _65_152 = (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.refresh ())
in (let _65_154 = (let _131_99 = (Microsoft_FStar_Options.reset_options ())
in (All.pipe_right _131_99 Prims.ignore))
in (let _65_165 = (match (stack) with
| [] -> begin
(All.failwith "Too many pops")
end
| hd::tl -> begin
(hd, tl)
end)
in (match (_65_165) with
| ((curmod, dsenv, env), stack) -> begin
(go stack curmod dsenv env)
end)))))
end
| Push (msg) -> begin
(let stack = ((curmod, dsenv, env))::stack
in (let dsenv = (Microsoft_FStar_Parser_DesugarEnv.push dsenv)
in (let env = (Microsoft_FStar_Tc_Env.push env msg)
in (go stack curmod dsenv env))))
end
| Code (text, (ok, fail)) -> begin
(let mark = (fun dsenv env -> (let dsenv = (Microsoft_FStar_Parser_DesugarEnv.mark dsenv)
in (let env = (Microsoft_FStar_Tc_Env.mark env)
in (dsenv, env))))
in (let reset_mark = (fun dsenv env -> (let dsenv = (Microsoft_FStar_Parser_DesugarEnv.reset_mark dsenv)
in (let env = (Microsoft_FStar_Tc_Env.reset_mark env)
in (dsenv, env))))
in (let commit_mark = (fun dsenv env -> (let dsenv = (Microsoft_FStar_Parser_DesugarEnv.commit_mark dsenv)
in (let env = (Microsoft_FStar_Tc_Env.commit_mark env)
in (dsenv, env))))
in (let fail = (fun curmod dsenv_mark env_mark -> (let _65_196 = (let _131_118 = (Microsoft_FStar_Tc_Errors.report_all ())
in (All.pipe_right _131_118 Prims.ignore))
in (let _65_198 = (ST.op_Colon_Equals Microsoft_FStar_Tc_Errors.num_errs 0)
in (let _65_200 = (Microsoft_FStar_Util.fprint1 "%s\n" fail)
in (let _65_204 = (reset_mark dsenv_mark env_mark)
in (match (_65_204) with
| (dsenv, env) -> begin
(go stack curmod dsenv env)
end))))))
in (let _65_207 = (mark dsenv env)
in (match (_65_207) with
| (dsenv_mark, env_mark) -> begin
(let res = (tc_one_fragment curmod dsenv_mark env_mark text)
in (match (res) with
| Some (curmod, dsenv, env) -> begin
(match (((ST.read Microsoft_FStar_Tc_Errors.num_errs) = 0)) with
| true -> begin
(let _65_214 = (Microsoft_FStar_Util.fprint1 "\n%s\n" ok)
in (let _65_218 = (commit_mark dsenv env)
in (match (_65_218) with
| (dsenv, env) -> begin
(go stack curmod dsenv env)
end)))
end
| false -> begin
(fail curmod dsenv_mark env_mark)
end)
end
| _65_220 -> begin
(fail curmod dsenv_mark env_mark)
end))
end))))))
end))
in (go [] None dsenv env)))))))))

let batch_mode_tc = (fun filenames -> (let _65_225 = (tc_prims ())
in (match (_65_225) with
| (prims_mod, dsenv, env) -> begin
(let _65_240 = (All.pipe_right filenames (Microsoft_FStar_List.fold_left (fun _65_229 f -> (match (_65_229) with
| (all_mods, dsenv, env) -> begin
(let _65_231 = (Microsoft_FStar_Absyn_Util.reset_gensym ())
in (let _65_236 = (tc_one_file dsenv env f)
in (match (_65_236) with
| (dsenv, env, ms) -> begin
((Microsoft_FStar_List.append all_mods ms), dsenv, env)
end)))
end)) (prims_mod, dsenv, env)))
in (match (_65_240) with
| (all_mods, dsenv, env) -> begin
(let _65_241 = (match (((ST.read Microsoft_FStar_Options.interactive) && ((Microsoft_FStar_Tc_Errors.get_err_count ()) = 0))) with
| true -> begin
(env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.refresh ())
end
| false -> begin
(env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.finish ())
end)
in (all_mods, dsenv, env))
end))
end)))

let finished_message = (fun fmods -> (match ((not ((ST.read Microsoft_FStar_Options.silent)))) with
| true -> begin
(let msg = (match ((ST.read Microsoft_FStar_Options.verify)) with
| true -> begin
"Verifying"
end
| false -> begin
(match ((ST.read Microsoft_FStar_Options.pretype)) with
| true -> begin
"Lax type-checked"
end
| false -> begin
"Parsed and desugared"
end)
end)
in (let _65_246 = (All.pipe_right fmods (Microsoft_FStar_List.iter (fun m -> (match ((Microsoft_FStar_Options.should_verify m.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str)) with
| true -> begin
(let _131_127 = (let _131_126 = (Microsoft_FStar_Absyn_Syntax.text_of_lid m.Microsoft_FStar_Absyn_Syntax.name)
in (Microsoft_FStar_Util.format2 "%s module: %s\n" msg _131_126))
in (Microsoft_FStar_Util.print_string _131_127))
end
| false -> begin
()
end))))
in (Microsoft_FStar_Util.print_string "All verification conditions discharged successfully\n")))
end
| false -> begin
()
end))

let codegen = (fun fmods env -> (match (((((ST.read Microsoft_FStar_Options.codegen) = Some ("OCaml")) || ((ST.read Microsoft_FStar_Options.codegen) = Some ("OCaml-experimental"))) || ((ST.read Microsoft_FStar_Options.codegen) = Some ("FSharp")))) with
| true -> begin
(let _65_252 = (let _131_132 = (Microsoft_FStar_Extraction_ML_Env.mkContext env)
in (Microsoft_FStar_Util.fold_map Microsoft_FStar_Extraction_ML_ExtractMod.extract _131_132 fmods))
in (match (_65_252) with
| (c, mllibs) -> begin
(let mllibs = (Microsoft_FStar_List.flatten mllibs)
in (let ext = (match (((ST.read Microsoft_FStar_Options.codegen) = Some ("FSharp"))) with
| true -> begin
".fs"
end
| false -> begin
".ml"
end)
in (let newDocs = (Microsoft_FStar_List.collect Microsoft_FStar_Extraction_ML_Code.doc_of_mllib mllibs)
in (Microsoft_FStar_List.iter (fun _65_258 -> (match (_65_258) with
| (n, d) -> begin
(let _131_135 = (Microsoft_FStar_Options.prependOutputDir (Prims.strcat n ext))
in (let _131_134 = (FSharp_Format.pretty 120 d)
in (Microsoft_FStar_Util.write_file _131_135 _131_134)))
end)) newDocs))))
end))
end
| false -> begin
()
end))

let go = (fun _65_259 -> (let _65_263 = (process_args ())
in (match (_65_263) with
| (res, filenames) -> begin
(match (res) with
| Microsoft_FStar_Getopt.Help -> begin
(let _131_137 = (Microsoft_FStar_Options.specs ())
in (Microsoft_FStar_Options.display_usage _131_137))
end
| Microsoft_FStar_Getopt.Die (msg) -> begin
(Microsoft_FStar_Util.print_string msg)
end
| Microsoft_FStar_Getopt.GoOn -> begin
(let filenames = (match (((ST.read Microsoft_FStar_Options.use_build_config) || ((not ((ST.read Microsoft_FStar_Options.interactive))) && ((Microsoft_FStar_List.length filenames) = 1)))) with
| true -> begin
(match (filenames) with
| f::[] -> begin
(Microsoft_FStar_Parser_Driver.read_build_config f)
end
| _65_271 -> begin
(let _65_272 = (Microsoft_FStar_Util.print_string "--use_build_config expects just a single file on the command line and no other arguments")
in (All.exit 1))
end)
end
| false -> begin
filenames
end)
in (let _65_278 = (batch_mode_tc filenames)
in (match (_65_278) with
| (fmods, dsenv, env) -> begin
(let _65_279 = (report_errors None)
in (match ((ST.read Microsoft_FStar_Options.interactive)) with
| true -> begin
(interactive_mode dsenv env)
end
| false -> begin
(let _65_281 = (codegen fmods env)
in (finished_message fmods))
end))
end)))
end)
end)))

let main = (fun _65_283 -> (match (()) with
| () -> begin
(All.try_with (fun _65_285 -> (match (()) with
| () -> begin
(let _65_296 = (go ())
in (let _65_298 = (cleanup ())
in (All.exit 0)))
end)) (fun _65_284 -> (match (_65_284) with
| e -> begin
(let _65_288 = (match ((Microsoft_FStar_Absyn_Util.handleable e)) with
| true -> begin
(Microsoft_FStar_Absyn_Util.handle_err false () e)
end
| false -> begin
()
end)
in (let _65_290 = (match ((ST.read Microsoft_FStar_Options.trace_error)) with
| true -> begin
(let _131_142 = (Microsoft_FStar_Util.message_of_exn e)
in (let _131_141 = (Microsoft_FStar_Util.trace_of_exn e)
in (Microsoft_FStar_Util.fprint2 "\nUnexpected error\n%s\n%s\n" _131_142 _131_141)))
end
| false -> begin
(match ((not ((Microsoft_FStar_Absyn_Util.handleable e)))) with
| true -> begin
(let _131_143 = (Microsoft_FStar_Util.message_of_exn e)
in (Microsoft_FStar_Util.fprint1 "\nUnexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" _131_143))
end
| false -> begin
()
end)
end)
in (let _65_292 = (cleanup ())
in (All.exit 1))))
end)))
end))




