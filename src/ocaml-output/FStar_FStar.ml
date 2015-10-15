
open Prims
let process_args = (fun _64_1 -> (match (()) with
| () -> begin
(let file_list = (FStar_Util.mk_ref [])
in (let res = (let _129_6 = (FStar_Options.specs ())
in (FStar_Getopt.parse_cmdline _129_6 (fun i -> (let _129_5 = (let _129_4 = (FStar_ST.read file_list)
in (FStar_List.append _129_4 ((i)::[])))
in (FStar_ST.op_Colon_Equals file_list _129_5)))))
in (let _64_8 = (match (res) with
| FStar_Getopt.GoOn -> begin
(let _129_7 = (FStar_Options.set_fstar_home ())
in (Prims.ignore _129_7))
end
| _64_7 -> begin
()
end)
in (let _129_8 = (FStar_ST.read file_list)
in (res, _129_8)))))
end))

let cleanup = (fun _64_10 -> (match (()) with
| () -> begin
(FStar_Util.kill_all ())
end))

let has_prims_cache = (fun l -> (FStar_List.mem "Prims.cache" l))

let tc_prims = (fun _64_12 -> (match (()) with
| () -> begin
(let solver = (match ((FStar_ST.read FStar_Options.verify)) with
| true -> begin
FStar_ToSMT_Encode.solver
end
| false -> begin
FStar_ToSMT_Encode.dummy
end)
in (let env = (FStar_Tc_Env.initial_env solver FStar_Absyn_Const.prims_lid)
in (let _64_15 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.init env)
in (let p = (FStar_Options.prims ())
in (let _64_20 = (let _129_15 = (FStar_Parser_DesugarEnv.empty_env ())
in (FStar_Parser_Driver.parse_file _129_15 p))
in (match (_64_20) with
| (dsenv, prims_mod) -> begin
(let _64_23 = (let _129_16 = (FStar_List.hd prims_mod)
in (FStar_Tc_Tc.check_module env _129_16))
in (match (_64_23) with
| (prims_mod, env) -> begin
(prims_mod, dsenv, env)
end))
end))))))
end))

let report_errors = (fun nopt -> (let errs = (match (nopt) with
| None -> begin
(FStar_Tc_Errors.get_err_count ())
end
| Some (n) -> begin
n
end)
in (match ((errs > 0)) with
| true -> begin
(let _64_29 = (let _129_19 = (FStar_Util.string_of_int errs)
in (FStar_Util.fprint1 "Error: %s errors were reported (see above)\n" _129_19))
in (FStar_All.exit 1))
end
| false -> begin
()
end)))

let tc_one_file = (fun dsenv env fn -> (let _64_36 = (FStar_Parser_Driver.parse_file dsenv fn)
in (match (_64_36) with
| (dsenv, fmods) -> begin
(let _64_46 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun _64_39 m -> (match (_64_39) with
| (env, all_mods) -> begin
(let _64_43 = (FStar_Tc_Tc.check_module env m)
in (match (_64_43) with
| (ms, env) -> begin
(env, (FStar_List.append ms all_mods))
end))
end)) (env, [])))
in (match (_64_46) with
| (env, all_mods) -> begin
(dsenv, env, (FStar_List.rev all_mods))
end))
end)))

let tc_one_fragment = (fun curmod dsenv env frag -> (FStar_All.try_with (fun _64_52 -> (match (()) with
| () -> begin
(match ((FStar_Parser_Driver.parse_fragment curmod dsenv frag)) with
| FStar_Parser_Driver.Empty -> begin
Some ((None, dsenv, env))
end
| FStar_Parser_Driver.Modul (dsenv, modul) -> begin
(let env = (match (curmod) with
| None -> begin
env
end
| Some (_64_74) -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("Interactive mode only supports a single module at the top-level")))
end)
in (let _64_80 = (FStar_Tc_Tc.tc_partial_modul env modul)
in (match (_64_80) with
| (modul, npds, env) -> begin
Some ((Some ((modul, npds)), dsenv, env))
end)))
end
| FStar_Parser_Driver.Decls (dsenv, decls) -> begin
(match (curmod) with
| None -> begin
(FStar_All.failwith "Fragment without an enclosing module")
end
| Some (modul, npds) -> begin
(let _64_93 = (FStar_Tc_Tc.tc_more_partial_modul env modul decls)
in (match (_64_93) with
| (modul, npds', env) -> begin
Some ((Some ((modul, (FStar_List.append npds npds'))), dsenv, env))
end))
end)
end)
end)) (fun _64_51 -> (match (_64_51) with
| FStar_Absyn_Syntax.Error (msg, r) -> begin
(let _64_58 = (FStar_Tc_Errors.add_errors env (((msg, r))::[]))
in None)
end
| FStar_Absyn_Syntax.Err (msg) -> begin
(let _64_62 = (FStar_Tc_Errors.add_errors env (((msg, FStar_Absyn_Syntax.dummyRange))::[]))
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
| Push (_64_96) -> begin
_64_96
end))

let ___Pop____0 = (fun projectee -> (match (projectee) with
| Pop (_64_99) -> begin
_64_99
end))

let ___Code____0 = (fun projectee -> (match (projectee) with
| Code (_64_102) -> begin
_64_102
end))

type stack_elt =
((FStar_Absyn_Syntax.modul * FStar_Absyn_Syntax.sigelt Prims.list) Prims.option * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env)

type stack =
stack_elt Prims.list

let batch_mode_tc_no_prims = (fun dsenv env filenames -> (let _64_120 = (FStar_All.pipe_right filenames (FStar_List.fold_left (fun _64_109 f -> (match (_64_109) with
| (all_mods, dsenv, env) -> begin
(let _64_111 = (FStar_Absyn_Util.reset_gensym ())
in (let _64_116 = (tc_one_file dsenv env f)
in (match (_64_116) with
| (dsenv, env, ms) -> begin
((FStar_List.append all_mods ms), dsenv, env)
end)))
end)) ([], dsenv, env)))
in (match (_64_120) with
| (all_mods, dsenv, env) -> begin
(let _64_121 = (match (((FStar_ST.read FStar_Options.interactive) && ((FStar_Tc_Errors.get_err_count ()) = 0))) with
| true -> begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
end
| false -> begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.finish ())
end)
in (all_mods, dsenv, env))
end)))

let batch_mode_tc = (fun filenames -> (let _64_127 = (tc_prims ())
in (match (_64_127) with
| (prims_mod, dsenv, env) -> begin
(let _64_131 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (_64_131) with
| (all_mods, dsenv, env) -> begin
((FStar_List.append prims_mod all_mods), dsenv, env)
end))
end)))

let finished_message = (fun fmods -> (match ((not ((FStar_ST.read FStar_Options.silent)))) with
| true -> begin
(let msg = (match ((FStar_ST.read FStar_Options.verify)) with
| true -> begin
"Verifying"
end
| false -> begin
(match ((FStar_ST.read FStar_Options.pretype)) with
| true -> begin
"Lax type-checked"
end
| false -> begin
"Parsed and desugared"
end)
end)
in (let _64_135 = (FStar_All.pipe_right fmods (FStar_List.iter (fun m -> (match ((FStar_Options.should_print_message m.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str)) with
| true -> begin
(let _129_94 = (let _129_93 = (FStar_Absyn_Syntax.text_of_lid m.FStar_Absyn_Syntax.name)
in (FStar_Util.format2 "%s module: %s\n" msg _129_93))
in (FStar_Util.print_string _129_94))
end
| false -> begin
()
end))))
in (FStar_Util.print_string "All verification conditions discharged successfully\n")))
end
| false -> begin
()
end))

let interactive_mode = (fun dsenv env -> (let should_read_build_config = (FStar_ST.alloc true)
in (let should_log = ((FStar_ST.read FStar_Options.debug) <> [])
in (let log = (match (should_log) with
| true -> begin
(let transcript = (FStar_Util.open_file_for_writing "transcript")
in (fun line -> (let _64_143 = (FStar_Util.append_to_file transcript line)
in (FStar_Util.flush_file transcript))))
end
| false -> begin
(fun line -> ())
end)
in (let _64_147 = (match ((let _129_102 = (FStar_ST.read FStar_Options.codegen)
in (FStar_Option.isSome _129_102))) with
| true -> begin
(FStar_Util.print_string "Warning: Code-generation is not supported in interactive mode, ignoring the codegen flag")
end
| false -> begin
()
end)
in (let chunk = (FStar_Util.new_string_builder ())
in (let stdin = (FStar_Util.open_stdin ())
in (let rec fill_chunk = (fun _64_152 -> (match (()) with
| () -> begin
(let line = (match ((FStar_Util.read_line stdin)) with
| None -> begin
(FStar_All.exit 0)
end
| Some (l) -> begin
l
end)
in (let _64_157 = (log line)
in (let l = (FStar_Util.trim_string line)
in (match ((FStar_Util.starts_with l "#end")) with
| true -> begin
(let responses = (match ((FStar_Util.split l " ")) with
| _64_163::ok::fail::[] -> begin
(ok, fail)
end
| _64_166 -> begin
("ok", "fail")
end)
in (let str = (FStar_Util.string_of_string_builder chunk)
in (let _64_169 = (FStar_Util.clear_string_builder chunk)
in Code ((str, responses)))))
end
| false -> begin
(match ((FStar_Util.starts_with l "#pop")) with
| true -> begin
(let _64_171 = (FStar_Util.clear_string_builder chunk)
in Pop (l))
end
| false -> begin
(match ((FStar_Util.starts_with l "#push")) with
| true -> begin
(let _64_173 = (FStar_Util.clear_string_builder chunk)
in Push (l))
end
| false -> begin
(match ((l = "#finish")) with
| true -> begin
(FStar_All.exit 0)
end
| false -> begin
(let _64_175 = (FStar_Util.string_builder_append chunk line)
in (let _64_177 = (FStar_Util.string_builder_append chunk "\n")
in (fill_chunk ())))
end)
end)
end)
end))))
end))
in (let rec go = (fun stack curmod dsenv env -> (match ((fill_chunk ())) with
| Pop (msg) -> begin
(let _64_186 = (let _129_113 = (FStar_Tc_Env.pop env msg)
in (FStar_All.pipe_right _129_113 Prims.ignore))
in (let _64_188 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in (let _64_190 = (let _129_114 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _129_114 Prims.ignore))
in (let _64_201 = (match (stack) with
| [] -> begin
(FStar_All.failwith "Too many pops")
end
| hd::tl -> begin
(hd, tl)
end)
in (match (_64_201) with
| ((curmod, dsenv, env), stack) -> begin
(go stack curmod dsenv env)
end)))))
end
| Push (msg) -> begin
(let stack = ((curmod, dsenv, env))::stack
in (let dsenv = (FStar_Parser_DesugarEnv.push dsenv)
in (let env = (FStar_Tc_Env.push env msg)
in (go stack curmod dsenv env))))
end
| Code (text, (ok, fail)) -> begin
(let mark = (fun dsenv env -> (let dsenv = (FStar_Parser_DesugarEnv.mark dsenv)
in (let env = (FStar_Tc_Env.mark env)
in (dsenv, env))))
in (let reset_mark = (fun dsenv env -> (let dsenv = (FStar_Parser_DesugarEnv.reset_mark dsenv)
in (let env = (FStar_Tc_Env.reset_mark env)
in (dsenv, env))))
in (let commit_mark = (fun dsenv env -> (let dsenv = (FStar_Parser_DesugarEnv.commit_mark dsenv)
in (let env = (FStar_Tc_Env.commit_mark env)
in (dsenv, env))))
in (let fail = (fun curmod dsenv_mark env_mark -> (let _64_232 = (let _129_133 = (FStar_Tc_Errors.report_all ())
in (FStar_All.pipe_right _129_133 Prims.ignore))
in (let _64_234 = (FStar_ST.op_Colon_Equals FStar_Tc_Errors.num_errs 0)
in (let _64_236 = (FStar_Util.fprint1 "%s\n" fail)
in (let _64_240 = (reset_mark dsenv_mark env_mark)
in (match (_64_240) with
| (dsenv, env) -> begin
(go stack curmod dsenv env)
end))))))
in (let _64_253 = (match ((FStar_ST.read should_read_build_config)) with
| true -> begin
(match ((let _129_134 = (FStar_Parser_ParseIt.get_bc_start_string ())
in (FStar_Util.starts_with text _129_134))) with
| true -> begin
(let filenames = (FStar_Parser_ParseIt.read_build_config_from_string "" false text)
in (let _64_246 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (_64_246) with
| (_64_243, dsenv, env) -> begin
(let _64_247 = (FStar_ST.op_Colon_Equals should_read_build_config false)
in (dsenv, env))
end)))
end
| false -> begin
(let _64_249 = (FStar_ST.op_Colon_Equals should_read_build_config false)
in (dsenv, env))
end)
end
| false -> begin
(dsenv, env)
end)
in (match (_64_253) with
| (dsenv, env) -> begin
(let _64_256 = (mark dsenv env)
in (match (_64_256) with
| (dsenv_mark, env_mark) -> begin
(let res = (tc_one_fragment curmod dsenv_mark env_mark text)
in (match (res) with
| Some (curmod, dsenv, env) -> begin
(match (((FStar_ST.read FStar_Tc_Errors.num_errs) = 0)) with
| true -> begin
(let _64_263 = (FStar_Util.fprint1 "\n%s\n" ok)
in (let _64_267 = (commit_mark dsenv env)
in (match (_64_267) with
| (dsenv, env) -> begin
(go stack curmod dsenv env)
end)))
end
| false -> begin
(fail curmod dsenv_mark env_mark)
end)
end
| _64_269 -> begin
(fail curmod dsenv_mark env_mark)
end))
end))
end))))))
end))
in (go [] None dsenv env))))))))))

let codegen = (fun fmods env -> (match ((((FStar_ST.read FStar_Options.codegen) = Some ("OCaml")) || ((FStar_ST.read FStar_Options.codegen) = Some ("FSharp")))) with
| true -> begin
(let _64_274 = (let _129_139 = (FStar_Extraction_ML_Env.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_ExtractMod.extract _129_139 fmods))
in (match (_64_274) with
| (c, mllibs) -> begin
(let mllibs = (FStar_List.flatten mllibs)
in (let ext = (match (((FStar_ST.read FStar_Options.codegen) = Some ("FSharp"))) with
| true -> begin
".fs"
end
| false -> begin
".ml"
end)
in (let newDocs = (FStar_List.collect FStar_Extraction_ML_Code.doc_of_mllib mllibs)
in (FStar_List.iter (fun _64_280 -> (match (_64_280) with
| (n, d) -> begin
(let _129_142 = (FStar_Options.prependOutputDir (Prims.strcat n ext))
in (let _129_141 = (FSharp_Format.pretty 120 d)
in (FStar_Util.write_file _129_142 _129_141)))
end)) newDocs))))
end))
end
| false -> begin
()
end))

let go = (fun _64_281 -> (let _64_285 = (process_args ())
in (match (_64_285) with
| (res, filenames) -> begin
(match (res) with
| FStar_Getopt.Help -> begin
(let _129_144 = (FStar_Options.specs ())
in (FStar_Options.display_usage _129_144))
end
| FStar_Getopt.Die (msg) -> begin
(FStar_Util.print_string msg)
end
| FStar_Getopt.GoOn -> begin
(let filenames = (match (((FStar_ST.read FStar_Options.use_build_config) || ((not ((FStar_ST.read FStar_Options.interactive))) && ((FStar_List.length filenames) = 1)))) with
| true -> begin
(match (filenames) with
| f::[] -> begin
(FStar_Parser_Driver.read_build_config f)
end
| _64_293 -> begin
(let _64_294 = (FStar_Util.print_string "--use_build_config expects just a single file on the command line and no other arguments")
in (FStar_All.exit 1))
end)
end
| false -> begin
filenames
end)
in (let _64_300 = (batch_mode_tc filenames)
in (match (_64_300) with
| (fmods, dsenv, env) -> begin
(let _64_301 = (report_errors None)
in (match ((FStar_ST.read FStar_Options.interactive)) with
| true -> begin
(interactive_mode dsenv env)
end
| false -> begin
(let _64_303 = (codegen fmods env)
in (finished_message fmods))
end))
end)))
end)
end)))

let main = (fun _64_305 -> (match (()) with
| () -> begin
(FStar_All.try_with (fun _64_307 -> (match (()) with
| () -> begin
(let _64_318 = (go ())
in (let _64_320 = (cleanup ())
in (FStar_All.exit 0)))
end)) (fun _64_306 -> (match (_64_306) with
| e -> begin
(let _64_310 = (match ((FStar_Absyn_Util.handleable e)) with
| true -> begin
(FStar_Absyn_Util.handle_err false () e)
end
| false -> begin
()
end)
in (let _64_312 = (match ((FStar_ST.read FStar_Options.trace_error)) with
| true -> begin
(let _129_149 = (FStar_Util.message_of_exn e)
in (let _129_148 = (FStar_Util.trace_of_exn e)
in (FStar_Util.fprint2 "\nUnexpected error\n%s\n%s\n" _129_149 _129_148)))
end
| false -> begin
(match ((not ((FStar_Absyn_Util.handleable e)))) with
| true -> begin
(let _129_150 = (FStar_Util.message_of_exn e)
in (FStar_Util.fprint1 "\nUnexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" _129_150))
end
| false -> begin
()
end)
end)
in (let _64_314 = (cleanup ())
in (FStar_All.exit 1))))
end)))
end))
