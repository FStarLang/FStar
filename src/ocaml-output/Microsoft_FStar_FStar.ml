
let process_args = (fun ( _63_1 ) -> (match (()) with
| () -> begin
(let file_list = (Support.Microsoft.FStar.Util.mk_ref [])
in (let res = (let _127_6 = (Microsoft_FStar_Options.specs ())
in (Support.Microsoft.FStar.Getopt.parse_cmdline _127_6 (fun ( i ) -> (let _127_5 = (let _127_4 = (Support.ST.read file_list)
in (Support.List.append _127_4 ((i)::[])))
in (Support.ST.op_Colon_Equals file_list _127_5)))))
in (let _63_8 = (match (res) with
| Support.Microsoft.FStar.Getopt.GoOn -> begin
(let _127_7 = (Microsoft_FStar_Options.set_fstar_home ())
in (Support.Prims.ignore _127_7))
end
| _63_7 -> begin
()
end)
in (let _127_8 = (Support.ST.read file_list)
in (res, _127_8)))))
end))

let cleanup = (fun ( _63_10 ) -> (match (()) with
| () -> begin
(Support.Microsoft.FStar.Util.kill_all ())
end))

let has_prims_cache = (fun ( l ) -> (Support.List.mem "Prims.cache" l))

let tc_prims = (fun ( _63_12 ) -> (match (()) with
| () -> begin
(let solver = (match ((Support.ST.read Microsoft_FStar_Options.verify)) with
| true -> begin
Microsoft_FStar_ToSMT_Encode.solver
end
| false -> begin
Microsoft_FStar_ToSMT_Encode.dummy
end)
in (let env = (Microsoft_FStar_Tc_Env.initial_env solver Microsoft_FStar_Absyn_Const.prims_lid)
in (let _63_15 = (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.init env)
in (let p = (Microsoft_FStar_Options.prims ())
in (let _63_20 = (let _127_15 = (Microsoft_FStar_Parser_DesugarEnv.empty_env ())
in (Microsoft_FStar_Parser_Driver.parse_file _127_15 p))
in (match (_63_20) with
| (dsenv, prims_mod) -> begin
(let _63_23 = (let _127_16 = (Support.List.hd prims_mod)
in (Microsoft_FStar_Tc_Tc.check_module env _127_16))
in (match (_63_23) with
| (prims_mod, env) -> begin
(prims_mod, dsenv, env)
end))
end))))))
end))

let report_errors = (fun ( nopt ) -> (let errs = (match (nopt) with
| None -> begin
(Microsoft_FStar_Tc_Errors.get_err_count ())
end
| Some (n) -> begin
n
end)
in (match ((errs > 0)) with
| true -> begin
(let _63_29 = (let _127_19 = (Support.Microsoft.FStar.Util.string_of_int errs)
in (Support.Microsoft.FStar.Util.fprint1 "Error: %s errors were reported (see above)\n" _127_19))
in (Support.All.exit 1))
end
| false -> begin
()
end)))

let tc_one_file = (fun ( dsenv ) ( env ) ( fn ) -> (let _63_36 = (Microsoft_FStar_Parser_Driver.parse_file dsenv fn)
in (match (_63_36) with
| (dsenv, fmods) -> begin
(let _63_46 = (Support.All.pipe_right fmods (Support.List.fold_left (fun ( _63_39 ) ( m ) -> (match (_63_39) with
| (env, all_mods) -> begin
(let _63_43 = (Microsoft_FStar_Tc_Tc.check_module env m)
in (match (_63_43) with
| (ms, env) -> begin
(env, (Support.List.append ms all_mods))
end))
end)) (env, [])))
in (match (_63_46) with
| (env, all_mods) -> begin
(dsenv, env, (Support.List.rev all_mods))
end))
end)))

let tc_one_fragment = (fun ( curmod ) ( dsenv ) ( env ) ( frag ) -> (Support.All.try_with (fun ( _63_52 ) -> (match (()) with
| () -> begin
(match ((Microsoft_FStar_Parser_Driver.parse_fragment curmod dsenv frag)) with
| Support.Microsoft.FStar.Util.Inl ((dsenv, modul)) -> begin
(let env = (match (curmod) with
| None -> begin
env
end
| Some (_63_73) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Err ("Interactive mode only supports a single module at the top-level")))
end)
in (let _63_79 = (Microsoft_FStar_Tc_Tc.tc_partial_modul env modul)
in (match (_63_79) with
| (modul, npds, env) -> begin
Some ((Some ((modul, npds)), dsenv, env))
end)))
end
| Support.Microsoft.FStar.Util.Inr ((dsenv, decls)) -> begin
(match (curmod) with
| None -> begin
(Support.All.failwith "Fragment without an enclosing module")
end
| Some ((modul, npds)) -> begin
(let _63_92 = (Microsoft_FStar_Tc_Tc.tc_more_partial_modul env modul decls)
in (match (_63_92) with
| (modul, npds', env) -> begin
Some ((Some ((modul, (Support.List.append npds npds'))), dsenv, env))
end))
end)
end)
end)) (fun ( _63_51 ) -> (match (_63_51) with
| Microsoft_FStar_Absyn_Syntax.Error ((msg, r)) -> begin
(let _63_58 = (Microsoft_FStar_Tc_Errors.add_errors env (((msg, r))::[]))
in None)
end
| Microsoft_FStar_Absyn_Syntax.Err (msg) -> begin
(let _63_62 = (Microsoft_FStar_Tc_Errors.add_errors env (((msg, Microsoft_FStar_Absyn_Syntax.dummyRange))::[]))
in None)
end
| e -> begin
(raise (e))
end))))

type input_chunks =
| Push of string
| Pop of string
| Code of (string * (string * string))

let is_Push = (fun ( _discr_ ) -> (match (_discr_) with
| Push (_) -> begin
true
end
| _ -> begin
false
end))

let is_Pop = (fun ( _discr_ ) -> (match (_discr_) with
| Pop (_) -> begin
true
end
| _ -> begin
false
end))

let is_Code = (fun ( _discr_ ) -> (match (_discr_) with
| Code (_) -> begin
true
end
| _ -> begin
false
end))

let ___Push____0 = (fun ( projectee ) -> (match (projectee) with
| Push (_63_95) -> begin
_63_95
end))

let ___Pop____0 = (fun ( projectee ) -> (match (projectee) with
| Pop (_63_98) -> begin
_63_98
end))

let ___Code____0 = (fun ( projectee ) -> (match (projectee) with
| Code (_63_101) -> begin
_63_101
end))

type stack_elt =
((Microsoft_FStar_Absyn_Syntax.modul * Microsoft_FStar_Absyn_Syntax.sigelt list) option * Microsoft_FStar_Parser_DesugarEnv.env * Microsoft_FStar_Tc_Env.env)

type stack =
stack_elt list

let interactive_mode = (fun ( dsenv ) ( env ) -> (let should_log = ((Support.ST.read Microsoft_FStar_Options.debug) <> [])
in (let log = (match (should_log) with
| true -> begin
(let transcript = (Support.Microsoft.FStar.Util.open_file_for_writing "transcript")
in (fun ( line ) -> (let _63_107 = (Support.Microsoft.FStar.Util.append_to_file transcript line)
in (Support.Microsoft.FStar.Util.flush_file transcript))))
end
| false -> begin
(fun ( line ) -> ())
end)
in (let _63_111 = (match ((let _127_87 = (Support.ST.read Microsoft_FStar_Options.codegen)
in (Support.Option.isSome _127_87))) with
| true -> begin
(Support.Microsoft.FStar.Util.print_string "Warning: Code-generation is not supported in interactive mode, ignoring the codegen flag")
end
| false -> begin
()
end)
in (let chunk = (Support.Microsoft.FStar.Util.new_string_builder ())
in (let stdin = (Support.Microsoft.FStar.Util.open_stdin ())
in (let rec fill_chunk = (fun ( _63_116 ) -> (match (()) with
| () -> begin
(let line = (match ((Support.Microsoft.FStar.Util.read_line stdin)) with
| None -> begin
(Support.All.exit 0)
end
| Some (l) -> begin
l
end)
in (let _63_121 = (log line)
in (let l = (Support.Microsoft.FStar.Util.trim_string line)
in (match ((Support.Microsoft.FStar.Util.starts_with l "#end")) with
| true -> begin
(let responses = (match ((Support.Microsoft.FStar.Util.split l " ")) with
| _63_127::ok::fail::[] -> begin
(ok, fail)
end
| _63_130 -> begin
("ok", "fail")
end)
in (let str = (Support.Microsoft.FStar.Util.string_of_string_builder chunk)
in (let _63_133 = (Support.Microsoft.FStar.Util.clear_string_builder chunk)
in Code ((str, responses)))))
end
| false -> begin
(match ((Support.Microsoft.FStar.Util.starts_with l "#pop")) with
| true -> begin
(let _63_135 = (Support.Microsoft.FStar.Util.clear_string_builder chunk)
in Pop (l))
end
| false -> begin
(match ((Support.Microsoft.FStar.Util.starts_with l "#push")) with
| true -> begin
(let _63_137 = (Support.Microsoft.FStar.Util.clear_string_builder chunk)
in Push (l))
end
| false -> begin
(match ((l = "#finish")) with
| true -> begin
(Support.All.exit 0)
end
| false -> begin
(let _63_139 = (Support.Microsoft.FStar.Util.string_builder_append chunk line)
in (let _63_141 = (Support.Microsoft.FStar.Util.string_builder_append chunk "\n")
in (fill_chunk ())))
end)
end)
end)
end))))
end))
in (let rec go = (fun ( stack ) ( curmod ) ( dsenv ) ( env ) -> (match ((fill_chunk ())) with
| Pop (msg) -> begin
(let _63_150 = (let _127_98 = (Microsoft_FStar_Tc_Env.pop env msg)
in (Support.All.pipe_right _127_98 Support.Prims.ignore))
in (let _63_152 = (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.refresh ())
in (let _63_154 = (let _127_99 = (Microsoft_FStar_Options.reset_options ())
in (Support.All.pipe_right _127_99 Support.Prims.ignore))
in (let _63_165 = (match (stack) with
| [] -> begin
(Support.All.failwith "Too many pops")
end
| hd::tl -> begin
(hd, tl)
end)
in (match (_63_165) with
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
| Code ((text, (ok, fail))) -> begin
(let mark = (fun ( dsenv ) ( env ) -> (let dsenv = (Microsoft_FStar_Parser_DesugarEnv.mark dsenv)
in (let env = (Microsoft_FStar_Tc_Env.mark env)
in (dsenv, env))))
in (let reset_mark = (fun ( dsenv ) ( env ) -> (let dsenv = (Microsoft_FStar_Parser_DesugarEnv.reset_mark dsenv)
in (let env = (Microsoft_FStar_Tc_Env.reset_mark env)
in (dsenv, env))))
in (let commit_mark = (fun ( dsenv ) ( env ) -> (let dsenv = (Microsoft_FStar_Parser_DesugarEnv.commit_mark dsenv)
in (let env = (Microsoft_FStar_Tc_Env.commit_mark env)
in (dsenv, env))))
in (let fail = (fun ( curmod ) ( dsenv_mark ) ( env_mark ) -> (let _63_196 = (let _127_118 = (Microsoft_FStar_Tc_Errors.report_all ())
in (Support.All.pipe_right _127_118 Support.Prims.ignore))
in (let _63_198 = (Support.ST.op_Colon_Equals Microsoft_FStar_Tc_Errors.num_errs 0)
in (let _63_200 = (Support.Microsoft.FStar.Util.fprint1 "%s\n" fail)
in (let _63_204 = (reset_mark dsenv_mark env_mark)
in (match (_63_204) with
| (dsenv, env) -> begin
(go stack curmod dsenv env)
end))))))
in (let _63_207 = (mark dsenv env)
in (match (_63_207) with
| (dsenv_mark, env_mark) -> begin
(let res = (tc_one_fragment curmod dsenv_mark env_mark text)
in (match (res) with
| Some ((curmod, dsenv, env)) -> begin
(match (((Support.ST.read Microsoft_FStar_Tc_Errors.num_errs) = 0)) with
| true -> begin
(let _63_214 = (Support.Microsoft.FStar.Util.fprint1 "\n%s\n" ok)
in (let _63_218 = (commit_mark dsenv env)
in (match (_63_218) with
| (dsenv, env) -> begin
(go stack curmod dsenv env)
end)))
end
| false -> begin
(fail curmod dsenv_mark env_mark)
end)
end
| _63_220 -> begin
(fail curmod dsenv_mark env_mark)
end))
end))))))
end))
in (go [] None dsenv env)))))))))

let batch_mode_tc = (fun ( filenames ) -> (let _63_225 = (tc_prims ())
in (match (_63_225) with
| (prims_mod, dsenv, env) -> begin
(let _63_240 = (Support.All.pipe_right filenames (Support.List.fold_left (fun ( _63_229 ) ( f ) -> (match (_63_229) with
| (all_mods, dsenv, env) -> begin
(let _63_231 = (Microsoft_FStar_Absyn_Util.reset_gensym ())
in (let _63_236 = (tc_one_file dsenv env f)
in (match (_63_236) with
| (dsenv, env, ms) -> begin
((Support.List.append all_mods ms), dsenv, env)
end)))
end)) (prims_mod, dsenv, env)))
in (match (_63_240) with
| (all_mods, dsenv, env) -> begin
(let _63_241 = (match (((Support.ST.read Microsoft_FStar_Options.interactive) && ((Microsoft_FStar_Tc_Errors.get_err_count ()) = 0))) with
| true -> begin
(env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.refresh ())
end
| false -> begin
(env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.finish ())
end)
in (all_mods, dsenv, env))
end))
end)))

let finished_message = (fun ( fmods ) -> (match ((not ((Support.ST.read Microsoft_FStar_Options.silent)))) with
| true -> begin
(let msg = (match ((Support.ST.read Microsoft_FStar_Options.verify)) with
| true -> begin
"Verified"
end
| false -> begin
(match ((Support.ST.read Microsoft_FStar_Options.pretype)) with
| true -> begin
"Lax type-checked"
end
| false -> begin
"Parsed and desugared"
end)
end)
in (let _63_246 = (Support.All.pipe_right fmods (Support.List.iter (fun ( m ) -> (match ((Microsoft_FStar_Options.should_verify m.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str)) with
| true -> begin
(let _127_127 = (let _127_126 = (Microsoft_FStar_Absyn_Syntax.text_of_lid m.Microsoft_FStar_Absyn_Syntax.name)
in (Support.Microsoft.FStar.Util.format2 "%s module: %s\n" msg _127_126))
in (Support.Microsoft.FStar.Util.print_string _127_127))
end
| false -> begin
()
end))))
in (Support.Microsoft.FStar.Util.print_string "All verification conditions discharged successfully\n")))
end
| false -> begin
()
end))

let codegen = (fun ( fmods ) ( env ) -> (match ((((Support.ST.read Microsoft_FStar_Options.codegen) = Some ("OCaml")) || ((Support.ST.read Microsoft_FStar_Options.codegen) = Some ("OCaml-experimental")))) with
| true -> begin
(let _63_252 = (let _127_132 = (Microsoft_FStar_Extraction_ML_Env.mkContext env)
in (Support.Microsoft.FStar.Util.fold_map Microsoft_FStar_Extraction_ML_ExtractMod.extract _127_132 fmods))
in (match (_63_252) with
| (c, mllibs) -> begin
(let mllibs = (Support.List.flatten mllibs)
in (let newDocs = (Support.List.collect Microsoft_FStar_Extraction_OCaml_Code.doc_of_mllib mllibs)
in (Support.List.iter (fun ( _63_257 ) -> (match (_63_257) with
| (n, d) -> begin
(let _127_135 = (Microsoft_FStar_Options.prependOutputDir (Support.String.strcat n ".ml"))
in (let _127_134 = (FSharp_Format.pretty 120 d)
in (Support.Microsoft.FStar.Util.write_file _127_135 _127_134)))
end)) newDocs)))
end))
end
| false -> begin
()
end))

let go = (fun ( _63_258 ) -> (let _63_262 = (process_args ())
in (match (_63_262) with
| (res, filenames) -> begin
(match (res) with
| Support.Microsoft.FStar.Getopt.Help -> begin
(let _127_137 = (Microsoft_FStar_Options.specs ())
in (Microsoft_FStar_Options.display_usage _127_137))
end
| Support.Microsoft.FStar.Getopt.Die (msg) -> begin
(Support.Microsoft.FStar.Util.print_string msg)
end
| Support.Microsoft.FStar.Getopt.GoOn -> begin
(let filenames = (match (((Support.ST.read Microsoft_FStar_Options.use_build_config) || ((not ((Support.ST.read Microsoft_FStar_Options.interactive))) && ((Support.List.length filenames) = 1)))) with
| true -> begin
(match (filenames) with
| f::[] -> begin
(Microsoft_FStar_Parser_Driver.read_build_config f)
end
| _63_270 -> begin
(let _63_271 = (Support.Microsoft.FStar.Util.print_string "--use_build_config expects just a single file on the command line and no other arguments")
in (Support.All.exit 1))
end)
end
| false -> begin
filenames
end)
in (let _63_277 = (batch_mode_tc filenames)
in (match (_63_277) with
| (fmods, dsenv, env) -> begin
(let _63_278 = (report_errors None)
in (match ((Support.ST.read Microsoft_FStar_Options.interactive)) with
| true -> begin
(interactive_mode dsenv env)
end
| false -> begin
(let _63_280 = (codegen fmods env)
in (finished_message fmods))
end))
end)))
end)
end)))

let main = (fun ( _63_282 ) -> (match (()) with
| () -> begin
(Support.All.try_with (fun ( _63_284 ) -> (match (()) with
| () -> begin
(let _63_295 = (go ())
in (let _63_297 = (cleanup ())
in (Support.All.exit 0)))
end)) (fun ( _63_283 ) -> (match (_63_283) with
| e -> begin
(let _63_287 = (match ((Microsoft_FStar_Absyn_Util.handleable e)) with
| true -> begin
(Microsoft_FStar_Absyn_Util.handle_err false () e)
end
| false -> begin
()
end)
in (let _63_289 = (match ((Support.ST.read Microsoft_FStar_Options.trace_error)) with
| true -> begin
(let _127_142 = (Support.Microsoft.FStar.Util.message_of_exn e)
in (let _127_141 = (Support.Microsoft.FStar.Util.trace_of_exn e)
in (Support.Microsoft.FStar.Util.fprint2 "\nUnexpected error\n%s\n%s\n" _127_142 _127_141)))
end
| false -> begin
(match ((not ((Microsoft_FStar_Absyn_Util.handleable e)))) with
| true -> begin
(let _127_143 = (Support.Microsoft.FStar.Util.message_of_exn e)
in (Support.Microsoft.FStar.Util.fprint1 "\nUnexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" _127_143))
end
| false -> begin
()
end)
end)
in (let _63_291 = (cleanup ())
in (Support.All.exit 1))))
end)))
end))




