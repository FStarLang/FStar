
let process_args = (fun ( _65_1 ) -> (match (()) with
| () -> begin
(let file_list = (Support.Microsoft.FStar.Util.mk_ref [])
in (let res = (let _65_25927 = (Microsoft_FStar_Options.specs ())
in (Support.Microsoft.FStar.Getopt.parse_cmdline _65_25927 (fun ( i ) -> (let _65_25926 = (let _65_25925 = (Support.ST.read file_list)
in (Support.List.append _65_25925 ((i)::[])))
in (Support.ST.op_Colon_Equals file_list _65_25926)))))
in (let _65_8 = (match (res) with
| Support.Microsoft.FStar.Getopt.GoOn -> begin
(let _65_25928 = (Microsoft_FStar_Options.set_fstar_home ())
in (Support.Prims.ignore _65_25928))
end
| _ -> begin
()
end)
in (let _65_25929 = (Support.ST.read file_list)
in (res, _65_25929)))))
end))

let cleanup = (fun ( _65_10 ) -> (match (()) with
| () -> begin
(Support.Microsoft.FStar.Util.kill_all ())
end))

let has_prims_cache = (fun ( l ) -> (Support.List.mem "Prims.cache" l))

let tc_prims = (fun ( _65_12 ) -> (match (()) with
| () -> begin
(let solver = (match ((Support.ST.read Microsoft_FStar_Options.verify)) with
| true -> begin
Microsoft_FStar_ToSMT_Encode.solver
end
| false -> begin
Microsoft_FStar_ToSMT_Encode.dummy
end)
in (let env = (Microsoft_FStar_Tc_Env.initial_env solver Microsoft_FStar_Absyn_Const.prims_lid)
in (let _65_15 = (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.init env)
in (let p = (Microsoft_FStar_Options.prims ())
in (let _65_20 = (let _65_25936 = (Microsoft_FStar_Parser_DesugarEnv.empty_env ())
in (Microsoft_FStar_Parser_Driver.parse_file _65_25936 p))
in (match (_65_20) with
| (dsenv, prims_mod) -> begin
(let _65_23 = (let _65_25937 = (Support.List.hd prims_mod)
in (Microsoft_FStar_Tc_Tc.check_module env _65_25937))
in (match (_65_23) with
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
(let _65_29 = (let _65_25940 = (Support.Microsoft.FStar.Util.string_of_int errs)
in (Support.Microsoft.FStar.Util.fprint1 "Error: %s errors were reported (see above)\n" _65_25940))
in (exit (1)))
end
| false -> begin
()
end)))

let tc_one_file = (fun ( dsenv ) ( env ) ( fn ) -> (let _65_36 = (Microsoft_FStar_Parser_Driver.parse_file dsenv fn)
in (match (_65_36) with
| (dsenv, fmods) -> begin
(let _65_46 = (Support.Prims.pipe_right fmods (Support.List.fold_left (fun ( _65_39 ) ( m ) -> (match (_65_39) with
| (env, all_mods) -> begin
(let _65_43 = (Microsoft_FStar_Tc_Tc.check_module env m)
in (match (_65_43) with
| (ms, env) -> begin
(env, (Support.List.append ms all_mods))
end))
end)) (env, [])))
in (match (_65_46) with
| (env, all_mods) -> begin
(dsenv, env, (Support.List.rev all_mods))
end))
end)))

let tc_one_fragment = (fun ( curmod ) ( dsenv ) ( env ) ( frag ) -> (Support.Prims.try_with (fun ( _65_52 ) -> (match (()) with
| () -> begin
(match ((Microsoft_FStar_Parser_Driver.parse_fragment curmod dsenv frag)) with
| Support.Microsoft.FStar.Util.Inl ((dsenv, modul)) -> begin
(let env = (match (curmod) with
| None -> begin
env
end
| Some (_) -> begin
(raise (Microsoft_FStar_Absyn_Syntax.Err ("Interactive mode only supports a single module at the top-level")))
end)
in (let _65_79 = (Microsoft_FStar_Tc_Tc.tc_partial_modul env modul)
in (match (_65_79) with
| (modul, npds, env) -> begin
Some ((Some ((modul, npds)), dsenv, env))
end)))
end
| Support.Microsoft.FStar.Util.Inr ((dsenv, decls)) -> begin
(match (curmod) with
| None -> begin
(failwith ("Fragment without an enclosing module"))
end
| Some ((modul, npds)) -> begin
(let _65_92 = (Microsoft_FStar_Tc_Tc.tc_more_partial_modul env modul decls)
in (match (_65_92) with
| (modul, npds', env) -> begin
Some ((Some ((modul, (Support.List.append npds npds'))), dsenv, env))
end))
end)
end)
end)) (fun ( _65_51 ) -> (match (_65_51) with
| Microsoft_FStar_Absyn_Syntax.Error ((msg, r)) -> begin
(let _65_58 = (Microsoft_FStar_Tc_Errors.add_errors env (((msg, r))::[]))
in None)
end
| Microsoft_FStar_Absyn_Syntax.Err (msg) -> begin
(let _65_62 = (Microsoft_FStar_Tc_Errors.add_errors env (((msg, Microsoft_FStar_Absyn_Syntax.dummyRange))::[]))
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

type stack_elt =
((Microsoft_FStar_Absyn_Syntax.modul * Microsoft_FStar_Absyn_Syntax.sigelt list) option * Microsoft_FStar_Parser_DesugarEnv.env * Microsoft_FStar_Tc_Env.env)

type stack =
stack_elt list

let interactive_mode = (fun ( dsenv ) ( env ) -> (let should_log = ((Support.ST.read Microsoft_FStar_Options.debug) <> [])
in (let log = (match (should_log) with
| true -> begin
(let transcript = (Support.Microsoft.FStar.Util.open_file_for_writing "transcript")
in (fun ( line ) -> (let _65_104 = (Support.Microsoft.FStar.Util.append_to_file transcript line)
in (Support.Microsoft.FStar.Util.flush_file transcript))))
end
| false -> begin
(fun ( line ) -> ())
end)
in (let _65_110 = (match ((let _65_25987 = (Support.ST.read Microsoft_FStar_Options.codegen)
in (Support.Option.isSome _65_25987))) with
| true -> begin
(let _65_108 = (Support.Microsoft.FStar.Util.print_string "Code-generation is not supported in interactive mode")
in (exit (1)))
end
| false -> begin
()
end)
in (let chunk = (Support.Microsoft.FStar.Util.new_string_builder ())
in (let stdin = (Support.Microsoft.FStar.Util.open_stdin ())
in (let rec fill_chunk = (fun ( _65_115 ) -> (match (()) with
| () -> begin
(let line = (match ((Support.Microsoft.FStar.Util.read_line stdin)) with
| None -> begin
(exit (0))
end
| Some (l) -> begin
l
end)
in (let _65_120 = (log line)
in (let l = (Support.Microsoft.FStar.Util.trim_string line)
in (match ((Support.Microsoft.FStar.Util.starts_with l "#end")) with
| true -> begin
(let responses = (match ((Support.Microsoft.FStar.Util.split l " ")) with
| _::ok::fail::[] -> begin
(ok, fail)
end
| _ -> begin
("ok", "fail")
end)
in (let str = (Support.Microsoft.FStar.Util.string_of_string_builder chunk)
in (let _65_132 = (Support.Microsoft.FStar.Util.clear_string_builder chunk)
in Code ((str, responses)))))
end
| false -> begin
(match ((Support.Microsoft.FStar.Util.starts_with l "#pop")) with
| true -> begin
(let _65_134 = (Support.Microsoft.FStar.Util.clear_string_builder chunk)
in Pop (l))
end
| false -> begin
(match ((Support.Microsoft.FStar.Util.starts_with l "#push")) with
| true -> begin
(let _65_136 = (Support.Microsoft.FStar.Util.clear_string_builder chunk)
in Push (l))
end
| false -> begin
(match ((l = "#finish")) with
| true -> begin
(exit (0))
end
| false -> begin
(let _65_138 = (Support.Microsoft.FStar.Util.string_builder_append chunk line)
in (let _65_140 = (Support.Microsoft.FStar.Util.string_builder_append chunk "\n")
in (fill_chunk ())))
end)
end)
end)
end))))
end))
in (let rec go = (fun ( stack ) ( curmod ) ( dsenv ) ( env ) -> (match ((fill_chunk ())) with
| Pop (msg) -> begin
(let _65_149 = (let _65_25998 = (Microsoft_FStar_Tc_Env.pop env msg)
in (Support.Prims.pipe_right _65_25998 Support.Prims.ignore))
in (let _65_151 = (env.Microsoft_FStar_Tc_Env.solver.Microsoft_FStar_Tc_Env.refresh ())
in (let _65_153 = (let _65_25999 = (Microsoft_FStar_Options.reset_options ())
in (Support.Prims.pipe_right _65_25999 Support.Prims.ignore))
in (let _65_164 = (match (stack) with
| [] -> begin
(failwith ("Too many pops"))
end
| hd::tl -> begin
(hd, tl)
end)
in (match (_65_164) with
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
in (let fail = (fun ( curmod ) ( dsenv_mark ) ( env_mark ) -> (let _65_195 = (let _65_26018 = (Microsoft_FStar_Tc_Errors.report_all ())
in (Support.Prims.pipe_right _65_26018 Support.Prims.ignore))
in (let _65_197 = (Support.ST.op_Colon_Equals Microsoft_FStar_Tc_Errors.num_errs 0)
in (let _65_199 = (Support.Microsoft.FStar.Util.fprint1 "%s\n" fail)
in (let _65_203 = (reset_mark dsenv_mark env_mark)
in (match (_65_203) with
| (dsenv, env) -> begin
(go stack curmod dsenv env)
end))))))
in (let _65_206 = (mark dsenv env)
in (match (_65_206) with
| (dsenv_mark, env_mark) -> begin
(let res = (tc_one_fragment curmod dsenv_mark env_mark text)
in (match (res) with
| Some ((curmod, dsenv, env)) -> begin
(match (((Support.ST.read Microsoft_FStar_Tc_Errors.num_errs) = 0)) with
| true -> begin
(let _65_213 = (Support.Microsoft.FStar.Util.fprint1 "\n%s\n" ok)
in (let _65_217 = (commit_mark dsenv env)
in (match (_65_217) with
| (dsenv, env) -> begin
(go stack curmod dsenv env)
end)))
end
| false -> begin
(fail curmod dsenv_mark env_mark)
end)
end
| _ -> begin
(fail curmod dsenv_mark env_mark)
end))
end))))))
end))
in (go [] None dsenv env)))))))))

let batch_mode_tc = (fun ( filenames ) -> (let _65_224 = (tc_prims ())
in (match (_65_224) with
| (prims_mod, dsenv, env) -> begin
(let _65_239 = (Support.Prims.pipe_right filenames (Support.List.fold_left (fun ( _65_228 ) ( f ) -> (match (_65_228) with
| (all_mods, dsenv, env) -> begin
(let _65_230 = (Microsoft_FStar_Absyn_Util.reset_gensym ())
in (let _65_235 = (tc_one_file dsenv env f)
in (match (_65_235) with
| (dsenv, env, ms) -> begin
((Support.List.append all_mods ms), dsenv, env)
end)))
end)) (prims_mod, dsenv, env)))
in (match (_65_239) with
| (all_mods, dsenv, env) -> begin
(let _65_240 = (match (((Support.ST.read Microsoft_FStar_Options.interactive) && ((Microsoft_FStar_Tc_Errors.get_err_count ()) = 0))) with
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
in (let _65_245 = (Support.Prims.pipe_right fmods (Support.List.iter (fun ( m ) -> (match ((Microsoft_FStar_Options.should_verify m.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str)) with
| true -> begin
(let _65_26027 = (let _65_26026 = (Microsoft_FStar_Absyn_Syntax.text_of_lid m.Microsoft_FStar_Absyn_Syntax.name)
in (Support.Microsoft.FStar.Util.format2 "%s module: %s\n" msg _65_26026))
in (Support.Microsoft.FStar.Util.print_string _65_26027))
end
| false -> begin
()
end))))
in (Support.Microsoft.FStar.Util.print_string "All verification conditions discharged successfully\n")))
end
| false -> begin
()
end))

let codegen = (fun ( fmods ) ( env ) -> (match (((Support.ST.read Microsoft_FStar_Options.codegen) = Some ("OCaml"))) with
| true -> begin
(Support.Prims.try_with (fun ( _65_250 ) -> (match (()) with
| () -> begin
(let mllib = (let _65_26033 = (Support.List.tail fmods)
in (Microsoft_FStar_Backends_OCaml_ASTTrans.mlmod_of_fstars _65_26033))
in (let doc = (Microsoft_FStar_Backends_OCaml_Code.doc_of_mllib mllib)
in (Support.List.iter (fun ( _65_264 ) -> (match (_65_264) with
| (n, d) -> begin
(let _65_26036 = (Microsoft_FStar_Options.prependOutputDir (Support.String.strcat n ".ml"))
in (let _65_26035 = (FSharp_Format.pretty 120 d)
in (Support.Microsoft.FStar.Util.write_file _65_26036 _65_26035)))
end)) doc)))
end)) (fun ( _65_249 ) -> (match (_65_249) with
| Microsoft_FStar_Backends_OCaml_ASTTrans.OCamlFailure ((rg, error)) -> begin
(let _65_256 = (let _65_26040 = (let _65_26039 = (Support.Microsoft.FStar.Range.string_of_range rg)
in (let _65_26038 = (Microsoft_FStar_Backends_OCaml_ASTTrans.string_of_error error)
in (Support.Microsoft.FStar.Util.format2 "OCaml Backend Error: %s %s\n" _65_26039 _65_26038)))
in (Support.Prims.pipe_left Support.Microsoft.FStar.Util.print_string _65_26040))
in (exit (1)))
end)))
end
| false -> begin
(match (((Support.ST.read Microsoft_FStar_Options.codegen) = Some ("OCaml-experimental"))) with
| true -> begin
(let _65_267 = (let _65_26041 = (Microsoft_FStar_Backends_ML_Env.mkContext env)
in (Support.Microsoft.FStar.Util.fold_map Microsoft_FStar_Backends_ML_ExtractMod.extract _65_26041 fmods))
in (match (_65_267) with
| (c, mllibs) -> begin
(let mllibs = (Support.List.flatten mllibs)
in (let newDocs = (Support.List.collect Microsoft_FStar_Backends_OCaml_Code.doc_of_mllib mllibs)
in (Support.List.iter (fun ( _65_272 ) -> (match (_65_272) with
| (n, d) -> begin
(let _65_26044 = (Microsoft_FStar_Options.prependOutputDir (Support.String.strcat n ".ml"))
in (let _65_26043 = (FSharp_Format.pretty 120 d)
in (Support.Microsoft.FStar.Util.write_file _65_26044 _65_26043)))
end)) newDocs)))
end))
end
| false -> begin
()
end)
end))

let go = (fun ( _65_273 ) -> (let _65_277 = (process_args ())
in (match (_65_277) with
| (res, filenames) -> begin
(match (res) with
| Support.Microsoft.FStar.Getopt.Help -> begin
(let _65_26046 = (Microsoft_FStar_Options.specs ())
in (Microsoft_FStar_Options.display_usage _65_26046))
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
| _ -> begin
(let _65_286 = (Support.Microsoft.FStar.Util.print_string "--use_build_config expects just a single file on the command line and no other arguments")
in (exit (1)))
end)
end
| false -> begin
filenames
end)
in (let _65_292 = (batch_mode_tc filenames)
in (match (_65_292) with
| (fmods, dsenv, env) -> begin
(let _65_293 = (report_errors None)
in (match ((Support.ST.read Microsoft_FStar_Options.interactive)) with
| true -> begin
(interactive_mode dsenv env)
end
| false -> begin
(let _65_295 = (codegen fmods env)
in (finished_message fmods))
end))
end)))
end)
end)))

let main = (fun ( _65_297 ) -> (match (()) with
| () -> begin
(Support.Prims.try_with (fun ( _65_299 ) -> (match (()) with
| () -> begin
(let _65_310 = (go ())
in (let _65_312 = (cleanup ())
in (exit (0))))
end)) (fun ( _65_298 ) -> (match (_65_298) with
| e -> begin
(let _65_302 = (match ((Microsoft_FStar_Absyn_Util.handleable e)) with
| true -> begin
(Microsoft_FStar_Absyn_Util.handle_err false () e)
end
| false -> begin
()
end)
in (let _65_304 = (match ((Support.ST.read Microsoft_FStar_Options.trace_error)) with
| true -> begin
(let _65_26051 = (Support.Microsoft.FStar.Util.message_of_exn e)
in (let _65_26050 = (Support.Microsoft.FStar.Util.trace_of_exn e)
in (Support.Microsoft.FStar.Util.fprint2 "\nUnexpected error\n%s\n%s\n" _65_26051 _65_26050)))
end
| false -> begin
(match ((not ((Microsoft_FStar_Absyn_Util.handleable e)))) with
| true -> begin
(let _65_26052 = (Support.Microsoft.FStar.Util.message_of_exn e)
in (Support.Microsoft.FStar.Util.fprint1 "\nUnexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" _65_26052))
end
| false -> begin
()
end)
end)
in (let _65_306 = (cleanup ())
in (exit (1)))))
end)))
end))




