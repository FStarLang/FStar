
open Prims
let process_args : Prims.unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun _102_1 -> (match (()) with
| () -> begin
(let file_list = (FStar_Util.mk_ref [])
in (let res = (let _205_6 = (FStar_Options.specs ())
in (FStar_Getopt.parse_cmdline _205_6 (fun i -> (let _205_5 = (let _205_4 = (FStar_ST.read file_list)
in (FStar_List.append _205_4 ((i)::[])))
in (FStar_ST.op_Colon_Equals file_list _205_5)))))
in (let _102_8 = (match (res) with
| FStar_Getopt.GoOn -> begin
(let _205_7 = (FStar_Options.set_fstar_home ())
in (Prims.ignore _205_7))
end
| _102_7 -> begin
()
end)
in (let _205_8 = (FStar_ST.read file_list)
in (res, _205_8)))))
end))

let cleanup : Prims.unit  ->  Prims.unit = (fun _102_10 -> (match (()) with
| () -> begin
(FStar_Util.kill_all ())
end))

let has_prims_cache : Prims.string Prims.list  ->  Prims.bool = (fun l -> (FStar_List.mem "Prims.cache" l))

let u_parse : FStar_Parser_Env.env  ->  Prims.string  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env fn -> (FStar_All.try_with (fun _102_15 -> (match (()) with
| () -> begin
(match ((FStar_Parser_ParseIt.parse (FStar_Util.Inl (fn)))) with
| FStar_Util.Inl (FStar_Util.Inl (ast)) -> begin
(FStar_Parser_ToSyntax.desugar_file env ast)
end
| FStar_Util.Inl (FStar_Util.Inr (_102_29)) -> begin
(let _102_32 = (FStar_Util.print1 "%s: Expected a module\n" fn)
in (FStar_All.exit 1))
end
| FStar_Util.Inr (msg, r) -> begin
(let _102_38 = (let _205_18 = (FStar_Absyn_Print.format_error r msg)
in (FStar_All.pipe_left FStar_Util.print_string _205_18))
in (FStar_All.exit 1))
end)
end)) (fun _102_14 -> (match (_102_14) with
| e when (((FStar_ST.read FStar_Options.trace_error) && (FStar_Syntax_Util.handleable e)) && (let _102_18 = (FStar_Syntax_Util.handle_err false () e)
in false)) -> begin
(FStar_All.failwith "Impossible")
end
| e when ((not ((FStar_ST.read FStar_Options.trace_error))) && (FStar_Syntax_Util.handleable e)) -> begin
(let _102_21 = (FStar_Syntax_Util.handle_err false () e)
in (FStar_All.exit 1))
end))))

let u_tc_prims : Prims.unit  ->  (FStar_Syntax_Syntax.modul * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun _102_40 -> (match (()) with
| () -> begin
(let solver = if (FStar_ST.read FStar_Options.verify) then begin
FStar_SMTEncoding_Encode.solver
end else begin
FStar_SMTEncoding_Encode.dummy
end
in (let env = (FStar_TypeChecker_Env.initial_env FStar_TypeChecker_Tc.type_of solver FStar_Absyn_Const.prims_lid)
in (let _102_43 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env)
in (let p = (FStar_Options.prims ())
in (let _102_48 = (let _205_22 = (FStar_Parser_Env.empty_env ())
in (u_parse _205_22 p))
in (match (_102_48) with
| (dsenv, prims_mod) -> begin
(let _102_51 = (let _205_23 = (FStar_List.hd prims_mod)
in (FStar_TypeChecker_Tc.check_module env _205_23))
in (match (_102_51) with
| (prims_mod, env) -> begin
(prims_mod, dsenv, env)
end))
end))))))
end))

let test_universes : Prims.string Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list * FStar_TypeChecker_Env.env) = (fun filenames -> (FStar_All.try_with (fun _102_54 -> (match (()) with
| () -> begin
(let _102_67 = (u_tc_prims ())
in (match (_102_67) with
| (prims_mod, dsenv, env) -> begin
(let _102_85 = (FStar_List.fold_left (fun _102_71 fn -> (match (_102_71) with
| (dsenv, fmods, env) -> begin
(let _102_73 = (FStar_Util.print1 "Parsing file %s\n" fn)
in (let _102_77 = (u_parse dsenv fn)
in (match (_102_77) with
| (dsenv, mods) -> begin
(let _102_81 = (let _205_29 = (FStar_List.hd mods)
in (FStar_TypeChecker_Tc.check_module env _205_29))
in (match (_102_81) with
| (_102_79, env) -> begin
(dsenv, (FStar_List.append mods fmods), env)
end))
end)))
end)) (dsenv, [], env) filenames)
in (match (_102_85) with
| (dsenv, mods, env) -> begin
(let _102_86 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
in (dsenv, mods, env))
end))
end))
end)) (fun _102_53 -> (match (_102_53) with
| FStar_Syntax_Syntax.Error (msg, r) when (not ((FStar_ST.read FStar_Options.trace_error))) -> begin
(let _102_60 = (let _205_32 = (let _205_31 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "Error : %s\n%s\n" _205_31 msg))
in (FStar_Util.print_string _205_32))
in (FStar_All.exit 1))
end))))

let tc_prims : Prims.unit  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) = (fun _102_88 -> (match (()) with
| () -> begin
(let solver = if (FStar_ST.read FStar_Options.verify) then begin
FStar_ToSMT_Encode.solver
end else begin
FStar_ToSMT_Encode.dummy
end
in (let env = (FStar_Tc_Env.initial_env solver FStar_Absyn_Const.prims_lid)
in (let _102_91 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.init env)
in (let p = (FStar_Options.prims ())
in (let _102_96 = (let _205_35 = (FStar_Parser_DesugarEnv.empty_env ())
in (FStar_Parser_Driver.parse_file _205_35 p))
in (match (_102_96) with
| (dsenv, prims_mod) -> begin
(let _102_99 = (let _205_36 = (FStar_List.hd prims_mod)
in (FStar_Tc_Tc.check_module env _205_36))
in (match (_102_99) with
| (prims_mod, env) -> begin
(prims_mod, dsenv, env)
end))
end))))))
end))

let report_errors : Prims.int Prims.option  ->  Prims.unit = (fun nopt -> (let errs = (match (nopt) with
| None -> begin
(FStar_Tc_Errors.get_err_count ())
end
| Some (n) -> begin
n
end)
in if (errs > 0) then begin
(let _102_105 = (let _205_39 = (FStar_Util.string_of_int errs)
in (FStar_Util.print1 "Error: %s errors were reported (see above)\n" _205_39))
in (FStar_All.exit 1))
end else begin
()
end))

let report_universes_errors : Prims.int Prims.option  ->  Prims.unit = (fun nopt -> (let errs = (match (nopt) with
| None -> begin
(FStar_TypeChecker_Errors.get_err_count ())
end
| Some (n) -> begin
n
end)
in if (errs > 0) then begin
(let _102_112 = (let _205_42 = (FStar_Util.string_of_int errs)
in (FStar_Util.print1 "Error: %s errors were reported (see above)\n" _205_42))
in (FStar_All.exit 1))
end else begin
()
end))

let tc_one_file : FStar_Parser_DesugarEnv.env  ->  FStar_Tc_Env.env  ->  Prims.string  ->  (FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env * FStar_Absyn_Syntax.modul Prims.list) = (fun dsenv env fn -> (let _102_119 = (FStar_Parser_Driver.parse_file dsenv fn)
in (match (_102_119) with
| (dsenv, fmods) -> begin
(let _102_129 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun _102_122 m -> (match (_102_122) with
| (env, all_mods) -> begin
(let _102_126 = (FStar_Tc_Tc.check_module env m)
in (match (_102_126) with
| (ms, env) -> begin
(env, (FStar_List.append ms all_mods))
end))
end)) (env, [])))
in (match (_102_129) with
| (env, all_mods) -> begin
(dsenv, env, (FStar_List.rev all_mods))
end))
end)))

let tc_one_fragment : (FStar_Absyn_Syntax.modul * FStar_Absyn_Syntax.sigelt Prims.list) Prims.option  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Tc_Env.env  ->  Prims.string  ->  ((FStar_Absyn_Syntax.modul * FStar_Absyn_Syntax.sigelt Prims.list) Prims.option * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) Prims.option = (fun curmod dsenv env frag -> (FStar_All.try_with (fun _102_135 -> (match (()) with
| () -> begin
(match ((FStar_Parser_Driver.parse_fragment curmod dsenv frag)) with
| FStar_Parser_Driver.Empty -> begin
Some ((curmod, dsenv, env))
end
| FStar_Parser_Driver.Modul (dsenv, modul) -> begin
(let env = (match (curmod) with
| None -> begin
env
end
| Some (_102_157) -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("Interactive mode only supports a single module at the top-level")))
end)
in (let _102_163 = (FStar_Tc_Tc.tc_partial_modul env modul)
in (match (_102_163) with
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
(let _102_176 = (FStar_Tc_Tc.tc_more_partial_modul env modul decls)
in (match (_102_176) with
| (modul, npds', env) -> begin
Some ((Some ((modul, (FStar_List.append npds npds'))), dsenv, env))
end))
end)
end)
end)) (fun _102_134 -> (match (_102_134) with
| FStar_Absyn_Syntax.Error (msg, r) -> begin
(let _102_141 = (FStar_Tc_Errors.add_errors env (((msg, r))::[]))
in None)
end
| FStar_Absyn_Syntax.Err (msg) -> begin
(let _102_145 = (FStar_Tc_Errors.add_errors env (((msg, FStar_Absyn_Syntax.dummyRange))::[]))
in None)
end
| e -> begin
(Prims.raise e)
end))))

type input_chunks =
| Push of Prims.string
| Pop of Prims.string
| Code of (Prims.string * (Prims.string * Prims.string))

let is_Push : input_chunks  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Push (_) -> begin
true
end
| _ -> begin
false
end))

let is_Pop : input_chunks  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Pop (_) -> begin
true
end
| _ -> begin
false
end))

let is_Code : input_chunks  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Code (_) -> begin
true
end
| _ -> begin
false
end))

let ___Push____0 : input_chunks  ->  Prims.string = (fun projectee -> (match (projectee) with
| Push (_102_179) -> begin
_102_179
end))

let ___Pop____0 : input_chunks  ->  Prims.string = (fun projectee -> (match (projectee) with
| Pop (_102_182) -> begin
_102_182
end))

let ___Code____0 : input_chunks  ->  (Prims.string * (Prims.string * Prims.string)) = (fun projectee -> (match (projectee) with
| Code (_102_185) -> begin
_102_185
end))

type stack_elt =
((FStar_Absyn_Syntax.modul * FStar_Absyn_Syntax.sigelt Prims.list) Prims.option * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env)

type stack =
stack_elt Prims.list

let batch_mode_tc_no_prims : FStar_Parser_DesugarEnv.env  ->  FStar_Tc_Env.env  ->  Prims.string Prims.list  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) = (fun dsenv env filenames -> (let _102_203 = (FStar_All.pipe_right filenames (FStar_List.fold_left (fun _102_192 f -> (match (_102_192) with
| (all_mods, dsenv, env) -> begin
(let _102_194 = (FStar_Absyn_Util.reset_gensym ())
in (let _102_199 = (tc_one_file dsenv env f)
in (match (_102_199) with
| (dsenv, env, ms) -> begin
((FStar_List.append all_mods ms), dsenv, env)
end)))
end)) ([], dsenv, env)))
in (match (_102_203) with
| (all_mods, dsenv, env) -> begin
(let _102_204 = if ((FStar_ST.read FStar_Options.interactive) && ((FStar_Tc_Errors.get_err_count ()) = 0)) then begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
end else begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.finish ())
end
in (all_mods, dsenv, env))
end)))

let batch_mode_tc : Prims.string Prims.list  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) = (fun filenames -> (let _102_210 = (tc_prims ())
in (match (_102_210) with
| (prims_mod, dsenv, env) -> begin
(let _102_214 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (_102_214) with
| (all_mods, dsenv, env) -> begin
((FStar_List.append prims_mod all_mods), dsenv, env)
end))
end)))

let finished_message : FStar_Absyn_Syntax.modul Prims.list  ->  Prims.unit = (fun fmods -> if (not ((FStar_ST.read FStar_Options.silent))) then begin
(let msg = if (FStar_ST.read FStar_Options.verify) then begin
"Verifying"
end else begin
if (FStar_ST.read FStar_Options.pretype) then begin
"Lax type-checked"
end else begin
"Parsed and desugared"
end
end
in (let _102_219 = (FStar_All.pipe_right fmods (FStar_List.iter (fun m -> (let tag = if m.FStar_Absyn_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end
in if (FStar_Options.should_print_message m.FStar_Absyn_Syntax.name.FStar_Ident.str) then begin
(let _205_116 = (FStar_Util.format3 "%s %s: %s\n" msg tag (FStar_Absyn_Syntax.text_of_lid m.FStar_Absyn_Syntax.name))
in (FStar_Util.print_string _205_116))
end else begin
()
end))))
in (FStar_Util.print_string "All verification conditions discharged successfully\n")))
end else begin
()
end)

let interactive_mode = (fun dsenv env -> (let should_read_build_config = (FStar_ST.alloc true)
in (let should_log = ((FStar_ST.read FStar_Options.debug) <> [])
in (let log = if should_log then begin
(let transcript = (FStar_Util.open_file_for_writing "transcript")
in (fun line -> (let _102_227 = (FStar_Util.append_to_file transcript line)
in (FStar_Util.flush_file transcript))))
end else begin
(fun line -> ())
end
in (let _102_231 = if (let _205_124 = (FStar_ST.read FStar_Options.codegen)
in (FStar_Option.isSome _205_124)) then begin
(FStar_Util.print_string "Warning: Code-generation is not supported in interactive mode, ignoring the codegen flag")
end else begin
()
end
in (let chunk = (FStar_Util.new_string_builder ())
in (let stdin = (FStar_Util.open_stdin ())
in (let rec fill_chunk = (fun _102_236 -> (match (()) with
| () -> begin
(let line = (match ((FStar_Util.read_line stdin)) with
| None -> begin
(FStar_All.exit 0)
end
| Some (l) -> begin
l
end)
in (let _102_241 = (log line)
in (let l = (FStar_Util.trim_string line)
in if (FStar_Util.starts_with l "#end") then begin
(let responses = (match ((FStar_Util.split l " ")) with
| _102_247::ok::fail::[] -> begin
(ok, fail)
end
| _102_250 -> begin
("ok", "fail")
end)
in (let str = (FStar_Util.string_of_string_builder chunk)
in (let _102_253 = (FStar_Util.clear_string_builder chunk)
in Code ((str, responses)))))
end else begin
if (FStar_Util.starts_with l "#pop") then begin
(let _102_255 = (FStar_Util.clear_string_builder chunk)
in Pop (l))
end else begin
if (FStar_Util.starts_with l "#push") then begin
(let _102_257 = (FStar_Util.clear_string_builder chunk)
in Push (l))
end else begin
if (l = "#finish") then begin
(FStar_All.exit 0)
end else begin
(let _102_259 = (FStar_Util.string_builder_append chunk line)
in (let _102_261 = (FStar_Util.string_builder_append chunk "\n")
in (fill_chunk ())))
end
end
end
end)))
end))
in (let rec go = (fun stack curmod dsenv env -> (match ((fill_chunk ())) with
| Pop (msg) -> begin
(let _102_270 = (let _205_135 = (FStar_Parser_DesugarEnv.pop dsenv)
in (FStar_All.pipe_right _205_135 Prims.ignore))
in (let _102_272 = (let _205_136 = (FStar_Tc_Env.pop env msg)
in (FStar_All.pipe_right _205_136 Prims.ignore))
in (let _102_274 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in (let _102_276 = (let _205_137 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _205_137 Prims.ignore))
in (let _102_287 = (match (stack) with
| [] -> begin
(FStar_All.failwith "Too many pops")
end
| hd::tl -> begin
(hd, tl)
end)
in (match (_102_287) with
| ((curmod, dsenv, env), stack) -> begin
(go stack curmod dsenv env)
end))))))
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
in (let fail = (fun curmod dsenv_mark env_mark -> (let _102_318 = (let _205_156 = (FStar_Tc_Errors.report_all ())
in (FStar_All.pipe_right _205_156 Prims.ignore))
in (let _102_320 = (FStar_ST.op_Colon_Equals FStar_Tc_Errors.num_errs 0)
in (let _102_322 = (FStar_Util.print1 "%s\n" fail)
in (let _102_326 = (reset_mark dsenv_mark env_mark)
in (match (_102_326) with
| (dsenv, env) -> begin
(go stack curmod dsenv env)
end))))))
in (let _102_342 = if (FStar_ST.read should_read_build_config) then begin
if (let _205_157 = (FStar_Parser_ParseIt.get_bc_start_string ())
in (FStar_Util.starts_with text _205_157)) then begin
(let filenames = (match ((FStar_ST.read FStar_Options.interactive_context)) with
| Some (s) -> begin
(FStar_Parser_ParseIt.read_build_config_from_string s false text true)
end
| None -> begin
(FStar_Parser_ParseIt.read_build_config_from_string "" false text true)
end)
in (let _102_335 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (_102_335) with
| (_102_332, dsenv, env) -> begin
(let _102_336 = (FStar_ST.op_Colon_Equals should_read_build_config false)
in (dsenv, env))
end)))
end else begin
(let _102_338 = (FStar_ST.op_Colon_Equals should_read_build_config false)
in (dsenv, env))
end
end else begin
(dsenv, env)
end
in (match (_102_342) with
| (dsenv, env) -> begin
(let _102_345 = (mark dsenv env)
in (match (_102_345) with
| (dsenv_mark, env_mark) -> begin
(let res = (tc_one_fragment curmod dsenv_mark env_mark text)
in (match (res) with
| Some (curmod, dsenv, env) -> begin
if ((FStar_ST.read FStar_Tc_Errors.num_errs) = 0) then begin
(let _102_352 = (FStar_Util.print1 "\n%s\n" ok)
in (let _102_356 = (commit_mark dsenv env)
in (match (_102_356) with
| (dsenv, env) -> begin
(go stack curmod dsenv env)
end)))
end else begin
(fail curmod dsenv_mark env_mark)
end
end
| _102_358 -> begin
(fail curmod dsenv_mark env_mark)
end))
end))
end))))))
end))
in (go [] None dsenv env))))))))))

let codegen : FStar_Absyn_Syntax.modul Prims.list  ->  FStar_Tc_Env.env  ->  Prims.unit = (fun fmods env -> if (((FStar_ST.read FStar_Options.codegen) = Some ("OCaml")) || ((FStar_ST.read FStar_Options.codegen) = Some ("FSharp"))) then begin
(let _102_363 = (let _205_162 = (FStar_Extraction_ML_Env.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_ExtractMod.extract _205_162 fmods))
in (match (_102_363) with
| (c, mllibs) -> begin
(let mllibs = (FStar_List.flatten mllibs)
in (let ext = if ((FStar_ST.read FStar_Options.codegen) = Some ("FSharp")) then begin
".fs"
end else begin
".ml"
end
in (let newDocs = (FStar_List.collect FStar_Extraction_ML_Code.doc_of_mllib mllibs)
in (FStar_List.iter (fun _102_369 -> (match (_102_369) with
| (n, d) -> begin
(let _205_165 = (FStar_Options.prependOutputDir (Prims.strcat n ext))
in (let _205_164 = (FSharp_Format.pretty 120 d)
in (FStar_Util.write_file _205_165 _205_164)))
end)) newDocs))))
end))
end else begin
()
end)

let go = (fun _102_370 -> (let _102_374 = (process_args ())
in (match (_102_374) with
| (res, filenames) -> begin
(match (res) with
| FStar_Getopt.Help -> begin
(let _205_167 = (FStar_Options.specs ())
in (FStar_Options.display_usage _205_167))
end
| FStar_Getopt.Die (msg) -> begin
(FStar_Util.print_string msg)
end
| FStar_Getopt.GoOn -> begin
(let filenames = if ((FStar_ST.read FStar_Options.use_build_config) || ((not ((FStar_ST.read FStar_Options.interactive))) && ((FStar_List.length filenames) = 1))) then begin
(match (filenames) with
| f::[] -> begin
(FStar_Parser_Driver.read_build_config f)
end
| _102_382 -> begin
(let _102_383 = (FStar_Util.print_string "--use_build_config expects just a single file on the command line and no other arguments")
in (FStar_All.exit 1))
end)
end else begin
filenames
end
in if (FStar_ST.read FStar_Options.find_deps) then begin
(let _205_170 = (let _205_169 = (let _205_168 = (FStar_List.map FStar_Util.normalize_file_path filenames)
in (FStar_Util.concat_l "\n" _205_168))
in (FStar_Util.format1 "%s\n" _205_169))
in (FStar_Util.print_string _205_170))
end else begin
if ((FStar_ST.read FStar_Options.dep) <> None) then begin
(let _205_171 = (FStar_Parser_Dep.collect filenames)
in (FStar_Parser_Dep.print _205_171))
end else begin
if (FStar_ST.read FStar_Options.universes) then begin
(let _102_386 = (let _205_172 = (test_universes filenames)
in (FStar_All.pipe_right _205_172 Prims.ignore))
in (report_universes_errors None))
end else begin
(let _102_391 = (batch_mode_tc filenames)
in (match (_102_391) with
| (fmods, dsenv, env) -> begin
(let _102_392 = (report_errors None)
in if (FStar_ST.read FStar_Options.interactive) then begin
(interactive_mode dsenv env)
end else begin
(let _102_394 = (codegen fmods env)
in (finished_message fmods))
end)
end))
end
end
end)
end)
end)))

let main = (fun _102_396 -> (match (()) with
| () -> begin
(FStar_All.try_with (fun _102_398 -> (match (()) with
| () -> begin
(let _102_409 = (go ())
in (let _102_411 = (cleanup ())
in (FStar_All.exit 0)))
end)) (fun _102_397 -> (match (_102_397) with
| e -> begin
(let _102_401 = if (FStar_Absyn_Util.handleable e) then begin
(FStar_Absyn_Util.handle_err false () e)
end else begin
()
end
in (let _102_403 = if (FStar_ST.read FStar_Options.trace_error) then begin
(let _205_177 = (FStar_Util.message_of_exn e)
in (let _205_176 = (FStar_Util.trace_of_exn e)
in (FStar_Util.print2 "\nUnexpected error\n%s\n%s\n" _205_177 _205_176)))
end else begin
if (not ((FStar_Absyn_Util.handleable e))) then begin
(let _205_178 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1 "\nUnexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" _205_178))
end else begin
()
end
end
in (let _102_405 = (cleanup ())
in (FStar_All.exit 1))))
end)))
end))




