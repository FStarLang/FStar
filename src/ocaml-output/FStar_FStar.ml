
open Prims
let process_args = (fun _66_1 -> (match (()) with
| () -> begin
(let file_list = (FStar_Util.mk_ref [])
in (let res = (let _133_6 = (FStar_Options.specs ())
in (FStar_Getopt.parse_cmdline _133_6 (fun i -> (let _133_5 = (let _133_4 = (FStar_ST.read file_list)
in (FStar_List.append _133_4 ((i)::[])))
in (FStar_ST.op_Colon_Equals file_list _133_5)))))
in (let _66_8 = (match (res) with
| FStar_Getopt.GoOn -> begin
(let _133_7 = (FStar_Options.set_fstar_home ())
in (Prims.ignore _133_7))
end
| _66_7 -> begin
()
end)
in (let _133_8 = (FStar_ST.read file_list)
in (res, _133_8)))))
end))

let cleanup = (fun _66_10 -> (match (()) with
| () -> begin
(FStar_Util.kill_all ())
end))

let has_prims_cache = (fun l -> (FStar_List.mem "Prims.cache" l))

let tc_prims = (fun _66_12 -> (match (()) with
| () -> begin
(let solver = if (FStar_ST.read FStar_Options.verify) then begin
FStar_ToSMT_Encode.solver
end else begin
FStar_ToSMT_Encode.dummy
end
in (let env = (FStar_Tc_Env.initial_env solver FStar_Absyn_Const.prims_lid)
in (let _66_15 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.init env)
in (let p = (FStar_Options.prims ())
in (let _66_20 = (let _133_15 = (FStar_Parser_DesugarEnv.empty_env ())
in (FStar_Parser_Driver.parse_file _133_15 p))
in (match (_66_20) with
| (dsenv, prims_mod) -> begin
(let _66_23 = (let _133_16 = (FStar_List.hd prims_mod)
in (FStar_Tc_Tc.check_module env _133_16))
in (match (_66_23) with
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
in if (errs > 0) then begin
(let _66_29 = (let _133_19 = (FStar_Util.string_of_int errs)
in (FStar_Util.print1 "Error: %s errors were reported (see above)\n" _133_19))
in (FStar_All.exit 1))
end else begin
()
end))

let tc_one_file = (fun dsenv env fn -> (let _66_36 = (FStar_Parser_Driver.parse_file dsenv fn)
in (match (_66_36) with
| (dsenv, fmods) -> begin
(let _66_46 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun _66_39 m -> (match (_66_39) with
| (env, all_mods) -> begin
(let _66_43 = (FStar_Tc_Tc.check_module env m)
in (match (_66_43) with
| (ms, env) -> begin
(env, (FStar_List.append ms all_mods))
end))
end)) (env, [])))
in (match (_66_46) with
| (env, all_mods) -> begin
(dsenv, env, (FStar_List.rev all_mods))
end))
end)))

let tc_one_fragment = (fun curmod dsenv env frag -> (FStar_All.try_with (fun _66_52 -> (match (()) with
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
| Some (_66_74) -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("Interactive mode only supports a single module at the top-level")))
end)
in (let _66_80 = (FStar_Tc_Tc.tc_partial_modul env modul)
in (match (_66_80) with
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
(let _66_93 = (FStar_Tc_Tc.tc_more_partial_modul env modul decls)
in (match (_66_93) with
| (modul, npds', env) -> begin
Some ((Some ((modul, (FStar_List.append npds npds'))), dsenv, env))
end))
end)
end)
end)) (fun _66_51 -> (match (_66_51) with
| FStar_Absyn_Syntax.Error (msg, r) -> begin
(let _66_58 = (FStar_Tc_Errors.add_errors env (((msg, r))::[]))
in None)
end
| FStar_Absyn_Syntax.Err (msg) -> begin
(let _66_62 = (FStar_Tc_Errors.add_errors env (((msg, FStar_Absyn_Syntax.dummyRange))::[]))
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
| Push (_66_96) -> begin
_66_96
end))

let ___Pop____0 = (fun projectee -> (match (projectee) with
| Pop (_66_99) -> begin
_66_99
end))

let ___Code____0 = (fun projectee -> (match (projectee) with
| Code (_66_102) -> begin
_66_102
end))

type stack_elt =
((FStar_Absyn_Syntax.modul * FStar_Absyn_Syntax.sigelt Prims.list) Prims.option * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env)

type stack =
stack_elt Prims.list

let batch_mode_tc_no_prims = (fun dsenv env filenames -> (let _66_120 = (FStar_All.pipe_right filenames (FStar_List.fold_left (fun _66_109 f -> (match (_66_109) with
| (all_mods, dsenv, env) -> begin
(let _66_111 = (FStar_Absyn_Util.reset_gensym ())
in (let _66_116 = (tc_one_file dsenv env f)
in (match (_66_116) with
| (dsenv, env, ms) -> begin
((FStar_List.append all_mods ms), dsenv, env)
end)))
end)) ([], dsenv, env)))
in (match (_66_120) with
| (all_mods, dsenv, env) -> begin
(let _66_121 = if ((FStar_ST.read FStar_Options.interactive) && ((FStar_Tc_Errors.get_err_count ()) = 0)) then begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
end else begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.finish ())
end
in (all_mods, dsenv, env))
end)))

let batch_mode_tc = (fun filenames -> (let _66_127 = (tc_prims ())
in (match (_66_127) with
| (prims_mod, dsenv, env) -> begin
(let _66_131 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (_66_131) with
| (all_mods, dsenv, env) -> begin
((FStar_List.append prims_mod all_mods), dsenv, env)
end))
end)))

let finished_message = (fun fmods -> if (not ((FStar_ST.read FStar_Options.silent))) then begin
(let msg = if (FStar_ST.read FStar_Options.verify) then begin
"Verifying"
end else begin
if (FStar_ST.read FStar_Options.pretype) then begin
"Lax type-checked"
end else begin
"Parsed and desugared"
end
end
in (let _66_136 = (FStar_All.pipe_right fmods (FStar_List.iter (fun m -> (let tag = if m.FStar_Absyn_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end
in if (FStar_Options.should_print_message m.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str) then begin
(let _133_94 = (let _133_93 = (FStar_Absyn_Syntax.text_of_lid m.FStar_Absyn_Syntax.name)
in (FStar_Util.format3 "%s %s: %s\n" msg tag _133_93))
in (FStar_Util.print_string _133_94))
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
in (fun line -> (let _66_144 = (FStar_Util.append_to_file transcript line)
in (FStar_Util.flush_file transcript))))
end else begin
(fun line -> ())
end
in (let _66_148 = if (let _133_102 = (FStar_ST.read FStar_Options.codegen)
in (FStar_Option.isSome _133_102)) then begin
(FStar_Util.print_string "Warning: Code-generation is not supported in interactive mode, ignoring the codegen flag")
end else begin
()
end
in (let chunk = (FStar_Util.new_string_builder ())
in (let stdin = (FStar_Util.open_stdin ())
in (let rec fill_chunk = (fun _66_153 -> (match (()) with
| () -> begin
(let line = (match ((FStar_Util.read_line stdin)) with
| None -> begin
(FStar_All.exit 0)
end
| Some (l) -> begin
l
end)
in (let _66_158 = (log line)
in (let l = (FStar_Util.trim_string line)
in if (FStar_Util.starts_with l "#end") then begin
(let responses = (match ((FStar_Util.split l " ")) with
| _66_164::ok::fail::[] -> begin
(ok, fail)
end
| _66_167 -> begin
("ok", "fail")
end)
in (let str = (FStar_Util.string_of_string_builder chunk)
in (let _66_170 = (FStar_Util.clear_string_builder chunk)
in Code ((str, responses)))))
end else begin
if (FStar_Util.starts_with l "#pop") then begin
(let _66_172 = (FStar_Util.clear_string_builder chunk)
in Pop (l))
end else begin
if (FStar_Util.starts_with l "#push") then begin
(let _66_174 = (FStar_Util.clear_string_builder chunk)
in Push (l))
end else begin
if (l = "#finish") then begin
(FStar_All.exit 0)
end else begin
(let _66_176 = (FStar_Util.string_builder_append chunk line)
in (let _66_178 = (FStar_Util.string_builder_append chunk "\n")
in (fill_chunk ())))
end
end
end
end)))
end))
in (let rec go = (fun stack curmod dsenv env -> (match ((fill_chunk ())) with
| Pop (msg) -> begin
(let _66_187 = (let _133_113 = (FStar_Parser_DesugarEnv.pop dsenv)
in (FStar_All.pipe_right _133_113 Prims.ignore))
in (let _66_189 = (let _133_114 = (FStar_Tc_Env.pop env msg)
in (FStar_All.pipe_right _133_114 Prims.ignore))
in (let _66_191 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in (let _66_193 = (let _133_115 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _133_115 Prims.ignore))
in (let _66_204 = (match (stack) with
| [] -> begin
(FStar_All.failwith "Too many pops")
end
| hd::tl -> begin
(hd, tl)
end)
in (match (_66_204) with
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
in (let fail = (fun curmod dsenv_mark env_mark -> (let _66_235 = (let _133_134 = (FStar_Tc_Errors.report_all ())
in (FStar_All.pipe_right _133_134 Prims.ignore))
in (let _66_237 = (FStar_ST.op_Colon_Equals FStar_Tc_Errors.num_errs 0)
in (let _66_239 = (FStar_Util.print1 "%s\n" fail)
in (let _66_243 = (reset_mark dsenv_mark env_mark)
in (match (_66_243) with
| (dsenv, env) -> begin
(go stack curmod dsenv env)
end))))))
in (let _66_259 = if (FStar_ST.read should_read_build_config) then begin
if (let _133_135 = (FStar_Parser_ParseIt.get_bc_start_string ())
in (FStar_Util.starts_with text _133_135)) then begin
(let filenames = (match ((FStar_ST.read FStar_Options.interactive_context)) with
| Some (s) -> begin
(FStar_Parser_ParseIt.read_build_config_from_string s false text true)
end
| None -> begin
(FStar_Parser_ParseIt.read_build_config_from_string "" false text true)
end)
in (let _66_252 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (_66_252) with
| (_66_249, dsenv, env) -> begin
(let _66_253 = (FStar_ST.op_Colon_Equals should_read_build_config false)
in (dsenv, env))
end)))
end else begin
(let _66_255 = (FStar_ST.op_Colon_Equals should_read_build_config false)
in (dsenv, env))
end
end else begin
(dsenv, env)
end
in (match (_66_259) with
| (dsenv, env) -> begin
(let _66_262 = (mark dsenv env)
in (match (_66_262) with
| (dsenv_mark, env_mark) -> begin
(let res = (tc_one_fragment curmod dsenv_mark env_mark text)
in (match (res) with
| Some (curmod, dsenv, env) -> begin
if ((FStar_ST.read FStar_Tc_Errors.num_errs) = 0) then begin
(let _66_269 = (FStar_Util.print1 "\n%s\n" ok)
in (let _66_273 = (commit_mark dsenv env)
in (match (_66_273) with
| (dsenv, env) -> begin
(go stack curmod dsenv env)
end)))
end else begin
(fail curmod dsenv_mark env_mark)
end
end
| _66_275 -> begin
(fail curmod dsenv_mark env_mark)
end))
end))
end))))))
end))
in (go [] None dsenv env))))))))))

let codegen = (fun fmods env -> if (((FStar_ST.read FStar_Options.codegen) = Some ("OCaml")) || ((FStar_ST.read FStar_Options.codegen) = Some ("FSharp"))) then begin
(let _66_280 = (let _133_140 = (FStar_Extraction_ML_Env.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_ExtractMod.extract _133_140 fmods))
in (match (_66_280) with
| (c, mllibs) -> begin
(let mllibs = (FStar_List.flatten mllibs)
in (let ext = if ((FStar_ST.read FStar_Options.codegen) = Some ("FSharp")) then begin
".fs"
end else begin
".ml"
end
in (let newDocs = (FStar_List.collect FStar_Extraction_ML_Code.doc_of_mllib mllibs)
in (FStar_List.iter (fun _66_286 -> (match (_66_286) with
| (n, d) -> begin
(let _133_143 = (FStar_Options.prependOutputDir (Prims.strcat n ext))
in (let _133_142 = (FSharp_Format.pretty 120 d)
in (FStar_Util.write_file _133_143 _133_142)))
end)) newDocs))))
end))
end else begin
if ((FStar_ST.read FStar_Options.codegen) = Some ("Wysteria")) then begin
(FStar_Extraction_Wysteria_Extract.extract fmods env)
end else begin
()
end
end)

let go = (fun _66_287 -> (let _66_291 = (process_args ())
in (match (_66_291) with
| (res, filenames) -> begin
(match (res) with
| FStar_Getopt.Help -> begin
(let _133_145 = (FStar_Options.specs ())
in (FStar_Options.display_usage _133_145))
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
| _66_299 -> begin
(let _66_300 = (FStar_Util.print_string "--use_build_config expects just a single file on the command line and no other arguments")
in (FStar_All.exit 1))
end)
end else begin
filenames
end
in if (FStar_ST.read FStar_Options.find_deps) then begin
(let _133_148 = (let _133_147 = (let _133_146 = (FStar_List.map FStar_Util.normalize_file_path filenames)
in (FStar_Util.concat_l "\n" _133_146))
in (FStar_Util.format1 "%s\n" _133_147))
in (FStar_Util.print_string _133_148))
end else begin
if ((FStar_ST.read FStar_Options.dep) <> None) then begin
(let _133_149 = (FStar_Parser_Dep.collect filenames)
in (FStar_Parser_Dep.print _133_149))
end else begin
(let _66_306 = (batch_mode_tc filenames)
in (match (_66_306) with
| (fmods, dsenv, env) -> begin
(let _66_307 = (report_errors None)
in if (FStar_ST.read FStar_Options.interactive) then begin
(interactive_mode dsenv env)
end else begin
(let _66_309 = (codegen fmods env)
in (finished_message fmods))
end)
end))
end
end)
end)
end)))

let main = (fun _66_311 -> (match (()) with
| () -> begin
(FStar_All.try_with (fun _66_313 -> (match (()) with
| () -> begin
(let _66_324 = (go ())
in (let _66_326 = (cleanup ())
in (FStar_All.exit 0)))
end)) (fun _66_312 -> (match (_66_312) with
| e -> begin
(let _66_316 = if (FStar_Absyn_Util.handleable e) then begin
(FStar_Absyn_Util.handle_err false () e)
end else begin
()
end
in (let _66_318 = if (FStar_ST.read FStar_Options.trace_error) then begin
(let _133_154 = (FStar_Util.message_of_exn e)
in (let _133_153 = (FStar_Util.trace_of_exn e)
in (FStar_Util.print2 "\nUnexpected error\n%s\n%s\n" _133_154 _133_153)))
end else begin
if (not ((FStar_Absyn_Util.handleable e))) then begin
(let _133_155 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1 "\nUnexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" _133_155))
end else begin
()
end
end
in (let _66_320 = (cleanup ())
in (FStar_All.exit 1))))
end)))
end))




