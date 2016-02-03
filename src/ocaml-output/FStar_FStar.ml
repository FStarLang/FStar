
open Prims
let process_args = (fun _65_1 -> (match (()) with
| () -> begin
(let file_list = (FStar_Util.mk_ref [])
in (let res = (let _131_6 = (FStar_Options.specs ())
in (FStar_Getopt.parse_cmdline _131_6 (fun i -> (let _131_5 = (let _131_4 = (FStar_ST.read file_list)
in (FStar_List.append _131_4 ((i)::[])))
in (FStar_ST.op_Colon_Equals file_list _131_5)))))
in (let _65_8 = (match (res) with
| FStar_Getopt.GoOn -> begin
(let _131_7 = (FStar_Options.set_fstar_home ())
in (Prims.ignore _131_7))
end
| _65_7 -> begin
()
end)
in (let _131_8 = (FStar_ST.read file_list)
in (res, _131_8)))))
end))

let cleanup = (fun _65_10 -> (match (()) with
| () -> begin
(FStar_Util.kill_all ())
end))

let has_prims_cache = (fun l -> (FStar_List.mem "Prims.cache" l))

let tc_prims = (fun _65_12 -> (match (()) with
| () -> begin
(let solver = if (FStar_ST.read FStar_Options.verify) then begin
FStar_ToSMT_Encode.solver
end else begin
FStar_ToSMT_Encode.dummy
end
in (let env = (FStar_Tc_Env.initial_env solver FStar_Absyn_Const.prims_lid)
in (let _65_15 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.init env)
in (let p = (FStar_Options.prims ())
in (let _65_20 = (let _131_15 = (FStar_Parser_DesugarEnv.empty_env ())
in (FStar_Parser_Driver.parse_file _131_15 p))
in (match (_65_20) with
| (dsenv, prims_mod) -> begin
(let _65_23 = (let _131_16 = (FStar_List.hd prims_mod)
in (FStar_Tc_Tc.check_module env _131_16))
in (match (_65_23) with
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
(let _65_29 = (let _131_19 = (FStar_Util.string_of_int errs)
in (FStar_Util.print1 "Error: %s errors were reported (see above)\n" _131_19))
in (FStar_All.exit 1))
end else begin
()
end))

let tc_one_file = (fun dsenv env fn -> (let _65_36 = (FStar_Parser_Driver.parse_file dsenv fn)
in (match (_65_36) with
| (dsenv, fmods) -> begin
(let _65_46 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun _65_39 m -> (match (_65_39) with
| (env, all_mods) -> begin
(let _65_43 = (FStar_Tc_Tc.check_module env m)
in (match (_65_43) with
| (ms, env) -> begin
(env, (FStar_List.append ms all_mods))
end))
end)) (env, [])))
in (match (_65_46) with
| (env, all_mods) -> begin
(dsenv, env, (FStar_List.rev all_mods))
end))
end)))

let tc_one_fragment = (fun curmod dsenv env frag -> (FStar_All.try_with (fun _65_52 -> (match (()) with
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
| Some (_65_74) -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("Interactive mode only supports a single module at the top-level")))
end)
in (let _65_80 = (FStar_Tc_Tc.tc_partial_modul env modul)
in (match (_65_80) with
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
(let _65_93 = (FStar_Tc_Tc.tc_more_partial_modul env modul decls)
in (match (_65_93) with
| (modul, npds', env) -> begin
Some ((Some ((modul, (FStar_List.append npds npds'))), dsenv, env))
end))
end)
end)
end)) (fun _65_51 -> (match (_65_51) with
| FStar_Absyn_Syntax.Error (msg, r) -> begin
(let _65_58 = (FStar_Tc_Errors.add_errors env (((msg, r))::[]))
in None)
end
| FStar_Absyn_Syntax.Err (msg) -> begin
(let _65_62 = (FStar_Tc_Errors.add_errors env (((msg, FStar_Absyn_Syntax.dummyRange))::[]))
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
| Push (_65_96) -> begin
_65_96
end))

let ___Pop____0 = (fun projectee -> (match (projectee) with
| Pop (_65_99) -> begin
_65_99
end))

let ___Code____0 = (fun projectee -> (match (projectee) with
| Code (_65_102) -> begin
_65_102
end))

type stack_elt =
((FStar_Absyn_Syntax.modul * FStar_Absyn_Syntax.sigelt Prims.list) Prims.option * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env)

type stack =
stack_elt Prims.list

let batch_mode_tc_no_prims = (fun dsenv env filenames -> (let _65_120 = (FStar_All.pipe_right filenames (FStar_List.fold_left (fun _65_109 f -> (match (_65_109) with
| (all_mods, dsenv, env) -> begin
(let _65_111 = (FStar_Absyn_Util.reset_gensym ())
in (let _65_116 = (tc_one_file dsenv env f)
in (match (_65_116) with
| (dsenv, env, ms) -> begin
((FStar_List.append all_mods ms), dsenv, env)
end)))
end)) ([], dsenv, env)))
in (match (_65_120) with
| (all_mods, dsenv, env) -> begin
(let _65_121 = if ((FStar_ST.read FStar_Options.interactive) && ((FStar_Tc_Errors.get_err_count ()) = 0)) then begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
end else begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.finish ())
end
in (all_mods, dsenv, env))
end)))

let find_deps_if_needed = (fun files -> if (FStar_ST.read FStar_Options.explicit_deps) then begin
files
end else begin
(let _65_127 = (FStar_Parser_Dep.collect files)
in (match (_65_127) with
| (_65_125, deps) -> begin
(let deps = (FStar_List.rev deps)
in (let deps = if ((let _131_90 = (FStar_List.hd deps)
in (FStar_Util.basename _131_90)) = "prims.fst") then begin
(FStar_List.tl deps)
end else begin
(FStar_All.failwith "dependency analysis did not find prims.fst?!")
end
in (let _65_132 = (FStar_List.iter (fun d -> (let d = (FStar_Util.basename d)
in if ((FStar_Util.get_file_extension d) = ".fsti") then begin
(let _131_94 = (let _131_93 = (FStar_Util.substring d 0 ((FStar_String.length d) - 5))
in (let _131_92 = (FStar_ST.read FStar_Options.admit_fsi)
in (_131_93)::_131_92))
in (FStar_ST.op_Colon_Equals FStar_Options.admit_fsi _131_94))
end else begin
if ((FStar_Util.get_file_extension d) = ".fsi") then begin
(let _131_97 = (let _131_96 = (FStar_Util.substring d 0 ((FStar_String.length d) - 4))
in (let _131_95 = (FStar_ST.read FStar_Options.admit_fsi)
in (_131_96)::_131_95))
in (FStar_ST.op_Colon_Equals FStar_Options.admit_fsi _131_97))
end else begin
()
end
end)) deps)
in deps)))
end))
end)

let batch_mode_tc = (fun filenames -> (let _65_138 = (tc_prims ())
in (match (_65_138) with
| (prims_mod, dsenv, env) -> begin
(let filenames = (find_deps_if_needed filenames)
in (let _65_143 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (_65_143) with
| (all_mods, dsenv, env) -> begin
((FStar_List.append prims_mod all_mods), dsenv, env)
end)))
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
in (let _65_148 = (FStar_All.pipe_right fmods (FStar_List.iter (fun m -> (let tag = if m.FStar_Absyn_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end
in if (FStar_Options.should_print_message m.FStar_Absyn_Syntax.name.FStar_Absyn_Syntax.str) then begin
(let _131_104 = (let _131_103 = (FStar_Absyn_Syntax.text_of_lid m.FStar_Absyn_Syntax.name)
in (FStar_Util.format3 "%s %s: %s\n" msg tag _131_103))
in (FStar_Util.print_string _131_104))
end else begin
()
end))))
in (FStar_Util.print_string "\x1b[0;1mAll verification conditions discharged successfully\x1b[0m\n")))
end else begin
()
end)

type interactive_state =
{chunk : FStar_Util.string_builder; stdin : FStar_Util.stream_reader Prims.option FStar_ST.ref; buffer : input_chunks Prims.list FStar_ST.ref; log : FStar_Util.file_handle Prims.option FStar_ST.ref}

let is_Mkinteractive_state = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkinteractive_state"))))

let the_interactive_state = (let _131_121 = (FStar_Util.new_string_builder ())
in (let _131_120 = (FStar_ST.alloc None)
in (let _131_119 = (FStar_ST.alloc [])
in (let _131_118 = (FStar_ST.alloc None)
in {chunk = _131_121; stdin = _131_120; buffer = _131_119; log = _131_118}))))

let rec read_chunk = (fun _65_155 -> (match (()) with
| () -> begin
(let s = the_interactive_state
in (let log = if ((FStar_ST.read FStar_Options.debug) <> []) then begin
(let transcript = (match ((FStar_ST.read s.log)) with
| Some (transcript) -> begin
transcript
end
| None -> begin
(let transcript = (FStar_Util.open_file_for_writing "transcript")
in (let _65_161 = (FStar_ST.op_Colon_Equals s.log (Some (transcript)))
in transcript))
end)
in (fun line -> (let _65_165 = (FStar_Util.append_to_file transcript line)
in (FStar_Util.flush_file transcript))))
end else begin
(fun _65_167 -> ())
end
in (let stdin = (match ((FStar_ST.read s.stdin)) with
| Some (i) -> begin
i
end
| None -> begin
(let i = (FStar_Util.open_stdin ())
in (let _65_174 = (FStar_ST.op_Colon_Equals s.stdin (Some (i)))
in i))
end)
in (let line = (match ((FStar_Util.read_line stdin)) with
| None -> begin
(FStar_All.exit 0)
end
| Some (l) -> begin
l
end)
in (let _65_181 = (log line)
in (let l = (FStar_Util.trim_string line)
in if (FStar_Util.starts_with l "#end") then begin
(let responses = (match ((FStar_Util.split l " ")) with
| _65_187::ok::fail::[] -> begin
(ok, fail)
end
| _65_190 -> begin
("ok", "fail")
end)
in (let str = (FStar_Util.string_of_string_builder s.chunk)
in (let _65_193 = (FStar_Util.clear_string_builder s.chunk)
in Code ((str, responses)))))
end else begin
if (FStar_Util.starts_with l "#pop") then begin
(let _65_195 = (FStar_Util.clear_string_builder s.chunk)
in Pop (l))
end else begin
if (FStar_Util.starts_with l "#push") then begin
(let _65_197 = (FStar_Util.clear_string_builder s.chunk)
in Push (l))
end else begin
if (l = "#finish") then begin
(FStar_All.exit 0)
end else begin
(let _65_199 = (FStar_Util.string_builder_append s.chunk line)
in (let _65_201 = (FStar_Util.string_builder_append s.chunk "\n")
in (read_chunk ())))
end
end
end
end))))))
end))

let shift_chunk = (fun _65_203 -> (match (()) with
| () -> begin
(let s = the_interactive_state
in (match ((FStar_ST.read s.buffer)) with
| [] -> begin
(read_chunk ())
end
| chunk::chunks -> begin
(let _65_209 = (FStar_ST.op_Colon_Equals s.buffer chunks)
in chunk)
end))
end))

let fill_buffer = (fun _65_211 -> (match (()) with
| () -> begin
(let s = the_interactive_state
in (let _131_136 = (let _131_135 = (FStar_ST.read s.buffer)
in (let _131_134 = (let _131_133 = (read_chunk ())
in (_131_133)::[])
in (FStar_List.append _131_135 _131_134)))
in (FStar_ST.op_Colon_Equals s.buffer _131_136)))
end))

let interactive_mode = (fun dsenv env -> (let _65_215 = if (let _131_139 = (FStar_ST.read FStar_Options.codegen)
in (FStar_Option.isSome _131_139)) then begin
(FStar_Util.print_string "Warning: Code-generation is not supported in interactive mode, ignoring the codegen flag")
end else begin
()
end
in (let rec go = (fun stack curmod dsenv env -> (match ((shift_chunk ())) with
| Pop (msg) -> begin
(let _65_224 = (let _131_148 = (FStar_Parser_DesugarEnv.pop dsenv)
in (FStar_All.pipe_right _131_148 Prims.ignore))
in (let _65_226 = (let _131_149 = (FStar_Tc_Env.pop env msg)
in (FStar_All.pipe_right _131_149 Prims.ignore))
in (let _65_228 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in (let _65_230 = (let _131_150 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _131_150 Prims.ignore))
in (let _65_241 = (match (stack) with
| [] -> begin
(FStar_All.failwith "Too many pops")
end
| hd::tl -> begin
(hd, tl)
end)
in (match (_65_241) with
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
in (let fail = (fun curmod dsenv_mark env_mark -> (let _65_272 = (let _131_169 = (FStar_Tc_Errors.report_all ())
in (FStar_All.pipe_right _131_169 Prims.ignore))
in (let _65_274 = (FStar_ST.op_Colon_Equals FStar_Tc_Errors.num_errs 0)
in (let _65_276 = (FStar_Util.print1 "%s\n" fail)
in (let _65_280 = (reset_mark dsenv_mark env_mark)
in (match (_65_280) with
| (dsenv, env) -> begin
(go stack curmod dsenv env)
end))))))
in (let _65_283 = (mark dsenv env)
in (match (_65_283) with
| (dsenv_mark, env_mark) -> begin
(let res = (tc_one_fragment curmod dsenv_mark env_mark text)
in (match (res) with
| Some (curmod, dsenv, env) -> begin
if ((FStar_ST.read FStar_Tc_Errors.num_errs) = 0) then begin
(let _65_290 = (FStar_Util.print1 "\n%s\n" ok)
in (let _65_294 = (commit_mark dsenv env)
in (match (_65_294) with
| (dsenv, env) -> begin
(go stack curmod dsenv env)
end)))
end else begin
(fail curmod dsenv_mark env_mark)
end
end
| _65_296 -> begin
(fail curmod dsenv_mark env_mark)
end))
end))))))
end))
in (go [] None dsenv env))))

let codegen = (fun fmods env -> if (((FStar_ST.read FStar_Options.codegen) = Some ("OCaml")) || ((FStar_ST.read FStar_Options.codegen) = Some ("FSharp"))) then begin
(let _65_301 = (let _131_174 = (FStar_Extraction_ML_Env.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_ExtractMod.extract _131_174 fmods))
in (match (_65_301) with
| (c, mllibs) -> begin
(let mllibs = (FStar_List.flatten mllibs)
in (let ext = if ((FStar_ST.read FStar_Options.codegen) = Some ("FSharp")) then begin
".fs"
end else begin
".ml"
end
in (let newDocs = (FStar_List.collect FStar_Extraction_ML_Code.doc_of_mllib mllibs)
in (FStar_List.iter (fun _65_307 -> (match (_65_307) with
| (n, d) -> begin
(let _131_177 = (FStar_Options.prependOutputDir (Prims.strcat n ext))
in (let _131_176 = (FSharp_Format.pretty 120 d)
in (FStar_Util.write_file _131_177 _131_176)))
end)) newDocs))))
end))
end else begin
()
end)

exception Found of (Prims.string)

let is_Found = (fun _discr_ -> (match (_discr_) with
| Found (_) -> begin
true
end
| _ -> begin
false
end))

let ___Found____0 = (fun projectee -> (match (projectee) with
| Found (_65_309) -> begin
_65_309
end))

let find_initial_module_name = (fun _65_310 -> (match (()) with
| () -> begin
(let _65_311 = (fill_buffer ())
in (let _65_313 = (fill_buffer ())
in (FStar_All.try_with (fun _65_316 -> (match (()) with
| () -> begin
(let _65_337 = (match ((FStar_ST.read the_interactive_state.buffer)) with
| Push (_65_328)::Code (code, _65_324)::[] -> begin
(let lines = (FStar_Util.split code "\n")
in (FStar_List.iter (fun line -> (let line = (FStar_Util.trim_string line)
in if (((FStar_String.length line) > 7) && ((FStar_Util.substring line 0 6) = "module")) then begin
(let module_name = (FStar_Util.substring line 7 ((FStar_String.length line) - 7))
in (Prims.raise (Found (module_name))))
end else begin
()
end)) lines))
end
| _65_336 -> begin
()
end)
in None)
end)) (fun _65_315 -> (match (_65_315) with
| Found (n) -> begin
Some (n)
end)))))
end))

let detect_dependencies_with_first_interactive_chunk = (fun _65_339 -> (match (()) with
| () -> begin
(match ((find_initial_module_name ())) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("No initial module directive found\n")))
end
| Some (module_name) -> begin
(let file_of_module_name = (FStar_Parser_Dep.build_map [])
in (let filename = (FStar_Util.smap_try_find file_of_module_name (FStar_String.lowercase module_name))
in (match (filename) with
| None -> begin
(let _131_191 = (let _131_190 = (FStar_Util.format2 "I found a \"module %s\" directive, but there is no %s.fst\n" module_name module_name)
in FStar_Absyn_Syntax.Err (_131_190))
in (Prims.raise _131_191))
end
| Some (filename) -> begin
(let _65_351 = (FStar_Parser_Dep.collect ((filename)::[]))
in (match (_65_351) with
| (_65_349, all_filenames) -> begin
(let _131_192 = (FStar_List.tl all_filenames)
in (FStar_List.rev _131_192))
end))
end)))
end)
end))

let go = (fun _65_352 -> (let _65_356 = (process_args ())
in (match (_65_356) with
| (res, filenames) -> begin
(match (res) with
| FStar_Getopt.Help -> begin
(let _131_194 = (FStar_Options.specs ())
in (FStar_Options.display_usage _131_194))
end
| FStar_Getopt.Die (msg) -> begin
(FStar_Util.print_string msg)
end
| FStar_Getopt.GoOn -> begin
if ((FStar_ST.read FStar_Options.dep) <> None) then begin
(let _131_195 = (FStar_Parser_Dep.collect filenames)
in (FStar_Parser_Dep.print _131_195))
end else begin
if (FStar_ST.read FStar_Options.interactive) then begin
(let filenames = if (FStar_ST.read FStar_Options.explicit_deps) then begin
(let _65_361 = if ((FStar_List.length filenames) = 0) then begin
(FStar_Util.print_endline "--explicit_deps was provided without a file list!")
end else begin
()
end
in filenames)
end else begin
(let _65_363 = if ((FStar_List.length filenames) > 0) then begin
(FStar_Util.print_endline "ignoring the file list (no --explicit_deps)")
end else begin
()
end
in (detect_dependencies_with_first_interactive_chunk ()))
end
in (let _65_369 = (batch_mode_tc filenames)
in (match (_65_369) with
| (fmods, dsenv, env) -> begin
(interactive_mode dsenv env)
end)))
end else begin
if ((FStar_List.length filenames) >= 1) then begin
(let _65_373 = (batch_mode_tc filenames)
in (match (_65_373) with
| (fmods, dsenv, env) -> begin
(let _65_374 = (report_errors None)
in (let _65_376 = (codegen fmods env)
in (finished_message fmods)))
end))
end else begin
(FStar_Util.print_string "No file provided\n")
end
end
end
end)
end)))

let main = (fun _65_378 -> (match (()) with
| () -> begin
(FStar_All.try_with (fun _65_380 -> (match (()) with
| () -> begin
(let _65_391 = (go ())
in (let _65_393 = (cleanup ())
in (FStar_All.exit 0)))
end)) (fun _65_379 -> (match (_65_379) with
| e -> begin
(let _65_383 = if (FStar_Absyn_Util.handleable e) then begin
(FStar_Absyn_Util.handle_err false () e)
end else begin
()
end
in (let _65_385 = if (FStar_ST.read FStar_Options.trace_error) then begin
(let _131_200 = (FStar_Util.message_of_exn e)
in (let _131_199 = (FStar_Util.trace_of_exn e)
in (FStar_Util.print2 "\nUnexpected error\n%s\n%s\n" _131_200 _131_199)))
end else begin
if (not ((FStar_Absyn_Util.handleable e))) then begin
(let _131_201 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1 "\nUnexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" _131_201))
end else begin
()
end
end
in (let _65_387 = (cleanup ())
in (FStar_All.exit 1))))
end)))
end))




