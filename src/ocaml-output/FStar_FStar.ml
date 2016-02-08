
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

let find_deps_if_needed : Prims.string Prims.list  ->  Prims.string Prims.list = (fun files -> if (FStar_ST.read FStar_Options.explicit_deps) then begin
files
end else begin
(let _102_210 = (FStar_Parser_Dep.collect files)
in (match (_102_210) with
| (_102_208, deps) -> begin
(let deps = (FStar_List.rev deps)
in (let deps = if ((let _205_113 = (FStar_List.hd deps)
in (FStar_Util.basename _205_113)) = "prims.fst") then begin
(FStar_List.tl deps)
end else begin
(FStar_All.failwith "dependency analysis did not find prims.fst?!")
end
in (let _102_215 = (FStar_List.iter (fun d -> (let d = (FStar_Util.basename d)
in if ((FStar_Util.get_file_extension d) = "fsti") then begin
(let _205_117 = (let _205_116 = (FStar_Util.substring d 0 ((FStar_String.length d) - 5))
in (let _205_115 = (FStar_ST.read FStar_Options.admit_fsi)
in (_205_116)::_205_115))
in (FStar_ST.op_Colon_Equals FStar_Options.admit_fsi _205_117))
end else begin
if ((FStar_Util.get_file_extension d) = "fsi") then begin
(let _205_120 = (let _205_119 = (FStar_Util.substring d 0 ((FStar_String.length d) - 4))
in (let _205_118 = (FStar_ST.read FStar_Options.admit_fsi)
in (_205_119)::_205_118))
in (FStar_ST.op_Colon_Equals FStar_Options.admit_fsi _205_120))
end else begin
()
end
end)) deps)
in deps)))
end))
end)

let batch_mode_tc : Prims.string Prims.list  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) = (fun filenames -> (let _102_221 = (tc_prims ())
in (match (_102_221) with
| (prims_mod, dsenv, env) -> begin
(let filenames = (find_deps_if_needed filenames)
in (let _102_226 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (_102_226) with
| (all_mods, dsenv, env) -> begin
((FStar_List.append prims_mod all_mods), dsenv, env)
end)))
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
in (let _102_231 = (FStar_All.pipe_right fmods (FStar_List.iter (fun m -> (let tag = if m.FStar_Absyn_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end
in if (FStar_Options.should_print_message m.FStar_Absyn_Syntax.name.FStar_Ident.str) then begin
(let _205_126 = (FStar_Util.format3 "%s %s: %s\n" msg tag (FStar_Absyn_Syntax.text_of_lid m.FStar_Absyn_Syntax.name))
in (FStar_Util.print_string _205_126))
end else begin
()
end))))
in (let _205_128 = (let _205_127 = (FStar_Util.colorize_bold "All verification conditions discharged successfully")
in (FStar_Util.format1 "%s\n" _205_127))
in (FStar_Util.print_string _205_128))))
end else begin
()
end)

type interactive_state =
{chunk : FStar_Util.string_builder; stdin : FStar_Util.stream_reader Prims.option FStar_ST.ref; buffer : input_chunks Prims.list FStar_ST.ref; log : FStar_Util.file_handle Prims.option FStar_ST.ref}

let is_Mkinteractive_state : interactive_state  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkinteractive_state"))))

let the_interactive_state : interactive_state = (let _205_145 = (FStar_Util.new_string_builder ())
in (let _205_144 = (FStar_ST.alloc None)
in (let _205_143 = (FStar_ST.alloc [])
in (let _205_142 = (FStar_ST.alloc None)
in {chunk = _205_145; stdin = _205_144; buffer = _205_143; log = _205_142}))))

let rec read_chunk : Prims.unit  ->  input_chunks = (fun _102_238 -> (match (()) with
| () -> begin
(let s = the_interactive_state
in (let log = if ((FStar_ST.read FStar_Options.debug) <> []) then begin
(let transcript = (match ((FStar_ST.read s.log)) with
| Some (transcript) -> begin
transcript
end
| None -> begin
(let transcript = (FStar_Util.open_file_for_writing "transcript")
in (let _102_244 = (FStar_ST.op_Colon_Equals s.log (Some (transcript)))
in transcript))
end)
in (fun line -> (let _102_248 = (FStar_Util.append_to_file transcript line)
in (FStar_Util.flush_file transcript))))
end else begin
(fun _102_250 -> ())
end
in (let stdin = (match ((FStar_ST.read s.stdin)) with
| Some (i) -> begin
i
end
| None -> begin
(let i = (FStar_Util.open_stdin ())
in (let _102_257 = (FStar_ST.op_Colon_Equals s.stdin (Some (i)))
in i))
end)
in (let line = (match ((FStar_Util.read_line stdin)) with
| None -> begin
(FStar_All.exit 0)
end
| Some (l) -> begin
l
end)
in (let _102_264 = (log line)
in (let l = (FStar_Util.trim_string line)
in if (FStar_Util.starts_with l "#end") then begin
(let responses = (match ((FStar_Util.split l " ")) with
| _102_270::ok::fail::[] -> begin
(ok, fail)
end
| _102_273 -> begin
("ok", "fail")
end)
in (let str = (FStar_Util.string_of_string_builder s.chunk)
in (let _102_276 = (FStar_Util.clear_string_builder s.chunk)
in Code ((str, responses)))))
end else begin
if (FStar_Util.starts_with l "#pop") then begin
(let _102_278 = (FStar_Util.clear_string_builder s.chunk)
in Pop (l))
end else begin
if (FStar_Util.starts_with l "#push") then begin
(let _102_280 = (FStar_Util.clear_string_builder s.chunk)
in Push (l))
end else begin
if (l = "#finish") then begin
(FStar_All.exit 0)
end else begin
(let _102_282 = (FStar_Util.string_builder_append s.chunk line)
in (let _102_284 = (FStar_Util.string_builder_append s.chunk "\n")
in (read_chunk ())))
end
end
end
end))))))
end))

let shift_chunk : Prims.unit  ->  input_chunks = (fun _102_286 -> (match (()) with
| () -> begin
(let s = the_interactive_state
in (match ((FStar_ST.read s.buffer)) with
| [] -> begin
(read_chunk ())
end
| chunk::chunks -> begin
(let _102_292 = (FStar_ST.op_Colon_Equals s.buffer chunks)
in chunk)
end))
end))

let fill_buffer : Prims.unit  ->  Prims.unit = (fun _102_294 -> (match (()) with
| () -> begin
(let s = the_interactive_state
in (let _205_160 = (let _205_159 = (FStar_ST.read s.buffer)
in (let _205_158 = (let _205_157 = (read_chunk ())
in (_205_157)::[])
in (FStar_List.append _205_159 _205_158)))
in (FStar_ST.op_Colon_Equals s.buffer _205_160)))
end))

let interactive_mode = (fun dsenv env -> (let _102_298 = if (let _205_163 = (FStar_ST.read FStar_Options.codegen)
in (FStar_Option.isSome _205_163)) then begin
(FStar_Util.print_string "Warning: Code-generation is not supported in interactive mode, ignoring the codegen flag")
end else begin
()
end
in (let rec go = (fun stack curmod dsenv env -> (match ((shift_chunk ())) with
| Pop (msg) -> begin
(let _102_307 = (let _205_172 = (FStar_Parser_DesugarEnv.pop dsenv)
in (FStar_All.pipe_right _205_172 Prims.ignore))
in (let _102_309 = (let _205_173 = (FStar_Tc_Env.pop env msg)
in (FStar_All.pipe_right _205_173 Prims.ignore))
in (let _102_311 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in (let _102_313 = (let _205_174 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _205_174 Prims.ignore))
in (let _102_324 = (match (stack) with
| [] -> begin
(FStar_All.failwith "Too many pops")
end
| hd::tl -> begin
(hd, tl)
end)
in (match (_102_324) with
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
in (let fail = (fun curmod dsenv_mark env_mark -> (let _102_355 = (let _205_193 = (FStar_Tc_Errors.report_all ())
in (FStar_All.pipe_right _205_193 Prims.ignore))
in (let _102_357 = (FStar_ST.op_Colon_Equals FStar_Tc_Errors.num_errs 0)
in (let _102_359 = (FStar_Util.print1 "%s\n" fail)
in (let _102_363 = (reset_mark dsenv_mark env_mark)
in (match (_102_363) with
| (dsenv, env) -> begin
(go stack curmod dsenv env)
end))))))
in (let _102_366 = (mark dsenv env)
in (match (_102_366) with
| (dsenv_mark, env_mark) -> begin
(let res = (tc_one_fragment curmod dsenv_mark env_mark text)
in (match (res) with
| Some (curmod, dsenv, env) -> begin
if ((FStar_ST.read FStar_Tc_Errors.num_errs) = 0) then begin
(let _102_373 = (FStar_Util.print1 "\n%s\n" ok)
in (let _102_377 = (commit_mark dsenv env)
in (match (_102_377) with
| (dsenv, env) -> begin
(go stack curmod dsenv env)
end)))
end else begin
(fail curmod dsenv_mark env_mark)
end
end
| _102_379 -> begin
(fail curmod dsenv_mark env_mark)
end))
end))))))
end))
in (go [] None dsenv env))))

let codegen : FStar_Absyn_Syntax.modul Prims.list  ->  FStar_Tc_Env.env  ->  Prims.unit = (fun fmods env -> if (((FStar_ST.read FStar_Options.codegen) = Some ("OCaml")) || ((FStar_ST.read FStar_Options.codegen) = Some ("FSharp"))) then begin
(let _102_384 = (let _205_198 = (FStar_Extraction_ML_Env.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_ExtractMod.extract _205_198 fmods))
in (match (_102_384) with
| (c, mllibs) -> begin
(let mllibs = (FStar_List.flatten mllibs)
in (let ext = if ((FStar_ST.read FStar_Options.codegen) = Some ("FSharp")) then begin
".fs"
end else begin
".ml"
end
in (let newDocs = (FStar_List.collect FStar_Extraction_ML_Code.doc_of_mllib mllibs)
in (FStar_List.iter (fun _102_390 -> (match (_102_390) with
| (n, d) -> begin
(let _205_201 = (FStar_Options.prependOutputDir (Prims.strcat n ext))
in (let _205_200 = (FSharp_Format.pretty 120 d)
in (FStar_Util.write_file _205_201 _205_200)))
end)) newDocs))))
end))
end else begin
()
end)

exception Found of (Prims.string)

let is_Found : Prims.exn  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Found (_) -> begin
true
end
| _ -> begin
false
end))

let ___Found____0 : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| Found (_102_392) -> begin
_102_392
end))

let find_initial_module_name : Prims.unit  ->  Prims.string Prims.option = (fun _102_393 -> (match (()) with
| () -> begin
(let _102_394 = (fill_buffer ())
in (let _102_396 = (fill_buffer ())
in (FStar_All.try_with (fun _102_399 -> (match (()) with
| () -> begin
(let _102_420 = (match ((FStar_ST.read the_interactive_state.buffer)) with
| Push (_102_411)::Code (code, _102_407)::[] -> begin
(let lines = (FStar_Util.split code "\n")
in (FStar_List.iter (fun line -> (let line = (FStar_Util.trim_string line)
in if (((FStar_String.length line) > 7) && ((FStar_Util.substring line 0 6) = "module")) then begin
(let module_name = (FStar_Util.substring line 7 ((FStar_String.length line) - 7))
in (Prims.raise (Found (module_name))))
end else begin
()
end)) lines))
end
| _102_419 -> begin
()
end)
in None)
end)) (fun _102_398 -> (match (_102_398) with
| Found (n) -> begin
Some (n)
end)))))
end))

let detect_dependencies_with_first_interactive_chunk : Prims.unit  ->  Prims.string Prims.list = (fun _102_422 -> (match (()) with
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
(let _205_215 = (let _205_214 = (FStar_Util.format2 "I found a \"module %s\" directive, but there is no %s.fst\n" module_name module_name)
in FStar_Absyn_Syntax.Err (_205_214))
in (Prims.raise _205_215))
end
| Some (filename) -> begin
(let _102_434 = (FStar_Parser_Dep.collect ((filename)::[]))
in (match (_102_434) with
| (_102_432, all_filenames) -> begin
(let _205_216 = (FStar_List.tl all_filenames)
in (FStar_List.rev _205_216))
end))
end)))
end)
end))

let go = (fun _102_435 -> (let _102_439 = (process_args ())
in (match (_102_439) with
| (res, filenames) -> begin
(match (res) with
| FStar_Getopt.Help -> begin
(let _205_218 = (FStar_Options.specs ())
in (FStar_Options.display_usage _205_218))
end
| FStar_Getopt.Die (msg) -> begin
(FStar_Util.print_string msg)
end
| FStar_Getopt.GoOn -> begin
if ((FStar_ST.read FStar_Options.dep) <> None) then begin
(let _205_219 = (FStar_Parser_Dep.collect filenames)
in (FStar_Parser_Dep.print _205_219))
end else begin
if (FStar_ST.read FStar_Options.universes) then begin
(let _102_444 = (let _205_220 = (test_universes filenames)
in (FStar_All.pipe_right _205_220 Prims.ignore))
in (report_universes_errors None))
end else begin
if (FStar_ST.read FStar_Options.interactive) then begin
(let filenames = if (FStar_ST.read FStar_Options.explicit_deps) then begin
(let _102_446 = if ((FStar_List.length filenames) = 0) then begin
(FStar_Util.print_endline "--explicit_deps was provided without a file list!")
end else begin
()
end
in filenames)
end else begin
(let _102_448 = if ((FStar_List.length filenames) > 0) then begin
(FStar_Util.print_endline "ignoring the file list (no --explicit_deps)")
end else begin
()
end
in (detect_dependencies_with_first_interactive_chunk ()))
end
in (let _102_454 = (batch_mode_tc filenames)
in (match (_102_454) with
| (fmods, dsenv, env) -> begin
(interactive_mode dsenv env)
end)))
end else begin
if ((FStar_List.length filenames) >= 1) then begin
(let _102_458 = (batch_mode_tc filenames)
in (match (_102_458) with
| (fmods, dsenv, env) -> begin
(let _102_459 = (report_errors None)
in (let _102_461 = (codegen fmods env)
in (finished_message fmods)))
end))
end else begin
(FStar_Util.print_string "No file provided\n")
end
end
end
end
end)
end)))

let main = (fun _102_463 -> (match (()) with
| () -> begin
(FStar_All.try_with (fun _102_465 -> (match (()) with
| () -> begin
(let _102_476 = (go ())
in (let _102_478 = (cleanup ())
in (FStar_All.exit 0)))
end)) (fun _102_464 -> (match (_102_464) with
| e -> begin
(let _102_468 = if (FStar_Absyn_Util.handleable e) then begin
(FStar_Absyn_Util.handle_err false () e)
end else begin
()
end
in (let _102_470 = if (FStar_ST.read FStar_Options.trace_error) then begin
(let _205_225 = (FStar_Util.message_of_exn e)
in (let _205_224 = (FStar_Util.trace_of_exn e)
in (FStar_Util.print2 "\nUnexpected error\n%s\n%s\n" _205_225 _205_224)))
end else begin
if (not ((FStar_Absyn_Util.handleable e))) then begin
(let _205_226 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1 "\nUnexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" _205_226))
end else begin
()
end
end
in (let _102_472 = (cleanup ())
in (FStar_All.exit 1))))
end)))
end))




