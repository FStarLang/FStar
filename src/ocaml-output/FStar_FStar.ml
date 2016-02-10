
open Prims
# 24 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let process_args : Prims.unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun _101_1 -> (match (()) with
| () -> begin
(let file_list = (FStar_Util.mk_ref [])
in (let res = (let _203_6 = (FStar_Options.specs ())
in (FStar_Getopt.parse_cmdline _203_6 (fun i -> (let _203_5 = (let _203_4 = (FStar_ST.read file_list)
in (FStar_List.append _203_4 ((i)::[])))
in (FStar_ST.op_Colon_Equals file_list _203_5)))))
in (let _101_8 = (match (res) with
| FStar_Getopt.GoOn -> begin
(let _203_7 = (FStar_Options.set_fstar_home ())
in (Prims.ignore _203_7))
end
| _101_7 -> begin
()
end)
in (let _203_8 = (FStar_ST.read file_list)
in (res, _203_8)))))
end))

# 32 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let cleanup : Prims.unit  ->  Prims.unit = (fun _101_10 -> (match (()) with
| () -> begin
(FStar_Util.kill_all ())
end))

# 34 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let has_prims_cache : Prims.string Prims.list  ->  Prims.bool = (fun l -> (FStar_List.mem "Prims.cache" l))

# 38 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let u_parse : FStar_Parser_ToSyntax.env_t  ->  Prims.string  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env fn -> (FStar_All.try_with (fun _101_15 -> (match (()) with
| () -> begin
(match ((FStar_Parser_ParseIt.parse (FStar_Util.Inl (fn)))) with
| FStar_Util.Inl (FStar_Util.Inl (ast)) -> begin
(FStar_Parser_ToSyntax.desugar_file env ast)
end
| FStar_Util.Inl (FStar_Util.Inr (_101_29)) -> begin
(let _101_32 = (FStar_Util.print1 "%s: Expected a module\n" fn)
in (FStar_All.exit 1))
end
| FStar_Util.Inr (msg, r) -> begin
(let _101_38 = (let _203_18 = (FStar_Absyn_Print.format_error r msg)
in (FStar_All.pipe_left FStar_Util.print_string _203_18))
in (FStar_All.exit 1))
end)
end)) (fun _101_14 -> (match (_101_14) with
| e when (((FStar_ST.read FStar_Options.trace_error) && (FStar_Syntax_Util.handleable e)) && (let _101_18 = (FStar_Syntax_Util.handle_err false () e)
in false)) -> begin
(FStar_All.failwith "Impossible")
end
| e when ((not ((FStar_ST.read FStar_Options.trace_error))) && (FStar_Syntax_Util.handleable e)) -> begin
(let _101_21 = (FStar_Syntax_Util.handle_err false () e)
in (FStar_All.exit 1))
end))))

# 59 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let u_tc_prims : Prims.unit  ->  (FStar_Syntax_Syntax.modul * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun _101_40 -> (match (()) with
| () -> begin
(let solver = if (FStar_ST.read FStar_Options.verify) then begin
FStar_SMTEncoding_Encode.solver
end else begin
FStar_SMTEncoding_Encode.dummy
end
in (let env = (FStar_TypeChecker_Env.initial_env FStar_TypeChecker_Tc.type_of solver FStar_Absyn_Const.prims_lid)
in (let _101_43 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env)
in (let p = (FStar_Options.prims ())
in (let _101_48 = (let _203_22 = (FStar_Parser_Env.empty_env ())
in (u_parse _203_22 p))
in (match (_101_48) with
| (dsenv, prims_mod) -> begin
(let _101_51 = (let _203_23 = (FStar_List.hd prims_mod)
in (FStar_TypeChecker_Tc.check_module env _203_23))
in (match (_101_51) with
| (prims_mod, env) -> begin
(prims_mod, dsenv, env)
end))
end))))))
end))

# 71 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let test_universes : Prims.string Prims.list  ->  (FStar_Parser_ToSyntax.env_t * FStar_Syntax_Syntax.modul Prims.list * FStar_TypeChecker_Env.env) = (fun filenames -> (FStar_All.try_with (fun _101_54 -> (match (()) with
| () -> begin
(let _101_67 = (u_tc_prims ())
in (match (_101_67) with
| (prims_mod, dsenv, env) -> begin
(let _101_85 = (FStar_List.fold_left (fun _101_71 fn -> (match (_101_71) with
| (dsenv, fmods, env) -> begin
(let _101_73 = (FStar_Util.print1 "Parsing file %s\n" fn)
in (let _101_77 = (u_parse dsenv fn)
in (match (_101_77) with
| (dsenv, mods) -> begin
(let _101_81 = (let _203_29 = (FStar_List.hd mods)
in (FStar_TypeChecker_Tc.check_module env _203_29))
in (match (_101_81) with
| (_101_79, env) -> begin
(dsenv, (FStar_List.append mods fmods), env)
end))
end)))
end)) (dsenv, [], env) filenames)
in (match (_101_85) with
| (dsenv, mods, env) -> begin
(let _101_86 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
in (dsenv, mods, env))
end))
end))
end)) (fun _101_53 -> (match (_101_53) with
| FStar_Syntax_Syntax.Error (msg, r) when (not ((FStar_ST.read FStar_Options.trace_error))) -> begin
(let _101_60 = (let _203_32 = (let _203_31 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "Error : %s\n%s\n" _203_31 msg))
in (FStar_Util.print_string _203_32))
in (FStar_All.exit 1))
end))))

# 89 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let tc_prims : Prims.unit  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) = (fun _101_88 -> (match (()) with
| () -> begin
(let solver = if (FStar_ST.read FStar_Options.verify) then begin
FStar_ToSMT_Encode.solver
end else begin
FStar_ToSMT_Encode.dummy
end
in (let env = (FStar_Tc_Env.initial_env solver FStar_Absyn_Const.prims_lid)
in (let _101_91 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.init env)
in (let p = (FStar_Options.prims ())
in (let _101_96 = (let _203_35 = (FStar_Parser_DesugarEnv.empty_env ())
in (FStar_Parser_Driver.parse_file _203_35 p))
in (match (_101_96) with
| (dsenv, prims_mod) -> begin
(let _101_99 = (let _203_36 = (FStar_List.hd prims_mod)
in (FStar_Tc_Tc.check_module env _203_36))
in (match (_101_99) with
| (prims_mod, env) -> begin
(prims_mod, dsenv, env)
end))
end))))))
end))

# 98 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let report_errors : Prims.int Prims.option  ->  Prims.unit = (fun nopt -> (let errs = (match (nopt) with
| None -> begin
(FStar_Tc_Errors.get_err_count ())
end
| Some (n) -> begin
n
end)
in if (errs > 0) then begin
(let _101_105 = (let _203_39 = (FStar_Util.string_of_int errs)
in (FStar_Util.print1 "Error: %s errors were reported (see above)\n" _203_39))
in (FStar_All.exit 1))
end else begin
()
end))

# 108 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let report_universes_errors : Prims.int Prims.option  ->  Prims.unit = (fun nopt -> (let errs = (match (nopt) with
| None -> begin
(FStar_TypeChecker_Errors.get_err_count ())
end
| Some (n) -> begin
n
end)
in if (errs > 0) then begin
(let _101_112 = (let _203_42 = (FStar_Util.string_of_int errs)
in (FStar_Util.print1 "Error: %s errors were reported (see above)\n" _203_42))
in (FStar_All.exit 1))
end else begin
()
end))

# 118 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let tc_one_file : FStar_Parser_DesugarEnv.env  ->  FStar_Tc_Env.env  ->  Prims.string  ->  (FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env * FStar_Absyn_Syntax.modul Prims.list) = (fun dsenv env fn -> (let _101_119 = (FStar_Parser_Driver.parse_file dsenv fn)
in (match (_101_119) with
| (dsenv, fmods) -> begin
(let _101_129 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun _101_122 m -> (match (_101_122) with
| (env, all_mods) -> begin
(let _101_126 = (FStar_Tc_Tc.check_module env m)
in (match (_101_126) with
| (ms, env) -> begin
(env, (FStar_List.append ms all_mods))
end))
end)) (env, [])))
in (match (_101_129) with
| (env, all_mods) -> begin
(dsenv, env, (FStar_List.rev all_mods))
end))
end)))

# 125 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let tc_one_fragment : FStar_Absyn_Syntax.modul Prims.option  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Tc_Env.env  ->  Prims.string  ->  (FStar_Absyn_Syntax.modul Prims.option * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) Prims.option = (fun curmod dsenv env frag -> (FStar_All.try_with (fun _101_135 -> (match (()) with
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
| Some (_101_157) -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("Interactive mode only supports a single module at the top-level")))
end)
in (let _101_162 = (FStar_Tc_Tc.tc_partial_modul env modul)
in (match (_101_162) with
| (modul, env) -> begin
Some ((Some (modul), dsenv, env))
end)))
end
| FStar_Parser_Driver.Decls (dsenv, decls) -> begin
(match (curmod) with
| None -> begin
(FStar_All.failwith "Fragment without an enclosing module")
end
| Some (modul) -> begin
(let _101_172 = (FStar_Tc_Tc.tc_more_partial_modul env modul decls)
in (match (_101_172) with
| (modul, env) -> begin
Some ((Some (modul), dsenv, env))
end))
end)
end)
end)) (fun _101_134 -> (match (_101_134) with
| FStar_Absyn_Syntax.Error (msg, r) -> begin
(let _101_141 = (FStar_Tc_Errors.add_errors env (((msg, r))::[]))
in None)
end
| FStar_Absyn_Syntax.Err (msg) -> begin
(let _101_145 = (FStar_Tc_Errors.add_errors env (((msg, FStar_Absyn_Syntax.dummyRange))::[]))
in None)
end
| e -> begin
(Prims.raise e)
end))))

# 157 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

type input_chunks =
| Push of Prims.string
| Pop of Prims.string
| Code of (Prims.string * (Prims.string * Prims.string))

# 160 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let is_Push = (fun _discr_ -> (match (_discr_) with
| Push (_) -> begin
true
end
| _ -> begin
false
end))

# 161 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let is_Pop = (fun _discr_ -> (match (_discr_) with
| Pop (_) -> begin
true
end
| _ -> begin
false
end))

# 162 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let is_Code = (fun _discr_ -> (match (_discr_) with
| Code (_) -> begin
true
end
| _ -> begin
false
end))

# 160 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let ___Push____0 : input_chunks  ->  Prims.string = (fun projectee -> (match (projectee) with
| Push (_101_175) -> begin
_101_175
end))

# 161 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let ___Pop____0 : input_chunks  ->  Prims.string = (fun projectee -> (match (projectee) with
| Pop (_101_178) -> begin
_101_178
end))

# 162 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let ___Code____0 : input_chunks  ->  (Prims.string * (Prims.string * Prims.string)) = (fun projectee -> (match (projectee) with
| Code (_101_181) -> begin
_101_181
end))

# 162 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

type stack_elt =
(FStar_Absyn_Syntax.modul Prims.option * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env)

# 167 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

type stack =
stack_elt Prims.list

# 168 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let batch_mode_tc_no_prims : FStar_Parser_DesugarEnv.env  ->  FStar_Tc_Env.env  ->  Prims.string Prims.list  ->  Prims.string Prims.list  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) = (fun dsenv env filenames admit_fsi -> (let _101_202 = (FStar_All.pipe_right filenames (FStar_List.fold_left (fun _101_189 f -> (match (_101_189) with
| (all_mods, dsenv, env) -> begin
(let _101_191 = (FStar_Absyn_Util.reset_gensym ())
in (let _101_193 = (let _203_114 = (let _203_113 = (FStar_ST.read FStar_Options.admit_fsi)
in (FStar_List.append admit_fsi _203_113))
in (FStar_ST.op_Colon_Equals FStar_Options.admit_fsi _203_114))
in (let _101_198 = (tc_one_file dsenv env f)
in (match (_101_198) with
| (dsenv, env, ms) -> begin
((FStar_List.append all_mods ms), dsenv, env)
end))))
end)) ([], dsenv, env)))
in (match (_101_202) with
| (all_mods, dsenv, env) -> begin
(let _101_203 = if ((FStar_ST.read FStar_Options.interactive) && ((FStar_Tc_Errors.get_err_count ()) = 0)) then begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
end else begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.finish ())
end
in (all_mods, dsenv, env))
end)))

# 183 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let find_deps_if_needed : Prims.string Prims.list  ->  (Prims.string Prims.list * Prims.string Prims.list) = (fun files -> if (FStar_ST.read FStar_Options.explicit_deps) then begin
(files, [])
end else begin
(let _101_209 = (FStar_Parser_Dep.collect files)
in (match (_101_209) with
| (_101_207, deps) -> begin
(let deps = (FStar_List.rev deps)
in (let deps = if ((let _203_117 = (FStar_List.hd deps)
in (FStar_Util.basename _203_117)) = "prims.fst") then begin
(FStar_List.tl deps)
end else begin
(FStar_All.failwith "dependency analysis did not find prims.fst?!")
end
in (let admit_fsi = (FStar_ST.alloc [])
in (let _101_215 = (FStar_List.iter (fun d -> (let d = (FStar_Util.basename d)
in if ((FStar_Util.get_file_extension d) = "fsti") then begin
(let _203_121 = (let _203_120 = (FStar_Util.substring d 0 ((FStar_String.length d) - 5))
in (let _203_119 = (FStar_ST.read admit_fsi)
in (_203_120)::_203_119))
in (FStar_ST.op_Colon_Equals admit_fsi _203_121))
end else begin
if ((FStar_Util.get_file_extension d) = "fsi") then begin
(let _203_124 = (let _203_123 = (FStar_Util.substring d 0 ((FStar_String.length d) - 4))
in (let _203_122 = (FStar_ST.read admit_fsi)
in (_203_123)::_203_122))
in (FStar_ST.op_Colon_Equals admit_fsi _203_124))
end else begin
()
end
end)) deps)
in (let _203_125 = (FStar_ST.read admit_fsi)
in (deps, _203_125))))))
end))
end)

# 206 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let batch_mode_tc : Prims.string Prims.list  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) = (fun filenames -> (let _101_221 = (tc_prims ())
in (match (_101_221) with
| (prims_mod, dsenv, env) -> begin
(let _101_224 = (find_deps_if_needed filenames)
in (match (_101_224) with
| (filenames, admit_fsi) -> begin
(let _101_228 = (batch_mode_tc_no_prims dsenv env filenames admit_fsi)
in (match (_101_228) with
| (all_mods, dsenv, env) -> begin
((FStar_List.append prims_mod all_mods), dsenv, env)
end))
end))
end)))

# 213 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

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
in (let _101_233 = (FStar_All.pipe_right fmods (FStar_List.iter (fun m -> (let tag = if m.FStar_Absyn_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end
in if (FStar_Options.should_print_message m.FStar_Absyn_Syntax.name.FStar_Ident.str) then begin
(let _203_131 = (FStar_Util.format3 "%s %s: %s\n" msg tag (FStar_Absyn_Syntax.text_of_lid m.FStar_Absyn_Syntax.name))
in (FStar_Util.print_string _203_131))
end else begin
()
end))))
in (let _203_133 = (let _203_132 = (FStar_Util.colorize_bold "All verification conditions discharged successfully")
in (FStar_Util.format1 "%s\n" _203_132))
in (FStar_Util.print_string _203_133))))
end else begin
()
end)

# 227 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

type interactive_state =
{chunk : FStar_Util.string_builder; stdin : FStar_Util.stream_reader Prims.option FStar_ST.ref; buffer : input_chunks Prims.list FStar_ST.ref; log : FStar_Util.file_handle Prims.option FStar_ST.ref}

# 229 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let is_Mkinteractive_state : interactive_state  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkinteractive_state"))))

# 234 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let the_interactive_state : interactive_state = (let _203_150 = (FStar_Util.new_string_builder ())
in (let _203_149 = (FStar_ST.alloc None)
in (let _203_148 = (FStar_ST.alloc [])
in (let _203_147 = (FStar_ST.alloc None)
in {chunk = _203_150; stdin = _203_149; buffer = _203_148; log = _203_147}))))

# 241 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let rec read_chunk : Prims.unit  ->  input_chunks = (fun _101_240 -> (match (()) with
| () -> begin
(let s = the_interactive_state
in (let log = if ((FStar_ST.read FStar_Options.debug) <> []) then begin
(let transcript = (match ((FStar_ST.read s.log)) with
| Some (transcript) -> begin
transcript
end
| None -> begin
(let transcript = (FStar_Util.open_file_for_writing "transcript")
in (let _101_246 = (FStar_ST.op_Colon_Equals s.log (Some (transcript)))
in transcript))
end)
in (fun line -> (let _101_250 = (FStar_Util.append_to_file transcript line)
in (FStar_Util.flush_file transcript))))
end else begin
(fun _101_252 -> ())
end
in (let stdin = (match ((FStar_ST.read s.stdin)) with
| Some (i) -> begin
i
end
| None -> begin
(let i = (FStar_Util.open_stdin ())
in (let _101_259 = (FStar_ST.op_Colon_Equals s.stdin (Some (i)))
in i))
end)
in (let line = (match ((FStar_Util.read_line stdin)) with
| None -> begin
(FStar_All.exit 0)
end
| Some (l) -> begin
l
end)
in (let _101_266 = (log line)
in (let l = (FStar_Util.trim_string line)
in if (FStar_Util.starts_with l "#end") then begin
(let responses = (match ((FStar_Util.split l " ")) with
| _101_272::ok::fail::[] -> begin
(ok, fail)
end
| _101_275 -> begin
("ok", "fail")
end)
in (let str = (FStar_Util.string_of_string_builder s.chunk)
in (let _101_278 = (FStar_Util.clear_string_builder s.chunk)
in Code ((str, responses)))))
end else begin
if (FStar_Util.starts_with l "#pop") then begin
(let _101_280 = (FStar_Util.clear_string_builder s.chunk)
in Pop (l))
end else begin
if (FStar_Util.starts_with l "#push") then begin
(let _101_282 = (FStar_Util.clear_string_builder s.chunk)
in Push (l))
end else begin
if (l = "#finish") then begin
(FStar_All.exit 0)
end else begin
(let _101_284 = (FStar_Util.string_builder_append s.chunk line)
in (let _101_286 = (FStar_Util.string_builder_append s.chunk "\n")
in (read_chunk ())))
end
end
end
end))))))
end))

# 294 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let shift_chunk : Prims.unit  ->  input_chunks = (fun _101_288 -> (match (()) with
| () -> begin
(let s = the_interactive_state
in (match ((FStar_ST.read s.buffer)) with
| [] -> begin
(read_chunk ())
end
| chunk::chunks -> begin
(let _101_294 = (FStar_ST.op_Colon_Equals s.buffer chunks)
in chunk)
end))
end))

# 303 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let fill_buffer : Prims.unit  ->  Prims.unit = (fun _101_296 -> (match (()) with
| () -> begin
(let s = the_interactive_state
in (let _203_165 = (let _203_164 = (FStar_ST.read s.buffer)
in (let _203_163 = (let _203_162 = (read_chunk ())
in (_203_162)::[])
in (FStar_List.append _203_164 _203_163)))
in (FStar_ST.op_Colon_Equals s.buffer _203_165)))
end))

# 307 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let interactive_mode = (fun dsenv env -> (let _101_300 = if (let _203_168 = (FStar_ST.read FStar_Options.codegen)
in (FStar_Option.isSome _203_168)) then begin
(FStar_Util.print_string "Warning: Code-generation is not supported in interactive mode, ignoring the codegen flag")
end else begin
()
end
in (let rec go = (fun stack curmod dsenv env -> (match ((shift_chunk ())) with
| Pop (msg) -> begin
(let _101_309 = (let _203_177 = (FStar_Parser_DesugarEnv.pop dsenv)
in (FStar_All.pipe_right _203_177 Prims.ignore))
in (let _101_311 = (let _203_178 = (FStar_Tc_Env.pop env msg)
in (FStar_All.pipe_right _203_178 Prims.ignore))
in (let _101_313 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in (let _101_315 = (let _203_179 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _203_179 Prims.ignore))
in (let _101_326 = (match (stack) with
| [] -> begin
(FStar_All.failwith "Too many pops")
end
| hd::tl -> begin
(hd, tl)
end)
in (match (_101_326) with
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
in (let fail = (fun curmod dsenv_mark env_mark -> (let _101_357 = (let _203_198 = (FStar_Tc_Errors.report_all ())
in (FStar_All.pipe_right _203_198 Prims.ignore))
in (let _101_359 = (FStar_ST.op_Colon_Equals FStar_Tc_Errors.num_errs 0)
in (let _101_361 = (FStar_Util.print1 "%s\n" fail)
in (let _101_365 = (reset_mark dsenv_mark env_mark)
in (match (_101_365) with
| (dsenv, env) -> begin
(go stack curmod dsenv env)
end))))))
in (let _101_368 = (mark dsenv env)
in (match (_101_368) with
| (dsenv_mark, env_mark) -> begin
(let res = (tc_one_fragment curmod dsenv_mark env_mark text)
in (match (res) with
| Some (curmod, dsenv, env) -> begin
if ((FStar_ST.read FStar_Tc_Errors.num_errs) = 0) then begin
(let _101_375 = (FStar_Util.print1 "\n%s\n" ok)
in (let _101_379 = (commit_mark dsenv env)
in (match (_101_379) with
| (dsenv, env) -> begin
(go stack curmod dsenv env)
end)))
end else begin
(fail curmod dsenv_mark env_mark)
end
end
| _101_381 -> begin
(fail curmod dsenv_mark env_mark)
end))
end))))))
end))
in (go [] None dsenv env))))

# 372 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let codegen : FStar_Absyn_Syntax.modul Prims.list  ->  FStar_Tc_Env.env  ->  Prims.unit = (fun fmods env -> if (((FStar_ST.read FStar_Options.codegen) = Some ("OCaml")) || ((FStar_ST.read FStar_Options.codegen) = Some ("FSharp"))) then begin
(let _101_386 = (let _203_203 = (FStar_Extraction_ML_Env.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_ExtractMod.extract _203_203 fmods))
in (match (_101_386) with
| (c, mllibs) -> begin
(let mllibs = (FStar_List.flatten mllibs)
in (let ext = if ((FStar_ST.read FStar_Options.codegen) = Some ("FSharp")) then begin
".fs"
end else begin
".ml"
end
in (let newDocs = (FStar_List.collect FStar_Extraction_ML_Code.doc_of_mllib mllibs)
in (FStar_List.iter (fun _101_392 -> (match (_101_392) with
| (n, d) -> begin
(let _203_205 = (FStar_Options.prependOutputDir (Prims.strcat n ext))
in (FStar_Util.write_file _203_205 (FSharp_Format.pretty 120 d)))
end)) newDocs))))
end))
end else begin
()
end)

# 387 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

exception Found of (Prims.string)

# 387 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let is_Found = (fun _discr_ -> (match (_discr_) with
| Found (_) -> begin
true
end
| _ -> begin
false
end))

# 387 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let ___Found____0 : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| Found (_101_394) -> begin
_101_394
end))

# 387 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let find_initial_module_name : Prims.unit  ->  Prims.string Prims.option = (fun _101_395 -> (match (()) with
| () -> begin
(let _101_396 = (fill_buffer ())
in (let _101_398 = (fill_buffer ())
in (FStar_All.try_with (fun _101_401 -> (match (()) with
| () -> begin
(let _101_422 = (match ((FStar_ST.read the_interactive_state.buffer)) with
| Push (_101_413)::Code (code, _101_409)::[] -> begin
(let lines = (FStar_Util.split code "\n")
in (FStar_List.iter (fun line -> (let line = (FStar_Util.trim_string line)
in if (((FStar_String.length line) > 7) && ((FStar_Util.substring line 0 6) = "module")) then begin
(let module_name = (FStar_Util.substring line 7 ((FStar_String.length line) - 7))
in (Prims.raise (Found (module_name))))
end else begin
()
end)) lines))
end
| _101_421 -> begin
()
end)
in None)
end)) (fun _101_400 -> (match (_101_400) with
| Found (n) -> begin
Some (n)
end)))))
end))

# 405 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let detect_dependencies_with_first_interactive_chunk : Prims.unit  ->  Prims.string Prims.list = (fun _101_424 -> (match (()) with
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
(let _203_219 = (let _203_218 = (FStar_Util.format2 "I found a \"module %s\" directive, but there is no %s.fst\n" module_name module_name)
in FStar_Absyn_Syntax.Err (_203_218))
in (Prims.raise _203_219))
end
| Some (filename) -> begin
(let _101_436 = (FStar_Parser_Dep.collect ((filename)::[]))
in (match (_101_436) with
| (_101_434, all_filenames) -> begin
(let _203_220 = (FStar_List.tl all_filenames)
in (FStar_List.rev _203_220))
end))
end)))
end)
end))

# 420 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let go = (fun _101_437 -> (let _101_441 = (process_args ())
in (match (_101_441) with
| (res, filenames) -> begin
(match (res) with
| FStar_Getopt.Help -> begin
(let _203_222 = (FStar_Options.specs ())
in (FStar_Options.display_usage _203_222))
end
| FStar_Getopt.Die (msg) -> begin
(FStar_Util.print_string msg)
end
| FStar_Getopt.GoOn -> begin
if ((FStar_ST.read FStar_Options.dep) <> None) then begin
(let _203_223 = (FStar_Parser_Dep.collect filenames)
in (FStar_Parser_Dep.print _203_223))
end else begin
if (FStar_ST.read FStar_Options.universes) then begin
(let _101_446 = (let _203_224 = (test_universes filenames)
in (FStar_All.pipe_right _203_224 Prims.ignore))
in (report_universes_errors None))
end else begin
if (FStar_ST.read FStar_Options.interactive) then begin
(let filenames = if (FStar_ST.read FStar_Options.explicit_deps) then begin
(let _101_448 = if ((FStar_List.length filenames) = 0) then begin
(FStar_Util.print_endline "--explicit_deps was provided without a file list!")
end else begin
()
end
in filenames)
end else begin
(let _101_450 = if ((FStar_List.length filenames) > 0) then begin
(FStar_Util.print_endline "ignoring the file list (no --explicit_deps)")
end else begin
()
end
in (detect_dependencies_with_first_interactive_chunk ()))
end
in (let _101_456 = (batch_mode_tc filenames)
in (match (_101_456) with
| (fmods, dsenv, env) -> begin
(interactive_mode dsenv env)
end)))
end else begin
if ((FStar_List.length filenames) >= 1) then begin
(let _101_460 = (batch_mode_tc filenames)
in (match (_101_460) with
| (fmods, dsenv, env) -> begin
(let _101_461 = (report_errors None)
in (let _101_463 = (codegen fmods env)
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

# 458 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\fstar\\fstar.fs"

let main = (fun _101_465 -> (match (()) with
| () -> begin
(FStar_All.try_with (fun _101_467 -> (match (()) with
| () -> begin
(let _101_478 = (go ())
in (let _101_480 = (cleanup ())
in (FStar_All.exit 0)))
end)) (fun _101_466 -> (match (_101_466) with
| e -> begin
(let _101_470 = if (FStar_Absyn_Util.handleable e) then begin
(FStar_Absyn_Util.handle_err false () e)
end else begin
()
end
in (let _101_472 = if (FStar_ST.read FStar_Options.trace_error) then begin
(let _203_229 = (FStar_Util.message_of_exn e)
in (let _203_228 = (FStar_Util.trace_of_exn e)
in (FStar_Util.print2 "\nUnexpected error\n%s\n%s\n" _203_229 _203_228)))
end else begin
if (not ((FStar_Absyn_Util.handleable e))) then begin
(let _203_230 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1 "\nUnexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" _203_230))
end else begin
()
end
end
in (let _101_474 = (cleanup ())
in (FStar_All.exit 1))))
end)))
end))




