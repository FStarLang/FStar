
open Prims
# 26 "FStar.FStar.fst"
let process_args : Prims.unit  ->  (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) = (fun _78_1 -> (match (()) with
| () -> begin
(
# 27 "FStar.FStar.fst"
let file_list = (FStar_Util.mk_ref [])
in (
# 28 "FStar.FStar.fst"
let res = (let _157_6 = (FStar_Options.specs ())
in (FStar_Getopt.parse_cmdline _157_6 (fun i -> (let _157_5 = (let _157_4 = (FStar_ST.read file_list)
in (FStar_List.append _157_4 ((i)::[])))
in (FStar_ST.op_Colon_Equals file_list _157_5)))))
in (
# 29 "FStar.FStar.fst"
let _78_8 = (match (res) with
| FStar_Getopt.GoOn -> begin
(let _157_7 = (FStar_Options.set_fstar_home ())
in (Prims.ignore _157_7))
end
| _78_7 -> begin
()
end)
in (let _157_8 = (FStar_ST.read file_list)
in (res, _157_8)))))
end))

# 34 "FStar.FStar.fst"
let cleanup : Prims.unit  ->  Prims.unit = (fun _78_10 -> (match (()) with
| () -> begin
(FStar_Util.kill_all ())
end))

# 36 "FStar.FStar.fst"
let has_prims_cache : Prims.string Prims.list  ->  Prims.bool = (fun l -> (FStar_List.mem "Prims.cache" l))

# 39 "FStar.FStar.fst"
let u_parse : FStar_Parser_Env.env  ->  Prims.string  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env fn -> (FStar_All.try_with (fun _78_15 -> (match (()) with
| () -> begin
(match ((FStar_Parser_ParseIt.parse (FStar_Util.Inl (fn)))) with
| FStar_Util.Inl (FStar_Util.Inl (ast)) -> begin
(FStar_Parser_ToSyntax.desugar_file env ast)
end
| FStar_Util.Inl (FStar_Util.Inr (_78_29)) -> begin
(
# 46 "FStar.FStar.fst"
let _78_32 = (FStar_Util.print1_error "%s expected a module\n" fn)
in (FStar_All.exit 1))
end
| FStar_Util.Inr (msg, r) -> begin
(
# 50 "FStar.FStar.fst"
let _78_38 = (let _157_18 = (FStar_Absyn_Print.format_error r msg)
in (FStar_All.pipe_left FStar_Util.print_string _157_18))
in (FStar_All.exit 1))
end)
end)) (fun _78_14 -> (match (_78_14) with
| e when (((FStar_ST.read FStar_Options.trace_error) && (FStar_Syntax_Util.handleable e)) && (
# 54 "FStar.FStar.fst"
let _78_18 = (FStar_Syntax_Util.handle_err false () e)
in false)) -> begin
(FStar_All.failwith "Impossible")
end
| e when ((not ((FStar_ST.read FStar_Options.trace_error))) && (FStar_Syntax_Util.handleable e)) -> begin
(
# 58 "FStar.FStar.fst"
let _78_21 = (FStar_Syntax_Util.handle_err false () e)
in (FStar_All.exit 1))
end))))

# 61 "FStar.FStar.fst"
let u_tc_prims : Prims.unit  ->  (FStar_Syntax_Syntax.modul * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun _78_40 -> (match (()) with
| () -> begin
(
# 62 "FStar.FStar.fst"
let solver = if (FStar_ST.read FStar_Options.verify) then begin
FStar_SMTEncoding_Encode.solver
end else begin
FStar_SMTEncoding_Encode.dummy
end
in (
# 63 "FStar.FStar.fst"
let env = (FStar_TypeChecker_Env.initial_env FStar_TypeChecker_Tc.type_of solver FStar_Absyn_Const.prims_lid)
in (
# 67 "FStar.FStar.fst"
let _78_43 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env)
in (
# 68 "FStar.FStar.fst"
let p = (FStar_Options.prims ())
in (
# 69 "FStar.FStar.fst"
let _78_48 = (let _157_22 = (FStar_Parser_Env.empty_env ())
in (u_parse _157_22 p))
in (match (_78_48) with
| (dsenv, prims_mod) -> begin
(
# 70 "FStar.FStar.fst"
let _78_51 = (let _157_23 = (FStar_List.hd prims_mod)
in (FStar_TypeChecker_Tc.check_module env _157_23))
in (match (_78_51) with
| (prims_mod, env) -> begin
(prims_mod, dsenv, env)
end))
end))))))
end))

# 74 "FStar.FStar.fst"
let test_universes : Prims.string Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list * FStar_TypeChecker_Env.env) = (fun filenames -> (FStar_All.try_with (fun _78_54 -> (match (()) with
| () -> begin
(
# 76 "FStar.FStar.fst"
let _78_67 = (u_tc_prims ())
in (match (_78_67) with
| (prims_mod, dsenv, env) -> begin
(
# 77 "FStar.FStar.fst"
let _78_85 = (FStar_List.fold_left (fun _78_71 fn -> (match (_78_71) with
| (dsenv, fmods, env) -> begin
(
# 78 "FStar.FStar.fst"
let _78_73 = (FStar_Util.print1 "Parsing file %s\n" fn)
in (
# 79 "FStar.FStar.fst"
let _78_77 = (u_parse dsenv fn)
in (match (_78_77) with
| (dsenv, mods) -> begin
(
# 80 "FStar.FStar.fst"
let _78_81 = (let _157_29 = (FStar_List.hd mods)
in (FStar_TypeChecker_Tc.check_module env _157_29))
in (match (_78_81) with
| (_78_79, env) -> begin
(dsenv, (FStar_List.append mods fmods), env)
end))
end)))
end)) (dsenv, [], env) filenames)
in (match (_78_85) with
| (dsenv, mods, env) -> begin
(
# 82 "FStar.FStar.fst"
let _78_86 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
in (dsenv, mods, env))
end))
end))
end)) (fun _78_53 -> (match (_78_53) with
| FStar_Syntax_Syntax.Error (msg, r) when (not ((FStar_ST.read FStar_Options.trace_error))) -> begin
(
# 86 "FStar.FStar.fst"
let _78_60 = (let _157_32 = (let _157_31 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s\n%s\n" _157_31 msg))
in (FStar_Util.print_error _157_32))
in (FStar_All.exit 1))
end))))

# 90 "FStar.FStar.fst"
let tc_prims : Prims.unit  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) = (fun _78_88 -> (match (()) with
| () -> begin
(
# 91 "FStar.FStar.fst"
let solver = if (FStar_ST.read FStar_Options.verify) then begin
FStar_ToSMT_Encode.solver
end else begin
FStar_ToSMT_Encode.dummy
end
in (
# 92 "FStar.FStar.fst"
let env = (FStar_Tc_Env.initial_env solver FStar_Absyn_Const.prims_lid)
in (
# 93 "FStar.FStar.fst"
let _78_91 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.init env)
in (
# 95 "FStar.FStar.fst"
let p = (FStar_Options.prims ())
in (
# 96 "FStar.FStar.fst"
let _78_96 = (let _157_35 = (FStar_Parser_DesugarEnv.empty_env ())
in (FStar_Parser_Driver.parse_file _157_35 p))
in (match (_78_96) with
| (dsenv, prims_mod) -> begin
(
# 97 "FStar.FStar.fst"
let _78_99 = (let _157_36 = (FStar_List.hd prims_mod)
in (FStar_Tc_Tc.check_module env _157_36))
in (match (_78_99) with
| (prims_mod, env) -> begin
(prims_mod, dsenv, env)
end))
end))))))
end))

# 100 "FStar.FStar.fst"
let report_errors : Prims.int Prims.option  ->  Prims.unit = (fun nopt -> (
# 101 "FStar.FStar.fst"
let errs = (match (nopt) with
| None -> begin
(FStar_Tc_Errors.get_err_count ())
end
| Some (n) -> begin
n
end)
in if (errs > 0) then begin
(
# 106 "FStar.FStar.fst"
let _78_105 = (let _157_39 = (FStar_Util.string_of_int errs)
in (FStar_Util.print1_error "%s errors were reported (see above)\n" _157_39))
in (FStar_All.exit 1))
end else begin
()
end))

# 110 "FStar.FStar.fst"
let report_universes_errors : Prims.int Prims.option  ->  Prims.unit = (fun nopt -> (
# 111 "FStar.FStar.fst"
let errs = (match (nopt) with
| None -> begin
(FStar_TypeChecker_Errors.get_err_count ())
end
| Some (n) -> begin
n
end)
in if (errs > 0) then begin
(
# 116 "FStar.FStar.fst"
let _78_112 = (let _157_42 = (FStar_Util.string_of_int errs)
in (FStar_Util.print1_error "%s errors were reported (see above)\n" _157_42))
in (FStar_All.exit 1))
end else begin
()
end))

# 120 "FStar.FStar.fst"
let tc_one_file : FStar_Parser_DesugarEnv.env  ->  FStar_Tc_Env.env  ->  Prims.string  ->  (FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env * FStar_Absyn_Syntax.modul Prims.list) = (fun dsenv env fn -> (
# 121 "FStar.FStar.fst"
let _78_119 = (FStar_Parser_Driver.parse_file dsenv fn)
in (match (_78_119) with
| (dsenv, fmods) -> begin
(
# 122 "FStar.FStar.fst"
let _78_129 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun _78_122 m -> (match (_78_122) with
| (env, all_mods) -> begin
(
# 123 "FStar.FStar.fst"
let _78_126 = (FStar_Tc_Tc.check_module env m)
in (match (_78_126) with
| (ms, env) -> begin
(env, (FStar_List.append ms all_mods))
end))
end)) (env, [])))
in (match (_78_129) with
| (env, all_mods) -> begin
(dsenv, env, (FStar_List.rev all_mods))
end))
end)))

# 127 "FStar.FStar.fst"
let tc_one_fragment : FStar_Absyn_Syntax.modul Prims.option  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Tc_Env.env  ->  Prims.string  ->  (FStar_Absyn_Syntax.modul Prims.option * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) Prims.option = (fun curmod dsenv env frag -> (FStar_All.try_with (fun _78_135 -> (match (()) with
| () -> begin
(match ((FStar_Parser_Driver.parse_fragment curmod dsenv frag)) with
| FStar_Parser_Driver.Empty -> begin
Some ((curmod, dsenv, env))
end
| FStar_Parser_Driver.Modul (dsenv, modul) -> begin
(
# 134 "FStar.FStar.fst"
let env = (match (curmod) with
| None -> begin
env
end
| Some (_78_157) -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("Interactive mode only supports a single module at the top-level")))
end)
in (
# 138 "FStar.FStar.fst"
let _78_162 = (FStar_Tc_Tc.tc_partial_modul env modul)
in (match (_78_162) with
| (modul, env) -> begin
Some ((Some (modul), dsenv, env))
end)))
end
| FStar_Parser_Driver.Decls (dsenv, decls) -> begin
(match (curmod) with
| None -> begin
(
# 143 "FStar.FStar.fst"
let _78_168 = (FStar_Util.print_error "fragment without an enclosing module")
in (FStar_All.exit 1))
end
| Some (modul) -> begin
(
# 145 "FStar.FStar.fst"
let _78_174 = (FStar_Tc_Tc.tc_more_partial_modul env modul decls)
in (match (_78_174) with
| (modul, env) -> begin
Some ((Some (modul), dsenv, env))
end))
end)
end)
end)) (fun _78_134 -> (match (_78_134) with
| FStar_Absyn_Syntax.Error (msg, r) -> begin
(
# 150 "FStar.FStar.fst"
let _78_141 = (FStar_Tc_Errors.add_errors env (((msg, r))::[]))
in None)
end
| FStar_Absyn_Syntax.Err (msg) -> begin
(
# 154 "FStar.FStar.fst"
let _78_145 = (FStar_Tc_Errors.add_errors env (((msg, FStar_Absyn_Syntax.dummyRange))::[]))
in None)
end
| e -> begin
(Prims.raise e)
end))))

# 159 "FStar.FStar.fst"
type input_chunks =
| Push of Prims.string
| Pop of Prims.string
| Code of (Prims.string * (Prims.string * Prims.string))

# 160 "FStar.FStar.fst"
let is_Push = (fun _discr_ -> (match (_discr_) with
| Push (_) -> begin
true
end
| _ -> begin
false
end))

# 161 "FStar.FStar.fst"
let is_Pop = (fun _discr_ -> (match (_discr_) with
| Pop (_) -> begin
true
end
| _ -> begin
false
end))

# 162 "FStar.FStar.fst"
let is_Code = (fun _discr_ -> (match (_discr_) with
| Code (_) -> begin
true
end
| _ -> begin
false
end))

# 160 "FStar.FStar.fst"
let ___Push____0 : input_chunks  ->  Prims.string = (fun projectee -> (match (projectee) with
| Push (_78_177) -> begin
_78_177
end))

# 161 "FStar.FStar.fst"
let ___Pop____0 : input_chunks  ->  Prims.string = (fun projectee -> (match (projectee) with
| Pop (_78_180) -> begin
_78_180
end))

# 162 "FStar.FStar.fst"
let ___Code____0 : input_chunks  ->  (Prims.string * (Prims.string * Prims.string)) = (fun projectee -> (match (projectee) with
| Code (_78_183) -> begin
_78_183
end))

# 164 "FStar.FStar.fst"
type stack_elt =
(FStar_Absyn_Syntax.modul Prims.option * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env)

# 168 "FStar.FStar.fst"
type stack =
stack_elt Prims.list

# 171 "FStar.FStar.fst"
let batch_mode_tc_no_prims = (fun dsenv env filenames admit_fsi -> (
# 172 "FStar.FStar.fst"
let _78_202 = (FStar_All.pipe_right filenames (FStar_List.fold_left (fun _78_191 f -> (match (_78_191) with
| (all_mods, dsenv, env) -> begin
(
# 173 "FStar.FStar.fst"
let _78_193 = (FStar_Absyn_Util.reset_gensym ())
in (
# 174 "FStar.FStar.fst"
let _78_198 = (tc_one_file dsenv env f)
in (match (_78_198) with
| (dsenv, env, ms) -> begin
((FStar_List.append all_mods ms), dsenv, env)
end)))
end)) ([], dsenv, env)))
in (match (_78_202) with
| (all_mods, dsenv, env) -> begin
(
# 178 "FStar.FStar.fst"
let _78_203 = if ((FStar_ST.read FStar_Options.interactive) && ((FStar_Tc_Errors.get_err_count ()) = 0)) then begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
end else begin
(env.FStar_Tc_Env.solver.FStar_Tc_Env.finish ())
end
in (all_mods, dsenv, env))
end)))

# 183 "FStar.FStar.fst"
let find_deps_if_needed : Prims.string Prims.list  ->  (Prims.string Prims.list * Prims.string Prims.list) = (fun files -> if (FStar_ST.read FStar_Options.explicit_deps) then begin
(files, [])
end else begin
(
# 187 "FStar.FStar.fst"
let _78_209 = (FStar_Parser_Dep.collect files)
in (match (_78_209) with
| (_78_207, deps) -> begin
(
# 188 "FStar.FStar.fst"
let deps = (FStar_List.rev deps)
in (
# 189 "FStar.FStar.fst"
let deps = if ((let _157_111 = (FStar_List.hd deps)
in (FStar_Util.basename _157_111)) = "prims.fst") then begin
(FStar_List.tl deps)
end else begin
(
# 193 "FStar.FStar.fst"
let _78_211 = (FStar_Util.print_error "dependency analysis did not find prims.fst?!")
in (FStar_All.exit 1))
end
in (
# 197 "FStar.FStar.fst"
let admit_fsi = (FStar_ST.alloc [])
in (
# 198 "FStar.FStar.fst"
let _78_217 = (FStar_List.iter (fun d -> (
# 199 "FStar.FStar.fst"
let d = (FStar_Util.basename d)
in if ((FStar_Util.get_file_extension d) = "fsti") then begin
(let _157_115 = (let _157_114 = (FStar_Util.substring d 0 ((FStar_String.length d) - 5))
in (let _157_113 = (FStar_ST.read admit_fsi)
in (_157_114)::_157_113))
in (FStar_ST.op_Colon_Equals admit_fsi _157_115))
end else begin
if ((FStar_Util.get_file_extension d) = "fsi") then begin
(let _157_118 = (let _157_117 = (FStar_Util.substring d 0 ((FStar_String.length d) - 4))
in (let _157_116 = (FStar_ST.read admit_fsi)
in (_157_117)::_157_116))
in (FStar_ST.op_Colon_Equals admit_fsi _157_118))
end else begin
()
end
end)) deps)
in (let _157_119 = (FStar_ST.read admit_fsi)
in (deps, _157_119))))))
end))
end)

# 208 "FStar.FStar.fst"
let batch_mode_tc : Prims.string Prims.list  ->  (FStar_Absyn_Syntax.modul Prims.list * FStar_Parser_DesugarEnv.env * FStar_Tc_Env.env) = (fun filenames -> (
# 209 "FStar.FStar.fst"
let _78_223 = (tc_prims ())
in (match (_78_223) with
| (prims_mod, dsenv, env) -> begin
(
# 211 "FStar.FStar.fst"
let _78_226 = (find_deps_if_needed filenames)
in (match (_78_226) with
| (filenames, admit_fsi) -> begin
(
# 212 "FStar.FStar.fst"
let _78_230 = (batch_mode_tc_no_prims dsenv env filenames admit_fsi)
in (match (_78_230) with
| (all_mods, dsenv, env) -> begin
((FStar_List.append prims_mod all_mods), dsenv, env)
end))
end))
end)))

# 215 "FStar.FStar.fst"
let finished_message : FStar_Absyn_Syntax.modul Prims.list  ->  Prims.unit = (fun fmods -> if (not ((FStar_ST.read FStar_Options.silent))) then begin
(
# 218 "FStar.FStar.fst"
let msg = if (FStar_ST.read FStar_Options.verify) then begin
"Verifying"
end else begin
if (FStar_ST.read FStar_Options.pretype) then begin
"Lax type-checked"
end else begin
"Parsed and desugared"
end
end
in (
# 222 "FStar.FStar.fst"
let _78_235 = (FStar_All.pipe_right fmods (FStar_List.iter (fun m -> (
# 223 "FStar.FStar.fst"
let tag = if m.FStar_Absyn_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end
in if (FStar_Options.should_print_message m.FStar_Absyn_Syntax.name.FStar_Ident.str) then begin
(let _157_126 = (let _157_125 = (FStar_Absyn_Syntax.text_of_lid m.FStar_Absyn_Syntax.name)
in (FStar_Util.format3 "%s %s: %s\n" msg tag _157_125))
in (FStar_Util.print_string _157_126))
end else begin
()
end))))
in (let _157_128 = (let _157_127 = (FStar_Util.colorize_bold "All verification conditions discharged successfully")
in (FStar_Util.format1 "%s\n" _157_127))
in (FStar_Util.print_string _157_128))))
end else begin
()
end)

# 229 "FStar.FStar.fst"
type interactive_state =
{chunk : FStar_Util.string_builder; stdin : FStar_Util.stream_reader Prims.option FStar_ST.ref; buffer : input_chunks Prims.list FStar_ST.ref; log : FStar_Util.file_handle Prims.option FStar_ST.ref}

# 229 "FStar.FStar.fst"
let is_Mkinteractive_state : interactive_state  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkinteractive_state"))))

# 236 "FStar.FStar.fst"
let the_interactive_state : interactive_state = (let _157_145 = (FStar_Util.new_string_builder ())
in (let _157_144 = (FStar_ST.alloc None)
in (let _157_143 = (FStar_ST.alloc [])
in (let _157_142 = (FStar_ST.alloc None)
in {chunk = _157_145; stdin = _157_144; buffer = _157_143; log = _157_142}))))

# 243 "FStar.FStar.fst"
let rec read_chunk : Prims.unit  ->  input_chunks = (fun _78_242 -> (match (()) with
| () -> begin
(
# 244 "FStar.FStar.fst"
let s = the_interactive_state
in (
# 245 "FStar.FStar.fst"
let log = if ((FStar_ST.read FStar_Options.debug) <> []) then begin
(
# 247 "FStar.FStar.fst"
let transcript = (match ((FStar_ST.read s.log)) with
| Some (transcript) -> begin
transcript
end
| None -> begin
(
# 251 "FStar.FStar.fst"
let transcript = (FStar_Util.open_file_for_writing "transcript")
in (
# 252 "FStar.FStar.fst"
let _78_248 = (FStar_ST.op_Colon_Equals s.log (Some (transcript)))
in transcript))
end)
in (fun line -> (
# 256 "FStar.FStar.fst"
let _78_252 = (FStar_Util.append_to_file transcript line)
in (FStar_Util.flush_file transcript))))
end else begin
(fun _78_254 -> ())
end
in (
# 263 "FStar.FStar.fst"
let stdin = (match ((FStar_ST.read s.stdin)) with
| Some (i) -> begin
i
end
| None -> begin
(
# 268 "FStar.FStar.fst"
let i = (FStar_Util.open_stdin ())
in (
# 269 "FStar.FStar.fst"
let _78_261 = (FStar_ST.op_Colon_Equals s.stdin (Some (i)))
in i))
end)
in (
# 272 "FStar.FStar.fst"
let line = (match ((FStar_Util.read_line stdin)) with
| None -> begin
(FStar_All.exit 0)
end
| Some (l) -> begin
l
end)
in (
# 275 "FStar.FStar.fst"
let _78_268 = (log line)
in (
# 277 "FStar.FStar.fst"
let l = (FStar_Util.trim_string line)
in if (FStar_Util.starts_with l "#end") then begin
(
# 280 "FStar.FStar.fst"
let responses = (match ((FStar_Util.split l " ")) with
| _78_274::ok::fail::[] -> begin
(ok, fail)
end
| _78_277 -> begin
("ok", "fail")
end)
in (
# 283 "FStar.FStar.fst"
let str = (FStar_Util.string_of_string_builder s.chunk)
in (
# 284 "FStar.FStar.fst"
let _78_280 = (FStar_Util.clear_string_builder s.chunk)
in Code ((str, responses)))))
end else begin
if (FStar_Util.starts_with l "#pop") then begin
(
# 287 "FStar.FStar.fst"
let _78_282 = (FStar_Util.clear_string_builder s.chunk)
in Pop (l))
end else begin
if (FStar_Util.starts_with l "#push") then begin
(
# 289 "FStar.FStar.fst"
let _78_284 = (FStar_Util.clear_string_builder s.chunk)
in Push (l))
end else begin
if (l = "#finish") then begin
(FStar_All.exit 0)
end else begin
(
# 292 "FStar.FStar.fst"
let _78_286 = (FStar_Util.string_builder_append s.chunk line)
in (
# 293 "FStar.FStar.fst"
let _78_288 = (FStar_Util.string_builder_append s.chunk "\n")
in (read_chunk ())))
end
end
end
end))))))
end))

# 296 "FStar.FStar.fst"
let shift_chunk : Prims.unit  ->  input_chunks = (fun _78_290 -> (match (()) with
| () -> begin
(
# 297 "FStar.FStar.fst"
let s = the_interactive_state
in (match ((FStar_ST.read s.buffer)) with
| [] -> begin
(read_chunk ())
end
| chunk::chunks -> begin
(
# 302 "FStar.FStar.fst"
let _78_296 = (FStar_ST.op_Colon_Equals s.buffer chunks)
in chunk)
end))
end))

# 305 "FStar.FStar.fst"
let fill_buffer : Prims.unit  ->  Prims.unit = (fun _78_298 -> (match (()) with
| () -> begin
(
# 306 "FStar.FStar.fst"
let s = the_interactive_state
in (let _157_160 = (let _157_159 = (FStar_ST.read s.buffer)
in (let _157_158 = (let _157_157 = (read_chunk ())
in (_157_157)::[])
in (FStar_List.append _157_159 _157_158)))
in (FStar_ST.op_Colon_Equals s.buffer _157_160)))
end))

# 309 "FStar.FStar.fst"
let interactive_mode = (fun dsenv env -> (
# 310 "FStar.FStar.fst"
let _78_302 = if (let _157_163 = (FStar_ST.read FStar_Options.codegen)
in (FStar_Option.isSome _157_163)) then begin
(FStar_Util.print_warning "code-generation is not supported in interactive mode, ignoring the codegen flag")
end else begin
()
end
in (
# 313 "FStar.FStar.fst"
let rec go = (fun stack curmod dsenv env -> (match ((shift_chunk ())) with
| Pop (msg) -> begin
(
# 316 "FStar.FStar.fst"
let _78_311 = (let _157_172 = (FStar_Parser_DesugarEnv.pop dsenv)
in (FStar_All.pipe_right _157_172 Prims.ignore))
in (
# 317 "FStar.FStar.fst"
let _78_313 = (let _157_173 = (FStar_Tc_Env.pop env msg)
in (FStar_All.pipe_right _157_173 Prims.ignore))
in (
# 318 "FStar.FStar.fst"
let _78_315 = (env.FStar_Tc_Env.solver.FStar_Tc_Env.refresh ())
in (
# 319 "FStar.FStar.fst"
let _78_317 = (let _157_174 = (FStar_Options.reset_options ())
in (FStar_All.pipe_right _157_174 Prims.ignore))
in (
# 320 "FStar.FStar.fst"
let _78_330 = (match (stack) with
| [] -> begin
(
# 321 "FStar.FStar.fst"
let _78_320 = (FStar_Util.print_error "too many pops")
in (FStar_All.exit 1))
end
| hd::tl -> begin
(hd, tl)
end)
in (match (_78_330) with
| ((curmod, dsenv, env), stack) -> begin
(go stack curmod dsenv env)
end))))))
end
| Push (msg) -> begin
(
# 326 "FStar.FStar.fst"
let stack = ((curmod, dsenv, env))::stack
in (
# 327 "FStar.FStar.fst"
let dsenv = (FStar_Parser_DesugarEnv.push dsenv)
in (
# 328 "FStar.FStar.fst"
let env = (FStar_Tc_Env.push env msg)
in (go stack curmod dsenv env))))
end
| Code (text, (ok, fail)) -> begin
(
# 332 "FStar.FStar.fst"
let mark = (fun dsenv env -> (
# 333 "FStar.FStar.fst"
let dsenv = (FStar_Parser_DesugarEnv.mark dsenv)
in (
# 334 "FStar.FStar.fst"
let env = (FStar_Tc_Env.mark env)
in (dsenv, env))))
in (
# 337 "FStar.FStar.fst"
let reset_mark = (fun dsenv env -> (
# 338 "FStar.FStar.fst"
let dsenv = (FStar_Parser_DesugarEnv.reset_mark dsenv)
in (
# 339 "FStar.FStar.fst"
let env = (FStar_Tc_Env.reset_mark env)
in (dsenv, env))))
in (
# 342 "FStar.FStar.fst"
let commit_mark = (fun dsenv env -> (
# 343 "FStar.FStar.fst"
let dsenv = (FStar_Parser_DesugarEnv.commit_mark dsenv)
in (
# 344 "FStar.FStar.fst"
let env = (FStar_Tc_Env.commit_mark env)
in (dsenv, env))))
in (
# 347 "FStar.FStar.fst"
let fail = (fun curmod dsenv_mark env_mark -> (
# 348 "FStar.FStar.fst"
let _78_361 = (let _157_193 = (FStar_Tc_Errors.report_all ())
in (FStar_All.pipe_right _157_193 Prims.ignore))
in (
# 349 "FStar.FStar.fst"
let _78_363 = (FStar_ST.op_Colon_Equals FStar_Tc_Errors.num_errs 0)
in (
# 350 "FStar.FStar.fst"
let _78_365 = (FStar_Util.print1 "%s\n" fail)
in (
# 351 "FStar.FStar.fst"
let _78_369 = (reset_mark dsenv_mark env_mark)
in (match (_78_369) with
| (dsenv, env) -> begin
(go stack curmod dsenv env)
end))))))
in (
# 354 "FStar.FStar.fst"
let _78_372 = (mark dsenv env)
in (match (_78_372) with
| (dsenv_mark, env_mark) -> begin
(
# 355 "FStar.FStar.fst"
let res = (tc_one_fragment curmod dsenv_mark env_mark text)
in (match (res) with
| Some (curmod, dsenv, env) -> begin
if ((FStar_ST.read FStar_Tc_Errors.num_errs) = 0) then begin
(
# 361 "FStar.FStar.fst"
let _78_379 = (FStar_Util.print1 "\n%s\n" ok)
in (
# 362 "FStar.FStar.fst"
let _78_383 = (commit_mark dsenv env)
in (match (_78_383) with
| (dsenv, env) -> begin
(go stack curmod dsenv env)
end)))
end else begin
(fail curmod dsenv_mark env_mark)
end
end
| _78_385 -> begin
(fail curmod dsenv_mark env_mark)
end))
end))))))
end))
in (go [] None dsenv env))))

# 375 "FStar.FStar.fst"
let codegen : FStar_Absyn_Syntax.modul Prims.list  ->  FStar_Tc_Env.env  ->  Prims.unit = (fun fmods env -> if (((FStar_ST.read FStar_Options.codegen) = Some ("OCaml")) || ((FStar_ST.read FStar_Options.codegen) = Some ("FSharp"))) then begin
(
# 379 "FStar.FStar.fst"
let _78_390 = (let _157_198 = (FStar_Extraction_ML_Env.mkContext env)
in (FStar_Util.fold_map FStar_Extraction_ML_ExtractMod.extract _157_198 fmods))
in (match (_78_390) with
| (c, mllibs) -> begin
(
# 380 "FStar.FStar.fst"
let mllibs = (FStar_List.flatten mllibs)
in (
# 381 "FStar.FStar.fst"
let ext = if ((FStar_ST.read FStar_Options.codegen) = Some ("FSharp")) then begin
".fs"
end else begin
".ml"
end
in (
# 382 "FStar.FStar.fst"
let newDocs = (FStar_List.collect FStar_Extraction_ML_Code.doc_of_mllib mllibs)
in (FStar_List.iter (fun _78_396 -> (match (_78_396) with
| (n, d) -> begin
(let _157_201 = (FStar_Options.prependOutputDir (Prims.strcat n ext))
in (let _157_200 = (FStar_Format.pretty 120 d)
in (FStar_Util.write_file _157_201 _157_200)))
end)) newDocs))))
end))
end else begin
()
end)

# 387 "FStar.FStar.fst"
exception Found of (Prims.string)

# 387 "FStar.FStar.fst"
let is_Found = (fun _discr_ -> (match (_discr_) with
| Found (_) -> begin
true
end
| _ -> begin
false
end))

# 387 "FStar.FStar.fst"
let ___Found____0 : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| Found (_78_398) -> begin
_78_398
end))

# 389 "FStar.FStar.fst"
let find_initial_module_name : Prims.unit  ->  Prims.string Prims.option = (fun _78_399 -> (match (()) with
| () -> begin
(
# 390 "FStar.FStar.fst"
let _78_400 = (fill_buffer ())
in (
# 390 "FStar.FStar.fst"
let _78_402 = (fill_buffer ())
in (FStar_All.try_with (fun _78_405 -> (match (()) with
| () -> begin
(
# 391 "FStar.FStar.fst"
let _78_426 = (match ((FStar_ST.read the_interactive_state.buffer)) with
| Push (_78_417)::Code (code, _78_413)::[] -> begin
(
# 393 "FStar.FStar.fst"
let lines = (FStar_Util.split code "\n")
in (FStar_List.iter (fun line -> (
# 395 "FStar.FStar.fst"
let line = (FStar_Util.trim_string line)
in if (((FStar_String.length line) > 7) && ((FStar_Util.substring line 0 6) = "module")) then begin
(
# 397 "FStar.FStar.fst"
let module_name = (FStar_Util.substring line 7 ((FStar_String.length line) - 7))
in (Prims.raise (Found (module_name))))
end else begin
()
end)) lines))
end
| _78_425 -> begin
()
end)
in None)
end)) (fun _78_404 -> (match (_78_404) with
| Found (n) -> begin
Some (n)
end)))))
end))

# 407 "FStar.FStar.fst"
let detect_dependencies_with_first_interactive_chunk : Prims.unit  ->  Prims.string Prims.list = (fun _78_428 -> (match (()) with
| () -> begin
(match ((find_initial_module_name ())) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("No initial module directive found\n")))
end
| Some (module_name) -> begin
(
# 412 "FStar.FStar.fst"
let file_of_module_name = (FStar_Parser_Dep.build_map [])
in (
# 413 "FStar.FStar.fst"
let filename = (FStar_Util.smap_try_find file_of_module_name (FStar_String.lowercase module_name))
in (match (filename) with
| None -> begin
(let _157_215 = (let _157_214 = (FStar_Util.format2 "I found a \"module %s\" directive, but there is no %s.fst\n" module_name module_name)
in FStar_Absyn_Syntax.Err (_157_214))
in (Prims.raise _157_215))
end
| Some (filename) -> begin
(
# 419 "FStar.FStar.fst"
let _78_440 = (FStar_Parser_Dep.collect ((filename)::[]))
in (match (_78_440) with
| (_78_438, all_filenames) -> begin
(let _157_216 = (FStar_List.tl all_filenames)
in (FStar_List.rev _157_216))
end))
end)))
end)
end))

# 424 "FStar.FStar.fst"
let go = (fun _78_441 -> (
# 425 "FStar.FStar.fst"
let _78_445 = (process_args ())
in (match (_78_445) with
| (res, filenames) -> begin
(match (res) with
| FStar_Getopt.Help -> begin
(let _157_218 = (FStar_Options.specs ())
in (FStar_Options.display_usage _157_218))
end
| FStar_Getopt.Die (msg) -> begin
(FStar_Util.print_string msg)
end
| FStar_Getopt.GoOn -> begin
if ((FStar_ST.read FStar_Options.dep) <> None) then begin
(let _157_219 = (FStar_Parser_Dep.collect filenames)
in (FStar_Parser_Dep.print _157_219))
end else begin
if (FStar_ST.read FStar_Options.universes) then begin
(
# 435 "FStar.FStar.fst"
let _78_450 = (let _157_220 = (test_universes filenames)
in (FStar_All.pipe_right _157_220 Prims.ignore))
in (report_universes_errors None))
end else begin
if (FStar_ST.read FStar_Options.interactive) then begin
(
# 439 "FStar.FStar.fst"
let filenames = if (FStar_ST.read FStar_Options.explicit_deps) then begin
(
# 441 "FStar.FStar.fst"
let _78_452 = if ((FStar_List.length filenames) = 0) then begin
(FStar_Util.print_error "--explicit_deps was provided without a file list!\n")
end else begin
()
end
in filenames)
end else begin
(
# 445 "FStar.FStar.fst"
let _78_454 = if ((FStar_List.length filenames) > 0) then begin
(FStar_Util.print_warning "ignoring the file list (no --explicit_deps)\n")
end else begin
()
end
in (detect_dependencies_with_first_interactive_chunk ()))
end
in (
# 450 "FStar.FStar.fst"
let _78_460 = (batch_mode_tc filenames)
in (match (_78_460) with
| (fmods, dsenv, env) -> begin
(interactive_mode dsenv env)
end)))
end else begin
if ((FStar_List.length filenames) >= 1) then begin
(
# 453 "FStar.FStar.fst"
let _78_464 = (batch_mode_tc filenames)
in (match (_78_464) with
| (fmods, dsenv, env) -> begin
(
# 454 "FStar.FStar.fst"
let _78_465 = (report_errors None)
in (
# 455 "FStar.FStar.fst"
let _78_467 = (codegen fmods env)
in (finished_message fmods)))
end))
end else begin
(FStar_Util.print_error "no file provided\n")
end
end
end
end
end)
end)))

# 460 "FStar.FStar.fst"
let main = (fun _78_469 -> (match (()) with
| () -> begin
(FStar_All.try_with (fun _78_471 -> (match (()) with
| () -> begin
(
# 462 "FStar.FStar.fst"
let _78_482 = (go ())
in (
# 463 "FStar.FStar.fst"
let _78_484 = (cleanup ())
in (FStar_All.exit 0)))
end)) (fun _78_470 -> (match (_78_470) with
| e -> begin
(
# 467 "FStar.FStar.fst"
let _78_474 = if (FStar_Absyn_Util.handleable e) then begin
(FStar_Absyn_Util.handle_err false () e)
end else begin
()
end
in (
# 468 "FStar.FStar.fst"
let _78_476 = if (FStar_ST.read FStar_Options.trace_error) then begin
(let _157_225 = (FStar_Util.message_of_exn e)
in (let _157_224 = (FStar_Util.trace_of_exn e)
in (FStar_Util.print2_error "Unexpected error\n%s\n%s\n" _157_225 _157_224)))
end else begin
if (not ((FStar_Absyn_Util.handleable e))) then begin
(let _157_226 = (FStar_Util.message_of_exn e)
in (FStar_Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" _157_226))
end else begin
()
end
end
in (
# 472 "FStar.FStar.fst"
let _78_478 = (cleanup ())
in (FStar_All.exit 1))))
end)))
end))




