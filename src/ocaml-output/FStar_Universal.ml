
open Prims
# 39 "FStar.Universal.fst"
let module_or_interface_name : FStar_Syntax_Syntax.modul  ->  (Prims.bool * FStar_Ident.lident) = (fun m -> (m.FStar_Syntax_Syntax.is_interface, m.FStar_Syntax_Syntax.name))

# 44 "FStar.Universal.fst"
let parse : FStar_Parser_Env.env  ->  Prims.string Prims.option  ->  Prims.string  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env pre_fn fn -> (
# 47 "FStar.Universal.fst"
let ast = (FStar_Parser_Driver.parse_file fn)
in (
# 48 "FStar.Universal.fst"
let ast = (match (pre_fn) with
| None -> begin
ast
end
| Some (pre_fn) -> begin
(
# 52 "FStar.Universal.fst"
let pre_ast = (FStar_Parser_Driver.parse_file pre_fn)
in (match ((pre_ast, ast)) with
| (FStar_Parser_AST.Interface (lid1, decls1, _87_13)::[], FStar_Parser_AST.Module (lid2, decls2)::[]) when (FStar_Ident.lid_equals lid1 lid2) -> begin
(let _176_11 = (let _176_10 = (let _176_9 = (FStar_Parser_Interleave.interleave decls1 decls2)
in (lid1, _176_9))
in FStar_Parser_AST.Module (_176_10))
in (_176_11)::[])
end
| _87_24 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("mismatch between pre-module and module\n")))
end))
end)
in (FStar_Parser_ToSyntax.desugar_file env ast))))

# 66 "FStar.Universal.fst"
let tc_prims : Prims.unit  ->  (FStar_Syntax_Syntax.modul * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun _87_26 -> (match (()) with
| () -> begin
(
# 69 "FStar.Universal.fst"
let solver = if (FStar_ST.read FStar_Options.verify) then begin
FStar_SMTEncoding_Encode.solver
end else begin
FStar_SMTEncoding_Encode.dummy
end
in (
# 70 "FStar.Universal.fst"
let env = (FStar_TypeChecker_Env.initial_env FStar_TypeChecker_Tc.type_of solver FStar_Syntax_Const.prims_lid)
in (
# 71 "FStar.Universal.fst"
let _87_29 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env)
in (
# 72 "FStar.Universal.fst"
let p = (FStar_Options.prims ())
in (
# 73 "FStar.Universal.fst"
let _87_34 = (let _176_14 = (FStar_Parser_Env.empty_env ())
in (parse _176_14 None p))
in (match (_87_34) with
| (dsenv, prims_mod) -> begin
(
# 74 "FStar.Universal.fst"
let _87_37 = (let _176_15 = (FStar_List.hd prims_mod)
in (FStar_TypeChecker_Tc.check_module env _176_15))
in (match (_87_37) with
| (prims_mod, env) -> begin
(prims_mod, dsenv, env)
end))
end))))))
end))

# 80 "FStar.Universal.fst"
let tc_one_fragment : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string  ->  (FStar_Syntax_Syntax.modul Prims.option * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) Prims.option = (fun curmod dsenv env frag -> try
(match (()) with
| () -> begin
(match ((FStar_Parser_Driver.parse_fragment frag)) with
| FStar_Parser_Driver.Empty -> begin
Some ((curmod, dsenv, env))
end
| FStar_Parser_Driver.Modul (ast_modul) -> begin
(
# 87 "FStar.Universal.fst"
let _87_63 = (FStar_Parser_ToSyntax.desugar_partial_modul curmod dsenv ast_modul)
in (match (_87_63) with
| (dsenv, modul) -> begin
(
# 88 "FStar.Universal.fst"
let env = (match (curmod) with
| None -> begin
env
end
| Some (_87_66) -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Interactive mode only supports a single module at the top-level")))
end)
in (
# 91 "FStar.Universal.fst"
let _87_73 = (FStar_TypeChecker_Tc.tc_partial_modul env modul)
in (match (_87_73) with
| (modul, _87_71, env) -> begin
Some ((Some (modul), dsenv, env))
end)))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(
# 95 "FStar.Universal.fst"
let _87_78 = (FStar_Parser_ToSyntax.desugar_decls dsenv ast_decls)
in (match (_87_78) with
| (dsenv, decls) -> begin
(match (curmod) with
| None -> begin
(
# 97 "FStar.Universal.fst"
let _87_80 = (FStar_Util.print_error "fragment without an enclosing module")
in (FStar_All.exit 1))
end
| Some (modul) -> begin
(
# 99 "FStar.Universal.fst"
let _87_88 = (FStar_TypeChecker_Tc.tc_more_partial_modul env modul decls)
in (match (_87_88) with
| (modul, _87_86, env) -> begin
Some ((Some (modul), dsenv, env))
end))
end)
end))
end)
end)
with
| FStar_Syntax_Syntax.Error (msg, r) when (not ((FStar_ST.read FStar_Options.trace_error))) -> begin
(
# 104 "FStar.Universal.fst"
let _87_49 = (FStar_TypeChecker_Errors.add_errors env (((msg, r))::[]))
in None)
end
| FStar_Syntax_Syntax.Err (msg) when (not ((FStar_ST.read FStar_Options.trace_error))) -> begin
(
# 107 "FStar.Universal.fst"
let _87_53 = (FStar_TypeChecker_Errors.add_errors env (((msg, FStar_Range.dummyRange))::[]))
in None)
end
| e when (not ((FStar_ST.read FStar_Options.trace_error))) -> begin
(Prims.raise e)
end)

# 114 "FStar.Universal.fst"
let interactive_tc : ((FStar_Parser_Env.env * FStar_TypeChecker_Env.env), FStar_Syntax_Syntax.modul Prims.option) FStar_Interactive.interactive_tc = (
# 115 "FStar.Universal.fst"
let pop = (fun _87_92 msg -> (match (_87_92) with
| (dsenv, env) -> begin
(
# 116 "FStar.Universal.fst"
let _87_94 = (let _176_30 = (FStar_Parser_Env.pop dsenv)
in (FStar_All.pipe_right _176_30 Prims.ignore))
in (
# 117 "FStar.Universal.fst"
let _87_96 = (let _176_31 = (FStar_TypeChecker_Env.pop env msg)
in (FStar_All.pipe_right _176_31 Prims.ignore))
in (
# 118 "FStar.Universal.fst"
let _87_98 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _176_32 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _176_32 Prims.ignore)))))
end))
in (
# 121 "FStar.Universal.fst"
let push = (fun _87_103 msg -> (match (_87_103) with
| (dsenv, env) -> begin
(
# 122 "FStar.Universal.fst"
let dsenv = (FStar_Parser_Env.push dsenv)
in (
# 123 "FStar.Universal.fst"
let env = (FStar_TypeChecker_Env.push env msg)
in (dsenv, env)))
end))
in (
# 126 "FStar.Universal.fst"
let mark = (fun _87_110 -> (match (_87_110) with
| (dsenv, env) -> begin
(
# 127 "FStar.Universal.fst"
let dsenv = (FStar_Parser_Env.mark dsenv)
in (
# 128 "FStar.Universal.fst"
let env = (FStar_TypeChecker_Env.mark env)
in (dsenv, env)))
end))
in (
# 131 "FStar.Universal.fst"
let reset_mark = (fun _87_116 -> (match (_87_116) with
| (dsenv, env) -> begin
(
# 132 "FStar.Universal.fst"
let dsenv = (FStar_Parser_Env.reset_mark dsenv)
in (
# 133 "FStar.Universal.fst"
let env = (FStar_TypeChecker_Env.reset_mark env)
in (dsenv, env)))
end))
in (
# 136 "FStar.Universal.fst"
let commit_mark = (fun _87_122 -> (match (_87_122) with
| (dsenv, env) -> begin
(
# 137 "FStar.Universal.fst"
let dsenv = (FStar_Parser_Env.commit_mark dsenv)
in (
# 138 "FStar.Universal.fst"
let env = (FStar_TypeChecker_Env.commit_mark env)
in (dsenv, env)))
end))
in (
# 141 "FStar.Universal.fst"
let check_frag = (fun _87_128 curmod text -> (match (_87_128) with
| (dsenv, env) -> begin
try
(match (()) with
| () -> begin
(match ((tc_one_fragment curmod dsenv env text)) with
| Some (m, dsenv, env) -> begin
(let _176_51 = (let _176_50 = (FStar_TypeChecker_Errors.get_err_count ())
in (m, (dsenv, env), _176_50))
in Some (_176_51))
end
| _87_152 -> begin
None
end)
end)
with
| FStar_Syntax_Syntax.Error (msg, r) when (not ((FStar_ST.read FStar_Options.trace_error))) -> begin
(
# 149 "FStar.Universal.fst"
let _87_138 = (FStar_TypeChecker_Errors.add_errors env (((msg, r))::[]))
in None)
end
| FStar_Syntax_Syntax.Err (msg) when (not ((FStar_ST.read FStar_Options.trace_error))) -> begin
(
# 153 "FStar.Universal.fst"
let _87_142 = (let _176_55 = (let _176_54 = (let _176_53 = (FStar_TypeChecker_Env.get_range env)
in (msg, _176_53))
in (_176_54)::[])
in (FStar_TypeChecker_Errors.add_errors env _176_55))
in None)
end
end))
in (
# 156 "FStar.Universal.fst"
let report_fail = (fun _87_154 -> (match (()) with
| () -> begin
(
# 157 "FStar.Universal.fst"
let _87_155 = (let _176_58 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _176_58 Prims.ignore))
in (FStar_ST.op_Colon_Equals FStar_TypeChecker_Errors.num_errs 0))
end))
in {FStar_Interactive.pop = pop; FStar_Interactive.push = push; FStar_Interactive.mark = mark; FStar_Interactive.reset_mark = reset_mark; FStar_Interactive.commit_mark = commit_mark; FStar_Interactive.check_frag = check_frag; FStar_Interactive.report_fail = report_fail})))))))

# 171 "FStar.Universal.fst"
let tc_one_file : FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.option  ->  Prims.string  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env pre_fn fn -> (
# 174 "FStar.Universal.fst"
let _87_163 = (parse dsenv pre_fn fn)
in (match (_87_163) with
| (dsenv, fmods) -> begin
(
# 175 "FStar.Universal.fst"
let _87_173 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun _87_166 m -> (match (_87_166) with
| (env, all_mods) -> begin
(
# 177 "FStar.Universal.fst"
let _87_170 = (FStar_TypeChecker_Tc.check_module env m)
in (match (_87_170) with
| (m, env) -> begin
(env, (m)::all_mods)
end))
end)) (env, [])))
in (match (_87_173) with
| (env, all_mods) -> begin
((FStar_List.rev all_mods), dsenv, env)
end))
end)))

# 184 "FStar.Universal.fst"
let needs_interleaving : Prims.string  ->  Prims.string  ->  Prims.bool = (fun intf impl -> (
# 185 "FStar.Universal.fst"
let m1 = (FStar_Parser_Dep.lowercase_module_name intf)
in (
# 186 "FStar.Universal.fst"
let m2 = (FStar_Parser_Dep.lowercase_module_name impl)
in (((m1 = m2) && ((FStar_Util.get_file_extension intf) = "fsti")) && ((FStar_Util.get_file_extension impl) = "fst")))))

# 190 "FStar.Universal.fst"
let rec tc_fold_interleave : (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string Prims.list  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun acc remaining -> (
# 191 "FStar.Universal.fst"
let move = (fun intf impl remaining -> (
# 192 "FStar.Universal.fst"
let _87_184 = (FStar_Syntax_Syntax.reset_gensym ())
in (
# 193 "FStar.Universal.fst"
let _87_189 = acc
in (match (_87_189) with
| (all_mods, dsenv, env) -> begin
(
# 194 "FStar.Universal.fst"
let _87_212 = (match (intf) with
| None -> begin
(tc_one_file dsenv env intf impl)
end
| Some (_87_192) when ((FStar_ST.read FStar_Options.codegen) <> None) -> begin
(
# 199 "FStar.Universal.fst"
let _87_194 = if (FStar_ST.read FStar_Options.verify) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Verification and code generation are no supported together with partial modules (i.e, *.fsti); use --lax to extract code separately")))
end else begin
()
end
in (tc_one_file dsenv env intf impl))
end
| Some (iname) -> begin
(
# 204 "FStar.Universal.fst"
let caption = (Prims.strcat "interface: " iname)
in (
# 206 "FStar.Universal.fst"
let _87_201 = (interactive_tc.FStar_Interactive.push (dsenv, env) caption)
in (match (_87_201) with
| (dsenv', env') -> begin
(
# 207 "FStar.Universal.fst"
let _87_206 = (tc_one_file dsenv' env' intf impl)
in (match (_87_206) with
| (_87_203, dsenv', env') -> begin
(
# 209 "FStar.Universal.fst"
let _87_207 = (interactive_tc.FStar_Interactive.pop (dsenv', env') caption)
in (tc_one_file dsenv env None iname))
end))
end)))
end)
in (match (_87_212) with
| (ms, dsenv, env) -> begin
(
# 211 "FStar.Universal.fst"
let acc = ((FStar_List.append all_mods ms), dsenv, env)
in (tc_fold_interleave acc remaining))
end))
end))))
in (match (remaining) with
| intf::impl::remaining when (needs_interleaving intf impl) -> begin
(move (Some (intf)) impl remaining)
end
| intf_or_impl::remaining -> begin
(move None intf_or_impl remaining)
end
| [] -> begin
acc
end)))

# 226 "FStar.Universal.fst"
let batch_mode_tc_no_prims : FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env filenames -> (
# 227 "FStar.Universal.fst"
let _87_229 = (tc_fold_interleave ([], dsenv, env) filenames)
in (match (_87_229) with
| (all_mods, dsenv, env) -> begin
(
# 228 "FStar.Universal.fst"
let _87_230 = if ((FStar_ST.read FStar_Options.interactive) && ((FStar_TypeChecker_Errors.get_err_count ()) = 0)) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end else begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end
in (all_mods, dsenv, env))
end)))

# 233 "FStar.Universal.fst"
let batch_mode_tc : Prims.string Prims.list  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun filenames -> (
# 234 "FStar.Universal.fst"
let _87_236 = (tc_prims ())
in (match (_87_236) with
| (prims_mod, dsenv, env) -> begin
(
# 235 "FStar.Universal.fst"
let _87_239 = (FStar_Dependences.find_deps_if_needed filenames)
in (match (_87_239) with
| (filenames, admit_fsi) -> begin
(
# 236 "FStar.Universal.fst"
let _87_243 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (_87_243) with
| (all_mods, dsenv, env) -> begin
((prims_mod)::all_mods, dsenv, env)
end))
end))
end)))




