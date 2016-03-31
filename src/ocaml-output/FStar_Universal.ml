
open Prims
# 37 "FStar.Universal.fst"
let module_or_interface_name : FStar_Syntax_Syntax.modul  ->  (Prims.bool * FStar_Ident.lident) = (fun m -> (m.FStar_Syntax_Syntax.is_interface, m.FStar_Syntax_Syntax.name))

# 39 "FStar.Universal.fst"
let parse : FStar_Parser_Env.env  ->  Prims.string Prims.option  ->  Prims.string  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env pre_fn fn -> (
# 46 "FStar.Universal.fst"
let ast = (FStar_Parser_Driver.parse_file fn)
in (
# 47 "FStar.Universal.fst"
let ast = (match (pre_fn) with
| None -> begin
ast
end
| Some (pre_fn) -> begin
(
# 51 "FStar.Universal.fst"
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

# 59 "FStar.Universal.fst"
let tc_prims : Prims.unit  ->  (FStar_Syntax_Syntax.modul * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun _87_26 -> (match (()) with
| () -> begin
(
# 68 "FStar.Universal.fst"
let solver = if (FStar_ST.read FStar_Options.verify) then begin
FStar_SMTEncoding_Encode.solver
end else begin
FStar_SMTEncoding_Encode.dummy
end
in (
# 69 "FStar.Universal.fst"
let env = (FStar_TypeChecker_Env.initial_env FStar_TypeChecker_Tc.type_of solver FStar_Syntax_Const.prims_lid)
in (
# 70 "FStar.Universal.fst"
let _87_29 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env)
in (
# 71 "FStar.Universal.fst"
let p = (FStar_Options.prims ())
in (
# 72 "FStar.Universal.fst"
let _87_34 = (let _176_14 = (FStar_Parser_Env.empty_env ())
in (parse _176_14 None p))
in (match (_87_34) with
| (dsenv, prims_mod) -> begin
(
# 73 "FStar.Universal.fst"
let _87_37 = (let _176_15 = (FStar_List.hd prims_mod)
in (FStar_TypeChecker_Tc.check_module env _176_15))
in (match (_87_37) with
| (prims_mod, env) -> begin
(prims_mod, dsenv, env)
end))
end))))))
end))

# 74 "FStar.Universal.fst"
let tc_one_file : FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.option  ->  Prims.string  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env pre_fn fn -> (
# 82 "FStar.Universal.fst"
let _87_44 = (parse dsenv pre_fn fn)
in (match (_87_44) with
| (dsenv, fmods) -> begin
(
# 83 "FStar.Universal.fst"
let _87_54 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun _87_47 m -> (match (_87_47) with
| (env, all_mods) -> begin
(
# 85 "FStar.Universal.fst"
let _87_51 = (FStar_TypeChecker_Tc.check_module env m)
in (match (_87_51) with
| (m, env) -> begin
(env, (m)::all_mods)
end))
end)) (env, [])))
in (match (_87_54) with
| (env, all_mods) -> begin
((FStar_List.rev all_mods), dsenv, env)
end))
end)))

# 87 "FStar.Universal.fst"
let needs_interleaving : Prims.string  ->  Prims.string  ->  Prims.bool = (fun intf impl -> (
# 93 "FStar.Universal.fst"
let m1 = (FStar_Parser_Dep.lowercase_module_name intf)
in (
# 94 "FStar.Universal.fst"
let m2 = (FStar_Parser_Dep.lowercase_module_name impl)
in (((m1 = m2) && ((FStar_Util.get_file_extension intf) = "fsti")) && ((FStar_Util.get_file_extension impl) = "fst")))))

# 96 "FStar.Universal.fst"
let rec tc_fold_interleave : (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string Prims.list  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun acc remaining -> (
# 99 "FStar.Universal.fst"
let move = (fun intf impl remaining -> (
# 100 "FStar.Universal.fst"
let _87_68 = acc
in (match (_87_68) with
| (all_mods, dsenv, env) -> begin
(
# 101 "FStar.Universal.fst"
let _87_69 = (FStar_Syntax_Syntax.reset_gensym ())
in (
# 102 "FStar.Universal.fst"
let _87_74 = (tc_one_file dsenv env intf impl)
in (match (_87_74) with
| (ms, dsenv, env) -> begin
(
# 103 "FStar.Universal.fst"
let acc = ((FStar_List.append all_mods ms), dsenv, env)
in (tc_fold_interleave acc remaining))
end)))
end)))
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

# 113 "FStar.Universal.fst"
let batch_mode_tc_no_prims : FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env filenames -> (
# 119 "FStar.Universal.fst"
let _87_91 = (tc_fold_interleave ([], dsenv, env) filenames)
in (match (_87_91) with
| (all_mods, dsenv, env) -> begin
(
# 120 "FStar.Universal.fst"
let _87_92 = if ((FStar_ST.read FStar_Options.interactive) && ((FStar_TypeChecker_Errors.get_err_count ()) = 0)) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end else begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end
in (all_mods, dsenv, env))
end)))

# 123 "FStar.Universal.fst"
let batch_mode_tc : Prims.string Prims.list  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun filenames -> (
# 126 "FStar.Universal.fst"
let _87_98 = (tc_prims ())
in (match (_87_98) with
| (prims_mod, dsenv, env) -> begin
(
# 127 "FStar.Universal.fst"
let _87_101 = (FStar_Dependences.find_deps_if_needed filenames)
in (match (_87_101) with
| (filenames, admit_fsi) -> begin
(
# 128 "FStar.Universal.fst"
let _87_105 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (_87_105) with
| (all_mods, dsenv, env) -> begin
((prims_mod)::all_mods, dsenv, env)
end))
end))
end)))

# 129 "FStar.Universal.fst"
let tc_one_fragment : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string  ->  (FStar_Syntax_Syntax.modul Prims.option * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) Prims.option = (fun curmod dsenv env frag -> try
(match (()) with
| () -> begin
(match ((FStar_Parser_Driver.parse_fragment frag)) with
| FStar_Parser_Driver.Empty -> begin
Some ((curmod, dsenv, env))
end
| FStar_Parser_Driver.Modul (ast_modul) -> begin
(
# 141 "FStar.Universal.fst"
let _87_131 = (FStar_Parser_ToSyntax.desugar_partial_modul curmod dsenv ast_modul)
in (match (_87_131) with
| (dsenv, modul) -> begin
(
# 142 "FStar.Universal.fst"
let env = (match (curmod) with
| None -> begin
env
end
| Some (_87_134) -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Interactive mode only supports a single module at the top-level")))
end)
in (
# 145 "FStar.Universal.fst"
let _87_141 = (FStar_TypeChecker_Tc.tc_partial_modul env modul)
in (match (_87_141) with
| (modul, _87_139, env) -> begin
Some ((Some (modul), dsenv, env))
end)))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(
# 149 "FStar.Universal.fst"
let _87_146 = (FStar_Parser_ToSyntax.desugar_decls dsenv ast_decls)
in (match (_87_146) with
| (dsenv, decls) -> begin
(match (curmod) with
| None -> begin
(
# 151 "FStar.Universal.fst"
let _87_148 = (FStar_Util.print_error "fragment without an enclosing module")
in (FStar_All.exit 1))
end
| Some (modul) -> begin
(
# 153 "FStar.Universal.fst"
let _87_156 = (FStar_TypeChecker_Tc.tc_more_partial_modul env modul decls)
in (match (_87_156) with
| (modul, _87_154, env) -> begin
Some ((Some (modul), dsenv, env))
end))
end)
end))
end)
end)
with
| FStar_Syntax_Syntax.Error (msg, r) when (not ((FStar_ST.read FStar_Options.trace_error))) -> begin
(
# 158 "FStar.Universal.fst"
let _87_117 = (FStar_TypeChecker_Errors.add_errors env (((msg, r))::[]))
in None)
end
| FStar_Syntax_Syntax.Err (msg) when (not ((FStar_ST.read FStar_Options.trace_error))) -> begin
(
# 161 "FStar.Universal.fst"
let _87_121 = (FStar_TypeChecker_Errors.add_errors env (((msg, FStar_Range.dummyRange))::[]))
in None)
end
| e when (not ((FStar_ST.read FStar_Options.trace_error))) -> begin
(Prims.raise e)
end)

# 163 "FStar.Universal.fst"
let interactive_tc : ((FStar_Parser_Env.env * FStar_TypeChecker_Env.env), FStar_Syntax_Syntax.modul Prims.option) FStar_Interactive.interactive_tc = (
# 169 "FStar.Universal.fst"
let pop = (fun _87_160 msg -> (match (_87_160) with
| (dsenv, env) -> begin
(
# 170 "FStar.Universal.fst"
let _87_162 = (let _176_62 = (FStar_Parser_Env.pop dsenv)
in (FStar_All.pipe_right _176_62 Prims.ignore))
in (
# 171 "FStar.Universal.fst"
let _87_164 = (let _176_63 = (FStar_TypeChecker_Env.pop env msg)
in (FStar_All.pipe_right _176_63 Prims.ignore))
in (
# 172 "FStar.Universal.fst"
let _87_166 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (let _176_64 = (FStar_Options.restore_cmd_line_options ())
in (FStar_All.pipe_right _176_64 Prims.ignore)))))
end))
in (
# 175 "FStar.Universal.fst"
let push = (fun _87_171 msg -> (match (_87_171) with
| (dsenv, env) -> begin
(
# 176 "FStar.Universal.fst"
let dsenv = (FStar_Parser_Env.push dsenv)
in (
# 177 "FStar.Universal.fst"
let env = (FStar_TypeChecker_Env.push env msg)
in (dsenv, env)))
end))
in (
# 180 "FStar.Universal.fst"
let mark = (fun _87_178 -> (match (_87_178) with
| (dsenv, env) -> begin
(
# 181 "FStar.Universal.fst"
let dsenv = (FStar_Parser_Env.mark dsenv)
in (
# 182 "FStar.Universal.fst"
let env = (FStar_TypeChecker_Env.mark env)
in (dsenv, env)))
end))
in (
# 185 "FStar.Universal.fst"
let reset_mark = (fun _87_184 -> (match (_87_184) with
| (dsenv, env) -> begin
(
# 186 "FStar.Universal.fst"
let dsenv = (FStar_Parser_Env.reset_mark dsenv)
in (
# 187 "FStar.Universal.fst"
let env = (FStar_TypeChecker_Env.reset_mark env)
in (dsenv, env)))
end))
in (
# 190 "FStar.Universal.fst"
let commit_mark = (fun _87_190 -> (match (_87_190) with
| (dsenv, env) -> begin
(
# 191 "FStar.Universal.fst"
let dsenv = (FStar_Parser_Env.commit_mark dsenv)
in (
# 192 "FStar.Universal.fst"
let env = (FStar_TypeChecker_Env.commit_mark env)
in (dsenv, env)))
end))
in (
# 195 "FStar.Universal.fst"
let check_frag = (fun _87_196 curmod text -> (match (_87_196) with
| (dsenv, env) -> begin
try
(match (()) with
| () -> begin
(match ((tc_one_fragment curmod dsenv env text)) with
| Some (m, dsenv, env) -> begin
(let _176_83 = (let _176_82 = (FStar_TypeChecker_Errors.get_err_count ())
in (m, (dsenv, env), _176_82))
in Some (_176_83))
end
| _87_220 -> begin
None
end)
end)
with
| FStar_Syntax_Syntax.Error (msg, r) when (not ((FStar_ST.read FStar_Options.trace_error))) -> begin
(
# 203 "FStar.Universal.fst"
let _87_206 = (FStar_TypeChecker_Errors.add_errors env (((msg, r))::[]))
in None)
end
| FStar_Syntax_Syntax.Err (msg) when (not ((FStar_ST.read FStar_Options.trace_error))) -> begin
(
# 207 "FStar.Universal.fst"
let _87_210 = (let _176_87 = (let _176_86 = (let _176_85 = (FStar_TypeChecker_Env.get_range env)
in (msg, _176_85))
in (_176_86)::[])
in (FStar_TypeChecker_Errors.add_errors env _176_87))
in None)
end
end))
in (
# 210 "FStar.Universal.fst"
let report_fail = (fun _87_222 -> (match (()) with
| () -> begin
(
# 211 "FStar.Universal.fst"
let _87_223 = (let _176_90 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _176_90 Prims.ignore))
in (FStar_ST.op_Colon_Equals FStar_TypeChecker_Errors.num_errs 0))
end))
in {FStar_Interactive.pop = pop; FStar_Interactive.push = push; FStar_Interactive.mark = mark; FStar_Interactive.reset_mark = reset_mark; FStar_Interactive.commit_mark = commit_mark; FStar_Interactive.check_frag = check_frag; FStar_Interactive.report_fail = report_fail})))))))




