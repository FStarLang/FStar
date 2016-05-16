
open Prims

let module_or_interface_name : FStar_Syntax_Syntax.modul  ->  (Prims.bool * FStar_Ident.lident) = (fun m -> (m.FStar_Syntax_Syntax.is_interface, m.FStar_Syntax_Syntax.name))


let parse : FStar_Parser_Env.env  ->  Prims.string Prims.option  ->  Prims.string  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env pre_fn fn -> (

let ast = (FStar_Parser_Driver.parse_file fn)
in (

let ast = (match (pre_fn) with
| None -> begin
ast
end
| Some (pre_fn) -> begin
(

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


let tc_prims : Prims.unit  ->  (FStar_Syntax_Syntax.modul * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun _87_26 -> (match (()) with
| () -> begin
(

let solver = if (FStar_Options.lax ()) then begin
FStar_SMTEncoding_Encode.dummy
end else begin
FStar_SMTEncoding_Encode.solver
end
in (

let env = (FStar_TypeChecker_Env.initial_env FStar_TypeChecker_Tc.type_of solver FStar_Syntax_Const.prims_lid)
in (

let _87_29 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env)
in (

let p = (FStar_Options.prims ())
in (

let _87_34 = (let _176_14 = (FStar_Parser_Env.empty_env ())
in (parse _176_14 None p))
in (match (_87_34) with
| (dsenv, prims_mod) -> begin
(

let _87_37 = (let _176_15 = (FStar_List.hd prims_mod)
in (FStar_TypeChecker_Tc.check_module env _176_15))
in (match (_87_37) with
| (prims_mod, env) -> begin
(prims_mod, dsenv, env)
end))
end))))))
end))


let tc_one_fragment : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string  ->  (FStar_Syntax_Syntax.modul Prims.option * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) Prims.option = (fun curmod dsenv env frag -> try
(match (()) with
| () -> begin
(match ((FStar_Parser_Driver.parse_fragment frag)) with
| FStar_Parser_Driver.Empty -> begin
Some ((curmod, dsenv, env))
end
| FStar_Parser_Driver.Modul (ast_modul) -> begin
(

let _87_63 = (FStar_Parser_ToSyntax.desugar_partial_modul curmod dsenv ast_modul)
in (match (_87_63) with
| (dsenv, modul) -> begin
(

let env = (match (curmod) with
| None -> begin
env
end
| Some (_87_66) -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Interactive mode only supports a single module at the top-level")))
end)
in (

let _87_73 = (FStar_TypeChecker_Tc.tc_partial_modul env modul)
in (match (_87_73) with
| (modul, _87_71, env) -> begin
Some ((Some (modul), dsenv, env))
end)))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(

let _87_78 = (FStar_Parser_ToSyntax.desugar_decls dsenv ast_decls)
in (match (_87_78) with
| (dsenv, decls) -> begin
(match (curmod) with
| None -> begin
(

let _87_80 = (FStar_Util.print_error "fragment without an enclosing module")
in (FStar_All.exit 1))
end
| Some (modul) -> begin
(

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
| FStar_Syntax_Syntax.Error (msg, r) when (not ((FStar_Options.trace_error ()))) -> begin
(

let _87_49 = (FStar_TypeChecker_Errors.add_errors env (((msg, r))::[]))
in None)
end
| FStar_Syntax_Syntax.Err (msg) when (not ((FStar_Options.trace_error ()))) -> begin
(

let _87_53 = (FStar_TypeChecker_Errors.add_errors env (((msg, FStar_Range.dummyRange))::[]))
in None)
end
| e when (not ((FStar_Options.trace_error ()))) -> begin
(Prims.raise e)
end)


let pop_context : (FStar_Parser_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  Prims.unit = (fun _87_91 msg -> (match (_87_91) with
| (dsenv, env) -> begin
(

let _87_93 = (let _176_30 = (FStar_Parser_Env.pop dsenv)
in (FStar_All.pipe_right _176_30 Prims.ignore))
in (

let _87_95 = (let _176_31 = (FStar_TypeChecker_Env.pop env msg)
in (FStar_All.pipe_right _176_31 Prims.ignore))
in (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())))
end))


let push_context : (FStar_Parser_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  (FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun _87_99 msg -> (match (_87_99) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_Env.push dsenv)
in (

let env = (FStar_TypeChecker_Env.push env msg)
in (dsenv, env)))
end))


let interactive_tc : ((FStar_Parser_Env.env * FStar_TypeChecker_Env.env), FStar_Syntax_Syntax.modul Prims.option) FStar_Interactive.interactive_tc = (

let pop = (fun _87_106 msg -> (match (_87_106) with
| (dsenv, env) -> begin
(

let _87_108 = (pop_context (dsenv, env) msg)
in (FStar_Options.pop ()))
end))
in (

let push = (fun _87_113 msg -> (match (_87_113) with
| (dsenv, env) -> begin
(

let res = (push_context (dsenv, env) msg)
in (

let _87_116 = (FStar_Options.push ())
in res))
end))
in (

let mark = (fun _87_121 -> (match (_87_121) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_Env.mark dsenv)
in (

let env = (FStar_TypeChecker_Env.mark env)
in (

let _87_124 = (FStar_Options.push ())
in (dsenv, env))))
end))
in (

let reset_mark = (fun _87_129 -> (match (_87_129) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_Env.reset_mark dsenv)
in (

let env = (FStar_TypeChecker_Env.reset_mark env)
in (

let _87_132 = (FStar_Options.pop ())
in (dsenv, env))))
end))
in (

let commit_mark = (fun _87_137 -> (match (_87_137) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_Env.commit_mark dsenv)
in (

let env = (FStar_TypeChecker_Env.commit_mark env)
in (dsenv, env)))
end))
in (

let check_frag = (fun _87_143 curmod text -> (match (_87_143) with
| (dsenv, env) -> begin
try
(match (()) with
| () -> begin
(match ((tc_one_fragment curmod dsenv env text)) with
| Some (m, dsenv, env) -> begin
(let _176_58 = (let _176_57 = (FStar_TypeChecker_Errors.get_err_count ())
in (m, (dsenv, env), _176_57))
in Some (_176_58))
end
| _87_167 -> begin
None
end)
end)
with
| FStar_Syntax_Syntax.Error (msg, r) when (not ((FStar_Options.trace_error ()))) -> begin
(

let _87_153 = (FStar_TypeChecker_Errors.add_errors env (((msg, r))::[]))
in None)
end
| FStar_Syntax_Syntax.Err (msg) when (not ((FStar_Options.trace_error ()))) -> begin
(

let _87_157 = (let _176_62 = (let _176_61 = (let _176_60 = (FStar_TypeChecker_Env.get_range env)
in (msg, _176_60))
in (_176_61)::[])
in (FStar_TypeChecker_Errors.add_errors env _176_62))
in None)
end
end))
in (

let report_fail = (fun _87_169 -> (match (()) with
| () -> begin
(

let _87_170 = (let _176_65 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _176_65 Prims.ignore))
in (FStar_ST.op_Colon_Equals FStar_TypeChecker_Errors.num_errs 0))
end))
in {FStar_Interactive.pop = pop; FStar_Interactive.push = push; FStar_Interactive.mark = mark; FStar_Interactive.reset_mark = reset_mark; FStar_Interactive.commit_mark = commit_mark; FStar_Interactive.check_frag = check_frag; FStar_Interactive.report_fail = report_fail})))))))


let tc_one_file : FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.option  ->  Prims.string  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env pre_fn fn -> (

let _87_178 = (parse dsenv pre_fn fn)
in (match (_87_178) with
| (dsenv, fmods) -> begin
(

let _87_188 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun _87_181 m -> (match (_87_181) with
| (env, all_mods) -> begin
(

let _87_185 = (FStar_TypeChecker_Tc.check_module env m)
in (match (_87_185) with
| (m, env) -> begin
(env, (m)::all_mods)
end))
end)) (env, [])))
in (match (_87_188) with
| (env, all_mods) -> begin
((FStar_List.rev all_mods), dsenv, env)
end))
end)))


let needs_interleaving : Prims.string  ->  Prims.string  ->  Prims.bool = (fun intf impl -> (

let m1 = (FStar_Parser_Dep.lowercase_module_name intf)
in (

let m2 = (FStar_Parser_Dep.lowercase_module_name impl)
in (((m1 = m2) && ((FStar_Util.get_file_extension intf) = "fsti")) && ((FStar_Util.get_file_extension impl) = "fst")))))


let rec tc_fold_interleave : (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string Prims.list  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun acc remaining -> (

let move = (fun intf impl remaining -> (

let _87_199 = (FStar_Syntax_Syntax.reset_gensym ())
in (

let _87_204 = acc
in (match (_87_204) with
| (all_mods, dsenv, env) -> begin
(

let _87_229 = (match (intf) with
| None -> begin
(tc_one_file dsenv env intf impl)
end
| Some (_87_207) when ((FStar_Options.codegen ()) <> None) -> begin
(

let _87_209 = if (not ((FStar_Options.lax ()))) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Verification and code generation are no supported together with partial modules (i.e, *.fsti); use --lax to extract code separately")))
end else begin
()
end
in (tc_one_file dsenv env intf impl))
end
| Some (iname) -> begin
(

let _87_213 = (FStar_Util.print1 "Interleaving iface+module: %s\n" iname)
in (

let caption = (Prims.strcat "interface: " iname)
in (

let _87_218 = (push_context (dsenv, env) caption)
in (match (_87_218) with
| (dsenv', env') -> begin
(

let _87_223 = (tc_one_file dsenv' env' intf impl)
in (match (_87_223) with
| (_87_220, dsenv', env') -> begin
(

let _87_224 = (pop_context (dsenv', env') caption)
in (tc_one_file dsenv env None iname))
end))
end))))
end)
in (match (_87_229) with
| (ms, dsenv, env) -> begin
(

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


let batch_mode_tc_no_prims : FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env filenames -> (

let _87_246 = (tc_fold_interleave ([], dsenv, env) filenames)
in (match (_87_246) with
| (all_mods, dsenv, env) -> begin
(

let _87_247 = if ((FStar_Options.interactive ()) && ((FStar_TypeChecker_Errors.get_err_count ()) = 0)) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end else begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end
in (all_mods, dsenv, env))
end)))


let batch_mode_tc : Prims.string Prims.list  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun filenames -> (

let _87_253 = (tc_prims ())
in (match (_87_253) with
| (prims_mod, dsenv, env) -> begin
(

let filenames = (FStar_Dependences.find_deps_if_needed filenames)
in (

let _87_258 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (_87_258) with
| (all_mods, dsenv, env) -> begin
((prims_mod)::all_mods, dsenv, env)
end)))
end)))




