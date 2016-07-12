
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
| ((FStar_Parser_AST.Interface (lid1, decls1, _89_13))::[], (FStar_Parser_AST.Module (lid2, decls2))::[]) when (FStar_Ident.lid_equals lid1 lid2) -> begin
(let _180_11 = (let _180_10 = (let _180_9 = (FStar_Parser_Interleave.interleave decls1 decls2)
in (lid1, _180_9))
in FStar_Parser_AST.Module (_180_10))
in (_180_11)::[])
end
| _89_24 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("mismatch between pre-module and module\n")))
end))
end)
in (FStar_Parser_ToSyntax.desugar_file env ast))))


let tc_prims : Prims.unit  ->  (FStar_Syntax_Syntax.modul * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun _89_26 -> (match (()) with
| () -> begin
(

let solver = if (FStar_Options.lax ()) then begin
FStar_SMTEncoding_Solver.dummy
end else begin
FStar_SMTEncoding_Solver.solver
end
in (

let env = (FStar_TypeChecker_Env.initial_env FStar_TypeChecker_Tc.type_of solver FStar_Syntax_Const.prims_lid)
in (

let _89_29 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env)
in (

let p = (FStar_Options.prims ())
in (

let _89_34 = (let _180_14 = (FStar_Parser_Env.empty_env ())
in (parse _180_14 None p))
in (match (_89_34) with
| (dsenv, prims_mod) -> begin
(

let _89_37 = (let _180_15 = (FStar_List.hd prims_mod)
in (FStar_TypeChecker_Tc.check_module env _180_15))
in (match (_89_37) with
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

let _89_63 = (FStar_Parser_ToSyntax.desugar_partial_modul curmod dsenv ast_modul)
in (match (_89_63) with
| (dsenv, modul) -> begin
(

let env = (match (curmod) with
| None -> begin
env
end
| Some (_89_66) -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Interactive mode only supports a single module at the top-level")))
end)
in (

let _89_73 = (FStar_TypeChecker_Tc.tc_partial_modul env modul)
in (match (_89_73) with
| (modul, _89_71, env) -> begin
Some ((Some (modul), dsenv, env))
end)))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(

let _89_78 = (FStar_Parser_ToSyntax.desugar_decls dsenv ast_decls)
in (match (_89_78) with
| (dsenv, decls) -> begin
(match (curmod) with
| None -> begin
(

let _89_80 = (FStar_Util.print_error "fragment without an enclosing module")
in (FStar_All.exit 1))
end
| Some (modul) -> begin
(

let _89_88 = (FStar_TypeChecker_Tc.tc_more_partial_modul env modul decls)
in (match (_89_88) with
| (modul, _89_86, env) -> begin
Some ((Some (modul), dsenv, env))
end))
end)
end))
end)
end)
with
| FStar_Syntax_Syntax.Error (msg, r) when (not ((FStar_Options.trace_error ()))) -> begin
(

let _89_49 = (FStar_TypeChecker_Errors.add_errors env (((msg, r))::[]))
in None)
end
| FStar_Syntax_Syntax.Err (msg) when (not ((FStar_Options.trace_error ()))) -> begin
(

let _89_53 = (FStar_TypeChecker_Errors.add_errors env (((msg, FStar_Range.dummyRange))::[]))
in None)
end
| e when (not ((FStar_Options.trace_error ()))) -> begin
(Prims.raise e)
end)


let pop_context : (FStar_Parser_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  Prims.unit = (fun _89_91 msg -> (match (_89_91) with
| (dsenv, env) -> begin
(

let _89_93 = (let _180_30 = (FStar_Parser_Env.pop dsenv)
in (FStar_All.pipe_right _180_30 Prims.ignore))
in (

let _89_95 = (let _180_31 = (FStar_TypeChecker_Env.pop env msg)
in (FStar_All.pipe_right _180_31 Prims.ignore))
in (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())))
end))


let push_context : (FStar_Parser_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  (FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun _89_99 msg -> (match (_89_99) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_Env.push dsenv)
in (

let env = (FStar_TypeChecker_Env.push env msg)
in (dsenv, env)))
end))


let interactive_tc : ((FStar_Parser_Env.env * FStar_TypeChecker_Env.env), FStar_Syntax_Syntax.modul Prims.option) FStar_Interactive.interactive_tc = (

let pop = (fun _89_106 msg -> (match (_89_106) with
| (dsenv, env) -> begin
(

let _89_108 = (pop_context (dsenv, env) msg)
in (FStar_Options.pop ()))
end))
in (

let push = (fun _89_113 msg -> (match (_89_113) with
| (dsenv, env) -> begin
(

let res = (push_context (dsenv, env) msg)
in (

let _89_116 = (FStar_Options.push ())
in res))
end))
in (

let mark = (fun _89_121 -> (match (_89_121) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_Env.mark dsenv)
in (

let env = (FStar_TypeChecker_Env.mark env)
in (

let _89_124 = (FStar_Options.push ())
in (dsenv, env))))
end))
in (

let reset_mark = (fun _89_129 -> (match (_89_129) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_Env.reset_mark dsenv)
in (

let env = (FStar_TypeChecker_Env.reset_mark env)
in (

let _89_132 = (FStar_Options.pop ())
in (dsenv, env))))
end))
in (

let commit_mark = (fun _89_137 -> (match (_89_137) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_Env.commit_mark dsenv)
in (

let env = (FStar_TypeChecker_Env.commit_mark env)
in (dsenv, env)))
end))
in (

let check_frag = (fun _89_143 curmod text -> (match (_89_143) with
| (dsenv, env) -> begin
try
(match (()) with
| () -> begin
(match ((tc_one_fragment curmod dsenv env text)) with
| Some (m, dsenv, env) -> begin
(let _180_58 = (let _180_57 = (FStar_TypeChecker_Errors.get_err_count ())
in (m, (dsenv, env), _180_57))
in Some (_180_58))
end
| _89_167 -> begin
None
end)
end)
with
| FStar_Syntax_Syntax.Error (msg, r) when (not ((FStar_Options.trace_error ()))) -> begin
(

let _89_153 = (FStar_TypeChecker_Errors.add_errors env (((msg, r))::[]))
in None)
end
| FStar_Syntax_Syntax.Err (msg) when (not ((FStar_Options.trace_error ()))) -> begin
(

let _89_157 = (let _180_62 = (let _180_61 = (let _180_60 = (FStar_TypeChecker_Env.get_range env)
in (msg, _180_60))
in (_180_61)::[])
in (FStar_TypeChecker_Errors.add_errors env _180_62))
in None)
end
end))
in (

let report_fail = (fun _89_169 -> (match (()) with
| () -> begin
(

let _89_170 = (let _180_65 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _180_65 Prims.ignore))
in (FStar_ST.op_Colon_Equals FStar_TypeChecker_Errors.num_errs 0))
end))
in {FStar_Interactive.pop = pop; FStar_Interactive.push = push; FStar_Interactive.mark = mark; FStar_Interactive.reset_mark = reset_mark; FStar_Interactive.commit_mark = commit_mark; FStar_Interactive.check_frag = check_frag; FStar_Interactive.report_fail = report_fail})))))))


let tc_one_file : FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.option  ->  Prims.string  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env pre_fn fn -> (

let _89_178 = (parse dsenv pre_fn fn)
in (match (_89_178) with
| (dsenv, fmods) -> begin
(

let check_mods = (fun _89_180 -> (match (()) with
| () -> begin
(

let _89_190 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun _89_183 m -> (match (_89_183) with
| (env, all_mods) -> begin
(

let _89_187 = (FStar_TypeChecker_Tc.check_module env m)
in (match (_89_187) with
| (m, env) -> begin
(env, (m)::all_mods)
end))
end)) (env, [])))
in (match (_89_190) with
| (env, all_mods) -> begin
((FStar_List.rev all_mods), dsenv, env)
end))
end))
in (match (fmods) with
| (m)::[] when ((FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str) && ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))) -> begin
(FStar_SMTEncoding_Solver.with_hints_db fn check_mods)
end
| _89_194 -> begin
(check_mods ())
end))
end)))


let needs_interleaving : Prims.string  ->  Prims.string  ->  Prims.bool = (fun intf impl -> (

let m1 = (FStar_Parser_Dep.lowercase_module_name intf)
in (

let m2 = (FStar_Parser_Dep.lowercase_module_name impl)
in (((m1 = m2) && ((FStar_Util.get_file_extension intf) = "fsti")) && ((FStar_Util.get_file_extension impl) = "fst")))))


let rec tc_fold_interleave : (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string Prims.list  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun acc remaining -> (

let move = (fun intf impl remaining -> (

let _89_205 = (FStar_Syntax_Syntax.reset_gensym ())
in (

let _89_210 = acc
in (match (_89_210) with
| (all_mods, dsenv, env) -> begin
(

let _89_235 = (match (intf) with
| None -> begin
(tc_one_file dsenv env intf impl)
end
| Some (_89_213) when ((FStar_Options.codegen ()) <> None) -> begin
(

let _89_215 = if (not ((FStar_Options.lax ()))) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Verification and code generation are no supported together with partial modules (i.e, *.fsti); use --lax to extract code separately")))
end else begin
()
end
in (tc_one_file dsenv env intf impl))
end
| Some (iname) -> begin
(

let _89_219 = (FStar_Util.print1 "Interleaving iface+module: %s\n" iname)
in (

let caption = (Prims.strcat "interface: " iname)
in (

let _89_224 = (push_context (dsenv, env) caption)
in (match (_89_224) with
| (dsenv', env') -> begin
(

let _89_229 = (tc_one_file dsenv' env' intf impl)
in (match (_89_229) with
| (_89_226, dsenv', env') -> begin
(

let _89_230 = (pop_context (dsenv', env') caption)
in (tc_one_file dsenv env None iname))
end))
end))))
end)
in (match (_89_235) with
| (ms, dsenv, env) -> begin
(

let acc = ((FStar_List.append all_mods ms), dsenv, env)
in (tc_fold_interleave acc remaining))
end))
end))))
in (match (remaining) with
| (intf)::(impl)::remaining when (needs_interleaving intf impl) -> begin
(move (Some (intf)) impl remaining)
end
| (intf_or_impl)::remaining -> begin
(move None intf_or_impl remaining)
end
| [] -> begin
acc
end)))


let batch_mode_tc_no_prims : FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env filenames -> (

let _89_252 = (tc_fold_interleave ([], dsenv, env) filenames)
in (match (_89_252) with
| (all_mods, dsenv, env) -> begin
(

let _89_253 = if ((FStar_Options.interactive ()) && ((FStar_TypeChecker_Errors.get_err_count ()) = 0)) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end else begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end
in (all_mods, dsenv, env))
end)))


let batch_mode_tc : FStar_Parser_Dep.verify_mode  ->  Prims.string Prims.list  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun verify_mode filenames -> (

let _89_260 = (tc_prims ())
in (match (_89_260) with
| (prims_mod, dsenv, env) -> begin
(

let filenames = (FStar_Dependences.find_deps_if_needed verify_mode filenames)
in (

let _89_266 = if ((not ((FStar_Options.explicit_deps ()))) && (FStar_Options.debug_any ())) then begin
(

let _89_262 = (FStar_Util.print_endline "Auto-deps kicked in; here\'s some info.")
in (

let _89_264 = (FStar_Util.print1 "Here\'s the list of filenames we will process: %s\n" (FStar_String.concat " " filenames))
in (let _180_103 = (let _180_102 = (FStar_Options.verify_module ())
in (FStar_String.concat " " _180_102))
in (FStar_Util.print1 "Here\'s the list of modules we will verify: %s\n" _180_103))))
end else begin
()
end
in (

let _89_271 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (_89_271) with
| (all_mods, dsenv, env) -> begin
((prims_mod)::all_mods, dsenv, env)
end))))
end)))




