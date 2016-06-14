
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
| ((FStar_Parser_AST.Interface (lid1, decls1, _88_13))::[], (FStar_Parser_AST.Module (lid2, decls2))::[]) when (FStar_Ident.lid_equals lid1 lid2) -> begin
(let _178_11 = (let _178_10 = (let _178_9 = (FStar_Parser_Interleave.interleave decls1 decls2)
in (lid1, _178_9))
in FStar_Parser_AST.Module (_178_10))
in (_178_11)::[])
end
| _88_24 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("mismatch between pre-module and module\n")))
end))
end)
in (FStar_Parser_ToSyntax.desugar_file env ast))))


let tc_prims : Prims.unit  ->  (FStar_Syntax_Syntax.modul * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun _88_26 -> (match (()) with
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

let _88_29 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env)
in (

let p = (FStar_Options.prims ())
in (

let _88_34 = (let _178_14 = (FStar_Parser_Env.empty_env ())
in (parse _178_14 None p))
in (match (_88_34) with
| (dsenv, prims_mod) -> begin
(

let _88_37 = (let _178_15 = (FStar_List.hd prims_mod)
in (FStar_TypeChecker_Tc.check_module env _178_15))
in (match (_88_37) with
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

let _88_63 = (FStar_Parser_ToSyntax.desugar_partial_modul curmod dsenv ast_modul)
in (match (_88_63) with
| (dsenv, modul) -> begin
(

let env = (match (curmod) with
| None -> begin
env
end
| Some (_88_66) -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Interactive mode only supports a single module at the top-level")))
end)
in (

let _88_73 = (FStar_TypeChecker_Tc.tc_partial_modul env modul)
in (match (_88_73) with
| (modul, _88_71, env) -> begin
Some ((Some (modul), dsenv, env))
end)))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(

let _88_78 = (FStar_Parser_ToSyntax.desugar_decls dsenv ast_decls)
in (match (_88_78) with
| (dsenv, decls) -> begin
(match (curmod) with
| None -> begin
(

let _88_80 = (FStar_Util.print_error "fragment without an enclosing module")
in (FStar_All.exit 1))
end
| Some (modul) -> begin
(

let _88_88 = (FStar_TypeChecker_Tc.tc_more_partial_modul env modul decls)
in (match (_88_88) with
| (modul, _88_86, env) -> begin
Some ((Some (modul), dsenv, env))
end))
end)
end))
end)
end)
with
| FStar_Syntax_Syntax.Error (msg, r) when (not ((FStar_Options.trace_error ()))) -> begin
(

let _88_49 = (FStar_TypeChecker_Errors.add_errors env (((msg, r))::[]))
in None)
end
| FStar_Syntax_Syntax.Err (msg) when (not ((FStar_Options.trace_error ()))) -> begin
(

let _88_53 = (FStar_TypeChecker_Errors.add_errors env (((msg, FStar_Range.dummyRange))::[]))
in None)
end
| e when (not ((FStar_Options.trace_error ()))) -> begin
(Prims.raise e)
end)


let pop_context : (FStar_Parser_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  Prims.unit = (fun _88_91 msg -> (match (_88_91) with
| (dsenv, env) -> begin
(

let _88_93 = (let _178_30 = (FStar_Parser_Env.pop dsenv)
in (FStar_All.pipe_right _178_30 Prims.ignore))
in (

let _88_95 = (let _178_31 = (FStar_TypeChecker_Env.pop env msg)
in (FStar_All.pipe_right _178_31 Prims.ignore))
in (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())))
end))


let push_context : (FStar_Parser_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  (FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun _88_99 msg -> (match (_88_99) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_Env.push dsenv)
in (

let env = (FStar_TypeChecker_Env.push env msg)
in (dsenv, env)))
end))


let interactive_tc : ((FStar_Parser_Env.env * FStar_TypeChecker_Env.env), FStar_Syntax_Syntax.modul Prims.option) FStar_Interactive.interactive_tc = (

let pop = (fun _88_106 msg -> (match (_88_106) with
| (dsenv, env) -> begin
(

let _88_108 = (pop_context (dsenv, env) msg)
in (FStar_Options.pop ()))
end))
in (

let push = (fun _88_113 msg -> (match (_88_113) with
| (dsenv, env) -> begin
(

let res = (push_context (dsenv, env) msg)
in (

let _88_116 = (FStar_Options.push ())
in res))
end))
in (

let mark = (fun _88_121 -> (match (_88_121) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_Env.mark dsenv)
in (

let env = (FStar_TypeChecker_Env.mark env)
in (

let _88_124 = (FStar_Options.push ())
in (dsenv, env))))
end))
in (

let reset_mark = (fun _88_129 -> (match (_88_129) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_Env.reset_mark dsenv)
in (

let env = (FStar_TypeChecker_Env.reset_mark env)
in (

let _88_132 = (FStar_Options.pop ())
in (dsenv, env))))
end))
in (

let commit_mark = (fun _88_137 -> (match (_88_137) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_Env.commit_mark dsenv)
in (

let env = (FStar_TypeChecker_Env.commit_mark env)
in (dsenv, env)))
end))
in (

let check_frag = (fun _88_143 curmod text -> (match (_88_143) with
| (dsenv, env) -> begin
try
(match (()) with
| () -> begin
(match ((tc_one_fragment curmod dsenv env text)) with
| Some (m, dsenv, env) -> begin
(let _178_58 = (let _178_57 = (FStar_TypeChecker_Errors.get_err_count ())
in (m, (dsenv, env), _178_57))
in Some (_178_58))
end
| _88_167 -> begin
None
end)
end)
with
| FStar_Syntax_Syntax.Error (msg, r) when (not ((FStar_Options.trace_error ()))) -> begin
(

let _88_153 = (FStar_TypeChecker_Errors.add_errors env (((msg, r))::[]))
in None)
end
| FStar_Syntax_Syntax.Err (msg) when (not ((FStar_Options.trace_error ()))) -> begin
(

let _88_157 = (let _178_62 = (let _178_61 = (let _178_60 = (FStar_TypeChecker_Env.get_range env)
in (msg, _178_60))
in (_178_61)::[])
in (FStar_TypeChecker_Errors.add_errors env _178_62))
in None)
end
end))
in (

let report_fail = (fun _88_169 -> (match (()) with
| () -> begin
(

let _88_170 = (let _178_65 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _178_65 Prims.ignore))
in (FStar_ST.op_Colon_Equals FStar_TypeChecker_Errors.num_errs 0))
end))
in {FStar_Interactive.pop = pop; FStar_Interactive.push = push; FStar_Interactive.mark = mark; FStar_Interactive.reset_mark = reset_mark; FStar_Interactive.commit_mark = commit_mark; FStar_Interactive.check_frag = check_frag; FStar_Interactive.report_fail = report_fail})))))))


let tc_one_file : FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.option  ->  Prims.string  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env pre_fn fn -> (

let _88_178 = (parse dsenv pre_fn fn)
in (match (_88_178) with
| (dsenv, fmods) -> begin
(

let check_mods = (fun _88_180 -> (match (()) with
| () -> begin
(

let _88_190 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun _88_183 m -> (match (_88_183) with
| (env, all_mods) -> begin
(

let _88_187 = (FStar_TypeChecker_Tc.check_module env m)
in (match (_88_187) with
| (m, env) -> begin
(env, (m)::all_mods)
end))
end)) (env, [])))
in (match (_88_190) with
| (env, all_mods) -> begin
((FStar_List.rev all_mods), dsenv, env)
end))
end))
in (match (fmods) with
| (m)::[] when ((FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str) && ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))) -> begin
(FStar_SMTEncoding_Solver.with_hints_db fn check_mods)
end
| _88_194 -> begin
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

let _88_205 = (FStar_Syntax_Syntax.reset_gensym ())
in (

let _88_210 = acc
in (match (_88_210) with
| (all_mods, dsenv, env) -> begin
(

let _88_235 = (match (intf) with
| None -> begin
(tc_one_file dsenv env intf impl)
end
| Some (_88_213) when ((FStar_Options.codegen ()) <> None) -> begin
(

let _88_215 = if (not ((FStar_Options.lax ()))) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Verification and code generation are no supported together with partial modules (i.e, *.fsti); use --lax to extract code separately")))
end else begin
()
end
in (tc_one_file dsenv env intf impl))
end
| Some (iname) -> begin
(

let _88_219 = (FStar_Util.print1 "Interleaving iface+module: %s\n" iname)
in (

let caption = (Prims.strcat "interface: " iname)
in (

let _88_224 = (push_context (dsenv, env) caption)
in (match (_88_224) with
| (dsenv', env') -> begin
(

let _88_229 = (tc_one_file dsenv' env' intf impl)
in (match (_88_229) with
| (_88_226, dsenv', env') -> begin
(

let _88_230 = (pop_context (dsenv', env') caption)
in (tc_one_file dsenv env None iname))
end))
end))))
end)
in (match (_88_235) with
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

let _88_252 = (tc_fold_interleave ([], dsenv, env) filenames)
in (match (_88_252) with
| (all_mods, dsenv, env) -> begin
(

let _88_253 = if ((FStar_Options.interactive ()) && ((FStar_TypeChecker_Errors.get_err_count ()) = 0)) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end else begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end
in (all_mods, dsenv, env))
end)))


let batch_mode_tc : Prims.string Prims.list  ->  (FStar_Syntax_Syntax.modul Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun filenames -> (

let _88_259 = (tc_prims ())
in (match (_88_259) with
| (prims_mod, dsenv, env) -> begin
(

let filenames = (FStar_Dependences.find_deps_if_needed filenames)
in (

let _88_265 = if ((not ((FStar_Options.explicit_deps ()))) && (FStar_Options.debug_any ())) then begin
(

let _88_261 = (FStar_Util.print_endline "Auto-deps kicked in; here\'s some info.")
in (

let _88_263 = (FStar_Util.print1 "Here\'s the list of filenames we will process: %s\n" (FStar_String.concat " " filenames))
in (let _178_101 = (let _178_100 = (FStar_Options.verify_module ())
in (FStar_String.concat " " _178_100))
in (FStar_Util.print1 "Here\'s the list of modules we will verify: %s\n" _178_101))))
end else begin
()
end
in (

let _88_270 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (_88_270) with
| (all_mods, dsenv, env) -> begin
((prims_mod)::all_mods, dsenv, env)
end))))
end)))




