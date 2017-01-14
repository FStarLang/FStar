
open Prims

let module_or_interface_name : FStar_Syntax_Syntax.modul  ->  (Prims.bool * FStar_Ident.lident) = (fun m -> ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name)))


let parse : FStar_ToSyntax_Env.env  ->  Prims.string Prims.option  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env pre_fn fn -> (

let _98_8 = (FStar_Parser_Driver.parse_file fn)
in (match (_98_8) with
| (ast, _98_7) -> begin
(

let ast = (match (pre_fn) with
| None -> begin
ast
end
| Some (pre_fn) -> begin
(

let _98_15 = (FStar_Parser_Driver.parse_file pre_fn)
in (match (_98_15) with
| (pre_ast, _98_14) -> begin
(match (((pre_ast), (ast))) with
| ((FStar_Parser_AST.Interface (lid1, decls1, _98_19))::[], (FStar_Parser_AST.Module (lid2, decls2))::[]) when (FStar_Ident.lid_equals lid1 lid2) -> begin
(let _199_11 = (let _199_10 = (let _199_9 = (FStar_Parser_Interleave.interleave decls1 decls2)
in ((lid1), (_199_9)))
in FStar_Parser_AST.Module (_199_10))
in (_199_11)::[])
end
| _98_30 -> begin
(Prims.raise (FStar_Errors.Err ("mismatch between pre-module and module\n")))
end)
end))
end)
in (FStar_ToSyntax_ToSyntax.desugar_file env ast))
end)))


let tc_prims : Prims.unit  ->  ((FStar_Syntax_Syntax.modul * Prims.int) * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun _98_32 -> (match (()) with
| () -> begin
(

let solver = if (FStar_Options.lax ()) then begin
FStar_SMTEncoding_Solver.dummy
end else begin
FStar_SMTEncoding_Solver.solver
end
in (

let env = (FStar_TypeChecker_Env.initial_env FStar_TypeChecker_TcTerm.type_of_tot_term FStar_TypeChecker_TcTerm.universe_of solver FStar_Syntax_Const.prims_lid)
in (

let _98_35 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env)
in (

let prims_filename = (FStar_Options.prims ())
in (

let _98_40 = (let _199_14 = (FStar_ToSyntax_Env.empty_env ())
in (parse _199_14 None prims_filename))
in (match (_98_40) with
| (dsenv, prims_mod) -> begin
(

let _98_46 = (FStar_Util.record_time (fun _98_41 -> (match (()) with
| () -> begin
(let _199_16 = (FStar_List.hd prims_mod)
in (FStar_TypeChecker_Tc.check_module env _199_16))
end)))
in (match (_98_46) with
| ((prims_mod, env), elapsed_time) -> begin
((((prims_mod), (elapsed_time))), (dsenv), (env))
end))
end))))))
end))


let tc_one_fragment : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  FStar_Parser_ParseIt.input_frag  ->  (FStar_Syntax_Syntax.modul Prims.option * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) Prims.option = (fun curmod dsenv env frag -> try
(match (()) with
| () -> begin
(match ((FStar_Parser_Driver.parse_fragment frag)) with
| FStar_Parser_Driver.Empty -> begin
Some (((curmod), (dsenv), (env)))
end
| FStar_Parser_Driver.Modul (ast_modul) -> begin
(

let _98_70 = (FStar_ToSyntax_ToSyntax.desugar_partial_modul curmod dsenv ast_modul)
in (match (_98_70) with
| (dsenv, modul) -> begin
(

let env = (match (curmod) with
| None -> begin
env
end
| Some (_98_73) -> begin
(Prims.raise (FStar_Errors.Err ("Interactive mode only supports a single module at the top-level")))
end)
in (

let _98_80 = (FStar_TypeChecker_Tc.tc_partial_modul env modul)
in (match (_98_80) with
| (modul, _98_78, env) -> begin
Some (((Some (modul)), (dsenv), (env)))
end)))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(

let _98_85 = (FStar_ToSyntax_ToSyntax.desugar_decls dsenv ast_decls)
in (match (_98_85) with
| (dsenv, decls) -> begin
(match (curmod) with
| None -> begin
(

let _98_87 = (FStar_Util.print_error "fragment without an enclosing module")
in (FStar_All.exit (Prims.parse_int "1")))
end
| Some (modul) -> begin
(

let _98_95 = (FStar_TypeChecker_Tc.tc_more_partial_modul env modul decls)
in (match (_98_95) with
| (modul, _98_93, env) -> begin
Some (((Some (modul)), (dsenv), (env)))
end))
end)
end))
end)
end)
with
| FStar_Errors.Error (msg, r) when (not ((FStar_Options.trace_error ()))) -> begin
(

let _98_56 = (FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]))
in None)
end
| FStar_Errors.Err (msg) when (not ((FStar_Options.trace_error ()))) -> begin
(

let _98_60 = (FStar_TypeChecker_Err.add_errors env ((((msg), (FStar_Range.dummyRange)))::[]))
in None)
end
| e when (not ((FStar_Options.trace_error ()))) -> begin
(Prims.raise e)
end)


let tc_one_file : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.option  ->  Prims.string  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env pre_fn fn -> (

let _98_102 = (parse dsenv pre_fn fn)
in (match (_98_102) with
| (dsenv, fmods) -> begin
(

let check_mods = (fun _98_104 -> (match (()) with
| () -> begin
(

let _98_117 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun _98_107 m -> (match (_98_107) with
| (env, all_mods) -> begin
(

let _98_114 = (FStar_Util.record_time (fun _98_109 -> (match (()) with
| () -> begin
(FStar_TypeChecker_Tc.check_module env m)
end)))
in (match (_98_114) with
| ((m, env), elapsed_ms) -> begin
((env), ((((m), (elapsed_ms)))::all_mods))
end))
end)) ((env), ([]))))
in (match (_98_117) with
| (env, all_mods) -> begin
(((FStar_List.rev all_mods)), (dsenv), (env))
end))
end))
in (match (fmods) with
| (m)::[] when ((FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str) && ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))) -> begin
(FStar_SMTEncoding_Solver.with_hints_db fn check_mods)
end
| _98_121 -> begin
(check_mods ())
end))
end)))


let needs_interleaving : Prims.string  ->  Prims.string  ->  Prims.bool = (fun intf impl -> (

let m1 = (FStar_Parser_Dep.lowercase_module_name intf)
in (

let m2 = (FStar_Parser_Dep.lowercase_module_name impl)
in (((m1 = m2) && ((FStar_Util.get_file_extension intf) = "fsti")) && ((FStar_Util.get_file_extension impl) = "fst")))))


let pop_context : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  Prims.unit = (fun _98_128 msg -> (match (_98_128) with
| (dsenv, env) -> begin
(

let _98_130 = (let _199_48 = (FStar_ToSyntax_Env.pop dsenv)
in (FStar_All.pipe_right _199_48 Prims.ignore))
in (

let _98_132 = (let _199_49 = (FStar_TypeChecker_Env.pop env msg)
in (FStar_All.pipe_right _199_49 Prims.ignore))
in (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())))
end))


let push_context : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun _98_136 msg -> (match (_98_136) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_ToSyntax_Env.push dsenv)
in (

let env = (FStar_TypeChecker_Env.push env msg)
in ((dsenv), (env))))
end))


let tc_one_file_and_intf : Prims.string Prims.option  ->  Prims.string  ->  FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun intf impl dsenv env -> (

let _98_144 = (FStar_Syntax_Syntax.reset_gensym ())
in (match (intf) with
| None -> begin
(tc_one_file dsenv env None impl)
end
| Some (_98_148) when ((FStar_Options.codegen ()) <> None) -> begin
(

let _98_150 = if (not ((FStar_Options.lax ()))) then begin
(Prims.raise (FStar_Errors.Err ("Verification and code generation are no supported together with partial modules (i.e, *.fsti); use --lax to extract code separately")))
end else begin
()
end
in (tc_one_file dsenv env intf impl))
end
| Some (iname) -> begin
(

let _98_154 = if (FStar_Options.debug_any ()) then begin
(FStar_Util.print1 "Interleaving iface+module: %s\n" iname)
end else begin
()
end
in (

let caption = (Prims.strcat "interface: " iname)
in (

let _98_159 = (push_context ((dsenv), (env)) caption)
in (match (_98_159) with
| (dsenv', env') -> begin
(

let _98_164 = (tc_one_file dsenv' env' intf impl)
in (match (_98_164) with
| (_98_161, dsenv', env') -> begin
(

let _98_165 = (pop_context ((dsenv'), (env')) caption)
in (tc_one_file dsenv env None iname))
end))
end))))
end)))


type uenv =
(FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)


let tc_one_file_from_remaining : Prims.string Prims.list  ->  uenv  ->  (Prims.string Prims.list * (FStar_Syntax_Syntax.modul * Prims.int) Prims.list * (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)) = (fun remaining uenv -> (

let _98_171 = uenv
in (match (_98_171) with
| (dsenv, env) -> begin
(

let _98_186 = (match (remaining) with
| (intf)::(impl)::remaining when (needs_interleaving intf impl) -> begin
(let _199_66 = (tc_one_file_and_intf (Some (intf)) impl dsenv env)
in ((remaining), (_199_66)))
end
| (intf_or_impl)::remaining -> begin
(let _199_67 = (tc_one_file_and_intf None intf_or_impl dsenv env)
in ((remaining), (_199_67)))
end
| [] -> begin
(([]), ((([]), (dsenv), (env))))
end)
in (match (_98_186) with
| (remaining, (nmods, dsenv, env)) -> begin
((remaining), (nmods), (((dsenv), (env))))
end))
end)))


let rec tc_fold_interleave : ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * uenv)  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * uenv) = (fun acc remaining -> (match (remaining) with
| [] -> begin
acc
end
| _98_191 -> begin
(

let _98_194 = acc
in (match (_98_194) with
| (mods, uenv) -> begin
(

let _98_200 = (tc_one_file_from_remaining remaining uenv)
in (match (_98_200) with
| (remaining, nmods, (dsenv, env)) -> begin
(tc_fold_interleave (((FStar_List.append mods nmods)), (((dsenv), (env)))) remaining)
end))
end))
end))


let batch_mode_tc_no_prims : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env filenames -> (

let _98_208 = (tc_fold_interleave (([]), (((dsenv), (env)))) filenames)
in (match (_98_208) with
| (all_mods, (dsenv, env)) -> begin
(

let _98_209 = if ((FStar_Options.interactive ()) && ((FStar_Errors.get_err_count ()) = (Prims.parse_int "0"))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end else begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end
in ((all_mods), (dsenv), (env)))
end)))


let batch_mode_tc : Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun filenames -> (

let _98_215 = (tc_prims ())
in (match (_98_215) with
| (prims_mod, dsenv, env) -> begin
(

let _98_220 = if ((not ((FStar_Options.explicit_deps ()))) && (FStar_Options.debug_any ())) then begin
(

let _98_216 = (FStar_Util.print_endline "Auto-deps kicked in; here\'s some info.")
in (

let _98_218 = (FStar_Util.print1 "Here\'s the list of filenames we will process: %s\n" (FStar_String.concat " " filenames))
in (let _199_81 = (let _199_80 = (FStar_Options.verify_module ())
in (FStar_String.concat " " _199_80))
in (FStar_Util.print1 "Here\'s the list of modules we will verify: %s\n" _199_81))))
end else begin
()
end
in (

let _98_225 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (_98_225) with
| (all_mods, dsenv, env) -> begin
(((prims_mod)::all_mods), (dsenv), (env))
end)))
end)))


let tc_prims_interactive : Prims.unit  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun _98_226 -> (match (()) with
| () -> begin
(

let _98_231 = (tc_prims ())
in (match (_98_231) with
| (_98_228, dsenv, env) -> begin
((dsenv), (env))
end))
end))


let tc_one_file_interactive = (fun remaining uenv -> (

let _98_236 = uenv
in (match (_98_236) with
| (dsenv, env) -> begin
(

let _98_262 = (match (remaining) with
| (intf)::(impl)::remaining when (needs_interleaving intf impl) -> begin
(

let _98_246 = (tc_one_file_and_intf (Some (intf)) impl dsenv env)
in (match (_98_246) with
| (_98_243, dsenv, env) -> begin
((((Some (intf)), (impl))), (dsenv), (env), (remaining))
end))
end
| (intf_or_impl)::remaining -> begin
(

let _98_254 = (tc_one_file_and_intf None intf_or_impl dsenv env)
in (match (_98_254) with
| (_98_251, dsenv, env) -> begin
((((None), (intf_or_impl))), (dsenv), (env), (remaining))
end))
end
| [] -> begin
(failwith "Impossible")
end)
in (match (_98_262) with
| ((intf, impl), dsenv, env, remaining) -> begin
((((intf), (impl))), (((dsenv), (env))), (None), (remaining))
end))
end)))


let interactive_tc : ((FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env), FStar_Syntax_Syntax.modul Prims.option) FStar_Interactive.interactive_tc = (

let pop = (fun _98_266 msg -> (match (_98_266) with
| (dsenv, env) -> begin
(

let _98_268 = (pop_context ((dsenv), (env)) msg)
in (FStar_Options.pop ()))
end))
in (

let push = (fun _98_273 lax restore_cmd_line_options msg -> (match (_98_273) with
| (dsenv, env) -> begin
(

let env = (

let _98_277 = env
in {FStar_TypeChecker_Env.solver = _98_277.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _98_277.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _98_277.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _98_277.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _98_277.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _98_277.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _98_277.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _98_277.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _98_277.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _98_277.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _98_277.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _98_277.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _98_277.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _98_277.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _98_277.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _98_277.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _98_277.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _98_277.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = lax; FStar_TypeChecker_Env.lax_universes = _98_277.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _98_277.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _98_277.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _98_277.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _98_277.FStar_TypeChecker_Env.qname_and_index})
in (

let res = (push_context ((dsenv), (env)) msg)
in (

let _98_281 = (FStar_Options.push ())
in (

let _98_283 = if restore_cmd_line_options then begin
(let _199_98 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _199_98 Prims.ignore))
end else begin
()
end
in res))))
end))
in (

let mark = (fun _98_288 -> (match (_98_288) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_ToSyntax_Env.mark dsenv)
in (

let env = (FStar_TypeChecker_Env.mark env)
in (

let _98_291 = (FStar_Options.push ())
in ((dsenv), (env)))))
end))
in (

let reset_mark = (fun _98_296 -> (match (_98_296) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_ToSyntax_Env.reset_mark dsenv)
in (

let env = (FStar_TypeChecker_Env.reset_mark env)
in (

let _98_299 = (FStar_Options.pop ())
in ((dsenv), (env)))))
end))
in (

let cleanup = (fun _98_304 -> (match (_98_304) with
| (dsenv, env) -> begin
(FStar_TypeChecker_Env.cleanup_interactive env)
end))
in (

let commit_mark = (fun _98_308 -> (match (_98_308) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_ToSyntax_Env.commit_mark dsenv)
in (

let env = (FStar_TypeChecker_Env.commit_mark env)
in ((dsenv), (env))))
end))
in (

let check_frag = (fun _98_314 curmod text -> (match (_98_314) with
| (dsenv, env) -> begin
try
(match (()) with
| () -> begin
(match ((tc_one_fragment curmod dsenv env text)) with
| Some (m, dsenv, env) -> begin
(let _199_115 = (let _199_114 = (FStar_Errors.get_err_count ())
in ((m), (((dsenv), (env))), (_199_114)))
in Some (_199_115))
end
| _98_336 -> begin
None
end)
end)
with
| FStar_Errors.Error (msg, r) when (not ((FStar_Options.trace_error ()))) -> begin
(

let _98_322 = (FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]))
in None)
end
| FStar_Errors.Err (msg) when (not ((FStar_Options.trace_error ()))) -> begin
(

let _98_326 = (let _199_119 = (let _199_118 = (let _199_117 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (_199_117)))
in (_199_118)::[])
in (FStar_TypeChecker_Err.add_errors env _199_119))
in None)
end
end))
in (

let report_fail = (fun _98_338 -> (match (()) with
| () -> begin
(

let _98_339 = (let _199_122 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right _199_122 Prims.ignore))
in (FStar_ST.op_Colon_Equals FStar_Errors.num_errs (Prims.parse_int "0")))
end))
in {FStar_Interactive.pop = pop; FStar_Interactive.push = push; FStar_Interactive.mark = mark; FStar_Interactive.reset_mark = reset_mark; FStar_Interactive.commit_mark = commit_mark; FStar_Interactive.check_frag = check_frag; FStar_Interactive.report_fail = report_fail; FStar_Interactive.tc_prims = tc_prims_interactive; FStar_Interactive.tc_one_file = tc_one_file_interactive; FStar_Interactive.cleanup = cleanup}))))))))




