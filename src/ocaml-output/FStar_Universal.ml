
open Prims

let module_or_interface_name : FStar_Syntax_Syntax.modul  ->  (Prims.bool * FStar_Ident.lident) = (fun m -> ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name)))


let parse : FStar_Parser_Env.env  ->  Prims.string Prims.option  ->  Prims.string  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env pre_fn fn -> (

let _96_8 = (FStar_Parser_Driver.parse_file fn)
in (match (_96_8) with
| (ast, _96_7) -> begin
(

let ast = (match (pre_fn) with
| None -> begin
ast
end
| Some (pre_fn) -> begin
(

let _96_15 = (FStar_Parser_Driver.parse_file pre_fn)
in (match (_96_15) with
| (pre_ast, _96_14) -> begin
(match (((pre_ast), (ast))) with
| ((FStar_Parser_AST.Interface (lid1, decls1, _96_19))::[], (FStar_Parser_AST.Module (lid2, decls2))::[]) when (FStar_Ident.lid_equals lid1 lid2) -> begin
(let _195_11 = (let _195_10 = (let _195_9 = (FStar_Parser_Interleave.interleave decls1 decls2)
in ((lid1), (_195_9)))
in FStar_Parser_AST.Module (_195_10))
in (_195_11)::[])
end
| _96_30 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("mismatch between pre-module and module\n")))
end)
end))
end)
in (FStar_Parser_ToSyntax.desugar_file env ast))
end)))


let tc_prims : Prims.unit  ->  ((FStar_Syntax_Syntax.modul * Prims.int) * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun _96_32 -> (match (()) with
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

let _96_35 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env)
in (

let prims_filename = (FStar_Options.prims ())
in (

let _96_40 = (let _195_14 = (FStar_Parser_Env.empty_env ())
in (parse _195_14 None prims_filename))
in (match (_96_40) with
| (dsenv, prims_mod) -> begin
(

let _96_46 = (FStar_Util.record_time (fun _96_41 -> (match (()) with
| () -> begin
(let _195_16 = (FStar_List.hd prims_mod)
in (FStar_TypeChecker_Tc.check_module env _195_16))
end)))
in (match (_96_46) with
| ((prims_mod, env), elapsed_time) -> begin
((((prims_mod), (elapsed_time))), (dsenv), (env))
end))
end))))))
end))


let tc_one_fragment : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  FStar_Parser_ParseIt.input_frag  ->  (FStar_Syntax_Syntax.modul Prims.option * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) Prims.option = (fun curmod dsenv env frag -> try
(match (()) with
| () -> begin
(match ((FStar_Parser_Driver.parse_fragment frag)) with
| FStar_Parser_Driver.Empty -> begin
Some (((curmod), (dsenv), (env)))
end
| FStar_Parser_Driver.Modul (ast_modul) -> begin
(

let _96_72 = (FStar_Parser_ToSyntax.desugar_partial_modul curmod dsenv ast_modul)
in (match (_96_72) with
| (dsenv, modul) -> begin
(

let env = (match (curmod) with
| Some (modul) -> begin
if ((let _195_27 = (let _195_26 = (FStar_Options.file_list ())
in (FStar_List.hd _195_26))
in (FStar_Parser_Dep.lowercase_module_name _195_27)) <> (let _195_28 = (FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name)
in (FStar_String.lowercase _195_28))) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Interactive mode only supports a single module at the top-level")))
end else begin
env
end
end
| None -> begin
env
end)
in (

let _96_81 = (FStar_TypeChecker_Tc.tc_partial_modul env modul)
in (match (_96_81) with
| (modul, _96_79, env) -> begin
Some (((Some (modul)), (dsenv), (env)))
end)))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(

let _96_86 = (FStar_Parser_ToSyntax.desugar_decls dsenv ast_decls)
in (match (_96_86) with
| (dsenv, decls) -> begin
(match (curmod) with
| None -> begin
(

let _96_88 = (FStar_Util.print_error "fragment without an enclosing module")
in (FStar_All.exit (Prims.parse_int "1")))
end
| Some (modul) -> begin
(

let _96_96 = (FStar_TypeChecker_Tc.tc_more_partial_modul env modul decls)
in (match (_96_96) with
| (modul, _96_94, env) -> begin
Some (((Some (modul)), (dsenv), (env)))
end))
end)
end))
end)
end)
with
| FStar_Syntax_Syntax.Error (msg, r) when (not ((FStar_Options.trace_error ()))) -> begin
(

let _96_58 = (FStar_TypeChecker_Errors.add_errors env ((((msg), (r)))::[]))
in None)
end
| FStar_Syntax_Syntax.Err (msg) when (not ((FStar_Options.trace_error ()))) -> begin
(

let _96_62 = (FStar_TypeChecker_Errors.add_errors env ((((msg), (FStar_Range.dummyRange)))::[]))
in None)
end
| e when (not ((FStar_Options.trace_error ()))) -> begin
(Prims.raise e)
end)


let tc_one_file : FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.option  ->  Prims.string  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env pre_fn fn -> (

let _96_103 = (parse dsenv pre_fn fn)
in (match (_96_103) with
| (dsenv, fmods) -> begin
(

let check_mods = (fun _96_105 -> (match (()) with
| () -> begin
(

let _96_118 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun _96_108 m -> (match (_96_108) with
| (env, all_mods) -> begin
(

let _96_115 = (FStar_Util.record_time (fun _96_110 -> (match (()) with
| () -> begin
(FStar_TypeChecker_Tc.check_module env m)
end)))
in (match (_96_115) with
| ((m, env), elapsed_ms) -> begin
((env), ((((m), (elapsed_ms)))::all_mods))
end))
end)) ((env), ([]))))
in (match (_96_118) with
| (env, all_mods) -> begin
(((FStar_List.rev all_mods)), (dsenv), (env))
end))
end))
in (match (fmods) with
| (m)::[] when ((FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str) && ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))) -> begin
(FStar_SMTEncoding_Solver.with_hints_db fn check_mods)
end
| _96_122 -> begin
(check_mods ())
end))
end)))


let needs_interleaving : Prims.string  ->  Prims.string  ->  Prims.bool = (fun intf impl -> (

let m1 = (FStar_Parser_Dep.lowercase_module_name intf)
in (

let m2 = (FStar_Parser_Dep.lowercase_module_name impl)
in (((m1 = m2) && ((FStar_Util.get_file_extension intf) = "fsti")) && ((FStar_Util.get_file_extension impl) = "fst")))))


let pop_context : (FStar_Parser_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  Prims.unit = (fun _96_129 msg -> (match (_96_129) with
| (dsenv, env) -> begin
(

let _96_131 = (let _195_51 = (FStar_Parser_Env.pop dsenv)
in (FStar_All.pipe_right _195_51 Prims.ignore))
in (

let _96_133 = (let _195_52 = (FStar_TypeChecker_Env.pop env msg)
in (FStar_All.pipe_right _195_52 Prims.ignore))
in (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())))
end))


let push_context : (FStar_Parser_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  (FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun _96_137 msg -> (match (_96_137) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_Env.push dsenv)
in (

let env = (FStar_TypeChecker_Env.push env msg)
in ((dsenv), (env))))
end))


let tc_one_file_and_intf : Prims.string Prims.option  ->  Prims.string  ->  FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun intf impl dsenv env -> (

let _96_145 = (FStar_Syntax_Syntax.reset_gensym ())
in (match (intf) with
| None -> begin
(tc_one_file dsenv env None impl)
end
| Some (_96_149) when ((FStar_Options.codegen ()) <> None) -> begin
(

let _96_151 = if (not ((FStar_Options.lax ()))) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Verification and code generation are no supported together with partial modules (i.e, *.fsti); use --lax to extract code separately")))
end else begin
()
end
in (tc_one_file dsenv env intf impl))
end
| Some (iname) -> begin
(

let _96_155 = if (FStar_Options.debug_any ()) then begin
(FStar_Util.print1 "Interleaving iface+module: %s\n" iname)
end else begin
()
end
in (

let caption = (Prims.strcat "interface: " iname)
in (

let _96_160 = (push_context ((dsenv), (env)) caption)
in (match (_96_160) with
| (dsenv', env') -> begin
(

let _96_165 = (tc_one_file dsenv' env' intf impl)
in (match (_96_165) with
| (_96_162, dsenv', env') -> begin
(

let _96_166 = (pop_context ((dsenv'), (env')) caption)
in (tc_one_file dsenv env None iname))
end))
end))))
end)))


type uenv =
(FStar_Parser_Env.env * FStar_TypeChecker_Env.env)


let tc_one_file_from_remaining : Prims.string Prims.list  ->  uenv  ->  (Prims.string Prims.list * (FStar_Syntax_Syntax.modul * Prims.int) Prims.list * (FStar_Parser_Env.env * FStar_TypeChecker_Env.env)) = (fun remaining uenv -> (

let _96_172 = uenv
in (match (_96_172) with
| (dsenv, env) -> begin
(

let _96_187 = (match (remaining) with
| (intf)::(impl)::remaining when (needs_interleaving intf impl) -> begin
(let _195_69 = (tc_one_file_and_intf (Some (intf)) impl dsenv env)
in ((remaining), (_195_69)))
end
| (intf_or_impl)::remaining -> begin
(let _195_70 = (tc_one_file_and_intf None intf_or_impl dsenv env)
in ((remaining), (_195_70)))
end
| [] -> begin
(([]), ((([]), (dsenv), (env))))
end)
in (match (_96_187) with
| (remaining, (nmods, dsenv, env)) -> begin
((remaining), (nmods), (((dsenv), (env))))
end))
end)))


let rec tc_fold_interleave : ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * uenv)  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * uenv) = (fun acc remaining -> (match (remaining) with
| [] -> begin
acc
end
| _96_192 -> begin
(

let _96_195 = acc
in (match (_96_195) with
| (mods, uenv) -> begin
(

let _96_201 = (tc_one_file_from_remaining remaining uenv)
in (match (_96_201) with
| (remaining, nmods, (dsenv, env)) -> begin
(tc_fold_interleave (((FStar_List.append mods nmods)), (((dsenv), (env)))) remaining)
end))
end))
end))


let batch_mode_tc_no_prims : FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env filenames -> (

let _96_209 = (tc_fold_interleave (([]), (((dsenv), (env)))) filenames)
in (match (_96_209) with
| (all_mods, (dsenv, env)) -> begin
(

let _96_210 = if ((FStar_Options.interactive ()) && ((FStar_TypeChecker_Errors.get_err_count ()) = (Prims.parse_int "0"))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end else begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end
in ((all_mods), (dsenv), (env)))
end)))


let batch_mode_tc : Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun filenames -> (

let _96_216 = (tc_prims ())
in (match (_96_216) with
| (prims_mod, dsenv, env) -> begin
(

let _96_221 = if ((not ((FStar_Options.explicit_deps ()))) && (FStar_Options.debug_any ())) then begin
(

let _96_217 = (FStar_Util.print_endline "Auto-deps kicked in; here\'s some info.")
in (

let _96_219 = (FStar_Util.print1 "Here\'s the list of filenames we will process: %s\n" (FStar_String.concat " " filenames))
in (let _195_84 = (let _195_83 = (FStar_Options.verify_module ())
in (FStar_String.concat " " _195_83))
in (FStar_Util.print1 "Here\'s the list of modules we will verify: %s\n" _195_84))))
end else begin
()
end
in (

let _96_226 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (_96_226) with
| (all_mods, dsenv, env) -> begin
(((prims_mod)::all_mods), (dsenv), (env))
end)))
end)))


let tc_prims_interactive : Prims.unit  ->  (FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun _96_227 -> (match (()) with
| () -> begin
(

let _96_232 = (tc_prims ())
in (match (_96_232) with
| (_96_229, dsenv, env) -> begin
((dsenv), (env))
end))
end))


let tc_one_file_interactive = (fun remaining uenv -> (

let _96_237 = uenv
in (match (_96_237) with
| (dsenv, env) -> begin
(

let _96_263 = (match (remaining) with
| (intf)::(impl)::remaining when (needs_interleaving intf impl) -> begin
(

let _96_247 = (tc_one_file_and_intf (Some (intf)) impl dsenv env)
in (match (_96_247) with
| (_96_244, dsenv, env) -> begin
((((Some (intf)), (impl))), (dsenv), (env), (remaining))
end))
end
| (intf_or_impl)::remaining -> begin
(

let _96_255 = (tc_one_file_and_intf None intf_or_impl dsenv env)
in (match (_96_255) with
| (_96_252, dsenv, env) -> begin
((((None), (intf_or_impl))), (dsenv), (env), (remaining))
end))
end
| [] -> begin
(failwith "Impossible")
end)
in (match (_96_263) with
| ((intf, impl), dsenv, env, remaining) -> begin
((((intf), (impl))), (((dsenv), (env))), (None), (remaining))
end))
end)))


let interactive_tc : ((FStar_Parser_Env.env * FStar_TypeChecker_Env.env), FStar_Syntax_Syntax.modul Prims.option) FStar_Interactive.interactive_tc = (

let pop = (fun _96_267 msg -> (match (_96_267) with
| (dsenv, env) -> begin
(

let _96_269 = (pop_context ((dsenv), (env)) msg)
in (FStar_Options.pop ()))
end))
in (

let push = (fun _96_274 lax restore_cmd_line_options msg -> (match (_96_274) with
| (dsenv, env) -> begin
(

let env = (

let _96_278 = env
in {FStar_TypeChecker_Env.solver = _96_278.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _96_278.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _96_278.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _96_278.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _96_278.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _96_278.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _96_278.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _96_278.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _96_278.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _96_278.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _96_278.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _96_278.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _96_278.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _96_278.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _96_278.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _96_278.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _96_278.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _96_278.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = lax; FStar_TypeChecker_Env.lax_universes = _96_278.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _96_278.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _96_278.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _96_278.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _96_278.FStar_TypeChecker_Env.qname_and_index})
in (

let res = (push_context ((dsenv), (env)) msg)
in (

let _96_282 = (FStar_Options.push ())
in (

let _96_284 = if restore_cmd_line_options then begin
(let _195_101 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _195_101 Prims.ignore))
end else begin
()
end
in res))))
end))
in (

let mark = (fun _96_289 -> (match (_96_289) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_Env.mark dsenv)
in (

let env = (FStar_TypeChecker_Env.mark env)
in (

let _96_292 = (FStar_Options.push ())
in ((dsenv), (env)))))
end))
in (

let reset_mark = (fun _96_297 -> (match (_96_297) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_Env.reset_mark dsenv)
in (

let env = (FStar_TypeChecker_Env.reset_mark env)
in (

let _96_300 = (FStar_Options.pop ())
in ((dsenv), (env)))))
end))
in (

let cleanup = (fun _96_305 -> (match (_96_305) with
| (dsenv, env) -> begin
(FStar_TypeChecker_Env.cleanup_interactive env)
end))
in (

let commit_mark = (fun _96_309 -> (match (_96_309) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_Env.commit_mark dsenv)
in (

let env = (FStar_TypeChecker_Env.commit_mark env)
in ((dsenv), (env))))
end))
in (

let check_frag = (fun _96_315 curmod text -> (match (_96_315) with
| (dsenv, env) -> begin
try
(match (()) with
| () -> begin
(match ((tc_one_fragment curmod dsenv env text)) with
| Some (m, dsenv, env) -> begin
(let _195_118 = (let _195_117 = (FStar_TypeChecker_Errors.get_err_count ())
in ((m), (((dsenv), (env))), (_195_117)))
in Some (_195_118))
end
| _96_339 -> begin
None
end)
end)
with
| FStar_Syntax_Syntax.Error (msg, r) when (not ((FStar_Options.trace_error ()))) -> begin
(

let _96_325 = (FStar_TypeChecker_Errors.add_errors env ((((msg), (r)))::[]))
in None)
end
| FStar_Syntax_Syntax.Err (msg) when (not ((FStar_Options.trace_error ()))) -> begin
(

let _96_329 = (let _195_122 = (let _195_121 = (let _195_120 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (_195_120)))
in (_195_121)::[])
in (FStar_TypeChecker_Errors.add_errors env _195_122))
in None)
end
end))
in (

let report_fail = (fun _96_341 -> (match (()) with
| () -> begin
(

let _96_342 = (let _195_125 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _195_125 Prims.ignore))
in (FStar_ST.op_Colon_Equals FStar_TypeChecker_Errors.num_errs (Prims.parse_int "0")))
end))
in {FStar_Interactive.pop = pop; FStar_Interactive.push = push; FStar_Interactive.mark = mark; FStar_Interactive.reset_mark = reset_mark; FStar_Interactive.commit_mark = commit_mark; FStar_Interactive.check_frag = check_frag; FStar_Interactive.report_fail = report_fail; FStar_Interactive.tc_prims = tc_prims_interactive; FStar_Interactive.tc_one_file = tc_one_file_interactive; FStar_Interactive.cleanup = cleanup}))))))))




