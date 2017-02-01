
open Prims

let module_or_interface_name : FStar_Syntax_Syntax.modul  ->  (Prims.bool * FStar_Ident.lident) = (fun m -> ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name)))


let parse : FStar_ToSyntax_Env.env  ->  Prims.string Prims.option  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env pre_fn fn -> (

let uu____23 = (FStar_Parser_Driver.parse_file fn)
in (match (uu____23) with
| (ast, uu____33) -> begin
(

let ast = (match (pre_fn) with
| None -> begin
ast
end
| Some (pre_fn) -> begin
(

let uu____42 = (FStar_Parser_Driver.parse_file pre_fn)
in (match (uu____42) with
| (pre_ast, uu____49) -> begin
(match (((pre_ast), (ast))) with
| ((FStar_Parser_AST.Interface (lid1, decls1, uu____58))::[], (FStar_Parser_AST.Module (lid2, decls2))::[]) when (FStar_Ident.lid_equals lid1 lid2) -> begin
(

let uu____67 = (

let uu____68 = (

let uu____72 = (FStar_Parser_Interleave.interleave decls1 decls2)
in ((lid1), (uu____72)))
in FStar_Parser_AST.Module (uu____68))
in (uu____67)::[])
end
| uu____75 -> begin
(Prims.raise (FStar_Errors.Err ("mismatch between pre-module and module\n")))
end)
end))
end)
in (FStar_ToSyntax_ToSyntax.desugar_file env ast))
end)))


let tc_prims : Prims.unit  ->  ((FStar_Syntax_Syntax.modul * Prims.int) * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____85 -> (

let solver = (

let uu____92 = (FStar_Options.lax ())
in (match (uu____92) with
| true -> begin
FStar_SMTEncoding_Solver.dummy
end
| uu____93 -> begin
FStar_SMTEncoding_Solver.solver
end))
in (

let env = (FStar_TypeChecker_Env.initial_env FStar_TypeChecker_TcTerm.type_of_tot_term FStar_TypeChecker_TcTerm.universe_of solver FStar_Syntax_Const.prims_lid)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env);
(

let prims_filename = (FStar_Options.prims ())
in (

let uu____97 = (

let uu____101 = (FStar_ToSyntax_Env.empty_env ())
in (parse uu____101 None prims_filename))
in (match (uu____97) with
| (dsenv, prims_mod) -> begin
(

let uu____111 = (FStar_Util.record_time (fun uu____118 -> (

let uu____119 = (FStar_List.hd prims_mod)
in (FStar_TypeChecker_Tc.check_module env uu____119))))
in (match (uu____111) with
| ((prims_mod, env), elapsed_time) -> begin
((((prims_mod), (elapsed_time))), (dsenv), (env))
end))
end)));
))))


let tc_one_fragment : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  FStar_Parser_ParseIt.input_frag  ->  (FStar_Syntax_Syntax.modul Prims.option * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) Prims.option = (fun curmod dsenv env frag -> try
(match (()) with
| () -> begin
(

let uu____162 = (FStar_Parser_Driver.parse_fragment frag)
in (match (uu____162) with
| FStar_Parser_Driver.Empty -> begin
Some (((curmod), (dsenv), (env)))
end
| FStar_Parser_Driver.Modul (ast_modul) -> begin
(

let uu____174 = (FStar_ToSyntax_ToSyntax.desugar_partial_modul curmod dsenv ast_modul)
in (match (uu____174) with
| (dsenv, modul) -> begin
(

let env = (match (curmod) with
| None -> begin
env
end
| Some (uu____185) -> begin
(Prims.raise (FStar_Errors.Err ("Interactive mode only supports a single module at the top-level")))
end)
in (

let uu____186 = (FStar_TypeChecker_Tc.tc_partial_modul env modul)
in (match (uu____186) with
| (modul, uu____197, env) -> begin
Some (((Some (modul)), (dsenv), (env)))
end)))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(

let uu____208 = (FStar_ToSyntax_ToSyntax.desugar_decls dsenv ast_decls)
in (match (uu____208) with
| (dsenv, decls) -> begin
(match (curmod) with
| None -> begin
((FStar_Util.print_error "fragment without an enclosing module");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| Some (modul) -> begin
(

let uu____230 = (FStar_TypeChecker_Tc.tc_more_partial_modul env modul decls)
in (match (uu____230) with
| (modul, uu____241, env) -> begin
Some (((Some (modul)), (dsenv), (env)))
end))
end)
end))
end))
end)
with
| FStar_Errors.Error (msg, r) when (

let uu____258 = (FStar_Options.trace_error ())
in (not (uu____258))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]));
None;
)
end
| FStar_Errors.Err (msg) when (

let uu____269 = (FStar_Options.trace_error ())
in (not (uu____269))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (FStar_Range.dummyRange)))::[]));
None;
)
end
| e when (

let uu____280 = (FStar_Options.trace_error ())
in (not (uu____280))) -> begin
(Prims.raise e)
end)


let tc_one_file : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.option  ->  Prims.string  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env pre_fn fn -> (

let uu____312 = (parse dsenv pre_fn fn)
in (match (uu____312) with
| (dsenv, fmods) -> begin
(

let check_mods = (fun uu____335 -> (

let uu____336 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun uu____353 m -> (match (uu____353) with
| (env, all_mods) -> begin
(

let uu____373 = (FStar_Util.record_time (fun uu____380 -> (FStar_TypeChecker_Tc.check_module env m)))
in (match (uu____373) with
| ((m, env), elapsed_ms) -> begin
((env), ((((m), (elapsed_ms)))::all_mods))
end))
end)) ((env), ([]))))
in (match (uu____336) with
| (env, all_mods) -> begin
(((FStar_List.rev all_mods)), (dsenv), (env))
end)))
in (match (fmods) with
| (m)::[] when ((FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str) && ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))) -> begin
(FStar_SMTEncoding_Solver.with_hints_db fn check_mods)
end
| uu____433 -> begin
(check_mods ())
end))
end)))


let needs_interleaving : Prims.string  ->  Prims.string  ->  Prims.bool = (fun intf impl -> (

let m1 = (FStar_Parser_Dep.lowercase_module_name intf)
in (

let m2 = (FStar_Parser_Dep.lowercase_module_name impl)
in (((m1 = m2) && (

let uu____443 = (FStar_Util.get_file_extension intf)
in (uu____443 = "fsti"))) && (

let uu____444 = (FStar_Util.get_file_extension impl)
in (uu____444 = "fst"))))))


let pop_context : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  Prims.unit = (fun uu____451 msg -> (match (uu____451) with
| (dsenv, env) -> begin
((

let uu____458 = (FStar_ToSyntax_Env.pop dsenv)
in (FStar_All.pipe_right uu____458 Prims.ignore));
(

let uu____460 = (FStar_TypeChecker_Env.pop env msg)
in (FStar_All.pipe_right uu____460 Prims.ignore));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
)
end))


let push_context : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____469 msg -> (match (uu____469) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_ToSyntax_Env.push dsenv)
in (

let env = (FStar_TypeChecker_Env.push env msg)
in ((dsenv), (env))))
end))


let tc_one_file_and_intf : Prims.string Prims.option  ->  Prims.string  ->  FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun intf impl dsenv env -> ((FStar_Syntax_Syntax.reset_gensym ());
(match (intf) with
| None -> begin
(tc_one_file dsenv env None impl)
end
| Some (uu____506) when (

let uu____507 = (FStar_Options.codegen ())
in (uu____507 <> None)) -> begin
((

let uu____511 = (

let uu____512 = (FStar_Options.lax ())
in (not (uu____512)))
in (match (uu____511) with
| true -> begin
(Prims.raise (FStar_Errors.Err ("Verification and code generation are no supported together with partial modules (i.e, *.fsti); use --lax to extract code separately")))
end
| uu____513 -> begin
()
end));
(tc_one_file dsenv env intf impl);
)
end
| Some (iname) -> begin
((

let uu____516 = (FStar_Options.debug_any ())
in (match (uu____516) with
| true -> begin
(FStar_Util.print1 "Interleaving iface+module: %s\n" iname)
end
| uu____517 -> begin
()
end));
(

let caption = (Prims.strcat "interface: " iname)
in (

let uu____519 = (push_context ((dsenv), (env)) caption)
in (match (uu____519) with
| (dsenv', env') -> begin
(

let uu____530 = (tc_one_file dsenv' env' intf impl)
in (match (uu____530) with
| (uu____543, dsenv', env') -> begin
((pop_context ((dsenv'), (env')) caption);
(tc_one_file dsenv env None iname);
)
end))
end)));
)
end);
))


type uenv =
(FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)


let tc_one_file_from_remaining : Prims.string Prims.list  ->  uenv  ->  (Prims.string Prims.list * (FStar_Syntax_Syntax.modul * Prims.int) Prims.list * (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)) = (fun remaining uenv -> (

let uu____572 = uenv
in (match (uu____572) with
| (dsenv, env) -> begin
(

let uu____584 = (match (remaining) with
| (intf)::(impl)::remaining when (needs_interleaving intf impl) -> begin
(

let uu____607 = (tc_one_file_and_intf (Some (intf)) impl dsenv env)
in ((remaining), (uu____607)))
end
| (intf_or_impl)::remaining -> begin
(

let uu____624 = (tc_one_file_and_intf None intf_or_impl dsenv env)
in ((remaining), (uu____624)))
end
| [] -> begin
(([]), ((([]), (dsenv), (env))))
end)
in (match (uu____584) with
| (remaining, (nmods, dsenv, env)) -> begin
((remaining), (nmods), (((dsenv), (env))))
end))
end)))


let rec tc_fold_interleave : ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * uenv)  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * uenv) = (fun acc remaining -> (match (remaining) with
| [] -> begin
acc
end
| uu____711 -> begin
(

let uu____713 = acc
in (match (uu____713) with
| (mods, uenv) -> begin
(

let uu____732 = (tc_one_file_from_remaining remaining uenv)
in (match (uu____732) with
| (remaining, nmods, (dsenv, env)) -> begin
(tc_fold_interleave (((FStar_List.append mods nmods)), (((dsenv), (env)))) remaining)
end))
end))
end))


let batch_mode_tc_no_prims : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env filenames -> (

let uu____785 = (tc_fold_interleave (([]), (((dsenv), (env)))) filenames)
in (match (uu____785) with
| (all_mods, (dsenv, env)) -> begin
((

let uu____816 = ((FStar_Options.interactive ()) && (

let uu____817 = (FStar_Errors.get_err_count ())
in (uu____817 = (Prims.parse_int "0"))))
in (match (uu____816) with
| true -> begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end
| uu____818 -> begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end));
((all_mods), (dsenv), (env));
)
end)))


let batch_mode_tc : Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun filenames -> (

let uu____833 = (tc_prims ())
in (match (uu____833) with
| (prims_mod, dsenv, env) -> begin
((

let uu____853 = ((

let uu____854 = (FStar_Options.explicit_deps ())
in (not (uu____854))) && (FStar_Options.debug_any ()))
in (match (uu____853) with
| true -> begin
((FStar_Util.print_endline "Auto-deps kicked in; here\'s some info.");
(FStar_Util.print1 "Here\'s the list of filenames we will process: %s\n" (FStar_String.concat " " filenames));
(

let uu____857 = (

let uu____858 = (FStar_Options.verify_module ())
in (FStar_String.concat " " uu____858))
in (FStar_Util.print1 "Here\'s the list of modules we will verify: %s\n" uu____857));
)
end
| uu____860 -> begin
()
end));
(

let uu____861 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (uu____861) with
| (all_mods, dsenv, env) -> begin
(((prims_mod)::all_mods), (dsenv), (env))
end));
)
end)))


let tc_prims_interactive : Prims.unit  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____892 -> (

let uu____893 = (tc_prims ())
in (match (uu____893) with
| (uu____901, dsenv, env) -> begin
((dsenv), (env))
end)))


let tc_one_file_interactive = (fun remaining uenv -> (

let uu____933 = uenv
in (match (uu____933) with
| (dsenv, env) -> begin
(

let uu____947 = (match (remaining) with
| (intf)::(impl)::remaining when (needs_interleaving intf impl) -> begin
(

let uu____968 = (tc_one_file_and_intf (Some (intf)) impl dsenv env)
in (match (uu____968) with
| (uu____983, dsenv, env) -> begin
((((Some (intf)), (impl))), (dsenv), (env), (remaining))
end))
end
| (intf_or_impl)::remaining -> begin
(

let uu____1000 = (tc_one_file_and_intf None intf_or_impl dsenv env)
in (match (uu____1000) with
| (uu____1015, dsenv, env) -> begin
((((None), (intf_or_impl))), (dsenv), (env), (remaining))
end))
end
| [] -> begin
(failwith "Impossible")
end)
in (match (uu____947) with
| ((intf, impl), dsenv, env, remaining) -> begin
((((intf), (impl))), (((dsenv), (env))), (None), (remaining))
end))
end)))


let interactive_tc : ((FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env), FStar_Syntax_Syntax.modul Prims.option) FStar_Interactive.interactive_tc = (

let pop = (fun uu____1080 msg -> (match (uu____1080) with
| (dsenv, env) -> begin
((pop_context ((dsenv), (env)) msg);
(FStar_Options.pop ());
)
end))
in (

let push = (fun uu____1100 lax restore_cmd_line_options msg -> (match (uu____1100) with
| (dsenv, env) -> begin
(

let env = (

let uu___163_1111 = env
in {FStar_TypeChecker_Env.solver = uu___163_1111.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___163_1111.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___163_1111.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___163_1111.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___163_1111.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___163_1111.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___163_1111.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___163_1111.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___163_1111.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___163_1111.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___163_1111.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___163_1111.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___163_1111.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___163_1111.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___163_1111.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___163_1111.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___163_1111.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___163_1111.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = lax; FStar_TypeChecker_Env.lax_universes = uu___163_1111.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___163_1111.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___163_1111.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___163_1111.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___163_1111.FStar_TypeChecker_Env.qname_and_index})
in (

let res = (push_context ((dsenv), (env)) msg)
in ((FStar_Options.push ());
(match (restore_cmd_line_options) with
| true -> begin
(

let uu____1117 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____1117 Prims.ignore))
end
| uu____1118 -> begin
()
end);
res;
)))
end))
in (

let mark = (fun uu____1126 -> (match (uu____1126) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_ToSyntax_Env.mark dsenv)
in (

let env = (FStar_TypeChecker_Env.mark env)
in ((FStar_Options.push ());
((dsenv), (env));
)))
end))
in (

let reset_mark = (fun uu____1143 -> (match (uu____1143) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_ToSyntax_Env.reset_mark dsenv)
in (

let env = (FStar_TypeChecker_Env.reset_mark env)
in ((FStar_Options.pop ());
((dsenv), (env));
)))
end))
in (

let cleanup = (fun uu____1158 -> (match (uu____1158) with
| (dsenv, env) -> begin
(FStar_TypeChecker_Env.cleanup_interactive env)
end))
in (

let commit_mark = (fun uu____1170 -> (match (uu____1170) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_ToSyntax_Env.commit_mark dsenv)
in (

let env = (FStar_TypeChecker_Env.commit_mark env)
in ((dsenv), (env))))
end))
in (

let check_frag = (fun uu____1196 curmod text -> (match (uu____1196) with
| (dsenv, env) -> begin
try
(match (()) with
| () -> begin
(

let uu____1226 = (tc_one_fragment curmod dsenv env text)
in (match (uu____1226) with
| Some (m, dsenv, env) -> begin
(

let uu____1248 = (

let uu____1255 = (FStar_Errors.get_err_count ())
in ((m), (((dsenv), (env))), (uu____1255)))
in Some (uu____1248))
end
| uu____1265 -> begin
None
end))
end)
with
| FStar_Errors.Error (msg, r) when (

let uu____1287 = (FStar_Options.trace_error ())
in (not (uu____1287))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]));
None;
)
end
| FStar_Errors.Err (msg) when (

let uu____1300 = (FStar_Options.trace_error ())
in (not (uu____1300))) -> begin
((

let uu____1302 = (

let uu____1306 = (

let uu____1309 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (uu____1309)))
in (uu____1306)::[])
in (FStar_TypeChecker_Err.add_errors env uu____1302));
None;
)
end
end))
in (

let report_fail = (fun uu____1323 -> ((

let uu____1325 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right uu____1325 Prims.ignore));
(FStar_ST.write FStar_Errors.num_errs (Prims.parse_int "0"));
))
in {FStar_Interactive.pop = pop; FStar_Interactive.push = push; FStar_Interactive.mark = mark; FStar_Interactive.reset_mark = reset_mark; FStar_Interactive.commit_mark = commit_mark; FStar_Interactive.check_frag = check_frag; FStar_Interactive.report_fail = report_fail; FStar_Interactive.tc_prims = tc_prims_interactive; FStar_Interactive.tc_one_file = tc_one_file_interactive; FStar_Interactive.cleanup = cleanup}))))))))




