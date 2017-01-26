
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
(let _0_673 = FStar_Parser_AST.Module ((let _0_672 = (FStar_Parser_Interleave.interleave decls1 decls2)
in ((lid1), (_0_672))))
in (_0_673)::[])
end
| uu____68 -> begin
(Prims.raise (FStar_Errors.Err ("mismatch between pre-module and module\n")))
end)
end))
end)
in (FStar_ToSyntax_ToSyntax.desugar_file env ast))
end)))


let tc_prims : Prims.unit  ->  ((FStar_Syntax_Syntax.modul * Prims.int) * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____78 -> (

let solver = (

let uu____85 = (FStar_Options.lax ())
in (match (uu____85) with
| true -> begin
FStar_SMTEncoding_Solver.dummy
end
| uu____86 -> begin
FStar_SMTEncoding_Solver.solver
end))
in (

let env = (FStar_TypeChecker_Env.initial_env FStar_TypeChecker_TcTerm.type_of_tot_term FStar_TypeChecker_TcTerm.universe_of solver FStar_Syntax_Const.prims_lid)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env);
(

let prims_filename = (FStar_Options.prims ())
in (

let uu____90 = (let _0_674 = (FStar_ToSyntax_Env.empty_env ())
in (parse _0_674 None prims_filename))
in (match (uu____90) with
| (dsenv, prims_mod) -> begin
(

let uu____103 = (FStar_Util.record_time (fun uu____110 -> (let _0_675 = (FStar_List.hd prims_mod)
in (FStar_TypeChecker_Tc.check_module env _0_675))))
in (match (uu____103) with
| ((prims_mod, env), elapsed_time) -> begin
((((prims_mod), (elapsed_time))), (dsenv), (env))
end))
end)));
))))


let tc_one_fragment : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  FStar_Parser_ParseIt.input_frag  ->  (FStar_Syntax_Syntax.modul Prims.option * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) Prims.option = (fun curmod dsenv env frag -> try
(match (()) with
| () -> begin
(

let uu____153 = (FStar_Parser_Driver.parse_fragment frag)
in (match (uu____153) with
| FStar_Parser_Driver.Empty -> begin
Some (((curmod), (dsenv), (env)))
end
| FStar_Parser_Driver.Modul (ast_modul) -> begin
(

let uu____165 = (FStar_ToSyntax_ToSyntax.desugar_partial_modul curmod dsenv ast_modul)
in (match (uu____165) with
| (dsenv, modul) -> begin
(

let env = (match (curmod) with
| None -> begin
env
end
| Some (uu____176) -> begin
(Prims.raise (FStar_Errors.Err ("Interactive mode only supports a single module at the top-level")))
end)
in (

let uu____177 = (FStar_TypeChecker_Tc.tc_partial_modul env modul)
in (match (uu____177) with
| (modul, uu____188, env) -> begin
Some (((Some (modul)), (dsenv), (env)))
end)))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(

let uu____199 = (FStar_ToSyntax_ToSyntax.desugar_decls dsenv ast_decls)
in (match (uu____199) with
| (dsenv, decls) -> begin
(match (curmod) with
| None -> begin
((FStar_Util.print_error "fragment without an enclosing module");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| Some (modul) -> begin
(

let uu____221 = (FStar_TypeChecker_Tc.tc_more_partial_modul env modul decls)
in (match (uu____221) with
| (modul, uu____232, env) -> begin
Some (((Some (modul)), (dsenv), (env)))
end))
end)
end))
end))
end)
with
| FStar_Errors.Error (msg, r) when (not ((FStar_Options.trace_error ()))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]));
None;
)
end
| FStar_Errors.Err (msg) when (not ((FStar_Options.trace_error ()))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (FStar_Range.dummyRange)))::[]));
None;
)
end
| e when (not ((FStar_Options.trace_error ()))) -> begin
(Prims.raise e)
end)


let tc_one_file : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.option  ->  Prims.string  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env pre_fn fn -> (

let uu____300 = (parse dsenv pre_fn fn)
in (match (uu____300) with
| (dsenv, fmods) -> begin
(

let check_mods = (fun uu____323 -> (

let uu____324 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun uu____341 m -> (match (uu____341) with
| (env, all_mods) -> begin
(

let uu____361 = (FStar_Util.record_time (fun uu____368 -> (FStar_TypeChecker_Tc.check_module env m)))
in (match (uu____361) with
| ((m, env), elapsed_ms) -> begin
((env), ((((m), (elapsed_ms)))::all_mods))
end))
end)) ((env), ([]))))
in (match (uu____324) with
| (env, all_mods) -> begin
(((FStar_List.rev all_mods)), (dsenv), (env))
end)))
in (match (fmods) with
| (m)::[] when ((FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str) && ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))) -> begin
(FStar_SMTEncoding_Solver.with_hints_db fn check_mods)
end
| uu____421 -> begin
(check_mods ())
end))
end)))


let needs_interleaving : Prims.string  ->  Prims.string  ->  Prims.bool = (fun intf impl -> (

let m1 = (FStar_Parser_Dep.lowercase_module_name intf)
in (

let m2 = (FStar_Parser_Dep.lowercase_module_name impl)
in (((m1 = m2) && (let _0_676 = (FStar_Util.get_file_extension intf)
in (_0_676 = "fsti"))) && (let _0_677 = (FStar_Util.get_file_extension impl)
in (_0_677 = "fst"))))))


let pop_context : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  Prims.unit = (fun uu____437 msg -> (match (uu____437) with
| (dsenv, env) -> begin
((let _0_678 = (FStar_ToSyntax_Env.pop dsenv)
in (FStar_All.pipe_right _0_678 Prims.ignore));
(let _0_679 = (FStar_TypeChecker_Env.pop env msg)
in (FStar_All.pipe_right _0_679 Prims.ignore));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
)
end))


let push_context : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____453 msg -> (match (uu____453) with
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
| Some (uu____490) when (let _0_680 = (FStar_Options.codegen ())
in (_0_680 <> None)) -> begin
((

let uu____493 = (not ((FStar_Options.lax ())))
in (match (uu____493) with
| true -> begin
(Prims.raise (FStar_Errors.Err ("Verification and code generation are no supported together with partial modules (i.e, *.fsti); use --lax to extract code separately")))
end
| uu____494 -> begin
()
end));
(tc_one_file dsenv env intf impl);
)
end
| Some (iname) -> begin
((

let uu____497 = (FStar_Options.debug_any ())
in (match (uu____497) with
| true -> begin
(FStar_Util.print1 "Interleaving iface+module: %s\n" iname)
end
| uu____498 -> begin
()
end));
(

let caption = (Prims.strcat "interface: " iname)
in (

let uu____500 = (push_context ((dsenv), (env)) caption)
in (match (uu____500) with
| (dsenv', env') -> begin
(

let uu____511 = (tc_one_file dsenv' env' intf impl)
in (match (uu____511) with
| (uu____524, dsenv', env') -> begin
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

let uu____553 = uenv
in (match (uu____553) with
| (dsenv, env) -> begin
(

let uu____565 = (match (remaining) with
| (intf)::(impl)::remaining when (needs_interleaving intf impl) -> begin
(let _0_681 = (tc_one_file_and_intf (Some (intf)) impl dsenv env)
in ((remaining), (_0_681)))
end
| (intf_or_impl)::remaining -> begin
(let _0_682 = (tc_one_file_and_intf None intf_or_impl dsenv env)
in ((remaining), (_0_682)))
end
| [] -> begin
(([]), ((([]), (dsenv), (env))))
end)
in (match (uu____565) with
| (remaining, (nmods, dsenv, env)) -> begin
((remaining), (nmods), (((dsenv), (env))))
end))
end)))


let rec tc_fold_interleave : ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * uenv)  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * uenv) = (fun acc remaining -> (match (remaining) with
| [] -> begin
acc
end
| uu____678 -> begin
(

let uu____680 = acc
in (match (uu____680) with
| (mods, uenv) -> begin
(

let uu____699 = (tc_one_file_from_remaining remaining uenv)
in (match (uu____699) with
| (remaining, nmods, (dsenv, env)) -> begin
(tc_fold_interleave (((FStar_List.append mods nmods)), (((dsenv), (env)))) remaining)
end))
end))
end))


let batch_mode_tc_no_prims : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env filenames -> (

let uu____752 = (tc_fold_interleave (([]), (((dsenv), (env)))) filenames)
in (match (uu____752) with
| (all_mods, (dsenv, env)) -> begin
((

let uu____783 = ((FStar_Options.interactive ()) && (let _0_683 = (FStar_Errors.get_err_count ())
in (_0_683 = (Prims.parse_int "0"))))
in (match (uu____783) with
| true -> begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end
| uu____784 -> begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end));
((all_mods), (dsenv), (env));
)
end)))


let batch_mode_tc : Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun filenames -> (

let uu____799 = (tc_prims ())
in (match (uu____799) with
| (prims_mod, dsenv, env) -> begin
((

let uu____819 = ((not ((FStar_Options.explicit_deps ()))) && (FStar_Options.debug_any ()))
in (match (uu____819) with
| true -> begin
((FStar_Util.print_endline "Auto-deps kicked in; here\'s some info.");
(FStar_Util.print1 "Here\'s the list of filenames we will process: %s\n" (FStar_String.concat " " filenames));
(let _0_685 = (let _0_684 = (FStar_Options.verify_module ())
in (FStar_String.concat " " _0_684))
in (FStar_Util.print1 "Here\'s the list of modules we will verify: %s\n" _0_685));
)
end
| uu____822 -> begin
()
end));
(

let uu____823 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (uu____823) with
| (all_mods, dsenv, env) -> begin
(((prims_mod)::all_mods), (dsenv), (env))
end));
)
end)))


let tc_prims_interactive : Prims.unit  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____854 -> (

let uu____855 = (tc_prims ())
in (match (uu____855) with
| (uu____863, dsenv, env) -> begin
((dsenv), (env))
end)))


let tc_one_file_interactive = (fun remaining uenv -> (

let uu____895 = uenv
in (match (uu____895) with
| (dsenv, env) -> begin
(

let uu____909 = (match (remaining) with
| (intf)::(impl)::remaining when (needs_interleaving intf impl) -> begin
(

let uu____930 = (tc_one_file_and_intf (Some (intf)) impl dsenv env)
in (match (uu____930) with
| (uu____945, dsenv, env) -> begin
((((Some (intf)), (impl))), (dsenv), (env), (remaining))
end))
end
| (intf_or_impl)::remaining -> begin
(

let uu____962 = (tc_one_file_and_intf None intf_or_impl dsenv env)
in (match (uu____962) with
| (uu____977, dsenv, env) -> begin
((((None), (intf_or_impl))), (dsenv), (env), (remaining))
end))
end
| [] -> begin
(failwith "Impossible")
end)
in (match (uu____909) with
| ((intf, impl), dsenv, env, remaining) -> begin
((((intf), (impl))), (((dsenv), (env))), (None), (remaining))
end))
end)))


let interactive_tc : ((FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env), FStar_Syntax_Syntax.modul Prims.option) FStar_Interactive.interactive_tc = (

let pop = (fun uu____1042 msg -> (match (uu____1042) with
| (dsenv, env) -> begin
((pop_context ((dsenv), (env)) msg);
(FStar_Options.pop ());
)
end))
in (

let push = (fun uu____1062 lax restore_cmd_line_options msg -> (match (uu____1062) with
| (dsenv, env) -> begin
(

let env = (

let uu___163_1073 = env
in {FStar_TypeChecker_Env.solver = uu___163_1073.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___163_1073.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___163_1073.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___163_1073.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___163_1073.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___163_1073.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___163_1073.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___163_1073.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___163_1073.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___163_1073.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___163_1073.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___163_1073.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___163_1073.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___163_1073.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___163_1073.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___163_1073.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___163_1073.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___163_1073.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = lax; FStar_TypeChecker_Env.lax_universes = uu___163_1073.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___163_1073.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___163_1073.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___163_1073.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___163_1073.FStar_TypeChecker_Env.qname_and_index})
in (

let res = (push_context ((dsenv), (env)) msg)
in ((FStar_Options.push ());
(match (restore_cmd_line_options) with
| true -> begin
(let _0_686 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _0_686 Prims.ignore))
end
| uu____1079 -> begin
()
end);
res;
)))
end))
in (

let mark = (fun uu____1087 -> (match (uu____1087) with
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

let reset_mark = (fun uu____1104 -> (match (uu____1104) with
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

let cleanup = (fun uu____1119 -> (match (uu____1119) with
| (dsenv, env) -> begin
(FStar_TypeChecker_Env.cleanup_interactive env)
end))
in (

let commit_mark = (fun uu____1131 -> (match (uu____1131) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_ToSyntax_Env.commit_mark dsenv)
in (

let env = (FStar_TypeChecker_Env.commit_mark env)
in ((dsenv), (env))))
end))
in (

let check_frag = (fun uu____1157 curmod text -> (match (uu____1157) with
| (dsenv, env) -> begin
try
(match (()) with
| () -> begin
(

let uu____1187 = (tc_one_fragment curmod dsenv env text)
in (match (uu____1187) with
| Some (m, dsenv, env) -> begin
Some ((let _0_687 = (FStar_Errors.get_err_count ())
in ((m), (((dsenv), (env))), (_0_687))))
end
| uu____1218 -> begin
None
end))
end)
with
| FStar_Errors.Error (msg, r) when (not ((FStar_Options.trace_error ()))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]));
None;
)
end
| FStar_Errors.Err (msg) when (not ((FStar_Options.trace_error ()))) -> begin
((let _0_690 = (let _0_689 = (let _0_688 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (_0_688)))
in (_0_689)::[])
in (FStar_TypeChecker_Err.add_errors env _0_690));
None;
)
end
end))
in (

let report_fail = (fun uu____1266 -> ((let _0_691 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right _0_691 Prims.ignore));
(FStar_ST.write FStar_Errors.num_errs (Prims.parse_int "0"));
))
in {FStar_Interactive.pop = pop; FStar_Interactive.push = push; FStar_Interactive.mark = mark; FStar_Interactive.reset_mark = reset_mark; FStar_Interactive.commit_mark = commit_mark; FStar_Interactive.check_frag = check_frag; FStar_Interactive.report_fail = report_fail; FStar_Interactive.tc_prims = tc_prims_interactive; FStar_Interactive.tc_one_file = tc_one_file_interactive; FStar_Interactive.cleanup = cleanup}))))))))




