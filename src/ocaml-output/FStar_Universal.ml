
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
(let _0_698 = FStar_Parser_AST.Module ((let _0_697 = (FStar_Parser_Interleave.interleave decls1 decls2)
in ((lid1), (_0_697))))
in (_0_698)::[])
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

let uu____90 = (let _0_699 = (FStar_ToSyntax_Env.empty_env ())
in (parse _0_699 None prims_filename))
in (match (uu____90) with
| (dsenv, prims_mod) -> begin
(

let uu____103 = (FStar_Util.record_time (fun uu____110 -> (let _0_700 = (FStar_List.hd prims_mod)
in (FStar_TypeChecker_Tc.check_module env _0_700))))
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
| Some (modul) -> begin
(

let uu____177 = (let _0_702 = (FStar_Parser_Dep.lowercase_module_name (FStar_List.hd (FStar_Options.file_list ())))
in (let _0_701 = (FStar_String.lowercase (FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name))
in (_0_702 <> _0_701)))
in (match (uu____177) with
| true -> begin
(Prims.raise (FStar_Errors.Err ("Interactive mode only supports a single module at the top-level")))
end
| uu____178 -> begin
env
end))
end
| None -> begin
env
end)
in (

let uu____179 = (FStar_TypeChecker_Tc.tc_partial_modul env modul)
in (match (uu____179) with
| (modul, uu____190, env) -> begin
Some (((Some (modul)), (dsenv), (env)))
end)))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(

let uu____201 = (FStar_ToSyntax_ToSyntax.desugar_decls dsenv ast_decls)
in (match (uu____201) with
| (dsenv, decls) -> begin
(match (curmod) with
| None -> begin
((FStar_Util.print_error "fragment without an enclosing module");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| Some (modul) -> begin
(

let uu____223 = (FStar_TypeChecker_Tc.tc_more_partial_modul env modul decls)
in (match (uu____223) with
| (modul, uu____234, env) -> begin
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

let uu____302 = (parse dsenv pre_fn fn)
in (match (uu____302) with
| (dsenv, fmods) -> begin
(

let check_mods = (fun uu____325 -> (

let uu____326 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun uu____343 m -> (match (uu____343) with
| (env, all_mods) -> begin
(

let uu____363 = (FStar_Util.record_time (fun uu____370 -> (FStar_TypeChecker_Tc.check_module env m)))
in (match (uu____363) with
| ((m, env), elapsed_ms) -> begin
((env), ((((m), (elapsed_ms)))::all_mods))
end))
end)) ((env), ([]))))
in (match (uu____326) with
| (env, all_mods) -> begin
(((FStar_List.rev all_mods)), (dsenv), (env))
end)))
in (match (fmods) with
| (m)::[] when ((FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str) && ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))) -> begin
(FStar_SMTEncoding_Solver.with_hints_db fn check_mods)
end
| uu____423 -> begin
(check_mods ())
end))
end)))


let needs_interleaving : Prims.string  ->  Prims.string  ->  Prims.bool = (fun intf impl -> (

let m1 = (FStar_Parser_Dep.lowercase_module_name intf)
in (

let m2 = (FStar_Parser_Dep.lowercase_module_name impl)
in (((m1 = m2) && (let _0_703 = (FStar_Util.get_file_extension intf)
in (_0_703 = "fsti"))) && (let _0_704 = (FStar_Util.get_file_extension impl)
in (_0_704 = "fst"))))))


let pop_context : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  Prims.unit = (fun uu____439 msg -> (match (uu____439) with
| (dsenv, env) -> begin
((let _0_705 = (FStar_ToSyntax_Env.pop dsenv)
in (FStar_All.pipe_right _0_705 Prims.ignore));
(let _0_706 = (FStar_TypeChecker_Env.pop env msg)
in (FStar_All.pipe_right _0_706 Prims.ignore));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
)
end))


let push_context : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____455 msg -> (match (uu____455) with
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
| Some (uu____492) when (let _0_707 = (FStar_Options.codegen ())
in (_0_707 <> None)) -> begin
((

let uu____495 = (not ((FStar_Options.lax ())))
in (match (uu____495) with
| true -> begin
(Prims.raise (FStar_Errors.Err ("Verification and code generation are no supported together with partial modules (i.e, *.fsti); use --lax to extract code separately")))
end
| uu____496 -> begin
()
end));
(tc_one_file dsenv env intf impl);
)
end
| Some (iname) -> begin
((

let uu____499 = (FStar_Options.debug_any ())
in (match (uu____499) with
| true -> begin
(FStar_Util.print1 "Interleaving iface+module: %s\n" iname)
end
| uu____500 -> begin
()
end));
(

let caption = (Prims.strcat "interface: " iname)
in (

let uu____502 = (push_context ((dsenv), (env)) caption)
in (match (uu____502) with
| (dsenv', env') -> begin
(

let uu____513 = (tc_one_file dsenv' env' intf impl)
in (match (uu____513) with
| (uu____526, dsenv', env') -> begin
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

let uu____555 = uenv
in (match (uu____555) with
| (dsenv, env) -> begin
(

let uu____567 = (match (remaining) with
| (intf)::(impl)::remaining when (needs_interleaving intf impl) -> begin
(let _0_708 = (tc_one_file_and_intf (Some (intf)) impl dsenv env)
in ((remaining), (_0_708)))
end
| (intf_or_impl)::remaining -> begin
(let _0_709 = (tc_one_file_and_intf None intf_or_impl dsenv env)
in ((remaining), (_0_709)))
end
| [] -> begin
(([]), ((([]), (dsenv), (env))))
end)
in (match (uu____567) with
| (remaining, (nmods, dsenv, env)) -> begin
((remaining), (nmods), (((dsenv), (env))))
end))
end)))


let rec tc_fold_interleave : ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * uenv)  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * uenv) = (fun acc remaining -> (match (remaining) with
| [] -> begin
acc
end
| uu____680 -> begin
(

let uu____682 = acc
in (match (uu____682) with
| (mods, uenv) -> begin
(

let uu____701 = (tc_one_file_from_remaining remaining uenv)
in (match (uu____701) with
| (remaining, nmods, (dsenv, env)) -> begin
(tc_fold_interleave (((FStar_List.append mods nmods)), (((dsenv), (env)))) remaining)
end))
end))
end))


let batch_mode_tc_no_prims : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env filenames -> (

let uu____754 = (tc_fold_interleave (([]), (((dsenv), (env)))) filenames)
in (match (uu____754) with
| (all_mods, (dsenv, env)) -> begin
((

let uu____785 = ((FStar_Options.interactive ()) && (let _0_710 = (FStar_Errors.get_err_count ())
in (_0_710 = (Prims.parse_int "0"))))
in (match (uu____785) with
| true -> begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end
| uu____786 -> begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end));
((all_mods), (dsenv), (env));
)
end)))


let batch_mode_tc : Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun filenames -> (

let uu____801 = (tc_prims ())
in (match (uu____801) with
| (prims_mod, dsenv, env) -> begin
((

let uu____821 = ((not ((FStar_Options.explicit_deps ()))) && (FStar_Options.debug_any ()))
in (match (uu____821) with
| true -> begin
((FStar_Util.print_endline "Auto-deps kicked in; here\'s some info.");
(FStar_Util.print1 "Here\'s the list of filenames we will process: %s\n" (FStar_String.concat " " filenames));
(let _0_712 = (let _0_711 = (FStar_Options.verify_module ())
in (FStar_String.concat " " _0_711))
in (FStar_Util.print1 "Here\'s the list of modules we will verify: %s\n" _0_712));
)
end
| uu____824 -> begin
()
end));
(

let uu____825 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (uu____825) with
| (all_mods, dsenv, env) -> begin
(((prims_mod)::all_mods), (dsenv), (env))
end));
)
end)))


let tc_prims_interactive : Prims.unit  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____856 -> (

let uu____857 = (tc_prims ())
in (match (uu____857) with
| (uu____865, dsenv, env) -> begin
((dsenv), (env))
end)))


let tc_one_file_interactive = (fun remaining uenv -> (

let uu____897 = uenv
in (match (uu____897) with
| (dsenv, env) -> begin
(

let uu____911 = (match (remaining) with
| (intf)::(impl)::remaining when (needs_interleaving intf impl) -> begin
(

let uu____932 = (tc_one_file_and_intf (Some (intf)) impl dsenv env)
in (match (uu____932) with
| (uu____947, dsenv, env) -> begin
((((Some (intf)), (impl))), (dsenv), (env), (remaining))
end))
end
| (intf_or_impl)::remaining -> begin
(

let uu____964 = (tc_one_file_and_intf None intf_or_impl dsenv env)
in (match (uu____964) with
| (uu____979, dsenv, env) -> begin
((((None), (intf_or_impl))), (dsenv), (env), (remaining))
end))
end
| [] -> begin
(failwith "Impossible")
end)
in (match (uu____911) with
| ((intf, impl), dsenv, env, remaining) -> begin
((((intf), (impl))), (((dsenv), (env))), (None), (remaining))
end))
end)))


let interactive_tc : ((FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env), FStar_Syntax_Syntax.modul Prims.option) FStar_Interactive.interactive_tc = (

let pop = (fun uu____1044 msg -> (match (uu____1044) with
| (dsenv, env) -> begin
((FStar_Util.print_string "U/pop\n");
(pop_context ((dsenv), (env)) msg);
(FStar_Options.pop ());
)
end))
in (

let push = (fun uu____1065 lax restore_cmd_line_options msg -> (match (uu____1065) with
| (dsenv, env) -> begin
((FStar_Util.print_string "U/push\n");
(

let env = (

let uu___164_1077 = env
in {FStar_TypeChecker_Env.solver = uu___164_1077.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___164_1077.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___164_1077.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___164_1077.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___164_1077.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___164_1077.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___164_1077.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___164_1077.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___164_1077.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___164_1077.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___164_1077.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___164_1077.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___164_1077.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___164_1077.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___164_1077.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___164_1077.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___164_1077.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___164_1077.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = lax; FStar_TypeChecker_Env.lax_universes = uu___164_1077.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___164_1077.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___164_1077.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___164_1077.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___164_1077.FStar_TypeChecker_Env.qname_and_index})
in (

let res = (push_context ((dsenv), (env)) msg)
in ((FStar_Options.push ());
(match (restore_cmd_line_options) with
| true -> begin
(let _0_713 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _0_713 Prims.ignore))
end
| uu____1083 -> begin
()
end);
res;
)));
)
end))
in (

let mark = (fun uu____1091 -> (match (uu____1091) with
| (dsenv, env) -> begin
((FStar_Util.print_string "U/mark\n");
(

let dsenv = (FStar_ToSyntax_Env.mark dsenv)
in (

let env = (FStar_TypeChecker_Env.mark env)
in ((FStar_Options.push ());
((dsenv), (env));
)));
)
end))
in (

let reset_mark = (fun uu____1109 -> (match (uu____1109) with
| (dsenv, env) -> begin
((FStar_Util.print_string "U/reset_mark\n");
(

let dsenv = (FStar_ToSyntax_Env.reset_mark dsenv)
in (

let env = (FStar_TypeChecker_Env.reset_mark env)
in ((FStar_Options.pop ());
((dsenv), (env));
)));
)
end))
in (

let cleanup = (fun uu____1125 -> (match (uu____1125) with
| (dsenv, env) -> begin
(FStar_TypeChecker_Env.cleanup_interactive env)
end))
in (

let commit_mark = (fun uu____1137 -> (match (uu____1137) with
| (dsenv, env) -> begin
((FStar_Util.print_string "U/commit_mark\n");
(

let dsenv = (FStar_ToSyntax_Env.commit_mark dsenv)
in (

let env = (FStar_TypeChecker_Env.commit_mark env)
in ((dsenv), (env))));
)
end))
in (

let check_frag = (fun uu____1164 curmod text -> (match (uu____1164) with
| (dsenv, env) -> begin
((FStar_Util.print_string "U/check_frag\n");
try
(match (()) with
| () -> begin
(

let uu____1195 = (tc_one_fragment curmod dsenv env text)
in (match (uu____1195) with
| Some (m, dsenv, env) -> begin
((match ((FStar_Util.is_some curmod)) with
| true -> begin
(Prims.ignore (FStar_ToSyntax_Env.pop dsenv))
end
| uu____1218 -> begin
()
end);
Some ((let _0_714 = (FStar_Errors.get_err_count ())
in ((m), (((dsenv), (env))), (_0_714))));
)
end
| uu____1228 -> begin
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
((let _0_717 = (let _0_716 = (let _0_715 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (_0_715)))
in (_0_716)::[])
in (FStar_TypeChecker_Err.add_errors env _0_717));
None;
)
end;
)
end))
in (

let report_fail = (fun uu____1276 -> ((let _0_718 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right _0_718 Prims.ignore));
(FStar_ST.write FStar_Errors.num_errs (Prims.parse_int "0"));
))
in {FStar_Interactive.pop = pop; FStar_Interactive.push = push; FStar_Interactive.mark = mark; FStar_Interactive.reset_mark = reset_mark; FStar_Interactive.commit_mark = commit_mark; FStar_Interactive.check_frag = check_frag; FStar_Interactive.report_fail = report_fail; FStar_Interactive.tc_prims = tc_prims_interactive; FStar_Interactive.tc_one_file = tc_one_file_interactive; FStar_Interactive.cleanup = cleanup}))))))))




