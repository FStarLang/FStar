
open Prims

let module_or_interface_name : FStar_Syntax_Syntax.modul  ->  (Prims.bool * FStar_Ident.lident) = (fun m -> ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name)))


let parse : FStar_ToSyntax_Env.env  ->  Prims.string Prims.option  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env pre_fn fn -> (

let uu____23 = (FStar_Parser_Driver.parse_file fn)
in (match (uu____23) with
| (ast, uu____33) -> begin
(

let ast1 = (match (pre_fn) with
| None -> begin
ast
end
| Some (pre_fn1) -> begin
(

let uu____42 = (FStar_Parser_Driver.parse_file pre_fn1)
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
in (FStar_ToSyntax_ToSyntax.desugar_file env ast1))
end)))


let tc_prims : Prims.unit  ->  ((FStar_Syntax_Syntax.modul * Prims.int) * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____85 -> (

let solver1 = (

let uu____92 = (FStar_Options.lax ())
in (match (uu____92) with
| true -> begin
FStar_SMTEncoding_Solver.dummy
end
| uu____93 -> begin
(

let uu___214_94 = FStar_SMTEncoding_Solver.solver
in {FStar_TypeChecker_Env.init = uu___214_94.FStar_TypeChecker_Env.init; FStar_TypeChecker_Env.push = uu___214_94.FStar_TypeChecker_Env.push; FStar_TypeChecker_Env.pop = uu___214_94.FStar_TypeChecker_Env.pop; FStar_TypeChecker_Env.mark = uu___214_94.FStar_TypeChecker_Env.mark; FStar_TypeChecker_Env.reset_mark = uu___214_94.FStar_TypeChecker_Env.reset_mark; FStar_TypeChecker_Env.commit_mark = uu___214_94.FStar_TypeChecker_Env.commit_mark; FStar_TypeChecker_Env.encode_modul = uu___214_94.FStar_TypeChecker_Env.encode_modul; FStar_TypeChecker_Env.encode_sig = uu___214_94.FStar_TypeChecker_Env.encode_sig; FStar_TypeChecker_Env.preprocess = FStar_Tactics_Interpreter.preprocess; FStar_TypeChecker_Env.solve = uu___214_94.FStar_TypeChecker_Env.solve; FStar_TypeChecker_Env.is_trivial = uu___214_94.FStar_TypeChecker_Env.is_trivial; FStar_TypeChecker_Env.finish = uu___214_94.FStar_TypeChecker_Env.finish; FStar_TypeChecker_Env.refresh = uu___214_94.FStar_TypeChecker_Env.refresh})
end))
in (

let env = (FStar_TypeChecker_Env.initial_env FStar_TypeChecker_TcTerm.type_of_tot_term FStar_TypeChecker_TcTerm.universe_of solver1 FStar_Syntax_Const.prims_lid)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env);
(

let prims_filename = (FStar_Options.prims ())
in (

let uu____98 = (

let uu____102 = (FStar_ToSyntax_Env.empty_env ())
in (parse uu____102 None prims_filename))
in (match (uu____98) with
| (dsenv, prims_mod) -> begin
(

let uu____112 = (FStar_Util.record_time (fun uu____119 -> (

let uu____120 = (FStar_List.hd prims_mod)
in (FStar_TypeChecker_Tc.check_module env uu____120))))
in (match (uu____112) with
| ((prims_mod1, env1), elapsed_time) -> begin
((((prims_mod1), (elapsed_time))), (dsenv), (env1))
end))
end)));
))))


let tc_one_fragment : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  FStar_Parser_ParseIt.input_frag  ->  (FStar_Syntax_Syntax.modul Prims.option * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) Prims.option = (fun curmod dsenv env frag -> try
(match (()) with
| () -> begin
(

let uu____163 = (FStar_Parser_Driver.parse_fragment frag)
in (match (uu____163) with
| FStar_Parser_Driver.Empty -> begin
Some (((curmod), (dsenv), (env)))
end
| FStar_Parser_Driver.Modul (ast_modul) -> begin
(

let uu____175 = (FStar_ToSyntax_ToSyntax.desugar_partial_modul curmod dsenv ast_modul)
in (match (uu____175) with
| (dsenv1, modul) -> begin
(

let env1 = (match (curmod) with
| Some (modul1) -> begin
(

let uu____187 = (

let uu____188 = (

let uu____189 = (

let uu____190 = (FStar_Options.file_list ())
in (FStar_List.hd uu____190))
in (FStar_Parser_Dep.lowercase_module_name uu____189))
in (

let uu____192 = (

let uu____193 = (FStar_Ident.string_of_lid modul1.FStar_Syntax_Syntax.name)
in (FStar_String.lowercase uu____193))
in (uu____188 <> uu____192)))
in (match (uu____187) with
| true -> begin
(Prims.raise (FStar_Errors.Err ("Interactive mode only supports a single module at the top-level")))
end
| uu____194 -> begin
env
end))
end
| None -> begin
env
end)
in (

let uu____195 = (FStar_TypeChecker_Tc.tc_partial_modul env1 modul)
in (match (uu____195) with
| (modul1, uu____206, env2) -> begin
Some (((Some (modul1)), (dsenv1), (env2)))
end)))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(

let uu____217 = (FStar_ToSyntax_ToSyntax.desugar_decls dsenv ast_decls)
in (match (uu____217) with
| (dsenv1, decls) -> begin
(match (curmod) with
| None -> begin
((FStar_Util.print_error "fragment without an enclosing module");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| Some (modul) -> begin
(

let uu____239 = (FStar_TypeChecker_Tc.tc_more_partial_modul env modul decls)
in (match (uu____239) with
| (modul1, uu____250, env1) -> begin
Some (((Some (modul1)), (dsenv1), (env1)))
end))
end)
end))
end))
end)
with
| FStar_Errors.Error (msg, r) when (

let uu____267 = (FStar_Options.trace_error ())
in (not (uu____267))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]));
None;
)
end
| FStar_Errors.Err (msg) when (

let uu____278 = (FStar_Options.trace_error ())
in (not (uu____278))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (FStar_Range.dummyRange)))::[]));
None;
)
end
| e when (

let uu____289 = (FStar_Options.trace_error ())
in (not (uu____289))) -> begin
(Prims.raise e)
end)


let tc_one_file : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.option  ->  Prims.string  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env pre_fn fn -> (

let uu____321 = (parse dsenv pre_fn fn)
in (match (uu____321) with
| (dsenv1, fmods) -> begin
(

let check_mods = (fun uu____344 -> (

let uu____345 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun uu____362 m -> (match (uu____362) with
| (env1, all_mods) -> begin
(

let uu____382 = (FStar_Util.record_time (fun uu____389 -> (FStar_TypeChecker_Tc.check_module env1 m)))
in (match (uu____382) with
| ((m1, env2), elapsed_ms) -> begin
((env2), ((((m1), (elapsed_ms)))::all_mods))
end))
end)) ((env), ([]))))
in (match (uu____345) with
| (env1, all_mods) -> begin
(((FStar_List.rev all_mods)), (dsenv1), (env1))
end)))
in (match (fmods) with
| (m)::[] when ((FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str) && ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))) -> begin
(

let uu____436 = (FStar_Parser_ParseIt.find_file fn)
in (FStar_SMTEncoding_Solver.with_hints_db uu____436 check_mods))
end
| uu____443 -> begin
(check_mods ())
end))
end)))


let needs_interleaving : Prims.string  ->  Prims.string  ->  Prims.bool = (fun intf impl -> (

let m1 = (FStar_Parser_Dep.lowercase_module_name intf)
in (

let m2 = (FStar_Parser_Dep.lowercase_module_name impl)
in (((m1 = m2) && (

let uu____453 = (FStar_Util.get_file_extension intf)
in (uu____453 = "fsti"))) && (

let uu____454 = (FStar_Util.get_file_extension impl)
in (uu____454 = "fst"))))))


let pop_context : FStar_TypeChecker_Env.env  ->  Prims.string  ->  Prims.unit = (fun env msg -> ((

let uu____462 = (FStar_ToSyntax_Env.pop ())
in (FStar_All.pipe_right uu____462 Prims.ignore));
(

let uu____464 = (FStar_TypeChecker_Env.pop env msg)
in (FStar_All.pipe_right uu____464 Prims.ignore));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
))


let push_context : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____473 msg -> (match (uu____473) with
| (dsenv, env) -> begin
(

let dsenv1 = (FStar_ToSyntax_Env.push dsenv)
in (

let env1 = (FStar_TypeChecker_Env.push env msg)
in ((dsenv1), (env1))))
end))


let tc_one_file_and_intf : Prims.string Prims.option  ->  Prims.string  ->  FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun intf impl dsenv env -> ((FStar_Syntax_Syntax.reset_gensym ());
(match (intf) with
| None -> begin
(tc_one_file dsenv env None impl)
end
| Some (uu____510) when (

let uu____511 = (FStar_Options.codegen ())
in (uu____511 <> None)) -> begin
((

let uu____515 = (

let uu____516 = (FStar_Options.lax ())
in (not (uu____516)))
in (match (uu____515) with
| true -> begin
(Prims.raise (FStar_Errors.Err ("Verification and code generation are no supported together with partial modules (i.e, *.fsti); use --lax to extract code separately")))
end
| uu____517 -> begin
()
end));
(tc_one_file dsenv env intf impl);
)
end
| Some (iname) -> begin
((

let uu____520 = (FStar_Options.debug_any ())
in (match (uu____520) with
| true -> begin
(FStar_Util.print1 "Interleaving iface+module: %s\n" iname)
end
| uu____521 -> begin
()
end));
(

let caption = (Prims.strcat "interface: " iname)
in (

let uu____523 = (push_context ((dsenv), (env)) caption)
in (match (uu____523) with
| (dsenv', env') -> begin
(

let uu____534 = (tc_one_file dsenv' env' intf impl)
in (match (uu____534) with
| (uu____547, dsenv'1, env'1) -> begin
((pop_context env'1 caption);
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

let uu____576 = uenv
in (match (uu____576) with
| (dsenv, env) -> begin
(

let uu____588 = (match (remaining) with
| (intf)::(impl)::remaining1 when (needs_interleaving intf impl) -> begin
(

let uu____611 = (tc_one_file_and_intf (Some (intf)) impl dsenv env)
in ((remaining1), (uu____611)))
end
| (intf_or_impl)::remaining1 -> begin
(

let uu____628 = (tc_one_file_and_intf None intf_or_impl dsenv env)
in ((remaining1), (uu____628)))
end
| [] -> begin
(([]), ((([]), (dsenv), (env))))
end)
in (match (uu____588) with
| (remaining1, (nmods, dsenv1, env1)) -> begin
((remaining1), (nmods), (((dsenv1), (env1))))
end))
end)))


let rec tc_fold_interleave : ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * uenv)  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * uenv) = (fun acc remaining -> (match (remaining) with
| [] -> begin
acc
end
| uu____715 -> begin
(

let uu____717 = acc
in (match (uu____717) with
| (mods, uenv) -> begin
(

let uu____736 = (tc_one_file_from_remaining remaining uenv)
in (match (uu____736) with
| (remaining1, nmods, (dsenv, env)) -> begin
(tc_fold_interleave (((FStar_List.append mods nmods)), (((dsenv), (env)))) remaining1)
end))
end))
end))


let batch_mode_tc_no_prims : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env filenames -> (

let uu____789 = (tc_fold_interleave (([]), (((dsenv), (env)))) filenames)
in (match (uu____789) with
| (all_mods, (dsenv1, env1)) -> begin
((

let uu____820 = ((FStar_Options.interactive ()) && (

let uu____821 = (FStar_Errors.get_err_count ())
in (uu____821 = (Prims.parse_int "0"))))
in (match (uu____820) with
| true -> begin
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end
| uu____822 -> begin
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end));
((all_mods), (dsenv1), (env1));
)
end)))


let batch_mode_tc : Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun filenames -> (

let uu____837 = (tc_prims ())
in (match (uu____837) with
| (prims_mod, dsenv, env) -> begin
((

let uu____857 = ((

let uu____858 = (FStar_Options.explicit_deps ())
in (not (uu____858))) && (FStar_Options.debug_any ()))
in (match (uu____857) with
| true -> begin
((FStar_Util.print_endline "Auto-deps kicked in; here\'s some info.");
(FStar_Util.print1 "Here\'s the list of filenames we will process: %s\n" (FStar_String.concat " " filenames));
(

let uu____861 = (

let uu____862 = (FStar_Options.verify_module ())
in (FStar_String.concat " " uu____862))
in (FStar_Util.print1 "Here\'s the list of modules we will verify: %s\n" uu____861));
)
end
| uu____864 -> begin
()
end));
(

let uu____865 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (uu____865) with
| (all_mods, dsenv1, env1) -> begin
(((prims_mod)::all_mods), (dsenv1), (env1))
end));
)
end)))




