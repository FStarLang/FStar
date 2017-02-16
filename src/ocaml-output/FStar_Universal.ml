
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
| Some (modul) -> begin
(

let uu____186 = (

let uu____187 = (

let uu____188 = (

let uu____189 = (FStar_Options.file_list ())
in (FStar_List.hd uu____189))
in (FStar_Parser_Dep.lowercase_module_name uu____188))
in (

let uu____191 = (

let uu____192 = (FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name)
in (FStar_String.lowercase uu____192))
in (uu____187 <> uu____191)))
in (match (uu____186) with
| true -> begin
(Prims.raise (FStar_Errors.Err ("Interactive mode only supports a single module at the top-level")))
end
| uu____193 -> begin
env
end))
end
| None -> begin
env
end)
in (

let uu____194 = (FStar_TypeChecker_Tc.tc_partial_modul env modul)
in (match (uu____194) with
| (modul, uu____205, env) -> begin
Some (((Some (modul)), (dsenv), (env)))
end)))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(

let uu____216 = (FStar_ToSyntax_ToSyntax.desugar_decls dsenv ast_decls)
in (match (uu____216) with
| (dsenv, decls) -> begin
(match (curmod) with
| None -> begin
((FStar_Util.print_error "fragment without an enclosing module");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| Some (modul) -> begin
(

let uu____238 = (FStar_TypeChecker_Tc.tc_more_partial_modul env modul decls)
in (match (uu____238) with
| (modul, uu____249, env) -> begin
Some (((Some (modul)), (dsenv), (env)))
end))
end)
end))
end))
end)
with
| FStar_Errors.Error (msg, r) when (

let uu____266 = (FStar_Options.trace_error ())
in (not (uu____266))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]));
None;
)
end
| FStar_Errors.Err (msg) when (

let uu____277 = (FStar_Options.trace_error ())
in (not (uu____277))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (FStar_Range.dummyRange)))::[]));
None;
)
end
| e when (

let uu____288 = (FStar_Options.trace_error ())
in (not (uu____288))) -> begin
(Prims.raise e)
end)


let tc_one_file : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.option  ->  Prims.string  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env pre_fn fn -> (

let uu____320 = (parse dsenv pre_fn fn)
in (match (uu____320) with
| (dsenv, fmods) -> begin
(

let check_mods = (fun uu____343 -> (

let uu____344 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun uu____361 m -> (match (uu____361) with
| (env, all_mods) -> begin
(

let uu____381 = (FStar_Util.record_time (fun uu____388 -> (FStar_TypeChecker_Tc.check_module env m)))
in (match (uu____381) with
| ((m, env), elapsed_ms) -> begin
((env), ((((m), (elapsed_ms)))::all_mods))
end))
end)) ((env), ([]))))
in (match (uu____344) with
| (env, all_mods) -> begin
(((FStar_List.rev all_mods)), (dsenv), (env))
end)))
in (match (fmods) with
| (m)::[] when ((FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str) && ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))) -> begin
(

let uu____435 = (FStar_Parser_ParseIt.find_file fn)
in (FStar_SMTEncoding_Solver.with_hints_db uu____435 check_mods))
end
| uu____442 -> begin
(check_mods ())
end))
end)))


let needs_interleaving : Prims.string  ->  Prims.string  ->  Prims.bool = (fun intf impl -> (

let m1 = (FStar_Parser_Dep.lowercase_module_name intf)
in (

let m2 = (FStar_Parser_Dep.lowercase_module_name impl)
in (((m1 = m2) && (

let uu____452 = (FStar_Util.get_file_extension intf)
in (uu____452 = "fsti"))) && (

let uu____453 = (FStar_Util.get_file_extension impl)
in (uu____453 = "fst"))))))


let pop_context : FStar_TypeChecker_Env.env  ->  Prims.string  ->  Prims.unit = (fun env msg -> ((

let uu____461 = (FStar_ToSyntax_Env.pop ())
in (FStar_All.pipe_right uu____461 Prims.ignore));
(

let uu____463 = (FStar_TypeChecker_Env.pop env msg)
in (FStar_All.pipe_right uu____463 Prims.ignore));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
))


let push_context : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____472 msg -> (match (uu____472) with
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
| Some (uu____509) when (

let uu____510 = (FStar_Options.codegen ())
in (uu____510 <> None)) -> begin
((

let uu____514 = (

let uu____515 = (FStar_Options.lax ())
in (not (uu____515)))
in (match (uu____514) with
| true -> begin
(Prims.raise (FStar_Errors.Err ("Verification and code generation are no supported together with partial modules (i.e, *.fsti); use --lax to extract code separately")))
end
| uu____516 -> begin
()
end));
(tc_one_file dsenv env intf impl);
)
end
| Some (iname) -> begin
((

let uu____519 = (FStar_Options.debug_any ())
in (match (uu____519) with
| true -> begin
(FStar_Util.print1 "Interleaving iface+module: %s\n" iname)
end
| uu____520 -> begin
()
end));
(

let caption = (Prims.strcat "interface: " iname)
in (

let uu____522 = (push_context ((dsenv), (env)) caption)
in (match (uu____522) with
| (dsenv', env') -> begin
(

let uu____533 = (tc_one_file dsenv' env' intf impl)
in (match (uu____533) with
| (uu____546, dsenv', env') -> begin
((pop_context env' caption);
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

let uu____575 = uenv
in (match (uu____575) with
| (dsenv, env) -> begin
(

let uu____587 = (match (remaining) with
| (intf)::(impl)::remaining when (needs_interleaving intf impl) -> begin
(

let uu____610 = (tc_one_file_and_intf (Some (intf)) impl dsenv env)
in ((remaining), (uu____610)))
end
| (intf_or_impl)::remaining -> begin
(

let uu____627 = (tc_one_file_and_intf None intf_or_impl dsenv env)
in ((remaining), (uu____627)))
end
| [] -> begin
(([]), ((([]), (dsenv), (env))))
end)
in (match (uu____587) with
| (remaining, (nmods, dsenv, env)) -> begin
((remaining), (nmods), (((dsenv), (env))))
end))
end)))


let rec tc_fold_interleave : ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * uenv)  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * uenv) = (fun acc remaining -> (match (remaining) with
| [] -> begin
acc
end
| uu____714 -> begin
(

let uu____716 = acc
in (match (uu____716) with
| (mods, uenv) -> begin
(

let uu____735 = (tc_one_file_from_remaining remaining uenv)
in (match (uu____735) with
| (remaining, nmods, (dsenv, env)) -> begin
(tc_fold_interleave (((FStar_List.append mods nmods)), (((dsenv), (env)))) remaining)
end))
end))
end))


let batch_mode_tc_no_prims : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env filenames -> (

let uu____788 = (tc_fold_interleave (([]), (((dsenv), (env)))) filenames)
in (match (uu____788) with
| (all_mods, (dsenv, env)) -> begin
((

let uu____819 = ((FStar_Options.interactive ()) && (

let uu____820 = (FStar_Errors.get_err_count ())
in (uu____820 = (Prims.parse_int "0"))))
in (match (uu____819) with
| true -> begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end
| uu____821 -> begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end));
((all_mods), (dsenv), (env));
)
end)))


let batch_mode_tc : Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun filenames -> (

let uu____836 = (tc_prims ())
in (match (uu____836) with
| (prims_mod, dsenv, env) -> begin
((

let uu____856 = ((

let uu____857 = (FStar_Options.explicit_deps ())
in (not (uu____857))) && (FStar_Options.debug_any ()))
in (match (uu____856) with
| true -> begin
((FStar_Util.print_endline "Auto-deps kicked in; here\'s some info.");
(FStar_Util.print1 "Here\'s the list of filenames we will process: %s\n" (FStar_String.concat " " filenames));
(

let uu____860 = (

let uu____861 = (FStar_Options.verify_module ())
in (FStar_String.concat " " uu____861))
in (FStar_Util.print1 "Here\'s the list of modules we will verify: %s\n" uu____860));
)
end
| uu____863 -> begin
()
end));
(

let uu____864 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (uu____864) with
| (all_mods, dsenv, env) -> begin
(((prims_mod)::all_mods), (dsenv), (env))
end));
)
end)))




