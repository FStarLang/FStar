
open Prims
open FStar_Pervasives

let module_or_interface_name : FStar_Syntax_Syntax.modul  ->  (Prims.bool * FStar_Ident.lident) = (fun m -> ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name)))


let parse : FStar_ToSyntax_Env.env  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env pre_fn fn -> (

let uu____23 = (FStar_Parser_Driver.parse_file fn)
in (match (uu____23) with
| (ast, uu____33) -> begin
(

let uu____40 = (match (pre_fn) with
| FStar_Pervasives_Native.None -> begin
((env), (ast))
end
| FStar_Pervasives_Native.Some (pre_fn1) -> begin
(

let uu____46 = (FStar_Parser_Driver.parse_file pre_fn1)
in (match (uu____46) with
| (pre_ast, uu____55) -> begin
(match (((pre_ast), (ast))) with
| ((FStar_Parser_AST.Interface (lid1, decls1, uu____66))::[], (FStar_Parser_AST.Module (lid2, decls2))::[]) when (FStar_Ident.lid_equals lid1 lid2) -> begin
(

let env1 = (FStar_ToSyntax_Interleave.initialize_interface lid1 decls1 env)
in (

let uu____76 = (

let uu____79 = (FStar_List.hd ast)
in (FStar_ToSyntax_Interleave.interleave_module env1 uu____79 true))
in (match (uu____76) with
| (env2, ast1) -> begin
((env2), ((ast1)::[]))
end)))
end
| uu____85 -> begin
(FStar_Pervasives.raise (FStar_Errors.Err ("mismatch between pre-module and module\n")))
end)
end))
end)
in (match (uu____40) with
| (env1, ast1) -> begin
(FStar_ToSyntax_ToSyntax.desugar_file env1 ast1)
end))
end)))


let tc_prims : Prims.unit  ->  ((FStar_Syntax_Syntax.modul * Prims.int) * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____102 -> (

let solver1 = (

let uu____109 = (FStar_Options.lax ())
in (match (uu____109) with
| true -> begin
FStar_SMTEncoding_Solver.dummy
end
| uu____110 -> begin
(

let uu___192_111 = FStar_SMTEncoding_Solver.solver
in {FStar_TypeChecker_Env.init = uu___192_111.FStar_TypeChecker_Env.init; FStar_TypeChecker_Env.push = uu___192_111.FStar_TypeChecker_Env.push; FStar_TypeChecker_Env.pop = uu___192_111.FStar_TypeChecker_Env.pop; FStar_TypeChecker_Env.mark = uu___192_111.FStar_TypeChecker_Env.mark; FStar_TypeChecker_Env.reset_mark = uu___192_111.FStar_TypeChecker_Env.reset_mark; FStar_TypeChecker_Env.commit_mark = uu___192_111.FStar_TypeChecker_Env.commit_mark; FStar_TypeChecker_Env.encode_modul = uu___192_111.FStar_TypeChecker_Env.encode_modul; FStar_TypeChecker_Env.encode_sig = uu___192_111.FStar_TypeChecker_Env.encode_sig; FStar_TypeChecker_Env.preprocess = FStar_Tactics_Interpreter.preprocess; FStar_TypeChecker_Env.solve = uu___192_111.FStar_TypeChecker_Env.solve; FStar_TypeChecker_Env.is_trivial = uu___192_111.FStar_TypeChecker_Env.is_trivial; FStar_TypeChecker_Env.finish = uu___192_111.FStar_TypeChecker_Env.finish; FStar_TypeChecker_Env.refresh = uu___192_111.FStar_TypeChecker_Env.refresh})
end))
in (

let env = (FStar_TypeChecker_Env.initial_env FStar_TypeChecker_TcTerm.type_of_tot_term FStar_TypeChecker_TcTerm.universe_of solver1 FStar_Parser_Const.prims_lid)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env);
(

let prims_filename = (FStar_Options.prims ())
in (

let uu____115 = (

let uu____119 = (FStar_ToSyntax_Env.empty_env ())
in (parse uu____119 FStar_Pervasives_Native.None prims_filename))
in (match (uu____115) with
| (dsenv, prims_mod) -> begin
(

let uu____129 = (FStar_Util.record_time (fun uu____136 -> (

let uu____137 = (FStar_List.hd prims_mod)
in (FStar_TypeChecker_Tc.check_module env uu____137))))
in (match (uu____129) with
| ((prims_mod1, env1), elapsed_time) -> begin
((((prims_mod1), (elapsed_time))), (dsenv), (env1))
end))
end)));
))))


let tc_one_fragment : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  (FStar_Parser_ParseIt.input_frag * Prims.bool)  ->  (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) FStar_Pervasives_Native.option = (fun curmod dsenv env uu____169 -> (match (uu____169) with
| (frag, is_interface_dependence) -> begin
try
(match (()) with
| () -> begin
(

let uu____191 = (FStar_Parser_Driver.parse_fragment frag)
in (match (uu____191) with
| FStar_Parser_Driver.Empty -> begin
FStar_Pervasives_Native.Some (((curmod), (dsenv), (env)))
end
| FStar_Parser_Driver.Modul (ast_modul) -> begin
(

let uu____203 = (FStar_ToSyntax_Interleave.interleave_module dsenv ast_modul false)
in (match (uu____203) with
| (ds_env, ast_modul1) -> begin
(

let uu____213 = (FStar_ToSyntax_ToSyntax.desugar_partial_modul curmod dsenv ast_modul1)
in (match (uu____213) with
| (dsenv1, modul) -> begin
(

let dsenv2 = (match (is_interface_dependence) with
| true -> begin
(FStar_ToSyntax_Env.set_iface dsenv1 false)
end
| uu____224 -> begin
dsenv1
end)
in (

let env1 = (match (curmod) with
| FStar_Pervasives_Native.Some (modul1) -> begin
(

let uu____227 = (

let uu____228 = (

let uu____229 = (

let uu____230 = (FStar_Options.file_list ())
in (FStar_List.hd uu____230))
in (FStar_Parser_Dep.lowercase_module_name uu____229))
in (

let uu____232 = (

let uu____233 = (FStar_Ident.string_of_lid modul1.FStar_Syntax_Syntax.name)
in (FStar_String.lowercase uu____233))
in (uu____228 <> uu____232)))
in (match (uu____227) with
| true -> begin
(FStar_Pervasives.raise (FStar_Errors.Err ("Interactive mode only supports a single module at the top-level")))
end
| uu____234 -> begin
env
end))
end
| FStar_Pervasives_Native.None -> begin
env
end)
in (

let uu____235 = (

let uu____240 = (FStar_ToSyntax_Env.syntax_only dsenv2)
in (match (uu____240) with
| true -> begin
((modul), ([]), (env1))
end
| uu____246 -> begin
(FStar_TypeChecker_Tc.tc_partial_modul env1 modul)
end))
in (match (uu____235) with
| (modul1, uu____253, env2) -> begin
FStar_Pervasives_Native.Some (((FStar_Pervasives_Native.Some (modul1)), (dsenv2), (env2)))
end))))
end))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(

let uu____264 = (FStar_Util.fold_map FStar_ToSyntax_Interleave.prefix_with_interface_decls dsenv ast_decls)
in (match (uu____264) with
| (dsenv1, ast_decls_l) -> begin
(

let uu____281 = (FStar_ToSyntax_ToSyntax.desugar_decls dsenv1 (FStar_List.flatten ast_decls_l))
in (match (uu____281) with
| (dsenv2, decls) -> begin
(match (curmod) with
| FStar_Pervasives_Native.None -> begin
((FStar_Util.print_error "fragment without an enclosing module");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| FStar_Pervasives_Native.Some (modul) -> begin
(

let uu____303 = (

let uu____308 = (FStar_ToSyntax_Env.syntax_only dsenv2)
in (match (uu____308) with
| true -> begin
((modul), ([]), (env))
end
| uu____314 -> begin
(FStar_TypeChecker_Tc.tc_more_partial_modul env modul decls)
end))
in (match (uu____303) with
| (modul1, uu____321, env1) -> begin
FStar_Pervasives_Native.Some (((FStar_Pervasives_Native.Some (modul1)), (dsenv2), (env1)))
end))
end)
end))
end))
end))
end)
with
| FStar_Errors.Error (msg, r) when (

let uu____338 = (FStar_Options.trace_error ())
in (not (uu____338))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]));
FStar_Pervasives_Native.None;
)
end
| FStar_Errors.Err (msg) when (

let uu____349 = (FStar_Options.trace_error ())
in (not (uu____349))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (FStar_Range.dummyRange)))::[]));
FStar_Pervasives_Native.None;
)
end
| e when (

let uu____360 = (FStar_Options.trace_error ())
in (not (uu____360))) -> begin
(FStar_Pervasives.raise e)
end
end))


let load_interface_decls : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  FStar_Parser_ParseIt.filename  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____374 interface_file_name -> (match (uu____374) with
| (dsenv, env) -> begin
try
(match (()) with
| () -> begin
(

let r = (FStar_Parser_ParseIt.parse (FStar_Util.Inl (interface_file_name)))
in (match (r) with
| FStar_Util.Inl (FStar_Util.Inl ((FStar_Parser_AST.Interface (l, decls, uu____403))::[]), uu____404) -> begin
(

let uu____430 = (FStar_ToSyntax_Interleave.initialize_interface l decls dsenv)
in ((uu____430), (env)))
end
| FStar_Util.Inl (uu____431) -> begin
(

let uu____444 = (

let uu____445 = (FStar_Util.format1 "Unexpected result from parsing %s; expected a single interface" interface_file_name)
in FStar_Errors.Err (uu____445))
in (FStar_Pervasives.raise uu____444))
end
| FStar_Util.Inr (err1, rng) -> begin
(FStar_Pervasives.raise (FStar_Errors.Error (((err1), (rng)))))
end))
end)
with
| FStar_Errors.Error (msg, r) when (

let uu____464 = (FStar_Options.trace_error ())
in (not (uu____464))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]));
((dsenv), (env));
)
end
| FStar_Errors.Err (msg) when (

let uu____471 = (FStar_Options.trace_error ())
in (not (uu____471))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (FStar_Range.dummyRange)))::[]));
((dsenv), (env));
)
end
| e when (

let uu____478 = (FStar_Options.trace_error ())
in (not (uu____478))) -> begin
(FStar_Pervasives.raise e)
end
end))


let tc_one_file : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env pre_fn fn -> (

let uu____507 = (parse dsenv pre_fn fn)
in (match (uu____507) with
| (dsenv1, fmods) -> begin
(

let check_mods = (fun uu____530 -> (

let uu____531 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun uu____548 m -> (match (uu____548) with
| (env1, all_mods) -> begin
(

let uu____568 = (FStar_Util.record_time (fun uu____575 -> (FStar_TypeChecker_Tc.check_module env1 m)))
in (match (uu____568) with
| ((m1, env2), elapsed_ms) -> begin
((env2), ((((m1), (elapsed_ms)))::all_mods))
end))
end)) ((env), ([]))))
in (match (uu____531) with
| (env1, all_mods) -> begin
(((FStar_List.rev all_mods)), (dsenv1), (env1))
end)))
in (match (fmods) with
| (m)::[] when ((FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str) && ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))) -> begin
(

let uu____622 = (FStar_Parser_ParseIt.find_file fn)
in (FStar_SMTEncoding_Solver.with_hints_db uu____622 check_mods))
end
| uu____629 -> begin
(check_mods ())
end))
end)))


let needs_interleaving : Prims.string  ->  Prims.string  ->  Prims.bool = (fun intf impl -> (

let m1 = (FStar_Parser_Dep.lowercase_module_name intf)
in (

let m2 = (FStar_Parser_Dep.lowercase_module_name impl)
in (((m1 = m2) && (

let uu____639 = (FStar_Util.get_file_extension intf)
in (uu____639 = "fsti"))) && (

let uu____640 = (FStar_Util.get_file_extension impl)
in (uu____640 = "fst"))))))


let pop_context : FStar_TypeChecker_Env.env  ->  Prims.string  ->  Prims.unit = (fun env msg -> ((

let uu____648 = (FStar_ToSyntax_Env.pop ())
in (FStar_All.pipe_right uu____648 FStar_Pervasives.ignore));
(

let uu____650 = (FStar_TypeChecker_Env.pop env msg)
in (FStar_All.pipe_right uu____650 FStar_Pervasives.ignore));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
))


let push_context : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____659 msg -> (match (uu____659) with
| (dsenv, env) -> begin
(

let dsenv1 = (FStar_ToSyntax_Env.push dsenv)
in (

let env1 = (FStar_TypeChecker_Env.push env msg)
in ((dsenv1), (env1))))
end))


type uenv =
(FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)


let tc_one_file_from_remaining : Prims.string Prims.list  ->  uenv  ->  (Prims.string Prims.list * (FStar_Syntax_Syntax.modul * Prims.int) Prims.list * (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)) = (fun remaining uenv -> (

let uu____688 = uenv
in (match (uu____688) with
| (dsenv, env) -> begin
(

let uu____700 = (match (remaining) with
| (intf)::(impl)::remaining1 when (needs_interleaving intf impl) -> begin
(

let uu____723 = (tc_one_file dsenv env (FStar_Pervasives_Native.Some (intf)) impl)
in ((remaining1), (uu____723)))
end
| (intf_or_impl)::remaining1 -> begin
(

let uu____740 = (tc_one_file dsenv env FStar_Pervasives_Native.None intf_or_impl)
in ((remaining1), (uu____740)))
end
| [] -> begin
(([]), ((([]), (dsenv), (env))))
end)
in (match (uu____700) with
| (remaining1, (nmods, dsenv1, env1)) -> begin
((remaining1), (nmods), (((dsenv1), (env1))))
end))
end)))


let rec tc_fold_interleave : ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * uenv)  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * uenv) = (fun acc remaining -> (match (remaining) with
| [] -> begin
acc
end
| uu____827 -> begin
(

let uu____829 = acc
in (match (uu____829) with
| (mods, uenv) -> begin
(

let uu____848 = (tc_one_file_from_remaining remaining uenv)
in (match (uu____848) with
| (remaining1, nmods, (dsenv, env)) -> begin
(tc_fold_interleave (((FStar_List.append mods nmods)), (((dsenv), (env)))) remaining1)
end))
end))
end))


let batch_mode_tc_no_prims : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env filenames -> (

let uu____901 = (tc_fold_interleave (([]), (((dsenv), (env)))) filenames)
in (match (uu____901) with
| (all_mods, (dsenv1, env1)) -> begin
((

let uu____932 = ((FStar_Options.interactive ()) && (

let uu____933 = (FStar_Errors.get_err_count ())
in (uu____933 = (Prims.parse_int "0"))))
in (match (uu____932) with
| true -> begin
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end
| uu____934 -> begin
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end));
((all_mods), (dsenv1), (env1));
)
end)))


let batch_mode_tc : Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun filenames -> (

let uu____949 = (tc_prims ())
in (match (uu____949) with
| (prims_mod, dsenv, env) -> begin
((

let uu____969 = ((

let uu____970 = (FStar_Options.explicit_deps ())
in (not (uu____970))) && (FStar_Options.debug_any ()))
in (match (uu____969) with
| true -> begin
((FStar_Util.print_endline "Auto-deps kicked in; here\'s some info.");
(FStar_Util.print1 "Here\'s the list of filenames we will process: %s\n" (FStar_String.concat " " filenames));
(

let uu____973 = (

let uu____974 = (FStar_Options.verify_module ())
in (FStar_String.concat " " uu____974))
in (FStar_Util.print1 "Here\'s the list of modules we will verify: %s\n" uu____973));
)
end
| uu____976 -> begin
()
end));
(

let uu____977 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (uu____977) with
| (all_mods, dsenv1, env1) -> begin
(((prims_mod)::all_mods), (dsenv1), (env1))
end));
)
end)))




