
open Prims

let module_or_interface_name : FStar_Syntax_Syntax.modul  ->  (Prims.bool * FStar_Ident.lident) = (fun m -> ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name)))


let parse : FStar_ToSyntax_Env.env  ->  Prims.string Prims.option  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env pre_fn fn -> (

let uu____23 = (FStar_Parser_Driver.parse_file fn)
in (match (uu____23) with
| (ast, uu____33) -> begin
(

let uu____40 = (match (pre_fn) with
| None -> begin
((env), (ast))
end
| Some (pre_fn1) -> begin
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
(Prims.raise (FStar_Errors.Err ("mismatch between pre-module and module\n")))
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

let uu___232_111 = FStar_SMTEncoding_Solver.solver
in {FStar_TypeChecker_Env.init = uu___232_111.FStar_TypeChecker_Env.init; FStar_TypeChecker_Env.push = uu___232_111.FStar_TypeChecker_Env.push; FStar_TypeChecker_Env.pop = uu___232_111.FStar_TypeChecker_Env.pop; FStar_TypeChecker_Env.mark = uu___232_111.FStar_TypeChecker_Env.mark; FStar_TypeChecker_Env.reset_mark = uu___232_111.FStar_TypeChecker_Env.reset_mark; FStar_TypeChecker_Env.commit_mark = uu___232_111.FStar_TypeChecker_Env.commit_mark; FStar_TypeChecker_Env.encode_modul = uu___232_111.FStar_TypeChecker_Env.encode_modul; FStar_TypeChecker_Env.encode_sig = uu___232_111.FStar_TypeChecker_Env.encode_sig; FStar_TypeChecker_Env.preprocess = FStar_Tactics_Interpreter.preprocess; FStar_TypeChecker_Env.solve = uu___232_111.FStar_TypeChecker_Env.solve; FStar_TypeChecker_Env.is_trivial = uu___232_111.FStar_TypeChecker_Env.is_trivial; FStar_TypeChecker_Env.finish = uu___232_111.FStar_TypeChecker_Env.finish; FStar_TypeChecker_Env.refresh = uu___232_111.FStar_TypeChecker_Env.refresh})
end))
in (

let env = (FStar_TypeChecker_Env.initial_env FStar_TypeChecker_TcTerm.type_of_tot_term FStar_TypeChecker_TcTerm.universe_of solver1 FStar_Syntax_Const.prims_lid)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env);
(

let prims_filename = (FStar_Options.prims ())
in (

let uu____115 = (

let uu____119 = (FStar_ToSyntax_Env.empty_env ())
in (parse uu____119 None prims_filename))
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


let tc_one_fragment : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  (FStar_Parser_ParseIt.input_frag * Prims.bool)  ->  (FStar_Syntax_Syntax.modul Prims.option * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) Prims.option = (fun curmod dsenv env uu____169 -> (match (uu____169) with
| (frag, is_interface_dependence) -> begin
try
(match (()) with
| () -> begin
(

let uu____191 = (FStar_Parser_Driver.parse_fragment frag)
in (match (uu____191) with
| FStar_Parser_Driver.Empty -> begin
Some (((curmod), (dsenv), (env)))
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
| Some (modul1) -> begin
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
(Prims.raise (FStar_Errors.Err ("Interactive mode only supports a single module at the top-level")))
end
| uu____234 -> begin
env
end))
end
| None -> begin
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
Some (((Some (modul1)), (dsenv2), (env2)))
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
| None -> begin
((FStar_Util.print_error "fragment without an enclosing module");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| Some (modul) -> begin
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
Some (((Some (modul1)), (dsenv2), (env1)))
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
None;
)
end
| FStar_Errors.Err (msg) when (

let uu____349 = (FStar_Options.trace_error ())
in (not (uu____349))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (FStar_Range.dummyRange)))::[]));
None;
)
end
| e when (

let uu____360 = (FStar_Options.trace_error ())
in (not (uu____360))) -> begin
(Prims.raise e)
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
in (Prims.raise uu____444))
end
| FStar_Util.Inr (err1, rng) -> begin
(Prims.raise (FStar_Errors.Error (((err1), (rng)))))
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
(Prims.raise e)
end
end))


let tc_one_file : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.option  ->  Prims.string  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env pre_fn fn -> (

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
in (FStar_All.pipe_right uu____648 Prims.ignore));
(

let uu____650 = (FStar_TypeChecker_Env.pop env msg)
in (FStar_All.pipe_right uu____650 Prims.ignore));
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


let tc_one_file_and_intf : Prims.string Prims.option  ->  Prims.string  ->  FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun intf impl dsenv env -> ((FStar_Syntax_Syntax.reset_gensym ());
(match (intf) with
| None -> begin
(tc_one_file dsenv env None impl)
end
| Some (uu____696) when (

let uu____697 = (FStar_Options.codegen ())
in (uu____697 <> None)) -> begin
((

let uu____701 = (

let uu____702 = (FStar_Options.lax ())
in (not (uu____702)))
in (match (uu____701) with
| true -> begin
(Prims.raise (FStar_Errors.Err ("Verification and code generation are no supported together with partial modules (i.e, *.fsti); use --lax to extract code separately")))
end
| uu____703 -> begin
()
end));
(tc_one_file dsenv env intf impl);
)
end
| Some (iname) -> begin
((

let uu____706 = (FStar_Options.debug_any ())
in (match (uu____706) with
| true -> begin
(FStar_Util.print1 "Interleaving iface+module: %s\n" iname)
end
| uu____707 -> begin
()
end));
(

let caption = (Prims.strcat "interface: " iname)
in (

let uu____709 = (push_context ((dsenv), (env)) caption)
in (match (uu____709) with
| (dsenv', env') -> begin
(

let uu____720 = (tc_one_file dsenv' env' intf impl)
in (match (uu____720) with
| (uu____733, dsenv'1, env'1) -> begin
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

let uu____762 = uenv
in (match (uu____762) with
| (dsenv, env) -> begin
(

let uu____774 = (match (remaining) with
| (intf)::(impl)::remaining1 when (needs_interleaving intf impl) -> begin
(

let uu____797 = (tc_one_file_and_intf (Some (intf)) impl dsenv env)
in ((remaining1), (uu____797)))
end
| (intf_or_impl)::remaining1 -> begin
(

let uu____814 = (tc_one_file_and_intf None intf_or_impl dsenv env)
in ((remaining1), (uu____814)))
end
| [] -> begin
(([]), ((([]), (dsenv), (env))))
end)
in (match (uu____774) with
| (remaining1, (nmods, dsenv1, env1)) -> begin
((remaining1), (nmods), (((dsenv1), (env1))))
end))
end)))


let rec tc_fold_interleave : ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * uenv)  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * uenv) = (fun acc remaining -> (match (remaining) with
| [] -> begin
acc
end
| uu____901 -> begin
(

let uu____903 = acc
in (match (uu____903) with
| (mods, uenv) -> begin
(

let uu____922 = (tc_one_file_from_remaining remaining uenv)
in (match (uu____922) with
| (remaining1, nmods, (dsenv, env)) -> begin
(tc_fold_interleave (((FStar_List.append mods nmods)), (((dsenv), (env)))) remaining1)
end))
end))
end))


let batch_mode_tc_no_prims : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env filenames -> (

let uu____975 = (tc_fold_interleave (([]), (((dsenv), (env)))) filenames)
in (match (uu____975) with
| (all_mods, (dsenv1, env1)) -> begin
((

let uu____1006 = ((FStar_Options.interactive ()) && (

let uu____1007 = (FStar_Errors.get_err_count ())
in (uu____1007 = (Prims.parse_int "0"))))
in (match (uu____1006) with
| true -> begin
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end
| uu____1008 -> begin
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end));
((all_mods), (dsenv1), (env1));
)
end)))


let batch_mode_tc : Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun filenames -> (

let uu____1023 = (tc_prims ())
in (match (uu____1023) with
| (prims_mod, dsenv, env) -> begin
((

let uu____1043 = ((

let uu____1044 = (FStar_Options.explicit_deps ())
in (not (uu____1044))) && (FStar_Options.debug_any ()))
in (match (uu____1043) with
| true -> begin
((FStar_Util.print_endline "Auto-deps kicked in; here\'s some info.");
(FStar_Util.print1 "Here\'s the list of filenames we will process: %s\n" (FStar_String.concat " " filenames));
(

let uu____1047 = (

let uu____1048 = (FStar_Options.verify_module ())
in (FStar_String.concat " " uu____1048))
in (FStar_Util.print1 "Here\'s the list of modules we will verify: %s\n" uu____1047));
)
end
| uu____1050 -> begin
()
end));
(

let uu____1051 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (uu____1051) with
| (all_mods, dsenv1, env1) -> begin
(((prims_mod)::all_mods), (dsenv1), (env1))
end));
)
end)))




