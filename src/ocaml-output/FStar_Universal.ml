
open Prims
open FStar_Pervasives

let module_or_interface_name : FStar_Syntax_Syntax.modul  ->  (Prims.bool * FStar_Ident.lident) = (fun m -> ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name)))


let parse : FStar_ToSyntax_Env.env  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env pre_fn fn -> (

let uu____27 = (FStar_Parser_Driver.parse_file fn)
in (match (uu____27) with
| (ast, uu____37) -> begin
(

let uu____44 = (match (pre_fn) with
| FStar_Pervasives_Native.None -> begin
((env), (ast))
end
| FStar_Pervasives_Native.Some (pre_fn1) -> begin
(

let uu____50 = (FStar_Parser_Driver.parse_file pre_fn1)
in (match (uu____50) with
| (pre_ast, uu____59) -> begin
(match (((pre_ast), (ast))) with
| ((FStar_Parser_AST.Interface (lid1, decls1, uu____70))::[], (FStar_Parser_AST.Module (lid2, decls2))::[]) when (FStar_Ident.lid_equals lid1 lid2) -> begin
(

let env1 = (FStar_ToSyntax_Interleave.initialize_interface lid1 decls1 env)
in (

let uu____80 = (

let uu____83 = (FStar_List.hd ast)
in (FStar_ToSyntax_Interleave.interleave_module env1 uu____83 true))
in (match (uu____80) with
| (env2, ast1) -> begin
((env2), ((ast1)::[]))
end)))
end
| uu____89 -> begin
(FStar_Pervasives.raise (FStar_Errors.Err ("mismatch between pre-module and module\n")))
end)
end))
end)
in (match (uu____44) with
| (env1, ast1) -> begin
(FStar_ToSyntax_ToSyntax.desugar_file env1 ast1)
end))
end)))


let tc_prims : Prims.unit  ->  ((FStar_Syntax_Syntax.modul * Prims.int) * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____107 -> (

let solver1 = (

let uu____114 = (FStar_Options.lax ())
in (match (uu____114) with
| true -> begin
FStar_SMTEncoding_Solver.dummy
end
| uu____115 -> begin
(

let uu___175_116 = FStar_SMTEncoding_Solver.solver
in {FStar_TypeChecker_Env.init = uu___175_116.FStar_TypeChecker_Env.init; FStar_TypeChecker_Env.push = uu___175_116.FStar_TypeChecker_Env.push; FStar_TypeChecker_Env.pop = uu___175_116.FStar_TypeChecker_Env.pop; FStar_TypeChecker_Env.mark = uu___175_116.FStar_TypeChecker_Env.mark; FStar_TypeChecker_Env.reset_mark = uu___175_116.FStar_TypeChecker_Env.reset_mark; FStar_TypeChecker_Env.commit_mark = uu___175_116.FStar_TypeChecker_Env.commit_mark; FStar_TypeChecker_Env.encode_modul = uu___175_116.FStar_TypeChecker_Env.encode_modul; FStar_TypeChecker_Env.encode_sig = uu___175_116.FStar_TypeChecker_Env.encode_sig; FStar_TypeChecker_Env.preprocess = FStar_Tactics_Interpreter.preprocess; FStar_TypeChecker_Env.solve = uu___175_116.FStar_TypeChecker_Env.solve; FStar_TypeChecker_Env.is_trivial = uu___175_116.FStar_TypeChecker_Env.is_trivial; FStar_TypeChecker_Env.finish = uu___175_116.FStar_TypeChecker_Env.finish; FStar_TypeChecker_Env.refresh = uu___175_116.FStar_TypeChecker_Env.refresh})
end))
in (

let env = (FStar_TypeChecker_Env.initial_env FStar_TypeChecker_TcTerm.type_of_tot_term FStar_TypeChecker_TcTerm.universe_of solver1 FStar_Parser_Const.prims_lid)
in (

let env1 = (

let uu___176_119 = env
in {FStar_TypeChecker_Env.solver = uu___176_119.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___176_119.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___176_119.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___176_119.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___176_119.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___176_119.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___176_119.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___176_119.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___176_119.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___176_119.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___176_119.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___176_119.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___176_119.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___176_119.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___176_119.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___176_119.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___176_119.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___176_119.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___176_119.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___176_119.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___176_119.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___176_119.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___176_119.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___176_119.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___176_119.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = FStar_Tactics_Interpreter.synth; FStar_TypeChecker_Env.is_native_tactic = uu___176_119.FStar_TypeChecker_Env.is_native_tactic})
in (

let env2 = (

let uu___177_121 = env1
in {FStar_TypeChecker_Env.solver = uu___177_121.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___177_121.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___177_121.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___177_121.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___177_121.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___177_121.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___177_121.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___177_121.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___177_121.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___177_121.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___177_121.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___177_121.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___177_121.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___177_121.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___177_121.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___177_121.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___177_121.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___177_121.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___177_121.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___177_121.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___177_121.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___177_121.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___177_121.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___177_121.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___177_121.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___177_121.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = FStar_Tactics_Native.is_native_tactic})
in ((env2.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env2);
(

let prims_filename = (FStar_Options.prims ())
in (

let uu____124 = (

let uu____128 = (FStar_ToSyntax_Env.empty_env ())
in (parse uu____128 FStar_Pervasives_Native.None prims_filename))
in (match (uu____124) with
| (dsenv, prims_mod) -> begin
(

let uu____138 = (FStar_Util.record_time (fun uu____147 -> (

let uu____148 = (FStar_List.hd prims_mod)
in (FStar_TypeChecker_Tc.check_module env2 uu____148))))
in (match (uu____138) with
| ((prims_mod1, env3), elapsed_time) -> begin
((((prims_mod1), (elapsed_time))), (dsenv), (env3))
end))
end)));
))))))


let tc_one_fragment : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  (FStar_Parser_ParseIt.input_frag * Prims.bool)  ->  (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) FStar_Pervasives_Native.option = (fun curmod dsenv env uu____184 -> (match (uu____184) with
| (frag, is_interface_dependence) -> begin
try
(match (()) with
| () -> begin
(

let uu____208 = (FStar_Parser_Driver.parse_fragment frag)
in (match (uu____208) with
| FStar_Parser_Driver.Empty -> begin
FStar_Pervasives_Native.Some (((curmod), (dsenv), (env)))
end
| FStar_Parser_Driver.Modul (ast_modul) -> begin
(

let uu____220 = (FStar_ToSyntax_Interleave.interleave_module dsenv ast_modul false)
in (match (uu____220) with
| (ds_env, ast_modul1) -> begin
(

let uu____230 = (FStar_ToSyntax_ToSyntax.desugar_partial_modul curmod dsenv ast_modul1)
in (match (uu____230) with
| (dsenv1, modul) -> begin
(

let dsenv2 = (match (is_interface_dependence) with
| true -> begin
(FStar_ToSyntax_Env.set_iface dsenv1 false)
end
| uu____241 -> begin
dsenv1
end)
in (

let env1 = (match (curmod) with
| FStar_Pervasives_Native.Some (modul1) -> begin
(

let uu____244 = (

let uu____245 = (

let uu____246 = (

let uu____247 = (FStar_Options.file_list ())
in (FStar_List.hd uu____247))
in (FStar_Parser_Dep.lowercase_module_name uu____246))
in (

let uu____249 = (

let uu____250 = (FStar_Ident.string_of_lid modul1.FStar_Syntax_Syntax.name)
in (FStar_String.lowercase uu____250))
in (uu____245 <> uu____249)))
in (match (uu____244) with
| true -> begin
(FStar_Pervasives.raise (FStar_Errors.Err ("Interactive mode only supports a single module at the top-level")))
end
| uu____251 -> begin
env
end))
end
| FStar_Pervasives_Native.None -> begin
env
end)
in (

let uu____252 = (

let uu____257 = (FStar_ToSyntax_Env.syntax_only dsenv2)
in (match (uu____257) with
| true -> begin
((modul), ([]), (env1))
end
| uu____263 -> begin
(FStar_TypeChecker_Tc.tc_partial_modul env1 modul)
end))
in (match (uu____252) with
| (modul1, uu____270, env2) -> begin
FStar_Pervasives_Native.Some (((FStar_Pervasives_Native.Some (modul1)), (dsenv2), (env2)))
end))))
end))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(

let uu____281 = (FStar_Util.fold_map FStar_ToSyntax_Interleave.prefix_with_interface_decls dsenv ast_decls)
in (match (uu____281) with
| (dsenv1, ast_decls_l) -> begin
(

let uu____298 = (FStar_ToSyntax_ToSyntax.desugar_decls dsenv1 (FStar_List.flatten ast_decls_l))
in (match (uu____298) with
| (dsenv2, decls) -> begin
(match (curmod) with
| FStar_Pervasives_Native.None -> begin
((FStar_Util.print_error "fragment without an enclosing module");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| FStar_Pervasives_Native.Some (modul) -> begin
(

let uu____320 = (

let uu____325 = (FStar_ToSyntax_Env.syntax_only dsenv2)
in (match (uu____325) with
| true -> begin
((modul), ([]), (env))
end
| uu____331 -> begin
(FStar_TypeChecker_Tc.tc_more_partial_modul env modul decls)
end))
in (match (uu____320) with
| (modul1, uu____338, env1) -> begin
FStar_Pervasives_Native.Some (((FStar_Pervasives_Native.Some (modul1)), (dsenv2), (env1)))
end))
end)
end))
end))
end))
end)
with
| FStar_Errors.Error (msg, r) when (

let uu____359 = (FStar_Options.trace_error ())
in (not (uu____359))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]));
FStar_Pervasives_Native.None;
)
end
| FStar_Errors.Err (msg) when (

let uu____370 = (FStar_Options.trace_error ())
in (not (uu____370))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (FStar_Range.dummyRange)))::[]));
FStar_Pervasives_Native.None;
)
end
| e when (

let uu____381 = (FStar_Options.trace_error ())
in (not (uu____381))) -> begin
(FStar_Pervasives.raise e)
end
end))


let load_interface_decls : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  FStar_Parser_ParseIt.filename  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____397 interface_file_name -> (match (uu____397) with
| (dsenv, env) -> begin
try
(match (()) with
| () -> begin
(

let r = (FStar_Parser_ParseIt.parse (FStar_Util.Inl (interface_file_name)))
in (match (r) with
| FStar_Util.Inl (FStar_Util.Inl ((FStar_Parser_AST.Interface (l, decls, uu____433))::[]), uu____434) -> begin
(

let uu____460 = (FStar_ToSyntax_Interleave.initialize_interface l decls dsenv)
in ((uu____460), (env)))
end
| FStar_Util.Inl (uu____461) -> begin
(

let uu____474 = (

let uu____475 = (FStar_Util.format1 "Unexpected result from parsing %s; expected a single interface" interface_file_name)
in FStar_Errors.Err (uu____475))
in (FStar_Pervasives.raise uu____474))
end
| FStar_Util.Inr (err1, rng) -> begin
(FStar_Pervasives.raise (FStar_Errors.Error (((err1), (rng)))))
end))
end)
with
| FStar_Errors.Error (msg, r) when (

let uu____498 = (FStar_Options.trace_error ())
in (not (uu____498))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]));
((dsenv), (env));
)
end
| FStar_Errors.Err (msg) when (

let uu____505 = (FStar_Options.trace_error ())
in (not (uu____505))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (FStar_Range.dummyRange)))::[]));
((dsenv), (env));
)
end
| e when (

let uu____512 = (FStar_Options.trace_error ())
in (not (uu____512))) -> begin
(FStar_Pervasives.raise e)
end
end))


let tc_one_file : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env pre_fn fn -> (

let uu____545 = (parse dsenv pre_fn fn)
in (match (uu____545) with
| (dsenv1, fmods) -> begin
(

let check_mods = (fun uu____568 -> (

let uu____569 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun uu____594 m -> (match (uu____594) with
| (env1, all_mods) -> begin
(

let uu____614 = (FStar_Util.record_time (fun uu____622 -> (FStar_TypeChecker_Tc.check_module env1 m)))
in (match (uu____614) with
| ((m1, env2), elapsed_ms) -> begin
((env2), ((((m1), (elapsed_ms)))::all_mods))
end))
end)) ((env), ([]))))
in (match (uu____569) with
| (env1, all_mods) -> begin
(((FStar_List.rev all_mods)), (dsenv1), (env1))
end)))
in (match (fmods) with
| (m)::[] when ((FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str) && ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))) -> begin
(

let uu____669 = (FStar_Parser_ParseIt.find_file fn)
in (FStar_SMTEncoding_Solver.with_hints_db uu____669 check_mods))
end
| uu____676 -> begin
(check_mods ())
end))
end)))


let needs_interleaving : Prims.string  ->  Prims.string  ->  Prims.bool = (fun intf impl -> (

let m1 = (FStar_Parser_Dep.lowercase_module_name intf)
in (

let m2 = (FStar_Parser_Dep.lowercase_module_name impl)
in (((m1 = m2) && (

let uu____689 = (FStar_Util.get_file_extension intf)
in (uu____689 = "fsti"))) && (

let uu____691 = (FStar_Util.get_file_extension impl)
in (uu____691 = "fst"))))))


let pop_context : FStar_TypeChecker_Env.env  ->  Prims.string  ->  Prims.unit = (fun env msg -> ((

let uu____701 = (FStar_ToSyntax_Env.pop ())
in (FStar_All.pipe_right uu____701 FStar_Pervasives.ignore));
(

let uu____703 = (FStar_TypeChecker_Env.pop env msg)
in (FStar_All.pipe_right uu____703 FStar_Pervasives.ignore));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
))


let push_context : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____714 msg -> (match (uu____714) with
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

let uu____745 = uenv
in (match (uu____745) with
| (dsenv, env) -> begin
(

let uu____757 = (match (remaining) with
| (intf)::(impl)::remaining1 when (needs_interleaving intf impl) -> begin
(

let uu____780 = (tc_one_file dsenv env (FStar_Pervasives_Native.Some (intf)) impl)
in ((remaining1), (uu____780)))
end
| (intf_or_impl)::remaining1 -> begin
(

let uu____797 = (tc_one_file dsenv env FStar_Pervasives_Native.None intf_or_impl)
in ((remaining1), (uu____797)))
end
| [] -> begin
(([]), ((([]), (dsenv), (env))))
end)
in (match (uu____757) with
| (remaining1, (nmods, dsenv1, env1)) -> begin
((remaining1), (nmods), (((dsenv1), (env1))))
end))
end)))


let rec tc_fold_interleave : ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * uenv)  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * uenv) = (fun acc remaining -> (match (remaining) with
| [] -> begin
acc
end
| uu____886 -> begin
(

let uu____888 = acc
in (match (uu____888) with
| (mods, uenv) -> begin
(

let uu____907 = (tc_one_file_from_remaining remaining uenv)
in (match (uu____907) with
| (remaining1, nmods, (dsenv, env)) -> begin
(tc_fold_interleave (((FStar_List.append mods nmods)), (((dsenv), (env)))) remaining1)
end))
end))
end))


let batch_mode_tc_no_prims : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env filenames -> (

let uu____963 = (tc_fold_interleave (([]), (((dsenv), (env)))) filenames)
in (match (uu____963) with
| (all_mods, (dsenv1, env1)) -> begin
((

let uu____994 = ((FStar_Options.interactive ()) && (

let uu____996 = (FStar_Errors.get_err_count ())
in (uu____996 = (Prims.parse_int "0"))))
in (match (uu____994) with
| true -> begin
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end
| uu____997 -> begin
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end));
((all_mods), (dsenv1), (env1));
)
end)))


let batch_mode_tc : Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun filenames -> (

let uu____1013 = (tc_prims ())
in (match (uu____1013) with
| (prims_mod, dsenv, env) -> begin
((

let uu____1033 = ((

let uu____1036 = (FStar_Options.explicit_deps ())
in (not (uu____1036))) && (FStar_Options.debug_any ()))
in (match (uu____1033) with
| true -> begin
((FStar_Util.print_endline "Auto-deps kicked in; here\'s some info.");
(FStar_Util.print1 "Here\'s the list of filenames we will process: %s\n" (FStar_String.concat " " filenames));
(

let uu____1039 = (

let uu____1040 = (FStar_Options.verify_module ())
in (FStar_String.concat " " uu____1040))
in (FStar_Util.print1 "Here\'s the list of modules we will verify: %s\n" uu____1039));
)
end
| uu____1042 -> begin
()
end));
(

let uu____1043 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (uu____1043) with
| (all_mods, dsenv1, env1) -> begin
(((prims_mod)::all_mods), (dsenv1), (env1))
end));
)
end)))




