
open Prims
open FStar_Pervasives

let module_or_interface_name : FStar_Syntax_Syntax.modul  ->  (Prims.bool * FStar_Ident.lident) = (fun m -> ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name)))


let parse : FStar_ToSyntax_Env.env  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env pre_fn fn -> (

let uu____37 = (FStar_Parser_Driver.parse_file fn)
in (match (uu____37) with
| (ast, uu____55) -> begin
(

let uu____68 = (match (pre_fn) with
| FStar_Pervasives_Native.None -> begin
((env), (ast))
end
| FStar_Pervasives_Native.Some (pre_fn1) -> begin
(

let uu____78 = (FStar_Parser_Driver.parse_file pre_fn1)
in (match (uu____78) with
| (pre_ast, uu____94) -> begin
(match (((pre_ast), (ast))) with
| ((FStar_Parser_AST.Interface (lid1, decls1, uu____113))::[], (FStar_Parser_AST.Module (lid2, decls2))::[]) when (FStar_Ident.lid_equals lid1 lid2) -> begin
(

let env1 = (FStar_ToSyntax_Interleave.initialize_interface lid1 decls1 env)
in (

let uu____129 = (

let uu____134 = (FStar_List.hd ast)
in (FStar_ToSyntax_Interleave.interleave_module env1 uu____134 true))
in (match (uu____129) with
| (env2, ast1) -> begin
((env2), ((ast1)::[]))
end)))
end
| uu____143 -> begin
(FStar_Exn.raise (FStar_Errors.Err ("mismatch between pre-module and module\n")))
end)
end))
end)
in (match (uu____68) with
| (env1, ast1) -> begin
(FStar_ToSyntax_ToSyntax.desugar_file env1 ast1)
end))
end)))


let tc_prims : Prims.unit  ->  ((FStar_Syntax_Syntax.modul * Prims.int) * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____173 -> (

let solver1 = (

let uu____185 = (FStar_Options.lax ())
in (match (uu____185) with
| true -> begin
FStar_SMTEncoding_Solver.dummy
end
| uu____186 -> begin
(

let uu___186_187 = FStar_SMTEncoding_Solver.solver
in {FStar_TypeChecker_Env.init = uu___186_187.FStar_TypeChecker_Env.init; FStar_TypeChecker_Env.push = uu___186_187.FStar_TypeChecker_Env.push; FStar_TypeChecker_Env.pop = uu___186_187.FStar_TypeChecker_Env.pop; FStar_TypeChecker_Env.mark = uu___186_187.FStar_TypeChecker_Env.mark; FStar_TypeChecker_Env.reset_mark = uu___186_187.FStar_TypeChecker_Env.reset_mark; FStar_TypeChecker_Env.commit_mark = uu___186_187.FStar_TypeChecker_Env.commit_mark; FStar_TypeChecker_Env.encode_modul = uu___186_187.FStar_TypeChecker_Env.encode_modul; FStar_TypeChecker_Env.encode_sig = uu___186_187.FStar_TypeChecker_Env.encode_sig; FStar_TypeChecker_Env.preprocess = FStar_Tactics_Interpreter.preprocess; FStar_TypeChecker_Env.solve = uu___186_187.FStar_TypeChecker_Env.solve; FStar_TypeChecker_Env.is_trivial = uu___186_187.FStar_TypeChecker_Env.is_trivial; FStar_TypeChecker_Env.finish = uu___186_187.FStar_TypeChecker_Env.finish; FStar_TypeChecker_Env.refresh = uu___186_187.FStar_TypeChecker_Env.refresh})
end))
in (

let env = (FStar_TypeChecker_Env.initial_env FStar_TypeChecker_TcTerm.type_of_tot_term FStar_TypeChecker_TcTerm.universe_of solver1 FStar_Parser_Const.prims_lid)
in (

let env1 = (

let uu___187_190 = env
in {FStar_TypeChecker_Env.solver = uu___187_190.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___187_190.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___187_190.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___187_190.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___187_190.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___187_190.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___187_190.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___187_190.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___187_190.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___187_190.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___187_190.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___187_190.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___187_190.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___187_190.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___187_190.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___187_190.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___187_190.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___187_190.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___187_190.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___187_190.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___187_190.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.type_of = uu___187_190.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___187_190.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___187_190.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___187_190.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___187_190.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = FStar_Tactics_Interpreter.synth; FStar_TypeChecker_Env.is_native_tactic = uu___187_190.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___187_190.FStar_TypeChecker_Env.identifier_info})
in (

let env2 = (

let uu___188_192 = env1
in {FStar_TypeChecker_Env.solver = uu___188_192.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___188_192.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___188_192.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___188_192.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___188_192.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___188_192.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___188_192.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___188_192.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___188_192.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___188_192.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___188_192.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___188_192.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___188_192.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___188_192.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___188_192.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___188_192.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___188_192.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___188_192.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___188_192.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___188_192.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___188_192.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.type_of = uu___188_192.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___188_192.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___188_192.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___188_192.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___188_192.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___188_192.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = FStar_Tactics_Native.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___188_192.FStar_TypeChecker_Env.identifier_info})
in ((env2.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env2);
(

let prims_filename = (FStar_Options.prims ())
in (

let uu____195 = (

let uu____202 = (FStar_ToSyntax_Env.empty_env ())
in (parse uu____202 FStar_Pervasives_Native.None prims_filename))
in (match (uu____195) with
| (dsenv, prims_mod) -> begin
(

let uu____219 = (FStar_Util.record_time (fun uu____234 -> (

let uu____235 = (FStar_List.hd prims_mod)
in (FStar_TypeChecker_Tc.check_module env2 uu____235))))
in (match (uu____219) with
| ((prims_mod1, env3), elapsed_time) -> begin
((((prims_mod1), (elapsed_time))), (dsenv), (env3))
end))
end)));
))))))


let tc_one_fragment : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  (FStar_Parser_ParseIt.input_frag * Prims.bool)  ->  (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) FStar_Pervasives_Native.option = (fun curmod dsenv env uu____288 -> (match (uu____288) with
| (frag, is_interface_dependence) -> begin
try
(match (()) with
| () -> begin
(

let uu____330 = (FStar_Parser_Driver.parse_fragment frag)
in (match (uu____330) with
| FStar_Parser_Driver.Empty -> begin
FStar_Pervasives_Native.Some (((curmod), (dsenv), (env)))
end
| FStar_Parser_Driver.Modul (ast_modul) -> begin
(

let uu____352 = (FStar_ToSyntax_Interleave.interleave_module dsenv ast_modul false)
in (match (uu____352) with
| (ds_env, ast_modul1) -> begin
(

let uu____369 = (FStar_ToSyntax_ToSyntax.desugar_partial_modul curmod dsenv ast_modul1)
in (match (uu____369) with
| (dsenv1, modul) -> begin
(

let dsenv2 = (match (is_interface_dependence) with
| true -> begin
(FStar_ToSyntax_Env.set_iface dsenv1 false)
end
| uu____387 -> begin
dsenv1
end)
in (

let env1 = (match (curmod) with
| FStar_Pervasives_Native.Some (modul1) -> begin
(

let uu____390 = (

let uu____391 = (

let uu____392 = (

let uu____393 = (FStar_Options.file_list ())
in (FStar_List.hd uu____393))
in (FStar_Parser_Dep.lowercase_module_name uu____392))
in (

let uu____396 = (

let uu____397 = (FStar_Ident.string_of_lid modul1.FStar_Syntax_Syntax.name)
in (FStar_String.lowercase uu____397))
in (uu____391 <> uu____396)))
in (match (uu____390) with
| true -> begin
(FStar_Exn.raise (FStar_Errors.Err ("Interactive mode only supports a single module at the top-level")))
end
| uu____398 -> begin
env
end))
end
| FStar_Pervasives_Native.None -> begin
env
end)
in (

let uu____399 = (

let uu____408 = (FStar_ToSyntax_Env.syntax_only dsenv2)
in (match (uu____408) with
| true -> begin
((modul), ([]), (env1))
end
| uu____419 -> begin
(FStar_TypeChecker_Tc.tc_partial_modul env1 modul)
end))
in (match (uu____399) with
| (modul1, uu____431, env2) -> begin
FStar_Pervasives_Native.Some (((FStar_Pervasives_Native.Some (modul1)), (dsenv2), (env2)))
end))))
end))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(

let uu____450 = (FStar_Util.fold_map FStar_ToSyntax_Interleave.prefix_with_interface_decls dsenv ast_decls)
in (match (uu____450) with
| (dsenv1, ast_decls_l) -> begin
(

let uu____481 = (FStar_ToSyntax_ToSyntax.desugar_decls dsenv1 (FStar_List.flatten ast_decls_l))
in (match (uu____481) with
| (dsenv2, decls) -> begin
(match (curmod) with
| FStar_Pervasives_Native.None -> begin
((FStar_Util.print_error "fragment without an enclosing module");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| FStar_Pervasives_Native.Some (modul) -> begin
(

let uu____520 = (

let uu____529 = (FStar_ToSyntax_Env.syntax_only dsenv2)
in (match (uu____529) with
| true -> begin
((modul), ([]), (env))
end
| uu____540 -> begin
(FStar_TypeChecker_Tc.tc_more_partial_modul env modul decls)
end))
in (match (uu____520) with
| (modul1, uu____552, env1) -> begin
FStar_Pervasives_Native.Some (((FStar_Pervasives_Native.Some (modul1)), (dsenv2), (env1)))
end))
end)
end))
end))
end))
end)
with
| FStar_Errors.Error (msg, r) when (

let uu____585 = (FStar_Options.trace_error ())
in (not (uu____585))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]));
FStar_Pervasives_Native.None;
)
end
| FStar_Errors.Err (msg) when (

let uu____604 = (FStar_Options.trace_error ())
in (not (uu____604))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (FStar_Range.dummyRange)))::[]));
FStar_Pervasives_Native.None;
)
end
| e when (

let uu____623 = (FStar_Options.trace_error ())
in (not (uu____623))) -> begin
(FStar_Exn.raise e)
end
end))


let load_interface_decls : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  FStar_Parser_ParseIt.filename  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____648 interface_file_name -> (match (uu____648) with
| (dsenv, env) -> begin
try
(match (()) with
| () -> begin
(

let r = (FStar_Parser_ParseIt.parse (FStar_Util.Inl (interface_file_name)))
in (match (r) with
| FStar_Util.Inl (FStar_Util.Inl ((FStar_Parser_AST.Interface (l, decls, uu____705))::[]), uu____706) -> begin
(

let uu____757 = (FStar_ToSyntax_Interleave.initialize_interface l decls dsenv)
in ((uu____757), (env)))
end
| FStar_Util.Inl (uu____758) -> begin
(

let uu____783 = (

let uu____784 = (FStar_Util.format1 "Unexpected result from parsing %s; expected a single interface" interface_file_name)
in FStar_Errors.Err (uu____784))
in (FStar_Exn.raise uu____783))
end
| FStar_Util.Inr (err1, rng) -> begin
(FStar_Exn.raise (FStar_Errors.Error (((err1), (rng)))))
end))
end)
with
| FStar_Errors.Error (msg, r) when (

let uu____820 = (FStar_Options.trace_error ())
in (not (uu____820))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]));
((dsenv), (env));
)
end
| FStar_Errors.Err (msg) when (

let uu____831 = (FStar_Options.trace_error ())
in (not (uu____831))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (FStar_Range.dummyRange)))::[]));
((dsenv), (env));
)
end
| e when (

let uu____842 = (FStar_Options.trace_error ())
in (not (uu____842))) -> begin
(FStar_Exn.raise e)
end
end))


let tc_one_file : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env pre_fn fn -> (

let uu____891 = (parse dsenv pre_fn fn)
in (match (uu____891) with
| (dsenv1, fmods) -> begin
(

let check_mods = (fun uu____931 -> (

let uu____932 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun uu____973 m -> (match (uu____973) with
| (env1, all_mods) -> begin
(

let uu____1009 = (FStar_Util.record_time (fun uu____1023 -> (FStar_TypeChecker_Tc.check_module env1 m)))
in (match (uu____1009) with
| ((m1, env2), elapsed_ms) -> begin
((env2), ((((m1), (elapsed_ms)))::all_mods))
end))
end)) ((env), ([]))))
in (match (uu____932) with
| (env1, all_mods) -> begin
(((FStar_List.rev all_mods)), (dsenv1), (env1))
end)))
in (match (fmods) with
| (m)::[] when ((FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str) && ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))) -> begin
(

let uu____1110 = (FStar_Parser_ParseIt.find_file fn)
in (FStar_SMTEncoding_Solver.with_hints_db uu____1110 check_mods))
end
| uu____1123 -> begin
(check_mods ())
end))
end)))


let needs_interleaving : Prims.string  ->  Prims.string  ->  Prims.bool = (fun intf impl -> (

let m1 = (FStar_Parser_Dep.lowercase_module_name intf)
in (

let m2 = (FStar_Parser_Dep.lowercase_module_name impl)
in (((m1 = m2) && (

let uu____1137 = (FStar_Util.get_file_extension intf)
in (FStar_List.mem uu____1137 (("fsti")::("fsi")::[])))) && (

let uu____1139 = (FStar_Util.get_file_extension impl)
in (FStar_List.mem uu____1139 (("fst")::("fs")::[])))))))


let pop_context : FStar_TypeChecker_Env.env  ->  Prims.string  ->  Prims.unit = (fun env msg -> ((

let uu____1149 = (FStar_ToSyntax_Env.pop ())
in (FStar_All.pipe_right uu____1149 FStar_Pervasives.ignore));
(

let uu____1151 = (FStar_TypeChecker_Env.pop env msg)
in (FStar_All.pipe_right uu____1151 FStar_Pervasives.ignore));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
))


let push_context : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____1166 msg -> (match (uu____1166) with
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

let uu____1214 = uenv
in (match (uu____1214) with
| (dsenv, env) -> begin
(

let uu____1235 = (match (remaining) with
| (intf)::(impl)::remaining1 when (needs_interleaving intf impl) -> begin
(

let uu____1277 = (tc_one_file dsenv env (FStar_Pervasives_Native.Some (intf)) impl)
in ((remaining1), (uu____1277)))
end
| (intf_or_impl)::remaining1 -> begin
(

let uu____1308 = (tc_one_file dsenv env FStar_Pervasives_Native.None intf_or_impl)
in ((remaining1), (uu____1308)))
end
| [] -> begin
(([]), ((([]), (dsenv), (env))))
end)
in (match (uu____1235) with
| (remaining1, (nmods, dsenv1, env1)) -> begin
((remaining1), (nmods), (((dsenv1), (env1))))
end))
end)))


let rec tc_fold_interleave : ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * uenv)  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * uenv) = (fun acc remaining -> (match (remaining) with
| [] -> begin
acc
end
| uu____1473 -> begin
(

let uu____1476 = acc
in (match (uu____1476) with
| (mods, uenv) -> begin
(

let uu____1511 = (tc_one_file_from_remaining remaining uenv)
in (match (uu____1511) with
| (remaining1, nmods, (dsenv, env)) -> begin
(tc_fold_interleave (((FStar_List.append mods nmods)), (((dsenv), (env)))) remaining1)
end))
end))
end))


let batch_mode_tc_no_prims : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env filenames -> (

let uu____1606 = (tc_fold_interleave (([]), (((dsenv), (env)))) filenames)
in (match (uu____1606) with
| (all_mods, (dsenv1, env1)) -> begin
((

let uu____1663 = ((FStar_Options.interactive ()) && (

let uu____1665 = (FStar_Errors.get_err_count ())
in (uu____1665 = (Prims.parse_int "0"))))
in (match (uu____1663) with
| true -> begin
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end
| uu____1666 -> begin
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end));
((all_mods), (dsenv1), (env1));
)
end)))


let batch_mode_tc : Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun filenames -> (

let uu____1693 = (tc_prims ())
in (match (uu____1693) with
| (prims_mod, dsenv, env) -> begin
((

let uu____1728 = ((

let uu____1731 = (FStar_Options.explicit_deps ())
in (not (uu____1731))) && (FStar_Options.debug_any ()))
in (match (uu____1728) with
| true -> begin
((FStar_Util.print_endline "Auto-deps kicked in; here\'s some info.");
(FStar_Util.print1 "Here\'s the list of filenames we will process: %s\n" (FStar_String.concat " " filenames));
(

let uu____1734 = (

let uu____1735 = (FStar_Options.verify_module ())
in (FStar_String.concat " " uu____1735))
in (FStar_Util.print1 "Here\'s the list of modules we will verify: %s\n" uu____1734));
)
end
| uu____1738 -> begin
()
end));
(

let uu____1739 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (uu____1739) with
| (all_mods, dsenv1, env1) -> begin
(((prims_mod)::all_mods), (dsenv1), (env1))
end));
)
end)))




