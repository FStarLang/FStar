
open Prims
open FStar_Pervasives

let module_or_interface_name : FStar_Syntax_Syntax.modul  ->  (Prims.bool * FStar_Ident.lident) = (fun m -> ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name)))


let parse : FStar_ToSyntax_Env.env  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul) = (fun env pre_fn fn -> (

let uu____33 = (FStar_Parser_Driver.parse_file fn)
in (match (uu____33) with
| (ast, uu____49) -> begin
(

let uu____62 = (match (pre_fn) with
| FStar_Pervasives_Native.None -> begin
((env), (ast))
end
| FStar_Pervasives_Native.Some (pre_fn1) -> begin
(

let uu____72 = (FStar_Parser_Driver.parse_file pre_fn1)
in (match (uu____72) with
| (pre_ast, uu____88) -> begin
(match (((pre_ast), (ast))) with
| (FStar_Parser_AST.Interface (lid1, decls1, uu____107), FStar_Parser_AST.Module (lid2, decls2)) when (FStar_Ident.lid_equals lid1 lid2) -> begin
(

let env1 = (FStar_ToSyntax_Interleave.initialize_interface lid1 decls1 env)
in (

let uu____119 = (FStar_ToSyntax_Interleave.interleave_module env1 ast true)
in (match (uu____119) with
| (env2, ast1) -> begin
((env2), (ast1))
end)))
end
| uu____130 -> begin
(FStar_Exn.raise (FStar_Errors.Err ("mismatch between pre-module and module\n")))
end)
end))
end)
in (match (uu____62) with
| (env1, ast1) -> begin
(FStar_ToSyntax_ToSyntax.desugar_modul env1 ast1)
end))
end)))


let tc_prims : Prims.unit  ->  ((FStar_Syntax_Syntax.modul * Prims.int) * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____158 -> (

let solver1 = (

let uu____170 = (FStar_Options.lax ())
in (match (uu____170) with
| true -> begin
FStar_SMTEncoding_Solver.dummy
end
| uu____171 -> begin
(

let uu___186_172 = FStar_SMTEncoding_Solver.solver
in {FStar_TypeChecker_Env.init = uu___186_172.FStar_TypeChecker_Env.init; FStar_TypeChecker_Env.push = uu___186_172.FStar_TypeChecker_Env.push; FStar_TypeChecker_Env.pop = uu___186_172.FStar_TypeChecker_Env.pop; FStar_TypeChecker_Env.mark = uu___186_172.FStar_TypeChecker_Env.mark; FStar_TypeChecker_Env.reset_mark = uu___186_172.FStar_TypeChecker_Env.reset_mark; FStar_TypeChecker_Env.commit_mark = uu___186_172.FStar_TypeChecker_Env.commit_mark; FStar_TypeChecker_Env.encode_modul = uu___186_172.FStar_TypeChecker_Env.encode_modul; FStar_TypeChecker_Env.encode_sig = uu___186_172.FStar_TypeChecker_Env.encode_sig; FStar_TypeChecker_Env.preprocess = FStar_Tactics_Interpreter.preprocess; FStar_TypeChecker_Env.solve = uu___186_172.FStar_TypeChecker_Env.solve; FStar_TypeChecker_Env.is_trivial = uu___186_172.FStar_TypeChecker_Env.is_trivial; FStar_TypeChecker_Env.finish = uu___186_172.FStar_TypeChecker_Env.finish; FStar_TypeChecker_Env.refresh = uu___186_172.FStar_TypeChecker_Env.refresh})
end))
in (

let env = (FStar_TypeChecker_Env.initial_env FStar_TypeChecker_TcTerm.type_of_tot_term FStar_TypeChecker_TcTerm.universe_of solver1 FStar_Parser_Const.prims_lid)
in (

let env1 = (

let uu___187_175 = env
in {FStar_TypeChecker_Env.solver = uu___187_175.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___187_175.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___187_175.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___187_175.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___187_175.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___187_175.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___187_175.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___187_175.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___187_175.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___187_175.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___187_175.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___187_175.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___187_175.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___187_175.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___187_175.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___187_175.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___187_175.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___187_175.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___187_175.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___187_175.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___187_175.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.type_of = uu___187_175.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___187_175.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___187_175.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___187_175.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___187_175.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = FStar_Tactics_Interpreter.synth; FStar_TypeChecker_Env.is_native_tactic = uu___187_175.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___187_175.FStar_TypeChecker_Env.identifier_info})
in (

let env2 = (

let uu___188_177 = env1
in {FStar_TypeChecker_Env.solver = uu___188_177.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___188_177.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___188_177.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___188_177.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___188_177.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___188_177.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___188_177.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___188_177.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___188_177.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___188_177.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___188_177.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___188_177.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___188_177.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___188_177.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___188_177.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___188_177.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___188_177.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___188_177.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___188_177.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___188_177.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___188_177.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.type_of = uu___188_177.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___188_177.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___188_177.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___188_177.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___188_177.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___188_177.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = FStar_Tactics_Native.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___188_177.FStar_TypeChecker_Env.identifier_info})
in ((env2.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env2);
(

let prims_filename = (FStar_Options.prims ())
in (

let uu____180 = (

let uu____185 = (FStar_ToSyntax_Env.empty_env ())
in (parse uu____185 FStar_Pervasives_Native.None prims_filename))
in (match (uu____180) with
| (dsenv, prims_mod) -> begin
(

let uu____198 = (FStar_Util.record_time (fun uu____212 -> (FStar_TypeChecker_Tc.check_module env2 prims_mod)))
in (match (uu____198) with
| ((prims_mod1, env3), elapsed_time) -> begin
((((prims_mod1), (elapsed_time))), (dsenv), (env3))
end))
end)));
))))))


let tc_one_fragment : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  (FStar_Parser_ParseIt.input_frag * Prims.bool)  ->  (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) FStar_Pervasives_Native.option = (fun curmod dsenv env uu____265 -> (match (uu____265) with
| (frag, is_interface_dependence) -> begin
try
(match (()) with
| () -> begin
(

let uu____307 = (FStar_Parser_Driver.parse_fragment frag)
in (match (uu____307) with
| FStar_Parser_Driver.Empty -> begin
FStar_Pervasives_Native.Some (((curmod), (dsenv), (env)))
end
| FStar_Parser_Driver.Modul (ast_modul) -> begin
(

let uu____329 = (FStar_ToSyntax_Interleave.interleave_module dsenv ast_modul false)
in (match (uu____329) with
| (ds_env, ast_modul1) -> begin
(

let uu____346 = (FStar_ToSyntax_ToSyntax.desugar_partial_modul curmod dsenv ast_modul1)
in (match (uu____346) with
| (dsenv1, modul) -> begin
(

let dsenv2 = (match (is_interface_dependence) with
| true -> begin
(FStar_ToSyntax_Env.set_iface dsenv1 false)
end
| uu____364 -> begin
dsenv1
end)
in (

let env1 = (match (curmod) with
| FStar_Pervasives_Native.Some (modul1) -> begin
(

let uu____367 = (

let uu____368 = (

let uu____369 = (

let uu____370 = (FStar_Options.file_list ())
in (FStar_List.hd uu____370))
in (FStar_Parser_Dep.lowercase_module_name uu____369))
in (

let uu____373 = (

let uu____374 = (FStar_Ident.string_of_lid modul1.FStar_Syntax_Syntax.name)
in (FStar_String.lowercase uu____374))
in (uu____368 <> uu____373)))
in (match (uu____367) with
| true -> begin
(FStar_Exn.raise (FStar_Errors.Err ("Interactive mode only supports a single module at the top-level")))
end
| uu____375 -> begin
env
end))
end
| FStar_Pervasives_Native.None -> begin
env
end)
in (

let uu____376 = (

let uu____385 = (FStar_ToSyntax_Env.syntax_only dsenv2)
in (match (uu____385) with
| true -> begin
((modul), ([]), (env1))
end
| uu____396 -> begin
(FStar_TypeChecker_Tc.tc_partial_modul env1 modul)
end))
in (match (uu____376) with
| (modul1, uu____408, env2) -> begin
FStar_Pervasives_Native.Some (((FStar_Pervasives_Native.Some (modul1)), (dsenv2), (env2)))
end))))
end))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(

let uu____427 = (FStar_Util.fold_map FStar_ToSyntax_Interleave.prefix_with_interface_decls dsenv ast_decls)
in (match (uu____427) with
| (dsenv1, ast_decls_l) -> begin
(

let uu____458 = (FStar_ToSyntax_ToSyntax.desugar_decls dsenv1 (FStar_List.flatten ast_decls_l))
in (match (uu____458) with
| (dsenv2, decls) -> begin
(match (curmod) with
| FStar_Pervasives_Native.None -> begin
((FStar_Util.print_error "fragment without an enclosing module");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| FStar_Pervasives_Native.Some (modul) -> begin
(

let uu____497 = (

let uu____506 = (FStar_ToSyntax_Env.syntax_only dsenv2)
in (match (uu____506) with
| true -> begin
((modul), ([]), (env))
end
| uu____517 -> begin
(FStar_TypeChecker_Tc.tc_more_partial_modul env modul decls)
end))
in (match (uu____497) with
| (modul1, uu____529, env1) -> begin
FStar_Pervasives_Native.Some (((FStar_Pervasives_Native.Some (modul1)), (dsenv2), (env1)))
end))
end)
end))
end))
end))
end)
with
| FStar_Errors.Error (msg, r) when (

let uu____562 = (FStar_Options.trace_error ())
in (not (uu____562))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]));
FStar_Pervasives_Native.None;
)
end
| FStar_Errors.Err (msg) when (

let uu____581 = (FStar_Options.trace_error ())
in (not (uu____581))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (FStar_Range.dummyRange)))::[]));
FStar_Pervasives_Native.None;
)
end
| e when (

let uu____600 = (FStar_Options.trace_error ())
in (not (uu____600))) -> begin
(FStar_Exn.raise e)
end
end))


let load_interface_decls : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  FStar_Parser_ParseIt.filename  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____625 interface_file_name -> (match (uu____625) with
| (dsenv, env) -> begin
try
(match (()) with
| () -> begin
(

let r = (FStar_Parser_ParseIt.parse (FStar_Util.Inl (interface_file_name)))
in (match (r) with
| FStar_Util.Inl (FStar_Util.Inl (FStar_Parser_AST.Interface (l, decls, uu____682)), uu____683) -> begin
(

let uu____728 = (FStar_ToSyntax_Interleave.initialize_interface l decls dsenv)
in ((uu____728), (env)))
end
| FStar_Util.Inl (uu____729) -> begin
(

let uu____754 = (

let uu____755 = (FStar_Util.format1 "Unexpected result from parsing %s; expected a single interface" interface_file_name)
in FStar_Errors.Err (uu____755))
in (FStar_Exn.raise uu____754))
end
| FStar_Util.Inr (err1, rng) -> begin
(FStar_Exn.raise (FStar_Errors.Error (((err1), (rng)))))
end))
end)
with
| FStar_Errors.Error (msg, r) when (

let uu____791 = (FStar_Options.trace_error ())
in (not (uu____791))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]));
((dsenv), (env));
)
end
| FStar_Errors.Err (msg) when (

let uu____802 = (FStar_Options.trace_error ())
in (not (uu____802))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (FStar_Range.dummyRange)))::[]));
((dsenv), (env));
)
end
| e when (

let uu____813 = (FStar_Options.trace_error ())
in (not (uu____813))) -> begin
(FStar_Exn.raise e)
end
end))


let tc_one_file : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  ((FStar_Syntax_Syntax.modul * Prims.int) * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env pre_fn fn -> (

let checked_file_name = (

let uu____859 = (FStar_Parser_ParseIt.find_file fn)
in (Prims.strcat uu____859 ".checked"))
in (

let lax_checked_file_name = (Prims.strcat checked_file_name ".lax")
in (

let lax_ok = (

let uu____862 = (FStar_Options.should_verify_file fn)
in (not (uu____862)))
in (

let cache_file_to_write = (match (lax_ok) with
| true -> begin
lax_checked_file_name
end
| uu____864 -> begin
checked_file_name
end)
in (

let cache_file_to_read = (fun uu____870 -> (match ((FStar_Util.file_exists checked_file_name)) with
| true -> begin
FStar_Pervasives_Native.Some (checked_file_name)
end
| uu____873 -> begin
(match ((lax_ok && (FStar_Util.file_exists lax_checked_file_name))) with
| true -> begin
FStar_Pervasives_Native.Some (lax_checked_file_name)
end
| uu____876 -> begin
FStar_Pervasives_Native.None
end)
end))
in (

let tc_source_file = (fun uu____890 -> (

let uu____891 = (parse dsenv pre_fn fn)
in (match (uu____891) with
| (dsenv1, fmod) -> begin
(

let check_mod = (fun uu____921 -> (

let uu____922 = (FStar_Util.record_time (fun uu____936 -> (FStar_TypeChecker_Tc.check_module env fmod)))
in (match (uu____922) with
| ((tcmod, env1), time) -> begin
((((tcmod), (time))), (dsenv1), (env1))
end)))
in (

let uu____958 = (

let uu____969 = ((FStar_Options.should_verify fmod.FStar_Syntax_Syntax.name.FStar_Ident.str) && ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ())))
in (match (uu____969) with
| true -> begin
(

let uu____980 = (FStar_Parser_ParseIt.find_file fn)
in (FStar_SMTEncoding_Solver.with_hints_db uu____980 check_mod))
end
| uu____991 -> begin
(check_mod ())
end))
in (match (uu____958) with
| (tcmod, dsenv2, tcenv) -> begin
((

let uu____1014 = (FStar_Options.cache_checked_modules ())
in (match (uu____1014) with
| true -> begin
(

let uu____1015 = tcmod
in (match (uu____1015) with
| (tcmod1, uu____1021) -> begin
(

let mii = (FStar_ToSyntax_Env.inclusion_info dsenv2 tcmod1.FStar_Syntax_Syntax.name)
in (

let uu____1023 = (

let uu____1030 = (FStar_Util.digest_of_file fn)
in ((uu____1030), (tcmod1), (mii)))
in (FStar_Util.save_value_to_file cache_file_to_write uu____1023)))
end))
end
| uu____1037 -> begin
()
end));
((tcmod), (dsenv2), (tcenv));
)
end)))
end)))
in (

let uu____1042 = (FStar_Options.cache_checked_modules ())
in (match (uu____1042) with
| true -> begin
(match ((cache_file_to_read ())) with
| FStar_Pervasives_Native.None -> begin
(tc_source_file ())
end
| FStar_Pervasives_Native.Some (cache_file) -> begin
(

let uu____1064 = (FStar_Util.load_value_from_file cache_file)
in (match (uu____1064) with
| FStar_Pervasives_Native.None -> begin
(failwith (Prims.strcat "Corrupt file: " cache_file))
end
| FStar_Pervasives_Native.Some (digest, tcmod, mii) -> begin
(

let uu____1114 = (

let uu____1115 = (FStar_Util.digest_of_file fn)
in (digest = uu____1115))
in (match (uu____1114) with
| true -> begin
(

let dsenv1 = (FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod mii dsenv)
in (

let tcenv = (FStar_TypeChecker_Tc.load_checked_module env tcmod)
in ((((tcmod), ((Prims.parse_int "0")))), (dsenv1), (tcenv))))
end
| uu____1132 -> begin
(

let uu____1133 = (FStar_Util.format1 "The file %s is stale; delete it" cache_file)
in (failwith uu____1133))
end))
end))
end)
end
| uu____1144 -> begin
(tc_source_file ())
end)))))))))


let needs_interleaving : Prims.string  ->  Prims.string  ->  Prims.bool = (fun intf impl -> (

let m1 = (FStar_Parser_Dep.lowercase_module_name intf)
in (

let m2 = (FStar_Parser_Dep.lowercase_module_name impl)
in (((m1 = m2) && (

let uu____1156 = (FStar_Util.get_file_extension intf)
in (FStar_List.mem uu____1156 (("fsti")::("fsi")::[])))) && (

let uu____1158 = (FStar_Util.get_file_extension impl)
in (FStar_List.mem uu____1158 (("fst")::("fs")::[])))))))


let pop_context : FStar_TypeChecker_Env.env  ->  Prims.string  ->  Prims.unit = (fun env msg -> ((

let uu____1168 = (FStar_ToSyntax_Env.pop ())
in (FStar_All.pipe_right uu____1168 FStar_Pervasives.ignore));
(

let uu____1170 = (FStar_TypeChecker_Env.pop env msg)
in (FStar_All.pipe_right uu____1170 FStar_Pervasives.ignore));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
))


let push_context : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____1185 msg -> (match (uu____1185) with
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

let uu____1233 = uenv
in (match (uu____1233) with
| (dsenv, env) -> begin
(

let uu____1254 = (match (remaining) with
| (intf)::(impl)::remaining1 when (needs_interleaving intf impl) -> begin
(

let uu____1296 = (tc_one_file dsenv env (FStar_Pervasives_Native.Some (intf)) impl)
in (match (uu____1296) with
| (m, dsenv1, env1) -> begin
((remaining1), ((((m)::[]), (dsenv1), (env1))))
end))
end
| (intf_or_impl)::remaining1 -> begin
(

let uu____1368 = (tc_one_file dsenv env FStar_Pervasives_Native.None intf_or_impl)
in (match (uu____1368) with
| (m, dsenv1, env1) -> begin
((remaining1), ((((m)::[]), (dsenv1), (env1))))
end))
end
| [] -> begin
(([]), ((([]), (dsenv), (env))))
end)
in (match (uu____1254) with
| (remaining1, (nmods, dsenv1, env1)) -> begin
((remaining1), (nmods), (((dsenv1), (env1))))
end))
end)))


let rec tc_fold_interleave : ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * uenv)  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * uenv) = (fun acc remaining -> (match (remaining) with
| [] -> begin
acc
end
| uu____1574 -> begin
(

let uu____1577 = acc
in (match (uu____1577) with
| (mods, uenv) -> begin
(

let uu____1612 = (tc_one_file_from_remaining remaining uenv)
in (match (uu____1612) with
| (remaining1, nmods, (dsenv, env)) -> begin
(tc_fold_interleave (((FStar_List.append mods nmods)), (((dsenv), (env)))) remaining1)
end))
end))
end))


let batch_mode_tc_no_prims : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env filenames -> (

let uu____1707 = (tc_fold_interleave (([]), (((dsenv), (env)))) filenames)
in (match (uu____1707) with
| (all_mods, (dsenv1, env1)) -> begin
((

let uu____1764 = ((FStar_Options.interactive ()) && (

let uu____1766 = (FStar_Errors.get_err_count ())
in (uu____1766 = (Prims.parse_int "0"))))
in (match (uu____1764) with
| true -> begin
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end
| uu____1767 -> begin
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end));
((all_mods), (dsenv1), (env1));
)
end)))


let batch_mode_tc : Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun filenames -> (

let uu____1794 = (tc_prims ())
in (match (uu____1794) with
| (prims_mod, dsenv, env) -> begin
((

let uu____1829 = ((

let uu____1832 = (FStar_Options.explicit_deps ())
in (not (uu____1832))) && (FStar_Options.debug_any ()))
in (match (uu____1829) with
| true -> begin
((FStar_Util.print_endline "Auto-deps kicked in; here\'s some info.");
(FStar_Util.print1 "Here\'s the list of filenames we will process: %s\n" (FStar_String.concat " " filenames));
(

let uu____1835 = (

let uu____1836 = (FStar_Options.verify_module ())
in (FStar_String.concat " " uu____1836))
in (FStar_Util.print1 "Here\'s the list of modules we will verify: %s\n" uu____1835));
)
end
| uu____1839 -> begin
()
end));
(

let uu____1840 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (uu____1840) with
| (all_mods, dsenv1, env1) -> begin
(((prims_mod)::all_mods), (dsenv1), (env1))
end));
)
end)))




