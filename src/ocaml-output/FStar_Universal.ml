
open Prims
open FStar_Pervasives

let module_or_interface_name : FStar_Syntax_Syntax.modul  ->  (Prims.bool * FStar_Ident.lident) = (fun m -> ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name)))


let user_tactics_modules : Prims.string Prims.list FStar_ST.ref = FStar_TypeChecker_Tc.user_tactics_modules


let parse : FStar_ToSyntax_Env.env  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul) = (fun env pre_fn fn -> (

let uu____44 = (FStar_Parser_Driver.parse_file fn)
in (match (uu____44) with
| (ast, uu____60) -> begin
(

let uu____73 = (match (pre_fn) with
| FStar_Pervasives_Native.None -> begin
((env), (ast))
end
| FStar_Pervasives_Native.Some (pre_fn1) -> begin
(

let uu____83 = (FStar_Parser_Driver.parse_file pre_fn1)
in (match (uu____83) with
| (pre_ast, uu____99) -> begin
(match (((pre_ast), (ast))) with
| (FStar_Parser_AST.Interface (lid1, decls1, uu____118), FStar_Parser_AST.Module (lid2, decls2)) when (FStar_Ident.lid_equals lid1 lid2) -> begin
(

let env1 = (FStar_ToSyntax_Interleave.initialize_interface lid1 decls1 env)
in (

let uu____130 = (FStar_ToSyntax_Interleave.interleave_module env1 ast true)
in (match (uu____130) with
| (env2, ast1) -> begin
((env2), (ast1))
end)))
end
| uu____141 -> begin
(FStar_Exn.raise (FStar_Errors.Err ("mismatch between pre-module and module\n")))
end)
end))
end)
in (match (uu____73) with
| (env1, ast1) -> begin
(FStar_ToSyntax_ToSyntax.desugar_modul env1 ast1)
end))
end)))


let tc_prims : Prims.unit  ->  ((FStar_Syntax_Syntax.modul * Prims.int) * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____169 -> (

let solver1 = (

let uu____181 = (FStar_Options.lax ())
in (match (uu____181) with
| true -> begin
FStar_SMTEncoding_Solver.dummy
end
| uu____182 -> begin
(

let uu___196_183 = FStar_SMTEncoding_Solver.solver
in {FStar_TypeChecker_Env.init = uu___196_183.FStar_TypeChecker_Env.init; FStar_TypeChecker_Env.push = uu___196_183.FStar_TypeChecker_Env.push; FStar_TypeChecker_Env.pop = uu___196_183.FStar_TypeChecker_Env.pop; FStar_TypeChecker_Env.encode_modul = uu___196_183.FStar_TypeChecker_Env.encode_modul; FStar_TypeChecker_Env.encode_sig = uu___196_183.FStar_TypeChecker_Env.encode_sig; FStar_TypeChecker_Env.preprocess = FStar_Tactics_Interpreter.preprocess; FStar_TypeChecker_Env.solve = uu___196_183.FStar_TypeChecker_Env.solve; FStar_TypeChecker_Env.is_trivial = uu___196_183.FStar_TypeChecker_Env.is_trivial; FStar_TypeChecker_Env.finish = uu___196_183.FStar_TypeChecker_Env.finish; FStar_TypeChecker_Env.refresh = uu___196_183.FStar_TypeChecker_Env.refresh})
end))
in (

let env = (FStar_TypeChecker_Env.initial_env FStar_TypeChecker_TcTerm.type_of_tot_term FStar_TypeChecker_TcTerm.universe_of solver1 FStar_Parser_Const.prims_lid)
in (

let env1 = (

let uu___197_186 = env
in {FStar_TypeChecker_Env.solver = uu___197_186.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___197_186.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___197_186.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___197_186.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___197_186.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___197_186.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___197_186.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___197_186.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___197_186.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___197_186.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___197_186.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___197_186.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___197_186.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___197_186.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___197_186.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___197_186.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___197_186.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___197_186.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___197_186.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___197_186.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___197_186.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___197_186.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.type_of = uu___197_186.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___197_186.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___197_186.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___197_186.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___197_186.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = FStar_Tactics_Interpreter.synth; FStar_TypeChecker_Env.is_native_tactic = uu___197_186.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___197_186.FStar_TypeChecker_Env.identifier_info})
in (

let env2 = (

let uu___198_188 = env1
in {FStar_TypeChecker_Env.solver = uu___198_188.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___198_188.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___198_188.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___198_188.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___198_188.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___198_188.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___198_188.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___198_188.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___198_188.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___198_188.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___198_188.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___198_188.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___198_188.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___198_188.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___198_188.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___198_188.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___198_188.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___198_188.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___198_188.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___198_188.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___198_188.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___198_188.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.type_of = uu___198_188.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___198_188.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___198_188.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___198_188.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___198_188.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___198_188.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = FStar_Tactics_Native.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___198_188.FStar_TypeChecker_Env.identifier_info})
in ((env2.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env2);
(

let prims_filename = (FStar_Options.prims ())
in (

let uu____191 = (

let uu____196 = (FStar_ToSyntax_Env.empty_env ())
in (parse uu____196 FStar_Pervasives_Native.None prims_filename))
in (match (uu____191) with
| (dsenv, prims_mod) -> begin
(

let uu____209 = (FStar_Util.record_time (fun uu____223 -> (FStar_TypeChecker_Tc.check_module env2 prims_mod)))
in (match (uu____209) with
| ((prims_mod1, env3), elapsed_time) -> begin
((((prims_mod1), (elapsed_time))), (dsenv), (env3))
end))
end)));
))))))


let tc_one_fragment : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  (FStar_Parser_ParseIt.input_frag * Prims.bool)  ->  (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) FStar_Pervasives_Native.option = (fun curmod dsenv env uu____276 -> (match (uu____276) with
| (frag, is_interface_dependence) -> begin
(FStar_All.try_with (fun uu___200_307 -> (match (()) with
| () -> begin
(

let uu____318 = (FStar_Parser_Driver.parse_fragment frag)
in (match (uu____318) with
| FStar_Parser_Driver.Empty -> begin
FStar_Pervasives_Native.Some (((curmod), (dsenv), (env)))
end
| FStar_Parser_Driver.Modul (ast_modul) -> begin
(

let uu____340 = (FStar_ToSyntax_Interleave.interleave_module dsenv ast_modul false)
in (match (uu____340) with
| (ds_env, ast_modul1) -> begin
(

let uu____357 = (FStar_ToSyntax_ToSyntax.desugar_partial_modul curmod dsenv ast_modul1)
in (match (uu____357) with
| (dsenv1, modul) -> begin
(

let dsenv2 = (match (is_interface_dependence) with
| true -> begin
(FStar_ToSyntax_Env.set_iface dsenv1 false)
end
| uu____375 -> begin
dsenv1
end)
in (

let env1 = (match (curmod) with
| FStar_Pervasives_Native.Some (modul1) -> begin
(

let uu____378 = (

let uu____379 = (

let uu____380 = (

let uu____381 = (FStar_Options.file_list ())
in (FStar_List.hd uu____381))
in (FStar_Parser_Dep.lowercase_module_name uu____380))
in (

let uu____384 = (

let uu____385 = (FStar_Ident.string_of_lid modul1.FStar_Syntax_Syntax.name)
in (FStar_String.lowercase uu____385))
in (Prims.op_disEquality uu____379 uu____384)))
in (match (uu____378) with
| true -> begin
(FStar_Exn.raise (FStar_Errors.Err ("Interactive mode only supports a single module at the top-level")))
end
| uu____386 -> begin
env
end))
end
| FStar_Pervasives_Native.None -> begin
env
end)
in (

let uu____387 = (

let uu____396 = (FStar_ToSyntax_Env.syntax_only dsenv2)
in (match (uu____396) with
| true -> begin
((modul), ([]), (env1))
end
| uu____407 -> begin
(FStar_TypeChecker_Tc.tc_partial_modul env1 modul)
end))
in (match (uu____387) with
| (modul1, uu____419, env2) -> begin
FStar_Pervasives_Native.Some (((FStar_Pervasives_Native.Some (modul1)), (dsenv2), (env2)))
end))))
end))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(

let uu____438 = (FStar_Util.fold_map FStar_ToSyntax_Interleave.prefix_with_interface_decls dsenv ast_decls)
in (match (uu____438) with
| (dsenv1, ast_decls_l) -> begin
(

let uu____469 = (FStar_ToSyntax_ToSyntax.desugar_decls dsenv1 (FStar_List.flatten ast_decls_l))
in (match (uu____469) with
| (dsenv2, decls) -> begin
(match (curmod) with
| FStar_Pervasives_Native.None -> begin
((FStar_Util.print_error "fragment without an enclosing module");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| FStar_Pervasives_Native.Some (modul) -> begin
(

let uu____508 = (

let uu____517 = (FStar_ToSyntax_Env.syntax_only dsenv2)
in (match (uu____517) with
| true -> begin
((modul), ([]), (env))
end
| uu____528 -> begin
(FStar_TypeChecker_Tc.tc_more_partial_modul env modul decls)
end))
in (match (uu____508) with
| (modul1, uu____540, env1) -> begin
FStar_Pervasives_Native.Some (((FStar_Pervasives_Native.Some (modul1)), (dsenv2), (env1)))
end))
end)
end))
end))
end))
end)) (fun uu___199_560 -> (match (uu___199_560) with
| FStar_Errors.Error (msg, r) when (

let uu____573 = (FStar_Options.trace_error ())
in (not (uu____573))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]));
FStar_Pervasives_Native.None;
)
end
| FStar_Errors.Err (msg) when (

let uu____592 = (FStar_Options.trace_error ())
in (not (uu____592))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (FStar_Range.dummyRange)))::[]));
FStar_Pervasives_Native.None;
)
end
| e when (

let uu____611 = (FStar_Options.trace_error ())
in (not (uu____611))) -> begin
(FStar_Exn.raise e)
end)))
end))


let load_interface_decls : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  FStar_Parser_ParseIt.filename  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____636 interface_file_name -> (match (uu____636) with
| (dsenv, env) -> begin
(FStar_All.try_with (fun uu___202_663 -> (match (()) with
| () -> begin
(

let r = (FStar_Parser_ParseIt.parse (FStar_Util.Inl (interface_file_name)))
in (match (r) with
| FStar_Util.Inl (FStar_Util.Inl (FStar_Parser_AST.Interface (l, decls, uu____693)), uu____694) -> begin
(

let uu____739 = (FStar_ToSyntax_Interleave.initialize_interface l decls dsenv)
in ((uu____739), (env)))
end
| FStar_Util.Inl (uu____740) -> begin
(

let uu____765 = (

let uu____766 = (FStar_Util.format1 "Unexpected result from parsing %s; expected a single interface" interface_file_name)
in FStar_Errors.Err (uu____766))
in (FStar_Exn.raise uu____765))
end
| FStar_Util.Inr (err1, rng) -> begin
(FStar_Exn.raise (FStar_Errors.Error (((err1), (rng)))))
end))
end)) (fun uu___201_795 -> (match (uu___201_795) with
| FStar_Errors.Error (msg, r) when (

let uu____802 = (FStar_Options.trace_error ())
in (not (uu____802))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]));
((dsenv), (env));
)
end
| FStar_Errors.Err (msg) when (

let uu____813 = (FStar_Options.trace_error ())
in (not (uu____813))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (FStar_Range.dummyRange)))::[]));
((dsenv), (env));
)
end
| e when (

let uu____824 = (FStar_Options.trace_error ())
in (not (uu____824))) -> begin
(FStar_Exn.raise e)
end)))
end))


let tc_one_file : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  ((FStar_Syntax_Syntax.modul * Prims.int) * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env pre_fn fn -> (

let checked_file_name = (

let uu____870 = (FStar_Parser_ParseIt.find_file fn)
in (Prims.strcat uu____870 ".checked"))
in (

let lax_checked_file_name = (Prims.strcat checked_file_name ".lax")
in (

let lax_ok = (

let uu____873 = (FStar_Options.should_verify_file fn)
in (not (uu____873)))
in (

let cache_file_to_write = (match (lax_ok) with
| true -> begin
lax_checked_file_name
end
| uu____875 -> begin
checked_file_name
end)
in (

let cache_file_to_read = (fun uu____881 -> (match ((FStar_Util.file_exists checked_file_name)) with
| true -> begin
FStar_Pervasives_Native.Some (checked_file_name)
end
| uu____884 -> begin
(match ((lax_ok && (FStar_Util.file_exists lax_checked_file_name))) with
| true -> begin
FStar_Pervasives_Native.Some (lax_checked_file_name)
end
| uu____887 -> begin
FStar_Pervasives_Native.None
end)
end))
in (

let tc_source_file = (fun uu____901 -> (

let uu____902 = (parse dsenv pre_fn fn)
in (match (uu____902) with
| (dsenv1, fmod) -> begin
(

let check_mod = (fun uu____932 -> (

let uu____933 = (FStar_Util.record_time (fun uu____947 -> (FStar_TypeChecker_Tc.check_module env fmod)))
in (match (uu____933) with
| ((tcmod, env1), time) -> begin
((((tcmod), (time))), (dsenv1), (env1))
end)))
in (

let uu____969 = (

let uu____980 = ((FStar_Options.should_verify fmod.FStar_Syntax_Syntax.name.FStar_Ident.str) && ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ())))
in (match (uu____980) with
| true -> begin
(

let uu____991 = (FStar_Parser_ParseIt.find_file fn)
in (FStar_SMTEncoding_Solver.with_hints_db uu____991 check_mod))
end
| uu____1002 -> begin
(check_mod ())
end))
in (match (uu____969) with
| (tcmod, dsenv2, tcenv) -> begin
((

let uu____1025 = (FStar_Options.cache_checked_modules ())
in (match (uu____1025) with
| true -> begin
(

let uu____1026 = tcmod
in (match (uu____1026) with
| (tcmod1, uu____1032) -> begin
(

let mii = (FStar_ToSyntax_Env.inclusion_info dsenv2 tcmod1.FStar_Syntax_Syntax.name)
in (

let uu____1034 = (

let uu____1041 = (FStar_Util.digest_of_file fn)
in ((uu____1041), (tcmod1), (mii)))
in (FStar_Util.save_value_to_file cache_file_to_write uu____1034)))
end))
end
| uu____1048 -> begin
()
end));
((tcmod), (dsenv2), (tcenv));
)
end)))
end)))
in (

let uu____1053 = (FStar_Options.cache_checked_modules ())
in (match (uu____1053) with
| true -> begin
(match ((cache_file_to_read ())) with
| FStar_Pervasives_Native.None -> begin
(tc_source_file ())
end
| FStar_Pervasives_Native.Some (cache_file) -> begin
(

let uu____1075 = (FStar_Util.load_value_from_file cache_file)
in (match (uu____1075) with
| FStar_Pervasives_Native.None -> begin
(failwith (Prims.strcat "Corrupt file: " cache_file))
end
| FStar_Pervasives_Native.Some (digest, tcmod, mii) -> begin
(

let uu____1125 = (

let uu____1126 = (FStar_Util.digest_of_file fn)
in (Prims.op_Equality digest uu____1126))
in (match (uu____1125) with
| true -> begin
(

let dsenv1 = (FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod mii dsenv)
in (

let tcenv = (FStar_TypeChecker_Tc.load_checked_module env tcmod)
in ((((tcmod), ((Prims.parse_int "0")))), (dsenv1), (tcenv))))
end
| uu____1143 -> begin
(

let uu____1144 = (FStar_Util.format1 "The file %s is stale; delete it" cache_file)
in (failwith uu____1144))
end))
end))
end)
end
| uu____1155 -> begin
(tc_source_file ())
end)))))))))


let needs_interleaving : Prims.string  ->  Prims.string  ->  Prims.bool = (fun intf impl -> (

let m1 = (FStar_Parser_Dep.lowercase_module_name intf)
in (

let m2 = (FStar_Parser_Dep.lowercase_module_name impl)
in (((Prims.op_Equality m1 m2) && (

let uu____1167 = (FStar_Util.get_file_extension intf)
in (FStar_List.mem uu____1167 (("fsti")::("fsi")::[])))) && (

let uu____1169 = (FStar_Util.get_file_extension impl)
in (FStar_List.mem uu____1169 (("fst")::("fs")::[])))))))


let pop_context : FStar_TypeChecker_Env.env  ->  Prims.string  ->  Prims.unit = (fun env msg -> ((

let uu____1179 = (FStar_ToSyntax_Env.pop ())
in (FStar_All.pipe_right uu____1179 FStar_Pervasives.ignore));
(

let uu____1181 = (FStar_TypeChecker_Env.pop env msg)
in (FStar_All.pipe_right uu____1181 FStar_Pervasives.ignore));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
))


let push_context : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____1196 msg -> (match (uu____1196) with
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

let uu____1244 = uenv
in (match (uu____1244) with
| (dsenv, env) -> begin
(

let uu____1265 = (match (remaining) with
| (intf)::(impl)::remaining1 when (needs_interleaving intf impl) -> begin
(

let uu____1307 = (tc_one_file dsenv env (FStar_Pervasives_Native.Some (intf)) impl)
in (match (uu____1307) with
| (m, dsenv1, env1) -> begin
((remaining1), ((((m)::[]), (dsenv1), (env1))))
end))
end
| (intf_or_impl)::remaining1 -> begin
(

let uu____1379 = (tc_one_file dsenv env FStar_Pervasives_Native.None intf_or_impl)
in (match (uu____1379) with
| (m, dsenv1, env1) -> begin
((remaining1), ((((m)::[]), (dsenv1), (env1))))
end))
end
| [] -> begin
(([]), ((([]), (dsenv), (env))))
end)
in (match (uu____1265) with
| (remaining1, (nmods, dsenv1, env1)) -> begin
((remaining1), (nmods), (((dsenv1), (env1))))
end))
end)))


let rec tc_fold_interleave : ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * uenv)  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * uenv) = (fun acc remaining -> (match (remaining) with
| [] -> begin
acc
end
| uu____1585 -> begin
(

let uu____1588 = acc
in (match (uu____1588) with
| (mods, uenv) -> begin
(

let uu____1623 = (tc_one_file_from_remaining remaining uenv)
in (match (uu____1623) with
| (remaining1, nmods, (dsenv, env)) -> begin
(tc_fold_interleave (((FStar_List.append mods nmods)), (((dsenv), (env)))) remaining1)
end))
end))
end))


let batch_mode_tc_no_prims : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env filenames -> (

let uu____1718 = (tc_fold_interleave (([]), (((dsenv), (env)))) filenames)
in (match (uu____1718) with
| (all_mods, (dsenv1, env1)) -> begin
((

let uu____1775 = ((FStar_Options.interactive ()) && (

let uu____1777 = (FStar_Errors.get_err_count ())
in (Prims.op_Equality uu____1777 (Prims.parse_int "0"))))
in (match (uu____1775) with
| true -> begin
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end
| uu____1778 -> begin
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end));
((all_mods), (dsenv1), (env1));
)
end)))


let batch_mode_tc : Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun filenames -> (

let uu____1805 = (tc_prims ())
in (match (uu____1805) with
| (prims_mod, dsenv, env) -> begin
((

let uu____1840 = ((

let uu____1843 = (FStar_Options.explicit_deps ())
in (not (uu____1843))) && (FStar_Options.debug_any ()))
in (match (uu____1840) with
| true -> begin
((FStar_Util.print_endline "Auto-deps kicked in; here\'s some info.");
(FStar_Util.print1 "Here\'s the list of filenames we will process: %s\n" (FStar_String.concat " " filenames));
(

let uu____1846 = (

let uu____1847 = (FStar_Options.verify_module ())
in (FStar_String.concat " " uu____1847))
in (FStar_Util.print1 "Here\'s the list of modules we will verify: %s\n" uu____1846));
)
end
| uu____1850 -> begin
()
end));
(

let uu____1851 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (uu____1851) with
| (all_mods, dsenv1, env1) -> begin
(((prims_mod)::all_mods), (dsenv1), (env1))
end));
)
end)))




