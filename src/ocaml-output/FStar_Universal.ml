
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


let init_env : Prims.unit  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____163 -> (

let solver1 = (

let uu____169 = (FStar_Options.lax ())
in (match (uu____169) with
| true -> begin
FStar_SMTEncoding_Solver.dummy
end
| uu____170 -> begin
(

let uu___229_171 = FStar_SMTEncoding_Solver.solver
in {FStar_TypeChecker_Env.init = uu___229_171.FStar_TypeChecker_Env.init; FStar_TypeChecker_Env.push = uu___229_171.FStar_TypeChecker_Env.push; FStar_TypeChecker_Env.pop = uu___229_171.FStar_TypeChecker_Env.pop; FStar_TypeChecker_Env.encode_modul = uu___229_171.FStar_TypeChecker_Env.encode_modul; FStar_TypeChecker_Env.encode_sig = uu___229_171.FStar_TypeChecker_Env.encode_sig; FStar_TypeChecker_Env.preprocess = FStar_Tactics_Interpreter.preprocess; FStar_TypeChecker_Env.solve = uu___229_171.FStar_TypeChecker_Env.solve; FStar_TypeChecker_Env.is_trivial = uu___229_171.FStar_TypeChecker_Env.is_trivial; FStar_TypeChecker_Env.finish = uu___229_171.FStar_TypeChecker_Env.finish; FStar_TypeChecker_Env.refresh = uu___229_171.FStar_TypeChecker_Env.refresh})
end))
in (

let env = (FStar_TypeChecker_Env.initial_env FStar_TypeChecker_TcTerm.tc_term FStar_TypeChecker_TcTerm.type_of_tot_term FStar_TypeChecker_TcTerm.universe_of solver1 FStar_Parser_Const.prims_lid)
in (

let env1 = (

let uu___230_174 = env
in {FStar_TypeChecker_Env.solver = uu___230_174.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___230_174.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___230_174.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___230_174.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___230_174.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___230_174.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___230_174.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___230_174.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___230_174.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___230_174.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___230_174.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___230_174.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___230_174.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___230_174.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___230_174.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___230_174.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___230_174.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___230_174.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___230_174.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___230_174.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___230_174.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___230_174.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___230_174.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___230_174.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___230_174.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___230_174.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___230_174.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___230_174.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = FStar_Tactics_Interpreter.synth; FStar_TypeChecker_Env.is_native_tactic = uu___230_174.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___230_174.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___230_174.FStar_TypeChecker_Env.tc_hooks})
in (

let env2 = (

let uu___231_176 = env1
in {FStar_TypeChecker_Env.solver = uu___231_176.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___231_176.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___231_176.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___231_176.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___231_176.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___231_176.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___231_176.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___231_176.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___231_176.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___231_176.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___231_176.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___231_176.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___231_176.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___231_176.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___231_176.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___231_176.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___231_176.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___231_176.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___231_176.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___231_176.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___231_176.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___231_176.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___231_176.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___231_176.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___231_176.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___231_176.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___231_176.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___231_176.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___231_176.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = FStar_Tactics_Native.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___231_176.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___231_176.FStar_TypeChecker_Env.tc_hooks})
in ((env2.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env2);
(

let uu____178 = (FStar_ToSyntax_Env.empty_env ())
in ((uu____178), (env2)));
))))))


let tc_prims : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  ((FStar_Syntax_Syntax.modul * Prims.int) * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____196 -> (match (uu____196) with
| (dsenv, env) -> begin
(

let prims_filename = (FStar_Options.prims ())
in (

let uu____224 = (parse dsenv FStar_Pervasives_Native.None prims_filename)
in (match (uu____224) with
| (dsenv1, prims_mod) -> begin
(

let uu____241 = (FStar_Util.record_time (fun uu____255 -> (FStar_TypeChecker_Tc.check_module env prims_mod)))
in (match (uu____241) with
| ((prims_mod1, env1), elapsed_time) -> begin
((((prims_mod1), (elapsed_time))), (dsenv1), (env1))
end))
end)))
end))


let tc_one_fragment : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  (FStar_Parser_ParseIt.input_frag * Prims.bool)  ->  (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) FStar_Pervasives_Native.option = (fun curmod dsenv env uu____308 -> (match (uu____308) with
| (frag, is_interface_dependence) -> begin
(FStar_All.try_with (fun uu___233_339 -> (match (()) with
| () -> begin
(

let uu____350 = (FStar_Parser_Driver.parse_fragment frag)
in (match (uu____350) with
| FStar_Parser_Driver.Empty -> begin
FStar_Pervasives_Native.Some (((curmod), (dsenv), (env)))
end
| FStar_Parser_Driver.Modul (ast_modul) -> begin
(

let uu____372 = (FStar_ToSyntax_Interleave.interleave_module dsenv ast_modul false)
in (match (uu____372) with
| (ds_env, ast_modul1) -> begin
(

let uu____389 = (FStar_ToSyntax_ToSyntax.desugar_partial_modul curmod dsenv ast_modul1)
in (match (uu____389) with
| (dsenv1, modul) -> begin
(

let dsenv2 = (match (is_interface_dependence) with
| true -> begin
(FStar_ToSyntax_Env.set_iface dsenv1 false)
end
| uu____407 -> begin
dsenv1
end)
in (

let env1 = (match (curmod) with
| FStar_Pervasives_Native.Some (modul1) -> begin
(

let uu____410 = (

let uu____411 = (

let uu____412 = (

let uu____413 = (FStar_Options.file_list ())
in (FStar_List.hd uu____413))
in (FStar_Parser_Dep.lowercase_module_name uu____412))
in (

let uu____416 = (

let uu____417 = (FStar_Ident.string_of_lid modul1.FStar_Syntax_Syntax.name)
in (FStar_String.lowercase uu____417))
in (Prims.op_disEquality uu____411 uu____416)))
in (match (uu____410) with
| true -> begin
(FStar_Exn.raise (FStar_Errors.Err ("Interactive mode only supports a single module at the top-level")))
end
| uu____418 -> begin
env
end))
end
| FStar_Pervasives_Native.None -> begin
env
end)
in (

let uu____419 = (

let uu____428 = (FStar_ToSyntax_Env.syntax_only dsenv2)
in (match (uu____428) with
| true -> begin
((modul), ([]), (env1))
end
| uu____439 -> begin
(FStar_TypeChecker_Tc.tc_partial_modul env1 modul)
end))
in (match (uu____419) with
| (modul1, uu____451, env2) -> begin
FStar_Pervasives_Native.Some (((FStar_Pervasives_Native.Some (modul1)), (dsenv2), (env2)))
end))))
end))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(

let uu____470 = (FStar_Util.fold_map FStar_ToSyntax_Interleave.prefix_with_interface_decls dsenv ast_decls)
in (match (uu____470) with
| (dsenv1, ast_decls_l) -> begin
(

let uu____501 = (FStar_ToSyntax_ToSyntax.desugar_decls dsenv1 (FStar_List.flatten ast_decls_l))
in (match (uu____501) with
| (dsenv2, decls) -> begin
(match (curmod) with
| FStar_Pervasives_Native.None -> begin
((FStar_Util.print_error "fragment without an enclosing module");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| FStar_Pervasives_Native.Some (modul) -> begin
(

let uu____540 = (

let uu____549 = (FStar_ToSyntax_Env.syntax_only dsenv2)
in (match (uu____549) with
| true -> begin
((modul), ([]), (env))
end
| uu____560 -> begin
(FStar_TypeChecker_Tc.tc_more_partial_modul env modul decls)
end))
in (match (uu____540) with
| (modul1, uu____572, env1) -> begin
FStar_Pervasives_Native.Some (((FStar_Pervasives_Native.Some (modul1)), (dsenv2), (env1)))
end))
end)
end))
end))
end))
end)) (fun uu___232_592 -> (match (uu___232_592) with
| FStar_Errors.Error (msg, r) when (

let uu____605 = (FStar_Options.trace_error ())
in (not (uu____605))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]));
FStar_Pervasives_Native.None;
)
end
| FStar_Errors.Err (msg) when (

let uu____624 = (FStar_Options.trace_error ())
in (not (uu____624))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (FStar_Range.dummyRange)))::[]));
FStar_Pervasives_Native.None;
)
end
| e when (

let uu____643 = (FStar_Options.trace_error ())
in (not (uu____643))) -> begin
(FStar_Exn.raise e)
end)))
end))


let load_interface_decls : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  FStar_Parser_ParseIt.filename  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____668 interface_file_name -> (match (uu____668) with
| (dsenv, env) -> begin
(FStar_All.try_with (fun uu___235_695 -> (match (()) with
| () -> begin
(

let r = (FStar_Parser_ParseIt.parse (FStar_Util.Inl (interface_file_name)))
in (match (r) with
| FStar_Util.Inl (FStar_Util.Inl (FStar_Parser_AST.Interface (l, decls, uu____725)), uu____726) -> begin
(

let uu____771 = (FStar_ToSyntax_Interleave.initialize_interface l decls dsenv)
in ((uu____771), (env)))
end
| FStar_Util.Inl (uu____772) -> begin
(

let uu____797 = (

let uu____798 = (FStar_Util.format1 "Unexpected result from parsing %s; expected a single interface" interface_file_name)
in FStar_Errors.Err (uu____798))
in (FStar_Exn.raise uu____797))
end
| FStar_Util.Inr (err1, rng) -> begin
(FStar_Exn.raise (FStar_Errors.Error (((err1), (rng)))))
end))
end)) (fun uu___234_827 -> (match (uu___234_827) with
| FStar_Errors.Error (msg, r) when (

let uu____834 = (FStar_Options.trace_error ())
in (not (uu____834))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (r)))::[]));
((dsenv), (env));
)
end
| FStar_Errors.Err (msg) when (

let uu____845 = (FStar_Options.trace_error ())
in (not (uu____845))) -> begin
((FStar_TypeChecker_Err.add_errors env ((((msg), (FStar_Range.dummyRange)))::[]));
((dsenv), (env));
)
end
| e when (

let uu____856 = (FStar_Options.trace_error ())
in (not (uu____856))) -> begin
(FStar_Exn.raise e)
end)))
end))


let tc_one_file : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  ((FStar_Syntax_Syntax.modul * Prims.int) * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env pre_fn fn -> (

let checked_file_name = (

let uu____902 = (FStar_Parser_ParseIt.find_file fn)
in (Prims.strcat uu____902 ".checked"))
in (

let lax_checked_file_name = (Prims.strcat checked_file_name ".lax")
in (

let lax_ok = (

let uu____905 = (FStar_Options.should_verify_file fn)
in (not (uu____905)))
in (

let cache_file_to_write = (match (lax_ok) with
| true -> begin
lax_checked_file_name
end
| uu____907 -> begin
checked_file_name
end)
in (

let cache_file_to_read = (fun uu____913 -> (match ((FStar_Util.file_exists checked_file_name)) with
| true -> begin
FStar_Pervasives_Native.Some (checked_file_name)
end
| uu____916 -> begin
(match ((lax_ok && (FStar_Util.file_exists lax_checked_file_name))) with
| true -> begin
FStar_Pervasives_Native.Some (lax_checked_file_name)
end
| uu____919 -> begin
FStar_Pervasives_Native.None
end)
end))
in (

let tc_source_file = (fun uu____933 -> (

let uu____934 = (parse dsenv pre_fn fn)
in (match (uu____934) with
| (dsenv1, fmod) -> begin
(

let check_mod = (fun uu____964 -> (

let uu____965 = (FStar_Util.record_time (fun uu____979 -> (FStar_TypeChecker_Tc.check_module env fmod)))
in (match (uu____965) with
| ((tcmod, env1), time) -> begin
((((tcmod), (time))), (dsenv1), (env1))
end)))
in (

let uu____1001 = (

let uu____1012 = ((FStar_Options.should_verify fmod.FStar_Syntax_Syntax.name.FStar_Ident.str) && ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ())))
in (match (uu____1012) with
| true -> begin
(

let uu____1023 = (FStar_Parser_ParseIt.find_file fn)
in (FStar_SMTEncoding_Solver.with_hints_db uu____1023 check_mod))
end
| uu____1034 -> begin
(check_mod ())
end))
in (match (uu____1001) with
| (tcmod, dsenv2, tcenv) -> begin
((

let uu____1057 = (FStar_Options.cache_checked_modules ())
in (match (uu____1057) with
| true -> begin
(

let uu____1058 = tcmod
in (match (uu____1058) with
| (tcmod1, uu____1064) -> begin
(

let mii = (FStar_ToSyntax_Env.inclusion_info dsenv2 tcmod1.FStar_Syntax_Syntax.name)
in (

let uu____1066 = (

let uu____1073 = (FStar_Util.digest_of_file fn)
in ((uu____1073), (tcmod1), (mii)))
in (FStar_Util.save_value_to_file cache_file_to_write uu____1066)))
end))
end
| uu____1080 -> begin
()
end));
((tcmod), (dsenv2), (tcenv));
)
end)))
end)))
in (

let uu____1085 = (FStar_Options.cache_checked_modules ())
in (match (uu____1085) with
| true -> begin
(match ((cache_file_to_read ())) with
| FStar_Pervasives_Native.None -> begin
(tc_source_file ())
end
| FStar_Pervasives_Native.Some (cache_file) -> begin
(

let uu____1107 = (FStar_Util.load_value_from_file cache_file)
in (match (uu____1107) with
| FStar_Pervasives_Native.None -> begin
(failwith (Prims.strcat "Corrupt file: " cache_file))
end
| FStar_Pervasives_Native.Some (digest, tcmod, mii) -> begin
(

let uu____1157 = (

let uu____1158 = (FStar_Util.digest_of_file fn)
in (Prims.op_Equality digest uu____1158))
in (match (uu____1157) with
| true -> begin
(

let dsenv1 = (FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod mii dsenv)
in (

let tcenv = (FStar_TypeChecker_Tc.load_checked_module env tcmod)
in ((((tcmod), ((Prims.parse_int "0")))), (dsenv1), (tcenv))))
end
| uu____1175 -> begin
(

let uu____1176 = (FStar_Util.format1 "The file %s is stale; delete it" cache_file)
in (failwith uu____1176))
end))
end))
end)
end
| uu____1187 -> begin
(tc_source_file ())
end)))))))))


let needs_interleaving : Prims.string  ->  Prims.string  ->  Prims.bool = (fun intf impl -> (

let m1 = (FStar_Parser_Dep.lowercase_module_name intf)
in (

let m2 = (FStar_Parser_Dep.lowercase_module_name impl)
in (((Prims.op_Equality m1 m2) && (

let uu____1199 = (FStar_Util.get_file_extension intf)
in (FStar_List.mem uu____1199 (("fsti")::("fsi")::[])))) && (

let uu____1201 = (FStar_Util.get_file_extension impl)
in (FStar_List.mem uu____1201 (("fst")::("fs")::[])))))))


let pop_context : FStar_TypeChecker_Env.env  ->  Prims.string  ->  Prims.unit = (fun env msg -> ((

let uu____1211 = (FStar_ToSyntax_Env.pop ())
in (FStar_All.pipe_right uu____1211 FStar_Pervasives.ignore));
(

let uu____1213 = (FStar_TypeChecker_Env.pop env msg)
in (FStar_All.pipe_right uu____1213 FStar_Pervasives.ignore));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
))


let push_context : (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  (FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun uu____1228 msg -> (match (uu____1228) with
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

let uu____1276 = uenv
in (match (uu____1276) with
| (dsenv, env) -> begin
(

let uu____1297 = (match (remaining) with
| (intf)::(impl)::remaining1 when (needs_interleaving intf impl) -> begin
(

let uu____1339 = (tc_one_file dsenv env (FStar_Pervasives_Native.Some (intf)) impl)
in (match (uu____1339) with
| (m, dsenv1, env1) -> begin
((remaining1), ((((m)::[]), (dsenv1), (env1))))
end))
end
| (intf_or_impl)::remaining1 -> begin
(

let uu____1411 = (tc_one_file dsenv env FStar_Pervasives_Native.None intf_or_impl)
in (match (uu____1411) with
| (m, dsenv1, env1) -> begin
((remaining1), ((((m)::[]), (dsenv1), (env1))))
end))
end
| [] -> begin
(([]), ((([]), (dsenv), (env))))
end)
in (match (uu____1297) with
| (remaining1, (nmods, dsenv1, env1)) -> begin
((remaining1), (nmods), (((dsenv1), (env1))))
end))
end)))


let rec tc_fold_interleave : ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * uenv)  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * uenv) = (fun acc remaining -> (match (remaining) with
| [] -> begin
acc
end
| uu____1617 -> begin
(

let uu____1620 = acc
in (match (uu____1620) with
| (mods, uenv) -> begin
(

let uu____1655 = (tc_one_file_from_remaining remaining uenv)
in (match (uu____1655) with
| (remaining1, nmods, (dsenv, env)) -> begin
(tc_fold_interleave (((FStar_List.append mods nmods)), (((dsenv), (env)))) remaining1)
end))
end))
end))


let batch_mode_tc_no_prims : FStar_ToSyntax_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env filenames -> (

let uu____1750 = (tc_fold_interleave (([]), (((dsenv), (env)))) filenames)
in (match (uu____1750) with
| (all_mods, (dsenv1, env1)) -> begin
((

let uu____1807 = ((FStar_Options.interactive ()) && (

let uu____1809 = (FStar_Errors.get_err_count ())
in (Prims.op_Equality uu____1809 (Prims.parse_int "0"))))
in (match (uu____1807) with
| true -> begin
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end
| uu____1810 -> begin
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end));
((all_mods), (dsenv1), (env1));
)
end)))


let batch_mode_tc : Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_ToSyntax_Env.env * FStar_TypeChecker_Env.env) = (fun filenames -> (

let uu____1837 = (

let uu____1848 = (init_env ())
in (tc_prims uu____1848))
in (match (uu____1837) with
| (prims_mod, dsenv, env) -> begin
((

let uu____1877 = ((

let uu____1880 = (FStar_Options.explicit_deps ())
in (not (uu____1880))) && (FStar_Options.debug_any ()))
in (match (uu____1877) with
| true -> begin
((FStar_Util.print_endline "Auto-deps kicked in; here\'s some info.");
(FStar_Util.print1 "Here\'s the list of filenames we will process: %s\n" (FStar_String.concat " " filenames));
(

let uu____1883 = (

let uu____1884 = (FStar_Options.verify_module ())
in (FStar_String.concat " " uu____1884))
in (FStar_Util.print1 "Here\'s the list of modules we will verify: %s\n" uu____1883));
)
end
| uu____1887 -> begin
()
end));
(

let uu____1888 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (uu____1888) with
| (all_mods, dsenv1, env1) -> begin
(((prims_mod)::all_mods), (dsenv1), (env1))
end));
)
end)))




