
open Prims
open FStar_Pervasives

let module_or_interface_name : FStar_Syntax_Syntax.modul  ->  (Prims.bool * FStar_Ident.lident) = (fun m -> ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name)))


let user_tactics_modules : Prims.string Prims.list FStar_ST.ref = FStar_TypeChecker_Tc.user_tactics_modules


let with_tcenv : 'a . FStar_TypeChecker_Env.env  ->  'a FStar_ToSyntax_Env.withenv  ->  ('a * FStar_TypeChecker_Env.env) = (fun env f -> (

let uu____47 = (f env.FStar_TypeChecker_Env.dsenv)
in (match (uu____47) with
| (a, dsenv) -> begin
((a), ((

let uu___235_61 = env
in {FStar_TypeChecker_Env.solver = uu___235_61.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___235_61.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___235_61.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___235_61.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___235_61.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___235_61.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___235_61.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___235_61.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___235_61.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___235_61.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___235_61.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___235_61.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___235_61.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___235_61.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___235_61.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___235_61.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___235_61.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___235_61.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___235_61.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___235_61.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___235_61.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___235_61.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___235_61.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___235_61.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___235_61.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___235_61.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___235_61.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___235_61.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___235_61.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___235_61.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___235_61.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___235_61.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = dsenv})))
end)))


let parse : FStar_TypeChecker_Env.env  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env pre_fn fn -> (

let uu____86 = (FStar_Parser_Driver.parse_file fn)
in (match (uu____86) with
| (ast, uu____102) -> begin
(

let uu____115 = (match (pre_fn) with
| FStar_Pervasives_Native.None -> begin
((ast), (env))
end
| FStar_Pervasives_Native.Some (pre_fn1) -> begin
(

let uu____125 = (FStar_Parser_Driver.parse_file pre_fn1)
in (match (uu____125) with
| (pre_ast, uu____141) -> begin
(match (((pre_ast), (ast))) with
| (FStar_Parser_AST.Interface (lid1, decls1, uu____160), FStar_Parser_AST.Module (lid2, decls2)) when (FStar_Ident.lid_equals lid1 lid2) -> begin
(

let uu____171 = (

let uu____176 = (FStar_ToSyntax_Interleave.initialize_interface lid1 decls1)
in (FStar_All.pipe_left (with_tcenv env) uu____176))
in (match (uu____171) with
| (uu____193, env1) -> begin
(

let uu____195 = (FStar_ToSyntax_Interleave.interleave_module ast true)
in (FStar_All.pipe_left (with_tcenv env1) uu____195))
end))
end
| uu____208 -> begin
(FStar_Exn.raise (FStar_Errors.Err ("mismatch between pre-module and module\n")))
end)
end))
end)
in (match (uu____115) with
| (ast1, env1) -> begin
(

let uu____223 = (FStar_ToSyntax_ToSyntax.ast_modul_to_modul ast1)
in (FStar_All.pipe_left (with_tcenv env1) uu____223))
end))
end)))


let init_env : Prims.unit  ->  FStar_TypeChecker_Env.env = (fun uu____239 -> (

let solver1 = (

let uu____241 = (FStar_Options.lax ())
in (match (uu____241) with
| true -> begin
FStar_SMTEncoding_Solver.dummy
end
| uu____242 -> begin
(

let uu___236_243 = FStar_SMTEncoding_Solver.solver
in {FStar_TypeChecker_Env.init = uu___236_243.FStar_TypeChecker_Env.init; FStar_TypeChecker_Env.push = uu___236_243.FStar_TypeChecker_Env.push; FStar_TypeChecker_Env.pop = uu___236_243.FStar_TypeChecker_Env.pop; FStar_TypeChecker_Env.encode_modul = uu___236_243.FStar_TypeChecker_Env.encode_modul; FStar_TypeChecker_Env.encode_sig = uu___236_243.FStar_TypeChecker_Env.encode_sig; FStar_TypeChecker_Env.preprocess = FStar_Tactics_Interpreter.preprocess; FStar_TypeChecker_Env.solve = uu___236_243.FStar_TypeChecker_Env.solve; FStar_TypeChecker_Env.finish = uu___236_243.FStar_TypeChecker_Env.finish; FStar_TypeChecker_Env.refresh = uu___236_243.FStar_TypeChecker_Env.refresh})
end))
in (

let env = (FStar_TypeChecker_Env.initial_env FStar_TypeChecker_TcTerm.tc_term FStar_TypeChecker_TcTerm.type_of_tot_term FStar_TypeChecker_TcTerm.universe_of solver1 FStar_Parser_Const.prims_lid)
in (

let env1 = (

let uu___237_246 = env
in {FStar_TypeChecker_Env.solver = uu___237_246.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___237_246.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___237_246.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___237_246.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___237_246.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___237_246.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___237_246.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___237_246.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___237_246.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___237_246.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___237_246.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___237_246.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___237_246.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___237_246.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___237_246.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___237_246.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___237_246.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___237_246.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___237_246.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___237_246.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___237_246.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___237_246.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___237_246.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___237_246.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___237_246.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___237_246.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___237_246.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___237_246.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = FStar_Tactics_Interpreter.synth; FStar_TypeChecker_Env.is_native_tactic = uu___237_246.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___237_246.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___237_246.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___237_246.FStar_TypeChecker_Env.dsenv})
in (

let env2 = (

let uu___238_248 = env1
in {FStar_TypeChecker_Env.solver = uu___238_248.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___238_248.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___238_248.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___238_248.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___238_248.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___238_248.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___238_248.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___238_248.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___238_248.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___238_248.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___238_248.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___238_248.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___238_248.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___238_248.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___238_248.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___238_248.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___238_248.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___238_248.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___238_248.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___238_248.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___238_248.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___238_248.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___238_248.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___238_248.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___238_248.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___238_248.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___238_248.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___238_248.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___238_248.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = FStar_Tactics_Native.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___238_248.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___238_248.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___238_248.FStar_TypeChecker_Env.dsenv})
in ((env2.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env2);
env2;
))))))


let tc_prims : FStar_TypeChecker_Env.env  ->  ((FStar_Syntax_Syntax.modul * Prims.int) * FStar_TypeChecker_Env.env) = (fun env -> (

let prims_filename = (FStar_Options.prims ())
in (

let uu____271 = (parse env FStar_Pervasives_Native.None prims_filename)
in (match (uu____271) with
| (prims_mod, env1) -> begin
(

let uu____286 = (FStar_Util.record_time (fun uu____300 -> (FStar_TypeChecker_Tc.check_module env1 prims_mod)))
in (match (uu____286) with
| ((prims_mod1, env2), elapsed_time) -> begin
((((prims_mod1), (elapsed_time))), (env2))
end))
end))))


let tc_one_fragment : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Parser_ParseIt.input_frag  ->  (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_TypeChecker_Env.env) = (fun curmod env frag -> (

let acceptable_mod_name = (fun modul -> (

let uu____346 = (

let uu____347 = (

let uu____348 = (FStar_Options.file_list ())
in (FStar_List.hd uu____348))
in (FStar_Parser_Dep.lowercase_module_name uu____347))
in (

let uu____351 = (

let uu____352 = (FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name)
in (FStar_String.lowercase uu____352))
in (Prims.op_Equality uu____346 uu____351))))
in (

let range_of_first_mod_decl = (fun modul -> (match (modul) with
| FStar_Parser_AST.Module (uu____357, ({FStar_Parser_AST.d = uu____358; FStar_Parser_AST.drange = d; FStar_Parser_AST.doc = uu____360; FStar_Parser_AST.quals = uu____361; FStar_Parser_AST.attrs = uu____362})::uu____363) -> begin
d
end
| FStar_Parser_AST.Interface (uu____370, ({FStar_Parser_AST.d = uu____371; FStar_Parser_AST.drange = d; FStar_Parser_AST.doc = uu____373; FStar_Parser_AST.quals = uu____374; FStar_Parser_AST.attrs = uu____375})::uu____376, uu____377) -> begin
d
end
| uu____384 -> begin
FStar_Range.dummyRange
end))
in (

let uu____385 = (FStar_Parser_Driver.parse_fragment frag)
in (match (uu____385) with
| FStar_Parser_Driver.Empty -> begin
((curmod), (env))
end
| FStar_Parser_Driver.Decls ([]) -> begin
((curmod), (env))
end
| FStar_Parser_Driver.Modul (ast_modul) -> begin
(

let uu____397 = (

let uu____402 = (FStar_ToSyntax_Interleave.interleave_module ast_modul false)
in (FStar_All.pipe_left (with_tcenv env) uu____402))
in (match (uu____397) with
| (ast_modul1, env1) -> begin
(

let uu____423 = (

let uu____428 = (FStar_ToSyntax_ToSyntax.partial_ast_modul_to_modul curmod ast_modul1)
in (FStar_All.pipe_left (with_tcenv env1) uu____428))
in (match (uu____423) with
| (modul, env2) -> begin
((match (curmod) with
| FStar_Pervasives_Native.Some (uu____450) when (

let uu____451 = (acceptable_mod_name modul)
in (not (uu____451))) -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Interactive mode only supports a single module at the top-level"), ((range_of_first_mod_decl ast_modul1))))))
end
| uu____452 -> begin
()
end);
(

let uu____455 = (

let uu____464 = (FStar_ToSyntax_Env.syntax_only env2.FStar_TypeChecker_Env.dsenv)
in (match (uu____464) with
| true -> begin
((modul), ([]), (env2))
end
| uu____475 -> begin
(FStar_TypeChecker_Tc.tc_partial_modul env2 modul false)
end))
in (match (uu____455) with
| (modul1, uu____483, env3) -> begin
((FStar_Pervasives_Native.Some (modul1)), (env3))
end));
)
end))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(match (curmod) with
| FStar_Pervasives_Native.None -> begin
(

let uu____500 = (FStar_List.hd ast_decls)
in (match (uu____500) with
| {FStar_Parser_AST.d = uu____507; FStar_Parser_AST.drange = rng; FStar_Parser_AST.doc = uu____509; FStar_Parser_AST.quals = uu____510; FStar_Parser_AST.attrs = uu____511} -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("First statement must be a module declaration"), (rng)))))
end))
end
| FStar_Pervasives_Native.Some (modul) -> begin
(

let uu____521 = (FStar_Util.fold_map (fun env1 a_decl -> (

let uu____539 = (

let uu____546 = (FStar_ToSyntax_Interleave.prefix_with_interface_decls a_decl)
in (FStar_All.pipe_left (with_tcenv env1) uu____546))
in (match (uu____539) with
| (decls, env2) -> begin
((env2), (decls))
end))) env ast_decls)
in (match (uu____521) with
| (env1, ast_decls_l) -> begin
(

let uu____597 = (

let uu____602 = (FStar_ToSyntax_ToSyntax.decls_to_sigelts (FStar_List.flatten ast_decls_l))
in (FStar_All.pipe_left (with_tcenv env1) uu____602))
in (match (uu____597) with
| (sigelts, env2) -> begin
(

let uu____623 = (

let uu____632 = (FStar_ToSyntax_Env.syntax_only env2.FStar_TypeChecker_Env.dsenv)
in (match (uu____632) with
| true -> begin
((modul), ([]), (env2))
end
| uu____643 -> begin
(FStar_TypeChecker_Tc.tc_more_partial_modul env2 modul sigelts)
end))
in (match (uu____623) with
| (modul1, uu____651, env3) -> begin
((FStar_Pervasives_Native.Some (modul1)), (env3))
end))
end))
end))
end)
end)))))


let load_interface_decls : FStar_TypeChecker_Env.env  ->  FStar_Parser_ParseIt.filename  ->  FStar_TypeChecker_Env.env = (fun env interface_file_name -> (

let r = (FStar_Parser_ParseIt.parse (FStar_Util.Inl (interface_file_name)))
in (match (r) with
| FStar_Util.Inl (FStar_Util.Inl (FStar_Parser_AST.Interface (l, decls, uu____688)), uu____689) -> begin
(

let uu____734 = (

let uu____739 = (FStar_ToSyntax_Interleave.initialize_interface l decls)
in (FStar_All.pipe_left (with_tcenv env) uu____739))
in (FStar_Pervasives_Native.snd uu____734))
end
| FStar_Util.Inl (uu____752) -> begin
(

let uu____777 = (

let uu____778 = (FStar_Util.format1 "Unexpected result from parsing %s; expected a single interface" interface_file_name)
in FStar_Errors.Err (uu____778))
in (FStar_Exn.raise uu____777))
end
| FStar_Util.Inr (err1, rng) -> begin
(FStar_Exn.raise (FStar_Errors.Error (((err1), (rng)))))
end)))


let tc_one_file : FStar_TypeChecker_Env.env  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  ((FStar_Syntax_Syntax.modul * Prims.int) * FStar_TypeChecker_Env.env) = (fun env pre_fn fn -> (

let checked_file_name = (

let uu____828 = (FStar_Parser_ParseIt.find_file fn)
in (Prims.strcat uu____828 ".checked"))
in (

let lax_checked_file_name = (Prims.strcat checked_file_name ".lax")
in (

let lax_ok = (

let uu____831 = (FStar_Options.should_verify_file fn)
in (not (uu____831)))
in (

let cache_file_to_write = (match (lax_ok) with
| true -> begin
lax_checked_file_name
end
| uu____833 -> begin
checked_file_name
end)
in (

let cache_file_to_read = (fun uu____839 -> (match ((FStar_Util.file_exists checked_file_name)) with
| true -> begin
FStar_Pervasives_Native.Some (checked_file_name)
end
| uu____842 -> begin
(match ((lax_ok && (FStar_Util.file_exists lax_checked_file_name))) with
| true -> begin
FStar_Pervasives_Native.Some (lax_checked_file_name)
end
| uu____845 -> begin
FStar_Pervasives_Native.None
end)
end))
in (

let tc_source_file = (fun uu____857 -> (

let uu____858 = (parse env pre_fn fn)
in (match (uu____858) with
| (fmod, env1) -> begin
(

let check_mod = (fun uu____884 -> (

let uu____885 = (FStar_Util.record_time (fun uu____899 -> (FStar_TypeChecker_Tc.check_module env1 fmod)))
in (match (uu____885) with
| ((tcmod, env2), time) -> begin
((((tcmod), (time))), (env2))
end)))
in (

let uu____919 = (

let uu____928 = ((FStar_Options.should_verify fmod.FStar_Syntax_Syntax.name.FStar_Ident.str) && ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ())))
in (match (uu____928) with
| true -> begin
(

let uu____937 = (FStar_Parser_ParseIt.find_file fn)
in (FStar_SMTEncoding_Solver.with_hints_db uu____937 check_mod))
end
| uu____946 -> begin
(check_mod ())
end))
in (match (uu____919) with
| (tcmod, env2) -> begin
((

let uu____966 = (FStar_Options.cache_checked_modules ())
in (match (uu____966) with
| true -> begin
(

let uu____967 = tcmod
in (match (uu____967) with
| (tcmod1, uu____973) -> begin
(

let mii = (FStar_ToSyntax_Env.inclusion_info env2.FStar_TypeChecker_Env.dsenv tcmod1.FStar_Syntax_Syntax.name)
in (

let uu____975 = (

let uu____982 = (FStar_Util.digest_of_file fn)
in ((uu____982), (tcmod1), (mii)))
in (FStar_Util.save_value_to_file cache_file_to_write uu____975)))
end))
end
| uu____989 -> begin
()
end));
((tcmod), (env2));
)
end)))
end)))
in (

let uu____994 = (FStar_Options.cache_checked_modules ())
in (match (uu____994) with
| true -> begin
(match ((cache_file_to_read ())) with
| FStar_Pervasives_Native.None -> begin
(tc_source_file ())
end
| FStar_Pervasives_Native.Some (cache_file) -> begin
(

let uu____1012 = (FStar_Util.load_value_from_file cache_file)
in (match (uu____1012) with
| FStar_Pervasives_Native.None -> begin
(failwith (Prims.strcat "Corrupt file: " cache_file))
end
| FStar_Pervasives_Native.Some (digest, tcmod, mii) -> begin
(

let uu____1058 = (

let uu____1059 = (FStar_Util.digest_of_file fn)
in (Prims.op_Equality digest uu____1059))
in (match (uu____1058) with
| true -> begin
(

let uu____1068 = (

let uu____1073 = (FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod mii)
in (FStar_All.pipe_left (with_tcenv env) uu____1073))
in (match (uu____1068) with
| (uu____1094, env1) -> begin
(

let env2 = (FStar_TypeChecker_Tc.load_checked_module env1 tcmod)
in ((((tcmod), ((Prims.parse_int "0")))), (env2)))
end))
end
| uu____1101 -> begin
(

let uu____1102 = (FStar_Util.format1 "The file %s is stale; delete it" cache_file)
in (failwith uu____1102))
end))
end))
end)
end
| uu____1111 -> begin
(tc_source_file ())
end)))))))))


let needs_interleaving : Prims.string  ->  Prims.string  ->  Prims.bool = (fun intf impl -> (

let m1 = (FStar_Parser_Dep.lowercase_module_name intf)
in (

let m2 = (FStar_Parser_Dep.lowercase_module_name impl)
in (((Prims.op_Equality m1 m2) && (

let uu____1123 = (FStar_Util.get_file_extension intf)
in (FStar_List.mem uu____1123 (("fsti")::("fsi")::[])))) && (

let uu____1125 = (FStar_Util.get_file_extension impl)
in (FStar_List.mem uu____1125 (("fst")::("fs")::[])))))))


let pop_context : FStar_TypeChecker_Env.env  ->  Prims.string  ->  Prims.unit = (fun env msg -> ((

let uu____1135 = (FStar_ToSyntax_Env.pop ())
in (FStar_All.pipe_right uu____1135 FStar_Pervasives.ignore));
(

let uu____1137 = (FStar_TypeChecker_Env.pop env msg)
in (FStar_All.pipe_right uu____1137 FStar_Pervasives.ignore));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
))


let push_context : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Env.env = (fun env msg -> (

let dsenv = (FStar_ToSyntax_Env.push env.FStar_TypeChecker_Env.dsenv)
in (

let env1 = (FStar_TypeChecker_Env.push env msg)
in (

let uu___239_1148 = env1
in {FStar_TypeChecker_Env.solver = uu___239_1148.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___239_1148.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___239_1148.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___239_1148.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___239_1148.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___239_1148.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___239_1148.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___239_1148.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___239_1148.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___239_1148.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___239_1148.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___239_1148.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___239_1148.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___239_1148.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___239_1148.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___239_1148.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___239_1148.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___239_1148.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___239_1148.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___239_1148.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___239_1148.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___239_1148.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___239_1148.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___239_1148.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___239_1148.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___239_1148.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___239_1148.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___239_1148.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___239_1148.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___239_1148.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___239_1148.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___239_1148.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = dsenv}))))


let tc_one_file_from_remaining : Prims.string Prims.list  ->  FStar_TypeChecker_Env.env  ->  (Prims.string Prims.list * (FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_TypeChecker_Env.env) = (fun remaining env -> (

let uu____1175 = (match (remaining) with
| (intf)::(impl)::remaining1 when (needs_interleaving intf impl) -> begin
(

let uu____1213 = (tc_one_file env (FStar_Pervasives_Native.Some (intf)) impl)
in (match (uu____1213) with
| (m, env1) -> begin
((remaining1), ((((m)::[]), (env1))))
end))
end
| (intf_or_impl)::remaining1 -> begin
(

let uu____1278 = (tc_one_file env FStar_Pervasives_Native.None intf_or_impl)
in (match (uu____1278) with
| (m, env1) -> begin
((remaining1), ((((m)::[]), (env1))))
end))
end
| [] -> begin
(([]), ((([]), (env))))
end)
in (match (uu____1175) with
| (remaining1, (nmods, env1)) -> begin
((remaining1), (nmods), (env1))
end)))


let rec tc_fold_interleave : ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_TypeChecker_Env.env)  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_TypeChecker_Env.env) = (fun acc remaining -> (match (remaining) with
| [] -> begin
acc
end
| uu____1464 -> begin
(

let uu____1467 = acc
in (match (uu____1467) with
| (mods, env) -> begin
(

let uu____1502 = (tc_one_file_from_remaining remaining env)
in (match (uu____1502) with
| (remaining1, nmods, env1) -> begin
(tc_fold_interleave (((FStar_List.append mods nmods)), (env1)) remaining1)
end))
end))
end))


let batch_mode_tc_no_prims : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_TypeChecker_Env.env) = (fun env filenames -> (

let uu____1578 = (tc_fold_interleave (([]), (env)) filenames)
in (match (uu____1578) with
| (all_mods, env1) -> begin
((

let uu____1624 = ((FStar_Options.interactive ()) && (

let uu____1626 = (FStar_Errors.get_err_count ())
in (Prims.op_Equality uu____1626 (Prims.parse_int "0"))))
in (match (uu____1624) with
| true -> begin
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end
| uu____1627 -> begin
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end));
((all_mods), (env1));
)
end)))


let batch_mode_tc : Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_TypeChecker_Env.env) = (fun filenames -> (

let uu____1652 = (

let uu____1661 = (init_env ())
in (tc_prims uu____1661))
in (match (uu____1652) with
| (prims_mod, env) -> begin
((

let uu____1683 = ((

let uu____1686 = (FStar_Options.explicit_deps ())
in (not (uu____1686))) && (FStar_Options.debug_any ()))
in (match (uu____1683) with
| true -> begin
((FStar_Util.print_endline "Auto-deps kicked in; here\'s some info.");
(FStar_Util.print1 "Here\'s the list of filenames we will process: %s\n" (FStar_String.concat " " filenames));
(

let uu____1689 = (

let uu____1690 = (FStar_Options.verify_module ())
in (FStar_String.concat " " uu____1690))
in (FStar_Util.print1 "Here\'s the list of modules we will verify: %s\n" uu____1689));
)
end
| uu____1693 -> begin
()
end));
(

let uu____1694 = (batch_mode_tc_no_prims env filenames)
in (match (uu____1694) with
| (all_mods, env1) -> begin
(((prims_mod)::all_mods), (env1))
end));
)
end)))




