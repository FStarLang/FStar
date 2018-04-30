
open Prims
open FStar_Pervasives

let cache_version_number : Prims.int = (Prims.parse_int "1")


let module_or_interface_name : FStar_Syntax_Syntax.modul  ->  (Prims.bool * FStar_Ident.lident) = (fun m -> ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name)))


let with_tcenv : 'a . FStar_TypeChecker_Env.env  ->  'a FStar_Syntax_DsEnv.withenv  ->  ('a * FStar_TypeChecker_Env.env) = (fun env f -> (

let uu____41 = (f env.FStar_TypeChecker_Env.dsenv)
in (match (uu____41) with
| (a, dsenv1) -> begin
((a), ((

let uu___55_55 = env
in {FStar_TypeChecker_Env.solver = uu___55_55.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___55_55.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___55_55.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___55_55.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___55_55.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___55_55.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___55_55.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___55_55.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___55_55.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___55_55.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___55_55.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___55_55.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___55_55.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___55_55.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___55_55.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___55_55.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___55_55.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___55_55.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___55_55.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___55_55.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___55_55.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___55_55.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___55_55.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___55_55.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___55_55.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___55_55.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___55_55.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___55_55.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___55_55.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___55_55.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___55_55.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___55_55.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___55_55.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___55_55.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___55_55.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___55_55.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = dsenv1; FStar_TypeChecker_Env.dep_graph = uu___55_55.FStar_TypeChecker_Env.dep_graph})))
end)))


let parse : FStar_TypeChecker_Env.env  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env pre_fn fn -> (

let uu____83 = (FStar_Parser_Driver.parse_file fn)
in (match (uu____83) with
| (ast, uu____99) -> begin
(

let uu____112 = (match (pre_fn) with
| FStar_Pervasives_Native.None -> begin
((ast), (env))
end
| FStar_Pervasives_Native.Some (pre_fn1) -> begin
(

let uu____122 = (FStar_Parser_Driver.parse_file pre_fn1)
in (match (uu____122) with
| (pre_ast, uu____138) -> begin
(match (((pre_ast), (ast))) with
| (FStar_Parser_AST.Interface (lid1, decls1, uu____157), FStar_Parser_AST.Module (lid2, decls2)) when (FStar_Ident.lid_equals lid1 lid2) -> begin
(

let uu____168 = (

let uu____173 = (FStar_ToSyntax_Interleave.initialize_interface lid1 decls1)
in (FStar_All.pipe_left (with_tcenv env) uu____173))
in (match (uu____168) with
| (uu____193, env1) -> begin
(

let uu____195 = (FStar_ToSyntax_Interleave.interleave_module ast true)
in (FStar_All.pipe_left (with_tcenv env1) uu____195))
end))
end
| uu____211 -> begin
(FStar_Errors.raise_err ((FStar_Errors.Fatal_PreModuleMismatch), ("mismatch between pre-module and module\n")))
end)
end))
end)
in (match (uu____112) with
| (ast1, env1) -> begin
(

let uu____226 = (FStar_ToSyntax_ToSyntax.ast_modul_to_modul ast1)
in (FStar_All.pipe_left (with_tcenv env1) uu____226))
end))
end)))


let init_env : FStar_Parser_Dep.deps  ->  FStar_TypeChecker_Env.env = (fun deps -> (

let solver1 = (

let uu____248 = (FStar_Options.lax ())
in (match (uu____248) with
| true -> begin
FStar_SMTEncoding_Solver.dummy
end
| uu____249 -> begin
(

let uu___56_250 = FStar_SMTEncoding_Solver.solver
in {FStar_TypeChecker_Env.init = uu___56_250.FStar_TypeChecker_Env.init; FStar_TypeChecker_Env.push = uu___56_250.FStar_TypeChecker_Env.push; FStar_TypeChecker_Env.pop = uu___56_250.FStar_TypeChecker_Env.pop; FStar_TypeChecker_Env.encode_modul = uu___56_250.FStar_TypeChecker_Env.encode_modul; FStar_TypeChecker_Env.encode_sig = uu___56_250.FStar_TypeChecker_Env.encode_sig; FStar_TypeChecker_Env.preprocess = FStar_Tactics_Interpreter.preprocess; FStar_TypeChecker_Env.solve = uu___56_250.FStar_TypeChecker_Env.solve; FStar_TypeChecker_Env.finish = uu___56_250.FStar_TypeChecker_Env.finish; FStar_TypeChecker_Env.refresh = uu___56_250.FStar_TypeChecker_Env.refresh})
end))
in (

let env = (FStar_TypeChecker_Env.initial_env deps FStar_TypeChecker_TcTerm.tc_term FStar_TypeChecker_TcTerm.type_of_tot_term FStar_TypeChecker_TcTerm.universe_of FStar_TypeChecker_TcTerm.check_type_of_well_typed_term solver1 FStar_Parser_Const.prims_lid)
in (

let env1 = (

let uu___57_253 = env
in {FStar_TypeChecker_Env.solver = uu___57_253.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___57_253.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___57_253.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___57_253.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___57_253.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___57_253.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___57_253.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___57_253.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___57_253.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___57_253.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___57_253.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___57_253.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___57_253.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___57_253.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___57_253.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___57_253.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___57_253.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___57_253.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___57_253.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___57_253.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___57_253.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___57_253.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___57_253.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___57_253.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___57_253.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___57_253.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___57_253.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___57_253.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___57_253.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___57_253.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___57_253.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = FStar_Tactics_Interpreter.synthesize; FStar_TypeChecker_Env.splice = uu___57_253.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___57_253.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___57_253.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___57_253.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___57_253.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___57_253.FStar_TypeChecker_Env.dep_graph})
in (

let env2 = (

let uu___58_255 = env1
in {FStar_TypeChecker_Env.solver = uu___58_255.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___58_255.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___58_255.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___58_255.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___58_255.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___58_255.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___58_255.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___58_255.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___58_255.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___58_255.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___58_255.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___58_255.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___58_255.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___58_255.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___58_255.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___58_255.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___58_255.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___58_255.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___58_255.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___58_255.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___58_255.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___58_255.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___58_255.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___58_255.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___58_255.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___58_255.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___58_255.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___58_255.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___58_255.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___58_255.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___58_255.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___58_255.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = FStar_Tactics_Interpreter.splice; FStar_TypeChecker_Env.is_native_tactic = uu___58_255.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___58_255.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___58_255.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___58_255.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___58_255.FStar_TypeChecker_Env.dep_graph})
in (

let env3 = (

let uu___59_257 = env2
in {FStar_TypeChecker_Env.solver = uu___59_257.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___59_257.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___59_257.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___59_257.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___59_257.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___59_257.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___59_257.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___59_257.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___59_257.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___59_257.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___59_257.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___59_257.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___59_257.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___59_257.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___59_257.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___59_257.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___59_257.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___59_257.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___59_257.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___59_257.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___59_257.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___59_257.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___59_257.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___59_257.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___59_257.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___59_257.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___59_257.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___59_257.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___59_257.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___59_257.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___59_257.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___59_257.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___59_257.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = FStar_Tactics_Native.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___59_257.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___59_257.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___59_257.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___59_257.FStar_TypeChecker_Env.dep_graph})
in ((env3.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env3);
env3;
)))))))


let tc_one_fragment : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Parser_ParseIt.input_frag  ->  (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_TypeChecker_Env.env) = (fun curmod env frag -> (

let acceptable_mod_name = (fun modul -> (

let uu____290 = (

let uu____291 = (

let uu____292 = (FStar_Options.file_list ())
in (FStar_List.hd uu____292))
in (FStar_Parser_Dep.lowercase_module_name uu____291))
in (

let uu____295 = (

let uu____296 = (FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name)
in (FStar_String.lowercase uu____296))
in (Prims.op_Equality uu____290 uu____295))))
in (

let range_of_first_mod_decl = (fun modul -> (match (modul) with
| FStar_Parser_AST.Module (uu____303, ({FStar_Parser_AST.d = uu____304; FStar_Parser_AST.drange = d; FStar_Parser_AST.doc = uu____306; FStar_Parser_AST.quals = uu____307; FStar_Parser_AST.attrs = uu____308})::uu____309) -> begin
d
end
| FStar_Parser_AST.Interface (uu____316, ({FStar_Parser_AST.d = uu____317; FStar_Parser_AST.drange = d; FStar_Parser_AST.doc = uu____319; FStar_Parser_AST.quals = uu____320; FStar_Parser_AST.attrs = uu____321})::uu____322, uu____323) -> begin
d
end
| uu____330 -> begin
FStar_Range.dummyRange
end))
in (

let uu____331 = (FStar_Parser_Driver.parse_fragment frag)
in (match (uu____331) with
| FStar_Parser_Driver.Empty -> begin
((curmod), (env))
end
| FStar_Parser_Driver.Decls ([]) -> begin
((curmod), (env))
end
| FStar_Parser_Driver.Modul (ast_modul) -> begin
(

let uu____343 = (

let uu____348 = (FStar_ToSyntax_Interleave.interleave_module ast_modul false)
in (FStar_All.pipe_left (with_tcenv env) uu____348))
in (match (uu____343) with
| (ast_modul1, env1) -> begin
(

let uu____372 = (

let uu____377 = (FStar_ToSyntax_ToSyntax.partial_ast_modul_to_modul curmod ast_modul1)
in (FStar_All.pipe_left (with_tcenv env1) uu____377))
in (match (uu____372) with
| (modul, env2) -> begin
((

let uu____402 = (

let uu____403 = (acceptable_mod_name modul)
in (not (uu____403)))
in (match (uu____402) with
| true -> begin
(

let msg = (

let uu____405 = (

let uu____406 = (

let uu____407 = (FStar_Options.file_list ())
in (FStar_List.hd uu____407))
in (FStar_Parser_Dep.module_name_of_file uu____406))
in (FStar_Util.format1 "Interactive mode only supports a single module at the top-level. Expected module %s" uu____405))
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_NonSingletonTopLevelModule), (msg)) (range_of_first_mod_decl ast_modul1)))
end
| uu____410 -> begin
()
end));
(

let uu____411 = (

let uu____420 = (FStar_Syntax_DsEnv.syntax_only env2.FStar_TypeChecker_Env.dsenv)
in (match (uu____420) with
| true -> begin
((modul), ([]), (env2))
end
| uu____431 -> begin
(FStar_TypeChecker_Tc.tc_partial_modul env2 modul)
end))
in (match (uu____411) with
| (modul1, uu____439, env3) -> begin
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

let uu____456 = (FStar_List.hd ast_decls)
in (match (uu____456) with
| {FStar_Parser_AST.d = uu____463; FStar_Parser_AST.drange = rng; FStar_Parser_AST.doc = uu____465; FStar_Parser_AST.quals = uu____466; FStar_Parser_AST.attrs = uu____467} -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_ModuleFirstStatement), ("First statement must be a module declaration")) rng)
end))
end
| FStar_Pervasives_Native.Some (modul) -> begin
(

let uu____477 = (FStar_Util.fold_map (fun env1 a_decl -> (

let uu____495 = (

let uu____502 = (FStar_ToSyntax_Interleave.prefix_with_interface_decls a_decl)
in (FStar_All.pipe_left (with_tcenv env1) uu____502))
in (match (uu____495) with
| (decls, env2) -> begin
((env2), (decls))
end))) env ast_decls)
in (match (uu____477) with
| (env1, ast_decls_l) -> begin
(

let uu____556 = (

let uu____563 = (FStar_ToSyntax_ToSyntax.decls_to_sigelts (FStar_List.flatten ast_decls_l))
in (FStar_All.pipe_left (with_tcenv env1) uu____563))
in (match (uu____556) with
| (sigelts, env2) -> begin
(

let uu____599 = (

let uu____608 = (FStar_Syntax_DsEnv.syntax_only env2.FStar_TypeChecker_Env.dsenv)
in (match (uu____608) with
| true -> begin
((modul), ([]), (env2))
end
| uu____619 -> begin
(FStar_TypeChecker_Tc.tc_more_partial_modul env2 modul sigelts)
end))
in (match (uu____599) with
| (modul1, uu____627, env3) -> begin
((FStar_Pervasives_Native.Some (modul1)), (env3))
end))
end))
end))
end)
end)))))


let load_interface_decls : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Env.env = (fun env interface_file_name -> (

let r = (FStar_Parser_ParseIt.parse (FStar_Parser_ParseIt.Filename (interface_file_name)))
in (match (r) with
| FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inl (FStar_Parser_AST.Interface (l, decls, uu____648)), uu____649) -> begin
(

let uu____668 = (

let uu____673 = (FStar_ToSyntax_Interleave.initialize_interface l decls)
in (FStar_All.pipe_left (with_tcenv env) uu____673))
in (FStar_Pervasives_Native.snd uu____668))
end
| FStar_Parser_ParseIt.ASTFragment (uu____689) -> begin
(

let uu____700 = (

let uu____705 = (FStar_Util.format1 "Unexpected result from parsing %s; expected a single interface" interface_file_name)
in ((FStar_Errors.Fatal_ParseErrors), (uu____705)))
in (FStar_Errors.raise_err uu____700))
end
| FStar_Parser_ParseIt.ParseError (err, msg, rng) -> begin
(FStar_Exn.raise (FStar_Errors.Error (((err), (msg), (rng)))))
end
| FStar_Parser_ParseIt.Term (uu____709) -> begin
(failwith "Impossible: parsing a Toplevel always results in an ASTFragment")
end)))


let load_module_from_cache : FStar_TypeChecker_Env.env  ->  Prims.string  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_Syntax_DsEnv.module_inclusion_info) FStar_Pervasives_Native.option = (

let some_cache_invalid = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let invalidate_cache = (fun fn -> (FStar_ST.op_Colon_Equals some_cache_invalid (FStar_Pervasives_Native.Some (()))))
in (

let load1 = (fun env source_file cache_file -> (

let uu____818 = (FStar_Util.load_value_from_file cache_file)
in (match (uu____818) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl ("Corrupt")
end
| FStar_Pervasives_Native.Some (vnum, digest, tcmod, tcmod_iface_opt, mii) -> begin
(match ((Prims.op_disEquality vnum cache_version_number)) with
| true -> begin
FStar_Util.Inl ("Stale, because inconsistent cache version")
end
| uu____954 -> begin
(

let uu____955 = (FStar_Parser_Dep.hash_dependences env.FStar_TypeChecker_Env.dep_graph source_file)
in (match (uu____955) with
| FStar_Pervasives_Native.Some (digest') -> begin
(match ((Prims.op_Equality digest digest')) with
| true -> begin
FStar_Util.Inr (((tcmod), (tcmod_iface_opt), (mii)))
end
| uu____1017 -> begin
((

let uu____1019 = (FStar_Options.debug_any ())
in (match (uu____1019) with
| true -> begin
((

let uu____1021 = (FStar_Util.string_of_int (FStar_List.length digest'))
in (

let uu____1026 = (FStar_Parser_Dep.print_digest digest')
in (

let uu____1027 = (FStar_Util.string_of_int (FStar_List.length digest))
in (

let uu____1032 = (FStar_Parser_Dep.print_digest digest)
in (FStar_Util.print4 "Expected (%s) hashes:\n%s\n\nGot (%s) hashes:\n\t%s\n" uu____1021 uu____1026 uu____1027 uu____1032)))));
(match ((Prims.op_Equality (FStar_List.length digest) (FStar_List.length digest'))) with
| true -> begin
(FStar_List.iter2 (fun uu____1057 uu____1058 -> (match (((uu____1057), (uu____1058))) with
| ((x, y), (x', y')) -> begin
(match (((Prims.op_disEquality x x') || (Prims.op_disEquality y y'))) with
| true -> begin
(

let uu____1087 = (FStar_Parser_Dep.print_digest ((((x), (y)))::[]))
in (

let uu____1096 = (FStar_Parser_Dep.print_digest ((((x'), (y')))::[]))
in (FStar_Util.print2 "Differ at: Expected %s\n Got %s\n" uu____1087 uu____1096)))
end
| uu____1105 -> begin
()
end)
end)) digest digest')
end
| uu____1106 -> begin
()
end);
)
end
| uu____1107 -> begin
()
end));
FStar_Util.Inl ("Stale");
)
end)
end
| uu____1116 -> begin
FStar_Util.Inl ("Stale")
end))
end)
end)))
in (fun env fn -> (

let cache_file = (FStar_Parser_Dep.cache_file_name fn)
in (

let fail1 = (fun tag -> ((invalidate_cache ());
(

let uu____1154 = (

let uu____1155 = (FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0"))
in (

let uu____1156 = (FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0"))
in (FStar_Range.mk_range fn uu____1155 uu____1156)))
in (

let uu____1157 = (

let uu____1162 = (FStar_Util.format3 "%s cache file %s; will recheck %s and all subsequent files" tag cache_file fn)
in ((FStar_Errors.Warning_CachedFile), (uu____1162)))
in (FStar_Errors.log_issue uu____1154 uu____1157)));
FStar_Pervasives_Native.None;
))
in (

let uu____1171 = (FStar_ST.op_Bang some_cache_invalid)
in (match (uu____1171) with
| FStar_Pervasives_Native.Some (uu____1233) -> begin
FStar_Pervasives_Native.None
end
| uu____1242 -> begin
(match ((FStar_Util.file_exists cache_file)) with
| true -> begin
(

let uu____1255 = (load1 env fn cache_file)
in (match (uu____1255) with
| FStar_Util.Inl (msg) -> begin
(fail1 msg)
end
| FStar_Util.Inr (res) -> begin
FStar_Pervasives_Native.Some (res)
end))
end
| uu____1312 -> begin
(

let uu____1313 = (

let uu____1316 = (FStar_Util.basename cache_file)
in (FStar_Options.find_file uu____1316))
in (match (uu____1313) with
| FStar_Pervasives_Native.None -> begin
(fail1 "Absent")
end
| FStar_Pervasives_Native.Some (alt_cache_file) -> begin
(

let uu____1328 = (load1 env fn alt_cache_file)
in (match (uu____1328) with
| FStar_Util.Inl (msg) -> begin
(fail1 msg)
end
| FStar_Util.Inr (res) -> begin
((

let uu____1378 = (FStar_Options.should_verify_file fn)
in (match (uu____1378) with
| true -> begin
(FStar_Util.copy_file alt_cache_file cache_file)
end
| uu____1379 -> begin
()
end));
FStar_Pervasives_Native.Some (res);
)
end))
end))
end)
end))))))))


let store_module_to_cache : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_Syntax_DsEnv.module_inclusion_info  ->  unit = (fun env fn m modul_iface_opt mii -> (

let cache_file = (FStar_Parser_Dep.cache_file_name fn)
in (

let digest = (FStar_Parser_Dep.hash_dependences env.FStar_TypeChecker_Env.dep_graph fn)
in (match (digest) with
| FStar_Pervasives_Native.Some (hashes) -> begin
(FStar_Util.save_value_to_file cache_file ((cache_version_number), (hashes), (m), (modul_iface_opt), (mii)))
end
| uu____1466 -> begin
(

let uu____1475 = (

let uu____1476 = (FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0"))
in (

let uu____1477 = (FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0"))
in (FStar_Range.mk_range fn uu____1476 uu____1477)))
in (

let uu____1478 = (

let uu____1483 = (FStar_Util.format1 "%s was not written, since some of its dependences were not also checked" cache_file)
in ((FStar_Errors.Warning_FileNotWritten), (uu____1483)))
in (FStar_Errors.log_issue uu____1475 uu____1478)))
end))))


type delta_env =
(FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env) FStar_Pervasives_Native.option


let apply_delta_env : FStar_TypeChecker_Env.env  ->  delta_env  ->  FStar_TypeChecker_Env.env = (fun env f -> (match (f) with
| FStar_Pervasives_Native.None -> begin
env
end
| FStar_Pervasives_Native.Some (f1) -> begin
(f1 env)
end))


let extend_delta_env : delta_env  ->  (FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env)  ->  (FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env) FStar_Pervasives_Native.option = (fun f g -> (match (f) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (g)
end
| FStar_Pervasives_Native.Some (f1) -> begin
FStar_Pervasives_Native.Some ((fun e -> (

let uu____1560 = (f1 e)
in (g uu____1560))))
end))


let tc_one_file : FStar_TypeChecker_Env.env  ->  delta_env  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  ((FStar_Syntax_Syntax.modul * Prims.int) * FStar_TypeChecker_Env.env * delta_env) = (fun env delta1 pre_fn fn -> ((FStar_Syntax_Syntax.reset_gensym ());
(

let tc_source_file = (fun uu____1627 -> (

let env1 = (apply_delta_env env delta1)
in (

let uu____1631 = (parse env1 pre_fn fn)
in (match (uu____1631) with
| (fmod, env2) -> begin
(

let check_mod = (fun uu____1669 -> (

let uu____1670 = (FStar_Util.record_time (fun uu____1692 -> (FStar_TypeChecker_Tc.check_module env2 fmod)))
in (match (uu____1670) with
| ((tcmod, tcmod_iface_opt, env3), time) -> begin
((((tcmod), (time))), (tcmod_iface_opt), (env3))
end)))
in (

let uu____1727 = (

let uu____1740 = ((FStar_Options.should_verify fmod.FStar_Syntax_Syntax.name.FStar_Ident.str) && ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ())))
in (match (uu____1740) with
| true -> begin
(

let uu____1753 = (FStar_Parser_ParseIt.find_file fn)
in (FStar_SMTEncoding_Solver.with_hints_db uu____1753 check_mod))
end
| uu____1766 -> begin
(check_mod ())
end))
in (match (uu____1727) with
| (tcmod, tcmod_iface_opt, env3) -> begin
(

let mii = (FStar_Syntax_DsEnv.inclusion_info env3.FStar_TypeChecker_Env.dsenv (FStar_Pervasives_Native.fst tcmod).FStar_Syntax_Syntax.name)
in ((tcmod), (tcmod_iface_opt), (mii), (env3)))
end)))
end))))
in (

let uu____1803 = (FStar_Options.cache_checked_modules ())
in (match (uu____1803) with
| true -> begin
(

let uu____1814 = (load_module_from_cache env fn)
in (match (uu____1814) with
| FStar_Pervasives_Native.None -> begin
(

let uu____1843 = (tc_source_file ())
in (match (uu____1843) with
| (tcmod, tcmod_iface_opt, mii, env1) -> begin
((

let uu____1885 = ((

let uu____1888 = (FStar_Errors.get_err_count ())
in (Prims.op_Equality uu____1888 (Prims.parse_int "0"))) && ((FStar_Options.lax ()) || (FStar_Options.should_verify (FStar_Pervasives_Native.fst tcmod).FStar_Syntax_Syntax.name.FStar_Ident.str)))
in (match (uu____1885) with
| true -> begin
(store_module_to_cache env1 fn (FStar_Pervasives_Native.fst tcmod) tcmod_iface_opt mii)
end
| uu____1889 -> begin
()
end));
((tcmod), (env1), (FStar_Pervasives_Native.None));
)
end))
end
| FStar_Pervasives_Native.Some (tcmod, tcmod_iface_opt, mii) -> begin
(

let tcmod1 = (match (tcmod.FStar_Syntax_Syntax.is_interface) with
| true -> begin
tcmod
end
| uu____1913 -> begin
(

let use_interface_from_the_cache = ((FStar_Options.use_extracted_interfaces ()) && (

let uu____1916 = ((FStar_Options.expose_interfaces ()) && (FStar_Options.should_verify tcmod.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (not (uu____1916))))
in (match (use_interface_from_the_cache) with
| true -> begin
(match ((Prims.op_Equality tcmod_iface_opt FStar_Pervasives_Native.None)) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_ModuleNotFound), ((Prims.strcat "use_extracted_interfaces option is set but could not find it in the cache for: " tcmod.FStar_Syntax_Syntax.name.FStar_Ident.str))) FStar_Range.dummyRange)
end
| uu____1919 -> begin
(FStar_All.pipe_right tcmod_iface_opt FStar_Util.must)
end)
end
| uu____1922 -> begin
tcmod
end))
end)
in (

let delta_env = (fun env1 -> (

let uu____1929 = (

let uu____1934 = (FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod1 mii (FStar_TypeChecker_Normalize.erase_universes env1))
in (FStar_All.pipe_left (with_tcenv env1) uu____1934))
in (match (uu____1929) with
| (uu____1950, env2) -> begin
(FStar_TypeChecker_Tc.load_checked_module env2 tcmod1)
end)))
in ((((tcmod1), ((Prims.parse_int "0")))), (env), ((extend_delta_env delta1 delta_env)))))
end))
end
| uu____1959 -> begin
(

let env1 = (apply_delta_env env delta1)
in (

let uu____1963 = (tc_source_file ())
in (match (uu____1963) with
| (tcmod, tcmod_iface_opt, uu____1990, env2) -> begin
(

let tcmod1 = (match ((FStar_Util.is_some tcmod_iface_opt)) with
| true -> begin
(

let uu____2013 = (FStar_All.pipe_right tcmod_iface_opt FStar_Util.must)
in ((uu____2013), ((FStar_Pervasives_Native.snd tcmod))))
end
| uu____2016 -> begin
tcmod
end)
in ((tcmod1), (env2), (FStar_Pervasives_Native.None)))
end)))
end)));
))


let needs_interleaving : Prims.string  ->  Prims.string  ->  Prims.bool = (fun intf impl -> (

let m1 = (FStar_Parser_Dep.lowercase_module_name intf)
in (

let m2 = (FStar_Parser_Dep.lowercase_module_name impl)
in (((Prims.op_Equality m1 m2) && (

let uu____2037 = (FStar_Util.get_file_extension intf)
in (FStar_List.mem uu____2037 (("fsti")::("fsi")::[])))) && (

let uu____2039 = (FStar_Util.get_file_extension impl)
in (FStar_List.mem uu____2039 (("fst")::("fs")::[])))))))


let pop_context : FStar_TypeChecker_Env.env  ->  Prims.string  ->  unit = (fun env msg -> (

let uu____2050 = (FStar_TypeChecker_Tc.pop_context env msg)
in (FStar_All.pipe_right uu____2050 (fun a238 -> ()))))


let push_context : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Env.env = (fun env msg -> (FStar_TypeChecker_Tc.push_context env msg))


let tc_one_file_from_remaining : Prims.string Prims.list  ->  FStar_TypeChecker_Env.env  ->  delta_env  ->  (Prims.string Prims.list * (FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_TypeChecker_Env.env * delta_env) = (fun remaining env delta_env -> (

let uu____2098 = (match (remaining) with
| (intf)::(impl)::remaining1 when (needs_interleaving intf impl) -> begin
(

let uu____2140 = (tc_one_file env delta_env (FStar_Pervasives_Native.Some (intf)) impl)
in (match (uu____2140) with
| (m, env1, delta_env1) -> begin
((remaining1), ((((m)::[]), (env1), (delta_env1))))
end))
end
| (intf_or_impl)::remaining1 -> begin
(

let uu____2216 = (tc_one_file env delta_env FStar_Pervasives_Native.None intf_or_impl)
in (match (uu____2216) with
| (m, env1, delta_env1) -> begin
((remaining1), ((((m)::[]), (env1), (delta_env1))))
end))
end
| [] -> begin
(([]), ((([]), (env), (delta_env))))
end)
in (match (uu____2098) with
| (remaining1, (nmods, env1, delta_env1)) -> begin
((remaining1), (nmods), (env1), (delta_env1))
end)))


let rec tc_fold_interleave : ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_TypeChecker_Env.env * delta_env)  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_TypeChecker_Env.env * delta_env) = (fun acc remaining -> (match (remaining) with
| [] -> begin
acc
end
| uu____2434 -> begin
(

let uu____2437 = acc
in (match (uu____2437) with
| (mods, env, delta_env) -> begin
(

let uu____2477 = (tc_one_file_from_remaining remaining env delta_env)
in (match (uu____2477) with
| (remaining1, nmods, env1, delta_env1) -> begin
(tc_fold_interleave (((FStar_List.append mods nmods)), (env1), (delta_env1)) remaining1)
end))
end))
end))


let batch_mode_tc : Prims.string Prims.list  ->  FStar_Parser_Dep.deps  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_TypeChecker_Env.env * (FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env) FStar_Pervasives_Native.option) = (fun filenames dep_graph1 -> ((

let uu____2572 = (FStar_Options.debug_any ())
in (match (uu____2572) with
| true -> begin
((FStar_Util.print_endline "Auto-deps kicked in; here\'s some info.");
(FStar_Util.print1 "Here\'s the list of filenames we will process: %s\n" (FStar_String.concat " " filenames));
(

let uu____2575 = (

let uu____2576 = (FStar_All.pipe_right filenames (FStar_List.filter FStar_Options.should_verify_file))
in (FStar_String.concat " " uu____2576))
in (FStar_Util.print1 "Here\'s the list of modules we will verify: %s\n" uu____2575));
)
end
| uu____2583 -> begin
()
end));
(

let env = (init_env dep_graph1)
in (

let uu____2585 = (tc_fold_interleave (([]), (env), (FStar_Pervasives_Native.None)) filenames)
in (match (uu____2585) with
| (all_mods, env1, delta1) -> begin
(

let solver_refresh = (fun env2 -> ((

let uu____2650 = ((FStar_Options.interactive ()) && (

let uu____2652 = (FStar_Errors.get_err_count ())
in (Prims.op_Equality uu____2652 (Prims.parse_int "0"))))
in (match (uu____2650) with
| true -> begin
(env2.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end
| uu____2653 -> begin
(env2.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end));
env2;
))
in ((all_mods), (env1), ((extend_delta_env delta1 solver_refresh))))
end)));
))




