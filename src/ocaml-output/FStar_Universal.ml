
open Prims
open FStar_Pervasives

let cache_version_number : Prims.int = (Prims.parse_int "5")


let module_or_interface_name : FStar_Syntax_Syntax.modul  ->  (Prims.bool * FStar_Ident.lident) = (fun m -> ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name)))


let with_tcenv : 'a . FStar_TypeChecker_Env.env  ->  'a FStar_Syntax_DsEnv.withenv  ->  ('a * FStar_TypeChecker_Env.env) = (fun env f -> (

let uu____41 = (f env.FStar_TypeChecker_Env.dsenv)
in (match (uu____41) with
| (a, dsenv1) -> begin
((a), ((

let uu___423_55 = env
in {FStar_TypeChecker_Env.solver = uu___423_55.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___423_55.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___423_55.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___423_55.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___423_55.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___423_55.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___423_55.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___423_55.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___423_55.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___423_55.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___423_55.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___423_55.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___423_55.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___423_55.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___423_55.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___423_55.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___423_55.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___423_55.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___423_55.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___423_55.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___423_55.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___423_55.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___423_55.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___423_55.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___423_55.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___423_55.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___423_55.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___423_55.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___423_55.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___423_55.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___423_55.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___423_55.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___423_55.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___423_55.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___423_55.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___423_55.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___423_55.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___423_55.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___423_55.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___423_55.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___423_55.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = dsenv1; FStar_TypeChecker_Env.nbe = uu___423_55.FStar_TypeChecker_Env.nbe})))
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

let uu___424_250 = FStar_SMTEncoding_Solver.solver
in {FStar_TypeChecker_Env.init = uu___424_250.FStar_TypeChecker_Env.init; FStar_TypeChecker_Env.push = uu___424_250.FStar_TypeChecker_Env.push; FStar_TypeChecker_Env.pop = uu___424_250.FStar_TypeChecker_Env.pop; FStar_TypeChecker_Env.snapshot = uu___424_250.FStar_TypeChecker_Env.snapshot; FStar_TypeChecker_Env.rollback = uu___424_250.FStar_TypeChecker_Env.rollback; FStar_TypeChecker_Env.encode_modul = uu___424_250.FStar_TypeChecker_Env.encode_modul; FStar_TypeChecker_Env.encode_sig = uu___424_250.FStar_TypeChecker_Env.encode_sig; FStar_TypeChecker_Env.preprocess = FStar_Tactics_Interpreter.preprocess; FStar_TypeChecker_Env.solve = uu___424_250.FStar_TypeChecker_Env.solve; FStar_TypeChecker_Env.finish = uu___424_250.FStar_TypeChecker_Env.finish; FStar_TypeChecker_Env.refresh = uu___424_250.FStar_TypeChecker_Env.refresh})
end))
in (

let env = (

let uu____252 = (

let uu____267 = (FStar_Tactics_Interpreter.primitive_steps ())
in (FStar_TypeChecker_NBE.normalize uu____267))
in (FStar_TypeChecker_Env.initial_env deps FStar_TypeChecker_TcTerm.tc_term FStar_TypeChecker_TcTerm.type_of_tot_term FStar_TypeChecker_TcTerm.universe_of FStar_TypeChecker_TcTerm.check_type_of_well_typed_term solver1 FStar_Parser_Const.prims_lid uu____252))
in (

let env1 = (

let uu___425_271 = env
in {FStar_TypeChecker_Env.solver = uu___425_271.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___425_271.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___425_271.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___425_271.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___425_271.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___425_271.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___425_271.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___425_271.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___425_271.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___425_271.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___425_271.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___425_271.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___425_271.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___425_271.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___425_271.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___425_271.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___425_271.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___425_271.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___425_271.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___425_271.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___425_271.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___425_271.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___425_271.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___425_271.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___425_271.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___425_271.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___425_271.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___425_271.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___425_271.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___425_271.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___425_271.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___425_271.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___425_271.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___425_271.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___425_271.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = FStar_Tactics_Interpreter.synthesize; FStar_TypeChecker_Env.splice = uu___425_271.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___425_271.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___425_271.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___425_271.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___425_271.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___425_271.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___425_271.FStar_TypeChecker_Env.nbe})
in (

let env2 = (

let uu___426_273 = env1
in {FStar_TypeChecker_Env.solver = uu___426_273.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___426_273.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___426_273.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___426_273.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___426_273.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___426_273.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___426_273.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___426_273.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___426_273.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___426_273.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___426_273.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___426_273.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___426_273.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___426_273.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___426_273.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___426_273.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___426_273.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___426_273.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___426_273.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___426_273.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___426_273.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___426_273.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___426_273.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___426_273.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___426_273.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___426_273.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___426_273.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___426_273.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___426_273.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___426_273.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___426_273.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___426_273.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___426_273.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___426_273.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___426_273.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___426_273.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = FStar_Tactics_Interpreter.splice; FStar_TypeChecker_Env.postprocess = uu___426_273.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___426_273.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___426_273.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___426_273.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___426_273.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___426_273.FStar_TypeChecker_Env.nbe})
in (

let env3 = (

let uu___427_275 = env2
in {FStar_TypeChecker_Env.solver = uu___427_275.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___427_275.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___427_275.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___427_275.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___427_275.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___427_275.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___427_275.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___427_275.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___427_275.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___427_275.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___427_275.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___427_275.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___427_275.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___427_275.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___427_275.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___427_275.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___427_275.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___427_275.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___427_275.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___427_275.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___427_275.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___427_275.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___427_275.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___427_275.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___427_275.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___427_275.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___427_275.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___427_275.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___427_275.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___427_275.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___427_275.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___427_275.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___427_275.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___427_275.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___427_275.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___427_275.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___427_275.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = FStar_Tactics_Interpreter.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___427_275.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___427_275.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___427_275.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___427_275.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___427_275.FStar_TypeChecker_Env.nbe})
in (

let env4 = (

let uu___428_277 = env3
in {FStar_TypeChecker_Env.solver = uu___428_277.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___428_277.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___428_277.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___428_277.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___428_277.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___428_277.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___428_277.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___428_277.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___428_277.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___428_277.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___428_277.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___428_277.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___428_277.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___428_277.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___428_277.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___428_277.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___428_277.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___428_277.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___428_277.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___428_277.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___428_277.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___428_277.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___428_277.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___428_277.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___428_277.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___428_277.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___428_277.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___428_277.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___428_277.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___428_277.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___428_277.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___428_277.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___428_277.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___428_277.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___428_277.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___428_277.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___428_277.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___428_277.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = FStar_Tactics_Native.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___428_277.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___428_277.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___428_277.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___428_277.FStar_TypeChecker_Env.nbe})
in ((env4.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env4);
env4;
))))))))


let tc_one_fragment : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Parser_ParseIt.input_frag  ->  (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_TypeChecker_Env.env) = (fun curmod env frag -> (

let acceptable_mod_name = (fun modul -> (

let uu____310 = (

let uu____311 = (

let uu____312 = (FStar_Options.file_list ())
in (FStar_List.hd uu____312))
in (FStar_Parser_Dep.lowercase_module_name uu____311))
in (

let uu____315 = (

let uu____316 = (FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name)
in (FStar_String.lowercase uu____316))
in (Prims.op_Equality uu____310 uu____315))))
in (

let range_of_first_mod_decl = (fun modul -> (match (modul) with
| FStar_Parser_AST.Module (uu____323, ({FStar_Parser_AST.d = uu____324; FStar_Parser_AST.drange = d; FStar_Parser_AST.doc = uu____326; FStar_Parser_AST.quals = uu____327; FStar_Parser_AST.attrs = uu____328})::uu____329) -> begin
d
end
| FStar_Parser_AST.Interface (uu____336, ({FStar_Parser_AST.d = uu____337; FStar_Parser_AST.drange = d; FStar_Parser_AST.doc = uu____339; FStar_Parser_AST.quals = uu____340; FStar_Parser_AST.attrs = uu____341})::uu____342, uu____343) -> begin
d
end
| uu____350 -> begin
FStar_Range.dummyRange
end))
in (

let uu____351 = (FStar_Parser_Driver.parse_fragment frag)
in (match (uu____351) with
| FStar_Parser_Driver.Empty -> begin
((curmod), (env))
end
| FStar_Parser_Driver.Decls ([]) -> begin
((curmod), (env))
end
| FStar_Parser_Driver.Modul (ast_modul) -> begin
(

let uu____363 = (

let uu____368 = (FStar_ToSyntax_Interleave.interleave_module ast_modul false)
in (FStar_All.pipe_left (with_tcenv env) uu____368))
in (match (uu____363) with
| (ast_modul1, env1) -> begin
(

let uu____392 = (

let uu____397 = (FStar_ToSyntax_ToSyntax.partial_ast_modul_to_modul curmod ast_modul1)
in (FStar_All.pipe_left (with_tcenv env1) uu____397))
in (match (uu____392) with
| (modul, env2) -> begin
((

let uu____422 = (

let uu____423 = (acceptable_mod_name modul)
in (not (uu____423)))
in (match (uu____422) with
| true -> begin
(

let msg = (

let uu____425 = (

let uu____426 = (

let uu____427 = (FStar_Options.file_list ())
in (FStar_List.hd uu____427))
in (FStar_Parser_Dep.module_name_of_file uu____426))
in (FStar_Util.format1 "Interactive mode only supports a single module at the top-level. Expected module %s" uu____425))
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_NonSingletonTopLevelModule), (msg)) (range_of_first_mod_decl ast_modul1)))
end
| uu____430 -> begin
()
end));
(

let uu____431 = (

let uu____440 = (FStar_Syntax_DsEnv.syntax_only env2.FStar_TypeChecker_Env.dsenv)
in (match (uu____440) with
| true -> begin
((modul), ([]), (env2))
end
| uu____451 -> begin
(FStar_TypeChecker_Tc.tc_partial_modul env2 modul)
end))
in (match (uu____431) with
| (modul1, uu____459, env3) -> begin
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

let uu____476 = (FStar_List.hd ast_decls)
in (match (uu____476) with
| {FStar_Parser_AST.d = uu____483; FStar_Parser_AST.drange = rng; FStar_Parser_AST.doc = uu____485; FStar_Parser_AST.quals = uu____486; FStar_Parser_AST.attrs = uu____487} -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_ModuleFirstStatement), ("First statement must be a module declaration")) rng)
end))
end
| FStar_Pervasives_Native.Some (modul) -> begin
(

let uu____497 = (FStar_Util.fold_map (fun env1 a_decl -> (

let uu____515 = (

let uu____522 = (FStar_ToSyntax_Interleave.prefix_with_interface_decls a_decl)
in (FStar_All.pipe_left (with_tcenv env1) uu____522))
in (match (uu____515) with
| (decls, env2) -> begin
((env2), (decls))
end))) env ast_decls)
in (match (uu____497) with
| (env1, ast_decls_l) -> begin
(

let uu____576 = (

let uu____583 = (FStar_ToSyntax_ToSyntax.decls_to_sigelts (FStar_List.flatten ast_decls_l))
in (FStar_All.pipe_left (with_tcenv env1) uu____583))
in (match (uu____576) with
| (sigelts, env2) -> begin
(

let uu____619 = (

let uu____628 = (FStar_Syntax_DsEnv.syntax_only env2.FStar_TypeChecker_Env.dsenv)
in (match (uu____628) with
| true -> begin
((modul), ([]), (env2))
end
| uu____639 -> begin
(FStar_TypeChecker_Tc.tc_more_partial_modul env2 modul sigelts)
end))
in (match (uu____619) with
| (modul1, uu____647, env3) -> begin
((FStar_Pervasives_Native.Some (modul1)), (env3))
end))
end))
end))
end)
end)))))


let load_interface_decls : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Env.env = (fun env interface_file_name -> (

let r = (FStar_Parser_ParseIt.parse (FStar_Parser_ParseIt.Filename (interface_file_name)))
in (match (r) with
| FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inl (FStar_Parser_AST.Interface (l, decls, uu____668)), uu____669) -> begin
(

let uu____688 = (

let uu____693 = (FStar_ToSyntax_Interleave.initialize_interface l decls)
in (FStar_All.pipe_left (with_tcenv env) uu____693))
in (FStar_Pervasives_Native.snd uu____688))
end
| FStar_Parser_ParseIt.ASTFragment (uu____709) -> begin
(

let uu____720 = (

let uu____725 = (FStar_Util.format1 "Unexpected result from parsing %s; expected a single interface" interface_file_name)
in ((FStar_Errors.Fatal_ParseErrors), (uu____725)))
in (FStar_Errors.raise_err uu____720))
end
| FStar_Parser_ParseIt.ParseError (err, msg, rng) -> begin
(FStar_Exn.raise (FStar_Errors.Error (((err), (msg), (rng)))))
end
| FStar_Parser_ParseIt.Term (uu____729) -> begin
(failwith "Impossible: parsing a Toplevel always results in an ASTFragment")
end)))


let load_module_from_cache : FStar_TypeChecker_Env.env  ->  Prims.string  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_Syntax_DsEnv.module_inclusion_info) FStar_Pervasives_Native.option = (

let some_cache_invalid = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let invalidate_cache = (fun fn -> (FStar_ST.op_Colon_Equals some_cache_invalid (FStar_Pervasives_Native.Some (()))))
in (

let load1 = (fun env source_file cache_file -> (

let uu____834 = (FStar_Util.load_value_from_file cache_file)
in (match (uu____834) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inl ("Corrupt")
end
| FStar_Pervasives_Native.Some (vnum, digest, tcmod, tcmod_iface_opt, mii) -> begin
(match ((Prims.op_disEquality vnum cache_version_number)) with
| true -> begin
FStar_Util.Inl ("Stale, because inconsistent cache version")
end
| uu____970 -> begin
(

let uu____971 = (

let uu____980 = (FStar_TypeChecker_Env.dep_graph env)
in (FStar_Parser_Dep.hash_dependences uu____980 source_file))
in (match (uu____971) with
| FStar_Pervasives_Native.Some (digest') -> begin
(match ((Prims.op_Equality digest digest')) with
| true -> begin
FStar_Util.Inr (((tcmod), (tcmod_iface_opt), (mii)))
end
| uu____1034 -> begin
((

let uu____1036 = (FStar_Options.debug_any ())
in (match (uu____1036) with
| true -> begin
((

let uu____1038 = (FStar_Util.string_of_int (FStar_List.length digest'))
in (

let uu____1043 = (FStar_Parser_Dep.print_digest digest')
in (

let uu____1044 = (FStar_Util.string_of_int (FStar_List.length digest))
in (

let uu____1049 = (FStar_Parser_Dep.print_digest digest)
in (FStar_Util.print4 "Expected (%s) hashes:\n%s\n\nGot (%s) hashes:\n\t%s\n" uu____1038 uu____1043 uu____1044 uu____1049)))));
(match ((Prims.op_Equality (FStar_List.length digest) (FStar_List.length digest'))) with
| true -> begin
(FStar_List.iter2 (fun uu____1074 uu____1075 -> (match (((uu____1074), (uu____1075))) with
| ((x, y), (x', y')) -> begin
(match (((Prims.op_disEquality x x') || (Prims.op_disEquality y y'))) with
| true -> begin
(

let uu____1104 = (FStar_Parser_Dep.print_digest ((((x), (y)))::[]))
in (

let uu____1113 = (FStar_Parser_Dep.print_digest ((((x'), (y')))::[]))
in (FStar_Util.print2 "Differ at: Expected %s\n Got %s\n" uu____1104 uu____1113)))
end
| uu____1122 -> begin
()
end)
end)) digest digest')
end
| uu____1123 -> begin
()
end);
)
end
| uu____1124 -> begin
()
end));
FStar_Util.Inl ("Stale");
)
end)
end
| uu____1133 -> begin
FStar_Util.Inl ("Unable to compute digest of")
end))
end)
end)))
in (fun env fn -> (

let cache_file = (FStar_Parser_Dep.cache_file_name fn)
in (

let fail1 = (fun tag should_warn cache_file1 -> ((invalidate_cache ());
(match (should_warn) with
| true -> begin
(

let uu____1181 = (

let uu____1182 = (FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0"))
in (

let uu____1183 = (FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0"))
in (FStar_Range.mk_range fn uu____1182 uu____1183)))
in (

let uu____1184 = (

let uu____1189 = (FStar_Util.format3 "%s cache file %s; will recheck %s and all subsequent files" tag cache_file1 fn)
in ((FStar_Errors.Warning_CachedFile), (uu____1189)))
in (FStar_Errors.log_issue uu____1181 uu____1184)))
end
| uu____1190 -> begin
()
end);
FStar_Pervasives_Native.None;
))
in (

let uu____1199 = (FStar_ST.op_Bang some_cache_invalid)
in (match (uu____1199) with
| FStar_Pervasives_Native.Some (uu____1257) -> begin
FStar_Pervasives_Native.None
end
| uu____1266 -> begin
(match ((FStar_Util.file_exists cache_file)) with
| true -> begin
(

let uu____1279 = (load1 env fn cache_file)
in (match (uu____1279) with
| FStar_Util.Inl (msg) -> begin
(fail1 msg true cache_file)
end
| FStar_Util.Inr (res) -> begin
FStar_Pervasives_Native.Some (res)
end))
end
| uu____1336 -> begin
(

let uu____1337 = (

let uu____1340 = (FStar_Util.basename cache_file)
in (FStar_Options.find_file uu____1340))
in (match (uu____1337) with
| FStar_Pervasives_Native.None -> begin
(fail1 "Absent" false cache_file)
end
| FStar_Pervasives_Native.Some (alt_cache_file) -> begin
(

let uu____1352 = (load1 env fn alt_cache_file)
in (match (uu____1352) with
| FStar_Util.Inl (msg) -> begin
(fail1 msg true alt_cache_file)
end
| FStar_Util.Inr (res) -> begin
((

let uu____1402 = (FStar_Options.should_verify_file fn)
in (match (uu____1402) with
| true -> begin
(FStar_Util.copy_file alt_cache_file cache_file)
end
| uu____1403 -> begin
()
end));
FStar_Pervasives_Native.Some (res);
)
end))
end))
end)
end))))))))


let store_module_to_cache : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_Syntax_DsEnv.module_inclusion_info  ->  unit = (fun env fn m modul_iface_opt mii -> (

let uu____1441 = ((FStar_Options.cache_checked_modules ()) && (

let uu____1443 = (FStar_Options.cache_off ())
in (not (uu____1443))))
in (match (uu____1441) with
| true -> begin
(

let cache_file = (FStar_Parser_Dep.cache_file_name fn)
in (

let digest = (

let uu____1454 = (FStar_TypeChecker_Env.dep_graph env)
in (FStar_Parser_Dep.hash_dependences uu____1454 fn))
in (match (digest) with
| FStar_Pervasives_Native.Some (hashes) -> begin
(FStar_Util.save_value_to_file cache_file ((cache_version_number), (hashes), (m), (modul_iface_opt), (mii)))
end
| uu____1494 -> begin
(

let uu____1503 = (

let uu____1504 = (FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0"))
in (

let uu____1505 = (FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0"))
in (FStar_Range.mk_range fn uu____1504 uu____1505)))
in (

let uu____1506 = (

let uu____1511 = (FStar_Util.format1 "%s was not written, since some of its dependences were not also checked" cache_file)
in ((FStar_Errors.Warning_FileNotWritten), (uu____1511)))
in (FStar_Errors.log_issue uu____1503 uu____1506)))
end)))
end
| uu____1512 -> begin
()
end)))


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

let uu____1589 = (f1 e)
in (g uu____1589))))
end))


let tc_one_file : FStar_TypeChecker_Env.env  ->  delta_env  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  ((FStar_Syntax_Syntax.modul * Prims.int) * FStar_TypeChecker_Env.env * delta_env) = (fun env delta1 pre_fn fn -> ((FStar_Syntax_Syntax.reset_gensym ());
(

let tc_source_file = (fun uu____1656 -> (

let env1 = (apply_delta_env env delta1)
in (

let uu____1660 = (parse env1 pre_fn fn)
in (match (uu____1660) with
| (fmod, env2) -> begin
(

let check_mod = (fun uu____1698 -> (

let uu____1699 = (FStar_Util.record_time (fun uu____1721 -> (FStar_TypeChecker_Tc.check_module env2 fmod (FStar_Util.is_some pre_fn))))
in (match (uu____1699) with
| ((tcmod, tcmod_iface_opt, env3), time) -> begin
((((tcmod), (time))), (tcmod_iface_opt), (env3))
end)))
in (

let uu____1756 = (

let uu____1769 = ((FStar_Options.should_verify fmod.FStar_Syntax_Syntax.name.FStar_Ident.str) && ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ())))
in (match (uu____1769) with
| true -> begin
(

let uu____1782 = (FStar_Parser_ParseIt.find_file fn)
in (FStar_SMTEncoding_Solver.with_hints_db uu____1782 check_mod))
end
| uu____1795 -> begin
(check_mod ())
end))
in (match (uu____1756) with
| (tcmod, tcmod_iface_opt, env3) -> begin
(

let mii = (FStar_Syntax_DsEnv.inclusion_info env3.FStar_TypeChecker_Env.dsenv (FStar_Pervasives_Native.fst tcmod).FStar_Syntax_Syntax.name)
in ((tcmod), (tcmod_iface_opt), (mii), (env3)))
end)))
end))))
in (

let uu____1832 = (

let uu____1833 = (FStar_Options.cache_off ())
in (not (uu____1833)))
in (match (uu____1832) with
| true -> begin
(

let uu____1844 = (load_module_from_cache env fn)
in (match (uu____1844) with
| FStar_Pervasives_Native.None -> begin
(

let uu____1873 = (tc_source_file ())
in (match (uu____1873) with
| (tcmod, tcmod_iface_opt, mii, env1) -> begin
((

let uu____1915 = ((

let uu____1918 = (FStar_Errors.get_err_count ())
in (Prims.op_Equality uu____1918 (Prims.parse_int "0"))) && ((FStar_Options.lax ()) || (FStar_Options.should_verify (FStar_Pervasives_Native.fst tcmod).FStar_Syntax_Syntax.name.FStar_Ident.str)))
in (match (uu____1915) with
| true -> begin
(store_module_to_cache env1 fn (FStar_Pervasives_Native.fst tcmod) tcmod_iface_opt mii)
end
| uu____1919 -> begin
()
end));
((tcmod), (env1), (FStar_Pervasives_Native.None));
)
end))
end
| FStar_Pervasives_Native.Some (tcmod, tcmod_iface_opt, mii) -> begin
((

let uu____1943 = (FStar_Options.dump_module tcmod.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____1943) with
| true -> begin
(

let uu____1944 = (FStar_Syntax_Print.modul_to_string tcmod)
in (FStar_Util.print1 "Module after type checking:\n%s\n" uu____1944))
end
| uu____1945 -> begin
()
end));
(

let tcmod1 = (match (tcmod.FStar_Syntax_Syntax.is_interface) with
| true -> begin
tcmod
end
| uu____1947 -> begin
(

let use_interface_from_the_cache = (((FStar_Options.use_extracted_interfaces ()) && (Prims.op_Equality pre_fn FStar_Pervasives_Native.None)) && (

let uu____1952 = ((FStar_Options.expose_interfaces ()) && (FStar_Options.should_verify tcmod.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (not (uu____1952))))
in (match (use_interface_from_the_cache) with
| true -> begin
(match ((FStar_Option.isNone tcmod_iface_opt)) with
| true -> begin
((

let uu____1954 = (

let uu____1955 = (FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0"))
in (

let uu____1956 = (FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0"))
in (FStar_Range.mk_range tcmod.FStar_Syntax_Syntax.name.FStar_Ident.str uu____1955 uu____1956)))
in (FStar_Errors.log_issue uu____1954 ((FStar_Errors.Warning_MissingInterfaceOrImplementation), ((Prims.strcat "use_extracted_interfaces option is set but could not find an interface in the cache for: " tcmod.FStar_Syntax_Syntax.name.FStar_Ident.str)))));
tcmod;
)
end
| uu____1957 -> begin
(FStar_All.pipe_right tcmod_iface_opt FStar_Util.must)
end)
end
| uu____1960 -> begin
tcmod
end))
end)
in (

let delta_env = (fun env1 -> (

let uu____1967 = (

let uu____1972 = (FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod1 mii (FStar_TypeChecker_Normalize.erase_universes env1))
in (FStar_All.pipe_left (with_tcenv env1) uu____1972))
in (match (uu____1967) with
| (uu____1988, env2) -> begin
(FStar_TypeChecker_Tc.load_checked_module env2 tcmod1)
end)))
in ((((tcmod1), ((Prims.parse_int "0")))), (env), ((extend_delta_env delta1 delta_env)))));
)
end))
end
| uu____1997 -> begin
(

let uu____1998 = (tc_source_file ())
in (match (uu____1998) with
| (tcmod, tcmod_iface_opt, uu____2025, env1) -> begin
(

let tcmod1 = (match ((FStar_Util.is_some tcmod_iface_opt)) with
| true -> begin
(

let uu____2048 = (FStar_All.pipe_right tcmod_iface_opt FStar_Util.must)
in ((uu____2048), ((FStar_Pervasives_Native.snd tcmod))))
end
| uu____2051 -> begin
tcmod
end)
in ((tcmod1), (env1), (FStar_Pervasives_Native.None)))
end))
end)));
))


let needs_interleaving : Prims.string  ->  Prims.string  ->  Prims.bool = (fun intf impl -> (

let m1 = (FStar_Parser_Dep.lowercase_module_name intf)
in (

let m2 = (FStar_Parser_Dep.lowercase_module_name impl)
in (((Prims.op_Equality m1 m2) && (

let uu____2072 = (FStar_Util.get_file_extension intf)
in (FStar_List.mem uu____2072 (("fsti")::("fsi")::[])))) && (

let uu____2074 = (FStar_Util.get_file_extension impl)
in (FStar_List.mem uu____2074 (("fst")::("fs")::[])))))))


let tc_one_file_from_remaining : Prims.string Prims.list  ->  FStar_TypeChecker_Env.env  ->  delta_env  ->  (Prims.string Prims.list * (FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_TypeChecker_Env.env * delta_env) = (fun remaining env delta_env -> (

let uu____2112 = (match (remaining) with
| (intf)::(impl)::remaining1 when (needs_interleaving intf impl) -> begin
(

let uu____2154 = (tc_one_file env delta_env (FStar_Pervasives_Native.Some (intf)) impl)
in (match (uu____2154) with
| (m, env1, delta_env1) -> begin
((remaining1), ((((m)::[]), (env1), (delta_env1))))
end))
end
| (intf_or_impl)::remaining1 -> begin
(

let uu____2230 = (tc_one_file env delta_env FStar_Pervasives_Native.None intf_or_impl)
in (match (uu____2230) with
| (m, env1, delta_env1) -> begin
((remaining1), ((((m)::[]), (env1), (delta_env1))))
end))
end
| [] -> begin
(([]), ((([]), (env), (delta_env))))
end)
in (match (uu____2112) with
| (remaining1, (nmods, env1, delta_env1)) -> begin
((remaining1), (nmods), (env1), (delta_env1))
end)))


let rec tc_fold_interleave : ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_TypeChecker_Env.env * delta_env)  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_TypeChecker_Env.env * delta_env) = (fun acc remaining -> (match (remaining) with
| [] -> begin
acc
end
| uu____2448 -> begin
(

let uu____2451 = acc
in (match (uu____2451) with
| (mods, env, delta_env) -> begin
(

let uu____2491 = (tc_one_file_from_remaining remaining env delta_env)
in (match (uu____2491) with
| (remaining1, nmods, env1, delta_env1) -> begin
(tc_fold_interleave (((FStar_List.append mods nmods)), (env1), (delta_env1)) remaining1)
end))
end))
end))


let batch_mode_tc : Prims.string Prims.list  ->  FStar_Parser_Dep.deps  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_TypeChecker_Env.env * (FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env) FStar_Pervasives_Native.option) = (fun filenames dep_graph1 -> ((

let uu____2586 = (FStar_Options.debug_any ())
in (match (uu____2586) with
| true -> begin
((FStar_Util.print_endline "Auto-deps kicked in; here\'s some info.");
(FStar_Util.print1 "Here\'s the list of filenames we will process: %s\n" (FStar_String.concat " " filenames));
(

let uu____2589 = (

let uu____2590 = (FStar_All.pipe_right filenames (FStar_List.filter FStar_Options.should_verify_file))
in (FStar_String.concat " " uu____2590))
in (FStar_Util.print1 "Here\'s the list of modules we will verify: %s\n" uu____2589));
)
end
| uu____2597 -> begin
()
end));
(

let env = (init_env dep_graph1)
in (

let uu____2599 = (tc_fold_interleave (([]), (env), (FStar_Pervasives_Native.None)) filenames)
in (match (uu____2599) with
| (all_mods, env1, delta1) -> begin
(

let solver_refresh = (fun env2 -> ((

let uu____2664 = ((FStar_Options.interactive ()) && (

let uu____2666 = (FStar_Errors.get_err_count ())
in (Prims.op_Equality uu____2666 (Prims.parse_int "0"))))
in (match (uu____2664) with
| true -> begin
(env2.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end
| uu____2667 -> begin
(env2.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end));
env2;
))
in ((all_mods), (env1), ((extend_delta_env delta1 solver_refresh))))
end)));
))




