
open Prims
open FStar_Pervasives

let module_or_interface_name : FStar_Syntax_Syntax.modul  ->  (Prims.bool * FStar_Ident.lident) = (fun m -> ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name)))


type uenv =
FStar_Extraction_ML_UEnv.uenv


let with_dsenv_of_tcenv : 'a . FStar_TypeChecker_Env.env  ->  'a FStar_Syntax_DsEnv.withenv  ->  ('a * FStar_TypeChecker_Env.env) = (fun tcenv f -> (

let uu____39 = (f tcenv.FStar_TypeChecker_Env.dsenv)
in (match (uu____39) with
| (a, dsenv1) -> begin
((a), ((

let uu___8_51 = tcenv
in {FStar_TypeChecker_Env.solver = uu___8_51.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___8_51.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___8_51.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___8_51.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___8_51.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___8_51.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___8_51.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___8_51.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___8_51.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___8_51.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___8_51.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___8_51.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___8_51.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___8_51.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___8_51.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___8_51.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___8_51.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___8_51.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___8_51.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___8_51.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___8_51.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___8_51.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___8_51.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___8_51.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___8_51.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___8_51.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___8_51.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___8_51.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___8_51.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___8_51.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___8_51.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___8_51.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___8_51.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___8_51.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___8_51.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___8_51.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___8_51.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___8_51.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___8_51.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___8_51.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___8_51.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = dsenv1; FStar_TypeChecker_Env.nbe = uu___8_51.FStar_TypeChecker_Env.nbe})))
end)))


let with_tcenv_of_env : 'a . uenv  ->  (FStar_TypeChecker_Env.env  ->  ('a * FStar_TypeChecker_Env.env))  ->  ('a * uenv) = (fun e f -> (

let uu____87 = (f e.FStar_Extraction_ML_UEnv.env_tcenv)
in (match (uu____87) with
| (a, t') -> begin
((a), ((

let uu___16_99 = e
in {FStar_Extraction_ML_UEnv.env_tcenv = t'; FStar_Extraction_ML_UEnv.env_bindings = uu___16_99.FStar_Extraction_ML_UEnv.env_bindings; FStar_Extraction_ML_UEnv.tydefs = uu___16_99.FStar_Extraction_ML_UEnv.tydefs; FStar_Extraction_ML_UEnv.type_names = uu___16_99.FStar_Extraction_ML_UEnv.type_names; FStar_Extraction_ML_UEnv.currentModule = uu___16_99.FStar_Extraction_ML_UEnv.currentModule})))
end)))


let with_dsenv_of_env : 'a . uenv  ->  'a FStar_Syntax_DsEnv.withenv  ->  ('a * uenv) = (fun e f -> (

let uu____128 = (with_dsenv_of_tcenv e.FStar_Extraction_ML_UEnv.env_tcenv f)
in (match (uu____128) with
| (a, tcenv) -> begin
((a), ((

let uu___24_140 = e
in {FStar_Extraction_ML_UEnv.env_tcenv = tcenv; FStar_Extraction_ML_UEnv.env_bindings = uu___24_140.FStar_Extraction_ML_UEnv.env_bindings; FStar_Extraction_ML_UEnv.tydefs = uu___24_140.FStar_Extraction_ML_UEnv.tydefs; FStar_Extraction_ML_UEnv.type_names = uu___24_140.FStar_Extraction_ML_UEnv.type_names; FStar_Extraction_ML_UEnv.currentModule = uu___24_140.FStar_Extraction_ML_UEnv.currentModule})))
end)))


let push_env : uenv  ->  uenv = (fun env -> (

let uu____147 = (with_tcenv_of_env env (fun tcenv -> (

let uu____155 = (FStar_TypeChecker_Env.push env.FStar_Extraction_ML_UEnv.env_tcenv "top-level: push_env")
in ((()), (uu____155)))))
in (FStar_Pervasives_Native.snd uu____147)))


let pop_env : uenv  ->  uenv = (fun env -> (

let uu____163 = (with_tcenv_of_env env (fun tcenv -> (

let uu____171 = (FStar_TypeChecker_Env.pop tcenv "top-level: pop_env")
in ((()), (uu____171)))))
in (FStar_Pervasives_Native.snd uu____163)))


let with_env : 'a . uenv  ->  (uenv  ->  'a)  ->  'a = (fun env f -> (

let env1 = (push_env env)
in (

let res = (f env1)
in (

let uu____198 = (pop_env env1)
in res))))


let env_of_tcenv : FStar_TypeChecker_Env.env  ->  FStar_Extraction_ML_UEnv.uenv = (fun env -> (FStar_Extraction_ML_UEnv.mkContext env))


let parse : uenv  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  (FStar_Syntax_Syntax.modul * uenv) = (fun env pre_fn fn -> (

let uu____237 = (FStar_Parser_Driver.parse_file fn)
in (match (uu____237) with
| (ast, uu____254) -> begin
(

let uu____269 = (match (pre_fn) with
| FStar_Pervasives_Native.None -> begin
((ast), (env))
end
| FStar_Pervasives_Native.Some (pre_fn1) -> begin
(

let uu____282 = (FStar_Parser_Driver.parse_file pre_fn1)
in (match (uu____282) with
| (pre_ast, uu____299) -> begin
(match (((pre_ast), (ast))) with
| (FStar_Parser_AST.Interface (lid1, decls1, uu____320), FStar_Parser_AST.Module (lid2, decls2)) when (FStar_Ident.lid_equals lid1 lid2) -> begin
(

let uu____333 = (

let uu____338 = (FStar_ToSyntax_Interleave.initialize_interface lid1 decls1)
in (with_dsenv_of_env env uu____338))
in (match (uu____333) with
| (uu____347, env1) -> begin
(

let uu____349 = (FStar_ToSyntax_Interleave.interleave_module ast true)
in (with_dsenv_of_env env1 uu____349))
end))
end
| uu____355 -> begin
(FStar_Errors.raise_err ((FStar_Errors.Fatal_PreModuleMismatch), ("mismatch between pre-module and module\n")))
end)
end))
end)
in (match (uu____269) with
| (ast1, env1) -> begin
(

let uu____372 = (FStar_ToSyntax_ToSyntax.ast_modul_to_modul ast1)
in (with_dsenv_of_env env1 uu____372))
end))
end)))


let init_env : FStar_Parser_Dep.deps  ->  FStar_TypeChecker_Env.env = (fun deps -> (

let solver1 = (

let uu____384 = (FStar_Options.lax ())
in (match (uu____384) with
| true -> begin
FStar_SMTEncoding_Solver.dummy
end
| uu____387 -> begin
(

let uu___68_389 = FStar_SMTEncoding_Solver.solver
in {FStar_TypeChecker_Env.init = uu___68_389.FStar_TypeChecker_Env.init; FStar_TypeChecker_Env.push = uu___68_389.FStar_TypeChecker_Env.push; FStar_TypeChecker_Env.pop = uu___68_389.FStar_TypeChecker_Env.pop; FStar_TypeChecker_Env.snapshot = uu___68_389.FStar_TypeChecker_Env.snapshot; FStar_TypeChecker_Env.rollback = uu___68_389.FStar_TypeChecker_Env.rollback; FStar_TypeChecker_Env.encode_sig = uu___68_389.FStar_TypeChecker_Env.encode_sig; FStar_TypeChecker_Env.preprocess = FStar_Tactics_Interpreter.preprocess; FStar_TypeChecker_Env.solve = uu___68_389.FStar_TypeChecker_Env.solve; FStar_TypeChecker_Env.finish = uu___68_389.FStar_TypeChecker_Env.finish; FStar_TypeChecker_Env.refresh = uu___68_389.FStar_TypeChecker_Env.refresh})
end))
in (

let env = (

let uu____391 = (

let uu____406 = (FStar_Tactics_Interpreter.primitive_steps ())
in (FStar_TypeChecker_NBE.normalize uu____406))
in (FStar_TypeChecker_Env.initial_env deps FStar_TypeChecker_TcTerm.tc_term FStar_TypeChecker_TcTerm.type_of_tot_term FStar_TypeChecker_TcTerm.universe_of FStar_TypeChecker_TcTerm.check_type_of_well_typed_term solver1 FStar_Parser_Const.prims_lid uu____391))
in (

let env1 = (

let uu___72_410 = env
in {FStar_TypeChecker_Env.solver = uu___72_410.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___72_410.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___72_410.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___72_410.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___72_410.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___72_410.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___72_410.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___72_410.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___72_410.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___72_410.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___72_410.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___72_410.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___72_410.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___72_410.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___72_410.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___72_410.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___72_410.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___72_410.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___72_410.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___72_410.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___72_410.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___72_410.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___72_410.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___72_410.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___72_410.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___72_410.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___72_410.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___72_410.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___72_410.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___72_410.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___72_410.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___72_410.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___72_410.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___72_410.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___72_410.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = FStar_Tactics_Interpreter.synthesize; FStar_TypeChecker_Env.splice = uu___72_410.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___72_410.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___72_410.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___72_410.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___72_410.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___72_410.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___72_410.FStar_TypeChecker_Env.nbe})
in (

let env2 = (

let uu___75_412 = env1
in {FStar_TypeChecker_Env.solver = uu___75_412.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___75_412.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___75_412.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___75_412.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___75_412.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___75_412.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___75_412.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___75_412.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___75_412.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___75_412.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___75_412.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___75_412.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___75_412.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___75_412.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___75_412.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___75_412.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___75_412.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___75_412.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___75_412.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___75_412.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___75_412.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___75_412.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___75_412.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___75_412.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___75_412.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___75_412.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___75_412.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___75_412.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___75_412.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___75_412.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___75_412.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___75_412.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___75_412.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___75_412.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___75_412.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___75_412.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = FStar_Tactics_Interpreter.splice; FStar_TypeChecker_Env.postprocess = uu___75_412.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___75_412.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___75_412.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___75_412.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___75_412.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___75_412.FStar_TypeChecker_Env.nbe})
in (

let env3 = (

let uu___78_414 = env2
in {FStar_TypeChecker_Env.solver = uu___78_414.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___78_414.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___78_414.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___78_414.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___78_414.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___78_414.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___78_414.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___78_414.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___78_414.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___78_414.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___78_414.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___78_414.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___78_414.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___78_414.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___78_414.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___78_414.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___78_414.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___78_414.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___78_414.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___78_414.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___78_414.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___78_414.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___78_414.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___78_414.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___78_414.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___78_414.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___78_414.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___78_414.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___78_414.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___78_414.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___78_414.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___78_414.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___78_414.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___78_414.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___78_414.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___78_414.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___78_414.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = FStar_Tactics_Interpreter.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___78_414.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___78_414.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___78_414.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___78_414.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___78_414.FStar_TypeChecker_Env.nbe})
in (

let env4 = (

let uu___81_416 = env3
in {FStar_TypeChecker_Env.solver = uu___81_416.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___81_416.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___81_416.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___81_416.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___81_416.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___81_416.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___81_416.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___81_416.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___81_416.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___81_416.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___81_416.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___81_416.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___81_416.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___81_416.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___81_416.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___81_416.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___81_416.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___81_416.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___81_416.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___81_416.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___81_416.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___81_416.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___81_416.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___81_416.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___81_416.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___81_416.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___81_416.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___81_416.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___81_416.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___81_416.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___81_416.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___81_416.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___81_416.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___81_416.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___81_416.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___81_416.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___81_416.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___81_416.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = FStar_Tactics_Native.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___81_416.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___81_416.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___81_416.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___81_416.FStar_TypeChecker_Env.nbe})
in ((env4.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env4);
env4;
))))))))


let tc_one_fragment : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env_t  ->  FStar_Parser_ParseIt.input_frag  ->  (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_TypeChecker_Env.env_t) = (fun curmod env frag -> (

let acceptable_mod_name = (fun modul -> (

let uu____451 = (

let uu____453 = (

let uu____455 = (FStar_Options.file_list ())
in (FStar_List.hd uu____455))
in (FStar_Parser_Dep.lowercase_module_name uu____453))
in (

let uu____460 = (

let uu____462 = (FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name)
in (FStar_String.lowercase uu____462))
in (Prims.op_Equality uu____451 uu____460))))
in (

let range_of_first_mod_decl = (fun modul -> (match (modul) with
| FStar_Parser_AST.Module (uu____471, ({FStar_Parser_AST.d = uu____472; FStar_Parser_AST.drange = d; FStar_Parser_AST.doc = uu____474; FStar_Parser_AST.quals = uu____475; FStar_Parser_AST.attrs = uu____476})::uu____477) -> begin
d
end
| FStar_Parser_AST.Interface (uu____484, ({FStar_Parser_AST.d = uu____485; FStar_Parser_AST.drange = d; FStar_Parser_AST.doc = uu____487; FStar_Parser_AST.quals = uu____488; FStar_Parser_AST.attrs = uu____489})::uu____490, uu____491) -> begin
d
end
| uu____500 -> begin
FStar_Range.dummyRange
end))
in (

let uu____501 = (FStar_Parser_Driver.parse_fragment frag)
in (match (uu____501) with
| FStar_Parser_Driver.Empty -> begin
((curmod), (env))
end
| FStar_Parser_Driver.Decls ([]) -> begin
((curmod), (env))
end
| FStar_Parser_Driver.Modul (ast_modul) -> begin
(

let uu____513 = (

let uu____518 = (FStar_ToSyntax_Interleave.interleave_module ast_modul false)
in (FStar_All.pipe_left (with_dsenv_of_tcenv env) uu____518))
in (match (uu____513) with
| (ast_modul1, env1) -> begin
(

let uu____539 = (

let uu____544 = (FStar_ToSyntax_ToSyntax.partial_ast_modul_to_modul curmod ast_modul1)
in (FStar_All.pipe_left (with_dsenv_of_tcenv env1) uu____544))
in (match (uu____539) with
| (modul, env2) -> begin
((

let uu____565 = (

let uu____567 = (acceptable_mod_name modul)
in (not (uu____567)))
in (match (uu____565) with
| true -> begin
(

let msg = (

let uu____572 = (

let uu____574 = (

let uu____576 = (FStar_Options.file_list ())
in (FStar_List.hd uu____576))
in (FStar_Parser_Dep.module_name_of_file uu____574))
in (FStar_Util.format1 "Interactive mode only supports a single module at the top-level. Expected module %s" uu____572))
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_NonSingletonTopLevelModule), (msg)) (range_of_first_mod_decl ast_modul1)))
end
| uu____583 -> begin
()
end));
(

let uu____585 = (

let uu____596 = (FStar_Syntax_DsEnv.syntax_only env2.FStar_TypeChecker_Env.dsenv)
in (match (uu____596) with
| true -> begin
((((modul), ([]))), (env2))
end
| uu____617 -> begin
(

let uu____619 = (FStar_TypeChecker_Tc.tc_partial_modul env2 modul)
in (match (uu____619) with
| (m, i, e) -> begin
((((m), (i))), (e))
end))
end))
in (match (uu____585) with
| ((modul1, uu____660), env3) -> begin
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

let uu____683 = (FStar_List.hd ast_decls)
in (match (uu____683) with
| {FStar_Parser_AST.d = uu____690; FStar_Parser_AST.drange = rng; FStar_Parser_AST.doc = uu____692; FStar_Parser_AST.quals = uu____693; FStar_Parser_AST.attrs = uu____694} -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_ModuleFirstStatement), ("First statement must be a module declaration")) rng)
end))
end
| FStar_Pervasives_Native.Some (modul) -> begin
(

let uu____706 = (FStar_Util.fold_map (fun env1 a_decl -> (

let uu____724 = (

let uu____731 = (FStar_ToSyntax_Interleave.prefix_with_interface_decls a_decl)
in (FStar_All.pipe_left (with_dsenv_of_tcenv env1) uu____731))
in (match (uu____724) with
| (decls, env2) -> begin
((env2), (decls))
end))) env ast_decls)
in (match (uu____706) with
| (env1, ast_decls_l) -> begin
(

let uu____781 = (

let uu____786 = (FStar_ToSyntax_ToSyntax.decls_to_sigelts (FStar_List.flatten ast_decls_l))
in (FStar_All.pipe_left (with_dsenv_of_tcenv env1) uu____786))
in (match (uu____781) with
| (sigelts, env2) -> begin
(

let uu____806 = (

let uu____815 = (FStar_Syntax_DsEnv.syntax_only env2.FStar_TypeChecker_Env.dsenv)
in (match (uu____815) with
| true -> begin
((modul), ([]), (env2))
end
| uu____828 -> begin
(FStar_TypeChecker_Tc.tc_more_partial_modul env2 modul sigelts)
end))
in (match (uu____806) with
| (modul1, uu____837, env3) -> begin
((FStar_Pervasives_Native.Some (modul1)), (env3))
end))
end))
end))
end)
end)))))


let load_interface_decls : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Env.env_t = (fun env interface_file_name -> (

let r = (FStar_Parser_ParseIt.parse (FStar_Parser_ParseIt.Filename (interface_file_name)))
in (match (r) with
| FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inl (FStar_Parser_AST.Interface (l, decls, uu____861)), uu____862) -> begin
(

let uu____885 = (

let uu____890 = (FStar_ToSyntax_Interleave.initialize_interface l decls)
in (FStar_All.pipe_left (with_dsenv_of_tcenv env) uu____890))
in (FStar_Pervasives_Native.snd uu____885))
end
| FStar_Parser_ParseIt.ASTFragment (uu____902) -> begin
(

let uu____914 = (

let uu____920 = (FStar_Util.format1 "Unexpected result from parsing %s; expected a single interface" interface_file_name)
in ((FStar_Errors.Fatal_ParseErrors), (uu____920)))
in (FStar_Errors.raise_err uu____914))
end
| FStar_Parser_ParseIt.ParseError (err, msg, rng) -> begin
(FStar_Exn.raise (FStar_Errors.Error (((err), (msg), (rng)))))
end
| FStar_Parser_ParseIt.Term (uu____930) -> begin
(failwith "Impossible: parsing a Toplevel always results in an ASTFragment")
end)))


let emit : FStar_Extraction_ML_Syntax.mllib Prims.list  ->  unit = (fun mllibs -> (

let opt = (FStar_Options.codegen ())
in (match ((Prims.op_disEquality opt FStar_Pervasives_Native.None)) with
| true -> begin
(

let ext = (match (opt) with
| FStar_Pervasives_Native.Some (FStar_Options.FSharp) -> begin
".fs"
end
| FStar_Pervasives_Native.Some (FStar_Options.OCaml) -> begin
".ml"
end
| FStar_Pervasives_Native.Some (FStar_Options.Plugin) -> begin
".ml"
end
| FStar_Pervasives_Native.Some (FStar_Options.Kremlin) -> begin
".krml"
end
| uu____955 -> begin
(failwith "Unrecognized option")
end)
in (match (opt) with
| FStar_Pervasives_Native.Some (FStar_Options.FSharp) -> begin
(

let outdir = (FStar_Options.output_dir ())
in (FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext) mllibs))
end
| FStar_Pervasives_Native.Some (FStar_Options.OCaml) -> begin
(

let outdir = (FStar_Options.output_dir ())
in (FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext) mllibs))
end
| FStar_Pervasives_Native.Some (FStar_Options.Plugin) -> begin
(

let outdir = (FStar_Options.output_dir ())
in (FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext) mllibs))
end
| FStar_Pervasives_Native.Some (FStar_Options.Kremlin) -> begin
(

let programs = (FStar_List.collect FStar_Extraction_Kremlin.translate mllibs)
in (

let bin = ((FStar_Extraction_Kremlin.current_version), (programs))
in (match (programs) with
| ((name, uu____980))::[] -> begin
(

let uu____983 = (FStar_Options.prepend_output_dir (Prims.op_Hat name ext))
in (FStar_Util.save_value_to_file uu____983 bin))
end
| uu____985 -> begin
(

let uu____988 = (FStar_Options.prepend_output_dir "out.krml")
in (FStar_Util.save_value_to_file uu____988 bin))
end)))
end
| uu____991 -> begin
(failwith "Unrecognized option")
end))
end
| uu____995 -> begin
()
end)))


let tc_one_file : uenv  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  FStar_Parser_Dep.parsing_data  ->  (FStar_CheckedFiles.tc_result * FStar_Extraction_ML_Syntax.mllib FStar_Pervasives_Native.option * uenv) = (fun env pre_fn fn parsing_data -> ((FStar_Ident.reset_gensym ());
(

let maybe_restore_opts = (fun uu____1048 -> (

let uu____1049 = (

let uu____1051 = (FStar_Options.interactive ())
in (not (uu____1051)))
in (match (uu____1049) with
| true -> begin
(

let uu____1054 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right uu____1054 (fun a1 -> ())))
end
| uu____1056 -> begin
()
end)))
in (

let post_smt_encoding = (fun uu____1063 -> (FStar_SMTEncoding_Z3.refresh ()))
in (

let maybe_extract_mldefs = (fun tcmod env1 -> (

let uu____1082 = ((

let uu____1086 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____1086 FStar_Pervasives_Native.None)) || (

let uu____1092 = (FStar_Options.should_extract tcmod.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (not (uu____1092))))
in (match (uu____1082) with
| true -> begin
((FStar_Pervasives_Native.None), ((Prims.parse_int "0")))
end
| uu____1106 -> begin
(FStar_Util.record_time (fun uu____1114 -> (

let uu____1115 = (FStar_Extraction_ML_Modul.extract env1 tcmod)
in (match (uu____1115) with
| (uu____1124, defs) -> begin
defs
end))))
end)))
in (

let maybe_extract_ml_iface = (fun tcmod env1 -> (

let uu____1146 = (

let uu____1148 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____1148 FStar_Pervasives_Native.None))
in (match (uu____1146) with
| true -> begin
((env1), ((Prims.parse_int "0")))
end
| uu____1161 -> begin
(

let uu____1163 = (FStar_Util.record_time (fun uu____1178 -> (FStar_Extraction_ML_Modul.extract_iface env1 tcmod)))
in (match (uu____1163) with
| ((env2, _extracted_iface), iface_extract_time) -> begin
((env2), (iface_extract_time))
end))
end)))
in (

let tc_source_file = (fun uu____1207 -> (

let uu____1208 = (parse env pre_fn fn)
in (match (uu____1208) with
| (fmod, env1) -> begin
(

let mii = (FStar_Syntax_DsEnv.inclusion_info env1.FStar_Extraction_ML_UEnv.env_tcenv.FStar_TypeChecker_Env.dsenv fmod.FStar_Syntax_Syntax.name)
in (

let check_mod = (fun uu____1237 -> (

let uu____1238 = (FStar_Util.record_time (fun uu____1273 -> (with_tcenv_of_env env1 (fun tcenv -> ((match (tcenv.FStar_TypeChecker_Env.gamma) with
| [] -> begin
()
end
| uu____1293 -> begin
(failwith "Impossible: gamma contains leaked names")
end);
(

let uu____1297 = (FStar_TypeChecker_Tc.check_module tcenv fmod (FStar_Util.is_some pre_fn))
in (match (uu____1297) with
| (modul, env2) -> begin
((maybe_restore_opts ());
(

let smt_decls = (

let uu____1327 = (

let uu____1329 = (FStar_Options.lax ())
in (not (uu____1329)))
in (match (uu____1327) with
| true -> begin
(

let smt_decls = (FStar_SMTEncoding_Encode.encode_modul env2 modul)
in ((post_smt_encoding ());
smt_decls;
))
end
| uu____1346 -> begin
(([]), ([]))
end))
in ((((modul), (smt_decls))), (env2)));
)
end));
)))))
in (match (uu____1238) with
| (((tcmod, smt_decls), env2), tc_time) -> begin
(

let uu____1416 = (with_env env2 (maybe_extract_mldefs tcmod))
in (match (uu____1416) with
| (extracted_defs, extract_time) -> begin
(

let uu____1447 = (with_env env2 (maybe_extract_ml_iface tcmod))
in (match (uu____1447) with
| (env3, iface_extraction_time) -> begin
(({FStar_CheckedFiles.checked_module = tcmod; FStar_CheckedFiles.mii = mii; FStar_CheckedFiles.smt_decls = smt_decls; FStar_CheckedFiles.tc_time = tc_time; FStar_CheckedFiles.extraction_time = (extract_time + iface_extraction_time)}), (extracted_defs), (env3))
end))
end))
end)))
in (

let uu____1472 = ((FStar_Options.should_verify fmod.FStar_Syntax_Syntax.name.FStar_Ident.str) && ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ())))
in (match (uu____1472) with
| true -> begin
(

let uu____1483 = (FStar_Parser_ParseIt.find_file fn)
in (FStar_SMTEncoding_Solver.with_hints_db uu____1483 check_mod))
end
| uu____1493 -> begin
(check_mod ())
end))))
end)))
in (

let uu____1495 = (

let uu____1497 = (FStar_Options.cache_off ())
in (not (uu____1497)))
in (match (uu____1495) with
| true -> begin
(

let uu____1508 = (FStar_CheckedFiles.load_module_from_cache env fn)
in (match (uu____1508) with
| FStar_Pervasives_Native.None -> begin
((

let uu____1520 = (

let uu____1522 = (FStar_Parser_Dep.module_name_of_file fn)
in (FStar_Options.should_be_already_cached uu____1522))
in (match (uu____1520) with
| true -> begin
(

let uu____1525 = (

let uu____1531 = (FStar_Util.format1 "Expected %s to already be checked" fn)
in ((FStar_Errors.Error_AlreadyCachedAssertionFailure), (uu____1531)))
in (FStar_Errors.raise_err uu____1525))
end
| uu____1535 -> begin
()
end));
(

let uu____1538 = ((

let uu____1542 = (FStar_Options.codegen ())
in (FStar_Option.isSome uu____1542)) && (FStar_Options.cmi ()))
in (match (uu____1538) with
| true -> begin
(

let uu____1546 = (

let uu____1552 = (FStar_Util.format1 "Cross-module inlining expects all modules to be checked first; %s was not checked" fn)
in ((FStar_Errors.Error_AlreadyCachedAssertionFailure), (uu____1552)))
in (FStar_Errors.raise_err uu____1546))
end
| uu____1556 -> begin
()
end));
(

let uu____1558 = (tc_source_file ())
in (match (uu____1558) with
| (tc_result, mllib, env1) -> begin
((

let uu____1583 = ((

let uu____1587 = (FStar_Errors.get_err_count ())
in (Prims.op_Equality uu____1587 (Prims.parse_int "0"))) && ((FStar_Options.lax ()) || (FStar_Options.should_verify tc_result.FStar_CheckedFiles.checked_module.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in (match (uu____1583) with
| true -> begin
(FStar_CheckedFiles.store_module_to_cache env1 fn parsing_data tc_result)
end
| uu____1592 -> begin
()
end));
((tc_result), (mllib), (env1));
)
end));
)
end
| FStar_Pervasives_Native.Some (tc_result) -> begin
(

let tcmod = tc_result.FStar_CheckedFiles.checked_module
in (

let smt_decls = tc_result.FStar_CheckedFiles.smt_decls
in ((

let uu____1606 = (FStar_Options.dump_module tcmod.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____1606) with
| true -> begin
(

let uu____1609 = (FStar_Syntax_Print.modul_to_string tcmod)
in (FStar_Util.print1 "Module after type checking:\n%s\n" uu____1609))
end
| uu____1612 -> begin
()
end));
(

let extend_tcenv = (fun tcmod1 tcenv -> (

let uu____1629 = (

let uu____1634 = (FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod1 tc_result.FStar_CheckedFiles.mii (FStar_TypeChecker_Normalize.erase_universes tcenv))
in (FStar_All.pipe_left (with_dsenv_of_tcenv tcenv) uu____1634))
in (match (uu____1629) with
| (uu____1650, tcenv1) -> begin
(

let env1 = (FStar_TypeChecker_Tc.load_checked_module tcenv1 tcmod1)
in ((maybe_restore_opts ());
(

let uu____1655 = (

let uu____1657 = (FStar_Options.lax ())
in (not (uu____1657)))
in (match (uu____1655) with
| true -> begin
((FStar_SMTEncoding_Encode.encode_modul_from_cache env1 tcmod1.FStar_Syntax_Syntax.name smt_decls);
(post_smt_encoding ());
)
end
| uu____1661 -> begin
()
end));
((()), (env1));
))
end)))
in (

let env1 = (FStar_Options.profile (fun uu____1666 -> (

let uu____1667 = (with_tcenv_of_env env (extend_tcenv tcmod))
in (FStar_All.pipe_right uu____1667 FStar_Pervasives_Native.snd))) (fun uu____1677 -> (FStar_Util.format1 "Extending environment with module %s" tcmod.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in (

let mllib = (

let uu____1682 = (((

let uu____1686 = (FStar_Options.codegen ())
in (Prims.op_disEquality uu____1686 FStar_Pervasives_Native.None)) && (FStar_Options.should_extract tcmod.FStar_Syntax_Syntax.name.FStar_Ident.str)) && ((not (tcmod.FStar_Syntax_Syntax.is_interface)) || (

let uu____1692 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____1692 (FStar_Pervasives_Native.Some (FStar_Options.Kremlin))))))
in (match (uu____1682) with
| true -> begin
(with_env env1 (fun env2 -> (

let uu____1707 = (maybe_extract_mldefs tcmod env2)
in (match (uu____1707) with
| (extracted_defs, _extraction_time) -> begin
extracted_defs
end))))
end
| uu____1725 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____1727 = (with_env env1 (maybe_extract_ml_iface tcmod))
in (match (uu____1727) with
| (env2, _time) -> begin
((tc_result), (mllib), (env2))
end)))));
)))
end))
end
| uu____1752 -> begin
(

let uu____1754 = (tc_source_file ())
in (match (uu____1754) with
| (tc_result, mllib, env1) -> begin
((tc_result), (mllib), (env1))
end))
end)))))));
))


let tc_one_file_for_ide : FStar_TypeChecker_Env.env_t  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  FStar_Parser_Dep.parsing_data  ->  (FStar_CheckedFiles.tc_result * FStar_TypeChecker_Env.env_t) = (fun env pre_fn fn parsing_data -> (

let env1 = (env_of_tcenv env)
in (

let uu____1818 = (tc_one_file env1 pre_fn fn parsing_data)
in (match (uu____1818) with
| (tc_result, uu____1832, env2) -> begin
((tc_result), (env2.FStar_Extraction_ML_UEnv.env_tcenv))
end))))


let needs_interleaving : Prims.string  ->  Prims.string  ->  Prims.bool = (fun intf impl -> (

let m1 = (FStar_Parser_Dep.lowercase_module_name intf)
in (

let m2 = (FStar_Parser_Dep.lowercase_module_name impl)
in (((Prims.op_Equality m1 m2) && (

let uu____1860 = (FStar_Util.get_file_extension intf)
in (FStar_List.mem uu____1860 (("fsti")::("fsi")::[])))) && (

let uu____1869 = (FStar_Util.get_file_extension impl)
in (FStar_List.mem uu____1869 (("fst")::("fs")::[])))))))


let tc_one_file_from_remaining : Prims.string Prims.list  ->  uenv  ->  FStar_Parser_Dep.deps  ->  (Prims.string Prims.list * FStar_CheckedFiles.tc_result Prims.list * FStar_Extraction_ML_Syntax.mllib FStar_Pervasives_Native.option * uenv) = (fun remaining env deps -> (

let uu____1914 = (match (remaining) with
| (intf)::(impl)::remaining1 when (needs_interleaving intf impl) -> begin
(

let uu____1959 = (

let uu____1968 = (FStar_All.pipe_right impl (FStar_Parser_Dep.parsing_data_of deps))
in (tc_one_file env (FStar_Pervasives_Native.Some (intf)) impl uu____1968))
in (match (uu____1959) with
| (m, mllib, env1) -> begin
((remaining1), ((((m)::[]), (mllib), (env1))))
end))
end
| (intf_or_impl)::remaining1 -> begin
(

let uu____2019 = (

let uu____2028 = (FStar_All.pipe_right intf_or_impl (FStar_Parser_Dep.parsing_data_of deps))
in (tc_one_file env FStar_Pervasives_Native.None intf_or_impl uu____2028))
in (match (uu____2019) with
| (m, mllib, env1) -> begin
((remaining1), ((((m)::[]), (mllib), (env1))))
end))
end
| [] -> begin
(([]), ((([]), (FStar_Pervasives_Native.None), (env))))
end)
in (match (uu____1914) with
| (remaining1, (nmods, mllib, env1)) -> begin
((remaining1), (nmods), (mllib), (env1))
end)))


let rec tc_fold_interleave : FStar_Parser_Dep.deps  ->  (FStar_CheckedFiles.tc_result Prims.list * FStar_Extraction_ML_Syntax.mllib Prims.list * uenv)  ->  Prims.string Prims.list  ->  (FStar_CheckedFiles.tc_result Prims.list * FStar_Extraction_ML_Syntax.mllib Prims.list * uenv) = (fun deps acc remaining -> (

let as_list = (fun uu___0_2202 -> (match (uu___0_2202) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (l) -> begin
(l)::[]
end))
in (match (remaining) with
| [] -> begin
acc
end
| uu____2219 -> begin
(

let uu____2223 = acc
in (match (uu____2223) with
| (mods, mllibs, env) -> begin
(

let uu____2255 = (tc_one_file_from_remaining remaining env deps)
in (match (uu____2255) with
| (remaining1, nmods, mllib, env1) -> begin
(tc_fold_interleave deps (((FStar_List.append mods nmods)), ((FStar_List.append mllibs (as_list mllib))), (env1)) remaining1)
end))
end))
end)))


let batch_mode_tc : Prims.string Prims.list  ->  FStar_Parser_Dep.deps  ->  (FStar_CheckedFiles.tc_result Prims.list * uenv * (uenv  ->  uenv)) = (fun filenames dep_graph1 -> ((

let uu____2332 = (FStar_Options.debug_any ())
in (match (uu____2332) with
| true -> begin
((FStar_Util.print_endline "Auto-deps kicked in; here\'s some info.");
(FStar_Util.print1 "Here\'s the list of filenames we will process: %s\n" (FStar_String.concat " " filenames));
(

let uu____2340 = (

let uu____2342 = (FStar_All.pipe_right filenames (FStar_List.filter FStar_Options.should_verify_file))
in (FStar_String.concat " " uu____2342))
in (FStar_Util.print1 "Here\'s the list of modules we will verify: %s\n" uu____2340));
)
end
| uu____2355 -> begin
()
end));
(

let env = (

let uu____2358 = (init_env dep_graph1)
in (FStar_Extraction_ML_UEnv.mkContext uu____2358))
in (

let uu____2359 = (tc_fold_interleave dep_graph1 (([]), ([]), (env)) filenames)
in (match (uu____2359) with
| (all_mods, mllibs, env1) -> begin
((emit mllibs);
(

let solver_refresh = (fun env2 -> (

let uu____2403 = (with_tcenv_of_env env2 (fun tcenv -> ((

let uu____2412 = ((FStar_Options.interactive ()) && (

let uu____2415 = (FStar_Errors.get_err_count ())
in (Prims.op_Equality uu____2415 (Prims.parse_int "0"))))
in (match (uu____2412) with
| true -> begin
(tcenv.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end
| uu____2420 -> begin
(tcenv.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end));
((()), (tcenv));
)))
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____2403)))
in ((all_mods), (env1), (solver_refresh)));
)
end)));
))




