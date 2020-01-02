
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
in {FStar_TypeChecker_Env.solver = uu___8_51.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___8_51.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___8_51.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___8_51.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___8_51.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___8_51.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___8_51.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___8_51.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___8_51.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___8_51.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.instantiate_imp = uu___8_51.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___8_51.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___8_51.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___8_51.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___8_51.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___8_51.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___8_51.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___8_51.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___8_51.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___8_51.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___8_51.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___8_51.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___8_51.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___8_51.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___8_51.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___8_51.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___8_51.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___8_51.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___8_51.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___8_51.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___8_51.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___8_51.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___8_51.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___8_51.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___8_51.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___8_51.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.mpreprocess = uu___8_51.FStar_TypeChecker_Env.mpreprocess; FStar_TypeChecker_Env.postprocess = uu___8_51.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___8_51.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___8_51.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___8_51.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = dsenv1; FStar_TypeChecker_Env.nbe = uu___8_51.FStar_TypeChecker_Env.nbe; FStar_TypeChecker_Env.strict_args_tab = uu___8_51.FStar_TypeChecker_Env.strict_args_tab; FStar_TypeChecker_Env.erasable_types_tab = uu___8_51.FStar_TypeChecker_Env.erasable_types_tab})))
end)))


let with_tcenv_of_env : 'a . uenv  ->  (FStar_TypeChecker_Env.env  ->  ('a * FStar_TypeChecker_Env.env))  ->  ('a * uenv) = (fun e f -> (

let uu____87 = (f e.FStar_Extraction_ML_UEnv.env_tcenv)
in (match (uu____87) with
| (a, t') -> begin
((a), ((

let uu___16_99 = e
in {FStar_Extraction_ML_UEnv.env_tcenv = t'; FStar_Extraction_ML_UEnv.env_bindings = uu___16_99.FStar_Extraction_ML_UEnv.env_bindings; FStar_Extraction_ML_UEnv.env_mlident_map = uu___16_99.FStar_Extraction_ML_UEnv.env_mlident_map; FStar_Extraction_ML_UEnv.tydefs = uu___16_99.FStar_Extraction_ML_UEnv.tydefs; FStar_Extraction_ML_UEnv.type_names = uu___16_99.FStar_Extraction_ML_UEnv.type_names; FStar_Extraction_ML_UEnv.currentModule = uu___16_99.FStar_Extraction_ML_UEnv.currentModule})))
end)))


let with_dsenv_of_env : 'a . uenv  ->  'a FStar_Syntax_DsEnv.withenv  ->  ('a * uenv) = (fun e f -> (

let uu____128 = (with_dsenv_of_tcenv e.FStar_Extraction_ML_UEnv.env_tcenv f)
in (match (uu____128) with
| (a, tcenv) -> begin
((a), ((

let uu___24_140 = e
in {FStar_Extraction_ML_UEnv.env_tcenv = tcenv; FStar_Extraction_ML_UEnv.env_bindings = uu___24_140.FStar_Extraction_ML_UEnv.env_bindings; FStar_Extraction_ML_UEnv.env_mlident_map = uu___24_140.FStar_Extraction_ML_UEnv.env_mlident_map; FStar_Extraction_ML_UEnv.tydefs = uu___24_140.FStar_Extraction_ML_UEnv.tydefs; FStar_Extraction_ML_UEnv.type_names = uu___24_140.FStar_Extraction_ML_UEnv.type_names; FStar_Extraction_ML_UEnv.currentModule = uu___24_140.FStar_Extraction_ML_UEnv.currentModule})))
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
in {FStar_TypeChecker_Env.solver = uu___72_410.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___72_410.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___72_410.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___72_410.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___72_410.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___72_410.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___72_410.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___72_410.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___72_410.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___72_410.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.instantiate_imp = uu___72_410.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___72_410.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___72_410.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___72_410.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___72_410.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___72_410.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___72_410.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___72_410.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___72_410.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___72_410.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___72_410.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___72_410.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___72_410.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___72_410.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___72_410.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___72_410.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___72_410.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___72_410.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___72_410.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___72_410.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___72_410.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___72_410.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___72_410.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___72_410.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = FStar_Tactics_Interpreter.synthesize; FStar_TypeChecker_Env.splice = uu___72_410.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.mpreprocess = uu___72_410.FStar_TypeChecker_Env.mpreprocess; FStar_TypeChecker_Env.postprocess = uu___72_410.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___72_410.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___72_410.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___72_410.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___72_410.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___72_410.FStar_TypeChecker_Env.nbe; FStar_TypeChecker_Env.strict_args_tab = uu___72_410.FStar_TypeChecker_Env.strict_args_tab; FStar_TypeChecker_Env.erasable_types_tab = uu___72_410.FStar_TypeChecker_Env.erasable_types_tab})
in (

let env2 = (

let uu___75_412 = env1
in {FStar_TypeChecker_Env.solver = uu___75_412.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___75_412.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___75_412.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___75_412.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___75_412.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___75_412.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___75_412.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___75_412.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___75_412.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___75_412.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.instantiate_imp = uu___75_412.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___75_412.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___75_412.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___75_412.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___75_412.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___75_412.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___75_412.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___75_412.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___75_412.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___75_412.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___75_412.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___75_412.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___75_412.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___75_412.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___75_412.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___75_412.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___75_412.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___75_412.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___75_412.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___75_412.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___75_412.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___75_412.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___75_412.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___75_412.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___75_412.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = FStar_Tactics_Interpreter.splice; FStar_TypeChecker_Env.mpreprocess = uu___75_412.FStar_TypeChecker_Env.mpreprocess; FStar_TypeChecker_Env.postprocess = uu___75_412.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___75_412.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___75_412.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___75_412.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___75_412.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___75_412.FStar_TypeChecker_Env.nbe; FStar_TypeChecker_Env.strict_args_tab = uu___75_412.FStar_TypeChecker_Env.strict_args_tab; FStar_TypeChecker_Env.erasable_types_tab = uu___75_412.FStar_TypeChecker_Env.erasable_types_tab})
in (

let env3 = (

let uu___78_414 = env2
in {FStar_TypeChecker_Env.solver = uu___78_414.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___78_414.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___78_414.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___78_414.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___78_414.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___78_414.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___78_414.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___78_414.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___78_414.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___78_414.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.instantiate_imp = uu___78_414.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___78_414.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___78_414.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___78_414.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___78_414.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___78_414.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___78_414.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___78_414.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___78_414.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___78_414.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___78_414.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___78_414.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___78_414.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___78_414.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___78_414.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___78_414.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___78_414.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___78_414.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___78_414.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___78_414.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___78_414.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___78_414.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___78_414.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___78_414.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___78_414.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___78_414.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.mpreprocess = FStar_Tactics_Interpreter.mpreprocess; FStar_TypeChecker_Env.postprocess = uu___78_414.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___78_414.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___78_414.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___78_414.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___78_414.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___78_414.FStar_TypeChecker_Env.nbe; FStar_TypeChecker_Env.strict_args_tab = uu___78_414.FStar_TypeChecker_Env.strict_args_tab; FStar_TypeChecker_Env.erasable_types_tab = uu___78_414.FStar_TypeChecker_Env.erasable_types_tab})
in (

let env4 = (

let uu___81_416 = env3
in {FStar_TypeChecker_Env.solver = uu___81_416.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___81_416.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___81_416.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___81_416.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___81_416.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___81_416.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___81_416.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___81_416.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___81_416.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___81_416.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.instantiate_imp = uu___81_416.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___81_416.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___81_416.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___81_416.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___81_416.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___81_416.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___81_416.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___81_416.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___81_416.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___81_416.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___81_416.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___81_416.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___81_416.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___81_416.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___81_416.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___81_416.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___81_416.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___81_416.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___81_416.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___81_416.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___81_416.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___81_416.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___81_416.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___81_416.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___81_416.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___81_416.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.mpreprocess = uu___81_416.FStar_TypeChecker_Env.mpreprocess; FStar_TypeChecker_Env.postprocess = FStar_Tactics_Interpreter.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___81_416.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___81_416.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___81_416.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___81_416.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___81_416.FStar_TypeChecker_Env.nbe; FStar_TypeChecker_Env.strict_args_tab = uu___81_416.FStar_TypeChecker_Env.strict_args_tab; FStar_TypeChecker_Env.erasable_types_tab = uu___81_416.FStar_TypeChecker_Env.erasable_types_tab})
in (

let env5 = (

let uu___84_418 = env4
in {FStar_TypeChecker_Env.solver = uu___84_418.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___84_418.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___84_418.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___84_418.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___84_418.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___84_418.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___84_418.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___84_418.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___84_418.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___84_418.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.instantiate_imp = uu___84_418.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___84_418.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___84_418.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___84_418.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___84_418.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___84_418.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___84_418.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___84_418.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___84_418.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___84_418.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___84_418.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___84_418.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___84_418.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___84_418.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___84_418.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___84_418.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___84_418.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___84_418.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___84_418.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___84_418.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___84_418.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___84_418.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___84_418.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___84_418.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___84_418.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___84_418.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.mpreprocess = uu___84_418.FStar_TypeChecker_Env.mpreprocess; FStar_TypeChecker_Env.postprocess = uu___84_418.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = FStar_Tactics_Native.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___84_418.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___84_418.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___84_418.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___84_418.FStar_TypeChecker_Env.nbe; FStar_TypeChecker_Env.strict_args_tab = uu___84_418.FStar_TypeChecker_Env.strict_args_tab; FStar_TypeChecker_Env.erasable_types_tab = uu___84_418.FStar_TypeChecker_Env.erasable_types_tab})
in ((env5.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env5);
env5;
)))))))))


let tc_one_fragment : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env_t  ->  FStar_Parser_ParseIt.input_frag  ->  (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_TypeChecker_Env.env) = (fun curmod env frag -> (

let fname = (fun env1 -> (

let uu____453 = (FStar_Options.lsp_server ())
in (match (uu____453) with
| true -> begin
(

let uu____457 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Range.file_of_range uu____457))
end
| uu____458 -> begin
(

let uu____460 = (FStar_Options.file_list ())
in (FStar_List.hd uu____460))
end)))
in (

let acceptable_mod_name = (fun modul -> (

let uu____472 = (

let uu____474 = (fname env)
in (FStar_Parser_Dep.lowercase_module_name uu____474))
in (

let uu____476 = (

let uu____478 = (FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name)
in (FStar_String.lowercase uu____478))
in (Prims.op_Equality uu____472 uu____476))))
in (

let range_of_first_mod_decl = (fun modul -> (match (modul) with
| FStar_Parser_AST.Module (uu____487, ({FStar_Parser_AST.d = uu____488; FStar_Parser_AST.drange = d; FStar_Parser_AST.doc = uu____490; FStar_Parser_AST.quals = uu____491; FStar_Parser_AST.attrs = uu____492})::uu____493) -> begin
d
end
| FStar_Parser_AST.Interface (uu____500, ({FStar_Parser_AST.d = uu____501; FStar_Parser_AST.drange = d; FStar_Parser_AST.doc = uu____503; FStar_Parser_AST.quals = uu____504; FStar_Parser_AST.attrs = uu____505})::uu____506, uu____507) -> begin
d
end
| uu____516 -> begin
FStar_Range.dummyRange
end))
in (

let uu____517 = (FStar_Parser_Driver.parse_fragment frag)
in (match (uu____517) with
| FStar_Parser_Driver.Empty -> begin
((curmod), (env))
end
| FStar_Parser_Driver.Decls ([]) -> begin
((curmod), (env))
end
| FStar_Parser_Driver.Modul (ast_modul) -> begin
(

let uu____529 = (

let uu____534 = (FStar_ToSyntax_Interleave.interleave_module ast_modul false)
in (FStar_All.pipe_left (with_dsenv_of_tcenv env) uu____534))
in (match (uu____529) with
| (ast_modul1, env1) -> begin
(

let uu____555 = (

let uu____560 = (FStar_ToSyntax_ToSyntax.partial_ast_modul_to_modul curmod ast_modul1)
in (FStar_All.pipe_left (with_dsenv_of_tcenv env1) uu____560))
in (match (uu____555) with
| (modul, env2) -> begin
((

let uu____581 = (

let uu____583 = (acceptable_mod_name modul)
in (not (uu____583)))
in (match (uu____581) with
| true -> begin
(

let msg = (

let uu____588 = (

let uu____590 = (fname env2)
in (FStar_Parser_Dep.module_name_of_file uu____590))
in (FStar_Util.format1 "Interactive mode only supports a single module at the top-level. Expected module %s" uu____588))
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_NonSingletonTopLevelModule), (msg)) (range_of_first_mod_decl ast_modul1)))
end
| uu____594 -> begin
()
end));
(

let uu____596 = (

let uu____607 = (FStar_Syntax_DsEnv.syntax_only env2.FStar_TypeChecker_Env.dsenv)
in (match (uu____607) with
| true -> begin
((((modul), ([]))), (env2))
end
| uu____628 -> begin
(

let uu____630 = (FStar_TypeChecker_Tc.tc_partial_modul env2 modul)
in (match (uu____630) with
| (m, i, e) -> begin
((((m), (i))), (e))
end))
end))
in (match (uu____596) with
| ((modul1, uu____671), env3) -> begin
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

let uu____694 = (FStar_List.hd ast_decls)
in (match (uu____694) with
| {FStar_Parser_AST.d = uu____701; FStar_Parser_AST.drange = rng; FStar_Parser_AST.doc = uu____703; FStar_Parser_AST.quals = uu____704; FStar_Parser_AST.attrs = uu____705} -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_ModuleFirstStatement), ("First statement must be a module declaration")) rng)
end))
end
| FStar_Pervasives_Native.Some (modul) -> begin
(

let uu____717 = (FStar_Util.fold_map (fun env1 a_decl -> (

let uu____735 = (

let uu____742 = (FStar_ToSyntax_Interleave.prefix_with_interface_decls a_decl)
in (FStar_All.pipe_left (with_dsenv_of_tcenv env1) uu____742))
in (match (uu____735) with
| (decls, env2) -> begin
((env2), (decls))
end))) env ast_decls)
in (match (uu____717) with
| (env1, ast_decls_l) -> begin
(

let uu____792 = (

let uu____797 = (FStar_ToSyntax_ToSyntax.decls_to_sigelts (FStar_List.flatten ast_decls_l))
in (FStar_All.pipe_left (with_dsenv_of_tcenv env1) uu____797))
in (match (uu____792) with
| (sigelts, env2) -> begin
(

let uu____817 = (

let uu____826 = (FStar_Syntax_DsEnv.syntax_only env2.FStar_TypeChecker_Env.dsenv)
in (match (uu____826) with
| true -> begin
((modul), ([]), (env2))
end
| uu____839 -> begin
(FStar_TypeChecker_Tc.tc_more_partial_modul env2 modul sigelts)
end))
in (match (uu____817) with
| (modul1, uu____848, env3) -> begin
((FStar_Pervasives_Native.Some (modul1)), (env3))
end))
end))
end))
end)
end))))))


let load_interface_decls : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Env.env_t = (fun env interface_file_name -> (

let r = (FStar_Parser_ParseIt.parse (FStar_Parser_ParseIt.Filename (interface_file_name)))
in (match (r) with
| FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inl (FStar_Parser_AST.Interface (l, decls, uu____872)), uu____873) -> begin
(

let uu____896 = (

let uu____901 = (FStar_ToSyntax_Interleave.initialize_interface l decls)
in (FStar_All.pipe_left (with_dsenv_of_tcenv env) uu____901))
in (FStar_Pervasives_Native.snd uu____896))
end
| FStar_Parser_ParseIt.ASTFragment (uu____913) -> begin
(

let uu____925 = (

let uu____931 = (FStar_Util.format1 "Unexpected result from parsing %s; expected a single interface" interface_file_name)
in ((FStar_Errors.Fatal_ParseErrors), (uu____931)))
in (FStar_Errors.raise_err uu____925))
end
| FStar_Parser_ParseIt.ParseError (err, msg, rng) -> begin
(FStar_Exn.raise (FStar_Errors.Error (((err), (msg), (rng)))))
end
| FStar_Parser_ParseIt.Term (uu____941) -> begin
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
| uu____966 -> begin
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
| ((name, uu____991))::[] -> begin
(

let uu____994 = (FStar_Options.prepend_output_dir (Prims.op_Hat name ext))
in (FStar_Util.save_value_to_file uu____994 bin))
end
| uu____996 -> begin
(

let uu____999 = (FStar_Options.prepend_output_dir "out.krml")
in (FStar_Util.save_value_to_file uu____999 bin))
end)))
end
| uu____1002 -> begin
(failwith "Unrecognized option")
end))
end
| uu____1006 -> begin
()
end)))


let tc_one_file : uenv  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  FStar_Parser_Dep.parsing_data  ->  (FStar_CheckedFiles.tc_result * FStar_Extraction_ML_Syntax.mllib FStar_Pervasives_Native.option * uenv) = (fun env pre_fn fn parsing_data -> ((FStar_Ident.reset_gensym ());
(

let maybe_restore_opts = (fun uu____1059 -> (

let uu____1060 = (

let uu____1062 = (FStar_Options.interactive ())
in (not (uu____1062)))
in (match (uu____1060) with
| true -> begin
(

let uu____1065 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right uu____1065 (fun a1 -> ())))
end
| uu____1067 -> begin
()
end)))
in (

let post_smt_encoding = (fun uu____1074 -> (FStar_SMTEncoding_Z3.refresh ()))
in (

let maybe_extract_mldefs = (fun tcmod env1 -> (

let uu____1093 = ((

let uu____1097 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____1097 FStar_Pervasives_Native.None)) || (

let uu____1103 = (FStar_Options.should_extract tcmod.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (not (uu____1103))))
in (match (uu____1093) with
| true -> begin
((FStar_Pervasives_Native.None), ((Prims.parse_int "0")))
end
| uu____1117 -> begin
(FStar_Util.record_time (fun uu____1122 -> (with_env env1 (fun env2 -> (

let uu____1130 = (FStar_Extraction_ML_Modul.extract env2 tcmod)
in (match (uu____1130) with
| (uu____1139, defs) -> begin
defs
end))))))
end)))
in (

let maybe_extract_ml_iface = (fun tcmod env1 -> (

let uu____1161 = (

let uu____1163 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____1163 FStar_Pervasives_Native.None))
in (match (uu____1161) with
| true -> begin
((env1), ((Prims.parse_int "0")))
end
| uu____1176 -> begin
(FStar_Util.record_time (fun uu____1182 -> (

let uu____1183 = (with_env env1 (fun env2 -> (FStar_Extraction_ML_Modul.extract_iface env2 tcmod)))
in (match (uu____1183) with
| (env2, uu____1195) -> begin
env2
end))))
end)))
in (

let tc_source_file = (fun uu____1209 -> (

let uu____1210 = (parse env pre_fn fn)
in (match (uu____1210) with
| (fmod, env1) -> begin
(

let mii = (FStar_Syntax_DsEnv.inclusion_info env1.FStar_Extraction_ML_UEnv.env_tcenv.FStar_TypeChecker_Env.dsenv fmod.FStar_Syntax_Syntax.name)
in (

let check_mod = (fun uu____1239 -> (

let check1 = (fun env2 -> (with_tcenv_of_env env2 (fun tcenv -> ((match (tcenv.FStar_TypeChecker_Env.gamma) with
| [] -> begin
()
end
| uu____1279 -> begin
(failwith "Impossible: gamma contains leaked names")
end);
(

let uu____1283 = (FStar_TypeChecker_Tc.check_module tcenv fmod (FStar_Util.is_some pre_fn))
in (match (uu____1283) with
| (modul, env3) -> begin
((maybe_restore_opts ());
(

let smt_decls = (

let uu____1313 = (

let uu____1315 = (FStar_Options.lax ())
in (not (uu____1315)))
in (match (uu____1313) with
| true -> begin
(

let smt_decls = (FStar_SMTEncoding_Encode.encode_modul env3 modul)
in ((post_smt_encoding ());
smt_decls;
))
end
| uu____1332 -> begin
(([]), ([]))
end))
in ((((modul), (smt_decls))), (env3)));
)
end));
))))
in (

let uu____1352 = (FStar_Profiling.profile (fun uu____1382 -> (check1 env1)) (FStar_Pervasives_Native.Some (fmod.FStar_Syntax_Syntax.name.FStar_Ident.str)) "FStar.Universal.tc_source_file")
in (match (uu____1352) with
| ((tcmod, smt_decls), env2) -> begin
(

let tc_time = (Prims.parse_int "0")
in (

let uu____1421 = (maybe_extract_mldefs tcmod env2)
in (match (uu____1421) with
| (extracted_defs, extract_time) -> begin
(

let uu____1445 = (maybe_extract_ml_iface tcmod env2)
in (match (uu____1445) with
| (env3, iface_extraction_time) -> begin
(({FStar_CheckedFiles.checked_module = tcmod; FStar_CheckedFiles.mii = mii; FStar_CheckedFiles.smt_decls = smt_decls; FStar_CheckedFiles.tc_time = tc_time; FStar_CheckedFiles.extraction_time = (extract_time + iface_extraction_time)}), (extracted_defs), (env3))
end))
end)))
end))))
in (

let uu____1465 = ((FStar_Options.should_verify fmod.FStar_Syntax_Syntax.name.FStar_Ident.str) && ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ())))
in (match (uu____1465) with
| true -> begin
(

let uu____1476 = (FStar_Parser_ParseIt.find_file fn)
in (FStar_SMTEncoding_Solver.with_hints_db uu____1476 check_mod))
end
| uu____1486 -> begin
(check_mod ())
end))))
end)))
in (

let uu____1488 = (

let uu____1490 = (FStar_Options.cache_off ())
in (not (uu____1490)))
in (match (uu____1488) with
| true -> begin
(

let uu____1501 = (FStar_CheckedFiles.load_module_from_cache env fn)
in (match (uu____1501) with
| FStar_Pervasives_Native.None -> begin
((

let uu____1513 = (

let uu____1515 = (FStar_Parser_Dep.module_name_of_file fn)
in (FStar_Options.should_be_already_cached uu____1515))
in (match (uu____1513) with
| true -> begin
(

let uu____1518 = (

let uu____1524 = (FStar_Util.format1 "Expected %s to already be checked" fn)
in ((FStar_Errors.Error_AlreadyCachedAssertionFailure), (uu____1524)))
in (FStar_Errors.raise_err uu____1518))
end
| uu____1528 -> begin
()
end));
(

let uu____1531 = ((

let uu____1535 = (FStar_Options.codegen ())
in (FStar_Option.isSome uu____1535)) && (FStar_Options.cmi ()))
in (match (uu____1531) with
| true -> begin
(

let uu____1539 = (

let uu____1545 = (FStar_Util.format1 "Cross-module inlining expects all modules to be checked first; %s was not checked" fn)
in ((FStar_Errors.Error_AlreadyCachedAssertionFailure), (uu____1545)))
in (FStar_Errors.raise_err uu____1539))
end
| uu____1549 -> begin
()
end));
(

let uu____1551 = (tc_source_file ())
in (match (uu____1551) with
| (tc_result, mllib, env1) -> begin
((

let uu____1576 = ((

let uu____1580 = (FStar_Errors.get_err_count ())
in (Prims.op_Equality uu____1580 (Prims.parse_int "0"))) && ((FStar_Options.lax ()) || (FStar_Options.should_verify tc_result.FStar_CheckedFiles.checked_module.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in (match (uu____1576) with
| true -> begin
(FStar_CheckedFiles.store_module_to_cache env1 fn parsing_data tc_result)
end
| uu____1585 -> begin
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

let uu____1599 = (FStar_Options.dump_module tcmod.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____1599) with
| true -> begin
(

let uu____1602 = (FStar_Syntax_Print.modul_to_string tcmod)
in (FStar_Util.print1 "Module after type checking:\n%s\n" uu____1602))
end
| uu____1605 -> begin
()
end));
(

let extend_tcenv = (fun tcmod1 tcenv -> (

let uu____1622 = (

let uu____1627 = (FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod1 tc_result.FStar_CheckedFiles.mii (FStar_TypeChecker_Normalize.erase_universes tcenv))
in (FStar_All.pipe_left (with_dsenv_of_tcenv tcenv) uu____1627))
in (match (uu____1622) with
| (uu____1643, tcenv1) -> begin
(

let env1 = (FStar_TypeChecker_Tc.load_checked_module tcenv1 tcmod1)
in ((maybe_restore_opts ());
(

let uu____1648 = (

let uu____1650 = (FStar_Options.lax ())
in (not (uu____1650)))
in (match (uu____1648) with
| true -> begin
((FStar_SMTEncoding_Encode.encode_modul_from_cache env1 tcmod1 smt_decls);
(post_smt_encoding ());
)
end
| uu____1654 -> begin
()
end));
((()), (env1));
))
end)))
in (

let env1 = (FStar_Profiling.profile (fun uu____1659 -> (

let uu____1660 = (with_tcenv_of_env env (extend_tcenv tcmod))
in (FStar_All.pipe_right uu____1660 FStar_Pervasives_Native.snd))) FStar_Pervasives_Native.None "FStar.Universal.extend_tcenv")
in (

let mllib = (

let uu____1674 = (((

let uu____1678 = (FStar_Options.codegen ())
in (Prims.op_disEquality uu____1678 FStar_Pervasives_Native.None)) && (FStar_Options.should_extract tcmod.FStar_Syntax_Syntax.name.FStar_Ident.str)) && ((not (tcmod.FStar_Syntax_Syntax.is_interface)) || (

let uu____1684 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____1684 (FStar_Pervasives_Native.Some (FStar_Options.Kremlin))))))
in (match (uu____1674) with
| true -> begin
(

let uu____1692 = (maybe_extract_mldefs tcmod env1)
in (match (uu____1692) with
| (extracted_defs, _extraction_time) -> begin
extracted_defs
end))
end
| uu____1710 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____1712 = (maybe_extract_ml_iface tcmod env1)
in (match (uu____1712) with
| (env2, _time) -> begin
((tc_result), (mllib), (env2))
end)))));
)))
end))
end
| uu____1732 -> begin
(

let uu____1734 = (tc_source_file ())
in (match (uu____1734) with
| (tc_result, mllib, env1) -> begin
((tc_result), (mllib), (env1))
end))
end)))))));
))


let tc_one_file_for_ide : FStar_TypeChecker_Env.env_t  ->  Prims.string FStar_Pervasives_Native.option  ->  Prims.string  ->  FStar_Parser_Dep.parsing_data  ->  (FStar_CheckedFiles.tc_result * FStar_TypeChecker_Env.env_t) = (fun env pre_fn fn parsing_data -> (

let env1 = (env_of_tcenv env)
in (

let uu____1798 = (tc_one_file env1 pre_fn fn parsing_data)
in (match (uu____1798) with
| (tc_result, uu____1812, env2) -> begin
((tc_result), (env2.FStar_Extraction_ML_UEnv.env_tcenv))
end))))


let needs_interleaving : Prims.string  ->  Prims.string  ->  Prims.bool = (fun intf impl -> (

let m1 = (FStar_Parser_Dep.lowercase_module_name intf)
in (

let m2 = (FStar_Parser_Dep.lowercase_module_name impl)
in (((Prims.op_Equality m1 m2) && (

let uu____1840 = (FStar_Util.get_file_extension intf)
in (FStar_List.mem uu____1840 (("fsti")::("fsi")::[])))) && (

let uu____1849 = (FStar_Util.get_file_extension impl)
in (FStar_List.mem uu____1849 (("fst")::("fs")::[])))))))


let tc_one_file_from_remaining : Prims.string Prims.list  ->  uenv  ->  FStar_Parser_Dep.deps  ->  (Prims.string Prims.list * FStar_CheckedFiles.tc_result * FStar_Extraction_ML_Syntax.mllib FStar_Pervasives_Native.option * uenv) = (fun remaining env deps -> (

let uu____1892 = (match (remaining) with
| (intf)::(impl)::remaining1 when (needs_interleaving intf impl) -> begin
(

let uu____1933 = (

let uu____1942 = (FStar_All.pipe_right impl (FStar_Parser_Dep.parsing_data_of deps))
in (tc_one_file env (FStar_Pervasives_Native.Some (intf)) impl uu____1942))
in (match (uu____1933) with
| (m, mllib, env1) -> begin
((remaining1), (((m), (mllib), (env1))))
end))
end
| (intf_or_impl)::remaining1 -> begin
(

let uu____1987 = (

let uu____1996 = (FStar_All.pipe_right intf_or_impl (FStar_Parser_Dep.parsing_data_of deps))
in (tc_one_file env FStar_Pervasives_Native.None intf_or_impl uu____1996))
in (match (uu____1987) with
| (m, mllib, env1) -> begin
((remaining1), (((m), (mllib), (env1))))
end))
end
| [] -> begin
(failwith "Impossible: Empty remaining modules")
end)
in (match (uu____1892) with
| (remaining1, (nmods, mllib, env1)) -> begin
((remaining1), (nmods), (mllib), (env1))
end)))


let rec tc_fold_interleave : FStar_Parser_Dep.deps  ->  (FStar_CheckedFiles.tc_result Prims.list * FStar_Extraction_ML_Syntax.mllib Prims.list * uenv)  ->  Prims.string Prims.list  ->  (FStar_CheckedFiles.tc_result Prims.list * FStar_Extraction_ML_Syntax.mllib Prims.list * uenv) = (fun deps acc remaining -> (

let as_list = (fun uu___0_2152 -> (match (uu___0_2152) with
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
| uu____2169 -> begin
(

let uu____2173 = acc
in (match (uu____2173) with
| (mods, mllibs, env) -> begin
(

let uu____2205 = (tc_one_file_from_remaining remaining env deps)
in (match (uu____2205) with
| (remaining1, nmod, mllib, env1) -> begin
((

let uu____2244 = (

let uu____2246 = (FStar_Options.profile_group_by_decls ())
in (not (uu____2246)))
in (match (uu____2244) with
| true -> begin
(

let uu____2249 = (FStar_Ident.string_of_lid nmod.FStar_CheckedFiles.checked_module.FStar_Syntax_Syntax.name)
in (FStar_Profiling.report_and_clear uu____2249))
end
| uu____2251 -> begin
()
end));
(tc_fold_interleave deps (((FStar_List.append mods ((nmod)::[]))), ((FStar_List.append mllibs (as_list mllib))), (env1)) remaining1);
)
end))
end))
end)))


let batch_mode_tc : Prims.string Prims.list  ->  FStar_Parser_Dep.deps  ->  (FStar_CheckedFiles.tc_result Prims.list * uenv * (uenv  ->  uenv)) = (fun filenames dep_graph1 -> ((

let uu____2286 = (FStar_Options.debug_any ())
in (match (uu____2286) with
| true -> begin
((FStar_Util.print_endline "Auto-deps kicked in; here\'s some info.");
(FStar_Util.print1 "Here\'s the list of filenames we will process: %s\n" (FStar_String.concat " " filenames));
(

let uu____2294 = (

let uu____2296 = (FStar_All.pipe_right filenames (FStar_List.filter FStar_Options.should_verify_file))
in (FStar_String.concat " " uu____2296))
in (FStar_Util.print1 "Here\'s the list of modules we will verify: %s\n" uu____2294));
)
end
| uu____2309 -> begin
()
end));
(

let env = (

let uu____2312 = (init_env dep_graph1)
in (FStar_Extraction_ML_UEnv.mkContext uu____2312))
in (

let uu____2313 = (tc_fold_interleave dep_graph1 (([]), ([]), (env)) filenames)
in (match (uu____2313) with
| (all_mods, mllibs, env1) -> begin
((emit mllibs);
(

let solver_refresh = (fun env2 -> (

let uu____2357 = (with_tcenv_of_env env2 (fun tcenv -> ((

let uu____2366 = ((FStar_Options.interactive ()) && (

let uu____2369 = (FStar_Errors.get_err_count ())
in (Prims.op_Equality uu____2369 (Prims.parse_int "0"))))
in (match (uu____2366) with
| true -> begin
(tcenv.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end
| uu____2374 -> begin
(tcenv.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end));
((()), (tcenv));
)))
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____2357)))
in ((all_mods), (env1), (solver_refresh)));
)
end)));
))




