
open Prims
open FStar_Pervasives

let test_lid : FStar_Ident.lident = (FStar_Ident.lid_of_path (("Test")::[]) FStar_Range.dummyRange)


let tcenv_ref : FStar_TypeChecker_Env.env FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let test_mod_ref : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref (FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.name = test_lid; FStar_Syntax_Syntax.declarations = []; FStar_Syntax_Syntax.exports = []; FStar_Syntax_Syntax.is_interface = false})))


let parse_mod : Prims.string  ->  FStar_Syntax_DsEnv.env  ->  (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.modul) = (fun mod_name1 dsenv1 -> (

let uu____49 = (FStar_Parser_ParseIt.parse (FStar_Parser_ParseIt.Filename (mod_name1)))
in (match (uu____49) with
| FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inl (m), uu____55) -> begin
(

let uu____70 = (

let uu____75 = (FStar_ToSyntax_ToSyntax.ast_modul_to_modul m)
in (uu____75 dsenv1))
in (match (uu____70) with
| (m1, env') -> begin
(

let uu____88 = (

let uu____93 = (FStar_Ident.lid_of_path (("Test")::[]) FStar_Range.dummyRange)
in (FStar_Syntax_DsEnv.prepare_module_or_interface false false env' uu____93 FStar_Syntax_DsEnv.default_mii))
in (match (uu____88) with
| (env'1, uu____99) -> begin
((env'1), (m1))
end))
end))
end
| FStar_Parser_ParseIt.ParseError (err, msg, r) -> begin
(FStar_Exn.raise (FStar_Errors.Error (((err), (msg), (r)))))
end
| FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inr (uu____107), uu____108) -> begin
(

let msg = (FStar_Util.format1 "%s: expected a module\n" mod_name1)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_ModuleExpected), (msg)) FStar_Range.dummyRange))
end
| FStar_Parser_ParseIt.Term (uu____130) -> begin
(failwith "Impossible: parsing a Filename always results in an ASTFragment")
end)))


let add_mods : Prims.string Prims.list  ->  FStar_Syntax_DsEnv.env  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_DsEnv.env * FStar_TypeChecker_Env.env) = (fun mod_names dsenv1 env -> (FStar_List.fold_left (fun uu____173 mod_name1 -> (match (uu____173) with
| (dsenv2, env1) -> begin
(

let uu____185 = (parse_mod mod_name1 dsenv2)
in (match (uu____185) with
| (dsenv3, string_mod) -> begin
(

let uu____196 = (FStar_TypeChecker_Tc.check_module env1 string_mod false)
in (match (uu____196) with
| (_mod, uu____210, env2) -> begin
((dsenv3), (env2))
end))
end))
end)) ((dsenv1), (env)) mod_names))


let init_once : unit  ->  unit = (fun uu____220 -> (

let solver1 = FStar_SMTEncoding_Solver.dummy
in (

let env = (FStar_TypeChecker_Env.initial_env FStar_Parser_Dep.empty_deps FStar_TypeChecker_TcTerm.tc_term FStar_TypeChecker_TcTerm.type_of_tot_term FStar_TypeChecker_TcTerm.universe_of FStar_TypeChecker_TcTerm.check_type_of_well_typed_term solver1 FStar_Parser_Const.prims_lid FStar_TypeChecker_NBE.normalize_for_unit_test)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env);
(

let uu____224 = (

let uu____229 = (FStar_Options.prims ())
in (

let uu____230 = (FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps)
in (parse_mod uu____229 uu____230)))
in (match (uu____224) with
| (dsenv1, prims_mod) -> begin
(

let env1 = (

let uu___423_234 = env
in {FStar_TypeChecker_Env.solver = uu___423_234.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___423_234.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___423_234.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___423_234.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___423_234.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___423_234.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___423_234.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___423_234.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___423_234.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___423_234.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___423_234.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___423_234.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___423_234.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___423_234.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___423_234.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___423_234.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___423_234.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___423_234.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___423_234.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___423_234.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___423_234.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___423_234.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___423_234.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___423_234.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___423_234.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___423_234.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___423_234.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___423_234.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___423_234.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___423_234.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___423_234.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___423_234.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___423_234.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___423_234.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___423_234.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___423_234.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___423_234.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___423_234.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___423_234.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___423_234.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___423_234.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = dsenv1; FStar_TypeChecker_Env.nbe = uu___423_234.FStar_TypeChecker_Env.nbe})
in (

let uu____235 = (FStar_TypeChecker_Tc.check_module env1 prims_mod false)
in (match (uu____235) with
| (_prims_mod, uu____245, env2) -> begin
(

let env3 = (

let uu___424_252 = env2
in {FStar_TypeChecker_Env.solver = uu___424_252.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___424_252.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___424_252.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___424_252.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___424_252.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___424_252.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___424_252.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___424_252.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___424_252.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___424_252.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___424_252.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___424_252.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___424_252.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___424_252.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___424_252.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___424_252.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___424_252.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___424_252.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___424_252.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___424_252.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___424_252.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___424_252.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___424_252.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___424_252.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___424_252.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___424_252.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___424_252.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___424_252.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___424_252.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___424_252.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___424_252.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___424_252.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___424_252.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___424_252.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___424_252.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___424_252.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___424_252.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___424_252.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___424_252.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___424_252.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___424_252.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = dsenv1; FStar_TypeChecker_Env.nbe = uu___424_252.FStar_TypeChecker_Env.nbe})
in (

let env4 = (FStar_TypeChecker_Env.set_current_module env3 test_lid)
in (FStar_ST.op_Colon_Equals tcenv_ref (FStar_Pervasives_Native.Some (env4)))))
end)))
end));
))))


let rec init : unit  ->  FStar_TypeChecker_Env.env = (fun uu____281 -> (

let uu____282 = (FStar_ST.op_Bang tcenv_ref)
in (match (uu____282) with
| FStar_Pervasives_Native.Some (f) -> begin
f
end
| uu____309 -> begin
((init_once ());
(init ());
)
end)))


let frag_of_text : Prims.string  ->  FStar_Parser_ParseIt.input_frag = (fun s -> {FStar_Parser_ParseIt.frag_text = s; FStar_Parser_ParseIt.frag_line = (Prims.parse_int "1"); FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")})


let pars : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (FStar_All.try_with (fun uu___426_327 -> (match (()) with
| () -> begin
(

let tcenv = (init ())
in (

let uu____329 = (

let uu____330 = (FStar_All.pipe_left (fun _0_1 -> FStar_Parser_ParseIt.Fragment (_0_1)) (frag_of_text s))
in (FStar_Parser_ParseIt.parse uu____330))
in (match (uu____329) with
| FStar_Parser_ParseIt.Term (t) -> begin
(FStar_ToSyntax_ToSyntax.desugar_term tcenv.FStar_TypeChecker_Env.dsenv t)
end
| FStar_Parser_ParseIt.ParseError (e, msg, r) -> begin
(FStar_Errors.raise_error ((e), (msg)) r)
end
| FStar_Parser_ParseIt.ASTFragment (uu____335) -> begin
(failwith "Impossible: parsing a Fragment always results in a Term")
end)))
end)) (fun uu___425_347 -> (Obj.magic (if (

let uu____348 = (FStar_Options.trace_error ())
in (not (uu____348))) then begin
(Obj.repr (FStar_Exn.raise uu___425_347))
end else begin
(Obj.repr (failwith "unreachable"))
end)))))


let tc' : Prims.string  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t * FStar_TypeChecker_Env.env) = (fun s -> (

let tm = (pars s)
in (

let tcenv = (init ())
in (

let tcenv1 = (

let uu___427_363 = tcenv
in {FStar_TypeChecker_Env.solver = uu___427_363.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___427_363.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___427_363.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___427_363.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___427_363.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___427_363.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___427_363.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___427_363.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___427_363.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___427_363.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___427_363.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___427_363.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___427_363.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___427_363.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___427_363.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___427_363.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___427_363.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___427_363.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___427_363.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___427_363.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___427_363.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___427_363.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___427_363.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___427_363.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___427_363.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___427_363.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___427_363.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___427_363.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___427_363.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___427_363.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___427_363.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___427_363.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___427_363.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___427_363.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___427_363.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___427_363.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___427_363.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___427_363.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___427_363.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___427_363.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___427_363.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___427_363.FStar_TypeChecker_Env.nbe})
in (

let uu____364 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term tcenv1 tm)
in (match (uu____364) with
| (tm1, uu____378, g) -> begin
((tm1), (g), (tcenv1))
end))))))


let tc : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (

let uu____385 = (tc' s)
in (match (uu____385) with
| (tm, uu____393, uu____394) -> begin
tm
end)))


let tc_nbe : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (

let uu____400 = (tc' s)
in (match (uu____400) with
| (tm, g, tcenv) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard tcenv g);
tm;
)
end)))


let tc_nbe_term : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun tm -> (

let tcenv = (init ())
in (

let tcenv1 = (

let uu___428_418 = tcenv
in {FStar_TypeChecker_Env.solver = uu___428_418.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___428_418.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___428_418.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___428_418.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___428_418.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___428_418.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___428_418.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___428_418.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___428_418.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___428_418.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___428_418.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___428_418.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___428_418.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___428_418.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___428_418.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___428_418.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___428_418.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___428_418.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___428_418.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___428_418.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___428_418.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___428_418.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___428_418.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___428_418.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___428_418.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___428_418.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___428_418.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___428_418.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___428_418.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___428_418.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___428_418.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___428_418.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___428_418.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___428_418.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___428_418.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___428_418.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___428_418.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___428_418.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___428_418.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___428_418.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___428_418.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___428_418.FStar_TypeChecker_Env.nbe})
in (

let uu____419 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term tcenv1 tm)
in (match (uu____419) with
| (tm1, uu____427, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard tcenv1 g);
tm1;
)
end)))))


let pars_and_tc_fragment : Prims.string  ->  unit = (fun s -> ((FStar_Options.set_option "trace_error" (FStar_Options.Bool (true)));
(

let report = (fun uu____441 -> (

let uu____442 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right uu____442 (fun a1 -> ()))))
in (FStar_All.try_with (fun uu___430_450 -> (match (()) with
| () -> begin
(

let tcenv = (init ())
in (

let frag = (frag_of_text s)
in (FStar_All.try_with (fun uu___432_462 -> (match (()) with
| () -> begin
(

let uu____463 = (

let uu____470 = (FStar_ST.op_Bang test_mod_ref)
in (FStar_Universal.tc_one_fragment uu____470 tcenv frag))
in (match (uu____463) with
| (test_mod', tcenv') -> begin
((FStar_ST.op_Colon_Equals test_mod_ref test_mod');
(FStar_ST.op_Colon_Equals tcenv_ref (FStar_Pervasives_Native.Some (tcenv')));
(

let n1 = (FStar_Errors.get_err_count ())
in (match ((Prims.op_disEquality n1 (Prims.parse_int "0"))) with
| true -> begin
((report ());
(

let uu____552 = (

let uu____557 = (

let uu____558 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "%s errors were reported" uu____558))
in ((FStar_Errors.Fatal_ErrorsReported), (uu____557)))
in (FStar_Errors.raise_err uu____552));
)
end
| uu____559 -> begin
()
end));
)
end))
end)) (fun uu___431_562 -> ((report ());
(FStar_Errors.raise_err ((FStar_Errors.Fatal_TcOneFragmentFailed), ((Prims.strcat "tc_one_fragment failed: " s))));
)))))
end)) (fun uu___429_565 -> (Obj.magic (if (

let uu____566 = (FStar_Options.trace_error ())
in (not (uu____566))) then begin
(Obj.repr (FStar_Exn.raise uu___429_565))
end else begin
(Obj.repr (failwith "unreachable"))
end)))));
))




