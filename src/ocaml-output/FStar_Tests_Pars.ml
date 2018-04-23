
open Prims
open FStar_Pervasives

let test_lid : FStar_Ident.lident = (FStar_Ident.lid_of_path (("Test")::[]) FStar_Range.dummyRange)


let tcenv_ref : FStar_TypeChecker_Env.env FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let test_mod_ref : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref (FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.name = test_lid; FStar_Syntax_Syntax.declarations = []; FStar_Syntax_Syntax.exports = []; FStar_Syntax_Syntax.is_interface = false})))


let parse_mod : FStar_Parser_ParseIt.filename  ->  FStar_Syntax_DsEnv.env  ->  (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.modul) = (fun mod_name1 dsenv1 -> (

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


let add_mods : FStar_Parser_ParseIt.filename Prims.list  ->  FStar_Syntax_DsEnv.env  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_DsEnv.env * FStar_TypeChecker_Env.env) = (fun mod_names dsenv1 env -> (FStar_List.fold_left (fun uu____173 mod_name1 -> (match (uu____173) with
| (dsenv2, env1) -> begin
(

let uu____185 = (parse_mod mod_name1 dsenv2)
in (match (uu____185) with
| (dsenv3, string_mod) -> begin
(

let uu____196 = (FStar_TypeChecker_Tc.check_module env1 string_mod)
in (match (uu____196) with
| (_mod, uu____210, env2) -> begin
((dsenv3), (env2))
end))
end))
end)) ((dsenv1), (env)) mod_names))


let init_once : unit  ->  unit = (fun uu____220 -> (

let solver1 = FStar_SMTEncoding_Solver.dummy
in (

let env = (FStar_TypeChecker_Env.initial_env FStar_Parser_Dep.empty_deps FStar_TypeChecker_TcTerm.tc_term FStar_TypeChecker_TcTerm.type_of_tot_term FStar_TypeChecker_TcTerm.universe_of FStar_TypeChecker_TcTerm.check_type_of_well_typed_term solver1 FStar_Parser_Const.prims_lid)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env);
(

let uu____224 = (

let uu____229 = (FStar_Options.prims ())
in (

let uu____230 = (FStar_Syntax_DsEnv.empty_env ())
in (parse_mod uu____229 uu____230)))
in (match (uu____224) with
| (dsenv1, prims_mod) -> begin
(

let env1 = (

let uu___55_234 = env
in {FStar_TypeChecker_Env.solver = uu___55_234.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___55_234.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___55_234.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___55_234.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___55_234.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___55_234.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___55_234.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___55_234.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___55_234.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___55_234.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___55_234.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___55_234.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___55_234.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___55_234.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___55_234.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___55_234.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___55_234.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___55_234.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___55_234.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___55_234.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___55_234.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___55_234.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___55_234.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___55_234.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___55_234.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___55_234.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___55_234.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___55_234.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___55_234.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___55_234.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___55_234.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___55_234.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___55_234.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___55_234.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___55_234.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___55_234.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = dsenv1; FStar_TypeChecker_Env.dep_graph = uu___55_234.FStar_TypeChecker_Env.dep_graph})
in (

let uu____235 = (FStar_TypeChecker_Tc.check_module env1 prims_mod)
in (match (uu____235) with
| (_prims_mod, uu____245, env2) -> begin
(

let env3 = (FStar_TypeChecker_Env.set_current_module env2 test_lid)
in (FStar_ST.op_Colon_Equals tcenv_ref (FStar_Pervasives_Native.Some (env3))))
end)))
end));
))))


let rec init : unit  ->  FStar_TypeChecker_Env.env = (fun uu____283 -> (

let uu____284 = (FStar_ST.op_Bang tcenv_ref)
in (match (uu____284) with
| FStar_Pervasives_Native.Some (f) -> begin
f
end
| uu____315 -> begin
((init_once ());
(init ());
)
end)))


let frag_of_text : Prims.string  ->  FStar_Parser_ParseIt.input_frag = (fun s -> {FStar_Parser_ParseIt.frag_text = s; FStar_Parser_ParseIt.frag_line = (Prims.parse_int "1"); FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")})


let pars : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (FStar_All.try_with (fun uu___57_333 -> (match (()) with
| () -> begin
(

let tcenv = (init ())
in (

let uu____335 = (

let uu____336 = (FStar_All.pipe_left (fun _0_17 -> FStar_Parser_ParseIt.Fragment (_0_17)) (frag_of_text s))
in (FStar_Parser_ParseIt.parse uu____336))
in (match (uu____335) with
| FStar_Parser_ParseIt.Term (t) -> begin
(FStar_ToSyntax_ToSyntax.desugar_term tcenv.FStar_TypeChecker_Env.dsenv t)
end
| FStar_Parser_ParseIt.ParseError (e, msg, r) -> begin
(FStar_Errors.raise_error ((e), (msg)) r)
end
| FStar_Parser_ParseIt.ASTFragment (uu____341) -> begin
(failwith "Impossible: parsing a Fragment always results in a Term")
end)))
end)) (fun uu___56_354 -> (match (uu___56_354) with
| e when (

let uu____356 = (FStar_Options.trace_error ())
in (not (uu____356))) -> begin
(FStar_Exn.raise e)
end))))


let tc : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (

let tm = (pars s)
in (

let tcenv = (init ())
in (

let tcenv1 = (

let uu___58_365 = tcenv
in {FStar_TypeChecker_Env.solver = uu___58_365.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___58_365.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___58_365.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___58_365.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___58_365.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___58_365.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___58_365.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___58_365.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___58_365.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___58_365.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___58_365.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___58_365.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___58_365.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___58_365.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = uu___58_365.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___58_365.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___58_365.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___58_365.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___58_365.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___58_365.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___58_365.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___58_365.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___58_365.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___58_365.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___58_365.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___58_365.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___58_365.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___58_365.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___58_365.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___58_365.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___58_365.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___58_365.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___58_365.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___58_365.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___58_365.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___58_365.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___58_365.FStar_TypeChecker_Env.dep_graph})
in (

let uu____366 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term tcenv1 tm)
in (match (uu____366) with
| (tm1, uu____374, uu____375) -> begin
tm1
end))))))


let pars_and_tc_fragment : Prims.string  ->  unit = (fun s -> ((FStar_Options.set_option "trace_error" (FStar_Options.Bool (true)));
(

let report = (fun uu____387 -> (

let uu____388 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right uu____388 (fun a239 -> ()))))
in (FStar_All.try_with (fun uu___60_396 -> (match (()) with
| () -> begin
(

let tcenv = (init ())
in (

let frag = (frag_of_text s)
in (FStar_All.try_with (fun uu___62_408 -> (match (()) with
| () -> begin
(

let uu____409 = (

let uu____416 = (FStar_ST.op_Bang test_mod_ref)
in (FStar_Universal.tc_one_fragment uu____416 tcenv frag))
in (match (uu____409) with
| (test_mod', tcenv') -> begin
((FStar_ST.op_Colon_Equals test_mod_ref test_mod');
(FStar_ST.op_Colon_Equals tcenv_ref (FStar_Pervasives_Native.Some (tcenv')));
(

let n1 = (FStar_Errors.get_err_count ())
in (match ((Prims.op_disEquality n1 (Prims.parse_int "0"))) with
| true -> begin
((report ());
(

let uu____510 = (

let uu____515 = (

let uu____516 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 "%s errors were reported" uu____516))
in ((FStar_Errors.Fatal_ErrorsReported), (uu____515)))
in (FStar_Errors.raise_err uu____510));
)
end
| uu____517 -> begin
()
end));
)
end))
end)) (fun uu___61_521 -> (match (uu___61_521) with
| e -> begin
((report ());
(FStar_Errors.raise_err ((FStar_Errors.Fatal_TcOneFragmentFailed), ((Prims.strcat "tc_one_fragment failed: " s))));
)
end)))))
end)) (fun uu___59_526 -> (match (uu___59_526) with
| e when (

let uu____528 = (FStar_Options.trace_error ())
in (not (uu____528))) -> begin
(FStar_Exn.raise e)
end))));
))




