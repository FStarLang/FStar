
open Prims
open FStar_Pervasives

let set_hint_correlator : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env = (fun env se -> (

let tbl = (FStar_All.pipe_right env.FStar_TypeChecker_Env.qtbl_name_and_index FStar_Pervasives_Native.fst)
in (

let get_n = (fun lid -> (

let n_opt = (FStar_Util.smap_try_find tbl lid.FStar_Ident.str)
in (match ((FStar_Util.is_some n_opt)) with
| true -> begin
(FStar_All.pipe_right n_opt FStar_Util.must)
end
| uu____61 -> begin
(Prims.parse_int "0")
end)))
in (

let uu____64 = (FStar_Options.reuse_hint_for ())
in (match (uu____64) with
| FStar_Pervasives_Native.Some (l) -> begin
(

let lid = (

let uu____72 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_add_suffix uu____72 l))
in (

let uu___16_73 = env
in (

let uu____74 = (

let uu____89 = (

let uu____97 = (

let uu____103 = (get_n lid)
in ((lid), (uu____103)))
in FStar_Pervasives_Native.Some (uu____97))
in ((tbl), (uu____89)))
in {FStar_TypeChecker_Env.solver = uu___16_73.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___16_73.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___16_73.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___16_73.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___16_73.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___16_73.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___16_73.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___16_73.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___16_73.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___16_73.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___16_73.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___16_73.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___16_73.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___16_73.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___16_73.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___16_73.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___16_73.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___16_73.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___16_73.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___16_73.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___16_73.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___16_73.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___16_73.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___16_73.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___16_73.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___16_73.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___16_73.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___16_73.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___16_73.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___16_73.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___16_73.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu____74; FStar_TypeChecker_Env.normalized_eff_names = uu___16_73.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___16_73.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___16_73.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___16_73.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___16_73.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___16_73.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___16_73.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___16_73.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___16_73.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___16_73.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___16_73.FStar_TypeChecker_Env.nbe})))
end
| FStar_Pervasives_Native.None -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (

let lid = (match (lids) with
| [] -> begin
(

let uu____126 = (FStar_TypeChecker_Env.current_module env)
in (

let uu____127 = (

let uu____129 = (FStar_Ident.next_id ())
in (FStar_All.pipe_right uu____129 FStar_Util.string_of_int))
in (FStar_Ident.lid_add_suffix uu____126 uu____127)))
end
| (l)::uu____134 -> begin
l
end)
in (

let uu___25_137 = env
in (

let uu____138 = (

let uu____153 = (

let uu____161 = (

let uu____167 = (get_n lid)
in ((lid), (uu____167)))
in FStar_Pervasives_Native.Some (uu____161))
in ((tbl), (uu____153)))
in {FStar_TypeChecker_Env.solver = uu___25_137.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___25_137.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___25_137.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___25_137.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___25_137.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___25_137.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___25_137.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___25_137.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___25_137.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___25_137.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___25_137.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___25_137.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___25_137.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___25_137.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___25_137.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___25_137.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___25_137.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___25_137.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___25_137.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___25_137.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___25_137.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___25_137.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___25_137.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___25_137.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___25_137.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___25_137.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___25_137.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___25_137.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___25_137.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___25_137.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___25_137.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu____138; FStar_TypeChecker_Env.normalized_eff_names = uu___25_137.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___25_137.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___25_137.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___25_137.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___25_137.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___25_137.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___25_137.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___25_137.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___25_137.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___25_137.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___25_137.FStar_TypeChecker_Env.nbe}))))
end)))))


let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_Options.log_types ()) && (

let uu____193 = (

let uu____195 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____195))
in (not (uu____193)))))


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let uu____212 = (FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k)
in (match (uu____212) with
| (t1, c, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
t1;
)
end)))


let recheck_debug : Prims.string  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s env t -> ((

let uu____242 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____242) with
| true -> begin
(

let uu____246 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Term has been %s-transformed to:\n%s\n----------\n" s uu____246))
end
| uu____249 -> begin
()
end));
(

let uu____251 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (uu____251) with
| (t', uu____259, uu____260) -> begin
((

let uu____262 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____262) with
| true -> begin
(

let uu____266 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print1 "Re-checked; got:\n%s\n----------\n" uu____266))
end
| uu____269 -> begin
()
end));
t';
)
end));
))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (

let uu____287 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env uu____287)))


let check_nogen : 'Auu____297 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  ('Auu____297 Prims.list * FStar_Syntax_Syntax.term) = (fun env t k -> (

let t1 = (tc_check_trivial_guard env t k)
in (

let uu____320 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::[]) env t1)
in (([]), (uu____320)))))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun env m s -> (

let fail1 = (fun uu____356 -> (

let uu____357 = (FStar_TypeChecker_Err.unexpected_signature_for_monad env m s)
in (

let uu____363 = (FStar_Ident.range_of_lid m)
in (FStar_Errors.raise_error uu____357 uu____363))))
in (

let s1 = (FStar_Syntax_Subst.compress s)
in (match (s1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs1 = (FStar_Syntax_Subst.open_binders bs)
in (match (bs1) with
| ((a, uu____407))::((wp, uu____409))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____438 -> begin
(fail1 ())
end))
end
| uu____439 -> begin
(fail1 ())
end))))


let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (

let uu____451 = (FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs)
in (match (uu____451) with
| (open_annotated_univs, annotated_univ_names) -> begin
(

let open_univs = (fun n_binders t -> (

let uu____483 = (FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs)
in (FStar_Syntax_Subst.subst uu____483 t)))
in (

let open_univs_binders = (fun n_binders bs -> (

let uu____499 = (FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs)
in (FStar_Syntax_Subst.subst_binders uu____499 bs)))
in (

let n_effect_params = (FStar_List.length ed.FStar_Syntax_Syntax.binders)
in (

let uu____509 = (

let uu____516 = (open_univs_binders (Prims.parse_int "0") ed.FStar_Syntax_Syntax.binders)
in (

let uu____518 = (open_univs n_effect_params ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Subst.open_term' uu____516 uu____518)))
in (match (uu____509) with
| (effect_params_un, signature_un, opening) -> begin
(

let env = (FStar_TypeChecker_Env.push_univ_vars env0 annotated_univ_names)
in (

let uu____523 = (FStar_TypeChecker_TcTerm.tc_tparams env effect_params_un)
in (match (uu____523) with
| (effect_params, env1, uu____532) -> begin
(

let uu____533 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un)
in (match (uu____533) with
| (signature, uu____539) -> begin
(

let ed1 = (

let uu___98_541 = ed
in {FStar_Syntax_Syntax.cattributes = uu___98_541.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___98_541.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___98_541.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = uu___98_541.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = uu___98_541.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = uu___98_541.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = uu___98_541.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = uu___98_541.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = uu___98_541.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = uu___98_541.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = uu___98_541.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = uu___98_541.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = uu___98_541.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = uu___98_541.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = uu___98_541.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = uu___98_541.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = uu___98_541.FStar_Syntax_Syntax.actions; FStar_Syntax_Syntax.eff_attrs = uu___98_541.FStar_Syntax_Syntax.eff_attrs})
in (

let ed2 = (match (((effect_params), (annotated_univ_names))) with
| ([], []) -> begin
ed1
end
| uu____569 -> begin
(

let op = (fun uu____601 -> (match (uu____601) with
| (us, t) -> begin
(

let n_us = (FStar_List.length us)
in (

let uu____621 = (

let uu____622 = (FStar_Syntax_Subst.shift_subst n_us opening)
in (

let uu____625 = (open_univs n_us t)
in (FStar_Syntax_Subst.subst uu____622 uu____625)))
in ((us), (uu____621))))
end))
in (

let uu___110_628 = ed1
in (

let uu____629 = (op ed1.FStar_Syntax_Syntax.ret_wp)
in (

let uu____630 = (op ed1.FStar_Syntax_Syntax.bind_wp)
in (

let uu____631 = (op ed1.FStar_Syntax_Syntax.if_then_else)
in (

let uu____632 = (op ed1.FStar_Syntax_Syntax.ite_wp)
in (

let uu____633 = (op ed1.FStar_Syntax_Syntax.stronger)
in (

let uu____634 = (op ed1.FStar_Syntax_Syntax.close_wp)
in (

let uu____635 = (op ed1.FStar_Syntax_Syntax.assert_p)
in (

let uu____636 = (op ed1.FStar_Syntax_Syntax.assume_p)
in (

let uu____637 = (op ed1.FStar_Syntax_Syntax.null_wp)
in (

let uu____638 = (op ed1.FStar_Syntax_Syntax.trivial)
in (

let uu____639 = (

let uu____640 = (op (([]), (ed1.FStar_Syntax_Syntax.repr)))
in (FStar_Pervasives_Native.snd uu____640))
in (

let uu____651 = (op ed1.FStar_Syntax_Syntax.return_repr)
in (

let uu____652 = (op ed1.FStar_Syntax_Syntax.bind_repr)
in (

let uu____653 = (FStar_List.map (fun a -> (

let uu___113_661 = a
in (

let uu____662 = (

let uu____663 = (op ((a.FStar_Syntax_Syntax.action_univs), (a.FStar_Syntax_Syntax.action_defn)))
in (FStar_Pervasives_Native.snd uu____663))
in (

let uu____674 = (

let uu____675 = (op ((a.FStar_Syntax_Syntax.action_univs), (a.FStar_Syntax_Syntax.action_typ)))
in (FStar_Pervasives_Native.snd uu____675))
in {FStar_Syntax_Syntax.action_name = uu___113_661.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___113_661.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___113_661.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = uu___113_661.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = uu____662; FStar_Syntax_Syntax.action_typ = uu____674})))) ed1.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.cattributes = uu___110_628.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___110_628.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = annotated_univ_names; FStar_Syntax_Syntax.binders = uu___110_628.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = uu___110_628.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = uu____629; FStar_Syntax_Syntax.bind_wp = uu____630; FStar_Syntax_Syntax.if_then_else = uu____631; FStar_Syntax_Syntax.ite_wp = uu____632; FStar_Syntax_Syntax.stronger = uu____633; FStar_Syntax_Syntax.close_wp = uu____634; FStar_Syntax_Syntax.assert_p = uu____635; FStar_Syntax_Syntax.assume_p = uu____636; FStar_Syntax_Syntax.null_wp = uu____637; FStar_Syntax_Syntax.trivial = uu____638; FStar_Syntax_Syntax.repr = uu____639; FStar_Syntax_Syntax.return_repr = uu____651; FStar_Syntax_Syntax.bind_repr = uu____652; FStar_Syntax_Syntax.actions = uu____653; FStar_Syntax_Syntax.eff_attrs = uu___110_628.FStar_Syntax_Syntax.eff_attrs}))))))))))))))))
end)
in (

let wp_with_fresh_result_type = (fun env2 mname signature1 -> (

let fail1 = (fun t -> (

let uu____720 = (FStar_TypeChecker_Err.unexpected_signature_for_monad env2 mname t)
in (

let uu____726 = (FStar_Ident.range_of_lid mname)
in (FStar_Errors.raise_error uu____720 uu____726))))
in (

let uu____733 = (

let uu____734 = (FStar_Syntax_Subst.compress signature1)
in uu____734.FStar_Syntax_Syntax.n)
in (match (uu____733) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs1 = (FStar_Syntax_Subst.open_binders bs)
in (match (bs1) with
| ((a, uu____773))::((wp, uu____775))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____804 -> begin
(fail1 signature1)
end))
end
| uu____805 -> begin
(fail1 signature1)
end))))
in (

let uu____806 = (wp_with_fresh_result_type env1 ed2.FStar_Syntax_Syntax.mname ed2.FStar_Syntax_Syntax.signature)
in (match (uu____806) with
| (a, wp_a) -> begin
(

let fresh_effect_signature = (fun uu____830 -> (match (annotated_univ_names) with
| [] -> begin
(

let uu____837 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un)
in (match (uu____837) with
| (signature1, uu____849) -> begin
(wp_with_fresh_result_type env1 ed2.FStar_Syntax_Syntax.mname signature1)
end))
end
| uu____850 -> begin
(

let uu____853 = (

let uu____858 = (

let uu____859 = (FStar_Syntax_Subst.close_univ_vars annotated_univ_names signature)
in ((annotated_univ_names), (uu____859)))
in (FStar_TypeChecker_Env.inst_tscheme uu____858))
in (match (uu____853) with
| (uu____872, signature1) -> begin
(wp_with_fresh_result_type env1 ed2.FStar_Syntax_Syntax.mname signature1)
end))
end))
in (

let env2 = (

let uu____875 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None ed2.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env1 uu____875))
in ((

let uu____877 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED")))
in (match (uu____877) with
| true -> begin
(

let uu____882 = (FStar_Syntax_Print.lid_to_string ed2.FStar_Syntax_Syntax.mname)
in (

let uu____884 = (FStar_Syntax_Print.binders_to_string " " ed2.FStar_Syntax_Syntax.binders)
in (

let uu____887 = (FStar_Syntax_Print.term_to_string ed2.FStar_Syntax_Syntax.signature)
in (

let uu____889 = (

let uu____891 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Print.term_to_string uu____891))
in (

let uu____892 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.sort)
in (FStar_Util.print5 "Checking effect signature: %s %s : %s\n(a is %s:%s)\n" uu____882 uu____884 uu____887 uu____889 uu____892))))))
end
| uu____895 -> begin
()
end));
(

let check_and_gen' = (fun env3 uu____927 k -> (match (uu____927) with
| (us, t) -> begin
(match (annotated_univ_names) with
| [] -> begin
(check_and_gen env3 t k)
end
| (uu____963)::uu____964 -> begin
(

let uu____967 = (FStar_Syntax_Subst.subst_tscheme open_annotated_univs ((us), (t)))
in (match (uu____967) with
| (us1, t1) -> begin
(

let uu____990 = (FStar_Syntax_Subst.open_univ_vars us1 t1)
in (match (uu____990) with
| (us2, t2) -> begin
(

let uu____1005 = (

let uu____1006 = (FStar_TypeChecker_Env.push_univ_vars env3 us2)
in (tc_check_trivial_guard uu____1006 t2 k))
in (

let uu____1007 = (FStar_Syntax_Subst.close_univ_vars us2 t2)
in ((us2), (uu____1007))))
end))
end))
end)
end))
in (

let return_wp = (

let expected_k = (

let uu____1026 = (

let uu____1035 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1042 = (

let uu____1051 = (

let uu____1058 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____1058))
in (uu____1051)::[])
in (uu____1035)::uu____1042))
in (

let uu____1077 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow uu____1026 uu____1077)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.ret_wp expected_k))
in (

let bind_wp = (

let uu____1081 = (fresh_effect_signature ())
in (match (uu____1081) with
| (b, wp_b) -> begin
(

let a_wp_b = (

let uu____1097 = (

let uu____1106 = (

let uu____1113 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____1113))
in (uu____1106)::[])
in (

let uu____1126 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____1097 uu____1126)))
in (

let expected_k = (

let uu____1132 = (

let uu____1141 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Syntax.t_range)
in (

let uu____1148 = (

let uu____1157 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1164 = (

let uu____1173 = (FStar_Syntax_Syntax.mk_binder b)
in (

let uu____1180 = (

let uu____1189 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____1196 = (

let uu____1205 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (uu____1205)::[])
in (uu____1189)::uu____1196))
in (uu____1173)::uu____1180))
in (uu____1157)::uu____1164))
in (uu____1141)::uu____1148))
in (

let uu____1248 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____1132 uu____1248)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else1 = (

let p = (

let uu____1261 = (

let uu____1264 = (FStar_Ident.range_of_lid ed2.FStar_Syntax_Syntax.mname)
in FStar_Pervasives_Native.Some (uu____1264))
in (

let uu____1265 = (

let uu____1266 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____1266 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.new_bv uu____1261 uu____1265)))
in (

let expected_k = (

let uu____1278 = (

let uu____1287 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1294 = (

let uu____1303 = (FStar_Syntax_Syntax.mk_binder p)
in (

let uu____1310 = (

let uu____1319 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____1326 = (

let uu____1335 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1335)::[])
in (uu____1319)::uu____1326))
in (uu____1303)::uu____1310))
in (uu____1287)::uu____1294))
in (

let uu____1372 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1278 uu____1372)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (

let uu____1387 = (

let uu____1396 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1403 = (

let uu____1412 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1412)::[])
in (uu____1396)::uu____1403))
in (

let uu____1437 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1387 uu____1437)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let uu____1441 = (FStar_Syntax_Util.type_u ())
in (match (uu____1441) with
| (t, uu____1447) -> begin
(

let expected_k = (

let uu____1451 = (

let uu____1460 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1467 = (

let uu____1476 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____1483 = (

let uu____1492 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1492)::[])
in (uu____1476)::uu____1483))
in (uu____1460)::uu____1467))
in (

let uu____1523 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow uu____1451 uu____1523)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (

let uu____1536 = (

let uu____1539 = (FStar_Ident.range_of_lid ed2.FStar_Syntax_Syntax.mname)
in FStar_Pervasives_Native.Some (uu____1539))
in (

let uu____1540 = (

let uu____1541 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____1541 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.new_bv uu____1536 uu____1540)))
in (

let b_wp_a = (

let uu____1553 = (

let uu____1562 = (

let uu____1569 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder uu____1569))
in (uu____1562)::[])
in (

let uu____1582 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1553 uu____1582)))
in (

let expected_k = (

let uu____1588 = (

let uu____1597 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1604 = (

let uu____1613 = (FStar_Syntax_Syntax.mk_binder b)
in (

let uu____1620 = (

let uu____1629 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (uu____1629)::[])
in (uu____1613)::uu____1620))
in (uu____1597)::uu____1604))
in (

let uu____1660 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1588 uu____1660)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (

let uu____1675 = (

let uu____1684 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1691 = (

let uu____1700 = (

let uu____1707 = (

let uu____1708 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____1708 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.null_binder uu____1707))
in (

let uu____1717 = (

let uu____1726 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1726)::[])
in (uu____1700)::uu____1717))
in (uu____1684)::uu____1691))
in (

let uu____1757 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1675 uu____1757)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (

let uu____1772 = (

let uu____1781 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1788 = (

let uu____1797 = (

let uu____1804 = (

let uu____1805 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____1805 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.null_binder uu____1804))
in (

let uu____1814 = (

let uu____1823 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1823)::[])
in (uu____1797)::uu____1814))
in (uu____1781)::uu____1788))
in (

let uu____1854 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1772 uu____1854)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (

let uu____1869 = (

let uu____1878 = (FStar_Syntax_Syntax.mk_binder a)
in (uu____1878)::[])
in (

let uu____1897 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1869 uu____1897)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let uu____1901 = (FStar_Syntax_Util.type_u ())
in (match (uu____1901) with
| (t, uu____1907) -> begin
(

let expected_k = (

let uu____1911 = (

let uu____1920 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1927 = (

let uu____1936 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1936)::[])
in (uu____1920)::uu____1927))
in (

let uu____1961 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow uu____1911 uu____1961)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let uu____1964 = (

let uu____1977 = (

let uu____1978 = (FStar_Syntax_Subst.compress ed2.FStar_Syntax_Syntax.repr)
in uu____1978.FStar_Syntax_Syntax.n)
in (match (uu____1977) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((ed2.FStar_Syntax_Syntax.repr), (ed2.FStar_Syntax_Syntax.bind_repr), (ed2.FStar_Syntax_Syntax.return_repr), (ed2.FStar_Syntax_Syntax.actions))
end
| uu____1997 -> begin
(

let repr = (

let uu____1999 = (FStar_Syntax_Util.type_u ())
in (match (uu____1999) with
| (t, uu____2005) -> begin
(

let expected_k = (

let uu____2009 = (

let uu____2018 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____2025 = (

let uu____2034 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____2034)::[])
in (uu____2018)::uu____2025))
in (

let uu____2059 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow uu____2009 uu____2059)))
in (tc_check_trivial_guard env2 ed2.FStar_Syntax_Syntax.repr expected_k))
end))
in (

let mk_repr' = (fun t wp -> (

let repr1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) env2 repr)
in (

let uu____2076 = (

let uu____2083 = (

let uu____2084 = (

let uu____2101 = (

let uu____2112 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____2121 = (

let uu____2132 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____2132)::[])
in (uu____2112)::uu____2121))
in ((repr1), (uu____2101)))
in FStar_Syntax_Syntax.Tm_app (uu____2084))
in (FStar_Syntax_Syntax.mk uu____2083))
in (uu____2076 FStar_Pervasives_Native.None FStar_Range.dummyRange))))
in (

let mk_repr = (fun a1 wp -> (

let uu____2190 = (FStar_Syntax_Syntax.bv_to_name a1)
in (mk_repr' uu____2190 wp)))
in (

let destruct_repr = (fun t -> (

let uu____2205 = (

let uu____2206 = (FStar_Syntax_Subst.compress t)
in uu____2206.FStar_Syntax_Syntax.n)
in (match (uu____2205) with
| FStar_Syntax_Syntax.Tm_app (uu____2217, ((t1, uu____2219))::((wp, uu____2221))::[]) -> begin
((t1), (wp))
end
| uu____2280 -> begin
(failwith "Unexpected repr type")
end)))
in (

let bind_repr = (

let r = (

let uu____2292 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.range_0 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_All.pipe_right uu____2292 FStar_Syntax_Syntax.fv_to_tm))
in (

let uu____2293 = (fresh_effect_signature ())
in (match (uu____2293) with
| (b, wp_b) -> begin
(

let a_wp_b = (

let uu____2309 = (

let uu____2318 = (

let uu____2325 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____2325))
in (uu____2318)::[])
in (

let uu____2338 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____2309 uu____2338)))
in (

let wp_f = (FStar_Syntax_Syntax.gen_bv "wp_f" FStar_Pervasives_Native.None wp_a)
in (

let wp_g = (FStar_Syntax_Syntax.gen_bv "wp_g" FStar_Pervasives_Native.None a_wp_b)
in (

let x_a = (

let uu____2346 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" FStar_Pervasives_Native.None uu____2346))
in (

let wp_g_x = (

let uu____2351 = (

let uu____2356 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (

let uu____2357 = (

let uu____2358 = (

let uu____2367 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____2367))
in (uu____2358)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____2356 uu____2357)))
in (uu____2351 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let res = (

let wp = (

let uu____2398 = (

let uu____2403 = (

let uu____2404 = (FStar_TypeChecker_Env.inst_tscheme bind_wp)
in (FStar_All.pipe_right uu____2404 FStar_Pervasives_Native.snd))
in (

let uu____2413 = (

let uu____2414 = (

let uu____2417 = (

let uu____2420 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____2421 = (

let uu____2424 = (FStar_Syntax_Syntax.bv_to_name b)
in (

let uu____2425 = (

let uu____2428 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (

let uu____2429 = (

let uu____2432 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (uu____2432)::[])
in (uu____2428)::uu____2429))
in (uu____2424)::uu____2425))
in (uu____2420)::uu____2421))
in (r)::uu____2417)
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____2414))
in (FStar_Syntax_Syntax.mk_Tm_app uu____2403 uu____2413)))
in (uu____2398 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (mk_repr b wp))
in (

let maybe_range_arg = (

let uu____2450 = (FStar_Util.for_some (FStar_Syntax_Util.attr_eq FStar_Syntax_Util.dm4f_bind_range_attr) ed2.FStar_Syntax_Syntax.eff_attrs)
in (match (uu____2450) with
| true -> begin
(

let uu____2461 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Syntax.t_range)
in (

let uu____2468 = (

let uu____2477 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Syntax.t_range)
in (uu____2477)::[])
in (uu____2461)::uu____2468))
end
| uu____2502 -> begin
[]
end))
in (

let expected_k = (

let uu____2513 = (

let uu____2522 = (

let uu____2531 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____2538 = (

let uu____2547 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____2547)::[])
in (uu____2531)::uu____2538))
in (

let uu____2572 = (

let uu____2581 = (

let uu____2590 = (FStar_Syntax_Syntax.mk_binder wp_f)
in (

let uu____2597 = (

let uu____2606 = (

let uu____2613 = (

let uu____2614 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (mk_repr a uu____2614))
in (FStar_Syntax_Syntax.null_binder uu____2613))
in (

let uu____2615 = (

let uu____2624 = (FStar_Syntax_Syntax.mk_binder wp_g)
in (

let uu____2631 = (

let uu____2640 = (

let uu____2647 = (

let uu____2648 = (

let uu____2657 = (FStar_Syntax_Syntax.mk_binder x_a)
in (uu____2657)::[])
in (

let uu____2676 = (

let uu____2679 = (mk_repr b wp_g_x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____2679))
in (FStar_Syntax_Util.arrow uu____2648 uu____2676)))
in (FStar_Syntax_Syntax.null_binder uu____2647))
in (uu____2640)::[])
in (uu____2624)::uu____2631))
in (uu____2606)::uu____2615))
in (uu____2590)::uu____2597))
in (FStar_List.append maybe_range_arg uu____2581))
in (FStar_List.append uu____2522 uu____2572)))
in (

let uu____2724 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow uu____2513 uu____2724)))
in (

let uu____2727 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env2 expected_k)
in (match (uu____2727) with
| (expected_k1, uu____2735, uu____2736) -> begin
(

let env3 = (FStar_TypeChecker_Env.set_range env2 (FStar_Pervasives_Native.snd ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos)
in (

let env4 = (

let uu___248_2743 = env3
in {FStar_TypeChecker_Env.solver = uu___248_2743.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___248_2743.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___248_2743.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___248_2743.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___248_2743.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___248_2743.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___248_2743.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___248_2743.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___248_2743.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___248_2743.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___248_2743.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___248_2743.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___248_2743.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___248_2743.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___248_2743.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___248_2743.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___248_2743.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___248_2743.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___248_2743.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___248_2743.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___248_2743.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___248_2743.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___248_2743.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___248_2743.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___248_2743.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___248_2743.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___248_2743.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___248_2743.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___248_2743.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___248_2743.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___248_2743.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___248_2743.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___248_2743.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___248_2743.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___248_2743.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___248_2743.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___248_2743.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___248_2743.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___248_2743.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___248_2743.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___248_2743.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___248_2743.FStar_TypeChecker_Env.nbe})
in (

let br = (check_and_gen' env4 ed2.FStar_Syntax_Syntax.bind_repr expected_k1)
in br)))
end))))))))))
end)))
in (

let return_repr = (

let x_a = (

let uu____2756 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" FStar_Pervasives_Native.None uu____2756))
in (

let res = (

let wp = (

let uu____2764 = (

let uu____2769 = (

let uu____2770 = (FStar_TypeChecker_Env.inst_tscheme return_wp)
in (FStar_All.pipe_right uu____2770 FStar_Pervasives_Native.snd))
in (

let uu____2779 = (

let uu____2780 = (

let uu____2783 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____2784 = (

let uu____2787 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (uu____2787)::[])
in (uu____2783)::uu____2784))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____2780))
in (FStar_Syntax_Syntax.mk_Tm_app uu____2769 uu____2779)))
in (uu____2764 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (mk_repr a wp))
in (

let expected_k = (

let uu____2799 = (

let uu____2808 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____2815 = (

let uu____2824 = (FStar_Syntax_Syntax.mk_binder x_a)
in (uu____2824)::[])
in (uu____2808)::uu____2815))
in (

let uu____2849 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow uu____2799 uu____2849)))
in (

let uu____2852 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env2 expected_k)
in (match (uu____2852) with
| (expected_k1, uu____2860, uu____2861) -> begin
(

let env3 = (FStar_TypeChecker_Env.set_range env2 (FStar_Pervasives_Native.snd ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos)
in (

let uu____2867 = (check_and_gen' env3 ed2.FStar_Syntax_Syntax.return_repr expected_k1)
in (match (uu____2867) with
| (univs1, repr1) -> begin
(match (univs1) with
| [] -> begin
(([]), (repr1))
end
| uu____2890 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn), ("Unexpected universe-polymorphic return for effect")) repr1.FStar_Syntax_Syntax.pos)
end)
end)))
end)))))
in (

let actions = (

let check_action = (fun act -> (

let uu____2905 = (match ((Prims.op_Equality act.FStar_Syntax_Syntax.action_univs [])) with
| true -> begin
((env2), (act))
end
| uu____2917 -> begin
(

let uu____2919 = (FStar_Syntax_Subst.univ_var_opening act.FStar_Syntax_Syntax.action_univs)
in (match (uu____2919) with
| (usubst, uvs) -> begin
(

let uu____2942 = (FStar_TypeChecker_Env.push_univ_vars env2 uvs)
in (

let uu____2943 = (

let uu___277_2944 = act
in (

let uu____2945 = (FStar_Syntax_Subst.subst_binders usubst act.FStar_Syntax_Syntax.action_params)
in (

let uu____2946 = (FStar_Syntax_Subst.subst usubst act.FStar_Syntax_Syntax.action_defn)
in (

let uu____2947 = (FStar_Syntax_Subst.subst usubst act.FStar_Syntax_Syntax.action_typ)
in {FStar_Syntax_Syntax.action_name = uu___277_2944.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___277_2944.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uvs; FStar_Syntax_Syntax.action_params = uu____2945; FStar_Syntax_Syntax.action_defn = uu____2946; FStar_Syntax_Syntax.action_typ = uu____2947}))))
in ((uu____2942), (uu____2943))))
end))
end)
in (match (uu____2905) with
| (env3, act1) -> begin
(

let act_typ = (

let uu____2951 = (

let uu____2952 = (FStar_Syntax_Subst.compress act1.FStar_Syntax_Syntax.action_typ)
in uu____2952.FStar_Syntax_Syntax.n)
in (match (uu____2951) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let c1 = (FStar_Syntax_Util.comp_to_comp_typ c)
in (

let uu____2978 = (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name ed2.FStar_Syntax_Syntax.mname)
in (match (uu____2978) with
| true -> begin
(

let uu____2981 = (

let uu____2984 = (

let uu____2985 = (

let uu____2986 = (FStar_List.hd c1.FStar_Syntax_Syntax.effect_args)
in (FStar_Pervasives_Native.fst uu____2986))
in (mk_repr' c1.FStar_Syntax_Syntax.result_typ uu____2985))
in (FStar_Syntax_Syntax.mk_Total uu____2984))
in (FStar_Syntax_Util.arrow bs uu____2981))
end
| uu____3007 -> begin
act1.FStar_Syntax_Syntax.action_typ
end)))
end
| uu____3009 -> begin
act1.FStar_Syntax_Syntax.action_typ
end))
in (

let uu____3010 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env3 act_typ)
in (match (uu____3010) with
| (act_typ1, uu____3018, g_t) -> begin
(

let env' = (

let uu___294_3021 = (FStar_TypeChecker_Env.set_expected_typ env3 act_typ1)
in {FStar_TypeChecker_Env.solver = uu___294_3021.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___294_3021.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___294_3021.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___294_3021.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___294_3021.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___294_3021.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___294_3021.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___294_3021.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___294_3021.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___294_3021.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___294_3021.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = uu___294_3021.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___294_3021.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___294_3021.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___294_3021.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___294_3021.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___294_3021.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___294_3021.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___294_3021.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___294_3021.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___294_3021.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___294_3021.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___294_3021.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___294_3021.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___294_3021.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___294_3021.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___294_3021.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___294_3021.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___294_3021.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___294_3021.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___294_3021.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___294_3021.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___294_3021.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___294_3021.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___294_3021.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___294_3021.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___294_3021.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___294_3021.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___294_3021.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___294_3021.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___294_3021.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___294_3021.FStar_TypeChecker_Env.nbe})
in ((

let uu____3024 = (FStar_TypeChecker_Env.debug env3 (FStar_Options.Other ("ED")))
in (match (uu____3024) with
| true -> begin
(

let uu____3028 = (FStar_Ident.text_of_lid act1.FStar_Syntax_Syntax.action_name)
in (

let uu____3030 = (FStar_Syntax_Print.term_to_string act1.FStar_Syntax_Syntax.action_defn)
in (

let uu____3032 = (FStar_Syntax_Print.term_to_string act_typ1)
in (FStar_Util.print3 "Checking action %s:\n[definition]: %s\n[cps\'d type]: %s\n" uu____3028 uu____3030 uu____3032))))
end
| uu____3035 -> begin
()
end));
(

let uu____3037 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' act1.FStar_Syntax_Syntax.action_defn)
in (match (uu____3037) with
| (act_defn, uu____3045, g_a) -> begin
(

let act_defn1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]) env3 act_defn)
in (

let act_typ2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Beta)::[]) env3 act_typ1)
in (

let uu____3049 = (

let act_typ3 = (FStar_Syntax_Subst.compress act_typ2)
in (match (act_typ3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____3085 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____3085) with
| (bs1, uu____3097) -> begin
(

let res = (mk_repr' FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun)
in (

let k = (

let uu____3104 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs1 uu____3104))
in (

let uu____3107 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env3 k)
in (match (uu____3107) with
| (k1, uu____3121, g) -> begin
((k1), (g))
end))))
end))
end
| uu____3125 -> begin
(

let uu____3126 = (

let uu____3132 = (

let uu____3134 = (FStar_Syntax_Print.term_to_string act_typ3)
in (

let uu____3136 = (FStar_Syntax_Print.tag_of_term act_typ3)
in (FStar_Util.format2 "Actions must have function types (not: %s, a.k.a. %s)" uu____3134 uu____3136)))
in ((FStar_Errors.Fatal_ActionMustHaveFunctionType), (uu____3132)))
in (FStar_Errors.raise_error uu____3126 act_defn1.FStar_Syntax_Syntax.pos))
end))
in (match (uu____3049) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env3 act_typ2 expected_k)
in ((

let uu____3154 = (

let uu____3155 = (

let uu____3156 = (FStar_TypeChecker_Env.conj_guard g_t g)
in (FStar_TypeChecker_Env.conj_guard g_k uu____3156))
in (FStar_TypeChecker_Env.conj_guard g_a uu____3155))
in (FStar_TypeChecker_Rel.force_trivial_guard env3 uu____3154));
(

let act_typ3 = (

let uu____3158 = (

let uu____3159 = (FStar_Syntax_Subst.compress expected_k)
in uu____3159.FStar_Syntax_Syntax.n)
in (match (uu____3158) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____3184 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____3184) with
| (bs1, c1) -> begin
(

let uu____3191 = (destruct_repr (FStar_Syntax_Util.comp_result c1))
in (match (uu____3191) with
| (a1, wp) -> begin
(

let c2 = (

let uu____3211 = (

let uu____3212 = (env3.FStar_TypeChecker_Env.universe_of env3 a1)
in (uu____3212)::[])
in (

let uu____3213 = (

let uu____3224 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____3224)::[])
in {FStar_Syntax_Syntax.comp_univs = uu____3211; FStar_Syntax_Syntax.effect_name = ed2.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a1; FStar_Syntax_Syntax.effect_args = uu____3213; FStar_Syntax_Syntax.flags = []}))
in (

let uu____3249 = (FStar_Syntax_Syntax.mk_Comp c2)
in (FStar_Syntax_Util.arrow bs1 uu____3249)))
end))
end))
end
| uu____3252 -> begin
(failwith "Impossible (expected_k is an arrow)")
end))
in (

let uu____3254 = (match ((Prims.op_Equality act1.FStar_Syntax_Syntax.action_univs [])) with
| true -> begin
(FStar_TypeChecker_Util.generalize_universes env3 act_defn1)
end
| uu____3274 -> begin
(

let uu____3276 = (FStar_Syntax_Subst.close_univ_vars act1.FStar_Syntax_Syntax.action_univs act_defn1)
in ((act1.FStar_Syntax_Syntax.action_univs), (uu____3276)))
end)
in (match (uu____3254) with
| (univs1, act_defn2) -> begin
(

let act_typ4 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::[]) env3 act_typ3)
in (

let act_typ5 = (FStar_Syntax_Subst.close_univ_vars univs1 act_typ4)
in (

let uu___344_3295 = act1
in {FStar_Syntax_Syntax.action_name = uu___344_3295.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___344_3295.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs1; FStar_Syntax_Syntax.action_params = uu___344_3295.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = act_defn2; FStar_Syntax_Syntax.action_typ = act_typ5})))
end)));
))
end))))
end));
))
end)))
end)))
in (FStar_All.pipe_right ed2.FStar_Syntax_Syntax.actions (FStar_List.map check_action)))
in ((repr), (bind_repr), (return_repr), (actions)))))))))
end))
in (match (uu____1964) with
| (repr, bind_repr, return_repr, actions) -> begin
(

let t0 = (

let uu____3319 = (FStar_Syntax_Syntax.mk_Total ed2.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed2.FStar_Syntax_Syntax.binders uu____3319))
in (

let uu____3322 = (

let uu____3327 = (FStar_TypeChecker_Util.generalize_universes env0 t0)
in (match (uu____3327) with
| (gen_univs, t) -> begin
(match (annotated_univ_names) with
| [] -> begin
((gen_univs), (t))
end
| uu____3346 -> begin
(

let uu____3349 = ((Prims.op_Equality (FStar_List.length gen_univs) (FStar_List.length annotated_univ_names)) && (FStar_List.forall2 (fun u1 u2 -> (

let uu____3356 = (FStar_Syntax_Syntax.order_univ_name u1 u2)
in (Prims.op_Equality uu____3356 (Prims.parse_int "0")))) gen_univs annotated_univ_names))
in (match (uu____3349) with
| true -> begin
((gen_univs), (t))
end
| uu____3365 -> begin
(

let uu____3367 = (

let uu____3373 = (

let uu____3375 = (FStar_Util.string_of_int (FStar_List.length annotated_univ_names))
in (

let uu____3377 = (FStar_Util.string_of_int (FStar_List.length gen_univs))
in (FStar_Util.format2 "Expected an effect definition with %s universes; but found %s" uu____3375 uu____3377)))
in ((FStar_Errors.Fatal_UnexpectedNumberOfUniverse), (uu____3373)))
in (FStar_Errors.raise_error uu____3367 ed2.FStar_Syntax_Syntax.signature.FStar_Syntax_Syntax.pos))
end))
end)
end))
in (match (uu____3322) with
| (univs1, t) -> begin
(

let signature1 = (

let uu____3388 = (

let uu____3401 = (

let uu____3402 = (FStar_Syntax_Subst.compress t)
in uu____3402.FStar_Syntax_Syntax.n)
in ((effect_params), (uu____3401)))
in (match (uu____3388) with
| ([], uu____3413) -> begin
t
end
| (uu____3428, FStar_Syntax_Syntax.Tm_arrow (uu____3429, c)) -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____3467 -> begin
(failwith "Impossible : t is an arrow")
end))
in (

let close1 = (fun n1 ts -> (

let ts1 = (

let uu____3495 = (FStar_Syntax_Subst.close_tscheme effect_params ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs1 uu____3495))
in (

let m = (FStar_List.length (FStar_Pervasives_Native.fst ts1))
in ((

let uu____3502 = (((n1 >= (Prims.parse_int "0")) && (

let uu____3506 = (FStar_Syntax_Util.is_unknown (FStar_Pervasives_Native.snd ts1))
in (not (uu____3506)))) && (Prims.op_disEquality m n1))
in (match (uu____3502) with
| true -> begin
(

let error = (match ((m < n1)) with
| true -> begin
"not universe-polymorphic enough"
end
| uu____3519 -> begin
"too universe-polymorphic"
end)
in (

let err_msg = (

let uu____3524 = (FStar_Util.string_of_int m)
in (

let uu____3526 = (FStar_Util.string_of_int n1)
in (

let uu____3528 = (FStar_Syntax_Print.tscheme_to_string ts1)
in (FStar_Util.format4 "The effect combinator is %s (m,n=%s,%s) (%s)" error uu____3524 uu____3526 uu____3528))))
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_MismatchUniversePolymorphic), (err_msg)) (FStar_Pervasives_Native.snd ts1).FStar_Syntax_Syntax.pos)))
end
| uu____3536 -> begin
()
end));
ts1;
))))
in (

let close_action = (fun act -> (

let uu____3544 = (close1 (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_defn)))
in (match (uu____3544) with
| (univs2, defn) -> begin
(

let uu____3560 = (close1 (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_typ)))
in (match (uu____3560) with
| (univs', typ) -> begin
(

let uu___394_3577 = act
in {FStar_Syntax_Syntax.action_name = uu___394_3577.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___394_3577.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs2; FStar_Syntax_Syntax.action_params = uu___394_3577.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = defn; FStar_Syntax_Syntax.action_typ = typ})
end))
end)))
in (

let ed3 = (

let uu___397_3580 = ed2
in (

let uu____3581 = (close1 (Prims.parse_int "0") return_wp)
in (

let uu____3583 = (close1 (Prims.parse_int "1") bind_wp)
in (

let uu____3585 = (close1 (Prims.parse_int "0") if_then_else1)
in (

let uu____3587 = (close1 (Prims.parse_int "0") ite_wp)
in (

let uu____3589 = (close1 (Prims.parse_int "0") stronger)
in (

let uu____3591 = (close1 (Prims.parse_int "1") close_wp)
in (

let uu____3593 = (close1 (Prims.parse_int "0") assert_p)
in (

let uu____3595 = (close1 (Prims.parse_int "0") assume_p)
in (

let uu____3597 = (close1 (Prims.parse_int "0") null_wp)
in (

let uu____3599 = (close1 (Prims.parse_int "0") trivial_wp)
in (

let uu____3601 = (

let uu____3602 = (close1 (Prims.parse_int "0") (([]), (repr)))
in (FStar_Pervasives_Native.snd uu____3602))
in (

let uu____3620 = (close1 (Prims.parse_int "0") return_repr)
in (

let uu____3622 = (close1 (Prims.parse_int "1") bind_repr)
in (

let uu____3624 = (FStar_List.map close_action actions)
in {FStar_Syntax_Syntax.cattributes = uu___397_3580.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___397_3580.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs1; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature1; FStar_Syntax_Syntax.ret_wp = uu____3581; FStar_Syntax_Syntax.bind_wp = uu____3583; FStar_Syntax_Syntax.if_then_else = uu____3585; FStar_Syntax_Syntax.ite_wp = uu____3587; FStar_Syntax_Syntax.stronger = uu____3589; FStar_Syntax_Syntax.close_wp = uu____3591; FStar_Syntax_Syntax.assert_p = uu____3593; FStar_Syntax_Syntax.assume_p = uu____3595; FStar_Syntax_Syntax.null_wp = uu____3597; FStar_Syntax_Syntax.trivial = uu____3599; FStar_Syntax_Syntax.repr = uu____3601; FStar_Syntax_Syntax.return_repr = uu____3620; FStar_Syntax_Syntax.bind_repr = uu____3622; FStar_Syntax_Syntax.actions = uu____3624; FStar_Syntax_Syntax.eff_attrs = uu___397_3580.FStar_Syntax_Syntax.eff_attrs})))))))))))))))
in ((

let uu____3628 = ((FStar_TypeChecker_Env.debug env2 FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("ED"))))
in (match (uu____3628) with
| true -> begin
(

let uu____3633 = (FStar_Syntax_Print.eff_decl_to_string false ed3)
in (FStar_Util.print_string uu____3633))
end
| uu____3636 -> begin
()
end));
ed3;
)))))
end)))
end)))))))))))));
)))
end)))))
end))
end)))
end)))))
end)))


let cps_and_elaborate : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option) = (fun env ed -> (

let uu____3659 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____3659) with
| (effect_binders_un, signature_un) -> begin
(

let uu____3676 = (FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un)
in (match (uu____3676) with
| (effect_binders, env1, uu____3695) -> begin
(

let uu____3696 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un)
in (match (uu____3696) with
| (signature, uu____3712) -> begin
(

let raise_error1 = (fun uu____3728 -> (match (uu____3728) with
| (e, err_msg) -> begin
(FStar_Errors.raise_error ((e), (err_msg)) signature.FStar_Syntax_Syntax.pos)
end))
in (

let effect_binders1 = (FStar_List.map (fun uu____3764 -> (match (uu____3764) with
| (bv, qual) -> begin
(

let uu____3783 = (

let uu___422_3784 = bv
in (

let uu____3785 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.EraseUniverses)::[]) env1 bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___422_3784.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___422_3784.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3785}))
in ((uu____3783), (qual)))
end)) effect_binders)
in (

let uu____3790 = (

let uu____3797 = (

let uu____3798 = (FStar_Syntax_Subst.compress signature_un)
in uu____3798.FStar_Syntax_Syntax.n)
in (match (uu____3797) with
| FStar_Syntax_Syntax.Tm_arrow (((a, uu____3808))::[], effect_marker) -> begin
((a), (effect_marker))
end
| uu____3840 -> begin
(raise_error1 ((FStar_Errors.Fatal_BadSignatureShape), ("bad shape for effect-for-free signature")))
end))
in (match (uu____3790) with
| (a, effect_marker) -> begin
(

let a1 = (

let uu____3866 = (FStar_Syntax_Syntax.is_null_bv a)
in (match (uu____3866) with
| true -> begin
(

let uu____3869 = (

let uu____3872 = (FStar_Syntax_Syntax.range_of_bv a)
in FStar_Pervasives_Native.Some (uu____3872))
in (FStar_Syntax_Syntax.gen_bv "a" uu____3869 a.FStar_Syntax_Syntax.sort))
end
| uu____3874 -> begin
a
end))
in (

let open_and_check = (fun env2 other_binders t -> (

let subst1 = (FStar_Syntax_Subst.opening_of_binders (FStar_List.append effect_binders1 other_binders))
in (

let t1 = (FStar_Syntax_Subst.subst subst1 t)
in (

let uu____3920 = (FStar_TypeChecker_TcTerm.tc_term env2 t1)
in (match (uu____3920) with
| (t2, comp, uu____3933) -> begin
((t2), (comp))
end)))))
in (

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None signature.FStar_Syntax_Syntax.pos))
in (

let uu____3942 = (open_and_check env1 [] ed.FStar_Syntax_Syntax.repr)
in (match (uu____3942) with
| (repr, _comp) -> begin
((

let uu____3966 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____3966) with
| true -> begin
(

let uu____3970 = (FStar_Syntax_Print.term_to_string repr)
in (FStar_Util.print1 "Representation is: %s\n" uu____3970))
end
| uu____3973 -> begin
()
end));
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env1 (FStar_TypeChecker_TcTerm.tc_constant env1 FStar_Range.dummyRange))
in (

let wp_type = (FStar_TypeChecker_DMFF.star_type dmff_env repr)
in (

let uu____3977 = (recheck_debug "*" env1 wp_type)
in (

let wp_a = (

let uu____3980 = (

let uu____3981 = (

let uu____3982 = (

let uu____3999 = (

let uu____4010 = (

let uu____4019 = (FStar_Syntax_Syntax.bv_to_name a1)
in (

let uu____4022 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____4019), (uu____4022))))
in (uu____4010)::[])
in ((wp_type), (uu____3999)))
in FStar_Syntax_Syntax.Tm_app (uu____3982))
in (mk1 uu____3981))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::[]) env1 uu____3980))
in (

let effect_signature = (

let binders = (

let uu____4070 = (

let uu____4077 = (FStar_Syntax_Syntax.as_implicit false)
in ((a1), (uu____4077)))
in (

let uu____4083 = (

let uu____4092 = (

let uu____4099 = (FStar_Syntax_Syntax.gen_bv "dijkstra_wp" FStar_Pervasives_Native.None wp_a)
in (FStar_All.pipe_right uu____4099 FStar_Syntax_Syntax.mk_binder))
in (uu____4092)::[])
in (uu____4070)::uu____4083))
in (

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in (mk1 (FStar_Syntax_Syntax.Tm_arrow (((binders1), (effect_marker)))))))
in (

let uu____4136 = (recheck_debug "turned into the effect signature" env1 effect_signature)
in (

let sigelts = (FStar_Util.mk_ref [])
in (

let mk_lid = (fun name -> (FStar_Syntax_Util.dm4f_lid ed name))
in (

let elaborate_and_star = (fun dmff_env1 other_binders item -> (

let env2 = (FStar_TypeChecker_DMFF.get_env dmff_env1)
in (

let uu____4202 = item
in (match (uu____4202) with
| (u_item, item1) -> begin
(

let uu____4217 = (open_and_check env2 other_binders item1)
in (match (uu____4217) with
| (item2, item_comp) -> begin
((

let uu____4233 = (

let uu____4235 = (FStar_Syntax_Util.is_total_lcomp item_comp)
in (not (uu____4235)))
in (match (uu____4233) with
| true -> begin
(

let uu____4238 = (

let uu____4244 = (

let uu____4246 = (FStar_Syntax_Print.term_to_string item2)
in (

let uu____4248 = (FStar_Syntax_Print.lcomp_to_string item_comp)
in (FStar_Util.format2 "Computation for [%s] is not total : %s !" uu____4246 uu____4248)))
in ((FStar_Errors.Fatal_ComputationNotTotal), (uu____4244)))
in (FStar_Errors.raise_err uu____4238))
end
| uu____4252 -> begin
()
end));
(

let uu____4254 = (FStar_TypeChecker_DMFF.star_expr dmff_env1 item2)
in (match (uu____4254) with
| (item_t, item_wp, item_elab) -> begin
(

let uu____4272 = (recheck_debug "*" env2 item_wp)
in (

let uu____4274 = (recheck_debug "_" env2 item_elab)
in ((dmff_env1), (item_t), (item_wp), (item_elab))))
end));
)
end))
end))))
in (

let uu____4276 = (elaborate_and_star dmff_env [] ed.FStar_Syntax_Syntax.bind_repr)
in (match (uu____4276) with
| (dmff_env1, uu____4302, bind_wp, bind_elab) -> begin
(

let uu____4305 = (elaborate_and_star dmff_env1 [] ed.FStar_Syntax_Syntax.return_repr)
in (match (uu____4305) with
| (dmff_env2, uu____4331, return_wp, return_elab) -> begin
(

let rc_gtot = {FStar_Syntax_Syntax.residual_effect = FStar_Parser_Const.effect_GTot_lid; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.None; FStar_Syntax_Syntax.residual_flags = []}
in (

let lift_from_pure_wp = (

let uu____4340 = (

let uu____4341 = (FStar_Syntax_Subst.compress return_wp)
in uu____4341.FStar_Syntax_Syntax.n)
in (match (uu____4340) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(

let uu____4399 = (

let uu____4418 = (

let uu____4423 = (FStar_Syntax_Util.abs bs body FStar_Pervasives_Native.None)
in (FStar_Syntax_Subst.open_term ((b1)::(b2)::[]) uu____4423))
in (match (uu____4418) with
| ((b11)::(b21)::[], body1) -> begin
((b11), (b21), (body1))
end
| uu____4505 -> begin
(failwith "Impossible : open_term not preserving binders arity")
end))
in (match (uu____4399) with
| (b11, b21, body1) -> begin
(

let env0 = (

let uu____4559 = (FStar_TypeChecker_DMFF.get_env dmff_env2)
in (FStar_TypeChecker_Env.push_binders uu____4559 ((b11)::(b21)::[])))
in (

let wp_b1 = (

let raw_wp_b1 = (

let uu____4582 = (

let uu____4583 = (

let uu____4600 = (

let uu____4611 = (

let uu____4620 = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst b11))
in (

let uu____4625 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____4620), (uu____4625))))
in (uu____4611)::[])
in ((wp_type), (uu____4600)))
in FStar_Syntax_Syntax.Tm_app (uu____4583))
in (mk1 uu____4582))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::[]) env0 raw_wp_b1))
in (

let uu____4661 = (

let uu____4670 = (

let uu____4671 = (FStar_Syntax_Util.unascribe wp_b1)
in (FStar_TypeChecker_Normalize.eta_expand_with_type env0 body1 uu____4671))
in (FStar_All.pipe_left FStar_Syntax_Util.abs_formals uu____4670))
in (match (uu____4661) with
| (bs1, body2, what') -> begin
(

let fail1 = (fun uu____4694 -> (

let error_msg = (

let uu____4697 = (FStar_Syntax_Print.term_to_string body2)
in (

let uu____4699 = (match (what') with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (rc) -> begin
(FStar_Ident.text_of_lid rc.FStar_Syntax_Syntax.residual_effect)
end)
in (FStar_Util.format2 "The body of return_wp (%s) should be of type Type0 but is of type %s" uu____4697 uu____4699)))
in (raise_error1 ((FStar_Errors.Fatal_WrongBodyTypeForReturnWP), (error_msg)))))
in ((match (what') with
| FStar_Pervasives_Native.None -> begin
(fail1 ())
end
| FStar_Pervasives_Native.Some (rc) -> begin
((

let uu____4709 = (

let uu____4711 = (FStar_Syntax_Util.is_pure_effect rc.FStar_Syntax_Syntax.residual_effect)
in (not (uu____4711)))
in (match (uu____4709) with
| true -> begin
(fail1 ())
end
| uu____4714 -> begin
()
end));
(

let uu____4716 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun rt -> (

let g_opt = (FStar_TypeChecker_Rel.try_teq true env1 rt FStar_Syntax_Util.ktype0)
in (match (g_opt) with
| FStar_Pervasives_Native.Some (g') -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env1 g')
end
| FStar_Pervasives_Native.None -> begin
(fail1 ())
end))))
in (FStar_All.pipe_right uu____4716 (fun a1 -> ())));
)
end);
(

let wp = (

let t2 = (FStar_Pervasives_Native.fst b21).FStar_Syntax_Syntax.sort
in (

let pure_wp_type = (FStar_TypeChecker_DMFF.double_star t2)
in (FStar_Syntax_Syntax.gen_bv "wp" FStar_Pervasives_Native.None pure_wp_type)))
in (

let body3 = (

let uu____4745 = (

let uu____4750 = (FStar_Syntax_Syntax.bv_to_name wp)
in (

let uu____4751 = (

let uu____4752 = (

let uu____4761 = (FStar_Syntax_Util.abs ((b21)::[]) body2 what')
in ((uu____4761), (FStar_Pervasives_Native.None)))
in (uu____4752)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____4750 uu____4751)))
in (uu____4745 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let uu____4796 = (

let uu____4797 = (

let uu____4806 = (FStar_Syntax_Syntax.mk_binder wp)
in (uu____4806)::[])
in (b11)::uu____4797)
in (

let uu____4831 = (FStar_Syntax_Util.abs bs1 body3 what)
in (FStar_Syntax_Util.abs uu____4796 uu____4831 (FStar_Pervasives_Native.Some (rc_gtot)))))));
))
end))))
end))
end
| uu____4834 -> begin
(raise_error1 ((FStar_Errors.Fatal_UnexpectedReturnShape), ("unexpected shape for return")))
end))
in (

let return_wp1 = (

let uu____4842 = (

let uu____4843 = (FStar_Syntax_Subst.compress return_wp)
in uu____4843.FStar_Syntax_Syntax.n)
in (match (uu____4842) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(

let uu____4901 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs ((b1)::(b2)::[]) uu____4901 (FStar_Pervasives_Native.Some (rc_gtot))))
end
| uu____4922 -> begin
(raise_error1 ((FStar_Errors.Fatal_UnexpectedReturnShape), ("unexpected shape for return")))
end))
in (

let bind_wp1 = (

let uu____4930 = (

let uu____4931 = (FStar_Syntax_Subst.compress bind_wp)
in uu____4931.FStar_Syntax_Syntax.n)
in (match (uu____4930) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let r = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.range_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let uu____4965 = (

let uu____4966 = (

let uu____4975 = (

let uu____4982 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (r)))
in (FStar_Syntax_Syntax.null_binder uu____4982))
in (uu____4975)::[])
in (FStar_List.append uu____4966 binders))
in (FStar_Syntax_Util.abs uu____4965 body what)))
end
| uu____5001 -> begin
(raise_error1 ((FStar_Errors.Fatal_UnexpectedBindShape), ("unexpected shape for bind")))
end))
in (

let apply_close = (fun t -> (match ((Prims.op_Equality (FStar_List.length effect_binders1) (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____5029 -> begin
(

let uu____5031 = (

let uu____5032 = (

let uu____5033 = (

let uu____5050 = (

let uu____5061 = (FStar_Syntax_Util.args_of_binders effect_binders1)
in (FStar_Pervasives_Native.snd uu____5061))
in ((t), (uu____5050)))
in FStar_Syntax_Syntax.Tm_app (uu____5033))
in (mk1 uu____5032))
in (FStar_Syntax_Subst.close effect_binders1 uu____5031))
end))
in (

let rec apply_last1 = (fun f l -> (match (l) with
| [] -> begin
(failwith "empty path..")
end
| (a2)::[] -> begin
(

let uu____5119 = (f a2)
in (uu____5119)::[])
end
| (x)::xs -> begin
(

let uu____5130 = (apply_last1 f xs)
in (x)::uu____5130)
end))
in (

let register = (fun name item -> (

let p = (FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname)
in (

let p' = (apply_last1 (fun s -> (Prims.op_Hat "__" (Prims.op_Hat s (Prims.op_Hat "_eff_override_" name)))) p)
in (

let l' = (FStar_Ident.lid_of_path p' FStar_Range.dummyRange)
in (

let uu____5164 = (FStar_TypeChecker_Env.try_lookup_lid env1 l')
in (match (uu____5164) with
| FStar_Pervasives_Native.Some (_us, _t) -> begin
((

let uu____5194 = (FStar_Options.debug_any ())
in (match (uu____5194) with
| true -> begin
(

let uu____5197 = (FStar_Ident.string_of_lid l')
in (FStar_Util.print1 "DM4F: Applying override %s\n" uu____5197))
end
| uu____5200 -> begin
()
end));
(

let uu____5202 = (FStar_Syntax_Syntax.lid_as_fv l' FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____5202));
)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5211 = (

let uu____5216 = (mk_lid name)
in (

let uu____5217 = (FStar_Syntax_Util.abs effect_binders1 item FStar_Pervasives_Native.None)
in (FStar_TypeChecker_Util.mk_toplevel_definition env1 uu____5216 uu____5217)))
in (match (uu____5211) with
| (sigelt, fv) -> begin
((

let uu____5221 = (

let uu____5224 = (FStar_ST.op_Bang sigelts)
in (sigelt)::uu____5224)
in (FStar_ST.op_Colon_Equals sigelts uu____5221));
fv;
)
end))
end))))))
in (

let lift_from_pure_wp1 = (register "lift_from_pure" lift_from_pure_wp)
in (

let return_wp2 = (register "return_wp" return_wp1)
in ((

let uu____5278 = (

let uu____5281 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions (FStar_Pervasives_Native.Some ("--admit_smt_queries true")))))
in (

let uu____5284 = (FStar_ST.op_Bang sigelts)
in (uu____5281)::uu____5284))
in (FStar_ST.op_Colon_Equals sigelts uu____5278));
(

let return_elab1 = (register "return_elab" return_elab)
in ((

let uu____5336 = (

let uu____5339 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions)))
in (

let uu____5340 = (FStar_ST.op_Bang sigelts)
in (uu____5339)::uu____5340))
in (FStar_ST.op_Colon_Equals sigelts uu____5336));
(

let bind_wp2 = (register "bind_wp" bind_wp1)
in ((

let uu____5392 = (

let uu____5395 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions (FStar_Pervasives_Native.Some ("--admit_smt_queries true")))))
in (

let uu____5398 = (FStar_ST.op_Bang sigelts)
in (uu____5395)::uu____5398))
in (FStar_ST.op_Colon_Equals sigelts uu____5392));
(

let bind_elab1 = (register "bind_elab" bind_elab)
in ((

let uu____5450 = (

let uu____5453 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions)))
in (

let uu____5454 = (FStar_ST.op_Bang sigelts)
in (uu____5453)::uu____5454))
in (FStar_ST.op_Colon_Equals sigelts uu____5450));
(

let uu____5503 = (FStar_List.fold_left (fun uu____5543 action -> (match (uu____5543) with
| (dmff_env3, actions) -> begin
(

let params_un = (FStar_Syntax_Subst.open_binders action.FStar_Syntax_Syntax.action_params)
in (

let uu____5564 = (

let uu____5571 = (FStar_TypeChecker_DMFF.get_env dmff_env3)
in (FStar_TypeChecker_TcTerm.tc_tparams uu____5571 params_un))
in (match (uu____5564) with
| (action_params, env', uu____5580) -> begin
(

let action_params1 = (FStar_List.map (fun uu____5606 -> (match (uu____5606) with
| (bv, qual) -> begin
(

let uu____5625 = (

let uu___615_5626 = bv
in (

let uu____5627 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.EraseUniverses)::[]) env' bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___615_5626.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___615_5626.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5627}))
in ((uu____5625), (qual)))
end)) action_params)
in (

let dmff_env' = (FStar_TypeChecker_DMFF.set_env dmff_env3 env')
in (

let uu____5633 = (elaborate_and_star dmff_env' action_params1 ((action.FStar_Syntax_Syntax.action_univs), (action.FStar_Syntax_Syntax.action_defn)))
in (match (uu____5633) with
| (dmff_env4, action_t, action_wp, action_elab) -> begin
(

let name = action.FStar_Syntax_Syntax.action_name.FStar_Ident.ident.FStar_Ident.idText
in (

let action_typ_with_wp = (FStar_TypeChecker_DMFF.trans_F dmff_env' action_t action_wp)
in (

let action_params2 = (FStar_Syntax_Subst.close_binders action_params1)
in (

let action_elab1 = (FStar_Syntax_Subst.close action_params2 action_elab)
in (

let action_typ_with_wp1 = (FStar_Syntax_Subst.close action_params2 action_typ_with_wp)
in (

let action_elab2 = (FStar_Syntax_Util.abs action_params2 action_elab1 FStar_Pervasives_Native.None)
in (

let action_typ_with_wp2 = (match (action_params2) with
| [] -> begin
action_typ_with_wp1
end
| uu____5672 -> begin
(

let uu____5673 = (FStar_Syntax_Syntax.mk_Total action_typ_with_wp1)
in (FStar_Syntax_Util.flat_arrow action_params2 uu____5673))
end)
in ((

let uu____5677 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("ED")))
in (match (uu____5677) with
| true -> begin
(

let uu____5682 = (FStar_Syntax_Print.binders_to_string "," params_un)
in (

let uu____5685 = (FStar_Syntax_Print.binders_to_string "," action_params2)
in (

let uu____5688 = (FStar_Syntax_Print.term_to_string action_typ_with_wp2)
in (

let uu____5690 = (FStar_Syntax_Print.term_to_string action_elab2)
in (FStar_Util.print4 "original action_params %s, end action_params %s, type %s, term %s\n" uu____5682 uu____5685 uu____5688 uu____5690)))))
end
| uu____5693 -> begin
()
end));
(

let action_elab3 = (register (Prims.op_Hat name "_elab") action_elab2)
in (

let action_typ_with_wp3 = (register (Prims.op_Hat name "_complete_type") action_typ_with_wp2)
in (

let uu____5699 = (

let uu____5702 = (

let uu___637_5703 = action
in (

let uu____5704 = (apply_close action_elab3)
in (

let uu____5705 = (apply_close action_typ_with_wp3)
in {FStar_Syntax_Syntax.action_name = uu___637_5703.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___637_5703.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___637_5703.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = []; FStar_Syntax_Syntax.action_defn = uu____5704; FStar_Syntax_Syntax.action_typ = uu____5705})))
in (uu____5702)::actions)
in ((dmff_env4), (uu____5699)))));
))))))))
end))))
end)))
end)) ((dmff_env2), ([])) ed.FStar_Syntax_Syntax.actions)
in (match (uu____5503) with
| (dmff_env3, actions) -> begin
(

let actions1 = (FStar_List.rev actions)
in (

let repr1 = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp_a" FStar_Pervasives_Native.None wp_a)
in (

let binders = (

let uu____5749 = (FStar_Syntax_Syntax.mk_binder a1)
in (

let uu____5756 = (

let uu____5765 = (FStar_Syntax_Syntax.mk_binder wp)
in (uu____5765)::[])
in (uu____5749)::uu____5756))
in (

let uu____5790 = (

let uu____5793 = (

let uu____5794 = (

let uu____5795 = (

let uu____5812 = (

let uu____5823 = (

let uu____5832 = (FStar_Syntax_Syntax.bv_to_name a1)
in (

let uu____5835 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____5832), (uu____5835))))
in (uu____5823)::[])
in ((repr), (uu____5812)))
in FStar_Syntax_Syntax.Tm_app (uu____5795))
in (mk1 uu____5794))
in (

let uu____5871 = (FStar_Syntax_Syntax.bv_to_name wp)
in (FStar_TypeChecker_DMFF.trans_F dmff_env3 uu____5793 uu____5871)))
in (FStar_Syntax_Util.abs binders uu____5790 FStar_Pervasives_Native.None))))
in (

let uu____5872 = (recheck_debug "FC" env1 repr1)
in (

let repr2 = (register "repr" repr1)
in (

let uu____5876 = (

let uu____5885 = (

let uu____5886 = (

let uu____5889 = (FStar_Syntax_Subst.compress wp_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____5889))
in uu____5886.FStar_Syntax_Syntax.n)
in (match (uu____5885) with
| FStar_Syntax_Syntax.Tm_abs ((type_param)::effect_param, arrow1, uu____5903) -> begin
(

let uu____5940 = (

let uu____5961 = (FStar_Syntax_Subst.open_term ((type_param)::effect_param) arrow1)
in (match (uu____5961) with
| ((b)::bs, body) -> begin
((b), (bs), (body))
end
| uu____6029 -> begin
(failwith "Impossible : open_term nt preserving binders arity")
end))
in (match (uu____5940) with
| (type_param1, effect_param1, arrow2) -> begin
(

let uu____6094 = (

let uu____6095 = (

let uu____6098 = (FStar_Syntax_Subst.compress arrow2)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____6098))
in uu____6095.FStar_Syntax_Syntax.n)
in (match (uu____6094) with
| FStar_Syntax_Syntax.Tm_arrow (wp_binders, c) -> begin
(

let uu____6131 = (FStar_Syntax_Subst.open_comp wp_binders c)
in (match (uu____6131) with
| (wp_binders1, c1) -> begin
(

let uu____6146 = (FStar_List.partition (fun uu____6177 -> (match (uu____6177) with
| (bv, uu____6186) -> begin
(

let uu____6191 = (

let uu____6193 = (FStar_Syntax_Free.names bv.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____6193 (FStar_Util.set_mem (FStar_Pervasives_Native.fst type_param1))))
in (FStar_All.pipe_right uu____6191 Prims.op_Negation))
end)) wp_binders1)
in (match (uu____6146) with
| (pre_args, post_args) -> begin
(

let post = (match (post_args) with
| (post)::[] -> begin
post
end
| [] -> begin
(

let err_msg = (

let uu____6285 = (FStar_Syntax_Print.term_to_string arrow2)
in (FStar_Util.format1 "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)" uu____6285))
in (FStar_Errors.raise_err ((FStar_Errors.Fatal_ImpossibleToGenerateDMEffect), (err_msg))))
end
| uu____6295 -> begin
(

let err_msg = (

let uu____6306 = (FStar_Syntax_Print.term_to_string arrow2)
in (FStar_Util.format1 "Impossible to generate DM effect: multiple post candidates %s" uu____6306))
in (FStar_Errors.raise_err ((FStar_Errors.Fatal_ImpossibleToGenerateDMEffect), (err_msg))))
end)
in (

let uu____6316 = (FStar_Syntax_Util.arrow pre_args c1)
in (

let uu____6319 = (FStar_Syntax_Util.abs ((type_param1)::effect_param1) (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort FStar_Pervasives_Native.None)
in ((uu____6316), (uu____6319)))))
end))
end))
end
| uu____6334 -> begin
(

let uu____6335 = (

let uu____6341 = (

let uu____6343 = (FStar_Syntax_Print.term_to_string arrow2)
in (FStar_Util.format1 "Impossible: pre/post arrow %s" uu____6343))
in ((FStar_Errors.Fatal_ImpossiblePrePostArrow), (uu____6341)))
in (raise_error1 uu____6335))
end))
end))
end
| uu____6355 -> begin
(

let uu____6356 = (

let uu____6362 = (

let uu____6364 = (FStar_Syntax_Print.term_to_string wp_type)
in (FStar_Util.format1 "Impossible: pre/post abs %s" uu____6364))
in ((FStar_Errors.Fatal_ImpossiblePrePostAbs), (uu____6362)))
in (raise_error1 uu____6356))
end))
in (match (uu____5876) with
| (pre, post) -> begin
((

let uu____6397 = (register "pre" pre)
in ());
(

let uu____6400 = (register "post" post)
in ());
(

let uu____6403 = (register "wp" wp_type)
in ());
(

let ed1 = (

let uu___693_6406 = ed
in (

let uu____6407 = (FStar_Syntax_Subst.close_binders effect_binders1)
in (

let uu____6408 = (FStar_Syntax_Subst.close effect_binders1 effect_signature)
in (

let uu____6409 = (

let uu____6410 = (apply_close return_wp2)
in (([]), (uu____6410)))
in (

let uu____6417 = (

let uu____6418 = (apply_close bind_wp2)
in (([]), (uu____6418)))
in (

let uu____6425 = (apply_close repr2)
in (

let uu____6426 = (

let uu____6427 = (apply_close return_elab1)
in (([]), (uu____6427)))
in (

let uu____6434 = (

let uu____6435 = (apply_close bind_elab1)
in (([]), (uu____6435)))
in {FStar_Syntax_Syntax.cattributes = uu___693_6406.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___693_6406.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___693_6406.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu____6407; FStar_Syntax_Syntax.signature = uu____6408; FStar_Syntax_Syntax.ret_wp = uu____6409; FStar_Syntax_Syntax.bind_wp = uu____6417; FStar_Syntax_Syntax.if_then_else = uu___693_6406.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = uu___693_6406.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = uu___693_6406.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = uu___693_6406.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = uu___693_6406.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = uu___693_6406.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = uu___693_6406.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = uu___693_6406.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = uu____6425; FStar_Syntax_Syntax.return_repr = uu____6426; FStar_Syntax_Syntax.bind_repr = uu____6434; FStar_Syntax_Syntax.actions = actions1; FStar_Syntax_Syntax.eff_attrs = uu___693_6406.FStar_Syntax_Syntax.eff_attrs}))))))))
in (

let uu____6442 = (FStar_TypeChecker_DMFF.gen_wps_for_free env1 effect_binders1 a1 wp_a ed1)
in (match (uu____6442) with
| (sigelts', ed2) -> begin
((

let uu____6460 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____6460) with
| true -> begin
(

let uu____6464 = (FStar_Syntax_Print.eff_decl_to_string true ed2)
in (FStar_Util.print_string uu____6464))
end
| uu____6467 -> begin
()
end));
(

let lift_from_pure_opt = (match ((Prims.op_Equality (FStar_List.length effect_binders1) (Prims.parse_int "0"))) with
| true -> begin
(

let lift_from_pure = (

let uu____6484 = (

let uu____6487 = (

let uu____6488 = (apply_close lift_from_pure_wp1)
in (([]), (uu____6488)))
in FStar_Pervasives_Native.Some (uu____6487))
in {FStar_Syntax_Syntax.source = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.target = ed2.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.lift_wp = uu____6484; FStar_Syntax_Syntax.lift = FStar_Pervasives_Native.None})
in (

let uu____6495 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_sub_effect (lift_from_pure)))
in FStar_Pervasives_Native.Some (uu____6495)))
end
| uu____6496 -> begin
FStar_Pervasives_Native.None
end)
in (

let uu____6498 = (

let uu____6501 = (

let uu____6504 = (FStar_ST.op_Bang sigelts)
in (FStar_List.rev uu____6504))
in (FStar_List.append uu____6501 sigelts'))
in ((uu____6498), (ed2), (lift_from_pure_opt))));
)
end)));
)
end))))))
end));
));
));
));
))))))))))
end))
end)))))))))));
)
end)))))
end))))
end))
end))
end)))


let tc_lex_t : 'Auu____6545 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  'Auu____6545 Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (

let err_range = (

let uu____6580 = (FStar_List.hd ses)
in uu____6580.FStar_Syntax_Syntax.sigrng)
in ((match (lids) with
| (lex_t1)::(lex_top1)::(lex_cons)::[] when (((FStar_Ident.lid_equals lex_t1 FStar_Parser_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top1 FStar_Parser_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Parser_Const.lexcons_lid)) -> begin
()
end
| uu____6585 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_InvalidRedefinitionOfLexT), ("Invalid (partial) redefinition of lex_t")) err_range)
end);
(match (ses) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (lex_t1, uu____6591, [], t, uu____6593, uu____6594); FStar_Syntax_Syntax.sigrng = r; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = uu____6596; FStar_Syntax_Syntax.sigattrs = uu____6597})::({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (lex_top1, uu____6599, _t_top, _lex_t_top, _6633, uu____6602); FStar_Syntax_Syntax.sigrng = r1; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = uu____6604; FStar_Syntax_Syntax.sigattrs = uu____6605})::({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (lex_cons, uu____6607, _t_cons, _lex_t_cons, _6641, uu____6610); FStar_Syntax_Syntax.sigrng = r2; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = uu____6612; FStar_Syntax_Syntax.sigattrs = uu____6613})::[] when (((_6633 = (Prims.parse_int "0")) && (_6641 = (Prims.parse_int "0"))) && (((FStar_Ident.lid_equals lex_t1 FStar_Parser_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top1 FStar_Parser_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Parser_Const.lexcons_lid))) -> begin
(

let u = (FStar_Syntax_Syntax.new_univ_name (FStar_Pervasives_Native.Some (r)))
in (

let t1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) FStar_Pervasives_Native.None r)
in (

let t2 = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t1)
in (

let tc = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((lex_t1), ((u)::[]), ([]), (t2), ([]), ((FStar_Parser_Const.lextop_lid)::(FStar_Parser_Const.lexcons_lid)::[]))); FStar_Syntax_Syntax.sigrng = r; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (

let utop = (FStar_Syntax_Syntax.new_univ_name (FStar_Pervasives_Native.Some (r1)))
in (

let lex_top_t = (

let uu____6666 = (

let uu____6673 = (

let uu____6674 = (

let uu____6681 = (

let uu____6684 = (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar uu____6684 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None))
in ((uu____6681), ((FStar_Syntax_Syntax.U_name (utop))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____6674))
in (FStar_Syntax_Syntax.mk uu____6673))
in (uu____6666 FStar_Pervasives_Native.None r1))
in (

let lex_top_t1 = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (

let dc_lextop = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((lex_top1), ((utop)::[]), (lex_top_t1), (FStar_Parser_Const.lex_t_lid), ((Prims.parse_int "0")), ([]))); FStar_Syntax_Syntax.sigrng = r1; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (

let ucons1 = (FStar_Syntax_Syntax.new_univ_name (FStar_Pervasives_Native.Some (r2)))
in (

let ucons2 = (FStar_Syntax_Syntax.new_univ_name (FStar_Pervasives_Native.Some (r2)))
in (

let lex_cons_t = (

let a = (

let uu____6699 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) FStar_Pervasives_Native.None r2)
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (r2)) uu____6699))
in (

let hd1 = (

let uu____6701 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (r2)) uu____6701))
in (

let tl1 = (

let uu____6703 = (

let uu____6704 = (

let uu____6711 = (

let uu____6712 = (

let uu____6719 = (

let uu____6722 = (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar uu____6722 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None))
in ((uu____6719), ((FStar_Syntax_Syntax.U_name (ucons2))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____6712))
in (FStar_Syntax_Syntax.mk uu____6711))
in (uu____6704 FStar_Pervasives_Native.None r2))
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (r2)) uu____6703))
in (

let res = (

let uu____6728 = (

let uu____6735 = (

let uu____6736 = (

let uu____6743 = (

let uu____6746 = (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar uu____6746 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None))
in ((uu____6743), ((FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____6736))
in (FStar_Syntax_Syntax.mk uu____6735))
in (uu____6728 FStar_Pervasives_Native.None r2))
in (

let uu____6749 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow ((((a), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::(((hd1), (FStar_Pervasives_Native.None)))::(((tl1), (FStar_Pervasives_Native.None)))::[]) uu____6749))))))
in (

let lex_cons_t1 = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((lex_cons), ((ucons1)::(ucons2)::[]), (lex_cons_t1), (FStar_Parser_Const.lex_t_lid), ((Prims.parse_int "0")), ([]))); FStar_Syntax_Syntax.sigrng = r2; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (

let uu____6788 = (FStar_TypeChecker_Env.get_range env)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle ((((tc)::(dc_lextop)::(dc_lexcons)::[]), (lids))); FStar_Syntax_Syntax.sigrng = uu____6788; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))))))))))))))
end
| uu____6793 -> begin
(

let err_msg = (

let uu____6798 = (

let uu____6800 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_bundle (((ses), (lids)))))
in (FStar_Syntax_Print.sigelt_to_string uu____6800))
in (FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n" uu____6798))
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_InvalidRedefinitionOfLexT), (err_msg)) err_range))
end);
)))


let tc_type_common : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.typ  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.tscheme = (fun env uu____6825 expected_typ1 r -> (match (uu____6825) with
| (uvs, t) -> begin
(

let uu____6838 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____6838) with
| (uvs1, t1) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env uvs1)
in (

let t2 = (tc_check_trivial_guard env1 t1 expected_typ1)
in (match ((Prims.op_Equality uvs1 [])) with
| true -> begin
(

let uu____6850 = (FStar_TypeChecker_Util.generalize_universes env1 t2)
in (match (uu____6850) with
| (uvs2, t3) -> begin
((FStar_TypeChecker_Util.check_uvars r t3);
((uvs2), (t3));
)
end))
end
| uu____6866 -> begin
(

let uu____6868 = (

let uu____6871 = (FStar_All.pipe_right t2 (FStar_TypeChecker_Normalize.remove_uvar_solutions env1))
in (FStar_All.pipe_right uu____6871 (FStar_Syntax_Subst.close_univ_vars uvs1)))
in ((uvs1), (uu____6868)))
end)))
end))
end))


let tc_declare_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.tscheme = (fun env ts r -> (

let uu____6894 = (

let uu____6895 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____6895 FStar_Pervasives_Native.fst))
in (tc_type_common env ts uu____6894 r)))


let tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.tscheme = (fun env ts r -> (

let uu____6920 = (

let uu____6921 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____6921 FStar_Pervasives_Native.fst))
in (tc_type_common env ts uu____6920 r)))


let tc_inductive' : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env ses quals lids -> ((

let uu____6970 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____6970) with
| true -> begin
(

let uu____6973 = (FStar_Common.string_of_list FStar_Syntax_Print.sigelt_to_string ses)
in (FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____6973))
end
| uu____6976 -> begin
()
end));
(

let uu____6978 = (FStar_TypeChecker_TcInductive.check_inductive_well_typedness env ses quals lids)
in (match (uu____6978) with
| (sig_bndle, tcs, datas) -> begin
(

let data_ops_ses = (

let uu____7009 = (FStar_List.map (FStar_TypeChecker_TcInductive.mk_data_operations quals env tcs) datas)
in (FStar_All.pipe_right uu____7009 FStar_List.flatten))
in ((

let uu____7023 = ((FStar_Options.no_positivity ()) || (

let uu____7026 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____7026))))
in (match (uu____7023) with
| true -> begin
()
end
| uu____7029 -> begin
(

let env1 = (FStar_TypeChecker_Env.push_sigelt env sig_bndle)
in ((FStar_List.iter (fun ty -> (

let b = (FStar_TypeChecker_TcInductive.check_positivity ty env1)
in (match ((not (b))) with
| true -> begin
(

let uu____7042 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____7052, uu____7053, uu____7054, uu____7055, uu____7056) -> begin
((lid), (ty.FStar_Syntax_Syntax.sigrng))
end
| uu____7065 -> begin
(failwith "Impossible!")
end)
in (match (uu____7042) with
| (lid, r) -> begin
(FStar_Errors.log_issue r ((FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition), ((Prims.op_Hat "Inductive type " (Prims.op_Hat lid.FStar_Ident.str " does not satisfy the positivity condition")))))
end))
end
| uu____7076 -> begin
()
end))) tcs);
(FStar_List.iter (fun d -> (

let uu____7084 = (match (d.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (data_lid, uu____7094, uu____7095, ty_lid, uu____7097, uu____7098) -> begin
((data_lid), (ty_lid))
end
| uu____7105 -> begin
(failwith "Impossible")
end)
in (match (uu____7084) with
| (data_lid, ty_lid) -> begin
(

let uu____7113 = ((FStar_Ident.lid_equals ty_lid FStar_Parser_Const.exn_lid) && (

let uu____7116 = (FStar_TypeChecker_TcInductive.check_exn_positivity data_lid env1)
in (not (uu____7116))))
in (match (uu____7113) with
| true -> begin
(FStar_Errors.log_issue d.FStar_Syntax_Syntax.sigrng ((FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition), ((Prims.op_Hat "Exception " (Prims.op_Hat data_lid.FStar_Ident.str " does not satisfy the positivity condition")))))
end
| uu____7122 -> begin
()
end))
end))) datas);
))
end));
(

let skip_prims_type = (fun uu____7130 -> (

let lid = (

let ty = (FStar_List.hd tcs)
in (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____7135, uu____7136, uu____7137, uu____7138, uu____7139) -> begin
lid
end
| uu____7148 -> begin
(failwith "Impossible")
end))
in (FStar_List.existsb (fun s -> (Prims.op_Equality s lid.FStar_Ident.ident.FStar_Ident.idText)) FStar_TypeChecker_TcInductive.early_prims_inductives)))
in (

let is_noeq = (FStar_List.existsb (fun q -> (Prims.op_Equality q FStar_Syntax_Syntax.Noeq)) quals)
in (

let res = (

let uu____7166 = (((Prims.op_Equality (FStar_List.length tcs) (Prims.parse_int "0")) || ((FStar_Ident.lid_equals env.FStar_TypeChecker_Env.curmodule FStar_Parser_Const.prims_lid) && (skip_prims_type ()))) || is_noeq)
in (match (uu____7166) with
| true -> begin
((sig_bndle), (data_ops_ses))
end
| uu____7179 -> begin
(

let is_unopteq = (FStar_List.existsb (fun q -> (Prims.op_Equality q FStar_Syntax_Syntax.Unopteq)) quals)
in (

let ses1 = (match (is_unopteq) with
| true -> begin
(FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme sig_bndle tcs datas env)
end
| uu____7191 -> begin
(FStar_TypeChecker_TcInductive.optimized_haseq_scheme sig_bndle tcs datas env)
end)
in ((sig_bndle), ((FStar_List.append ses1 data_ops_ses)))))
end))
in res)));
))
end));
))


let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env ses quals lids -> (

let env1 = (FStar_TypeChecker_Env.push env "tc_inductive")
in (

let pop1 = (fun uu____7241 -> (

let uu____7242 = (FStar_TypeChecker_Env.pop env1 "tc_inductive")
in ()))
in (FStar_All.try_with (fun uu___871_7252 -> (match (()) with
| () -> begin
(

let uu____7259 = (tc_inductive' env1 ses quals lids)
in (FStar_All.pipe_right uu____7259 (fun r -> ((pop1 ());
r;
))))
end)) (fun uu___870_7290 -> ((pop1 ());
(FStar_Exn.raise uu___870_7290);
))))))


let z3_reset_options : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun en -> (

let env = (

let uu____7311 = (FStar_Options.using_facts_from ())
in (FStar_TypeChecker_Env.set_proof_ns uu____7311 en))
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
env;
)))


let get_fail_se : FStar_Syntax_Syntax.sigelt  ->  (Prims.int Prims.list * Prims.bool) FStar_Pervasives_Native.option = (fun se -> (

let comb = (fun f1 f2 -> (match (((f1), (f2))) with
| (FStar_Pervasives_Native.Some (e1, l1), FStar_Pervasives_Native.Some (e2, l2)) -> begin
FStar_Pervasives_Native.Some ((((FStar_List.append e1 e2)), ((l1 || l2))))
end
| (FStar_Pervasives_Native.Some (e, l), FStar_Pervasives_Native.None) -> begin
FStar_Pervasives_Native.Some (((e), (l)))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (e, l)) -> begin
FStar_Pervasives_Native.Some (((e), (l)))
end
| uu____7615 -> begin
FStar_Pervasives_Native.None
end))
in (FStar_List.fold_right (fun at acc -> (

let uu____7673 = (FStar_ToSyntax_ToSyntax.get_fail_attr true at)
in (comb uu____7673 acc))) se.FStar_Syntax_Syntax.sigattrs FStar_Pervasives_Native.None)))


let list_of_option : 'Auu____7698 . 'Auu____7698 FStar_Pervasives_Native.option  ->  'Auu____7698 Prims.list = (fun uu___0_7707 -> (match (uu___0_7707) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (x) -> begin
(x)::[]
end))


let check_multi_eq : Prims.int Prims.list  ->  Prims.int Prims.list  ->  (Prims.int * Prims.int * Prims.int) FStar_Pervasives_Native.option = (fun l1 l2 -> (

let rec collect1 = (fun l -> (match (l) with
| [] -> begin
[]
end
| (hd1)::tl1 -> begin
(

let uu____7787 = (collect1 tl1)
in (match (uu____7787) with
| [] -> begin
(((hd1), ((Prims.parse_int "1"))))::[]
end
| ((h, n1))::t -> begin
(match ((Prims.op_Equality h hd1)) with
| true -> begin
(((h), ((n1 + (Prims.parse_int "1")))))::t
end
| uu____7851 -> begin
(((hd1), ((Prims.parse_int "1"))))::(((h), (n1)))::t
end)
end))
end))
in (

let summ = (fun l -> (collect1 l))
in (

let l11 = (summ l1)
in (

let l21 = (summ l2)
in (

let rec aux = (fun l12 l22 -> (match (((l12), (l22))) with
| ([], []) -> begin
FStar_Pervasives_Native.None
end
| (((e, n1))::uu____8025, []) -> begin
FStar_Pervasives_Native.Some (((e), (n1), ((Prims.parse_int "0"))))
end
| ([], ((e, n1))::uu____8081) -> begin
FStar_Pervasives_Native.Some (((e), ((Prims.parse_int "0")), (n1)))
end
| (((hd1, n1))::tl1, ((hd2, n2))::tl2) when (Prims.op_disEquality hd1 hd2) -> begin
(match ((hd1 < hd2)) with
| true -> begin
FStar_Pervasives_Native.Some (((hd1), (n1), ((Prims.parse_int "0"))))
end
| uu____8219 -> begin
(match ((hd1 > hd2)) with
| true -> begin
FStar_Pervasives_Native.Some (((hd2), ((Prims.parse_int "0")), (n2)))
end
| uu____8246 -> begin
(match ((Prims.op_disEquality n1 n2)) with
| true -> begin
FStar_Pervasives_Native.Some (((hd1), (n1), (n2)))
end
| uu____8273 -> begin
(aux tl1 tl2)
end)
end)
end)
end))
in (aux l11 l21)))))))


let check_must_erase_attribute : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  unit = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let (lbs, l) -> begin
(

let uu____8292 = (

let uu____8294 = (FStar_Options.ide ())
in (not (uu____8294)))
in (match (uu____8292) with
| true -> begin
(

let uu____8297 = (

let uu____8302 = (FStar_TypeChecker_Env.dsenv env)
in (

let uu____8303 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Syntax_DsEnv.iface_decls uu____8302 uu____8303)))
in (match (uu____8297) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (iface_decls1) -> begin
(FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.iter (fun lb -> (

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let has_iface_val = (FStar_All.pipe_right iface_decls1 (FStar_Util.for_some (FStar_Parser_AST.decl_is_val lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.ident)))
in (match (has_iface_val) with
| true -> begin
(

let must_erase = (FStar_TypeChecker_Util.must_erase_for_extraction env lb.FStar_Syntax_Syntax.lbdef)
in (

let has_attr = (FStar_TypeChecker_Env.fv_has_attr env lbname FStar_Parser_Const.must_erase_for_extraction_attr)
in (match ((must_erase && (not (has_attr)))) with
| true -> begin
(

let uu____8336 = (FStar_Syntax_Syntax.range_of_fv lbname)
in (

let uu____8337 = (

let uu____8343 = (

let uu____8345 = (FStar_Syntax_Print.fv_to_string lbname)
in (

let uu____8347 = (FStar_Syntax_Print.fv_to_string lbname)
in (FStar_Util.format2 "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface" uu____8345 uu____8347)))
in ((FStar_Errors.Error_MustEraseMissing), (uu____8343)))
in (FStar_Errors.log_issue uu____8336 uu____8337)))
end
| uu____8351 -> begin
(match ((has_attr && (not (must_erase)))) with
| true -> begin
(

let uu____8354 = (FStar_Syntax_Syntax.range_of_fv lbname)
in (

let uu____8355 = (

let uu____8361 = (

let uu____8363 = (FStar_Syntax_Print.fv_to_string lbname)
in (FStar_Util.format1 "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute." uu____8363))
in ((FStar_Errors.Error_MustEraseMissing), (uu____8361)))
in (FStar_Errors.log_issue uu____8354 uu____8355)))
end
| uu____8367 -> begin
()
end)
end)))
end
| uu____8369 -> begin
()
end))))))
end))
end
| uu____8371 -> begin
()
end))
end
| uu____8373 -> begin
()
end))


let tc_decl' : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env0 se -> (

let env = env0
in ((FStar_TypeChecker_Util.check_sigelt_quals env se);
(

let r = se.FStar_Syntax_Syntax.sigrng
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____8418) -> begin
(failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____8446) -> begin
(failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, lids) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Parser_Const.lex_t_lid))) -> begin
(

let env1 = (FStar_TypeChecker_Env.set_range env r)
in (

let se1 = (tc_lex_t env1 ses se.FStar_Syntax_Syntax.sigquals lids)
in (((se1)::[]), ([]), (env0))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, lids) -> begin
(

let env1 = (FStar_TypeChecker_Env.set_range env r)
in (

let ses1 = (

let uu____8506 = ((FStar_Options.use_two_phase_tc ()) && (FStar_TypeChecker_Env.should_verify env1))
in (match (uu____8506) with
| true -> begin
(

let ses1 = (

let uu____8514 = (

let uu____8515 = (

let uu____8516 = (tc_inductive (

let uu___1006_8525 = env1
in {FStar_TypeChecker_Env.solver = uu___1006_8525.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___1006_8525.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___1006_8525.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___1006_8525.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___1006_8525.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___1006_8525.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___1006_8525.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___1006_8525.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___1006_8525.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___1006_8525.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___1006_8525.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___1006_8525.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___1006_8525.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___1006_8525.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___1006_8525.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___1006_8525.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___1006_8525.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___1006_8525.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___1006_8525.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___1006_8525.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___1006_8525.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = true; FStar_TypeChecker_Env.failhard = uu___1006_8525.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___1006_8525.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___1006_8525.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___1006_8525.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___1006_8525.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___1006_8525.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___1006_8525.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___1006_8525.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___1006_8525.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___1006_8525.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___1006_8525.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___1006_8525.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___1006_8525.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___1006_8525.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___1006_8525.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___1006_8525.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___1006_8525.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___1006_8525.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___1006_8525.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___1006_8525.FStar_TypeChecker_Env.nbe}) ses se.FStar_Syntax_Syntax.sigquals lids)
in (FStar_All.pipe_right uu____8516 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____8515 (FStar_TypeChecker_Normalize.elim_uvars env1)))
in (FStar_All.pipe_right uu____8514 FStar_Syntax_Util.ses_of_sigbundle))
in ((

let uu____8539 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("TwoPhases")))
in (match (uu____8539) with
| true -> begin
(

let uu____8544 = (FStar_Syntax_Print.sigelt_to_string (

let uu___1010_8548 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (((ses1), (lids))); FStar_Syntax_Syntax.sigrng = uu___1010_8548.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___1010_8548.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___1010_8548.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___1010_8548.FStar_Syntax_Syntax.sigattrs}))
in (FStar_Util.print1 "Inductive after phase 1: %s\n" uu____8544))
end
| uu____8554 -> begin
()
end));
ses1;
))
end
| uu____8556 -> begin
ses
end))
in (

let uu____8558 = (tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids)
in (match (uu____8558) with
| (sigbndle, projectors_ses) -> begin
(

let sigbndle1 = (

let uu___1017_8582 = sigbndle
in {FStar_Syntax_Syntax.sigel = uu___1017_8582.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___1017_8582.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___1017_8582.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___1017_8582.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = se.FStar_Syntax_Syntax.sigattrs})
in (((sigbndle1)::[]), (projectors_ses), (env0)))
end))))
end
| FStar_Syntax_Syntax.Sig_pragma (p) -> begin
((FStar_Syntax_Util.process_pragma p r);
(((se)::[]), ([]), (env0));
)
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne) -> begin
(

let uu____8594 = (cps_and_elaborate env ne)
in (match (uu____8594) with
| (ses, ne1, lift_from_pure_opt) -> begin
(

let effect_and_lift_ses = (match (lift_from_pure_opt) with
| FStar_Pervasives_Native.Some (lift) -> begin
((

let uu___1031_8633 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne1); FStar_Syntax_Syntax.sigrng = uu___1031_8633.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___1031_8633.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___1031_8633.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___1031_8633.FStar_Syntax_Syntax.sigattrs}))::(lift)::[]
end
| FStar_Pervasives_Native.None -> begin
((

let uu___1034_8635 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne1); FStar_Syntax_Syntax.sigrng = uu___1034_8635.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___1034_8635.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___1034_8635.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___1034_8635.FStar_Syntax_Syntax.sigattrs}))::[]
end)
in (([]), ((FStar_List.append ses effect_and_lift_ses)), (env0)))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let ne1 = (

let uu____8642 = ((FStar_Options.use_two_phase_tc ()) && (FStar_TypeChecker_Env.should_verify env))
in (match (uu____8642) with
| true -> begin
(

let ne1 = (

let uu____8646 = (

let uu____8647 = (

let uu____8648 = (tc_eff_decl (

let uu___1040_8651 = env
in {FStar_TypeChecker_Env.solver = uu___1040_8651.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___1040_8651.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___1040_8651.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___1040_8651.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___1040_8651.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___1040_8651.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___1040_8651.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___1040_8651.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___1040_8651.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___1040_8651.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___1040_8651.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___1040_8651.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___1040_8651.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___1040_8651.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___1040_8651.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___1040_8651.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___1040_8651.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___1040_8651.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___1040_8651.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___1040_8651.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___1040_8651.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = true; FStar_TypeChecker_Env.failhard = uu___1040_8651.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___1040_8651.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___1040_8651.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___1040_8651.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___1040_8651.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___1040_8651.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___1040_8651.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___1040_8651.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___1040_8651.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___1040_8651.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___1040_8651.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___1040_8651.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___1040_8651.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___1040_8651.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___1040_8651.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___1040_8651.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___1040_8651.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___1040_8651.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___1040_8651.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___1040_8651.FStar_TypeChecker_Env.nbe}) ne)
in (FStar_All.pipe_right uu____8648 (fun ne1 -> (

let uu___1043_8657 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne1); FStar_Syntax_Syntax.sigrng = uu___1043_8657.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___1043_8657.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___1043_8657.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___1043_8657.FStar_Syntax_Syntax.sigattrs}))))
in (FStar_All.pipe_right uu____8647 (FStar_TypeChecker_Normalize.elim_uvars env)))
in (FStar_All.pipe_right uu____8646 FStar_Syntax_Util.eff_decl_of_new_effect))
in ((

let uu____8659 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("TwoPhases")))
in (match (uu____8659) with
| true -> begin
(

let uu____8664 = (FStar_Syntax_Print.sigelt_to_string (

let uu___1047_8668 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne1); FStar_Syntax_Syntax.sigrng = uu___1047_8668.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___1047_8668.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___1047_8668.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___1047_8668.FStar_Syntax_Syntax.sigattrs}))
in (FStar_Util.print1 "Effect decl after phase 1: %s\n" uu____8664))
end
| uu____8670 -> begin
()
end));
ne1;
))
end
| uu____8672 -> begin
ne
end))
in (

let ne2 = (tc_eff_decl env ne1)
in (

let se1 = (

let uu___1052_8676 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne2); FStar_Syntax_Syntax.sigrng = uu___1052_8676.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___1052_8676.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___1052_8676.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___1052_8676.FStar_Syntax_Syntax.sigattrs})
in (((se1)::[]), ([]), (env0)))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub1) -> begin
(

let ed_src = (FStar_TypeChecker_Env.get_effect_decl env sub1.FStar_Syntax_Syntax.source)
in (

let ed_tgt = (FStar_TypeChecker_Env.get_effect_decl env sub1.FStar_Syntax_Syntax.target)
in (

let uu____8684 = (

let uu____8691 = (FStar_TypeChecker_Env.lookup_effect_lid env sub1.FStar_Syntax_Syntax.source)
in (monad_signature env sub1.FStar_Syntax_Syntax.source uu____8691))
in (match (uu____8684) with
| (a, wp_a_src) -> begin
(

let uu____8708 = (

let uu____8715 = (FStar_TypeChecker_Env.lookup_effect_lid env sub1.FStar_Syntax_Syntax.target)
in (monad_signature env sub1.FStar_Syntax_Syntax.target uu____8715))
in (match (uu____8708) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (

let uu____8733 = (

let uu____8736 = (

let uu____8737 = (

let uu____8744 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (uu____8744)))
in FStar_Syntax_Syntax.NT (uu____8737))
in (uu____8736)::[])
in (FStar_Syntax_Subst.subst uu____8733 wp_b_tgt))
in (

let expected_k = (

let uu____8752 = (

let uu____8761 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____8768 = (

let uu____8777 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (uu____8777)::[])
in (uu____8761)::uu____8768))
in (

let uu____8802 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow uu____8752 uu____8802)))
in (

let repr_type = (fun eff_name a1 wp -> ((

let uu____8824 = (

let uu____8826 = (FStar_TypeChecker_Env.is_reifiable_effect env eff_name)
in (not (uu____8826)))
in (match (uu____8824) with
| true -> begin
(

let uu____8829 = (

let uu____8835 = (FStar_Util.format1 "Effect %s cannot be reified" eff_name.FStar_Ident.str)
in ((FStar_Errors.Fatal_EffectCannotBeReified), (uu____8835)))
in (

let uu____8839 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____8829 uu____8839)))
end
| uu____8840 -> begin
()
end));
(

let uu____8842 = (FStar_TypeChecker_Env.effect_decl_opt env eff_name)
in (match (uu____8842) with
| FStar_Pervasives_Native.None -> begin
(failwith "internal error: reifiable effect has no decl?")
end
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((FStar_Syntax_Syntax.U_unknown)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let uu____8879 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____8880 = (

let uu____8887 = (

let uu____8888 = (

let uu____8905 = (

let uu____8916 = (FStar_Syntax_Syntax.as_arg a1)
in (

let uu____8925 = (

let uu____8936 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____8936)::[])
in (uu____8916)::uu____8925))
in ((repr), (uu____8905)))
in FStar_Syntax_Syntax.Tm_app (uu____8888))
in (FStar_Syntax_Syntax.mk uu____8887))
in (uu____8880 FStar_Pervasives_Native.None uu____8879))))
end));
))
in (

let uu____8981 = (match (((sub1.FStar_Syntax_Syntax.lift), (sub1.FStar_Syntax_Syntax.lift_wp))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(failwith "Impossible (parser)")
end
| (lift, FStar_Pervasives_Native.Some (uvs, lift_wp)) -> begin
(

let uu____9154 = (match (((FStar_List.length uvs) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____9165 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____9165) with
| (usubst, uvs1) -> begin
(

let uu____9188 = (FStar_TypeChecker_Env.push_univ_vars env uvs1)
in (

let uu____9189 = (FStar_Syntax_Subst.subst usubst lift_wp)
in ((uu____9188), (uu____9189))))
end))
end
| uu____9190 -> begin
((env), (lift_wp))
end)
in (match (uu____9154) with
| (env1, lift_wp1) -> begin
(

let lift_wp2 = (match ((Prims.op_Equality (FStar_List.length uvs) (Prims.parse_int "0"))) with
| true -> begin
(check_and_gen env1 lift_wp1 expected_k)
end
| uu____9236 -> begin
(

let lift_wp2 = (tc_check_trivial_guard env1 lift_wp1 expected_k)
in (

let uu____9239 = (FStar_Syntax_Subst.close_univ_vars uvs lift_wp2)
in ((uvs), (uu____9239))))
end)
in ((lift), (lift_wp2)))
end))
end
| (FStar_Pervasives_Native.Some (what, lift), FStar_Pervasives_Native.None) -> begin
(

let uu____9310 = (match (((FStar_List.length what) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____9325 = (FStar_Syntax_Subst.univ_var_opening what)
in (match (uu____9325) with
| (usubst, uvs) -> begin
(

let uu____9350 = (FStar_Syntax_Subst.subst usubst lift)
in ((uvs), (uu____9350)))
end))
end
| uu____9353 -> begin
(([]), (lift))
end)
in (match (uu____9310) with
| (uvs, lift1) -> begin
((

let uu____9386 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____9386) with
| true -> begin
(

let uu____9390 = (FStar_Syntax_Print.term_to_string lift1)
in (FStar_Util.print1 "Lift for free : %s\n" uu____9390))
end
| uu____9393 -> begin
()
end));
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env (FStar_TypeChecker_TcTerm.tc_constant env FStar_Range.dummyRange))
in (

let uu____9396 = (

let uu____9403 = (FStar_TypeChecker_Env.push_univ_vars env uvs)
in (FStar_TypeChecker_TcTerm.tc_term uu____9403 lift1))
in (match (uu____9396) with
| (lift2, comp, uu____9428) -> begin
(

let uu____9429 = (FStar_TypeChecker_DMFF.star_expr dmff_env lift2)
in (match (uu____9429) with
| (uu____9458, lift_wp, lift_elab) -> begin
(

let lift_wp1 = (recheck_debug "lift-wp" env lift_wp)
in (

let lift_elab1 = (recheck_debug "lift-elab" env lift_elab)
in (match ((Prims.op_Equality (FStar_List.length uvs) (Prims.parse_int "0"))) with
| true -> begin
(

let uu____9490 = (

let uu____9501 = (FStar_TypeChecker_Util.generalize_universes env lift_elab1)
in FStar_Pervasives_Native.Some (uu____9501))
in (

let uu____9518 = (FStar_TypeChecker_Util.generalize_universes env lift_wp1)
in ((uu____9490), (uu____9518))))
end
| uu____9545 -> begin
(

let uu____9547 = (

let uu____9558 = (

let uu____9567 = (FStar_Syntax_Subst.close_univ_vars uvs lift_elab1)
in ((uvs), (uu____9567)))
in FStar_Pervasives_Native.Some (uu____9558))
in (

let uu____9582 = (

let uu____9591 = (FStar_Syntax_Subst.close_univ_vars uvs lift_wp1)
in ((uvs), (uu____9591)))
in ((uu____9547), (uu____9582))))
end)))
end))
end)));
)
end))
end)
in (match (uu____8981) with
| (lift, lift_wp) -> begin
(

let env1 = (

let uu___1128_9665 = env
in {FStar_TypeChecker_Env.solver = uu___1128_9665.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___1128_9665.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___1128_9665.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___1128_9665.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___1128_9665.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___1128_9665.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___1128_9665.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___1128_9665.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___1128_9665.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___1128_9665.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___1128_9665.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___1128_9665.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___1128_9665.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___1128_9665.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___1128_9665.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___1128_9665.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___1128_9665.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___1128_9665.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___1128_9665.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___1128_9665.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___1128_9665.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___1128_9665.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___1128_9665.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___1128_9665.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___1128_9665.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___1128_9665.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___1128_9665.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___1128_9665.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___1128_9665.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___1128_9665.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___1128_9665.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___1128_9665.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___1128_9665.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___1128_9665.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___1128_9665.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___1128_9665.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___1128_9665.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___1128_9665.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___1128_9665.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___1128_9665.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___1128_9665.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___1128_9665.FStar_TypeChecker_Env.nbe})
in (

let lift1 = (match (lift) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (uvs, lift1) -> begin
(

let uu____9722 = (

let uu____9727 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____9727) with
| (usubst, uvs1) -> begin
(

let uu____9750 = (FStar_TypeChecker_Env.push_univ_vars env1 uvs1)
in (

let uu____9751 = (FStar_Syntax_Subst.subst usubst lift1)
in ((uu____9750), (uu____9751))))
end))
in (match (uu____9722) with
| (env2, lift2) -> begin
(

let uu____9764 = (

let uu____9771 = (FStar_TypeChecker_Env.lookup_effect_lid env2 sub1.FStar_Syntax_Syntax.source)
in (monad_signature env2 sub1.FStar_Syntax_Syntax.source uu____9771))
in (match (uu____9764) with
| (a1, wp_a_src1) -> begin
(

let wp_a = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None wp_a_src1)
in (

let a_typ = (FStar_Syntax_Syntax.bv_to_name a1)
in (

let wp_a_typ = (FStar_Syntax_Syntax.bv_to_name wp_a)
in (

let repr_f = (repr_type sub1.FStar_Syntax_Syntax.source a_typ wp_a_typ)
in (

let repr_result = (

let lift_wp1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) env2 (FStar_Pervasives_Native.snd lift_wp))
in (

let lift_wp_a = (

let uu____9805 = (FStar_TypeChecker_Env.get_range env2)
in (

let uu____9806 = (

let uu____9813 = (

let uu____9814 = (

let uu____9831 = (

let uu____9842 = (FStar_Syntax_Syntax.as_arg a_typ)
in (

let uu____9851 = (

let uu____9862 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (uu____9862)::[])
in (uu____9842)::uu____9851))
in ((lift_wp1), (uu____9831)))
in FStar_Syntax_Syntax.Tm_app (uu____9814))
in (FStar_Syntax_Syntax.mk uu____9813))
in (uu____9806 FStar_Pervasives_Native.None uu____9805)))
in (repr_type sub1.FStar_Syntax_Syntax.target a_typ lift_wp_a)))
in (

let expected_k1 = (

let uu____9910 = (

let uu____9919 = (FStar_Syntax_Syntax.mk_binder a1)
in (

let uu____9926 = (

let uu____9935 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (

let uu____9942 = (

let uu____9951 = (FStar_Syntax_Syntax.null_binder repr_f)
in (uu____9951)::[])
in (uu____9935)::uu____9942))
in (uu____9919)::uu____9926))
in (

let uu____9982 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow uu____9910 uu____9982)))
in (

let uu____9985 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env2 expected_k1)
in (match (uu____9985) with
| (expected_k2, uu____10003, uu____10004) -> begin
(

let lift3 = (match ((Prims.op_Equality (FStar_List.length uvs) (Prims.parse_int "0"))) with
| true -> begin
(check_and_gen env2 lift2 expected_k2)
end
| uu____10025 -> begin
(

let lift3 = (tc_check_trivial_guard env2 lift2 expected_k2)
in (

let uu____10028 = (FStar_Syntax_Subst.close_univ_vars uvs lift3)
in ((uvs), (uu____10028))))
end)
in FStar_Pervasives_Native.Some (lift3))
end))))))))
end))
end))
end)
in ((

let uu____10044 = (

let uu____10046 = (

let uu____10048 = (FStar_All.pipe_right lift_wp FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____10048 FStar_List.length))
in (Prims.op_disEquality uu____10046 (Prims.parse_int "1")))
in (match (uu____10044) with
| true -> begin
(

let uu____10071 = (

let uu____10077 = (

let uu____10079 = (FStar_Syntax_Print.lid_to_string sub1.FStar_Syntax_Syntax.source)
in (

let uu____10081 = (FStar_Syntax_Print.lid_to_string sub1.FStar_Syntax_Syntax.target)
in (

let uu____10083 = (

let uu____10085 = (

let uu____10087 = (FStar_All.pipe_right lift_wp FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____10087 FStar_List.length))
in (FStar_All.pipe_right uu____10085 FStar_Util.string_of_int))
in (FStar_Util.format3 "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes" uu____10079 uu____10081 uu____10083))))
in ((FStar_Errors.Fatal_TooManyUniverse), (uu____10077)))
in (FStar_Errors.raise_error uu____10071 r))
end
| uu____10111 -> begin
()
end));
(

let uu____10114 = ((FStar_Util.is_some lift1) && (

let uu____10125 = (

let uu____10127 = (

let uu____10130 = (FStar_All.pipe_right lift1 FStar_Util.must)
in (FStar_All.pipe_right uu____10130 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____10127 FStar_List.length))
in (Prims.op_disEquality uu____10125 (Prims.parse_int "1"))))
in (match (uu____10114) with
| true -> begin
(

let uu____10185 = (

let uu____10191 = (

let uu____10193 = (FStar_Syntax_Print.lid_to_string sub1.FStar_Syntax_Syntax.source)
in (

let uu____10195 = (FStar_Syntax_Print.lid_to_string sub1.FStar_Syntax_Syntax.target)
in (

let uu____10197 = (

let uu____10199 = (

let uu____10201 = (

let uu____10204 = (FStar_All.pipe_right lift1 FStar_Util.must)
in (FStar_All.pipe_right uu____10204 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____10201 FStar_List.length))
in (FStar_All.pipe_right uu____10199 FStar_Util.string_of_int))
in (FStar_Util.format3 "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes" uu____10193 uu____10195 uu____10197))))
in ((FStar_Errors.Fatal_TooManyUniverse), (uu____10191)))
in (FStar_Errors.raise_error uu____10185 r))
end
| uu____10260 -> begin
()
end));
(

let sub2 = (

let uu___1165_10263 = sub1
in {FStar_Syntax_Syntax.source = uu___1165_10263.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = uu___1165_10263.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = FStar_Pervasives_Native.Some (lift_wp); FStar_Syntax_Syntax.lift = lift1})
in (

let se1 = (

let uu___1168_10265 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_sub_effect (sub2); FStar_Syntax_Syntax.sigrng = uu___1168_10265.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___1168_10265.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___1168_10265.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___1168_10265.FStar_Syntax_Syntax.sigattrs})
in (((se1)::[]), ([]), (env0))));
)))
end)))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, flags) -> begin
(

let uu____10279 = (match ((Prims.op_Equality (FStar_List.length uvs) (Prims.parse_int "0"))) with
| true -> begin
((env), (uvs), (tps), (c))
end
| uu____10305 -> begin
(

let uu____10307 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____10307) with
| (usubst, uvs1) -> begin
(

let tps1 = (FStar_Syntax_Subst.subst_binders usubst tps)
in (

let c1 = (

let uu____10338 = (FStar_Syntax_Subst.shift_subst (FStar_List.length tps1) usubst)
in (FStar_Syntax_Subst.subst_comp uu____10338 c))
in (

let uu____10347 = (FStar_TypeChecker_Env.push_univ_vars env uvs1)
in ((uu____10347), (uvs1), (tps1), (c1)))))
end))
end)
in (match (uu____10279) with
| (env1, uvs1, tps1, c1) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_range env1 r)
in (

let uu____10369 = (FStar_Syntax_Subst.open_comp tps1 c1)
in (match (uu____10369) with
| (tps2, c2) -> begin
(

let uu____10386 = (FStar_TypeChecker_TcTerm.tc_tparams env2 tps2)
in (match (uu____10386) with
| (tps3, env3, us) -> begin
(

let uu____10406 = (FStar_TypeChecker_TcTerm.tc_comp env3 c2)
in (match (uu____10406) with
| (c3, u, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env3 g);
(

let expected_result_typ = (match (tps3) with
| ((x, uu____10434))::uu____10435 -> begin
(FStar_Syntax_Syntax.bv_to_name x)
end
| uu____10454 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_NotEnoughArgumentsForEffect), ("Effect abbreviations must bind at least the result type")) r)
end)
in (

let def_result_typ = (FStar_Syntax_Util.comp_result c3)
in (

let uu____10462 = (

let uu____10464 = (FStar_TypeChecker_Rel.teq_nosmt_force env3 expected_result_typ def_result_typ)
in (not (uu____10464)))
in (match (uu____10462) with
| true -> begin
(

let uu____10467 = (

let uu____10473 = (

let uu____10475 = (FStar_Syntax_Print.term_to_string expected_result_typ)
in (

let uu____10477 = (FStar_Syntax_Print.term_to_string def_result_typ)
in (FStar_Util.format2 "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`" uu____10475 uu____10477)))
in ((FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch), (uu____10473)))
in (FStar_Errors.raise_error uu____10467 r))
end
| uu____10481 -> begin
()
end))));
(

let tps4 = (FStar_Syntax_Subst.close_binders tps3)
in (

let c4 = (FStar_Syntax_Subst.close_comp tps4 c3)
in (

let uu____10485 = (

let uu____10486 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps4), (c4)))) FStar_Pervasives_Native.None r)
in (FStar_TypeChecker_Util.generalize_universes env0 uu____10486))
in (match (uu____10485) with
| (uvs2, t) -> begin
(

let uu____10517 = (

let uu____10522 = (

let uu____10535 = (

let uu____10536 = (FStar_Syntax_Subst.compress t)
in uu____10536.FStar_Syntax_Syntax.n)
in ((tps4), (uu____10535)))
in (match (uu____10522) with
| ([], FStar_Syntax_Syntax.Tm_arrow (uu____10551, c5)) -> begin
(([]), (c5))
end
| (uu____10593, FStar_Syntax_Syntax.Tm_arrow (tps5, c5)) -> begin
((tps5), (c5))
end
| uu____10632 -> begin
(failwith "Impossible (t is an arrow)")
end))
in (match (uu____10517) with
| (tps5, c5) -> begin
((match ((Prims.op_disEquality (FStar_List.length uvs2) (Prims.parse_int "1"))) with
| true -> begin
(

let uu____10666 = (FStar_Syntax_Subst.open_univ_vars uvs2 t)
in (match (uu____10666) with
| (uu____10671, t1) -> begin
(

let uu____10673 = (

let uu____10679 = (

let uu____10681 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____10683 = (FStar_All.pipe_right (FStar_List.length uvs2) FStar_Util.string_of_int)
in (

let uu____10687 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)" uu____10681 uu____10683 uu____10687))))
in ((FStar_Errors.Fatal_TooManyUniverse), (uu____10679)))
in (FStar_Errors.raise_error uu____10673 r))
end))
end
| uu____10691 -> begin
()
end);
(

let se1 = (

let uu___1238_10694 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (((lid), (uvs2), (tps5), (c5), (flags))); FStar_Syntax_Syntax.sigrng = uu___1238_10694.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___1238_10694.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___1238_10694.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___1238_10694.FStar_Syntax_Syntax.sigattrs})
in (((se1)::[]), ([]), (env0)));
)
end))
end))));
)
end))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____10701, uu____10702, uu____10703) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___1_10708 -> (match (uu___1_10708) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____10711 -> begin
false
end)))) -> begin
(([]), ([]), (env0))
end
| FStar_Syntax_Syntax.Sig_let (uu____10717, uu____10718) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___1_10727 -> (match (uu___1_10727) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____10730 -> begin
false
end)))) -> begin
(([]), ([]), (env0))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) -> begin
(

let env1 = (FStar_TypeChecker_Env.set_range env r)
in ((

let uu____10741 = (FStar_TypeChecker_Env.lid_exists env1 lid)
in (match (uu____10741) with
| true -> begin
(

let uu____10744 = (

let uu____10750 = (

let uu____10752 = (FStar_Ident.text_of_lid lid)
in (FStar_Util.format1 "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module" uu____10752))
in ((FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration), (uu____10750)))
in (FStar_Errors.raise_error uu____10744 r))
end
| uu____10756 -> begin
()
end));
(

let uu____10758 = (

let uu____10767 = ((FStar_Options.use_two_phase_tc ()) && (FStar_TypeChecker_Env.should_verify env1))
in (match (uu____10767) with
| true -> begin
(

let uu____10778 = (tc_declare_typ (

let uu___1262_10781 = env1
in {FStar_TypeChecker_Env.solver = uu___1262_10781.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___1262_10781.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___1262_10781.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___1262_10781.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___1262_10781.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___1262_10781.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___1262_10781.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___1262_10781.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___1262_10781.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___1262_10781.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___1262_10781.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___1262_10781.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___1262_10781.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___1262_10781.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___1262_10781.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___1262_10781.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___1262_10781.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___1262_10781.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___1262_10781.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___1262_10781.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___1262_10781.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___1262_10781.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___1262_10781.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___1262_10781.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___1262_10781.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___1262_10781.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___1262_10781.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___1262_10781.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___1262_10781.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___1262_10781.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___1262_10781.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___1262_10781.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___1262_10781.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___1262_10781.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___1262_10781.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___1262_10781.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___1262_10781.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___1262_10781.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___1262_10781.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___1262_10781.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___1262_10781.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___1262_10781.FStar_TypeChecker_Env.nbe}) ((uvs), (t)) se.FStar_Syntax_Syntax.sigrng)
in (match (uu____10778) with
| (uvs1, t1) -> begin
((

let uu____10806 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("TwoPhases")))
in (match (uu____10806) with
| true -> begin
(

let uu____10811 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____10813 = (FStar_Syntax_Print.univ_names_to_string uvs1)
in (FStar_Util.print2 "Val declaration after phase 1: %s and uvs: %s\n" uu____10811 uu____10813)))
end
| uu____10816 -> begin
()
end));
((uvs1), (t1));
)
end))
end
| uu____10822 -> begin
((uvs), (t))
end))
in (match (uu____10758) with
| (uvs1, t1) -> begin
(

let uu____10848 = (tc_declare_typ env1 ((uvs1), (t1)) se.FStar_Syntax_Syntax.sigrng)
in (match (uu____10848) with
| (uvs2, t2) -> begin
((((

let uu___1275_10878 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (uvs2), (t2))); FStar_Syntax_Syntax.sigrng = uu___1275_10878.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___1275_10878.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___1275_10878.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___1275_10878.FStar_Syntax_Syntax.sigattrs}))::[]), ([]), (env0))
end))
end));
))
end
| FStar_Syntax_Syntax.Sig_assume (lid, uvs, t) -> begin
(

let env1 = (FStar_TypeChecker_Env.set_range env r)
in (

let uu____10883 = (

let uu____10892 = ((FStar_Options.use_two_phase_tc ()) && (FStar_TypeChecker_Env.should_verify env1))
in (match (uu____10892) with
| true -> begin
(

let uu____10903 = (tc_assume (

let uu___1284_10906 = env1
in {FStar_TypeChecker_Env.solver = uu___1284_10906.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___1284_10906.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___1284_10906.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___1284_10906.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___1284_10906.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___1284_10906.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___1284_10906.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___1284_10906.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___1284_10906.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___1284_10906.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___1284_10906.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___1284_10906.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___1284_10906.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___1284_10906.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___1284_10906.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___1284_10906.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___1284_10906.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___1284_10906.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___1284_10906.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___1284_10906.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___1284_10906.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = true; FStar_TypeChecker_Env.failhard = uu___1284_10906.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___1284_10906.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___1284_10906.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___1284_10906.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___1284_10906.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___1284_10906.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___1284_10906.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___1284_10906.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___1284_10906.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___1284_10906.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___1284_10906.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___1284_10906.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___1284_10906.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___1284_10906.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___1284_10906.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___1284_10906.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___1284_10906.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___1284_10906.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___1284_10906.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___1284_10906.FStar_TypeChecker_Env.nbe}) ((uvs), (t)) se.FStar_Syntax_Syntax.sigrng)
in (match (uu____10903) with
| (uvs1, t1) -> begin
((

let uu____10932 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("TwoPhases")))
in (match (uu____10932) with
| true -> begin
(

let uu____10937 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____10939 = (FStar_Syntax_Print.univ_names_to_string uvs1)
in (FStar_Util.print2 "Assume after phase 1: %s and uvs: %s\n" uu____10937 uu____10939)))
end
| uu____10942 -> begin
()
end));
((uvs1), (t1));
)
end))
end
| uu____10948 -> begin
((uvs), (t))
end))
in (match (uu____10883) with
| (uvs1, t1) -> begin
(

let uu____10974 = (tc_assume env1 ((uvs1), (t1)) se.FStar_Syntax_Syntax.sigrng)
in (match (uu____10974) with
| (uvs2, t2) -> begin
((((

let uu___1297_11004 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_assume (((lid), (uvs2), (t2))); FStar_Syntax_Syntax.sigrng = uu___1297_11004.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___1297_11004.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___1297_11004.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___1297_11004.FStar_Syntax_Syntax.sigattrs}))::[]), ([]), (env0))
end))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e) -> begin
(

let env1 = (FStar_TypeChecker_Env.set_range env r)
in (

let env2 = (FStar_TypeChecker_Env.set_expected_typ env1 FStar_Syntax_Syntax.t_unit)
in (

let uu____11008 = (FStar_TypeChecker_TcTerm.tc_term env2 e)
in (match (uu____11008) with
| (e1, c, g1) -> begin
(

let uu____11028 = (

let uu____11035 = (

let uu____11038 = (FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r)
in FStar_Pervasives_Native.Some (uu____11038))
in (

let uu____11039 = (

let uu____11044 = (FStar_Syntax_Syntax.lcomp_comp c)
in ((e1), (uu____11044)))
in (FStar_TypeChecker_TcTerm.check_expected_effect env2 uu____11035 uu____11039)))
in (match (uu____11028) with
| (e2, uu____11056, g) -> begin
((

let uu____11059 = (FStar_TypeChecker_Env.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env2 uu____11059));
(

let se1 = (

let uu___1312_11061 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_main (e2); FStar_Syntax_Syntax.sigrng = uu___1312_11061.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___1312_11061.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___1312_11061.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___1312_11061.FStar_Syntax_Syntax.sigattrs})
in (((se1)::[]), ([]), (env0)));
)
end))
end))))
end
| FStar_Syntax_Syntax.Sig_splice (lids, t) -> begin
((

let uu____11073 = (FStar_Options.debug_any ())
in (match (uu____11073) with
| true -> begin
(

let uu____11076 = (FStar_Ident.string_of_lid env.FStar_TypeChecker_Env.curmodule)
in (

let uu____11078 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "%s: Found splice of (%s)\n" uu____11076 uu____11078)))
end
| uu____11081 -> begin
()
end));
(

let uu____11083 = (FStar_TypeChecker_TcTerm.tc_tactic env t)
in (match (uu____11083) with
| (t1, uu____11101, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
(

let ses = (env.FStar_TypeChecker_Env.splice env t1)
in (

let lids' = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses)
in ((FStar_List.iter (fun lid -> (

let uu____11115 = (FStar_List.tryFind (FStar_Ident.lid_equals lid) lids')
in (match (uu____11115) with
| FStar_Pervasives_Native.None when (not (env.FStar_TypeChecker_Env.nosynth)) -> begin
(

let uu____11118 = (

let uu____11124 = (

let uu____11126 = (FStar_Ident.string_of_lid lid)
in (

let uu____11128 = (

let uu____11130 = (FStar_List.map FStar_Ident.string_of_lid lids')
in (FStar_All.pipe_left (FStar_String.concat ", ") uu____11130))
in (FStar_Util.format2 "Splice declared the name %s but it was not defined.\nThose defined were: %s" uu____11126 uu____11128)))
in ((FStar_Errors.Fatal_SplicedUndef), (uu____11124)))
in (FStar_Errors.raise_error uu____11118 r))
end
| uu____11142 -> begin
()
end))) lids);
(

let dsenv1 = (FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt_force env.FStar_TypeChecker_Env.dsenv ses)
in (

let env1 = (

let uu___1333_11147 = env
in {FStar_TypeChecker_Env.solver = uu___1333_11147.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___1333_11147.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___1333_11147.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___1333_11147.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___1333_11147.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___1333_11147.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___1333_11147.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___1333_11147.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___1333_11147.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___1333_11147.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___1333_11147.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___1333_11147.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___1333_11147.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___1333_11147.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___1333_11147.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___1333_11147.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___1333_11147.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___1333_11147.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___1333_11147.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___1333_11147.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___1333_11147.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___1333_11147.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___1333_11147.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___1333_11147.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___1333_11147.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___1333_11147.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___1333_11147.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___1333_11147.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___1333_11147.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___1333_11147.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___1333_11147.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___1333_11147.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___1333_11147.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___1333_11147.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___1333_11147.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___1333_11147.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___1333_11147.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___1333_11147.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___1333_11147.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___1333_11147.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___1333_11147.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = dsenv1; FStar_TypeChecker_Env.nbe = uu___1333_11147.FStar_TypeChecker_Env.nbe})
in (([]), (ses), (env1))));
)));
)
end));
)
end
| FStar_Syntax_Syntax.Sig_let (lbs, lids) -> begin
(

let env1 = (FStar_TypeChecker_Env.set_range env r)
in (

let check_quals_eq = (fun l qopt val_q -> (match (qopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (val_q)
end
| FStar_Pervasives_Native.Some (q') -> begin
(

let drop_logic = (FStar_List.filter (fun x -> (not ((Prims.op_Equality x FStar_Syntax_Syntax.Logic)))))
in (

let uu____11215 = (

let uu____11217 = (

let uu____11226 = (drop_logic val_q)
in (

let uu____11229 = (drop_logic q')
in ((uu____11226), (uu____11229))))
in (match (uu____11217) with
| (val_q1, q'1) -> begin
((Prims.op_Equality (FStar_List.length val_q1) (FStar_List.length q'1)) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal val_q1 q'1))
end))
in (match (uu____11215) with
| true -> begin
FStar_Pervasives_Native.Some (q')
end
| uu____11254 -> begin
(

let uu____11256 = (

let uu____11262 = (

let uu____11264 = (FStar_Syntax_Print.lid_to_string l)
in (

let uu____11266 = (FStar_Syntax_Print.quals_to_string val_q)
in (

let uu____11268 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" uu____11264 uu____11266 uu____11268))))
in ((FStar_Errors.Fatal_InconsistentQualifierAnnotation), (uu____11262)))
in (FStar_Errors.raise_error uu____11256 r))
end)))
end))
in (

let rename_parameters = (fun lb -> (

let rename_in_typ = (fun def typ -> (

let typ1 = (FStar_Syntax_Subst.compress typ)
in (

let def_bs = (

let uu____11305 = (

let uu____11306 = (FStar_Syntax_Subst.compress def)
in uu____11306.FStar_Syntax_Syntax.n)
in (match (uu____11305) with
| FStar_Syntax_Syntax.Tm_abs (binders, uu____11318, uu____11319) -> begin
binders
end
| uu____11344 -> begin
[]
end))
in (match (typ1) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow (val_bs, c); FStar_Syntax_Syntax.pos = r1; FStar_Syntax_Syntax.vars = uu____11356} -> begin
(

let has_auto_name = (fun bv -> (FStar_Util.starts_with bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Ident.reserved_prefix))
in (

let rec rename_binders1 = (fun def_bs1 val_bs1 -> (match (((def_bs1), (val_bs1))) with
| ([], uu____11461) -> begin
val_bs1
end
| (uu____11492, []) -> begin
val_bs1
end
| (((body_bv, uu____11524))::bt, ((val_bv, aqual))::vt) -> begin
(

let uu____11581 = (rename_binders1 bt vt)
in ((match ((((has_auto_name body_bv)), ((has_auto_name val_bv)))) with
| (true, uu____11605) -> begin
((val_bv), (aqual))
end
| (false, true) -> begin
(((

let uu___1402_11619 = val_bv
in {FStar_Syntax_Syntax.ppname = (

let uu___1404_11622 = val_bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = body_bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText; FStar_Ident.idRange = uu___1404_11622.FStar_Ident.idRange}); FStar_Syntax_Syntax.index = uu___1402_11619.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___1402_11619.FStar_Syntax_Syntax.sort})), (aqual))
end
| (false, false) -> begin
((val_bv), (aqual))
end))::uu____11581)
end))
in (

let uu____11629 = (

let uu____11636 = (

let uu____11637 = (

let uu____11652 = (rename_binders1 def_bs val_bs)
in ((uu____11652), (c)))
in FStar_Syntax_Syntax.Tm_arrow (uu____11637))
in (FStar_Syntax_Syntax.mk uu____11636))
in (uu____11629 FStar_Pervasives_Native.None r1))))
end
| uu____11671 -> begin
typ1
end))))
in (

let uu___1410_11672 = lb
in (

let uu____11673 = (rename_in_typ lb.FStar_Syntax_Syntax.lbdef lb.FStar_Syntax_Syntax.lbtyp)
in {FStar_Syntax_Syntax.lbname = uu___1410_11672.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___1410_11672.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____11673; FStar_Syntax_Syntax.lbeff = uu___1410_11672.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___1410_11672.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___1410_11672.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___1410_11672.FStar_Syntax_Syntax.lbpos}))))
in (

let uu____11676 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.fold_left (fun uu____11731 lb -> (match (uu____11731) with
| (gen1, lbs1, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____11777 = (

let uu____11789 = (FStar_TypeChecker_Env.try_lookup_val_decl env1 lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____11789) with
| FStar_Pervasives_Native.None -> begin
(match ((Prims.op_disEquality lb.FStar_Syntax_Syntax.lbunivs [])) with
| true -> begin
((false), (lb), (quals_opt))
end
| uu____11835 -> begin
((gen1), (lb), (quals_opt))
end)
end
| FStar_Pervasives_Native.Some ((uvs, tval), quals) -> begin
(

let quals_opt1 = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (

let def = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
lb.FStar_Syntax_Syntax.lbdef
end
| uu____11869 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((lb.FStar_Syntax_Syntax.lbdef), (((FStar_Util.Inl (lb.FStar_Syntax_Syntax.lbtyp)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.pos)
end)
in ((match (((Prims.op_disEquality lb.FStar_Syntax_Syntax.lbunivs []) && (Prims.op_disEquality (FStar_List.length lb.FStar_Syntax_Syntax.lbunivs) (FStar_List.length uvs)))) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_IncoherentInlineUniverse), ("Inline universes are incoherent with annotation from val declaration")) r)
end
| uu____11914 -> begin
()
end);
(

let uu____11916 = (FStar_Syntax_Syntax.mk_lb ((FStar_Util.Inr (lbname)), (uvs), (FStar_Parser_Const.effect_ALL_lid), (tval), (def), ([]), (lb.FStar_Syntax_Syntax.lbpos)))
in ((false), (uu____11916), (quals_opt1)));
)))
end))
in (match (uu____11777) with
| (gen2, lb1, quals_opt1) -> begin
((gen2), ((lb1)::lbs1), (quals_opt1))
end)))
end)) ((true), ([]), ((match ((Prims.op_Equality se.FStar_Syntax_Syntax.sigquals [])) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____11977 -> begin
FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
end)))))
in (match (uu____11676) with
| (should_generalize, lbs', quals_opt) -> begin
(

let quals = (match (quals_opt) with
| FStar_Pervasives_Native.None -> begin
(FStar_Syntax_Syntax.Visible_default)::[]
end
| FStar_Pervasives_Native.Some (q) -> begin
(

let uu____12020 = (FStar_All.pipe_right q (FStar_Util.for_some (fun uu___2_12026 -> (match (uu___2_12026) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| FStar_Syntax_Syntax.Visible_default -> begin
true
end
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____12031 -> begin
false
end))))
in (match (uu____12020) with
| true -> begin
q
end
| uu____12036 -> begin
(FStar_Syntax_Syntax.Visible_default)::q
end))
end)
in (

let lbs'1 = (FStar_List.rev lbs')
in (

let e = (

let uu____12044 = (

let uu____12051 = (

let uu____12052 = (

let uu____12066 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) FStar_Pervasives_Native.None r)
in (((((FStar_Pervasives_Native.fst lbs)), (lbs'1))), (uu____12066)))
in FStar_Syntax_Syntax.Tm_let (uu____12052))
in (FStar_Syntax_Syntax.mk uu____12051))
in (uu____12044 FStar_Pervasives_Native.None r))
in (

let env' = (

let uu___1453_12085 = env1
in {FStar_TypeChecker_Env.solver = uu___1453_12085.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___1453_12085.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___1453_12085.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___1453_12085.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___1453_12085.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___1453_12085.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___1453_12085.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___1453_12085.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___1453_12085.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___1453_12085.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___1453_12085.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___1453_12085.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___1453_12085.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = uu___1453_12085.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = uu___1453_12085.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___1453_12085.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___1453_12085.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___1453_12085.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___1453_12085.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___1453_12085.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___1453_12085.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___1453_12085.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___1453_12085.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___1453_12085.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___1453_12085.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___1453_12085.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___1453_12085.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___1453_12085.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___1453_12085.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___1453_12085.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___1453_12085.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___1453_12085.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___1453_12085.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___1453_12085.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___1453_12085.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___1453_12085.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___1453_12085.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___1453_12085.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___1453_12085.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___1453_12085.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___1453_12085.FStar_TypeChecker_Env.nbe})
in (

let e1 = (

let uu____12088 = ((FStar_Options.use_two_phase_tc ()) && (FStar_TypeChecker_Env.should_verify env'))
in (match (uu____12088) with
| true -> begin
(

let drop_lbtyp = (fun e_lax -> (

let uu____12097 = (

let uu____12098 = (FStar_Syntax_Subst.compress e_lax)
in uu____12098.FStar_Syntax_Syntax.n)
in (match (uu____12097) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let lb_unannotated = (

let uu____12120 = (

let uu____12121 = (FStar_Syntax_Subst.compress e)
in uu____12121.FStar_Syntax_Syntax.n)
in (match (uu____12120) with
| FStar_Syntax_Syntax.Tm_let ((uu____12125, (lb1)::[]), uu____12127) -> begin
(

let uu____12143 = (

let uu____12144 = (FStar_Syntax_Subst.compress lb1.FStar_Syntax_Syntax.lbtyp)
in uu____12144.FStar_Syntax_Syntax.n)
in (match (uu____12143) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| uu____12149 -> begin
false
end))
end
| uu____12151 -> begin
(failwith "Impossible: first phase lb and second phase lb differ in structure!")
end))
in (match (lb_unannotated) with
| true -> begin
(

let uu___1478_12155 = e_lax
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (((((false), (((

let uu___1480_12170 = lb
in {FStar_Syntax_Syntax.lbname = uu___1480_12170.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___1480_12170.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = uu___1480_12170.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___1480_12170.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___1480_12170.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___1480_12170.FStar_Syntax_Syntax.lbpos}))::[]))), (e2))); FStar_Syntax_Syntax.pos = uu___1478_12155.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___1478_12155.FStar_Syntax_Syntax.vars})
end
| uu____12171 -> begin
e_lax
end))
end
| uu____12173 -> begin
e_lax
end)))
in (

let uu____12174 = (FStar_Util.record_time (fun uu____12182 -> (

let uu____12183 = (

let uu____12184 = (

let uu____12185 = (FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term (

let uu___1484_12194 = env'
in {FStar_TypeChecker_Env.solver = uu___1484_12194.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___1484_12194.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___1484_12194.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___1484_12194.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___1484_12194.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___1484_12194.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___1484_12194.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___1484_12194.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___1484_12194.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___1484_12194.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___1484_12194.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___1484_12194.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___1484_12194.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___1484_12194.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___1484_12194.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___1484_12194.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___1484_12194.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___1484_12194.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___1484_12194.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___1484_12194.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___1484_12194.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = true; FStar_TypeChecker_Env.failhard = uu___1484_12194.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___1484_12194.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___1484_12194.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___1484_12194.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___1484_12194.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___1484_12194.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___1484_12194.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___1484_12194.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___1484_12194.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___1484_12194.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___1484_12194.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___1484_12194.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___1484_12194.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___1484_12194.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___1484_12194.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___1484_12194.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___1484_12194.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___1484_12194.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___1484_12194.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___1484_12194.FStar_TypeChecker_Env.nbe}) e)
in (FStar_All.pipe_right uu____12185 (fun uu____12207 -> (match (uu____12207) with
| (e1, uu____12215, uu____12216) -> begin
e1
end))))
in (FStar_All.pipe_right uu____12184 (FStar_TypeChecker_Normalize.remove_uvar_solutions env')))
in (FStar_All.pipe_right uu____12183 drop_lbtyp))))
in (match (uu____12174) with
| (e1, ms) -> begin
((

let uu____12222 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("TwoPhases")))
in (match (uu____12222) with
| true -> begin
(

let uu____12227 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.print1 "Let binding after phase 1: %s\n" uu____12227))
end
| uu____12230 -> begin
()
end));
(

let uu____12233 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("TCDeclTime")))
in (match (uu____12233) with
| true -> begin
(

let uu____12238 = (FStar_Util.string_of_int ms)
in (FStar_Util.print1 "Let binding elaborated (phase 1) in %s milliseconds\n" uu____12238))
end
| uu____12241 -> begin
()
end));
e1;
)
end)))
end
| uu____12243 -> begin
e
end))
in (

let uu____12245 = (

let uu____12254 = (FStar_Syntax_Util.extract_attr' FStar_Parser_Const.postprocess_with se.FStar_Syntax_Syntax.sigattrs)
in (match (uu____12254) with
| FStar_Pervasives_Native.None -> begin
((se.FStar_Syntax_Syntax.sigattrs), (FStar_Pervasives_Native.None))
end
| FStar_Pervasives_Native.Some (ats, ((tau, FStar_Pervasives_Native.None))::[]) -> begin
((ats), (FStar_Pervasives_Native.Some (tau)))
end
| FStar_Pervasives_Native.Some (ats, args) -> begin
((FStar_Errors.log_issue r ((FStar_Errors.Warning_UnrecognizedAttribute), ("Ill-formed application of `postprocess_with`")));
((se.FStar_Syntax_Syntax.sigattrs), (FStar_Pervasives_Native.None));
)
end))
in (match (uu____12245) with
| (attrs, post_tau) -> begin
(

let se1 = (

let uu___1514_12359 = se
in {FStar_Syntax_Syntax.sigel = uu___1514_12359.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___1514_12359.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___1514_12359.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___1514_12359.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = attrs})
in (

let postprocess_lb = (fun tau lb -> (

let lbdef = (env1.FStar_TypeChecker_Env.postprocess env1 tau lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (

let uu___1521_12372 = lb
in {FStar_Syntax_Syntax.lbname = uu___1521_12372.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___1521_12372.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___1521_12372.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___1521_12372.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef; FStar_Syntax_Syntax.lbattrs = uu___1521_12372.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___1521_12372.FStar_Syntax_Syntax.lbpos})))
in (

let uu____12373 = (FStar_Util.record_time (fun uu____12392 -> (FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term env' e1)))
in (match (uu____12373) with
| (r1, ms) -> begin
((

let uu____12420 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("TCDeclTime")))
in (match (uu____12420) with
| true -> begin
(

let uu____12425 = (FStar_Util.string_of_int ms)
in (FStar_Util.print1 "Let binding typechecked in phase 2 in %s milliseconds\n" uu____12425))
end
| uu____12428 -> begin
()
end));
(

let uu____12430 = (match (r1) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs1, e2); FStar_Syntax_Syntax.pos = uu____12455; FStar_Syntax_Syntax.vars = uu____12456}, uu____12457, g) when (FStar_TypeChecker_Env.is_trivial g) -> begin
(

let lbs2 = (

let uu____12487 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1) (FStar_List.map rename_parameters))
in (((FStar_Pervasives_Native.fst lbs1)), (uu____12487)))
in (

let lbs3 = (

let uu____12511 = (match (post_tau) with
| FStar_Pervasives_Native.Some (tau) -> begin
(FStar_List.map (postprocess_lb tau) (FStar_Pervasives_Native.snd lbs2))
end
| FStar_Pervasives_Native.None -> begin
(FStar_Pervasives_Native.snd lbs2)
end)
in (((FStar_Pervasives_Native.fst lbs2)), (uu____12511)))
in (

let quals1 = (match (e2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (uu____12534, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| uu____12539 -> begin
quals
end)
in (((

let uu___1551_12548 = se1
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((lbs3), (lids))); FStar_Syntax_Syntax.sigrng = uu___1551_12548.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = uu___1551_12548.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___1551_12548.FStar_Syntax_Syntax.sigattrs})), (lbs3)))))
end
| uu____12551 -> begin
(failwith "impossible (typechecking should preserve Tm_let)")
end)
in (match (uu____12430) with
| (se2, lbs1) -> begin
((FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1) (FStar_List.iter (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (FStar_TypeChecker_Env.insert_fv_info env1 fv lb.FStar_Syntax_Syntax.lbtyp)))));
(

let uu____12607 = (log env1)
in (match (uu____12607) with
| true -> begin
(

let uu____12610 = (

let uu____12612 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1) (FStar_List.map (fun lb -> (

let should_log = (

let uu____12632 = (

let uu____12641 = (

let uu____12642 = (

let uu____12645 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____12645.FStar_Syntax_Syntax.fv_name)
in uu____12642.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env1 uu____12641))
in (match (uu____12632) with
| FStar_Pervasives_Native.None -> begin
true
end
| uu____12654 -> begin
false
end))
in (match (should_log) with
| true -> begin
(

let uu____12666 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____12668 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" uu____12666 uu____12668)))
end
| uu____12671 -> begin
""
end)))))
in (FStar_All.pipe_right uu____12612 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" uu____12610))
end
| uu____12680 -> begin
()
end));
(check_must_erase_attribute env0 se2);
(((se2)::[]), ([]), (env0));
)
end));
)
end))))
end)))))))
end)))))
end));
)))


let tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env se -> (

let env1 = (set_hint_correlator env se)
in ((

let uu____12720 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____12720) with
| true -> begin
(

let uu____12723 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____12723))
end
| uu____12726 -> begin
()
end));
(

let uu____12728 = (get_fail_se se)
in (match (uu____12728) with
| FStar_Pervasives_Native.Some (uu____12749, false) when (

let uu____12766 = (FStar_TypeChecker_Env.should_verify env1)
in (not (uu____12766))) -> begin
(([]), ([]), (env1))
end
| FStar_Pervasives_Native.Some (errnos, lax1) -> begin
(

let env' = (match (lax1) with
| true -> begin
(

let uu___1582_12792 = env1
in {FStar_TypeChecker_Env.solver = uu___1582_12792.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___1582_12792.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___1582_12792.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___1582_12792.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___1582_12792.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___1582_12792.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___1582_12792.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___1582_12792.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___1582_12792.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___1582_12792.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___1582_12792.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___1582_12792.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___1582_12792.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___1582_12792.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___1582_12792.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___1582_12792.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___1582_12792.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___1582_12792.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___1582_12792.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___1582_12792.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___1582_12792.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___1582_12792.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___1582_12792.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___1582_12792.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___1582_12792.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___1582_12792.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___1582_12792.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___1582_12792.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___1582_12792.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___1582_12792.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___1582_12792.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___1582_12792.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___1582_12792.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___1582_12792.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___1582_12792.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___1582_12792.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___1582_12792.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___1582_12792.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___1582_12792.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___1582_12792.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___1582_12792.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___1582_12792.FStar_TypeChecker_Env.nbe})
end
| uu____12794 -> begin
env1
end)
in ((

let uu____12797 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____12797) with
| true -> begin
(

let uu____12800 = (

let uu____12802 = (FStar_List.map FStar_Util.string_of_int errnos)
in (FStar_All.pipe_left (FStar_String.concat "; ") uu____12802))
in (FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____12800))
end
| uu____12814 -> begin
()
end));
(

let uu____12816 = (FStar_Errors.catch_errors (fun uu____12846 -> (FStar_Options.with_saved_options (fun uu____12858 -> (tc_decl' env' se)))))
in (match (uu____12816) with
| (errs, uu____12870) -> begin
((

let uu____12900 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____12900) with
| true -> begin
((FStar_Util.print_string ">> Got issues: [\n");
(FStar_List.iter FStar_Errors.print_issue errs);
(FStar_Util.print_string ">>]\n");
)
end
| uu____12907 -> begin
()
end));
(

let sort = (FStar_List.sortWith (fun x y -> (x - y)))
in (

let errnos1 = (sort errnos)
in (

let actual = (

let uu____12935 = (FStar_List.concatMap (fun i -> (list_of_option i.FStar_Errors.issue_number)) errs)
in (sort uu____12935))
in ((match (errs) with
| [] -> begin
((FStar_List.iter FStar_Errors.print_issue errs);
(FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng ((FStar_Errors.Error_DidNotFail), ("This top-level definition was expected to fail, but it succeeded")));
)
end
| uu____12947 -> begin
(match (((Prims.op_disEquality errnos1 []) && (Prims.op_disEquality errnos1 actual))) with
| true -> begin
(

let uu____12958 = (

let uu____12968 = (check_multi_eq errnos1 actual)
in (match (uu____12968) with
| FStar_Pervasives_Native.Some (r) -> begin
r
end
| FStar_Pervasives_Native.None -> begin
(((~- ((Prims.parse_int "1")))), ((~- ((Prims.parse_int "1")))), ((~- ((Prims.parse_int "1")))))
end))
in (match (uu____12958) with
| (e, n1, n2) -> begin
((FStar_List.iter FStar_Errors.print_issue errs);
(

let uu____13033 = (

let uu____13039 = (

let uu____13041 = (FStar_Common.string_of_list FStar_Util.string_of_int errnos1)
in (

let uu____13044 = (FStar_Common.string_of_list FStar_Util.string_of_int actual)
in (

let uu____13047 = (FStar_Util.string_of_int e)
in (

let uu____13049 = (FStar_Util.string_of_int n2)
in (

let uu____13051 = (FStar_Util.string_of_int n1)
in (FStar_Util.format5 "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s." uu____13041 uu____13044 uu____13047 uu____13049 uu____13051))))))
in ((FStar_Errors.Error_DidNotFail), (uu____13039)))
in (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng uu____13033));
)
end))
end
| uu____13055 -> begin
()
end)
end);
(([]), ([]), (env1));
))));
)
end));
))
end
| FStar_Pervasives_Native.None -> begin
(tc_decl' env1 se)
end));
)))


let for_export : 'Auu____13078 . 'Auu____13078  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun env hidden se -> (

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___3_13121 -> (match (uu___3_13121) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| uu____13124 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| FStar_Syntax_Syntax.Projector (l, uu____13135) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| FStar_Syntax_Syntax.Discriminator (l) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| uu____13143 -> begin
false
end))
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_pragma (uu____13153) -> begin
(([]), (hidden))
end
| FStar_Syntax_Syntax.Sig_splice (uu____13158) -> begin
(failwith "Impossible (Already handled)")
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____13174) -> begin
(failwith "Impossible (Already handled)")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____13200) -> begin
(failwith "Impossible (Already handled)")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____13226) -> begin
(

let uu____13235 = (is_abstract se.FStar_Syntax_Syntax.sigquals)
in (match (uu____13235) with
| true -> begin
(

let for_export_bundle = (fun se1 uu____13272 -> (match (uu____13272) with
| (out, hidden1) -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, uu____13311, uu____13312) -> begin
(

let dec = (

let uu___1658_13322 = se1
in (

let uu____13323 = (

let uu____13324 = (

let uu____13331 = (

let uu____13332 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow bs uu____13332))
in ((l), (us), (uu____13331)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____13324))
in {FStar_Syntax_Syntax.sigel = uu____13323; FStar_Syntax_Syntax.sigrng = uu___1658_13322.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::se1.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___1658_13322.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___1658_13322.FStar_Syntax_Syntax.sigattrs}))
in (((dec)::out), (hidden1)))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, uu____13342, uu____13343, uu____13344) -> begin
(

let dec = (

let uu___1669_13352 = se1
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t))); FStar_Syntax_Syntax.sigrng = uu___1669_13352.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::[]; FStar_Syntax_Syntax.sigmeta = uu___1669_13352.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___1669_13352.FStar_Syntax_Syntax.sigattrs})
in (((dec)::out), ((l)::hidden1)))
end
| uu____13357 -> begin
((out), (hidden1))
end)
end))
in (FStar_List.fold_right for_export_bundle ses (([]), (hidden))))
end
| uu____13374 -> begin
(((se)::[]), (hidden))
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____13380, uu____13381, uu____13382) -> begin
(

let uu____13383 = (is_abstract se.FStar_Syntax_Syntax.sigquals)
in (match (uu____13383) with
| true -> begin
(([]), (hidden))
end
| uu____13398 -> begin
(((se)::[]), (hidden))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, us, t) -> begin
(

let uu____13407 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some is_hidden_proj_or_disc))
in (match (uu____13407) with
| true -> begin
((((

let uu___1685_13426 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t))); FStar_Syntax_Syntax.sigrng = uu___1685_13426.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::[]; FStar_Syntax_Syntax.sigmeta = uu___1685_13426.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___1685_13426.FStar_Syntax_Syntax.sigattrs}))::[]), ((l)::hidden))
end
| uu____13427 -> begin
(

let uu____13429 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___4_13435 -> (match (uu___4_13435) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____13438) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____13444) -> begin
true
end
| uu____13446 -> begin
false
end))))
in (match (uu____13429) with
| true -> begin
(((se)::[]), (hidden))
end
| uu____13461 -> begin
(([]), (hidden))
end))
end))
end
| FStar_Syntax_Syntax.Sig_main (uu____13467) -> begin
(([]), (hidden))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____13472) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____13477) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____13482) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____13487) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____13505) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____13519 = (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
in (match (uu____13519) with
| true -> begin
(([]), (hidden))
end
| uu____13537 -> begin
(

let dec = (

let uu____13540 = (FStar_Ident.range_of_lid lid)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu____13540; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::[]; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (((dec)::[]), ((lid)::hidden)))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, l) -> begin
(

let uu____13551 = (is_abstract se.FStar_Syntax_Syntax.sigquals)
in (match (uu____13551) with
| true -> begin
(

let uu____13562 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let uu___1722_13576 = se
in (

let uu____13577 = (

let uu____13578 = (

let uu____13585 = (

let uu____13586 = (

let uu____13589 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____13589.FStar_Syntax_Syntax.fv_name)
in uu____13586.FStar_Syntax_Syntax.v)
in ((uu____13585), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____13578))
in {FStar_Syntax_Syntax.sigel = uu____13577; FStar_Syntax_Syntax.sigrng = uu___1722_13576.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___1722_13576.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___1722_13576.FStar_Syntax_Syntax.sigattrs})))))
in ((uu____13562), (hidden)))
end
| uu____13594 -> begin
(((se)::[]), (hidden))
end))
end))))


let add_sigelt_to_env : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env = (fun env se -> ((

let uu____13612 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____13612) with
| true -> begin
(

let uu____13615 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Adding top-level decl to environment: %s\n" uu____13615))
end
| uu____13618 -> begin
()
end));
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____13620) -> begin
(failwith "add_sigelt_to_env: Impossible, bare data constructor")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____13638) -> begin
(failwith "add_sigelt_to_env: Impossible, bare data constructor")
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (uu____13655)) -> begin
(z3_reset_options env)
end
| FStar_Syntax_Syntax.Sig_pragma (uu____13659) -> begin
env
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____13660) -> begin
env
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_sigelt env se)
in (FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun env2 a -> (

let uu____13670 = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Env.push_sigelt env2 uu____13670))) env1)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____13671, uu____13672, uu____13673) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___5_13678 -> (match (uu___5_13678) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____13681 -> begin
false
end)))) -> begin
env
end
| FStar_Syntax_Syntax.Sig_let (uu____13683, uu____13684) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___5_13693 -> (match (uu___5_13693) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____13696 -> begin
false
end)))) -> begin
env
end
| uu____13698 -> begin
(FStar_TypeChecker_Env.push_sigelt env se)
end);
))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let rec process_one_decl = (fun uu____13767 se -> (match (uu____13767) with
| (ses1, exports, env1, hidden) -> begin
((

let uu____13820 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____13820) with
| true -> begin
(

let uu____13823 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____13823))
end
| uu____13826 -> begin
()
end));
(

let uu____13828 = (tc_decl env1 se)
in (match (uu____13828) with
| (ses', ses_elaborated, env2) -> begin
(

let ses'1 = (FStar_All.pipe_right ses' (FStar_List.map (fun se1 -> ((

let uu____13881 = (FStar_TypeChecker_Env.debug env2 (FStar_Options.Other ("UF")))
in (match (uu____13881) with
| true -> begin
(

let uu____13885 = (FStar_Syntax_Print.sigelt_to_string se1)
in (FStar_Util.print1 "About to elim vars from %s\n" uu____13885))
end
| uu____13888 -> begin
()
end));
(FStar_TypeChecker_Normalize.elim_uvars env2 se1);
))))
in (

let ses_elaborated1 = (FStar_All.pipe_right ses_elaborated (FStar_List.map (fun se1 -> ((

let uu____13901 = (FStar_TypeChecker_Env.debug env2 (FStar_Options.Other ("UF")))
in (match (uu____13901) with
| true -> begin
(

let uu____13905 = (FStar_Syntax_Print.sigelt_to_string se1)
in (FStar_Util.print1 "About to elim vars from (elaborated) %s\\m" uu____13905))
end
| uu____13908 -> begin
()
end));
(FStar_TypeChecker_Normalize.elim_uvars env2 se1);
))))
in ((FStar_TypeChecker_Env.promote_id_info env2 (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.AllowUnboundUniverses)::(FStar_TypeChecker_Env.CheckNoUvars)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::(FStar_TypeChecker_Env.CompressUvars)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota))::(FStar_TypeChecker_Env.NoFullNorm)::[]) env2 t)));
(

let env3 = (FStar_All.pipe_right ses'1 (FStar_List.fold_left (fun env3 se1 -> (add_sigelt_to_env env3 se1)) env2))
in ((FStar_Syntax_Unionfind.reset ());
(

let uu____13922 = ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env3) (FStar_Options.Other ("LogTypes"))))
in (match (uu____13922) with
| true -> begin
(

let uu____13927 = (FStar_List.fold_left (fun s se1 -> (

let uu____13936 = (

let uu____13938 = (FStar_Syntax_Print.sigelt_to_string se1)
in (Prims.op_Hat uu____13938 "\n"))
in (Prims.op_Hat s uu____13936))) "" ses'1)
in (FStar_Util.print1 "Checked: %s\n" uu____13927))
end
| uu____13943 -> begin
()
end));
(FStar_List.iter (fun se1 -> (env3.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env3 se1)) ses'1);
(

let uu____13948 = (

let uu____13957 = (FStar_Options.use_extracted_interfaces ())
in (match (uu____13957) with
| true -> begin
(((FStar_List.rev_append ses'1 exports)), ([]))
end
| uu____13972 -> begin
(

let accum_exports_hidden = (fun uu____13999 se1 -> (match (uu____13999) with
| (exports1, hidden1) -> begin
(

let uu____14027 = (for_export env3 hidden1 se1)
in (match (uu____14027) with
| (se_exported, hidden2) -> begin
(((FStar_List.rev_append se_exported exports1)), (hidden2))
end))
end))
in (FStar_List.fold_left accum_exports_hidden ((exports), (hidden)) ses'1))
end))
in (match (uu____13948) with
| (exports1, hidden1) -> begin
(((((FStar_List.rev_append ses'1 ses1)), (exports1), (env3), (hidden1))), (ses_elaborated1))
end));
));
)))
end));
)
end))
in (

let process_one_decl_timed = (fun acc se -> (

let uu____14181 = acc
in (match (uu____14181) with
| (uu____14216, uu____14217, env1, uu____14219) -> begin
(

let uu____14232 = (FStar_Util.record_time (fun uu____14279 -> (process_one_decl acc se)))
in (match (uu____14232) with
| (r, ms_elapsed) -> begin
((

let uu____14345 = (((FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("TCDeclTime"))) || (FStar_Util.for_some (FStar_Syntax_Util.attr_eq FStar_Syntax_Util.tcdecltime_attr) se.FStar_Syntax_Syntax.sigattrs)) || (FStar_Options.timing ()))
in (match (uu____14345) with
| true -> begin
(

let uu____14349 = (FStar_Syntax_Print.sigelt_to_string_short se)
in (

let uu____14351 = (FStar_Util.string_of_int ms_elapsed)
in (FStar_Util.print2 "Checked %s in %s milliseconds\n" uu____14349 uu____14351)))
end
| uu____14354 -> begin
()
end));
r;
)
end))
end)))
in (

let uu____14356 = (FStar_Util.fold_flatten process_one_decl_timed (([]), ([]), (env), ([])) ses)
in (match (uu____14356) with
| (ses1, exports, env1, uu____14404) -> begin
(((FStar_List.rev_append ses1 [])), ((FStar_List.rev_append exports [])), (env1))
end)))))


let check_exports : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  unit = (fun env modul exports -> (

let env1 = (

let uu___1826_14442 = env
in {FStar_TypeChecker_Env.solver = uu___1826_14442.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___1826_14442.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___1826_14442.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___1826_14442.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___1826_14442.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___1826_14442.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___1826_14442.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___1826_14442.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___1826_14442.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___1826_14442.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___1826_14442.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___1826_14442.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___1826_14442.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___1826_14442.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___1826_14442.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = uu___1826_14442.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___1826_14442.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___1826_14442.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___1826_14442.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = true; FStar_TypeChecker_Env.phase1 = uu___1826_14442.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___1826_14442.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___1826_14442.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___1826_14442.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___1826_14442.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___1826_14442.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___1826_14442.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___1826_14442.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___1826_14442.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___1826_14442.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___1826_14442.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___1826_14442.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___1826_14442.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___1826_14442.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___1826_14442.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___1826_14442.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___1826_14442.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___1826_14442.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___1826_14442.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___1826_14442.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___1826_14442.FStar_TypeChecker_Env.nbe})
in (

let check_term = (fun lid univs1 t -> (

let uu____14462 = (FStar_Syntax_Subst.open_univ_vars univs1 t)
in (match (uu____14462) with
| (univs2, t1) -> begin
((

let uu____14470 = (

let uu____14472 = (

let uu____14478 = (FStar_TypeChecker_Env.set_current_module env1 modul.FStar_Syntax_Syntax.name)
in (FStar_TypeChecker_Env.debug uu____14478))
in (FStar_All.pipe_left uu____14472 (FStar_Options.Other ("Exports"))))
in (match (uu____14470) with
| true -> begin
(

let uu____14482 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____14484 = (

let uu____14486 = (FStar_All.pipe_right univs2 (FStar_List.map (fun x -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (x))))))
in (FStar_All.pipe_right uu____14486 (FStar_String.concat ", ")))
in (

let uu____14503 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Checking for export %s <%s> : %s\n" uu____14482 uu____14484 uu____14503))))
end
| uu____14506 -> begin
()
end));
(

let env2 = (FStar_TypeChecker_Env.push_univ_vars env1 univs2)
in (

let uu____14509 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1)
in (FStar_All.pipe_right uu____14509 (fun a2 -> ()))));
)
end)))
in (

let check_term1 = (fun lid univs1 t -> ((

let uu____14535 = (

let uu____14537 = (FStar_Syntax_Print.lid_to_string modul.FStar_Syntax_Syntax.name)
in (

let uu____14539 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Interface of %s violates its abstraction (add a \'private\' qualifier to \'%s\'?)" uu____14537 uu____14539)))
in (FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____14535));
(check_term lid univs1 t);
(FStar_Errors.message_prefix.FStar_Errors.clear_prefix ());
))
in (

let rec check_sigelt = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____14550) -> begin
(

let uu____14559 = (

let uu____14561 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____14561)))
in (match (uu____14559) with
| true -> begin
(FStar_All.pipe_right ses (FStar_List.iter check_sigelt))
end
| uu____14569 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (l, univs1, binders, typ, uu____14575, uu____14576) -> begin
(

let t = (

let uu____14588 = (

let uu____14595 = (

let uu____14596 = (

let uu____14611 = (FStar_Syntax_Syntax.mk_Total typ)
in ((binders), (uu____14611)))
in FStar_Syntax_Syntax.Tm_arrow (uu____14596))
in (FStar_Syntax_Syntax.mk uu____14595))
in (uu____14588 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng))
in (check_term1 l univs1 t))
end
| FStar_Syntax_Syntax.Sig_datacon (l, univs1, t, uu____14627, uu____14628, uu____14629) -> begin
(check_term1 l univs1 t)
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, univs1, t) -> begin
(

let uu____14639 = (

let uu____14641 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____14641)))
in (match (uu____14639) with
| true -> begin
(check_term1 l univs1 t)
end
| uu____14647 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_let ((uu____14649, lbs), uu____14651) -> begin
(

let uu____14662 = (

let uu____14664 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____14664)))
in (match (uu____14662) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (check_term1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp)))))
end
| uu____14676 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs1, binders, comp, flags) -> begin
(

let uu____14687 = (

let uu____14689 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____14689)))
in (match (uu____14687) with
| true -> begin
(

let arrow1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))) FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng)
in (check_term1 l univs1 arrow1))
end
| uu____14708 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_main (uu____14710) -> begin
()
end
| FStar_Syntax_Syntax.Sig_assume (uu____14711) -> begin
()
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____14718) -> begin
()
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____14719) -> begin
()
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____14720) -> begin
()
end
| FStar_Syntax_Syntax.Sig_splice (uu____14721) -> begin
()
end
| FStar_Syntax_Syntax.Sig_pragma (uu____14728) -> begin
()
end))
in (

let uu____14729 = (FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Parser_Const.prims_lid)
in (match (uu____14729) with
| true -> begin
()
end
| uu____14732 -> begin
(FStar_List.iter check_sigelt exports)
end)))))))


let extract_interface : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.modul = (fun en m -> (

let is_abstract = (FStar_List.contains FStar_Syntax_Syntax.Abstract)
in (

let is_irreducible1 = (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
in (

let is_assume = (FStar_List.contains FStar_Syntax_Syntax.Assumption)
in (

let filter_out_abstract = (FStar_List.filter (fun q -> (not ((((Prims.op_Equality q FStar_Syntax_Syntax.Abstract) || (Prims.op_Equality q FStar_Syntax_Syntax.Irreducible)) || (Prims.op_Equality q FStar_Syntax_Syntax.Visible_default))))))
in (

let filter_out_abstract_and_noeq = (FStar_List.filter (fun q -> (not ((((((Prims.op_Equality q FStar_Syntax_Syntax.Abstract) || (Prims.op_Equality q FStar_Syntax_Syntax.Noeq)) || (Prims.op_Equality q FStar_Syntax_Syntax.Unopteq)) || (Prims.op_Equality q FStar_Syntax_Syntax.Irreducible)) || (Prims.op_Equality q FStar_Syntax_Syntax.Visible_default))))))
in (

let filter_out_abstract_and_inline = (FStar_List.filter (fun q -> (not ((((((Prims.op_Equality q FStar_Syntax_Syntax.Abstract) || (Prims.op_Equality q FStar_Syntax_Syntax.Irreducible)) || (Prims.op_Equality q FStar_Syntax_Syntax.Visible_default)) || (Prims.op_Equality q FStar_Syntax_Syntax.Inline_for_extraction)) || (Prims.op_Equality q FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))))))
in (

let abstract_inductive_tycons = (FStar_Util.mk_ref [])
in (

let abstract_inductive_datacons = (FStar_Util.mk_ref [])
in (

let is_projector_or_discriminator_of_an_abstract_inductive = (fun quals -> (FStar_List.existsML (fun q -> (match (q) with
| FStar_Syntax_Syntax.Discriminator (l) -> begin
true
end
| FStar_Syntax_Syntax.Projector (l, uu____14835) -> begin
true
end
| uu____14837 -> begin
false
end)) quals))
in (

let vals_of_abstract_inductive = (fun s -> (

let mk_typ_for_abstract_inductive = (fun bs t r -> (match (bs) with
| [] -> begin
t
end
| uu____14867 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs', c) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((((FStar_List.append bs bs')), (c)))) FStar_Pervasives_Native.None r)
end
| uu____14906 -> begin
(

let uu____14907 = (

let uu____14914 = (

let uu____14915 = (

let uu____14930 = (FStar_Syntax_Syntax.mk_Total t)
in ((bs), (uu____14930)))
in FStar_Syntax_Syntax.Tm_arrow (uu____14915))
in (FStar_Syntax_Syntax.mk uu____14914))
in (uu____14907 FStar_Pervasives_Native.None r))
end)
end))
in (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, bs, t, uu____14947, uu____14948) -> begin
(

let s1 = (

let uu___1952_14958 = s
in (

let uu____14959 = (

let uu____14960 = (

let uu____14967 = (mk_typ_for_abstract_inductive bs t s.FStar_Syntax_Syntax.sigrng)
in ((lid), (uvs), (uu____14967)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____14960))
in (

let uu____14968 = (

let uu____14971 = (

let uu____14974 = (filter_out_abstract_and_noeq s.FStar_Syntax_Syntax.sigquals)
in (FStar_Syntax_Syntax.New)::uu____14974)
in (FStar_Syntax_Syntax.Assumption)::uu____14971)
in {FStar_Syntax_Syntax.sigel = uu____14959; FStar_Syntax_Syntax.sigrng = uu___1952_14958.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu____14968; FStar_Syntax_Syntax.sigmeta = uu___1952_14958.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___1952_14958.FStar_Syntax_Syntax.sigattrs})))
in (s1)::[])
end
| uu____14977 -> begin
(failwith "Impossible!")
end)))
in (

let val_of_lb = (fun s lid uu____15002 lbdef -> (match (uu____15002) with
| (uvs, t) -> begin
(

let attrs = (

let uu____15013 = (FStar_TypeChecker_Util.must_erase_for_extraction en lbdef)
in (match (uu____15013) with
| true -> begin
(

let uu____15018 = (

let uu____15019 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.must_erase_for_extraction_attr FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_All.pipe_right uu____15019 FStar_Syntax_Syntax.fv_to_tm))
in (uu____15018)::s.FStar_Syntax_Syntax.sigattrs)
end
| uu____15020 -> begin
s.FStar_Syntax_Syntax.sigattrs
end))
in (

let uu___1965_15022 = s
in (

let uu____15023 = (

let uu____15026 = (filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals)
in (FStar_Syntax_Syntax.Assumption)::uu____15026)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (uvs), (t))); FStar_Syntax_Syntax.sigrng = uu___1965_15022.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu____15023; FStar_Syntax_Syntax.sigmeta = uu___1965_15022.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = attrs})))
end))
in (

let should_keep_lbdef = (fun t -> (

let comp_effect_name1 = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
c1.FStar_Syntax_Syntax.effect_name
end
| uu____15044 -> begin
(failwith "Impossible!")
end))
in (

let c_opt = (

let uu____15051 = (FStar_Syntax_Util.is_unit t)
in (match (uu____15051) with
| true -> begin
(

let uu____15058 = (FStar_Syntax_Syntax.mk_Total t)
in FStar_Pervasives_Native.Some (uu____15058))
end
| uu____15063 -> begin
(

let uu____15065 = (

let uu____15066 = (FStar_Syntax_Subst.compress t)
in uu____15066.FStar_Syntax_Syntax.n)
in (match (uu____15065) with
| FStar_Syntax_Syntax.Tm_arrow (uu____15073, c) -> begin
FStar_Pervasives_Native.Some (c)
end
| uu____15097 -> begin
FStar_Pervasives_Native.None
end))
end))
in (match (c_opt) with
| FStar_Pervasives_Native.None -> begin
true
end
| FStar_Pervasives_Native.Some (c) -> begin
(

let uu____15109 = (FStar_Syntax_Util.is_lemma_comp c)
in (match (uu____15109) with
| true -> begin
false
end
| uu____15114 -> begin
(

let uu____15116 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (match (uu____15116) with
| true -> begin
true
end
| uu____15121 -> begin
(

let uu____15123 = (comp_effect_name1 c)
in (FStar_TypeChecker_Env.is_reifiable_effect en uu____15123))
end))
end))
end))))
in (

let extract_sigelt = (fun s -> ((

let uu____15135 = (FStar_TypeChecker_Env.debug en FStar_Options.Extreme)
in (match (uu____15135) with
| true -> begin
(

let uu____15138 = (FStar_Syntax_Print.sigelt_to_string s)
in (FStar_Util.print1 "Extracting interface for %s\n" uu____15138))
end
| uu____15141 -> begin
()
end));
(match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____15145) -> begin
(failwith "Impossible! extract_interface: bare data constructor")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____15165) -> begin
(failwith "Impossible! extract_interface: bare data constructor")
end
| FStar_Syntax_Syntax.Sig_splice (uu____15184) -> begin
(failwith "Impossible! extract_interface: trying to extract splice")
end
| FStar_Syntax_Syntax.Sig_bundle (sigelts, lidents1) -> begin
(match ((is_abstract s.FStar_Syntax_Syntax.sigquals)) with
| true -> begin
(FStar_All.pipe_right sigelts (FStar_List.fold_left (fun sigelts1 s1 -> (match (s1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____15230, uu____15231, uu____15232, uu____15233, uu____15234) -> begin
((

let uu____15244 = (

let uu____15247 = (FStar_ST.op_Bang abstract_inductive_tycons)
in (lid)::uu____15247)
in (FStar_ST.op_Colon_Equals abstract_inductive_tycons uu____15244));
(

let uu____15296 = (vals_of_abstract_inductive s1)
in (FStar_List.append uu____15296 sigelts1));
)
end
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____15300, uu____15301, uu____15302, uu____15303, uu____15304) -> begin
((

let uu____15312 = (

let uu____15315 = (FStar_ST.op_Bang abstract_inductive_datacons)
in (lid)::uu____15315)
in (FStar_ST.op_Colon_Equals abstract_inductive_datacons uu____15312));
sigelts1;
)
end
| uu____15364 -> begin
(failwith "Impossible! extract_interface: Sig_bundle can\'t have anything other than Sig_inductive_typ and Sig_datacon")
end)) []))
end
| uu____15368 -> begin
(s)::[]
end)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) -> begin
(

let uu____15373 = (is_projector_or_discriminator_of_an_abstract_inductive s.FStar_Syntax_Syntax.sigquals)
in (match (uu____15373) with
| true -> begin
[]
end
| uu____15378 -> begin
(match ((is_assume s.FStar_Syntax_Syntax.sigquals)) with
| true -> begin
(

let uu____15383 = (

let uu___2029_15384 = s
in (

let uu____15385 = (filter_out_abstract s.FStar_Syntax_Syntax.sigquals)
in {FStar_Syntax_Syntax.sigel = uu___2029_15384.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___2029_15384.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu____15385; FStar_Syntax_Syntax.sigmeta = uu___2029_15384.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___2029_15384.FStar_Syntax_Syntax.sigattrs}))
in (uu____15383)::[])
end
| uu____15388 -> begin
[]
end)
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, lids) -> begin
(

let uu____15396 = (is_projector_or_discriminator_of_an_abstract_inductive s.FStar_Syntax_Syntax.sigquals)
in (match (uu____15396) with
| true -> begin
[]
end
| uu____15401 -> begin
(

let uu____15403 = lbs
in (match (uu____15403) with
| (flbs, slbs) -> begin
(

let typs_and_defs = (FStar_All.pipe_right slbs (FStar_List.map (fun lb -> ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (lb.FStar_Syntax_Syntax.lbdef)))))
in (

let is_lemma1 = (FStar_List.existsML (fun uu____15465 -> (match (uu____15465) with
| (uu____15473, t, uu____15475) -> begin
(FStar_All.pipe_right t FStar_Syntax_Util.is_lemma)
end)) typs_and_defs)
in (

let vals = (FStar_List.map2 (fun lid uu____15492 -> (match (uu____15492) with
| (u, t, d) -> begin
(val_of_lb s lid ((u), (t)) d)
end)) lids typs_and_defs)
in (match ((((is_abstract s.FStar_Syntax_Syntax.sigquals) || (is_irreducible1 s.FStar_Syntax_Syntax.sigquals)) || is_lemma1)) with
| true -> begin
vals
end
| uu____15505 -> begin
(

let should_keep_defs = (FStar_List.existsML (fun uu____15519 -> (match (uu____15519) with
| (uu____15527, t, uu____15529) -> begin
(FStar_All.pipe_right t should_keep_lbdef)
end)) typs_and_defs)
in (match (should_keep_defs) with
| true -> begin
(s)::[]
end
| uu____15534 -> begin
vals
end))
end))))
end))
end))
end
| FStar_Syntax_Syntax.Sig_main (t) -> begin
(failwith "Did not anticipate main would arise when extracting interfaces!")
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____15541, uu____15542) -> begin
(

let is_haseq = (FStar_TypeChecker_TcInductive.is_haseq_lid lid)
in (match (is_haseq) with
| true -> begin
(

let is_haseq_of_abstract_inductive = (

let uu____15550 = (FStar_ST.op_Bang abstract_inductive_tycons)
in (FStar_List.existsML (fun l -> (

let uu____15579 = (FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l)
in (FStar_Ident.lid_equals lid uu____15579))) uu____15550))
in (match (is_haseq_of_abstract_inductive) with
| true -> begin
(

let uu____15583 = (

let uu___2071_15584 = s
in (

let uu____15585 = (filter_out_abstract s.FStar_Syntax_Syntax.sigquals)
in {FStar_Syntax_Syntax.sigel = uu___2071_15584.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___2071_15584.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu____15585; FStar_Syntax_Syntax.sigmeta = uu___2071_15584.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___2071_15584.FStar_Syntax_Syntax.sigattrs}))
in (uu____15583)::[])
end
| uu____15588 -> begin
[]
end))
end
| uu____15590 -> begin
(

let uu____15592 = (

let uu___2073_15593 = s
in (

let uu____15594 = (filter_out_abstract s.FStar_Syntax_Syntax.sigquals)
in {FStar_Syntax_Syntax.sigel = uu___2073_15593.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___2073_15593.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu____15594; FStar_Syntax_Syntax.sigmeta = uu___2073_15593.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___2073_15593.FStar_Syntax_Syntax.sigattrs}))
in (uu____15592)::[])
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____15597) -> begin
(s)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____15598) -> begin
(s)::[]
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____15599) -> begin
(s)::[]
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____15600) -> begin
(s)::[]
end
| FStar_Syntax_Syntax.Sig_pragma (uu____15613) -> begin
(s)::[]
end);
))
in (

let uu___2085_15614 = m
in (

let uu____15615 = (

let uu____15616 = (FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations (FStar_List.map extract_sigelt))
in (FStar_All.pipe_right uu____15616 FStar_List.flatten))
in {FStar_Syntax_Syntax.name = uu___2085_15614.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu____15615; FStar_Syntax_Syntax.exports = uu___2085_15614.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = true}))))))))))))))))


let snapshot_context : FStar_TypeChecker_Env.env  ->  Prims.string  ->  ((Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t * Prims.int) * FStar_TypeChecker_Env.env) = (fun env msg -> (FStar_Util.atomically (fun uu____15667 -> (FStar_TypeChecker_Env.snapshot env msg))))


let rollback_context : FStar_TypeChecker_Env.solver_t  ->  Prims.string  ->  (Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t * Prims.int) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env = (fun solver msg depth -> (FStar_Util.atomically (fun uu____15714 -> (

let env = (FStar_TypeChecker_Env.rollback solver msg depth)
in env))))


let push_context : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Env.env = (fun env msg -> (

let uu____15729 = (snapshot_context env msg)
in (FStar_Pervasives_Native.snd uu____15729)))


let pop_context : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Env.env = (fun env msg -> (rollback_context env.FStar_TypeChecker_Env.solver msg FStar_Pervasives_Native.None))


let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (

let verify = (FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let action = (match (verify) with
| true -> begin
"Verifying"
end
| uu____15806 -> begin
"Lax-checking"
end)
in (

let label1 = (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____15814 -> begin
"implementation"
end)
in ((

let uu____15818 = (FStar_Options.debug_any ())
in (match (uu____15818) with
| true -> begin
(FStar_Util.print3 "%s %s of %s\n" action label1 modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
end
| uu____15822 -> begin
()
end));
(

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____15830 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let env1 = (

let uu___2110_15834 = env
in {FStar_TypeChecker_Env.solver = uu___2110_15834.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___2110_15834.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___2110_15834.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___2110_15834.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___2110_15834.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___2110_15834.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___2110_15834.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___2110_15834.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___2110_15834.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___2110_15834.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___2110_15834.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___2110_15834.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___2110_15834.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___2110_15834.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___2110_15834.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___2110_15834.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___2110_15834.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___2110_15834.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = (not (verify)); FStar_TypeChecker_Env.lax = uu___2110_15834.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___2110_15834.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___2110_15834.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___2110_15834.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___2110_15834.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___2110_15834.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___2110_15834.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___2110_15834.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___2110_15834.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___2110_15834.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___2110_15834.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___2110_15834.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___2110_15834.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___2110_15834.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___2110_15834.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___2110_15834.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___2110_15834.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___2110_15834.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___2110_15834.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___2110_15834.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___2110_15834.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___2110_15834.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___2110_15834.FStar_TypeChecker_Env.nbe})
in (

let env2 = (FStar_TypeChecker_Env.set_current_module env1 modul.FStar_Syntax_Syntax.name)
in (

let uu____15836 = (tc_decls env2 modul.FStar_Syntax_Syntax.declarations)
in (match (uu____15836) with
| (ses, exports, env3) -> begin
(((

let uu___2118_15869 = modul
in {FStar_Syntax_Syntax.name = uu___2118_15869.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = uu___2118_15869.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___2118_15869.FStar_Syntax_Syntax.is_interface})), (exports), (env3))
end)))));
)))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let uu____15898 = (tc_decls env decls)
in (match (uu____15898) with
| (ses, exports, env1) -> begin
(

let modul1 = (

let uu___2127_15929 = modul
in {FStar_Syntax_Syntax.name = uu___2127_15929.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = uu___2127_15929.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___2127_15929.FStar_Syntax_Syntax.is_interface})
in ((modul1), (exports), (env1)))
end)))


let rec tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.bool  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env0 m iface_exists -> (

let msg = (Prims.op_Hat "Internals for " m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let env01 = (push_context env0 msg)
in (

let uu____15990 = (tc_partial_modul env01 m)
in (match (uu____15990) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul false iface_exists env modul non_private_decls)
end)))))
and finish_partial_modul : Prims.bool  ->  Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun loading_from_cache iface_exists en m exports -> (

let should_extract_interface = (((((not (loading_from_cache)) && (not (iface_exists))) && (FStar_Options.use_extracted_interfaces ())) && (not (m.FStar_Syntax_Syntax.is_interface))) && (

let uu____16027 = (FStar_Errors.get_err_count ())
in (Prims.op_Equality uu____16027 (Prims.parse_int "0"))))
in (match (should_extract_interface) with
| true -> begin
(

let modul_iface = (extract_interface en m)
in ((

let uu____16038 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug en) FStar_Options.Low)
in (match (uu____16038) with
| true -> begin
(

let uu____16042 = (

let uu____16044 = (FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____16044) with
| true -> begin
""
end
| uu____16049 -> begin
" (in lax mode) "
end))
in (

let uu____16052 = (

let uu____16054 = (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____16054) with
| true -> begin
(

let uu____16058 = (

let uu____16060 = (FStar_Syntax_Print.modul_to_string m)
in (Prims.op_Hat uu____16060 "\n"))
in (Prims.op_Hat "\nfrom: " uu____16058))
end
| uu____16064 -> begin
""
end))
in (

let uu____16067 = (

let uu____16069 = (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____16069) with
| true -> begin
(

let uu____16073 = (

let uu____16075 = (FStar_Syntax_Print.modul_to_string modul_iface)
in (Prims.op_Hat uu____16075 "\n"))
in (Prims.op_Hat "\nto: " uu____16073))
end
| uu____16079 -> begin
""
end))
in (FStar_Util.print4 "Extracting and type checking module %s interface%s%s%s\n" m.FStar_Syntax_Syntax.name.FStar_Ident.str uu____16042 uu____16052 uu____16067))))
end
| uu____16083 -> begin
()
end));
(

let en0 = (

let en0 = (pop_context en (Prims.op_Hat "Ending modul " m.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (

let en01 = (

let uu___2153_16089 = en0
in {FStar_TypeChecker_Env.solver = uu___2153_16089.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___2153_16089.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___2153_16089.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___2153_16089.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___2153_16089.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___2153_16089.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___2153_16089.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___2153_16089.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___2153_16089.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___2153_16089.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___2153_16089.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___2153_16089.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___2153_16089.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___2153_16089.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___2153_16089.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___2153_16089.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___2153_16089.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___2153_16089.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___2153_16089.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___2153_16089.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___2153_16089.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___2153_16089.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___2153_16089.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___2153_16089.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___2153_16089.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___2153_16089.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___2153_16089.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___2153_16089.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___2153_16089.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___2153_16089.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___2153_16089.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___2153_16089.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___2153_16089.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___2153_16089.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___2153_16089.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___2153_16089.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___2153_16089.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___2153_16089.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___2153_16089.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___2153_16089.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___2153_16089.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = en.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___2153_16089.FStar_TypeChecker_Env.nbe})
in (

let en02 = (

let uu___2156_16091 = en01
in (

let uu____16092 = (

let uu____16107 = (FStar_All.pipe_right en.FStar_TypeChecker_Env.qtbl_name_and_index FStar_Pervasives_Native.fst)
in ((uu____16107), (FStar_Pervasives_Native.None)))
in {FStar_TypeChecker_Env.solver = uu___2156_16091.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___2156_16091.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___2156_16091.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___2156_16091.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___2156_16091.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___2156_16091.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___2156_16091.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___2156_16091.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___2156_16091.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___2156_16091.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___2156_16091.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___2156_16091.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___2156_16091.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___2156_16091.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___2156_16091.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___2156_16091.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___2156_16091.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___2156_16091.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___2156_16091.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___2156_16091.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___2156_16091.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___2156_16091.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___2156_16091.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___2156_16091.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___2156_16091.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___2156_16091.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___2156_16091.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___2156_16091.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___2156_16091.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___2156_16091.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___2156_16091.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu____16092; FStar_TypeChecker_Env.normalized_eff_names = uu___2156_16091.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___2156_16091.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___2156_16091.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___2156_16091.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___2156_16091.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___2156_16091.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___2156_16091.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___2156_16091.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___2156_16091.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___2156_16091.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___2156_16091.FStar_TypeChecker_Env.nbe}))
in (

let uu____16153 = (

let uu____16155 = (FStar_Options.interactive ())
in (not (uu____16155)))
in (match (uu____16153) with
| true -> begin
((

let uu____16159 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right uu____16159 (fun a3 -> ())));
(z3_reset_options en02);
)
end
| uu____16161 -> begin
en02
end)))))
in (

let uu____16163 = (tc_modul en0 modul_iface true)
in (match (uu____16163) with
| (modul_iface1, env) -> begin
(((

let uu___2165_16176 = m
in {FStar_Syntax_Syntax.name = uu___2165_16176.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu___2165_16176.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = modul_iface1.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___2165_16176.FStar_Syntax_Syntax.is_interface})), (env))
end)));
))
end
| uu____16177 -> begin
(

let modul = (

let uu___2167_16180 = m
in {FStar_Syntax_Syntax.name = uu___2167_16180.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu___2167_16180.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = uu___2167_16180.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module en modul)
in ((

let uu____16183 = (FStar_All.pipe_right env.FStar_TypeChecker_Env.qtbl_name_and_index FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____16183 FStar_Util.smap_clear));
(

let uu____16219 = (((

let uu____16223 = (FStar_Options.lax ())
in (not (uu____16223))) && (not (loading_from_cache))) && (

let uu____16226 = (FStar_Options.use_extracted_interfaces ())
in (not (uu____16226))))
in (match (uu____16219) with
| true -> begin
(check_exports env modul exports)
end
| uu____16229 -> begin
()
end));
(

let uu____16232 = (pop_context env (Prims.op_Hat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (FStar_All.pipe_right uu____16232 (fun a4 -> ())));
((modul), (env));
)))
end)))


let load_checked_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_TypeChecker_Env.env = (fun en m -> (

let env = (FStar_TypeChecker_Env.set_current_module en m.FStar_Syntax_Syntax.name)
in (

let env1 = (

let uu____16247 = (

let uu____16249 = (FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name)
in (Prims.op_Hat "Internals for " uu____16249))
in (push_context env uu____16247))
in (

let env2 = (FStar_List.fold_left (fun env2 se -> (

let env3 = (FStar_TypeChecker_Env.push_sigelt env2 se)
in (

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in ((FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (

let uu____16270 = (FStar_TypeChecker_Env.try_lookup_lid env3 lid)
in ()))));
env3;
)))) env1 m.FStar_Syntax_Syntax.declarations)
in (

let uu____16281 = (finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports)
in (match (uu____16281) with
| (uu____16288, env3) -> begin
env3
end))))))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.bool  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m b -> ((

let uu____16313 = (FStar_Options.debug_any ())
in (match (uu____16313) with
| true -> begin
(

let uu____16316 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (match (m.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"i\'face"
end
| uu____16322 -> begin
"module"
end) uu____16316))
end
| uu____16325 -> begin
()
end));
(

let uu____16328 = (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____16328) with
| true -> begin
(

let uu____16331 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "Module before type checking:\n%s\n" uu____16331))
end
| uu____16334 -> begin
()
end));
(

let env1 = (

let uu___2197_16337 = env
in (

let uu____16338 = (

let uu____16340 = (FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (not (uu____16340)))
in {FStar_TypeChecker_Env.solver = uu___2197_16337.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___2197_16337.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___2197_16337.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___2197_16337.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___2197_16337.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___2197_16337.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___2197_16337.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___2197_16337.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___2197_16337.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___2197_16337.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___2197_16337.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___2197_16337.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___2197_16337.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___2197_16337.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___2197_16337.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___2197_16337.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___2197_16337.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___2197_16337.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___2197_16337.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___2197_16337.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu____16338; FStar_TypeChecker_Env.lax_universes = uu___2197_16337.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___2197_16337.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___2197_16337.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___2197_16337.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___2197_16337.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___2197_16337.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___2197_16337.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___2197_16337.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___2197_16337.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___2197_16337.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___2197_16337.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___2197_16337.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___2197_16337.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___2197_16337.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___2197_16337.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___2197_16337.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___2197_16337.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___2197_16337.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___2197_16337.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___2197_16337.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___2197_16337.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___2197_16337.FStar_TypeChecker_Env.nbe}))
in (

let uu____16342 = (tc_modul env1 m b)
in (match (uu____16342) with
| (m1, env2) -> begin
((

let uu____16354 = (FStar_Options.dump_module m1.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____16354) with
| true -> begin
(

let uu____16357 = (FStar_Syntax_Print.modul_to_string m1)
in (FStar_Util.print1 "Module after type checking:\n%s\n" uu____16357))
end
| uu____16360 -> begin
()
end));
(

let uu____16363 = ((FStar_Options.dump_module m1.FStar_Syntax_Syntax.name.FStar_Ident.str) && (FStar_Options.debug_at_level m1.FStar_Syntax_Syntax.name.FStar_Ident.str (FStar_Options.Other ("Normalize"))))
in (match (uu____16363) with
| true -> begin
(

let normalize_toplevel_lets = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((b1, lbs), ids) -> begin
(

let n1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Reify)::(FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]))
in (

let update = (fun lb -> (

let uu____16401 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____16401) with
| (univnames1, e) -> begin
(

let uu___2219_16408 = lb
in (

let uu____16409 = (

let uu____16412 = (FStar_TypeChecker_Env.push_univ_vars env2 univnames1)
in (n1 uu____16412 e))
in {FStar_Syntax_Syntax.lbname = uu___2219_16408.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___2219_16408.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___2219_16408.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___2219_16408.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____16409; FStar_Syntax_Syntax.lbattrs = uu___2219_16408.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___2219_16408.FStar_Syntax_Syntax.lbpos}))
end)))
in (

let uu___2221_16413 = se
in (

let uu____16414 = (

let uu____16415 = (

let uu____16422 = (

let uu____16423 = (FStar_List.map update lbs)
in ((b1), (uu____16423)))
in ((uu____16422), (ids)))
in FStar_Syntax_Syntax.Sig_let (uu____16415))
in {FStar_Syntax_Syntax.sigel = uu____16414; FStar_Syntax_Syntax.sigrng = uu___2221_16413.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___2221_16413.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___2221_16413.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___2221_16413.FStar_Syntax_Syntax.sigattrs}))))
end
| uu____16431 -> begin
se
end))
in (

let normalized_module = (

let uu___2225_16433 = m1
in (

let uu____16434 = (FStar_List.map normalize_toplevel_lets m1.FStar_Syntax_Syntax.declarations)
in {FStar_Syntax_Syntax.name = uu___2225_16433.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu____16434; FStar_Syntax_Syntax.exports = uu___2225_16433.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___2225_16433.FStar_Syntax_Syntax.is_interface}))
in (

let uu____16435 = (FStar_Syntax_Print.modul_to_string normalized_module)
in (FStar_Util.print1 "%s\n" uu____16435))))
end
| uu____16438 -> begin
()
end));
((m1), (env2));
)
end)));
))




