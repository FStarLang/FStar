
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
| uu____41 -> begin
(Prims.parse_int "0")
end)))
in (

let uu____42 = (FStar_Options.reuse_hint_for ())
in (match (uu____42) with
| FStar_Pervasives_Native.Some (l) -> begin
(

let lid = (

let uu____47 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_add_suffix uu____47 l))
in (

let uu___64_48 = env
in (

let uu____49 = (

let uu____62 = (

let uu____69 = (

let uu____74 = (get_n lid)
in ((lid), (uu____74)))
in FStar_Pervasives_Native.Some (uu____69))
in ((tbl), (uu____62)))
in {FStar_TypeChecker_Env.solver = uu___64_48.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___64_48.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___64_48.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___64_48.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___64_48.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___64_48.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___64_48.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___64_48.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___64_48.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___64_48.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___64_48.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___64_48.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___64_48.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___64_48.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___64_48.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___64_48.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___64_48.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___64_48.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___64_48.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___64_48.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___64_48.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___64_48.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___64_48.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___64_48.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___64_48.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___64_48.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___64_48.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu____49; FStar_TypeChecker_Env.proof_ns = uu___64_48.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___64_48.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___64_48.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___64_48.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___64_48.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___64_48.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___64_48.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___64_48.FStar_TypeChecker_Env.dep_graph})))
end
| FStar_Pervasives_Native.None -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (

let lid = (match (lids) with
| [] -> begin
(

let uu____91 = (FStar_TypeChecker_Env.current_module env)
in (

let uu____92 = (

let uu____93 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_right uu____93 FStar_Util.string_of_int))
in (FStar_Ident.lid_add_suffix uu____91 uu____92)))
end
| (l)::uu____95 -> begin
l
end)
in (

let uu___65_98 = env
in (

let uu____99 = (

let uu____112 = (

let uu____119 = (

let uu____124 = (get_n lid)
in ((lid), (uu____124)))
in FStar_Pervasives_Native.Some (uu____119))
in ((tbl), (uu____112)))
in {FStar_TypeChecker_Env.solver = uu___65_98.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___65_98.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___65_98.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___65_98.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___65_98.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___65_98.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___65_98.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___65_98.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___65_98.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___65_98.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___65_98.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___65_98.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___65_98.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___65_98.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___65_98.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___65_98.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___65_98.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___65_98.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___65_98.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___65_98.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___65_98.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___65_98.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___65_98.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___65_98.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___65_98.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___65_98.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___65_98.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu____99; FStar_TypeChecker_Env.proof_ns = uu___65_98.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___65_98.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___65_98.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___65_98.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___65_98.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___65_98.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___65_98.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___65_98.FStar_TypeChecker_Env.dep_graph}))))
end)))))


let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_Options.log_types ()) && (

let uu____141 = (

let uu____142 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____142))
in (not (uu____141)))))


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let uu____152 = (FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k)
in (match (uu____152) with
| (t1, c, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
t1;
)
end)))


let recheck_debug : Prims.string  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s env t -> ((

let uu____173 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____173) with
| true -> begin
(

let uu____174 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Term has been %s-transformed to:\n%s\n----------\n" s uu____174))
end
| uu____175 -> begin
()
end));
(

let uu____176 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (uu____176) with
| (t', uu____184, uu____185) -> begin
((

let uu____187 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____187) with
| true -> begin
(

let uu____188 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print1 "Re-checked; got:\n%s\n----------\n" uu____188))
end
| uu____189 -> begin
()
end));
t;
)
end));
))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (

let uu____199 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env uu____199)))


let check_nogen : 'Auu____204 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  ('Auu____204 Prims.list * FStar_Syntax_Syntax.term) = (fun env t k -> (

let t1 = (tc_check_trivial_guard env t k)
in (

let uu____224 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t1)
in (([]), (uu____224)))))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun env m s -> (

let fail1 = (fun uu____251 -> (

let uu____252 = (FStar_TypeChecker_Err.unexpected_signature_for_monad env m s)
in (FStar_Errors.raise_error uu____252 (FStar_Ident.range_of_lid m))))
in (

let s1 = (FStar_Syntax_Subst.compress s)
in (match (s1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs1 = (FStar_Syntax_Subst.open_binders bs)
in (match (bs1) with
| ((a, uu____296))::((wp, uu____298))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____313 -> begin
(fail1 ())
end))
end
| uu____314 -> begin
(fail1 ())
end))))


let tc_eff_decl : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (

let uu____321 = (FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs)
in (match (uu____321) with
| (open_annotated_univs, annotated_univ_names) -> begin
(

let open_univs = (fun n_binders t -> (

let uu____347 = (FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs)
in (FStar_Syntax_Subst.subst uu____347 t)))
in (

let open_univs_binders = (fun n_binders bs -> (

let uu____357 = (FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs)
in (FStar_Syntax_Subst.subst_binders uu____357 bs)))
in (

let n_effect_params = (FStar_List.length ed.FStar_Syntax_Syntax.binders)
in (

let uu____365 = (

let uu____372 = (open_univs_binders (Prims.parse_int "0") ed.FStar_Syntax_Syntax.binders)
in (

let uu____373 = (open_univs n_effect_params ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Subst.open_term' uu____372 uu____373)))
in (match (uu____365) with
| (effect_params_un, signature_un, opening) -> begin
(

let uu____383 = (FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un)
in (match (uu____383) with
| (effect_params, env, uu____392) -> begin
(

let uu____393 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (uu____393) with
| (signature, uu____399) -> begin
(

let ed1 = (

let uu___66_401 = ed
in {FStar_Syntax_Syntax.cattributes = uu___66_401.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___66_401.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___66_401.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = uu___66_401.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = uu___66_401.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = uu___66_401.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = uu___66_401.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = uu___66_401.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = uu___66_401.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = uu___66_401.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = uu___66_401.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = uu___66_401.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = uu___66_401.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = uu___66_401.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = uu___66_401.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = uu___66_401.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = uu___66_401.FStar_Syntax_Syntax.actions; FStar_Syntax_Syntax.eff_attrs = uu___66_401.FStar_Syntax_Syntax.eff_attrs})
in (

let ed2 = (match (((effect_params), (annotated_univ_names))) with
| ([], []) -> begin
ed1
end
| uu____417 -> begin
(

let op = (fun uu____439 -> (match (uu____439) with
| (us, t) -> begin
(

let n_us = (FStar_List.length us)
in (

let uu____459 = (

let uu____460 = (FStar_Syntax_Subst.shift_subst n_us opening)
in (

let uu____469 = (open_univs n_us t)
in (FStar_Syntax_Subst.subst uu____460 uu____469)))
in ((us), (uu____459))))
end))
in (

let uu___67_478 = ed1
in (

let uu____479 = (op ed1.FStar_Syntax_Syntax.ret_wp)
in (

let uu____480 = (op ed1.FStar_Syntax_Syntax.bind_wp)
in (

let uu____481 = (op ed1.FStar_Syntax_Syntax.if_then_else)
in (

let uu____482 = (op ed1.FStar_Syntax_Syntax.ite_wp)
in (

let uu____483 = (op ed1.FStar_Syntax_Syntax.stronger)
in (

let uu____484 = (op ed1.FStar_Syntax_Syntax.close_wp)
in (

let uu____485 = (op ed1.FStar_Syntax_Syntax.assert_p)
in (

let uu____486 = (op ed1.FStar_Syntax_Syntax.assume_p)
in (

let uu____487 = (op ed1.FStar_Syntax_Syntax.null_wp)
in (

let uu____488 = (op ed1.FStar_Syntax_Syntax.trivial)
in (

let uu____489 = (

let uu____490 = (op (([]), (ed1.FStar_Syntax_Syntax.repr)))
in (FStar_Pervasives_Native.snd uu____490))
in (

let uu____501 = (op ed1.FStar_Syntax_Syntax.return_repr)
in (

let uu____502 = (op ed1.FStar_Syntax_Syntax.bind_repr)
in (

let uu____503 = (FStar_List.map (fun a -> (

let uu___68_511 = a
in (

let uu____512 = (

let uu____513 = (op ((a.FStar_Syntax_Syntax.action_univs), (a.FStar_Syntax_Syntax.action_defn)))
in (FStar_Pervasives_Native.snd uu____513))
in (

let uu____522 = (

let uu____523 = (op ((a.FStar_Syntax_Syntax.action_univs), (a.FStar_Syntax_Syntax.action_typ)))
in (FStar_Pervasives_Native.snd uu____523))
in {FStar_Syntax_Syntax.action_name = uu___68_511.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___68_511.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___68_511.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = uu___68_511.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = uu____512; FStar_Syntax_Syntax.action_typ = uu____522})))) ed1.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.cattributes = uu___67_478.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___67_478.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = annotated_univ_names; FStar_Syntax_Syntax.binders = uu___67_478.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = uu___67_478.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = uu____479; FStar_Syntax_Syntax.bind_wp = uu____480; FStar_Syntax_Syntax.if_then_else = uu____481; FStar_Syntax_Syntax.ite_wp = uu____482; FStar_Syntax_Syntax.stronger = uu____483; FStar_Syntax_Syntax.close_wp = uu____484; FStar_Syntax_Syntax.assert_p = uu____485; FStar_Syntax_Syntax.assume_p = uu____486; FStar_Syntax_Syntax.null_wp = uu____487; FStar_Syntax_Syntax.trivial = uu____488; FStar_Syntax_Syntax.repr = uu____489; FStar_Syntax_Syntax.return_repr = uu____501; FStar_Syntax_Syntax.bind_repr = uu____502; FStar_Syntax_Syntax.actions = uu____503; FStar_Syntax_Syntax.eff_attrs = uu___67_478.FStar_Syntax_Syntax.eff_attrs}))))))))))))))))
end)
in (

let wp_with_fresh_result_type = (fun env1 mname signature1 -> (

let fail1 = (fun t -> (

let uu____558 = (FStar_TypeChecker_Err.unexpected_signature_for_monad env1 mname t)
in (FStar_Errors.raise_error uu____558 (FStar_Ident.range_of_lid mname))))
in (

let uu____569 = (

let uu____570 = (FStar_Syntax_Subst.compress signature1)
in uu____570.FStar_Syntax_Syntax.n)
in (match (uu____569) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs1 = (FStar_Syntax_Subst.open_binders bs)
in (match (bs1) with
| ((a, uu____605))::((wp, uu____607))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____622 -> begin
(fail1 signature1)
end))
end
| uu____623 -> begin
(fail1 signature1)
end))))
in (

let uu____624 = (wp_with_fresh_result_type env ed2.FStar_Syntax_Syntax.mname ed2.FStar_Syntax_Syntax.signature)
in (match (uu____624) with
| (a, wp_a) -> begin
(

let fresh_effect_signature = (fun uu____646 -> (match (annotated_univ_names) with
| [] -> begin
(

let uu____653 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (uu____653) with
| (signature1, uu____665) -> begin
(wp_with_fresh_result_type env ed2.FStar_Syntax_Syntax.mname signature1)
end))
end
| uu____666 -> begin
(

let uu____669 = (

let uu____674 = (

let uu____675 = (FStar_Syntax_Subst.close_univ_vars annotated_univ_names signature)
in ((annotated_univ_names), (uu____675)))
in (FStar_TypeChecker_Env.inst_tscheme uu____674))
in (match (uu____669) with
| (uu____684, signature1) -> begin
(wp_with_fresh_result_type env ed2.FStar_Syntax_Syntax.mname signature1)
end))
end))
in (

let env1 = (

let uu____687 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None ed2.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env uu____687))
in ((

let uu____689 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED")))
in (match (uu____689) with
| true -> begin
(

let uu____690 = (FStar_Syntax_Print.lid_to_string ed2.FStar_Syntax_Syntax.mname)
in (

let uu____691 = (FStar_Syntax_Print.binders_to_string " " ed2.FStar_Syntax_Syntax.binders)
in (

let uu____692 = (FStar_Syntax_Print.term_to_string ed2.FStar_Syntax_Syntax.signature)
in (

let uu____693 = (

let uu____694 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Print.term_to_string uu____694))
in (

let uu____695 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.sort)
in (FStar_Util.print5 "Checking effect signature: %s %s : %s\n(a is %s:%s)\n" uu____690 uu____691 uu____692 uu____693 uu____695))))))
end
| uu____696 -> begin
()
end));
(

let check_and_gen' = (fun env2 uu____711 k -> (match (uu____711) with
| (us, t) -> begin
(match (annotated_univ_names) with
| [] -> begin
(check_and_gen env2 t k)
end
| (uu____725)::uu____726 -> begin
(

let uu____729 = (FStar_Syntax_Subst.subst_tscheme open_annotated_univs ((us), (t)))
in (match (uu____729) with
| (us1, t1) -> begin
(

let uu____738 = (FStar_Syntax_Subst.open_univ_vars us1 t1)
in (match (uu____738) with
| (us2, t2) -> begin
(

let uu____745 = (tc_check_trivial_guard env2 t2 k)
in (

let uu____746 = (FStar_Syntax_Subst.close_univ_vars us2 t2)
in ((us2), (uu____746))))
end))
end))
end)
end))
in (

let return_wp = (

let expected_k = (

let uu____751 = (

let uu____758 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____759 = (

let uu____762 = (

let uu____763 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____763))
in (uu____762)::[])
in (uu____758)::uu____759))
in (

let uu____764 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow uu____751 uu____764)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.ret_wp expected_k))
in (

let bind_wp = (

let uu____768 = (fresh_effect_signature ())
in (match (uu____768) with
| (b, wp_b) -> begin
(

let a_wp_b = (

let uu____784 = (

let uu____791 = (

let uu____792 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____792))
in (uu____791)::[])
in (

let uu____793 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____784 uu____793)))
in (

let expected_k = (

let uu____799 = (

let uu____806 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Syntax.t_range)
in (

let uu____807 = (

let uu____810 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____811 = (

let uu____814 = (FStar_Syntax_Syntax.mk_binder b)
in (

let uu____815 = (

let uu____818 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____819 = (

let uu____822 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (uu____822)::[])
in (uu____818)::uu____819))
in (uu____814)::uu____815))
in (uu____810)::uu____811))
in (uu____806)::uu____807))
in (

let uu____823 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____799 uu____823)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else1 = (

let p = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some ((FStar_Ident.range_of_lid ed2.FStar_Syntax_Syntax.mname))) FStar_Syntax_Util.kprop)
in (

let expected_k = (

let uu____831 = (

let uu____838 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____839 = (

let uu____842 = (FStar_Syntax_Syntax.mk_binder p)
in (

let uu____843 = (

let uu____846 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____847 = (

let uu____850 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____850)::[])
in (uu____846)::uu____847))
in (uu____842)::uu____843))
in (uu____838)::uu____839))
in (

let uu____851 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____831 uu____851)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (

let uu____858 = (

let uu____865 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____866 = (

let uu____869 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____869)::[])
in (uu____865)::uu____866))
in (

let uu____870 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____858 uu____870)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let uu____874 = (FStar_Syntax_Util.type_u ())
in (match (uu____874) with
| (t, uu____880) -> begin
(

let expected_k = (

let uu____884 = (

let uu____891 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____892 = (

let uu____895 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____896 = (

let uu____899 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____899)::[])
in (uu____895)::uu____896))
in (uu____891)::uu____892))
in (

let uu____900 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow uu____884 uu____900)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (

let uu____905 = (

let uu____906 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____906 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some ((FStar_Ident.range_of_lid ed2.FStar_Syntax_Syntax.mname))) uu____905))
in (

let b_wp_a = (

let uu____918 = (

let uu____925 = (

let uu____926 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder uu____926))
in (uu____925)::[])
in (

let uu____927 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____918 uu____927)))
in (

let expected_k = (

let uu____933 = (

let uu____940 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____941 = (

let uu____944 = (FStar_Syntax_Syntax.mk_binder b)
in (

let uu____945 = (

let uu____948 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (uu____948)::[])
in (uu____944)::uu____945))
in (uu____940)::uu____941))
in (

let uu____949 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____933 uu____949)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (

let uu____956 = (

let uu____963 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____964 = (

let uu____967 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Util.kprop)
in (

let uu____968 = (

let uu____971 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____971)::[])
in (uu____967)::uu____968))
in (uu____963)::uu____964))
in (

let uu____972 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____956 uu____972)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (

let uu____979 = (

let uu____986 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____987 = (

let uu____990 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Util.kprop)
in (

let uu____991 = (

let uu____994 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____994)::[])
in (uu____990)::uu____991))
in (uu____986)::uu____987))
in (

let uu____995 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____979 uu____995)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (

let uu____1002 = (

let uu____1009 = (FStar_Syntax_Syntax.mk_binder a)
in (uu____1009)::[])
in (

let uu____1010 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1002 uu____1010)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let uu____1014 = (FStar_Syntax_Util.type_u ())
in (match (uu____1014) with
| (t, uu____1020) -> begin
(

let expected_k = (

let uu____1024 = (

let uu____1031 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1032 = (

let uu____1035 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1035)::[])
in (uu____1031)::uu____1032))
in (

let uu____1036 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow uu____1024 uu____1036)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let uu____1039 = (

let uu____1050 = (

let uu____1051 = (FStar_Syntax_Subst.compress ed2.FStar_Syntax_Syntax.repr)
in uu____1051.FStar_Syntax_Syntax.n)
in (match (uu____1050) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((ed2.FStar_Syntax_Syntax.repr), (ed2.FStar_Syntax_Syntax.bind_repr), (ed2.FStar_Syntax_Syntax.return_repr), (ed2.FStar_Syntax_Syntax.actions))
end
| uu____1066 -> begin
(

let repr = (

let uu____1068 = (FStar_Syntax_Util.type_u ())
in (match (uu____1068) with
| (t, uu____1074) -> begin
(

let expected_k = (

let uu____1078 = (

let uu____1085 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1086 = (

let uu____1089 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1089)::[])
in (uu____1085)::uu____1086))
in (

let uu____1090 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow uu____1078 uu____1090)))
in (tc_check_trivial_guard env1 ed2.FStar_Syntax_Syntax.repr expected_k))
end))
in (

let mk_repr' = (fun t wp -> (

let repr1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env1 repr)
in (

let uu____1103 = (

let uu____1106 = (

let uu____1107 = (

let uu____1122 = (

let uu____1125 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____1126 = (

let uu____1129 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____1129)::[])
in (uu____1125)::uu____1126))
in ((repr1), (uu____1122)))
in FStar_Syntax_Syntax.Tm_app (uu____1107))
in (FStar_Syntax_Syntax.mk uu____1106))
in (uu____1103 FStar_Pervasives_Native.None FStar_Range.dummyRange))))
in (

let mk_repr = (fun a1 wp -> (

let uu____1144 = (FStar_Syntax_Syntax.bv_to_name a1)
in (mk_repr' uu____1144 wp)))
in (

let destruct_repr = (fun t -> (

let uu____1157 = (

let uu____1158 = (FStar_Syntax_Subst.compress t)
in uu____1158.FStar_Syntax_Syntax.n)
in (match (uu____1157) with
| FStar_Syntax_Syntax.Tm_app (uu____1169, ((t1, uu____1171))::((wp, uu____1173))::[]) -> begin
((t1), (wp))
end
| uu____1216 -> begin
(failwith "Unexpected repr type")
end)))
in (

let bind_repr = (

let r = (

let uu____1227 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.range_0 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_All.pipe_right uu____1227 FStar_Syntax_Syntax.fv_to_tm))
in (

let uu____1228 = (fresh_effect_signature ())
in (match (uu____1228) with
| (b, wp_b) -> begin
(

let a_wp_b = (

let uu____1244 = (

let uu____1251 = (

let uu____1252 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____1252))
in (uu____1251)::[])
in (

let uu____1253 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____1244 uu____1253)))
in (

let wp_f = (FStar_Syntax_Syntax.gen_bv "wp_f" FStar_Pervasives_Native.None wp_a)
in (

let wp_g = (FStar_Syntax_Syntax.gen_bv "wp_g" FStar_Pervasives_Native.None a_wp_b)
in (

let x_a = (

let uu____1259 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" FStar_Pervasives_Native.None uu____1259))
in (

let wp_g_x = (

let uu____1263 = (

let uu____1264 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (

let uu____1265 = (

let uu____1266 = (

let uu____1267 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____1267))
in (uu____1266)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____1264 uu____1265)))
in (uu____1263 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let res = (

let wp = (

let uu____1276 = (

let uu____1277 = (

let uu____1278 = (FStar_TypeChecker_Env.inst_tscheme bind_wp)
in (FStar_All.pipe_right uu____1278 FStar_Pervasives_Native.snd))
in (

let uu____1287 = (

let uu____1288 = (

let uu____1291 = (

let uu____1294 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____1295 = (

let uu____1298 = (FStar_Syntax_Syntax.bv_to_name b)
in (

let uu____1299 = (

let uu____1302 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (

let uu____1303 = (

let uu____1306 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (uu____1306)::[])
in (uu____1302)::uu____1303))
in (uu____1298)::uu____1299))
in (uu____1294)::uu____1295))
in (r)::uu____1291)
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1288))
in (FStar_Syntax_Syntax.mk_Tm_app uu____1277 uu____1287)))
in (uu____1276 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (mk_repr b wp))
in (

let maybe_range_arg = (

let uu____1312 = (FStar_Util.for_some (FStar_Syntax_Util.attr_eq FStar_Syntax_Util.dm4f_bind_range_attr) ed2.FStar_Syntax_Syntax.eff_attrs)
in (match (uu____1312) with
| true -> begin
(

let uu____1315 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Syntax.t_range)
in (

let uu____1316 = (

let uu____1319 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Syntax.t_range)
in (uu____1319)::[])
in (uu____1315)::uu____1316))
end
| uu____1320 -> begin
[]
end))
in (

let expected_k = (

let uu____1324 = (

let uu____1331 = (

let uu____1334 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1335 = (

let uu____1338 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____1338)::[])
in (uu____1334)::uu____1335))
in (

let uu____1339 = (

let uu____1342 = (

let uu____1345 = (FStar_Syntax_Syntax.mk_binder wp_f)
in (

let uu____1346 = (

let uu____1349 = (

let uu____1350 = (

let uu____1351 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (mk_repr a uu____1351))
in (FStar_Syntax_Syntax.null_binder uu____1350))
in (

let uu____1352 = (

let uu____1355 = (FStar_Syntax_Syntax.mk_binder wp_g)
in (

let uu____1356 = (

let uu____1359 = (

let uu____1360 = (

let uu____1361 = (

let uu____1368 = (FStar_Syntax_Syntax.mk_binder x_a)
in (uu____1368)::[])
in (

let uu____1369 = (

let uu____1372 = (mk_repr b wp_g_x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____1372))
in (FStar_Syntax_Util.arrow uu____1361 uu____1369)))
in (FStar_Syntax_Syntax.null_binder uu____1360))
in (uu____1359)::[])
in (uu____1355)::uu____1356))
in (uu____1349)::uu____1352))
in (uu____1345)::uu____1346))
in (FStar_List.append maybe_range_arg uu____1342))
in (FStar_List.append uu____1331 uu____1339)))
in (

let uu____1373 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow uu____1324 uu____1373)))
in (

let uu____1376 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1 expected_k)
in (match (uu____1376) with
| (expected_k1, uu____1384, uu____1385) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_range env1 (FStar_Pervasives_Native.snd ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos)
in (

let env3 = (

let uu___69_1390 = env2
in {FStar_TypeChecker_Env.solver = uu___69_1390.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___69_1390.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___69_1390.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___69_1390.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___69_1390.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___69_1390.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___69_1390.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___69_1390.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___69_1390.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___69_1390.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___69_1390.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___69_1390.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___69_1390.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___69_1390.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___69_1390.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___69_1390.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___69_1390.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___69_1390.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___69_1390.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___69_1390.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___69_1390.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___69_1390.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___69_1390.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___69_1390.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___69_1390.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___69_1390.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___69_1390.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___69_1390.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___69_1390.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___69_1390.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___69_1390.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___69_1390.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___69_1390.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___69_1390.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___69_1390.FStar_TypeChecker_Env.dep_graph})
in (

let br = (check_and_gen' env3 ed2.FStar_Syntax_Syntax.bind_repr expected_k1)
in br)))
end))))))))))
end)))
in (

let return_repr = (

let x_a = (

let uu____1400 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" FStar_Pervasives_Native.None uu____1400))
in (

let res = (

let wp = (

let uu____1407 = (

let uu____1408 = (

let uu____1409 = (FStar_TypeChecker_Env.inst_tscheme return_wp)
in (FStar_All.pipe_right uu____1409 FStar_Pervasives_Native.snd))
in (

let uu____1418 = (

let uu____1419 = (

let uu____1422 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____1423 = (

let uu____1426 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (uu____1426)::[])
in (uu____1422)::uu____1423))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1419))
in (FStar_Syntax_Syntax.mk_Tm_app uu____1408 uu____1418)))
in (uu____1407 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (mk_repr a wp))
in (

let expected_k = (

let uu____1432 = (

let uu____1439 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1440 = (

let uu____1443 = (FStar_Syntax_Syntax.mk_binder x_a)
in (uu____1443)::[])
in (uu____1439)::uu____1440))
in (

let uu____1444 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow uu____1432 uu____1444)))
in (

let uu____1447 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1 expected_k)
in (match (uu____1447) with
| (expected_k1, uu____1461, uu____1462) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_range env1 (FStar_Pervasives_Native.snd ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos)
in (

let uu____1466 = (check_and_gen' env2 ed2.FStar_Syntax_Syntax.return_repr expected_k1)
in (match (uu____1466) with
| (univs1, repr1) -> begin
(match (univs1) with
| [] -> begin
(([]), (repr1))
end
| uu____1487 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn), ("Unexpected universe-polymorphic return for effect")) repr1.FStar_Syntax_Syntax.pos)
end)
end)))
end)))))
in (

let actions = (

let check_action = (fun act -> (

let act1 = (match ((Prims.op_Equality act.FStar_Syntax_Syntax.action_univs [])) with
| true -> begin
act
end
| uu____1519 -> begin
(

let uu____1520 = (FStar_Syntax_Subst.univ_var_opening act.FStar_Syntax_Syntax.action_univs)
in (match (uu____1520) with
| (usubst, uvs) -> begin
(

let uu___70_1539 = act
in (

let uu____1540 = (FStar_Syntax_Subst.subst_binders usubst act.FStar_Syntax_Syntax.action_params)
in (

let uu____1541 = (FStar_Syntax_Subst.subst usubst act.FStar_Syntax_Syntax.action_defn)
in (

let uu____1542 = (FStar_Syntax_Subst.subst usubst act.FStar_Syntax_Syntax.action_typ)
in {FStar_Syntax_Syntax.action_name = uu___70_1539.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___70_1539.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uvs; FStar_Syntax_Syntax.action_params = uu____1540; FStar_Syntax_Syntax.action_defn = uu____1541; FStar_Syntax_Syntax.action_typ = uu____1542}))))
end))
end)
in (

let act_typ = (

let uu____1546 = (

let uu____1547 = (FStar_Syntax_Subst.compress act1.FStar_Syntax_Syntax.action_typ)
in uu____1547.FStar_Syntax_Syntax.n)
in (match (uu____1546) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let c1 = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match ((FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name ed2.FStar_Syntax_Syntax.mname)) with
| true -> begin
(

let uu____1573 = (

let uu____1576 = (

let uu____1577 = (

let uu____1578 = (FStar_List.hd c1.FStar_Syntax_Syntax.effect_args)
in (FStar_Pervasives_Native.fst uu____1578))
in (mk_repr' c1.FStar_Syntax_Syntax.result_typ uu____1577))
in (FStar_Syntax_Syntax.mk_Total uu____1576))
in (FStar_Syntax_Util.arrow bs uu____1573))
end
| uu____1593 -> begin
act1.FStar_Syntax_Syntax.action_typ
end))
end
| uu____1594 -> begin
act1.FStar_Syntax_Syntax.action_typ
end))
in (

let uu____1595 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1 act_typ)
in (match (uu____1595) with
| (act_typ1, uu____1603, g_t) -> begin
(

let env' = (

let uu___71_1606 = (FStar_TypeChecker_Env.set_expected_typ env1 act_typ1)
in {FStar_TypeChecker_Env.solver = uu___71_1606.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___71_1606.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___71_1606.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___71_1606.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___71_1606.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___71_1606.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___71_1606.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___71_1606.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___71_1606.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = uu___71_1606.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___71_1606.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___71_1606.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___71_1606.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___71_1606.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___71_1606.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___71_1606.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___71_1606.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___71_1606.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___71_1606.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___71_1606.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___71_1606.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___71_1606.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___71_1606.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___71_1606.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___71_1606.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___71_1606.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___71_1606.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___71_1606.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___71_1606.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___71_1606.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___71_1606.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___71_1606.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___71_1606.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___71_1606.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___71_1606.FStar_TypeChecker_Env.dep_graph})
in ((

let uu____1608 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____1608) with
| true -> begin
(

let uu____1609 = (FStar_Syntax_Print.term_to_string act1.FStar_Syntax_Syntax.action_defn)
in (

let uu____1610 = (FStar_Syntax_Print.term_to_string act_typ1)
in (FStar_Util.print3 "Checking action %s:\n[definition]: %s\n[cps\'d type]: %s\n" (FStar_Ident.text_of_lid act1.FStar_Syntax_Syntax.action_name) uu____1609 uu____1610)))
end
| uu____1611 -> begin
()
end));
(

let uu____1612 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' act1.FStar_Syntax_Syntax.action_defn)
in (match (uu____1612) with
| (act_defn, uu____1620, g_a) -> begin
(

let act_defn1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env1 act_defn)
in (

let act_typ2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::[]) env1 act_typ1)
in (

let uu____1624 = (

let act_typ3 = (FStar_Syntax_Subst.compress act_typ2)
in (match (act_typ3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____1652 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____1652) with
| (bs1, uu____1662) -> begin
(

let res = (mk_repr' FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun)
in (

let k = (

let uu____1669 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs1 uu____1669))
in (

let uu____1672 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1 k)
in (match (uu____1672) with
| (k1, uu____1684, g) -> begin
((k1), (g))
end))))
end))
end
| uu____1686 -> begin
(

let uu____1687 = (

let uu____1692 = (

let uu____1693 = (FStar_Syntax_Print.term_to_string act_typ3)
in (

let uu____1694 = (FStar_Syntax_Print.tag_of_term act_typ3)
in (FStar_Util.format2 "Actions must have function types (not: %s, a.k.a. %s)" uu____1693 uu____1694)))
in ((FStar_Errors.Fatal_ActionMustHaveFunctionType), (uu____1692)))
in (FStar_Errors.raise_error uu____1687 act_defn1.FStar_Syntax_Syntax.pos))
end))
in (match (uu____1624) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env1 act_typ2 expected_k)
in ((

let uu____1703 = (

let uu____1704 = (

let uu____1705 = (FStar_TypeChecker_Rel.conj_guard g_t g)
in (FStar_TypeChecker_Rel.conj_guard g_k uu____1705))
in (FStar_TypeChecker_Rel.conj_guard g_a uu____1704))
in (FStar_TypeChecker_Rel.force_trivial_guard env1 uu____1703));
(

let act_typ3 = (

let uu____1709 = (

let uu____1710 = (FStar_Syntax_Subst.compress expected_k)
in uu____1710.FStar_Syntax_Syntax.n)
in (match (uu____1709) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____1733 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____1733) with
| (bs1, c1) -> begin
(

let uu____1742 = (destruct_repr (FStar_Syntax_Util.comp_result c1))
in (match (uu____1742) with
| (a1, wp) -> begin
(

let c2 = (

let uu____1764 = (

let uu____1765 = (env1.FStar_TypeChecker_Env.universe_of env1 a1)
in (uu____1765)::[])
in (

let uu____1766 = (

let uu____1775 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____1775)::[])
in {FStar_Syntax_Syntax.comp_univs = uu____1764; FStar_Syntax_Syntax.effect_name = ed2.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a1; FStar_Syntax_Syntax.effect_args = uu____1766; FStar_Syntax_Syntax.flags = []}))
in (

let uu____1776 = (FStar_Syntax_Syntax.mk_Comp c2)
in (FStar_Syntax_Util.arrow bs1 uu____1776)))
end))
end))
end
| uu____1779 -> begin
(failwith "Impossible (expected_k is an arrow)")
end))
in (

let uu____1782 = (FStar_TypeChecker_Util.generalize_universes env1 act_defn1)
in (match (uu____1782) with
| (univs1, act_defn2) -> begin
(

let act_typ4 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env1 act_typ3)
in (

let act_typ5 = (FStar_Syntax_Subst.close_univ_vars univs1 act_typ4)
in (

let uu___72_1791 = act1
in {FStar_Syntax_Syntax.action_name = uu___72_1791.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___72_1791.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs1; FStar_Syntax_Syntax.action_params = uu___72_1791.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = act_defn2; FStar_Syntax_Syntax.action_typ = act_typ5})))
end)));
))
end))))
end));
))
end)))))
in (FStar_All.pipe_right ed2.FStar_Syntax_Syntax.actions (FStar_List.map check_action)))
in ((repr), (bind_repr), (return_repr), (actions)))))))))
end))
in (match (uu____1039) with
| (repr, bind_repr, return_repr, actions) -> begin
(

let t0 = (

let uu____1815 = (FStar_Syntax_Syntax.mk_Total ed2.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed2.FStar_Syntax_Syntax.binders uu____1815))
in (

let uu____1818 = (

let uu____1825 = (FStar_TypeChecker_Util.generalize_universes env0 t0)
in (match (uu____1825) with
| (gen_univs, t) -> begin
(match (annotated_univ_names) with
| [] -> begin
((gen_univs), (t))
end
| uu____1846 -> begin
(

let uu____1849 = ((Prims.op_Equality (FStar_List.length gen_univs) (FStar_List.length annotated_univ_names)) && (FStar_List.forall2 (fun u1 u2 -> (Prims.op_Equality (FStar_Syntax_Syntax.order_univ_name u1 u2) (Prims.parse_int "0"))) gen_univs annotated_univ_names))
in (match (uu____1849) with
| true -> begin
((gen_univs), (t))
end
| uu____1862 -> begin
(

let uu____1863 = (

let uu____1868 = (

let uu____1869 = (FStar_Util.string_of_int (FStar_List.length annotated_univ_names))
in (

let uu____1870 = (FStar_Util.string_of_int (FStar_List.length gen_univs))
in (FStar_Util.format2 "Expected an effect definition with %s universes; but found %s" uu____1869 uu____1870)))
in ((FStar_Errors.Fatal_UnexpectedNumberOfUniverse), (uu____1868)))
in (FStar_Errors.raise_error uu____1863 ed2.FStar_Syntax_Syntax.signature.FStar_Syntax_Syntax.pos))
end))
end)
end))
in (match (uu____1818) with
| (univs1, t) -> begin
(

let signature1 = (

let uu____1884 = (

let uu____1889 = (

let uu____1890 = (FStar_Syntax_Subst.compress t)
in uu____1890.FStar_Syntax_Syntax.n)
in ((effect_params), (uu____1889)))
in (match (uu____1884) with
| ([], uu____1893) -> begin
t
end
| (uu____1904, FStar_Syntax_Syntax.Tm_arrow (uu____1905, c)) -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____1923 -> begin
(failwith "Impossible : t is an arrow")
end))
in (

let close1 = (fun n1 ts -> (

let ts1 = (

let uu____1936 = (FStar_Syntax_Subst.close_tscheme effect_params ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs1 uu____1936))
in (

let m = (FStar_List.length (FStar_Pervasives_Native.fst ts1))
in ((

let uu____1941 = (((n1 >= (Prims.parse_int "0")) && (

let uu____1943 = (FStar_Syntax_Util.is_unknown (FStar_Pervasives_Native.snd ts1))
in (not (uu____1943)))) && (Prims.op_disEquality m n1))
in (match (uu____1941) with
| true -> begin
(

let error = (match ((m < n1)) with
| true -> begin
"not universe-polymorphic enough"
end
| uu____1957 -> begin
"too universe-polymorphic"
end)
in (

let err_msg = (

let uu____1959 = (FStar_Util.string_of_int m)
in (

let uu____1966 = (FStar_Util.string_of_int n1)
in (

let uu____1967 = (FStar_Syntax_Print.tscheme_to_string ts1)
in (FStar_Util.format4 "The effect combinator is %s (m,n=%s,%s) (%s)" error uu____1959 uu____1966 uu____1967))))
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_MismatchUniversePolymorphic), (err_msg)) (FStar_Pervasives_Native.snd ts1).FStar_Syntax_Syntax.pos)))
end
| uu____1970 -> begin
()
end));
ts1;
))))
in (

let close_action = (fun act -> (

let uu____1975 = (close1 (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_defn)))
in (match (uu____1975) with
| (univs2, defn) -> begin
(

let uu____1982 = (close1 (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_typ)))
in (match (uu____1982) with
| (univs', typ) -> begin
(

let uu___73_1998 = act
in {FStar_Syntax_Syntax.action_name = uu___73_1998.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___73_1998.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs2; FStar_Syntax_Syntax.action_params = uu___73_1998.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = defn; FStar_Syntax_Syntax.action_typ = typ})
end))
end)))
in (

let ed3 = (

let uu___74_2009 = ed2
in (

let uu____2010 = (close1 (Prims.parse_int "0") return_wp)
in (

let uu____2011 = (close1 (Prims.parse_int "1") bind_wp)
in (

let uu____2012 = (close1 (Prims.parse_int "0") if_then_else1)
in (

let uu____2013 = (close1 (Prims.parse_int "0") ite_wp)
in (

let uu____2014 = (close1 (Prims.parse_int "0") stronger)
in (

let uu____2015 = (close1 (Prims.parse_int "1") close_wp)
in (

let uu____2016 = (close1 (Prims.parse_int "0") assert_p)
in (

let uu____2017 = (close1 (Prims.parse_int "0") assume_p)
in (

let uu____2018 = (close1 (Prims.parse_int "0") null_wp)
in (

let uu____2019 = (close1 (Prims.parse_int "0") trivial_wp)
in (

let uu____2020 = (

let uu____2021 = (close1 (Prims.parse_int "0") (([]), (repr)))
in (FStar_Pervasives_Native.snd uu____2021))
in (

let uu____2032 = (close1 (Prims.parse_int "0") return_repr)
in (

let uu____2033 = (close1 (Prims.parse_int "1") bind_repr)
in (

let uu____2034 = (FStar_List.map close_action actions)
in {FStar_Syntax_Syntax.cattributes = uu___74_2009.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___74_2009.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs1; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature1; FStar_Syntax_Syntax.ret_wp = uu____2010; FStar_Syntax_Syntax.bind_wp = uu____2011; FStar_Syntax_Syntax.if_then_else = uu____2012; FStar_Syntax_Syntax.ite_wp = uu____2013; FStar_Syntax_Syntax.stronger = uu____2014; FStar_Syntax_Syntax.close_wp = uu____2015; FStar_Syntax_Syntax.assert_p = uu____2016; FStar_Syntax_Syntax.assume_p = uu____2017; FStar_Syntax_Syntax.null_wp = uu____2018; FStar_Syntax_Syntax.trivial = uu____2019; FStar_Syntax_Syntax.repr = uu____2020; FStar_Syntax_Syntax.return_repr = uu____2032; FStar_Syntax_Syntax.bind_repr = uu____2033; FStar_Syntax_Syntax.actions = uu____2034; FStar_Syntax_Syntax.eff_attrs = uu___74_2009.FStar_Syntax_Syntax.eff_attrs})))))))))))))))
in ((

let uu____2038 = ((FStar_TypeChecker_Env.debug env1 FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("ED"))))
in (match (uu____2038) with
| true -> begin
(

let uu____2039 = (FStar_Syntax_Print.eff_decl_to_string false ed3)
in (FStar_Util.print_string uu____2039))
end
| uu____2040 -> begin
()
end));
ed3;
)))))
end)))
end)))))))))))));
)))
end)))))
end))
end))
end)))))
end)))


let cps_and_elaborate : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option) = (fun env ed -> (

let uu____2057 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____2057) with
| (effect_binders_un, signature_un) -> begin
(

let uu____2074 = (FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un)
in (match (uu____2074) with
| (effect_binders, env1, uu____2093) -> begin
(

let uu____2094 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un)
in (match (uu____2094) with
| (signature, uu____2110) -> begin
(

let raise_error1 = (fun a uu____2121 -> (match (uu____2121) with
| (e, err_msg) -> begin
(FStar_Errors.raise_error ((e), (err_msg)) signature.FStar_Syntax_Syntax.pos)
end))
in (

let effect_binders1 = (FStar_List.map (fun uu____2147 -> (match (uu____2147) with
| (bv, qual) -> begin
(

let uu____2158 = (

let uu___75_2159 = bv
in (

let uu____2160 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env1 bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___75_2159.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___75_2159.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2160}))
in ((uu____2158), (qual)))
end)) effect_binders)
in (

let uu____2163 = (

let uu____2170 = (

let uu____2171 = (FStar_Syntax_Subst.compress signature_un)
in uu____2171.FStar_Syntax_Syntax.n)
in (Obj.magic ((match (uu____2170) with
| FStar_Syntax_Syntax.Tm_arrow (((a, uu____2181))::[], effect_marker) -> begin
(Obj.repr ((a), (effect_marker)))
end
| uu____2203 -> begin
(Obj.repr (raise_error1 () ((FStar_Errors.Fatal_BadSignatureShape), ("bad shape for effect-for-free signature"))))
end))))
in (match (uu____2163) with
| (a, effect_marker) -> begin
(

let a1 = (

let uu____2221 = (FStar_Syntax_Syntax.is_null_bv a)
in (match (uu____2221) with
| true -> begin
(

let uu____2222 = (

let uu____2225 = (FStar_Syntax_Syntax.range_of_bv a)
in FStar_Pervasives_Native.Some (uu____2225))
in (FStar_Syntax_Syntax.gen_bv "a" uu____2222 a.FStar_Syntax_Syntax.sort))
end
| uu____2226 -> begin
a
end))
in (

let open_and_check = (fun env2 other_binders t -> (

let subst1 = (FStar_Syntax_Subst.opening_of_binders (FStar_List.append effect_binders1 other_binders))
in (

let t1 = (FStar_Syntax_Subst.subst subst1 t)
in (

let uu____2259 = (FStar_TypeChecker_TcTerm.tc_term env2 t1)
in (match (uu____2259) with
| (t2, comp, uu____2272) -> begin
((t2), (comp))
end)))))
in (

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None signature.FStar_Syntax_Syntax.pos))
in (

let uu____2279 = (open_and_check env1 [] ed.FStar_Syntax_Syntax.repr)
in (match (uu____2279) with
| (repr, _comp) -> begin
((

let uu____2301 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____2301) with
| true -> begin
(

let uu____2302 = (FStar_Syntax_Print.term_to_string repr)
in (FStar_Util.print1 "Representation is: %s\n" uu____2302))
end
| uu____2303 -> begin
()
end));
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env1 (FStar_TypeChecker_TcTerm.tc_constant env1 FStar_Range.dummyRange))
in (

let wp_type = (FStar_TypeChecker_DMFF.star_type dmff_env repr)
in (

let wp_type1 = (recheck_debug "*" env1 wp_type)
in (

let wp_a = (

let uu____2308 = (

let uu____2309 = (

let uu____2310 = (

let uu____2325 = (

let uu____2332 = (

let uu____2337 = (FStar_Syntax_Syntax.bv_to_name a1)
in (

let uu____2338 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____2337), (uu____2338))))
in (uu____2332)::[])
in ((wp_type1), (uu____2325)))
in FStar_Syntax_Syntax.Tm_app (uu____2310))
in (mk1 uu____2309))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env1 uu____2308))
in (

let effect_signature = (

let binders = (

let uu____2363 = (

let uu____2368 = (FStar_Syntax_Syntax.as_implicit false)
in ((a1), (uu____2368)))
in (

let uu____2369 = (

let uu____2376 = (

let uu____2377 = (FStar_Syntax_Syntax.gen_bv "dijkstra_wp" FStar_Pervasives_Native.None wp_a)
in (FStar_All.pipe_right uu____2377 FStar_Syntax_Syntax.mk_binder))
in (uu____2376)::[])
in (uu____2363)::uu____2369))
in (

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in (mk1 (FStar_Syntax_Syntax.Tm_arrow (((binders1), (effect_marker)))))))
in (

let effect_signature1 = (recheck_debug "turned into the effect signature" env1 effect_signature)
in (

let sigelts = (FStar_Util.mk_ref [])
in (

let mk_lid = (fun name -> (FStar_Syntax_Util.dm4f_lid ed name))
in (

let elaborate_and_star = (fun dmff_env1 other_binders item -> (

let env2 = (FStar_TypeChecker_DMFF.get_env dmff_env1)
in (

let uu____2440 = item
in (match (uu____2440) with
| (u_item, item1) -> begin
(

let uu____2461 = (open_and_check env2 other_binders item1)
in (match (uu____2461) with
| (item2, item_comp) -> begin
((

let uu____2477 = (

let uu____2478 = (FStar_Syntax_Util.is_total_lcomp item_comp)
in (not (uu____2478)))
in (match (uu____2477) with
| true -> begin
(

let uu____2479 = (

let uu____2484 = (

let uu____2485 = (FStar_Syntax_Print.term_to_string item2)
in (

let uu____2486 = (FStar_Syntax_Print.lcomp_to_string item_comp)
in (FStar_Util.format2 "Computation for [%s] is not total : %s !" uu____2485 uu____2486)))
in ((FStar_Errors.Fatal_ComputationNotTotal), (uu____2484)))
in (FStar_Errors.raise_err uu____2479))
end
| uu____2487 -> begin
()
end));
(

let uu____2488 = (FStar_TypeChecker_DMFF.star_expr dmff_env1 item2)
in (match (uu____2488) with
| (item_t, item_wp, item_elab) -> begin
(

let item_wp1 = (recheck_debug "*" env2 item_wp)
in (

let item_elab1 = (recheck_debug "_" env2 item_elab)
in ((dmff_env1), (item_t), (item_wp1), (item_elab1))))
end));
)
end))
end))))
in (

let uu____2508 = (elaborate_and_star dmff_env [] ed.FStar_Syntax_Syntax.bind_repr)
in (match (uu____2508) with
| (dmff_env1, uu____2532, bind_wp, bind_elab) -> begin
(

let uu____2535 = (elaborate_and_star dmff_env1 [] ed.FStar_Syntax_Syntax.return_repr)
in (match (uu____2535) with
| (dmff_env2, uu____2559, return_wp, return_elab) -> begin
(

let rc_gtot = {FStar_Syntax_Syntax.residual_effect = FStar_Parser_Const.effect_GTot_lid; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.None; FStar_Syntax_Syntax.residual_flags = []}
in (

let lift_from_pure_wp = (

let uu____2566 = (

let uu____2567 = (FStar_Syntax_Subst.compress return_wp)
in uu____2567.FStar_Syntax_Syntax.n)
in (Obj.magic ((match (uu____2566) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(Obj.repr (

let uu____2611 = (

let uu____2626 = (

let uu____2631 = (FStar_Syntax_Util.abs bs body FStar_Pervasives_Native.None)
in (FStar_Syntax_Subst.open_term ((b1)::(b2)::[]) uu____2631))
in (match (uu____2626) with
| ((b11)::(b21)::[], body1) -> begin
((b11), (b21), (body1))
end
| uu____2695 -> begin
(failwith "Impossible : open_term not preserving binders arity")
end))
in (match (uu____2611) with
| (b11, b21, body1) -> begin
(

let env0 = (

let uu____2734 = (FStar_TypeChecker_DMFF.get_env dmff_env2)
in (FStar_TypeChecker_Env.push_binders uu____2734 ((b11)::(b21)::[])))
in (

let wp_b1 = (

let raw_wp_b1 = (

let uu____2751 = (

let uu____2752 = (

let uu____2767 = (

let uu____2774 = (

let uu____2779 = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst b11))
in (

let uu____2780 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____2779), (uu____2780))))
in (uu____2774)::[])
in ((wp_type1), (uu____2767)))
in FStar_Syntax_Syntax.Tm_app (uu____2752))
in (mk1 uu____2751))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env0 raw_wp_b1))
in (

let uu____2795 = (

let uu____2804 = (

let uu____2805 = (FStar_Syntax_Util.unascribe wp_b1)
in (FStar_TypeChecker_Normalize.eta_expand_with_type env0 body1 uu____2805))
in (FStar_All.pipe_left FStar_Syntax_Util.abs_formals uu____2804))
in (match (uu____2795) with
| (bs1, body2, what') -> begin
(

let fail1 = (fun a415 -> ((Obj.magic ((fun uu____2824 -> (

let error_msg = (

let uu____2826 = (FStar_Syntax_Print.term_to_string body2)
in (FStar_Util.format2 "The body of return_wp (%s) should be of type Type0 but is of type %s" uu____2826 (match (what') with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (rc) -> begin
(FStar_Ident.text_of_lid rc.FStar_Syntax_Syntax.residual_effect)
end)))
in (raise_error1 () ((FStar_Errors.Fatal_WrongBodyTypeForReturnWP), (error_msg))))))) a415))
in ((match (what') with
| FStar_Pervasives_Native.None -> begin
(fail1 ())
end
| FStar_Pervasives_Native.Some (rc) -> begin
((match ((not ((FStar_Syntax_Util.is_pure_effect rc.FStar_Syntax_Syntax.residual_effect)))) with
| true -> begin
(fail1 ())
end
| uu____2831 -> begin
()
end);
(

let uu____2832 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun rt -> (

let g_opt = (FStar_TypeChecker_Rel.try_teq true env1 rt FStar_Syntax_Util.ktype0)
in (match (g_opt) with
| FStar_Pervasives_Native.Some (g') -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env1 g')
end
| FStar_Pervasives_Native.None -> begin
(fail1 ())
end))))
in (FStar_All.pipe_right uu____2832 FStar_Pervasives.ignore));
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

let uu____2859 = (

let uu____2860 = (FStar_Syntax_Syntax.bv_to_name wp)
in (

let uu____2861 = (

let uu____2862 = (

let uu____2869 = (FStar_Syntax_Util.abs ((b21)::[]) body2 what')
in ((uu____2869), (FStar_Pervasives_Native.None)))
in (uu____2862)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____2860 uu____2861)))
in (uu____2859 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let uu____2894 = (

let uu____2895 = (

let uu____2902 = (FStar_Syntax_Syntax.mk_binder wp)
in (uu____2902)::[])
in (b11)::uu____2895)
in (

let uu____2907 = (FStar_Syntax_Util.abs bs1 body3 what)
in (FStar_Syntax_Util.abs uu____2894 uu____2907 (FStar_Pervasives_Native.Some (rc_gtot)))))));
))
end))))
end)))
end
| uu____2908 -> begin
(Obj.repr (raise_error1 () ((FStar_Errors.Fatal_UnexpectedReturnShape), ("unexpected shape for return"))))
end))))
in (

let return_wp1 = (

let uu____2910 = (

let uu____2911 = (FStar_Syntax_Subst.compress return_wp)
in uu____2911.FStar_Syntax_Syntax.n)
in (Obj.magic ((match (uu____2910) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(Obj.repr (

let uu____2955 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs ((b1)::(b2)::[]) uu____2955 (FStar_Pervasives_Native.Some (rc_gtot)))))
end
| uu____2968 -> begin
(Obj.repr (raise_error1 () ((FStar_Errors.Fatal_UnexpectedReturnShape), ("unexpected shape for return"))))
end))))
in (

let bind_wp1 = (

let uu____2970 = (

let uu____2971 = (FStar_Syntax_Subst.compress bind_wp)
in uu____2971.FStar_Syntax_Syntax.n)
in (Obj.magic ((match (uu____2970) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(Obj.repr (

let r = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.range_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let uu____2998 = (

let uu____2999 = (

let uu____3002 = (

let uu____3003 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (r)))
in (FStar_Syntax_Syntax.null_binder uu____3003))
in (uu____3002)::[])
in (FStar_List.append uu____2999 binders))
in (FStar_Syntax_Util.abs uu____2998 body what))))
end
| uu____3004 -> begin
(Obj.repr (raise_error1 () ((FStar_Errors.Fatal_UnexpectedBindShape), ("unexpected shape for bind"))))
end))))
in (

let apply_close = (fun t -> (match ((Prims.op_Equality (FStar_List.length effect_binders1) (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____3021 -> begin
(

let uu____3022 = (

let uu____3023 = (

let uu____3024 = (

let uu____3039 = (

let uu____3040 = (FStar_Syntax_Util.args_of_binders effect_binders1)
in (FStar_Pervasives_Native.snd uu____3040))
in ((t), (uu____3039)))
in FStar_Syntax_Syntax.Tm_app (uu____3024))
in (mk1 uu____3023))
in (FStar_Syntax_Subst.close effect_binders1 uu____3022))
end))
in (

let rec apply_last1 = (fun f l -> (match (l) with
| [] -> begin
(failwith "empty path..")
end
| (a2)::[] -> begin
(

let uu____3070 = (f a2)
in (uu____3070)::[])
end
| (x)::xs -> begin
(

let uu____3075 = (apply_last1 f xs)
in (x)::uu____3075)
end))
in (

let register = (fun name item -> (

let p = (FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname)
in (

let p' = (apply_last1 (fun s -> (Prims.strcat "__" (Prims.strcat s (Prims.strcat "_eff_override_" name)))) p)
in (

let l' = (FStar_Ident.lid_of_path p' FStar_Range.dummyRange)
in (

let uu____3095 = (FStar_TypeChecker_Env.try_lookup_lid env1 l')
in (match (uu____3095) with
| FStar_Pervasives_Native.Some (_us, _t) -> begin
((

let uu____3125 = (FStar_Options.debug_any ())
in (match (uu____3125) with
| true -> begin
(

let uu____3126 = (FStar_Ident.string_of_lid l')
in (FStar_Util.print1 "DM4F: Applying override %s\n" uu____3126))
end
| uu____3127 -> begin
()
end));
(

let uu____3128 = (FStar_Syntax_Syntax.lid_as_fv l' FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____3128));
)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3137 = (

let uu____3142 = (mk_lid name)
in (

let uu____3143 = (FStar_Syntax_Util.abs effect_binders1 item FStar_Pervasives_Native.None)
in (FStar_TypeChecker_Util.mk_toplevel_definition env1 uu____3142 uu____3143)))
in (match (uu____3137) with
| (sigelt, fv) -> begin
((

let uu____3147 = (

let uu____3150 = (FStar_ST.op_Bang sigelts)
in (sigelt)::uu____3150)
in (FStar_ST.op_Colon_Equals sigelts uu____3147));
fv;
)
end))
end))))))
in (

let lift_from_pure_wp1 = (register "lift_from_pure" lift_from_pure_wp)
in (

let return_wp2 = (register "return_wp" return_wp1)
in ((FStar_Options.push ());
(

let uu____3355 = (

let uu____3358 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true"))))
in (

let uu____3359 = (FStar_ST.op_Bang sigelts)
in (uu____3358)::uu____3359))
in (FStar_ST.op_Colon_Equals sigelts uu____3355));
(

let return_elab1 = (register "return_elab" return_elab)
in ((FStar_Options.pop ());
(

let bind_wp2 = (register "bind_wp" bind_wp1)
in ((FStar_Options.push ());
(

let uu____3565 = (

let uu____3568 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true"))))
in (

let uu____3569 = (FStar_ST.op_Bang sigelts)
in (uu____3568)::uu____3569))
in (FStar_ST.op_Colon_Equals sigelts uu____3565));
(

let bind_elab1 = (register "bind_elab" bind_elab)
in ((FStar_Options.pop ());
(

let uu____3772 = (FStar_List.fold_left (fun uu____3812 action -> (match (uu____3812) with
| (dmff_env3, actions) -> begin
(

let params_un = (FStar_Syntax_Subst.open_binders action.FStar_Syntax_Syntax.action_params)
in (

let uu____3833 = (

let uu____3840 = (FStar_TypeChecker_DMFF.get_env dmff_env3)
in (FStar_TypeChecker_TcTerm.tc_tparams uu____3840 params_un))
in (match (uu____3833) with
| (action_params, env', uu____3849) -> begin
(

let action_params1 = (FStar_List.map (fun uu____3869 -> (match (uu____3869) with
| (bv, qual) -> begin
(

let uu____3880 = (

let uu___76_3881 = bv
in (

let uu____3882 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env' bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___76_3881.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___76_3881.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3882}))
in ((uu____3880), (qual)))
end)) action_params)
in (

let dmff_env' = (FStar_TypeChecker_DMFF.set_env dmff_env3 env')
in (

let uu____3886 = (elaborate_and_star dmff_env' action_params1 ((action.FStar_Syntax_Syntax.action_univs), (action.FStar_Syntax_Syntax.action_defn)))
in (match (uu____3886) with
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
| uu____3916 -> begin
(

let uu____3917 = (FStar_Syntax_Syntax.mk_Total action_typ_with_wp1)
in (FStar_Syntax_Util.flat_arrow action_params2 uu____3917))
end)
in ((

let uu____3921 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("ED")))
in (match (uu____3921) with
| true -> begin
(

let uu____3922 = (FStar_Syntax_Print.binders_to_string "," params_un)
in (

let uu____3923 = (FStar_Syntax_Print.binders_to_string "," action_params2)
in (

let uu____3924 = (FStar_Syntax_Print.term_to_string action_typ_with_wp2)
in (

let uu____3925 = (FStar_Syntax_Print.term_to_string action_elab2)
in (FStar_Util.print4 "original action_params %s, end action_params %s, type %s, term %s\n" uu____3922 uu____3923 uu____3924 uu____3925)))))
end
| uu____3926 -> begin
()
end));
(

let action_elab3 = (register (Prims.strcat name "_elab") action_elab2)
in (

let action_typ_with_wp3 = (register (Prims.strcat name "_complete_type") action_typ_with_wp2)
in (

let uu____3929 = (

let uu____3932 = (

let uu___77_3933 = action
in (

let uu____3934 = (apply_close action_elab3)
in (

let uu____3935 = (apply_close action_typ_with_wp3)
in {FStar_Syntax_Syntax.action_name = uu___77_3933.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___77_3933.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___77_3933.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = []; FStar_Syntax_Syntax.action_defn = uu____3934; FStar_Syntax_Syntax.action_typ = uu____3935})))
in (uu____3932)::actions)
in ((dmff_env4), (uu____3929)))));
))))))))
end))))
end)))
end)) ((dmff_env2), ([])) ed.FStar_Syntax_Syntax.actions)
in (match (uu____3772) with
| (dmff_env3, actions) -> begin
(

let actions1 = (FStar_List.rev actions)
in (

let repr1 = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp_a" FStar_Pervasives_Native.None wp_a)
in (

let binders = (

let uu____3968 = (FStar_Syntax_Syntax.mk_binder a1)
in (

let uu____3969 = (

let uu____3972 = (FStar_Syntax_Syntax.mk_binder wp)
in (uu____3972)::[])
in (uu____3968)::uu____3969))
in (

let uu____3973 = (

let uu____3974 = (

let uu____3975 = (

let uu____3976 = (

let uu____3991 = (

let uu____3998 = (

let uu____4003 = (FStar_Syntax_Syntax.bv_to_name a1)
in (

let uu____4004 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____4003), (uu____4004))))
in (uu____3998)::[])
in ((repr), (uu____3991)))
in FStar_Syntax_Syntax.Tm_app (uu____3976))
in (mk1 uu____3975))
in (

let uu____4019 = (FStar_Syntax_Syntax.bv_to_name wp)
in (FStar_TypeChecker_DMFF.trans_F dmff_env3 uu____3974 uu____4019)))
in (FStar_Syntax_Util.abs binders uu____3973 FStar_Pervasives_Native.None))))
in (

let repr2 = (recheck_debug "FC" env1 repr1)
in (

let repr3 = (register "repr" repr2)
in (

let uu____4022 = (

let uu____4029 = (

let uu____4030 = (

let uu____4033 = (FStar_Syntax_Subst.compress wp_type1)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____4033))
in uu____4030.FStar_Syntax_Syntax.n)
in (Obj.magic ((match (uu____4029) with
| FStar_Syntax_Syntax.Tm_abs ((type_param)::effect_param, arrow1, uu____4043) -> begin
(Obj.repr (

let uu____4072 = (

let uu____4089 = (FStar_Syntax_Subst.open_term ((type_param)::effect_param) arrow1)
in (match (uu____4089) with
| ((b)::bs, body) -> begin
((b), (bs), (body))
end
| uu____4147 -> begin
(failwith "Impossible : open_term nt preserving binders arity")
end))
in (match (uu____4072) with
| (type_param1, effect_param1, arrow2) -> begin
(

let uu____4197 = (

let uu____4198 = (

let uu____4201 = (FStar_Syntax_Subst.compress arrow2)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____4201))
in uu____4198.FStar_Syntax_Syntax.n)
in (Obj.magic ((match (uu____4197) with
| FStar_Syntax_Syntax.Tm_arrow (wp_binders, c) -> begin
(Obj.repr (

let uu____4226 = (FStar_Syntax_Subst.open_comp wp_binders c)
in (match (uu____4226) with
| (wp_binders1, c1) -> begin
(

let uu____4239 = (FStar_List.partition (fun uu____4264 -> (match (uu____4264) with
| (bv, uu____4270) -> begin
(

let uu____4271 = (

let uu____4272 = (FStar_Syntax_Free.names bv.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____4272 (FStar_Util.set_mem (FStar_Pervasives_Native.fst type_param1))))
in (FStar_All.pipe_right uu____4271 Prims.op_Negation))
end)) wp_binders1)
in (match (uu____4239) with
| (pre_args, post_args) -> begin
(

let post = (match (post_args) with
| (post)::[] -> begin
post
end
| [] -> begin
(

let err_msg = (

let uu____4336 = (FStar_Syntax_Print.term_to_string arrow2)
in (FStar_Util.format1 "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)" uu____4336))
in (FStar_Errors.raise_err ((FStar_Errors.Fatal_ImpossibleToGenerateDMEffect), (err_msg))))
end
| uu____4341 -> begin
(

let err_msg = (

let uu____4349 = (FStar_Syntax_Print.term_to_string arrow2)
in (FStar_Util.format1 "Impossible to generate DM effect: multiple post candidates %s" uu____4349))
in (FStar_Errors.raise_err ((FStar_Errors.Fatal_ImpossibleToGenerateDMEffect), (err_msg))))
end)
in (

let uu____4354 = (FStar_Syntax_Util.arrow pre_args c1)
in (

let uu____4357 = (FStar_Syntax_Util.abs ((type_param1)::effect_param1) (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort FStar_Pervasives_Native.None)
in ((uu____4354), (uu____4357)))))
end))
end)))
end
| uu____4364 -> begin
(Obj.repr (

let uu____4365 = (

let uu____4370 = (

let uu____4371 = (FStar_Syntax_Print.term_to_string arrow2)
in (FStar_Util.format1 "Impossible: pre/post arrow %s" uu____4371))
in ((FStar_Errors.Fatal_ImpossiblePrePostArrow), (uu____4370)))
in (raise_error1 () uu____4365)))
end))))
end)))
end
| uu____4372 -> begin
(Obj.repr (

let uu____4373 = (

let uu____4378 = (

let uu____4379 = (FStar_Syntax_Print.term_to_string wp_type1)
in (FStar_Util.format1 "Impossible: pre/post abs %s" uu____4379))
in ((FStar_Errors.Fatal_ImpossiblePrePostAbs), (uu____4378)))
in (raise_error1 () uu____4373)))
end))))
in (match (uu____4022) with
| (pre, post) -> begin
((

let uu____4397 = (register "pre" pre)
in ());
(

let uu____4399 = (register "post" post)
in ());
(

let uu____4401 = (register "wp" wp_type1)
in ());
(

let ed1 = (

let uu___78_4403 = ed
in (

let uu____4404 = (FStar_Syntax_Subst.close_binders effect_binders1)
in (

let uu____4405 = (FStar_Syntax_Subst.close effect_binders1 effect_signature1)
in (

let uu____4406 = (

let uu____4407 = (apply_close return_wp2)
in (([]), (uu____4407)))
in (

let uu____4414 = (

let uu____4415 = (apply_close bind_wp2)
in (([]), (uu____4415)))
in (

let uu____4422 = (apply_close repr3)
in (

let uu____4423 = (

let uu____4424 = (apply_close return_elab1)
in (([]), (uu____4424)))
in (

let uu____4431 = (

let uu____4432 = (apply_close bind_elab1)
in (([]), (uu____4432)))
in {FStar_Syntax_Syntax.cattributes = uu___78_4403.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___78_4403.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___78_4403.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu____4404; FStar_Syntax_Syntax.signature = uu____4405; FStar_Syntax_Syntax.ret_wp = uu____4406; FStar_Syntax_Syntax.bind_wp = uu____4414; FStar_Syntax_Syntax.if_then_else = uu___78_4403.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = uu___78_4403.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = uu___78_4403.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = uu___78_4403.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = uu___78_4403.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = uu___78_4403.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = uu___78_4403.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = uu___78_4403.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = uu____4422; FStar_Syntax_Syntax.return_repr = uu____4423; FStar_Syntax_Syntax.bind_repr = uu____4431; FStar_Syntax_Syntax.actions = actions1; FStar_Syntax_Syntax.eff_attrs = uu___78_4403.FStar_Syntax_Syntax.eff_attrs}))))))))
in (

let uu____4439 = (FStar_TypeChecker_DMFF.gen_wps_for_free env1 effect_binders1 a1 wp_a ed1)
in (match (uu____4439) with
| (sigelts', ed2) -> begin
((

let uu____4457 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____4457) with
| true -> begin
(

let uu____4458 = (FStar_Syntax_Print.eff_decl_to_string true ed2)
in (FStar_Util.print_string uu____4458))
end
| uu____4459 -> begin
()
end));
(

let lift_from_pure_opt = (match ((Prims.op_Equality (FStar_List.length effect_binders1) (Prims.parse_int "0"))) with
| true -> begin
(

let lift_from_pure = (

let uu____4470 = (

let uu____4473 = (

let uu____4482 = (apply_close lift_from_pure_wp1)
in (([]), (uu____4482)))
in FStar_Pervasives_Native.Some (uu____4473))
in {FStar_Syntax_Syntax.source = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.target = ed2.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.lift_wp = uu____4470; FStar_Syntax_Syntax.lift = FStar_Pervasives_Native.None})
in (

let uu____4497 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_sub_effect (lift_from_pure)))
in FStar_Pervasives_Native.Some (uu____4497)))
end
| uu____4498 -> begin
FStar_Pervasives_Native.None
end)
in (

let uu____4499 = (

let uu____4502 = (

let uu____4505 = (FStar_ST.op_Bang sigelts)
in (FStar_List.rev uu____4505))
in (FStar_List.append uu____4502 sigelts'))
in ((uu____4499), (ed2), (lift_from_pure_opt))));
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


let tc_lex_t : 'Auu____4616 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  'Auu____4616 Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (

let err_range = (

let uu____4655 = (FStar_List.hd ses)
in uu____4655.FStar_Syntax_Syntax.sigrng)
in ((match (lids) with
| (lex_t1)::(lex_top1)::(lex_cons)::[] when (((FStar_Ident.lid_equals lex_t1 FStar_Parser_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top1 FStar_Parser_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Parser_Const.lexcons_lid)) -> begin
()
end
| uu____4660 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_InvalidRedefinitionOfLexT), ("Invalid (partial) redefinition of lex_t")) err_range)
end);
(match (ses) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (lex_t1, uu____4664, [], t, uu____4666, uu____4667); FStar_Syntax_Syntax.sigrng = r; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = uu____4669; FStar_Syntax_Syntax.sigattrs = uu____4670})::({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (lex_top1, uu____4672, _t_top, _lex_t_top, _0_40, uu____4675); FStar_Syntax_Syntax.sigrng = r1; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = uu____4677; FStar_Syntax_Syntax.sigattrs = uu____4678})::({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (lex_cons, uu____4680, _t_cons, _lex_t_cons, _0_41, uu____4683); FStar_Syntax_Syntax.sigrng = r2; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = uu____4685; FStar_Syntax_Syntax.sigattrs = uu____4686})::[] when (((_0_40 = (Prims.parse_int "0")) && (_0_41 = (Prims.parse_int "0"))) && (((FStar_Ident.lid_equals lex_t1 FStar_Parser_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top1 FStar_Parser_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Parser_Const.lexcons_lid))) -> begin
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

let uu____4745 = (

let uu____4748 = (

let uu____4749 = (

let uu____4756 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid r1) FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in ((uu____4756), ((FStar_Syntax_Syntax.U_name (utop))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____4749))
in (FStar_Syntax_Syntax.mk uu____4748))
in (uu____4745 FStar_Pervasives_Native.None r1))
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

let uu____4774 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) FStar_Pervasives_Native.None r2)
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (r2)) uu____4774))
in (

let hd1 = (

let uu____4776 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (r2)) uu____4776))
in (

let tl1 = (

let uu____4778 = (

let uu____4779 = (

let uu____4782 = (

let uu____4783 = (

let uu____4790 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid r2) FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in ((uu____4790), ((FStar_Syntax_Syntax.U_name (ucons2))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____4783))
in (FStar_Syntax_Syntax.mk uu____4782))
in (uu____4779 FStar_Pervasives_Native.None r2))
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (r2)) uu____4778))
in (

let res = (

let uu____4799 = (

let uu____4802 = (

let uu____4803 = (

let uu____4810 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid r2) FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in ((uu____4810), ((FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____4803))
in (FStar_Syntax_Syntax.mk uu____4802))
in (uu____4799 FStar_Pervasives_Native.None r2))
in (

let uu____4816 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow ((((a), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::(((hd1), (FStar_Pervasives_Native.None)))::(((tl1), (FStar_Pervasives_Native.None)))::[]) uu____4816))))))
in (

let lex_cons_t1 = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((lex_cons), ((ucons1)::(ucons2)::[]), (lex_cons_t1), (FStar_Parser_Const.lex_t_lid), ((Prims.parse_int "0")), ([]))); FStar_Syntax_Syntax.sigrng = r2; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (

let uu____4855 = (FStar_TypeChecker_Env.get_range env)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle ((((tc)::(dc_lextop)::(dc_lexcons)::[]), (lids))); FStar_Syntax_Syntax.sigrng = uu____4855; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))))))))))))))
end
| uu____4860 -> begin
(

let err_msg = (

let uu____4864 = (

let uu____4865 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_bundle (((ses), (lids)))))
in (FStar_Syntax_Print.sigelt_to_string uu____4865))
in (FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n" uu____4864))
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_InvalidRedefinitionOfLexT), (err_msg)) err_range))
end);
)))


let tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env1 = (FStar_TypeChecker_Env.set_range env r)
in (

let uu____4890 = (FStar_Syntax_Util.type_u ())
in (match (uu____4890) with
| (k, uu____4896) -> begin
(

let phi1 = (

let uu____4898 = (tc_check_trivial_guard env1 phi k)
in (FStar_All.pipe_right uu____4898 (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env1)))
in ((FStar_TypeChecker_Util.check_uvars r phi1);
(

let uu____4900 = (FStar_TypeChecker_Util.generalize_universes env1 phi1)
in (match (uu____4900) with
| (us, phi2) -> begin
{FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_assume (((lid), (us), (phi2))); FStar_Syntax_Syntax.sigrng = r; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
end));
))
end))))


let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env ses quals lids -> (

let env1 = (FStar_TypeChecker_Env.push env "tc_inductive")
in (

let uu____4942 = (FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1 ses quals lids)
in (match (uu____4942) with
| (sig_bndle, tcs, datas) -> begin
(

let data_ops_ses = (

let uu____4975 = (FStar_List.map (FStar_TypeChecker_Util.mk_data_operations quals env1 tcs) datas)
in (FStar_All.pipe_right uu____4975 FStar_List.flatten))
in ((

let uu____4989 = ((FStar_Options.no_positivity ()) || (FStar_Options.lax ()))
in (match (uu____4989) with
| true -> begin
()
end
| uu____4990 -> begin
(

let env2 = (FStar_TypeChecker_Env.push_sigelt env1 sig_bndle)
in (FStar_List.iter (fun ty -> (

let b = (FStar_TypeChecker_TcInductive.check_positivity ty env2)
in (match ((not (b))) with
| true -> begin
(

let uu____5000 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____5010, uu____5011, uu____5012, uu____5013, uu____5014) -> begin
((lid), (ty.FStar_Syntax_Syntax.sigrng))
end
| uu____5023 -> begin
(failwith "Impossible!")
end)
in (match (uu____5000) with
| (lid, r) -> begin
(FStar_Errors.log_issue r ((FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition), ((Prims.strcat "Inductive type " (Prims.strcat lid.FStar_Ident.str " does not satisfy the positivity condition")))))
end))
end
| uu____5030 -> begin
()
end))) tcs))
end));
(

let skip_prims_type = (fun uu____5034 -> (

let lid = (

let ty = (FStar_List.hd tcs)
in (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____5038, uu____5039, uu____5040, uu____5041, uu____5042) -> begin
lid
end
| uu____5051 -> begin
(failwith "Impossible")
end))
in (

let types_to_skip = ("c_False")::("c_True")::("equals")::("h_equals")::("c_and")::("c_or")::[]
in (FStar_List.existsb (fun s -> (Prims.op_Equality s lid.FStar_Ident.ident.FStar_Ident.idText)) types_to_skip))))
in (

let is_noeq = (FStar_List.existsb (fun q -> (Prims.op_Equality q FStar_Syntax_Syntax.Noeq)) quals)
in (

let res = (

let uu____5069 = (((Prims.op_Equality (FStar_List.length tcs) (Prims.parse_int "0")) || ((FStar_Ident.lid_equals env1.FStar_TypeChecker_Env.curmodule FStar_Parser_Const.prims_lid) && (skip_prims_type ()))) || is_noeq)
in (match (uu____5069) with
| true -> begin
(((sig_bndle)::[]), (data_ops_ses))
end
| uu____5082 -> begin
(

let is_unopteq = (FStar_List.existsb (fun q -> (Prims.op_Equality q FStar_Syntax_Syntax.Unopteq)) quals)
in (

let ses1 = (match (is_unopteq) with
| true -> begin
(FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme sig_bndle tcs datas env1 tc_assume)
end
| uu____5091 -> begin
(FStar_TypeChecker_TcInductive.optimized_haseq_scheme sig_bndle tcs datas env1 tc_assume)
end)
in (

let uu____5092 = (

let uu____5095 = (

let uu____5096 = (FStar_TypeChecker_Env.get_range env1)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle ((((FStar_List.append tcs datas)), (lids))); FStar_Syntax_Syntax.sigrng = uu____5096; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (uu____5095)::ses1)
in ((uu____5092), (data_ops_ses)))))
end))
in ((

let uu____5106 = (FStar_TypeChecker_Env.pop env1 "tc_inductive")
in ());
res;
))));
))
end))))


let tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env se -> (

let env1 = (set_hint_correlator env se)
in ((FStar_TypeChecker_Util.check_sigelt_quals env1 se);
(

let r = se.FStar_Syntax_Syntax.sigrng
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____5140) -> begin
(failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____5165) -> begin
(failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, lids) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Parser_Const.lex_t_lid))) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_range env1 r)
in (

let se1 = (tc_lex_t env2 ses se.FStar_Syntax_Syntax.sigquals lids)
in (((se1)::[]), ([]))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, lids) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_range env1 r)
in (

let uu____5217 = (tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids)
in (match (uu____5217) with
| (ses1, projectors_ses) -> begin
((ses1), (projectors_ses))
end)))
end
| FStar_Syntax_Syntax.Sig_pragma (p) -> begin
((FStar_Syntax_Util.process_pragma p r);
(((se)::[]), ([]));
)
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne) -> begin
(

let uu____5255 = (cps_and_elaborate env1 ne)
in (match (uu____5255) with
| (ses, ne1, lift_from_pure_opt) -> begin
(

let effect_and_lift_ses = (match (lift_from_pure_opt) with
| FStar_Pervasives_Native.Some (lift) -> begin
((

let uu___79_5292 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne1); FStar_Syntax_Syntax.sigrng = uu___79_5292.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___79_5292.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___79_5292.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___79_5292.FStar_Syntax_Syntax.sigattrs}))::(lift)::[]
end
| FStar_Pervasives_Native.None -> begin
((

let uu___80_5294 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne1); FStar_Syntax_Syntax.sigrng = uu___80_5294.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___80_5294.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___80_5294.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___80_5294.FStar_Syntax_Syntax.sigattrs}))::[]
end)
in (([]), ((FStar_List.append ses effect_and_lift_ses))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let ne1 = (tc_eff_decl env1 ne)
in (

let se1 = (

let uu___81_5302 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne1); FStar_Syntax_Syntax.sigrng = uu___81_5302.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___81_5302.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___81_5302.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___81_5302.FStar_Syntax_Syntax.sigattrs})
in (((se1)::[]), ([]))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub1) -> begin
(

let ed_src = (FStar_TypeChecker_Env.get_effect_decl env1 sub1.FStar_Syntax_Syntax.source)
in (

let ed_tgt = (FStar_TypeChecker_Env.get_effect_decl env1 sub1.FStar_Syntax_Syntax.target)
in (

let uu____5310 = (

let uu____5317 = (FStar_TypeChecker_Env.lookup_effect_lid env1 sub1.FStar_Syntax_Syntax.source)
in (monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____5317))
in (match (uu____5310) with
| (a, wp_a_src) -> begin
(

let uu____5332 = (

let uu____5339 = (FStar_TypeChecker_Env.lookup_effect_lid env1 sub1.FStar_Syntax_Syntax.target)
in (monad_signature env1 sub1.FStar_Syntax_Syntax.target uu____5339))
in (match (uu____5332) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (

let uu____5355 = (

let uu____5358 = (

let uu____5359 = (

let uu____5366 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (uu____5366)))
in FStar_Syntax_Syntax.NT (uu____5359))
in (uu____5358)::[])
in (FStar_Syntax_Subst.subst uu____5355 wp_b_tgt))
in (

let expected_k = (

let uu____5370 = (

let uu____5377 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____5378 = (

let uu____5381 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (uu____5381)::[])
in (uu____5377)::uu____5378))
in (

let uu____5382 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow uu____5370 uu____5382)))
in (

let repr_type = (fun eff_name a1 wp -> (

let no_reify = (fun l -> (

let uu____5403 = (

let uu____5408 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((FStar_Errors.Fatal_EffectCannotBeReified), (uu____5408)))
in (

let uu____5409 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error uu____5403 uu____5409))))
in (

let uu____5412 = (FStar_TypeChecker_Env.effect_decl_opt env1 eff_name)
in (match (uu____5412) with
| FStar_Pervasives_Native.None -> begin
(no_reify eff_name)
end
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((FStar_Syntax_Syntax.U_unknown)::[]) env1 ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let uu____5444 = (

let uu____5445 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (not (uu____5445)))
in (match (uu____5444) with
| true -> begin
(no_reify eff_name)
end
| uu____5450 -> begin
(

let uu____5451 = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____5452 = (

let uu____5455 = (

let uu____5456 = (

let uu____5471 = (

let uu____5474 = (FStar_Syntax_Syntax.as_arg a1)
in (

let uu____5475 = (

let uu____5478 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____5478)::[])
in (uu____5474)::uu____5475))
in ((repr), (uu____5471)))
in FStar_Syntax_Syntax.Tm_app (uu____5456))
in (FStar_Syntax_Syntax.mk uu____5455))
in (uu____5452 FStar_Pervasives_Native.None uu____5451)))
end)))
end))))
in (

let uu____5484 = (match (((sub1.FStar_Syntax_Syntax.lift), (sub1.FStar_Syntax_Syntax.lift_wp))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(failwith "Impossible (parser)")
end
| (lift, FStar_Pervasives_Native.Some (uvs, lift_wp)) -> begin
(

let lift_wp1 = (match (((FStar_List.length uvs) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____5537 = (

let uu____5540 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (FStar_Pervasives_Native.fst uu____5540))
in (FStar_Syntax_Subst.subst uu____5537 lift_wp))
end
| uu____5553 -> begin
lift_wp
end)
in (

let uu____5554 = (check_and_gen env1 lift_wp1 expected_k)
in ((lift), (uu____5554))))
end
| (FStar_Pervasives_Native.Some (what, lift), FStar_Pervasives_Native.None) -> begin
(

let lift1 = (match (((FStar_List.length what) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____5580 = (

let uu____5583 = (FStar_Syntax_Subst.univ_var_opening what)
in (FStar_Pervasives_Native.fst uu____5583))
in (FStar_Syntax_Subst.subst uu____5580 lift))
end
| uu____5596 -> begin
lift
end)
in ((

let uu____5598 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____5598) with
| true -> begin
(

let uu____5599 = (FStar_Syntax_Print.term_to_string lift1)
in (FStar_Util.print1 "Lift for free : %s\n" uu____5599))
end
| uu____5600 -> begin
()
end));
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env1 (FStar_TypeChecker_TcTerm.tc_constant env1 FStar_Range.dummyRange))
in (

let uu____5602 = (FStar_TypeChecker_TcTerm.tc_term env1 lift1)
in (match (uu____5602) with
| (lift2, comp, uu____5617) -> begin
(

let uu____5618 = (FStar_TypeChecker_DMFF.star_expr dmff_env lift2)
in (match (uu____5618) with
| (uu____5631, lift_wp, lift_elab) -> begin
(

let uu____5634 = (recheck_debug "lift-wp" env1 lift_wp)
in (

let uu____5635 = (recheck_debug "lift-elab" env1 lift_elab)
in ((FStar_Pervasives_Native.Some ((([]), (lift_elab)))), ((([]), (lift_wp))))))
end))
end)));
))
end)
in (match (uu____5484) with
| (lift, lift_wp) -> begin
(

let lax1 = env1.FStar_TypeChecker_Env.lax
in (

let env2 = (

let uu___82_5676 = env1
in {FStar_TypeChecker_Env.solver = uu___82_5676.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___82_5676.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___82_5676.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___82_5676.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___82_5676.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___82_5676.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___82_5676.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___82_5676.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___82_5676.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___82_5676.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___82_5676.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___82_5676.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___82_5676.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___82_5676.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___82_5676.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___82_5676.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___82_5676.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___82_5676.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___82_5676.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___82_5676.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___82_5676.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___82_5676.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___82_5676.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___82_5676.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___82_5676.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___82_5676.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___82_5676.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___82_5676.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___82_5676.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___82_5676.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___82_5676.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___82_5676.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___82_5676.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___82_5676.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___82_5676.FStar_TypeChecker_Env.dep_graph})
in (

let lift1 = (match (lift) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (uvs, lift1) -> begin
(

let lift2 = (

let uu____5695 = (

let uu____5698 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (FStar_Pervasives_Native.fst uu____5698))
in (FStar_Syntax_Subst.subst uu____5695 lift1))
in (

let uu____5711 = (

let uu____5718 = (FStar_TypeChecker_Env.lookup_effect_lid env2 sub1.FStar_Syntax_Syntax.source)
in (monad_signature env2 sub1.FStar_Syntax_Syntax.source uu____5718))
in (match (uu____5711) with
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

let lift_wp1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env2 (FStar_Pervasives_Native.snd lift_wp))
in (

let lift_wp_a = (

let uu____5742 = (FStar_TypeChecker_Env.get_range env2)
in (

let uu____5743 = (

let uu____5746 = (

let uu____5747 = (

let uu____5762 = (

let uu____5765 = (FStar_Syntax_Syntax.as_arg a_typ)
in (

let uu____5766 = (

let uu____5769 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (uu____5769)::[])
in (uu____5765)::uu____5766))
in ((lift_wp1), (uu____5762)))
in FStar_Syntax_Syntax.Tm_app (uu____5747))
in (FStar_Syntax_Syntax.mk uu____5746))
in (uu____5743 FStar_Pervasives_Native.None uu____5742)))
in (repr_type sub1.FStar_Syntax_Syntax.target a_typ lift_wp_a)))
in (

let expected_k1 = (

let uu____5778 = (

let uu____5785 = (FStar_Syntax_Syntax.mk_binder a1)
in (

let uu____5786 = (

let uu____5789 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (

let uu____5790 = (

let uu____5793 = (FStar_Syntax_Syntax.null_binder repr_f)
in (uu____5793)::[])
in (uu____5789)::uu____5790))
in (uu____5785)::uu____5786))
in (

let uu____5794 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow uu____5778 uu____5794)))
in (

let uu____5797 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env2 expected_k1)
in (match (uu____5797) with
| (expected_k2, uu____5807, uu____5808) -> begin
(

let lift3 = (check_and_gen env2 lift2 expected_k2)
in FStar_Pervasives_Native.Some (lift3))
end))))))))
end)))
end)
in (

let sub2 = (

let uu___83_5811 = sub1
in {FStar_Syntax_Syntax.source = uu___83_5811.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = uu___83_5811.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = FStar_Pervasives_Native.Some (lift_wp); FStar_Syntax_Syntax.lift = lift1})
in (

let se1 = (

let uu___84_5813 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_sub_effect (sub2); FStar_Syntax_Syntax.sigrng = uu___84_5813.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___84_5813.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___84_5813.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___84_5813.FStar_Syntax_Syntax.sigattrs})
in (((se1)::[]), ([])))))))
end)))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, flags1) -> begin
(

let env0 = env1
in (

let uu____5828 = (match ((Prims.op_Equality (FStar_List.length uvs) (Prims.parse_int "0"))) with
| true -> begin
((uvs), (tps), (c))
end
| uu____5841 -> begin
(

let uu____5842 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____5842) with
| (usubst, uvs1) -> begin
(

let tps1 = (FStar_Syntax_Subst.subst_binders usubst tps)
in (

let c1 = (

let uu____5869 = (FStar_Syntax_Subst.shift_subst (FStar_List.length tps1) usubst)
in (FStar_Syntax_Subst.subst_comp uu____5869 c))
in ((uvs1), (tps1), (c1))))
end))
end)
in (match (uu____5828) with
| (uvs1, tps1, c1) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_range env1 r)
in (

let uu____5890 = (FStar_Syntax_Subst.open_comp tps1 c1)
in (match (uu____5890) with
| (tps2, c2) -> begin
(

let uu____5905 = (FStar_TypeChecker_TcTerm.tc_tparams env2 tps2)
in (match (uu____5905) with
| (tps3, env3, us) -> begin
(

let uu____5923 = (FStar_TypeChecker_TcTerm.tc_comp env3 c2)
in (match (uu____5923) with
| (c3, u, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env3 g);
(

let tps4 = (FStar_Syntax_Subst.close_binders tps3)
in (

let c4 = (FStar_Syntax_Subst.close_comp tps4 c3)
in (

let uu____5944 = (

let uu____5945 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps4), (c4)))) FStar_Pervasives_Native.None r)
in (FStar_TypeChecker_Util.generalize_universes env0 uu____5945))
in (match (uu____5944) with
| (uvs2, t) -> begin
(

let uu____5960 = (

let uu____5973 = (

let uu____5978 = (

let uu____5979 = (FStar_Syntax_Subst.compress t)
in uu____5979.FStar_Syntax_Syntax.n)
in ((tps4), (uu____5978)))
in (match (uu____5973) with
| ([], FStar_Syntax_Syntax.Tm_arrow (uu____5994, c5)) -> begin
(([]), (c5))
end
| (uu____6034, FStar_Syntax_Syntax.Tm_arrow (tps5, c5)) -> begin
((tps5), (c5))
end
| uu____6061 -> begin
(failwith "Impossible (t is an arrow)")
end))
in (match (uu____5960) with
| (tps5, c5) -> begin
((match ((Prims.op_disEquality (FStar_List.length uvs2) (Prims.parse_int "1"))) with
| true -> begin
(

let uu____6105 = (FStar_Syntax_Subst.open_univ_vars uvs2 t)
in (match (uu____6105) with
| (uu____6110, t1) -> begin
(

let uu____6112 = (

let uu____6117 = (

let uu____6118 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____6119 = (FStar_All.pipe_right (FStar_List.length uvs2) FStar_Util.string_of_int)
in (

let uu____6120 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)" uu____6118 uu____6119 uu____6120))))
in ((FStar_Errors.Fatal_TooManyUniverse), (uu____6117)))
in (FStar_Errors.raise_error uu____6112 r))
end))
end
| uu____6121 -> begin
()
end);
(

let se1 = (

let uu___85_6123 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (((lid), (uvs2), (tps5), (c5), (flags1))); FStar_Syntax_Syntax.sigrng = uu___85_6123.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___85_6123.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___85_6123.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___85_6123.FStar_Syntax_Syntax.sigattrs})
in (((se1)::[]), ([])));
)
end))
end))));
)
end))
end))
end)))
end)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____6140, uu____6141, uu____6142) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___59_6146 -> (match (uu___59_6146) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____6147 -> begin
false
end)))) -> begin
(([]), ([]))
end
| FStar_Syntax_Syntax.Sig_let (uu____6152, uu____6153) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___59_6161 -> (match (uu___59_6161) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____6162 -> begin
false
end)))) -> begin
(([]), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_range env1 r)
in ((

let uu____6172 = (FStar_TypeChecker_Env.lid_exists env2 lid)
in (match (uu____6172) with
| true -> begin
(

let uu____6173 = (

let uu____6178 = (FStar_Util.format1 "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module" (FStar_Ident.text_of_lid lid))
in ((FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration), (uu____6178)))
in (FStar_Errors.raise_error uu____6173 r))
end
| uu____6179 -> begin
()
end));
(

let uu____6180 = (match ((Prims.op_Equality uvs [])) with
| true -> begin
(

let uu____6181 = (

let uu____6182 = (FStar_Syntax_Util.type_u ())
in (FStar_Pervasives_Native.fst uu____6182))
in (check_and_gen env2 t uu____6181))
end
| uu____6187 -> begin
(

let uu____6188 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____6188) with
| (uvs1, t1) -> begin
(

let t2 = (

let uu____6196 = (

let uu____6197 = (FStar_Syntax_Util.type_u ())
in (FStar_Pervasives_Native.fst uu____6197))
in (tc_check_trivial_guard env2 t1 uu____6196))
in (

let t3 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Beta)::[]) env2 t2)
in (

let uu____6203 = (FStar_Syntax_Subst.close_univ_vars uvs1 t3)
in ((uvs1), (uu____6203)))))
end))
end)
in (match (uu____6180) with
| (uvs1, t1) -> begin
(

let se1 = (

let uu___86_6219 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (uvs1), (t1))); FStar_Syntax_Syntax.sigrng = uu___86_6219.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___86_6219.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___86_6219.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___86_6219.FStar_Syntax_Syntax.sigattrs})
in (((se1)::[]), ([])))
end));
))
end
| FStar_Syntax_Syntax.Sig_assume (lid, us, phi) -> begin
(

let uu____6229 = (FStar_Syntax_Subst.open_univ_vars us phi)
in (match (uu____6229) with
| (uu____6242, phi1) -> begin
(

let se1 = (tc_assume env1 lid phi1 se.FStar_Syntax_Syntax.sigquals r)
in (((se1)::[]), ([])))
end))
end
| FStar_Syntax_Syntax.Sig_main (e) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_range env1 r)
in (

let env3 = (FStar_TypeChecker_Env.set_expected_typ env2 FStar_Syntax_Syntax.t_unit)
in (

let uu____6252 = (FStar_TypeChecker_TcTerm.tc_term env3 e)
in (match (uu____6252) with
| (e1, c, g1) -> begin
(

let uu____6270 = (

let uu____6277 = (

let uu____6280 = (FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r)
in FStar_Pervasives_Native.Some (uu____6280))
in (

let uu____6281 = (

let uu____6286 = (FStar_Syntax_Syntax.lcomp_comp c)
in ((e1), (uu____6286)))
in (FStar_TypeChecker_TcTerm.check_expected_effect env3 uu____6277 uu____6281)))
in (match (uu____6270) with
| (e2, uu____6296, g) -> begin
((

let uu____6299 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env3 uu____6299));
(

let se1 = (

let uu___87_6301 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_main (e2); FStar_Syntax_Syntax.sigrng = uu___87_6301.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___87_6301.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___87_6301.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___87_6301.FStar_Syntax_Syntax.sigattrs})
in (((se1)::[]), ([])));
)
end))
end))))
end
| FStar_Syntax_Syntax.Sig_splice (t) -> begin
((

let uu____6308 = (FStar_Options.debug_any ())
in (match (uu____6308) with
| true -> begin
(

let uu____6309 = (FStar_Ident.string_of_lid env1.FStar_TypeChecker_Env.curmodule)
in (

let uu____6310 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "%s: Found splice of (%s)\n" uu____6309 uu____6310)))
end
| uu____6311 -> begin
()
end));
(

let ses = (env1.FStar_TypeChecker_Env.splice env1 t)
in (([]), (ses)));
)
end
| FStar_Syntax_Syntax.Sig_let (lbs, lids) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_range env1 r)
in (

let check_quals_eq = (fun l qopt q -> (match (qopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (q)
end
| FStar_Pervasives_Native.Some (q') -> begin
(

let uu____6365 = ((Prims.op_Equality (FStar_List.length q) (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q'))
in (match (uu____6365) with
| true -> begin
FStar_Pervasives_Native.Some (q)
end
| uu____6372 -> begin
(

let uu____6373 = (

let uu____6378 = (

let uu____6379 = (FStar_Syntax_Print.lid_to_string l)
in (

let uu____6380 = (FStar_Syntax_Print.quals_to_string q)
in (

let uu____6381 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" uu____6379 uu____6380 uu____6381))))
in ((FStar_Errors.Fatal_InconsistentQualifierAnnotation), (uu____6378)))
in (FStar_Errors.raise_error uu____6373 r))
end))
end))
in (

let rename_parameters = (fun lb -> (

let rename_in_typ = (fun def typ -> (

let typ1 = (FStar_Syntax_Subst.compress typ)
in (

let def_bs = (

let uu____6407 = (

let uu____6408 = (FStar_Syntax_Subst.compress def)
in uu____6408.FStar_Syntax_Syntax.n)
in (match (uu____6407) with
| FStar_Syntax_Syntax.Tm_abs (binders, uu____6418, uu____6419) -> begin
binders
end
| uu____6440 -> begin
[]
end))
in (match (typ1) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow (val_bs, c); FStar_Syntax_Syntax.pos = r1; FStar_Syntax_Syntax.vars = uu____6450} -> begin
(

let has_auto_name = (fun bv -> (FStar_Util.starts_with bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Ident.reserved_prefix))
in (

let rec rename_binders1 = (fun def_bs1 val_bs1 -> (match (((def_bs1), (val_bs1))) with
| ([], uu____6528) -> begin
val_bs1
end
| (uu____6551, []) -> begin
val_bs1
end
| (((body_bv, uu____6575))::bt, ((val_bv, aqual))::vt) -> begin
(

let uu____6612 = (rename_binders1 bt vt)
in ((match ((((has_auto_name body_bv)), ((has_auto_name val_bv)))) with
| (true, uu____6628) -> begin
((val_bv), (aqual))
end
| (false, true) -> begin
(((

let uu___88_6630 = val_bv
in {FStar_Syntax_Syntax.ppname = (

let uu___89_6633 = val_bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = body_bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText; FStar_Ident.idRange = uu___89_6633.FStar_Ident.idRange}); FStar_Syntax_Syntax.index = uu___88_6630.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___88_6630.FStar_Syntax_Syntax.sort})), (aqual))
end
| (false, false) -> begin
((val_bv), (aqual))
end))::uu____6612)
end))
in (

let uu____6634 = (

let uu____6637 = (

let uu____6638 = (

let uu____6651 = (rename_binders1 def_bs val_bs)
in ((uu____6651), (c)))
in FStar_Syntax_Syntax.Tm_arrow (uu____6638))
in (FStar_Syntax_Syntax.mk uu____6637))
in (uu____6634 FStar_Pervasives_Native.None r1))))
end
| uu____6669 -> begin
typ1
end))))
in (

let uu___90_6670 = lb
in (

let uu____6671 = (rename_in_typ lb.FStar_Syntax_Syntax.lbdef lb.FStar_Syntax_Syntax.lbtyp)
in {FStar_Syntax_Syntax.lbname = uu___90_6670.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___90_6670.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____6671; FStar_Syntax_Syntax.lbeff = uu___90_6670.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___90_6670.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___90_6670.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___90_6670.FStar_Syntax_Syntax.lbpos}))))
in (

let uu____6674 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.fold_left (fun uu____6725 lb -> (match (uu____6725) with
| (gen1, lbs1, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____6767 = (

let uu____6778 = (FStar_TypeChecker_Env.try_lookup_val_decl env2 lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____6778) with
| FStar_Pervasives_Native.None -> begin
(match ((Prims.op_disEquality lb.FStar_Syntax_Syntax.lbunivs [])) with
| true -> begin
((false), (lb), (quals_opt))
end
| uu____6819 -> begin
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
| uu____6863 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((lb.FStar_Syntax_Syntax.lbdef), (((FStar_Util.Inl (lb.FStar_Syntax_Syntax.lbtyp)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.pos)
end)
in ((match (((Prims.op_disEquality lb.FStar_Syntax_Syntax.lbunivs []) && (Prims.op_disEquality (FStar_List.length lb.FStar_Syntax_Syntax.lbunivs) (FStar_List.length uvs)))) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_IncoherentInlineUniverse), ("Inline universes are incoherent with annotation from val declaration")) r)
end
| uu____6905 -> begin
()
end);
(

let uu____6906 = (FStar_Syntax_Syntax.mk_lb ((FStar_Util.Inr (lbname)), (uvs), (FStar_Parser_Const.effect_ALL_lid), (tval), (def), (lb.FStar_Syntax_Syntax.lbpos)))
in ((false), (uu____6906), (quals_opt1)));
)))
end))
in (match (uu____6767) with
| (gen2, lb1, quals_opt1) -> begin
((gen2), ((lb1)::lbs1), (quals_opt1))
end)))
end)) ((true), ([]), ((match ((Prims.op_Equality se.FStar_Syntax_Syntax.sigquals [])) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____6962 -> begin
FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
end)))))
in (match (uu____6674) with
| (should_generalize, lbs', quals_opt) -> begin
(

let quals = (match (quals_opt) with
| FStar_Pervasives_Native.None -> begin
(FStar_Syntax_Syntax.Visible_default)::[]
end
| FStar_Pervasives_Native.Some (q) -> begin
(

let uu____7000 = (FStar_All.pipe_right q (FStar_Util.for_some (fun uu___60_7004 -> (match (uu___60_7004) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| FStar_Syntax_Syntax.Visible_default -> begin
true
end
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____7005 -> begin
false
end))))
in (match (uu____7000) with
| true -> begin
q
end
| uu____7008 -> begin
(FStar_Syntax_Syntax.Visible_default)::q
end))
end)
in (

let lbs'1 = (FStar_List.rev lbs')
in (

let e = (

let uu____7015 = (

let uu____7018 = (

let uu____7019 = (

let uu____7032 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) FStar_Pervasives_Native.None r)
in (((((FStar_Pervasives_Native.fst lbs)), (lbs'1))), (uu____7032)))
in FStar_Syntax_Syntax.Tm_let (uu____7019))
in (FStar_Syntax_Syntax.mk uu____7018))
in (uu____7015 FStar_Pervasives_Native.None r))
in (

let uu____7050 = (

let uu____7061 = (FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term (

let uu___91_7070 = env2
in {FStar_TypeChecker_Env.solver = uu___91_7070.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___91_7070.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___91_7070.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___91_7070.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___91_7070.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___91_7070.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___91_7070.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___91_7070.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___91_7070.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___91_7070.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___91_7070.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = uu___91_7070.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = uu___91_7070.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___91_7070.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___91_7070.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___91_7070.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___91_7070.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___91_7070.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___91_7070.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___91_7070.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___91_7070.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___91_7070.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___91_7070.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___91_7070.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___91_7070.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___91_7070.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___91_7070.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___91_7070.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___91_7070.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___91_7070.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___91_7070.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___91_7070.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___91_7070.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___91_7070.FStar_TypeChecker_Env.dep_graph}) e)
in (match (uu____7061) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs1, e1); FStar_Syntax_Syntax.pos = uu____7083; FStar_Syntax_Syntax.vars = uu____7084}, uu____7085, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let lbs2 = (

let uu____7114 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1) (FStar_List.map rename_parameters))
in (((FStar_Pervasives_Native.fst lbs1)), (uu____7114)))
in (

let quals1 = (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (uu____7132, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| uu____7137 -> begin
quals
end)
in (((

let uu___92_7145 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((lbs2), (lids))); FStar_Syntax_Syntax.sigrng = uu___92_7145.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = uu___92_7145.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___92_7145.FStar_Syntax_Syntax.sigattrs})), (lbs2))))
end
| uu____7154 -> begin
(failwith "impossible (typechecking should preserve Tm_let)")
end))
in (match (uu____7050) with
| (se1, lbs1) -> begin
((FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1) (FStar_List.iter (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (FStar_TypeChecker_Env.insert_fv_info env2 fv lb.FStar_Syntax_Syntax.lbtyp)))));
(

let uu____7203 = (log env2)
in (match (uu____7203) with
| true -> begin
(

let uu____7204 = (

let uu____7205 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1) (FStar_List.map (fun lb -> (

let should_log = (

let uu____7220 = (

let uu____7229 = (

let uu____7230 = (

let uu____7233 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____7233.FStar_Syntax_Syntax.fv_name)
in uu____7230.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env2 uu____7229))
in (match (uu____7220) with
| FStar_Pervasives_Native.None -> begin
true
end
| uu____7240 -> begin
false
end))
in (match (should_log) with
| true -> begin
(

let uu____7249 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____7250 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" uu____7249 uu____7250)))
end
| uu____7251 -> begin
""
end)))))
in (FStar_All.pipe_right uu____7205 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" uu____7204))
end
| uu____7254 -> begin
()
end));
(((se1)::[]), ([]));
)
end)))))
end)))))
end));
)))


let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___61_7296 -> (match (uu___61_7296) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| uu____7297 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| FStar_Syntax_Syntax.Projector (l, uu____7303) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| FStar_Syntax_Syntax.Discriminator (l) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| uu____7309 -> begin
false
end))
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_pragma (uu____7318) -> begin
(([]), (hidden))
end
| FStar_Syntax_Syntax.Sig_splice (uu____7323) -> begin
(failwith "Impossible (Already handled)")
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____7332) -> begin
(failwith "Impossible (Already handled)")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____7357) -> begin
(failwith "Impossible (Already handled)")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____7381) -> begin
(

let uu____7390 = (is_abstract se.FStar_Syntax_Syntax.sigquals)
in (match (uu____7390) with
| true -> begin
(

let for_export_bundle = (fun se1 uu____7421 -> (match (uu____7421) with
| (out, hidden1) -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, uu____7460, uu____7461) -> begin
(

let dec = (

let uu___93_7471 = se1
in (

let uu____7472 = (

let uu____7473 = (

let uu____7480 = (

let uu____7483 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow bs uu____7483))
in ((l), (us), (uu____7480)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____7473))
in {FStar_Syntax_Syntax.sigel = uu____7472; FStar_Syntax_Syntax.sigrng = uu___93_7471.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::se1.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___93_7471.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___93_7471.FStar_Syntax_Syntax.sigattrs}))
in (((dec)::out), (hidden1)))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, uu____7495, uu____7496, uu____7497) -> begin
(

let dec = (

let uu___94_7503 = se1
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t))); FStar_Syntax_Syntax.sigrng = uu___94_7503.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::[]; FStar_Syntax_Syntax.sigmeta = uu___94_7503.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___94_7503.FStar_Syntax_Syntax.sigattrs})
in (((dec)::out), ((l)::hidden1)))
end
| uu____7508 -> begin
((out), (hidden1))
end)
end))
in (FStar_List.fold_right for_export_bundle ses (([]), (hidden))))
end
| uu____7525 -> begin
(((se)::[]), (hidden))
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____7530, uu____7531, uu____7532) -> begin
(

let uu____7533 = (is_abstract se.FStar_Syntax_Syntax.sigquals)
in (match (uu____7533) with
| true -> begin
(([]), (hidden))
end
| uu____7546 -> begin
(((se)::[]), (hidden))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, us, t) -> begin
(

let uu____7554 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some is_hidden_proj_or_disc))
in (match (uu____7554) with
| true -> begin
((((

let uu___95_7570 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t))); FStar_Syntax_Syntax.sigrng = uu___95_7570.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::[]; FStar_Syntax_Syntax.sigmeta = uu___95_7570.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___95_7570.FStar_Syntax_Syntax.sigattrs}))::[]), ((l)::hidden))
end
| uu____7571 -> begin
(

let uu____7572 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___62_7576 -> (match (uu___62_7576) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____7577) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____7582) -> begin
true
end
| uu____7583 -> begin
false
end))))
in (match (uu____7572) with
| true -> begin
(((se)::[]), (hidden))
end
| uu____7596 -> begin
(([]), (hidden))
end))
end))
end
| FStar_Syntax_Syntax.Sig_main (uu____7601) -> begin
(([]), (hidden))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____7606) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____7611) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____7616) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____7621) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____7639) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____7656 = (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
in (match (uu____7656) with
| true -> begin
(([]), (hidden))
end
| uu____7671 -> begin
(

let dec = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::[]; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (((dec)::[]), ((lid)::hidden)))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, l) -> begin
(

let uu____7687 = (is_abstract se.FStar_Syntax_Syntax.sigquals)
in (match (uu____7687) with
| true -> begin
(

let uu____7696 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let uu___96_7709 = se
in (

let uu____7710 = (

let uu____7711 = (

let uu____7718 = (

let uu____7719 = (

let uu____7722 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____7722.FStar_Syntax_Syntax.fv_name)
in uu____7719.FStar_Syntax_Syntax.v)
in ((uu____7718), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____7711))
in {FStar_Syntax_Syntax.sigel = uu____7710; FStar_Syntax_Syntax.sigrng = uu___96_7709.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___96_7709.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___96_7709.FStar_Syntax_Syntax.sigattrs})))))
in ((uu____7696), (hidden)))
end
| uu____7731 -> begin
(((se)::[]), (hidden))
end))
end))))


let add_sigelt_to_env : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____7742) -> begin
(failwith "add_sigelt_to_env: Impossible, bare data constructor")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____7759) -> begin
(failwith "add_sigelt_to_env: Impossible, bare data constructor")
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (uu____7774)) -> begin
(

let env1 = (

let uu____7778 = (FStar_Options.using_facts_from ())
in (FStar_TypeChecker_Env.set_proof_ns uu____7778 env))
in ((env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
env1;
))
end
| FStar_Syntax_Syntax.Sig_pragma (uu____7780) -> begin
env
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____7781) -> begin
env
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_sigelt env se)
in (FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun env2 a -> (

let uu____7791 = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Env.push_sigelt env2 uu____7791))) env1)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____7792, uu____7793, uu____7794) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___63_7798 -> (match (uu___63_7798) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____7799 -> begin
false
end)))) -> begin
env
end
| FStar_Syntax_Syntax.Sig_let (uu____7800, uu____7801) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___63_7809 -> (match (uu___63_7809) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____7810 -> begin
false
end)))) -> begin
env
end
| uu____7811 -> begin
(FStar_TypeChecker_Env.push_sigelt env se)
end))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let rec process_one_decl = (fun uu____7871 se -> (match (uu____7871) with
| (ses1, exports, env1, hidden) -> begin
((

let uu____7924 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____7924) with
| true -> begin
(

let uu____7925 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____7925))
end
| uu____7926 -> begin
()
end));
(

let uu____7927 = (tc_decl env1 se)
in (match (uu____7927) with
| (ses', ses_elaborated) -> begin
(

let ses'1 = (FStar_All.pipe_right ses' (FStar_List.map (fun se1 -> ((

let uu____7977 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("UF")))
in (match (uu____7977) with
| true -> begin
(

let uu____7978 = (FStar_Syntax_Print.sigelt_to_string se1)
in (FStar_Util.print1 "About to elim vars from %s" uu____7978))
end
| uu____7979 -> begin
()
end));
(FStar_TypeChecker_Normalize.elim_uvars env1 se1);
))))
in (

let ses_elaborated1 = (FStar_All.pipe_right ses_elaborated (FStar_List.map (fun se1 -> (FStar_TypeChecker_Normalize.elim_uvars env1 se1))))
in ((FStar_TypeChecker_Env.promote_id_info env1 (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.CheckNoUvars)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Iota))::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env1 t)));
(

let env2 = (FStar_All.pipe_right ses'1 (FStar_List.fold_left (fun env2 se1 -> (add_sigelt_to_env env2 se1)) env1))
in ((FStar_Syntax_Unionfind.reset ());
(

let uu____8001 = ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("LogTypes"))))
in (match (uu____8001) with
| true -> begin
(

let uu____8002 = (FStar_List.fold_left (fun s se1 -> (

let uu____8008 = (

let uu____8009 = (FStar_Syntax_Print.sigelt_to_string se1)
in (Prims.strcat uu____8009 "\n"))
in (Prims.strcat s uu____8008))) "" ses'1)
in (FStar_Util.print1 "Checked: %s\n" uu____8002))
end
| uu____8010 -> begin
()
end));
(FStar_List.iter (fun se1 -> (env2.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env2 se1)) ses'1);
(

let uu____8014 = (

let uu____8023 = (FStar_Options.use_extracted_interfaces ())
in (match (uu____8023) with
| true -> begin
(([]), ([]))
end
| uu____8036 -> begin
(

let accum_exports_hidden = (fun uu____8058 se1 -> (match (uu____8058) with
| (exports1, hidden1) -> begin
(

let uu____8086 = (for_export hidden1 se1)
in (match (uu____8086) with
| (se_exported, hidden2) -> begin
(((FStar_List.rev_append se_exported exports1)), (hidden2))
end))
end))
in (FStar_List.fold_left accum_exports_hidden ((exports), (hidden)) ses'1))
end))
in (match (uu____8014) with
| (exports1, hidden1) -> begin
(

let ses'2 = (FStar_List.map (fun s -> (

let uu___97_8165 = s
in {FStar_Syntax_Syntax.sigel = uu___97_8165.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___97_8165.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___97_8165.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___97_8165.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = se.FStar_Syntax_Syntax.sigattrs})) ses'1)
in (((((FStar_List.rev_append ses'2 ses1)), (exports1), (env2), (hidden1))), (ses_elaborated1)))
end));
));
)))
end));
)
end))
in (

let process_one_decl_timed = (fun acc se -> (

let uu____8243 = acc
in (match (uu____8243) with
| (uu____8278, uu____8279, env1, uu____8281) -> begin
(

let uu____8294 = (FStar_Util.record_time (fun uu____8340 -> (process_one_decl acc se)))
in (match (uu____8294) with
| (r, ms_elapsed) -> begin
((

let uu____8404 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("TCDeclTime")))
in (match (uu____8404) with
| true -> begin
(

let uu____8405 = (FStar_Syntax_Print.sigelt_to_string_short se)
in (

let uu____8406 = (FStar_Util.string_of_int ms_elapsed)
in (FStar_Util.print2 "Checked %s in %s milliseconds\n" uu____8405 uu____8406)))
end
| uu____8407 -> begin
()
end));
r;
)
end))
end)))
in (

let uu____8408 = (FStar_Util.fold_flatten process_one_decl_timed (([]), ([]), (env), ([])) ses)
in (match (uu____8408) with
| (ses1, exports, env1, uu____8456) -> begin
(((FStar_List.rev_append ses1 [])), ((FStar_List.rev_append exports [])), (env1))
end)))))


let check_exports : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env modul exports -> (

let env1 = (

let uu___98_8487 = env
in {FStar_TypeChecker_Env.solver = uu___98_8487.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___98_8487.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___98_8487.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___98_8487.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___98_8487.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___98_8487.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___98_8487.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___98_8487.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___98_8487.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___98_8487.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___98_8487.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___98_8487.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___98_8487.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = uu___98_8487.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___98_8487.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___98_8487.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___98_8487.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = true; FStar_TypeChecker_Env.failhard = uu___98_8487.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___98_8487.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___98_8487.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___98_8487.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___98_8487.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___98_8487.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___98_8487.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___98_8487.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___98_8487.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___98_8487.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___98_8487.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___98_8487.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___98_8487.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___98_8487.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___98_8487.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___98_8487.FStar_TypeChecker_Env.dep_graph})
in (

let check_term = (fun lid univs1 t -> (

let uu____8498 = (FStar_Syntax_Subst.open_univ_vars univs1 t)
in (match (uu____8498) with
| (univs2, t1) -> begin
((

let uu____8506 = (

let uu____8507 = (

let uu____8510 = (FStar_TypeChecker_Env.set_current_module env1 modul.FStar_Syntax_Syntax.name)
in (FStar_TypeChecker_Env.debug uu____8510))
in (FStar_All.pipe_left uu____8507 (FStar_Options.Other ("Exports"))))
in (match (uu____8506) with
| true -> begin
(

let uu____8511 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____8512 = (

let uu____8513 = (FStar_All.pipe_right univs2 (FStar_List.map (fun x -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (x))))))
in (FStar_All.pipe_right uu____8513 (FStar_String.concat ", ")))
in (

let uu____8522 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Checking for export %s <%s> : %s\n" uu____8511 uu____8512 uu____8522))))
end
| uu____8523 -> begin
()
end));
(

let env2 = (FStar_TypeChecker_Env.push_univ_vars env1 univs2)
in (

let uu____8525 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1)
in (FStar_All.pipe_right uu____8525 FStar_Pervasives.ignore)));
)
end)))
in (

let check_term1 = (fun lid univs1 t -> ((

let uu____8549 = (

let uu____8550 = (FStar_Syntax_Print.lid_to_string modul.FStar_Syntax_Syntax.name)
in (

let uu____8551 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Interface of %s violates its abstraction (add a \'private\' qualifier to \'%s\'?)" uu____8550 uu____8551)))
in (FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____8549));
(check_term lid univs1 t);
(FStar_Errors.message_prefix.FStar_Errors.clear_prefix ());
))
in (

let rec check_sigelt = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____8558) -> begin
(

let uu____8567 = (

let uu____8568 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____8568)))
in (match (uu____8567) with
| true -> begin
(FStar_All.pipe_right ses (FStar_List.iter check_sigelt))
end
| uu____8573 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (l, univs1, binders, typ, uu____8578, uu____8579) -> begin
(

let t = (

let uu____8591 = (

let uu____8594 = (

let uu____8595 = (

let uu____8608 = (FStar_Syntax_Syntax.mk_Total typ)
in ((binders), (uu____8608)))
in FStar_Syntax_Syntax.Tm_arrow (uu____8595))
in (FStar_Syntax_Syntax.mk uu____8594))
in (uu____8591 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng))
in (check_term1 l univs1 t))
end
| FStar_Syntax_Syntax.Sig_datacon (l, univs1, t, uu____8615, uu____8616, uu____8617) -> begin
(check_term1 l univs1 t)
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, univs1, t) -> begin
(

let uu____8625 = (

let uu____8626 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____8626)))
in (match (uu____8625) with
| true -> begin
(check_term1 l univs1 t)
end
| uu____8629 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_let ((uu____8630, lbs), uu____8632) -> begin
(

let uu____8647 = (

let uu____8648 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____8648)))
in (match (uu____8647) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (check_term1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp)))))
end
| uu____8657 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs1, binders, comp, flags1) -> begin
(

let uu____8667 = (

let uu____8668 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____8668)))
in (match (uu____8667) with
| true -> begin
(

let arrow1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))) FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng)
in (check_term1 l univs1 arrow1))
end
| uu____8674 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_main (uu____8675) -> begin
()
end
| FStar_Syntax_Syntax.Sig_assume (uu____8676) -> begin
()
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____8683) -> begin
()
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____8684) -> begin
()
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____8685) -> begin
()
end
| FStar_Syntax_Syntax.Sig_splice (uu____8686) -> begin
()
end
| FStar_Syntax_Syntax.Sig_pragma (uu____8687) -> begin
()
end))
in (match ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Parser_Const.prims_lid)) with
| true -> begin
()
end
| uu____8688 -> begin
(FStar_List.iter check_sigelt exports)
end))))))


let extract_interface : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.modul = (fun env m -> (

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
| FStar_Syntax_Syntax.Projector (l, uu____8764) -> begin
true
end
| uu____8765 -> begin
false
end)) quals))
in (

let vals_of_abstract_inductive = (fun s -> (

let mk_typ_for_abstract_inductive = (fun bs t r -> (match (bs) with
| [] -> begin
t
end
| uu____8784 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs', c) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((((FStar_List.append bs bs')), (c)))) FStar_Pervasives_Native.None r)
end
| uu____8815 -> begin
(

let uu____8816 = (

let uu____8819 = (

let uu____8820 = (

let uu____8833 = (FStar_Syntax_Syntax.mk_Total t)
in ((bs), (uu____8833)))
in FStar_Syntax_Syntax.Tm_arrow (uu____8820))
in (FStar_Syntax_Syntax.mk uu____8819))
in (uu____8816 FStar_Pervasives_Native.None r))
end)
end))
in (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, bs, t, uu____8841, uu____8842) -> begin
(

let s1 = (

let uu___99_8852 = s
in (

let uu____8853 = (

let uu____8854 = (

let uu____8861 = (mk_typ_for_abstract_inductive bs t s.FStar_Syntax_Syntax.sigrng)
in ((lid), (uvs), (uu____8861)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____8854))
in (

let uu____8862 = (

let uu____8865 = (

let uu____8868 = (filter_out_abstract_and_noeq s.FStar_Syntax_Syntax.sigquals)
in (FStar_Syntax_Syntax.New)::uu____8868)
in (FStar_Syntax_Syntax.Assumption)::uu____8865)
in {FStar_Syntax_Syntax.sigel = uu____8853; FStar_Syntax_Syntax.sigrng = uu___99_8852.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu____8862; FStar_Syntax_Syntax.sigmeta = uu___99_8852.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___99_8852.FStar_Syntax_Syntax.sigattrs})))
in (s1)::[])
end
| uu____8871 -> begin
(failwith "Impossible!")
end)))
in (

let val_of_lb = (fun s lid uu____8885 -> (match (uu____8885) with
| (uvs, t) -> begin
(

let uu___100_8892 = s
in (

let uu____8893 = (

let uu____8896 = (filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals)
in (FStar_Syntax_Syntax.Assumption)::uu____8896)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (uvs), (t))); FStar_Syntax_Syntax.sigrng = uu___100_8892.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu____8893; FStar_Syntax_Syntax.sigmeta = uu___100_8892.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___100_8892.FStar_Syntax_Syntax.sigattrs}))
end))
in (

let should_keep_lbdef = (fun t -> (

let comp_effect_name1 = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
c1.FStar_Syntax_Syntax.effect_name
end
| uu____8908 -> begin
(failwith "Impossible!")
end))
in (

let c_opt = (

let uu____8912 = (FStar_Syntax_Util.is_unit t)
in (match (uu____8912) with
| true -> begin
(

let uu____8915 = (FStar_Syntax_Syntax.mk_Total t)
in FStar_Pervasives_Native.Some (uu____8915))
end
| uu____8916 -> begin
(

let uu____8917 = (

let uu____8918 = (FStar_Syntax_Subst.compress t)
in uu____8918.FStar_Syntax_Syntax.n)
in (match (uu____8917) with
| FStar_Syntax_Syntax.Tm_arrow (uu____8923, c) -> begin
FStar_Pervasives_Native.Some (c)
end
| uu____8943 -> begin
FStar_Pervasives_Native.None
end))
end))
in ((Prims.op_Equality c_opt FStar_Pervasives_Native.None) || (

let c = (FStar_All.pipe_right c_opt FStar_Util.must)
in (

let uu____8952 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (match (uu____8952) with
| true -> begin
(

let uu____8953 = (

let uu____8954 = (FStar_All.pipe_right c FStar_Syntax_Util.comp_result)
in (FStar_All.pipe_right uu____8954 FStar_Syntax_Util.is_unit))
in (not (uu____8953)))
end
| uu____8961 -> begin
(

let uu____8962 = (comp_effect_name1 c)
in (FStar_TypeChecker_Env.is_reifiable_effect env uu____8962))
end)))))))
in (

let extract_sigelt = (fun s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____8971) -> begin
(failwith "Impossible! Bare data constructor")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____8990) -> begin
(failwith "Impossible! Bare data constructor")
end
| FStar_Syntax_Syntax.Sig_splice (uu____9007) -> begin
(failwith "Impossible! Trying to extract splice")
end
| FStar_Syntax_Syntax.Sig_bundle (sigelts, lidents1) -> begin
(match ((is_abstract s.FStar_Syntax_Syntax.sigquals)) with
| true -> begin
(FStar_List.fold_left (fun sigelts1 s1 -> (match (s1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____9041, uu____9042, uu____9043, uu____9044, uu____9045) -> begin
((

let uu____9055 = (

let uu____9058 = (FStar_ST.op_Bang abstract_inductive_tycons)
in (lid)::uu____9058)
in (FStar_ST.op_Colon_Equals abstract_inductive_tycons uu____9055));
(

let uu____9259 = (vals_of_abstract_inductive s1)
in (FStar_List.append uu____9259 sigelts1));
)
end
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____9263, uu____9264, uu____9265, uu____9266, uu____9267) -> begin
((

let uu____9273 = (

let uu____9276 = (FStar_ST.op_Bang abstract_inductive_datacons)
in (lid)::uu____9276)
in (FStar_ST.op_Colon_Equals abstract_inductive_datacons uu____9273));
sigelts1;
)
end
| uu____9477 -> begin
(failwith "Impossible! Sig_bundle can\'t have anything other than Sig_inductive_typ and Sig_datacon")
end)) [] sigelts)
end
| uu____9480 -> begin
(s)::[]
end)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) -> begin
(

let uu____9484 = (is_projector_or_discriminator_of_an_abstract_inductive s.FStar_Syntax_Syntax.sigquals)
in (match (uu____9484) with
| true -> begin
[]
end
| uu____9487 -> begin
(match ((is_assume s.FStar_Syntax_Syntax.sigquals)) with
| true -> begin
(

let uu____9490 = (

let uu___101_9491 = s
in (

let uu____9492 = (filter_out_abstract s.FStar_Syntax_Syntax.sigquals)
in {FStar_Syntax_Syntax.sigel = uu___101_9491.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___101_9491.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu____9492; FStar_Syntax_Syntax.sigmeta = uu___101_9491.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___101_9491.FStar_Syntax_Syntax.sigattrs}))
in (uu____9490)::[])
end
| uu____9495 -> begin
[]
end)
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, lids) -> begin
(

let uu____9502 = (is_projector_or_discriminator_of_an_abstract_inductive s.FStar_Syntax_Syntax.sigquals)
in (match (uu____9502) with
| true -> begin
[]
end
| uu____9505 -> begin
(

let uu____9506 = lbs
in (match (uu____9506) with
| (flbs, slbs) -> begin
(

let typs = (FStar_All.pipe_right slbs (FStar_List.map (fun lb -> ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))))
in (

let is_lemma1 = (FStar_List.existsML (fun uu____9562 -> (match (uu____9562) with
| (uu____9569, t) -> begin
(FStar_All.pipe_right t FStar_Syntax_Util.is_lemma)
end)) typs)
in (

let vals = (FStar_List.map2 (fun lid uu____9587 -> (match (uu____9587) with
| (u, t) -> begin
(val_of_lb s lid ((u), (t)))
end)) lids typs)
in (match ((((is_abstract s.FStar_Syntax_Syntax.sigquals) || (is_irreducible1 s.FStar_Syntax_Syntax.sigquals)) || is_lemma1)) with
| true -> begin
vals
end
| uu____9596 -> begin
(

let should_keep_defs = (FStar_List.existsML (fun uu____9607 -> (match (uu____9607) with
| (uu____9614, t) -> begin
(FStar_All.pipe_right t should_keep_lbdef)
end)) typs)
in (match (should_keep_defs) with
| true -> begin
(s)::[]
end
| uu____9622 -> begin
vals
end))
end))))
end))
end))
end
| FStar_Syntax_Syntax.Sig_main (t) -> begin
(failwith "Did not anticipate main would arise when extracting interfaces!")
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____9627, uu____9628) -> begin
(

let is_haseq = (FStar_TypeChecker_Util.is_haseq_lid lid)
in (match (is_haseq) with
| true -> begin
(

let is_haseq_of_abstract_inductive = (

let uu____9633 = (FStar_ST.op_Bang abstract_inductive_tycons)
in (FStar_List.existsML (fun l -> (

let uu____9738 = (FStar_TypeChecker_Util.get_haseq_axiom_lid l)
in (FStar_Ident.lid_equals lid uu____9738))) uu____9633))
in (match (is_haseq_of_abstract_inductive) with
| true -> begin
(

let uu____9741 = (

let uu___102_9742 = s
in (

let uu____9743 = (filter_out_abstract s.FStar_Syntax_Syntax.sigquals)
in {FStar_Syntax_Syntax.sigel = uu___102_9742.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___102_9742.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu____9743; FStar_Syntax_Syntax.sigmeta = uu___102_9742.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___102_9742.FStar_Syntax_Syntax.sigattrs}))
in (uu____9741)::[])
end
| uu____9746 -> begin
[]
end))
end
| uu____9747 -> begin
(

let uu____9748 = (

let uu___103_9749 = s
in (

let uu____9750 = (filter_out_abstract s.FStar_Syntax_Syntax.sigquals)
in {FStar_Syntax_Syntax.sigel = uu___103_9749.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___103_9749.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu____9750; FStar_Syntax_Syntax.sigmeta = uu___103_9749.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___103_9749.FStar_Syntax_Syntax.sigattrs}))
in (uu____9748)::[])
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____9753) -> begin
(s)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____9754) -> begin
(s)::[]
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____9755) -> begin
(s)::[]
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____9756) -> begin
(s)::[]
end
| FStar_Syntax_Syntax.Sig_pragma (uu____9769) -> begin
(s)::[]
end))
in (

let uu___104_9770 = m
in (

let uu____9771 = (

let uu____9772 = (FStar_List.map extract_sigelt m.FStar_Syntax_Syntax.declarations)
in (FStar_List.flatten uu____9772))
in {FStar_Syntax_Syntax.name = uu___104_9770.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu____9771; FStar_Syntax_Syntax.exports = uu___104_9770.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = true}))))))))))))))))


let pop_context : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Env.env = (fun env msg -> ((

let uu____9786 = (FStar_Syntax_DsEnv.pop ())
in (FStar_All.pipe_right uu____9786 FStar_Pervasives.ignore));
(

let en = (FStar_TypeChecker_Env.pop env msg)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
en;
));
))


let push_context : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Env.env = (fun env msg -> (

let dsenv1 = (FStar_Syntax_DsEnv.push env.FStar_TypeChecker_Env.dsenv)
in (

let env1 = (FStar_TypeChecker_Env.push env msg)
in (

let uu___105_9797 = env1
in {FStar_TypeChecker_Env.solver = uu___105_9797.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___105_9797.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___105_9797.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___105_9797.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___105_9797.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___105_9797.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___105_9797.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___105_9797.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___105_9797.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___105_9797.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___105_9797.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___105_9797.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___105_9797.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___105_9797.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___105_9797.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___105_9797.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___105_9797.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___105_9797.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___105_9797.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___105_9797.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___105_9797.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___105_9797.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___105_9797.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___105_9797.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___105_9797.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___105_9797.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___105_9797.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___105_9797.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___105_9797.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___105_9797.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___105_9797.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___105_9797.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___105_9797.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___105_9797.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = dsenv1; FStar_TypeChecker_Env.dep_graph = uu___105_9797.FStar_TypeChecker_Env.dep_graph}))))


let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (

let verify = (FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let action = (match (verify) with
| true -> begin
"Verifying"
end
| uu____9814 -> begin
"Lax-checking"
end)
in (

let label1 = (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____9816 -> begin
"implementation"
end)
in ((

let uu____9818 = (FStar_Options.debug_any ())
in (match (uu____9818) with
| true -> begin
(FStar_Util.print3 "%s %s of %s\n" action label1 modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
end
| uu____9819 -> begin
()
end));
(

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____9821 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let env1 = (

let uu___106_9823 = env
in {FStar_TypeChecker_Env.solver = uu___106_9823.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___106_9823.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___106_9823.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___106_9823.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___106_9823.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___106_9823.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___106_9823.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___106_9823.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___106_9823.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___106_9823.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___106_9823.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___106_9823.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___106_9823.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___106_9823.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___106_9823.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___106_9823.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = (not (verify)); FStar_TypeChecker_Env.lax = uu___106_9823.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___106_9823.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___106_9823.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___106_9823.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___106_9823.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___106_9823.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___106_9823.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___106_9823.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___106_9823.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___106_9823.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___106_9823.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___106_9823.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___106_9823.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___106_9823.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___106_9823.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___106_9823.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___106_9823.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___106_9823.FStar_TypeChecker_Env.dep_graph})
in (

let env2 = (FStar_TypeChecker_Env.set_current_module env1 modul.FStar_Syntax_Syntax.name)
in (

let uu____9825 = (tc_decls env2 modul.FStar_Syntax_Syntax.declarations)
in (match (uu____9825) with
| (ses, exports, env3) -> begin
(((

let uu___107_9858 = modul
in {FStar_Syntax_Syntax.name = uu___107_9858.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = uu___107_9858.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___107_9858.FStar_Syntax_Syntax.is_interface})), (exports), (env3))
end)))));
)))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let uu____9880 = (tc_decls env decls)
in (match (uu____9880) with
| (ses, exports, env1) -> begin
(

let modul1 = (

let uu___108_9911 = modul
in {FStar_Syntax_Syntax.name = uu___108_9911.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = uu___108_9911.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___108_9911.FStar_Syntax_Syntax.is_interface})
in ((modul1), (exports), (env1)))
end)))


let rec tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_TypeChecker_Env.env) = (fun env0 m -> (

let lax_mode = env0.FStar_TypeChecker_Env.lax
in (

let msg = (Prims.strcat "Internals for " m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let env01 = (push_context env0 msg)
in (

let uu____9957 = (tc_partial_modul env01 m)
in (match (uu____9957) with
| (modul, non_private_decls, env) -> begin
(

let uu____9981 = (finish_partial_modul false env modul non_private_decls)
in (match (uu____9981) with
| (m1, m_opt, env1) -> begin
((m1), (m_opt), ((

let uu___109_10008 = env1
in {FStar_TypeChecker_Env.solver = uu___109_10008.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___109_10008.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___109_10008.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___109_10008.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___109_10008.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___109_10008.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___109_10008.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___109_10008.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___109_10008.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___109_10008.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___109_10008.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___109_10008.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___109_10008.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___109_10008.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___109_10008.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___109_10008.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___109_10008.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___109_10008.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = lax_mode; FStar_TypeChecker_Env.lax_universes = uu___109_10008.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___109_10008.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___109_10008.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___109_10008.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___109_10008.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___109_10008.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___109_10008.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___109_10008.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___109_10008.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___109_10008.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___109_10008.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___109_10008.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___109_10008.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___109_10008.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___109_10008.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___109_10008.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___109_10008.FStar_TypeChecker_Env.dep_graph})))
end))
end))))))
and finish_partial_modul : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_TypeChecker_Env.env) = (fun loading_from_cache en m exports -> (

let uu____10023 = (((not (loading_from_cache)) && (FStar_Options.use_extracted_interfaces ())) && (not (m.FStar_Syntax_Syntax.is_interface)))
in (match (uu____10023) with
| true -> begin
(

let en0 = (pop_context en (Prims.strcat "Ending modul " m.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (

let en01 = (

let uu___110_10034 = en0
in (

let uu____10035 = (

let uu____10048 = (FStar_All.pipe_right en.FStar_TypeChecker_Env.qtbl_name_and_index FStar_Pervasives_Native.fst)
in ((uu____10048), (FStar_Pervasives_Native.None)))
in {FStar_TypeChecker_Env.solver = uu___110_10034.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___110_10034.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___110_10034.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___110_10034.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___110_10034.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___110_10034.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___110_10034.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___110_10034.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___110_10034.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___110_10034.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___110_10034.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___110_10034.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___110_10034.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___110_10034.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___110_10034.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___110_10034.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___110_10034.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___110_10034.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___110_10034.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___110_10034.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___110_10034.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___110_10034.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___110_10034.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___110_10034.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___110_10034.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___110_10034.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___110_10034.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu____10035; FStar_TypeChecker_Env.proof_ns = uu___110_10034.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___110_10034.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___110_10034.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___110_10034.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___110_10034.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___110_10034.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___110_10034.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___110_10034.FStar_TypeChecker_Env.dep_graph}))
in (

let en02 = (match ((FStar_Ident.lid_equals en01.FStar_TypeChecker_Env.curmodule FStar_Parser_Const.prims_lid)) with
| true -> begin
(

let uu___111_10086 = en01
in {FStar_TypeChecker_Env.solver = uu___111_10086.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___111_10086.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___111_10086.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___111_10086.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___111_10086.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___111_10086.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___111_10086.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___111_10086.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___111_10086.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___111_10086.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___111_10086.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___111_10086.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___111_10086.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___111_10086.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___111_10086.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___111_10086.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___111_10086.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___111_10086.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___111_10086.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___111_10086.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___111_10086.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___111_10086.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___111_10086.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___111_10086.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___111_10086.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___111_10086.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___111_10086.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___111_10086.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___111_10086.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___111_10086.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___111_10086.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___111_10086.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___111_10086.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___111_10086.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___111_10086.FStar_TypeChecker_Env.dep_graph})
end
| uu____10087 -> begin
en01
end)
in ((

let uu____10089 = (

let uu____10090 = (FStar_Options.interactive ())
in (not (uu____10090)))
in (match (uu____10089) with
| true -> begin
(

let uu____10091 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right uu____10091 FStar_Pervasives.ignore))
end
| uu____10092 -> begin
()
end));
(

let modul_iface = (extract_interface en m)
in ((

let uu____10095 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug en) FStar_Options.Low)
in (match (uu____10095) with
| true -> begin
(

let uu____10096 = (

let uu____10097 = (FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____10097) with
| true -> begin
""
end
| uu____10098 -> begin
" (in lax mode) "
end))
in (

let uu____10099 = (

let uu____10100 = (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____10100) with
| true -> begin
(

let uu____10101 = (

let uu____10102 = (FStar_Syntax_Print.modul_to_string m)
in (Prims.strcat uu____10102 "\n"))
in (Prims.strcat "\nfrom: " uu____10101))
end
| uu____10103 -> begin
""
end))
in (

let uu____10104 = (

let uu____10105 = (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____10105) with
| true -> begin
(

let uu____10106 = (

let uu____10107 = (FStar_Syntax_Print.modul_to_string modul_iface)
in (Prims.strcat uu____10107 "\n"))
in (Prims.strcat "\nto: " uu____10106))
end
| uu____10108 -> begin
""
end))
in (FStar_Util.print4 "Extracting and type checking module %s interface%s%s%s\n" m.FStar_Syntax_Syntax.name.FStar_Ident.str uu____10096 uu____10099 uu____10104))))
end
| uu____10109 -> begin
()
end));
(

let env0 = (

let uu___112_10111 = en02
in {FStar_TypeChecker_Env.solver = uu___112_10111.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___112_10111.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___112_10111.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___112_10111.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___112_10111.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___112_10111.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___112_10111.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___112_10111.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___112_10111.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___112_10111.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___112_10111.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___112_10111.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___112_10111.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___112_10111.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___112_10111.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___112_10111.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = true; FStar_TypeChecker_Env.admit = uu___112_10111.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___112_10111.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___112_10111.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___112_10111.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___112_10111.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___112_10111.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___112_10111.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___112_10111.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___112_10111.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___112_10111.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___112_10111.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___112_10111.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___112_10111.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___112_10111.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___112_10111.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___112_10111.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___112_10111.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___112_10111.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___112_10111.FStar_TypeChecker_Env.dep_graph})
in (

let uu____10112 = (tc_modul en02 modul_iface)
in (match (uu____10112) with
| (modul_iface1, must_be_none, env) -> begin
(match ((Prims.op_disEquality must_be_none FStar_Pervasives_Native.None)) with
| true -> begin
(failwith "Impossible! Expected the second component to be None")
end
| uu____10154 -> begin
(((

let uu___113_10158 = m
in {FStar_Syntax_Syntax.name = uu___113_10158.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu___113_10158.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = modul_iface1.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___113_10158.FStar_Syntax_Syntax.is_interface})), (FStar_Pervasives_Native.Some (modul_iface1)), (env))
end)
end)));
));
))))
end
| uu____10159 -> begin
(

let modul = (

let uu____10161 = (FStar_Options.use_extracted_interfaces ())
in (match (uu____10161) with
| true -> begin
(

let uu___114_10162 = m
in {FStar_Syntax_Syntax.name = uu___114_10162.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu___114_10162.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = m.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.is_interface = uu___114_10162.FStar_Syntax_Syntax.is_interface})
end
| uu____10163 -> begin
(

let uu___115_10164 = m
in {FStar_Syntax_Syntax.name = uu___115_10164.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu___115_10164.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = uu___115_10164.FStar_Syntax_Syntax.is_interface})
end))
in (

let env = (FStar_TypeChecker_Env.finish_module en modul)
in ((

let uu____10167 = (FStar_All.pipe_right env.FStar_TypeChecker_Env.qtbl_name_and_index FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____10167 FStar_Util.smap_clear));
(

let uu____10195 = (((

let uu____10198 = (FStar_Options.lax ())
in (not (uu____10198))) && (

let uu____10200 = (FStar_Options.use_extracted_interfaces ())
in (not (uu____10200)))) && (not (loading_from_cache)))
in (match (uu____10195) with
| true -> begin
(check_exports env modul exports)
end
| uu____10201 -> begin
()
end));
(

let uu____10203 = (pop_context env (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (FStar_All.pipe_right uu____10203 FStar_Pervasives.ignore));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul);
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
(

let uu____10207 = (

let uu____10208 = (FStar_Options.interactive ())
in (not (uu____10208)))
in (match (uu____10207) with
| true -> begin
(

let uu____10209 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right uu____10209 FStar_Pervasives.ignore))
end
| uu____10210 -> begin
()
end));
((modul), (FStar_Pervasives_Native.None), (env));
)))
end)))


let load_checked_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_TypeChecker_Env.env = (fun en m -> (

let env = (FStar_TypeChecker_Env.set_current_module en m.FStar_Syntax_Syntax.name)
in (

let env1 = (

let uu____10221 = (

let uu____10222 = (FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name)
in (Prims.strcat "Internals for " uu____10222))
in (push_context env uu____10221))
in (

let env2 = (FStar_List.fold_left (fun env2 se -> (

let env3 = (FStar_TypeChecker_Env.push_sigelt env2 se)
in (

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in ((FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (

let uu____10241 = (FStar_TypeChecker_Env.try_lookup_lid env3 lid)
in ()))));
env3;
)))) env1 m.FStar_Syntax_Syntax.declarations)
in (

let uu____10262 = (finish_partial_modul true env2 m m.FStar_Syntax_Syntax.exports)
in (match (uu____10262) with
| (uu____10271, uu____10272, env3) -> begin
env3
end))))))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_TypeChecker_Env.env) = (fun env m -> ((

let uu____10293 = (FStar_Options.debug_any ())
in (match (uu____10293) with
| true -> begin
(

let uu____10294 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (match (m.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"i\'face"
end
| uu____10295 -> begin
"module"
end) uu____10294))
end
| uu____10296 -> begin
()
end));
(

let env1 = (

let uu___116_10298 = env
in (

let uu____10299 = (

let uu____10300 = (FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (not (uu____10300)))
in {FStar_TypeChecker_Env.solver = uu___116_10298.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___116_10298.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___116_10298.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___116_10298.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___116_10298.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___116_10298.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___116_10298.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___116_10298.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___116_10298.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___116_10298.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___116_10298.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___116_10298.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___116_10298.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___116_10298.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___116_10298.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___116_10298.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___116_10298.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___116_10298.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu____10299; FStar_TypeChecker_Env.lax_universes = uu___116_10298.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___116_10298.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___116_10298.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___116_10298.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___116_10298.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___116_10298.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___116_10298.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___116_10298.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___116_10298.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.proof_ns = uu___116_10298.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___116_10298.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___116_10298.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___116_10298.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___116_10298.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___116_10298.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___116_10298.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___116_10298.FStar_TypeChecker_Env.dep_graph}))
in (

let uu____10301 = (tc_modul env1 m)
in (match (uu____10301) with
| (m1, m_iface_opt, env2) -> begin
((

let uu____10326 = (FStar_Options.dump_module m1.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____10326) with
| true -> begin
(

let uu____10327 = (FStar_Syntax_Print.modul_to_string m1)
in (FStar_Util.print1 "Module after type checking:\n%s\n" uu____10327))
end
| uu____10328 -> begin
()
end));
(

let uu____10330 = ((FStar_Options.dump_module m1.FStar_Syntax_Syntax.name.FStar_Ident.str) && (FStar_Options.debug_at_level m1.FStar_Syntax_Syntax.name.FStar_Ident.str (FStar_Options.Other ("Normalize"))))
in (match (uu____10330) with
| true -> begin
(

let normalize_toplevel_lets = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((b, lbs), ids) -> begin
(

let n1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]))
in (

let update = (fun lb -> (

let uu____10361 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____10361) with
| (univnames1, e) -> begin
(

let uu___117_10368 = lb
in (

let uu____10369 = (

let uu____10372 = (FStar_TypeChecker_Env.push_univ_vars env2 univnames1)
in (n1 uu____10372 e))
in {FStar_Syntax_Syntax.lbname = uu___117_10368.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___117_10368.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___117_10368.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___117_10368.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____10369; FStar_Syntax_Syntax.lbattrs = uu___117_10368.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___117_10368.FStar_Syntax_Syntax.lbpos}))
end)))
in (

let uu___118_10373 = se
in (

let uu____10374 = (

let uu____10375 = (

let uu____10382 = (

let uu____10389 = (FStar_List.map update lbs)
in ((b), (uu____10389)))
in ((uu____10382), (ids)))
in FStar_Syntax_Syntax.Sig_let (uu____10375))
in {FStar_Syntax_Syntax.sigel = uu____10374; FStar_Syntax_Syntax.sigrng = uu___118_10373.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___118_10373.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___118_10373.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___118_10373.FStar_Syntax_Syntax.sigattrs}))))
end
| uu____10402 -> begin
se
end))
in (

let normalized_module = (

let uu___119_10404 = m1
in (

let uu____10405 = (FStar_List.map normalize_toplevel_lets m1.FStar_Syntax_Syntax.declarations)
in {FStar_Syntax_Syntax.name = uu___119_10404.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu____10405; FStar_Syntax_Syntax.exports = uu___119_10404.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___119_10404.FStar_Syntax_Syntax.is_interface}))
in (

let uu____10406 = (FStar_Syntax_Print.modul_to_string normalized_module)
in (FStar_Util.print1 "%s\n" uu____10406))))
end
| uu____10407 -> begin
()
end));
((m1), (m_iface_opt), (env2));
)
end)));
))




