
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
| uu____47 -> begin
(Prims.parse_int "0")
end)))
in (

let uu____48 = (FStar_Options.reuse_hint_for ())
in (match (uu____48) with
| FStar_Pervasives_Native.Some (l) -> begin
(

let lid = (

let uu____53 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_add_suffix uu____53 l))
in (

let uu___65_54 = env
in (

let uu____55 = (

let uu____68 = (

let uu____75 = (

let uu____80 = (get_n lid)
in ((lid), (uu____80)))
in FStar_Pervasives_Native.Some (uu____75))
in ((tbl), (uu____68)))
in {FStar_TypeChecker_Env.solver = uu___65_54.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___65_54.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___65_54.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___65_54.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___65_54.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___65_54.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___65_54.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___65_54.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___65_54.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___65_54.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___65_54.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___65_54.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___65_54.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___65_54.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___65_54.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___65_54.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___65_54.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___65_54.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___65_54.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___65_54.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___65_54.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___65_54.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___65_54.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___65_54.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___65_54.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___65_54.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___65_54.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___65_54.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu____55; FStar_TypeChecker_Env.normalized_eff_names = uu___65_54.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___65_54.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___65_54.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___65_54.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___65_54.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___65_54.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___65_54.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___65_54.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___65_54.FStar_TypeChecker_Env.dep_graph})))
end
| FStar_Pervasives_Native.None -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (

let lid = (match (lids) with
| [] -> begin
(

let uu____97 = (FStar_TypeChecker_Env.current_module env)
in (

let uu____98 = (

let uu____99 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_right uu____99 FStar_Util.string_of_int))
in (FStar_Ident.lid_add_suffix uu____97 uu____98)))
end
| (l)::uu____101 -> begin
l
end)
in (

let uu___66_104 = env
in (

let uu____105 = (

let uu____118 = (

let uu____125 = (

let uu____130 = (get_n lid)
in ((lid), (uu____130)))
in FStar_Pervasives_Native.Some (uu____125))
in ((tbl), (uu____118)))
in {FStar_TypeChecker_Env.solver = uu___66_104.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___66_104.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___66_104.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___66_104.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___66_104.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___66_104.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___66_104.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___66_104.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___66_104.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___66_104.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___66_104.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___66_104.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___66_104.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___66_104.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___66_104.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___66_104.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___66_104.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___66_104.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___66_104.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___66_104.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___66_104.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___66_104.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___66_104.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___66_104.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___66_104.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___66_104.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___66_104.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___66_104.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu____105; FStar_TypeChecker_Env.normalized_eff_names = uu___66_104.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___66_104.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___66_104.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___66_104.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___66_104.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___66_104.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___66_104.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___66_104.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___66_104.FStar_TypeChecker_Env.dep_graph}))))
end)))))


let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_Options.log_types ()) && (

let uu____149 = (

let uu____150 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____150))
in (not (uu____149)))))


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let uu____166 = (FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k)
in (match (uu____166) with
| (t1, c, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
t1;
)
end)))


let recheck_debug : Prims.string  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s env t -> ((

let uu____193 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____193) with
| true -> begin
(

let uu____194 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Term has been %s-transformed to:\n%s\n----------\n" s uu____194))
end
| uu____195 -> begin
()
end));
(

let uu____196 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (uu____196) with
| (t', uu____204, uu____205) -> begin
((

let uu____207 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____207) with
| true -> begin
(

let uu____208 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print1 "Re-checked; got:\n%s\n----------\n" uu____208))
end
| uu____209 -> begin
()
end));
t';
)
end));
))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (

let uu____225 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env uu____225)))


let check_nogen : 'Auu____234 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  ('Auu____234 Prims.list * FStar_Syntax_Syntax.term) = (fun env t k -> (

let t1 = (tc_check_trivial_guard env t k)
in (

let uu____257 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t1)
in (([]), (uu____257)))))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun env m s -> (

let fail1 = (fun uu____292 -> (

let uu____293 = (FStar_TypeChecker_Err.unexpected_signature_for_monad env m s)
in (

let uu____298 = (FStar_Ident.range_of_lid m)
in (FStar_Errors.raise_error uu____293 uu____298))))
in (

let s1 = (FStar_Syntax_Subst.compress s)
in (match (s1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs1 = (FStar_Syntax_Subst.open_binders bs)
in (match (bs1) with
| ((a, uu____338))::((wp, uu____340))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____355 -> begin
(fail1 ())
end))
end
| uu____356 -> begin
(fail1 ())
end))))


let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (

let uu____367 = (FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs)
in (match (uu____367) with
| (open_annotated_univs, annotated_univ_names) -> begin
(

let open_univs = (fun n_binders t -> (

let uu____397 = (FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs)
in (FStar_Syntax_Subst.subst uu____397 t)))
in (

let open_univs_binders = (fun n_binders bs -> (

let uu____411 = (FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs)
in (FStar_Syntax_Subst.subst_binders uu____411 bs)))
in (

let n_effect_params = (FStar_List.length ed.FStar_Syntax_Syntax.binders)
in (

let uu____419 = (

let uu____426 = (open_univs_binders (Prims.parse_int "0") ed.FStar_Syntax_Syntax.binders)
in (

let uu____427 = (open_univs n_effect_params ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Subst.open_term' uu____426 uu____427)))
in (match (uu____419) with
| (effect_params_un, signature_un, opening) -> begin
(

let env = (FStar_TypeChecker_Env.push_univ_vars env0 annotated_univ_names)
in (

let uu____438 = (FStar_TypeChecker_TcTerm.tc_tparams env effect_params_un)
in (match (uu____438) with
| (effect_params, env1, uu____447) -> begin
(

let uu____448 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un)
in (match (uu____448) with
| (signature, uu____454) -> begin
(

let ed1 = (

let uu___67_456 = ed
in {FStar_Syntax_Syntax.cattributes = uu___67_456.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___67_456.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___67_456.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = uu___67_456.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = uu___67_456.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = uu___67_456.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = uu___67_456.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = uu___67_456.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = uu___67_456.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = uu___67_456.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = uu___67_456.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = uu___67_456.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = uu___67_456.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = uu___67_456.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = uu___67_456.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = uu___67_456.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = uu___67_456.FStar_Syntax_Syntax.actions; FStar_Syntax_Syntax.eff_attrs = uu___67_456.FStar_Syntax_Syntax.eff_attrs})
in (

let ed2 = (match (((effect_params), (annotated_univ_names))) with
| ([], []) -> begin
ed1
end
| uu____478 -> begin
(

let op = (fun uu____508 -> (match (uu____508) with
| (us, t) -> begin
(

let n_us = (FStar_List.length us)
in (

let uu____528 = (

let uu____529 = (FStar_Syntax_Subst.shift_subst n_us opening)
in (

let uu____538 = (open_univs n_us t)
in (FStar_Syntax_Subst.subst uu____529 uu____538)))
in ((us), (uu____528))))
end))
in (

let uu___68_547 = ed1
in (

let uu____548 = (op ed1.FStar_Syntax_Syntax.ret_wp)
in (

let uu____549 = (op ed1.FStar_Syntax_Syntax.bind_wp)
in (

let uu____550 = (op ed1.FStar_Syntax_Syntax.if_then_else)
in (

let uu____551 = (op ed1.FStar_Syntax_Syntax.ite_wp)
in (

let uu____552 = (op ed1.FStar_Syntax_Syntax.stronger)
in (

let uu____553 = (op ed1.FStar_Syntax_Syntax.close_wp)
in (

let uu____554 = (op ed1.FStar_Syntax_Syntax.assert_p)
in (

let uu____555 = (op ed1.FStar_Syntax_Syntax.assume_p)
in (

let uu____556 = (op ed1.FStar_Syntax_Syntax.null_wp)
in (

let uu____557 = (op ed1.FStar_Syntax_Syntax.trivial)
in (

let uu____558 = (

let uu____559 = (op (([]), (ed1.FStar_Syntax_Syntax.repr)))
in (FStar_Pervasives_Native.snd uu____559))
in (

let uu____570 = (op ed1.FStar_Syntax_Syntax.return_repr)
in (

let uu____571 = (op ed1.FStar_Syntax_Syntax.bind_repr)
in (

let uu____572 = (FStar_List.map (fun a -> (

let uu___69_580 = a
in (

let uu____581 = (

let uu____582 = (op ((a.FStar_Syntax_Syntax.action_univs), (a.FStar_Syntax_Syntax.action_defn)))
in (FStar_Pervasives_Native.snd uu____582))
in (

let uu____593 = (

let uu____594 = (op ((a.FStar_Syntax_Syntax.action_univs), (a.FStar_Syntax_Syntax.action_typ)))
in (FStar_Pervasives_Native.snd uu____594))
in {FStar_Syntax_Syntax.action_name = uu___69_580.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___69_580.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___69_580.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = uu___69_580.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = uu____581; FStar_Syntax_Syntax.action_typ = uu____593})))) ed1.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.cattributes = uu___68_547.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___68_547.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = annotated_univ_names; FStar_Syntax_Syntax.binders = uu___68_547.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = uu___68_547.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = uu____548; FStar_Syntax_Syntax.bind_wp = uu____549; FStar_Syntax_Syntax.if_then_else = uu____550; FStar_Syntax_Syntax.ite_wp = uu____551; FStar_Syntax_Syntax.stronger = uu____552; FStar_Syntax_Syntax.close_wp = uu____553; FStar_Syntax_Syntax.assert_p = uu____554; FStar_Syntax_Syntax.assume_p = uu____555; FStar_Syntax_Syntax.null_wp = uu____556; FStar_Syntax_Syntax.trivial = uu____557; FStar_Syntax_Syntax.repr = uu____558; FStar_Syntax_Syntax.return_repr = uu____570; FStar_Syntax_Syntax.bind_repr = uu____571; FStar_Syntax_Syntax.actions = uu____572; FStar_Syntax_Syntax.eff_attrs = uu___68_547.FStar_Syntax_Syntax.eff_attrs}))))))))))))))))
end)
in (

let wp_with_fresh_result_type = (fun env2 mname signature1 -> (

let fail1 = (fun t -> (

let uu____639 = (FStar_TypeChecker_Err.unexpected_signature_for_monad env2 mname t)
in (

let uu____644 = (FStar_Ident.range_of_lid mname)
in (FStar_Errors.raise_error uu____639 uu____644))))
in (

let uu____651 = (

let uu____652 = (FStar_Syntax_Subst.compress signature1)
in uu____652.FStar_Syntax_Syntax.n)
in (match (uu____651) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs1 = (FStar_Syntax_Subst.open_binders bs)
in (match (bs1) with
| ((a, uu____687))::((wp, uu____689))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____704 -> begin
(fail1 signature1)
end))
end
| uu____705 -> begin
(fail1 signature1)
end))))
in (

let uu____706 = (wp_with_fresh_result_type env1 ed2.FStar_Syntax_Syntax.mname ed2.FStar_Syntax_Syntax.signature)
in (match (uu____706) with
| (a, wp_a) -> begin
(

let fresh_effect_signature = (fun uu____730 -> (match (annotated_univ_names) with
| [] -> begin
(

let uu____737 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un)
in (match (uu____737) with
| (signature1, uu____749) -> begin
(wp_with_fresh_result_type env1 ed2.FStar_Syntax_Syntax.mname signature1)
end))
end
| uu____750 -> begin
(

let uu____753 = (

let uu____758 = (

let uu____759 = (FStar_Syntax_Subst.close_univ_vars annotated_univ_names signature)
in ((annotated_univ_names), (uu____759)))
in (FStar_TypeChecker_Env.inst_tscheme uu____758))
in (match (uu____753) with
| (uu____772, signature1) -> begin
(wp_with_fresh_result_type env1 ed2.FStar_Syntax_Syntax.mname signature1)
end))
end))
in (

let env2 = (

let uu____775 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None ed2.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env1 uu____775))
in ((

let uu____777 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED")))
in (match (uu____777) with
| true -> begin
(

let uu____778 = (FStar_Syntax_Print.lid_to_string ed2.FStar_Syntax_Syntax.mname)
in (

let uu____779 = (FStar_Syntax_Print.binders_to_string " " ed2.FStar_Syntax_Syntax.binders)
in (

let uu____780 = (FStar_Syntax_Print.term_to_string ed2.FStar_Syntax_Syntax.signature)
in (

let uu____781 = (

let uu____782 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Print.term_to_string uu____782))
in (

let uu____783 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.sort)
in (FStar_Util.print5 "Checking effect signature: %s %s : %s\n(a is %s:%s)\n" uu____778 uu____779 uu____780 uu____781 uu____783))))))
end
| uu____784 -> begin
()
end));
(

let check_and_gen' = (fun env3 uu____805 k -> (match (uu____805) with
| (us, t) -> begin
(match (annotated_univ_names) with
| [] -> begin
(check_and_gen env3 t k)
end
| (uu____819)::uu____820 -> begin
(

let uu____823 = (FStar_Syntax_Subst.subst_tscheme open_annotated_univs ((us), (t)))
in (match (uu____823) with
| (us1, t1) -> begin
(

let uu____838 = (FStar_Syntax_Subst.open_univ_vars us1 t1)
in (match (uu____838) with
| (us2, t2) -> begin
(

let uu____845 = (

let uu____846 = (FStar_TypeChecker_Env.push_univ_vars env3 us2)
in (tc_check_trivial_guard uu____846 t2 k))
in (

let uu____847 = (FStar_Syntax_Subst.close_univ_vars us2 t2)
in ((us2), (uu____847))))
end))
end))
end)
end))
in (

let return_wp = (

let expected_k = (

let uu____852 = (

let uu____859 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____864 = (

let uu____871 = (

let uu____876 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____876))
in (uu____871)::[])
in (uu____859)::uu____864))
in (

let uu____889 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow uu____852 uu____889)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.ret_wp expected_k))
in (

let bind_wp = (

let uu____893 = (fresh_effect_signature ())
in (match (uu____893) with
| (b, wp_b) -> begin
(

let a_wp_b = (

let uu____909 = (

let uu____916 = (

let uu____921 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____921))
in (uu____916)::[])
in (

let uu____930 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____909 uu____930)))
in (

let expected_k = (

let uu____936 = (

let uu____943 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Syntax.t_range)
in (

let uu____948 = (

let uu____955 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____960 = (

let uu____967 = (FStar_Syntax_Syntax.mk_binder b)
in (

let uu____972 = (

let uu____979 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____984 = (

let uu____991 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (uu____991)::[])
in (uu____979)::uu____984))
in (uu____967)::uu____972))
in (uu____955)::uu____960))
in (uu____943)::uu____948))
in (

let uu____1020 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____936 uu____1020)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else1 = (

let p = (

let uu____1025 = (

let uu____1028 = (FStar_Ident.range_of_lid ed2.FStar_Syntax_Syntax.mname)
in FStar_Pervasives_Native.Some (uu____1028))
in (

let uu____1029 = (

let uu____1030 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____1030 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.new_bv uu____1025 uu____1029)))
in (

let expected_k = (

let uu____1042 = (

let uu____1049 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1054 = (

let uu____1061 = (FStar_Syntax_Syntax.mk_binder p)
in (

let uu____1066 = (

let uu____1073 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____1078 = (

let uu____1085 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1085)::[])
in (uu____1073)::uu____1078))
in (uu____1061)::uu____1066))
in (uu____1049)::uu____1054))
in (

let uu____1110 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1042 uu____1110)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (

let uu____1117 = (

let uu____1124 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1129 = (

let uu____1136 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1136)::[])
in (uu____1124)::uu____1129))
in (

let uu____1153 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1117 uu____1153)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let uu____1157 = (FStar_Syntax_Util.type_u ())
in (match (uu____1157) with
| (t, uu____1163) -> begin
(

let expected_k = (

let uu____1167 = (

let uu____1174 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1179 = (

let uu____1186 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____1191 = (

let uu____1198 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1198)::[])
in (uu____1186)::uu____1191))
in (uu____1174)::uu____1179))
in (

let uu____1219 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow uu____1167 uu____1219)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (

let uu____1224 = (

let uu____1227 = (FStar_Ident.range_of_lid ed2.FStar_Syntax_Syntax.mname)
in FStar_Pervasives_Native.Some (uu____1227))
in (

let uu____1228 = (

let uu____1229 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____1229 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.new_bv uu____1224 uu____1228)))
in (

let b_wp_a = (

let uu____1241 = (

let uu____1248 = (

let uu____1253 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder uu____1253))
in (uu____1248)::[])
in (

let uu____1262 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1241 uu____1262)))
in (

let expected_k = (

let uu____1268 = (

let uu____1275 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1280 = (

let uu____1287 = (FStar_Syntax_Syntax.mk_binder b)
in (

let uu____1292 = (

let uu____1299 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (uu____1299)::[])
in (uu____1287)::uu____1292))
in (uu____1275)::uu____1280))
in (

let uu____1320 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1268 uu____1320)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (

let uu____1327 = (

let uu____1334 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1339 = (

let uu____1346 = (

let uu____1351 = (

let uu____1352 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____1352 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.null_binder uu____1351))
in (

let uu____1361 = (

let uu____1368 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1368)::[])
in (uu____1346)::uu____1361))
in (uu____1334)::uu____1339))
in (

let uu____1389 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1327 uu____1389)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (

let uu____1396 = (

let uu____1403 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1408 = (

let uu____1415 = (

let uu____1420 = (

let uu____1421 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____1421 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.null_binder uu____1420))
in (

let uu____1430 = (

let uu____1437 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1437)::[])
in (uu____1415)::uu____1430))
in (uu____1403)::uu____1408))
in (

let uu____1458 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1396 uu____1458)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (

let uu____1465 = (

let uu____1472 = (FStar_Syntax_Syntax.mk_binder a)
in (uu____1472)::[])
in (

let uu____1485 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1465 uu____1485)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let uu____1489 = (FStar_Syntax_Util.type_u ())
in (match (uu____1489) with
| (t, uu____1495) -> begin
(

let expected_k = (

let uu____1499 = (

let uu____1506 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1511 = (

let uu____1518 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1518)::[])
in (uu____1506)::uu____1511))
in (

let uu____1535 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow uu____1499 uu____1535)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let uu____1538 = (

let uu____1551 = (

let uu____1552 = (FStar_Syntax_Subst.compress ed2.FStar_Syntax_Syntax.repr)
in uu____1552.FStar_Syntax_Syntax.n)
in (match (uu____1551) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((ed2.FStar_Syntax_Syntax.repr), (ed2.FStar_Syntax_Syntax.bind_repr), (ed2.FStar_Syntax_Syntax.return_repr), (ed2.FStar_Syntax_Syntax.actions))
end
| uu____1569 -> begin
(

let repr = (

let uu____1571 = (FStar_Syntax_Util.type_u ())
in (match (uu____1571) with
| (t, uu____1577) -> begin
(

let expected_k = (

let uu____1581 = (

let uu____1588 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1593 = (

let uu____1600 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1600)::[])
in (uu____1588)::uu____1593))
in (

let uu____1617 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow uu____1581 uu____1617)))
in (tc_check_trivial_guard env2 ed2.FStar_Syntax_Syntax.repr expected_k))
end))
in (

let mk_repr' = (fun t wp -> (

let repr1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env2 repr)
in (

let uu____1634 = (

let uu____1641 = (

let uu____1642 = (

let uu____1657 = (

let uu____1666 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____1667 = (

let uu____1670 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____1670)::[])
in (uu____1666)::uu____1667))
in ((repr1), (uu____1657)))
in FStar_Syntax_Syntax.Tm_app (uu____1642))
in (FStar_Syntax_Syntax.mk uu____1641))
in (uu____1634 FStar_Pervasives_Native.None FStar_Range.dummyRange))))
in (

let mk_repr = (fun a1 wp -> (

let uu____1697 = (FStar_Syntax_Syntax.bv_to_name a1)
in (mk_repr' uu____1697 wp)))
in (

let destruct_repr = (fun t -> (

let uu____1712 = (

let uu____1713 = (FStar_Syntax_Subst.compress t)
in uu____1713.FStar_Syntax_Syntax.n)
in (match (uu____1712) with
| FStar_Syntax_Syntax.Tm_app (uu____1724, ((t1, uu____1726))::((wp, uu____1728))::[]) -> begin
((t1), (wp))
end
| uu____1771 -> begin
(failwith "Unexpected repr type")
end)))
in (

let bind_repr = (

let r = (

let uu____1782 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.range_0 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_All.pipe_right uu____1782 FStar_Syntax_Syntax.fv_to_tm))
in (

let uu____1783 = (fresh_effect_signature ())
in (match (uu____1783) with
| (b, wp_b) -> begin
(

let a_wp_b = (

let uu____1799 = (

let uu____1806 = (

let uu____1811 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____1811))
in (uu____1806)::[])
in (

let uu____1820 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____1799 uu____1820)))
in (

let wp_f = (FStar_Syntax_Syntax.gen_bv "wp_f" FStar_Pervasives_Native.None wp_a)
in (

let wp_g = (FStar_Syntax_Syntax.gen_bv "wp_g" FStar_Pervasives_Native.None a_wp_b)
in (

let x_a = (

let uu____1826 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" FStar_Pervasives_Native.None uu____1826))
in (

let wp_g_x = (

let uu____1830 = (

let uu____1835 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (

let uu____1836 = (

let uu____1837 = (

let uu____1844 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____1844))
in (uu____1837)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____1835 uu____1836)))
in (uu____1830 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let res = (

let wp = (

let uu____1871 = (

let uu____1876 = (

let uu____1877 = (FStar_TypeChecker_Env.inst_tscheme bind_wp)
in (FStar_All.pipe_right uu____1877 FStar_Pervasives_Native.snd))
in (

let uu____1886 = (

let uu____1887 = (

let uu____1890 = (

let uu____1893 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____1894 = (

let uu____1897 = (FStar_Syntax_Syntax.bv_to_name b)
in (

let uu____1898 = (

let uu____1901 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (

let uu____1902 = (

let uu____1905 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (uu____1905)::[])
in (uu____1901)::uu____1902))
in (uu____1897)::uu____1898))
in (uu____1893)::uu____1894))
in (r)::uu____1890)
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1887))
in (FStar_Syntax_Syntax.mk_Tm_app uu____1876 uu____1886)))
in (uu____1871 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (mk_repr b wp))
in (

let maybe_range_arg = (

let uu____1921 = (FStar_Util.for_some (FStar_Syntax_Util.attr_eq FStar_Syntax_Util.dm4f_bind_range_attr) ed2.FStar_Syntax_Syntax.eff_attrs)
in (match (uu____1921) with
| true -> begin
(

let uu____1928 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Syntax.t_range)
in (

let uu____1933 = (

let uu____1940 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Syntax.t_range)
in (uu____1940)::[])
in (uu____1928)::uu____1933))
end
| uu____1957 -> begin
[]
end))
in (

let expected_k = (

let uu____1965 = (

let uu____1972 = (

let uu____1979 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1984 = (

let uu____1991 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____1991)::[])
in (uu____1979)::uu____1984))
in (

let uu____2008 = (

let uu____2015 = (

let uu____2022 = (FStar_Syntax_Syntax.mk_binder wp_f)
in (

let uu____2027 = (

let uu____2034 = (

let uu____2039 = (

let uu____2040 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (mk_repr a uu____2040))
in (FStar_Syntax_Syntax.null_binder uu____2039))
in (

let uu____2041 = (

let uu____2048 = (FStar_Syntax_Syntax.mk_binder wp_g)
in (

let uu____2053 = (

let uu____2060 = (

let uu____2065 = (

let uu____2066 = (

let uu____2073 = (FStar_Syntax_Syntax.mk_binder x_a)
in (uu____2073)::[])
in (

let uu____2086 = (

let uu____2089 = (mk_repr b wp_g_x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____2089))
in (FStar_Syntax_Util.arrow uu____2066 uu____2086)))
in (FStar_Syntax_Syntax.null_binder uu____2065))
in (uu____2060)::[])
in (uu____2048)::uu____2053))
in (uu____2034)::uu____2041))
in (uu____2022)::uu____2027))
in (FStar_List.append maybe_range_arg uu____2015))
in (FStar_List.append uu____1972 uu____2008)))
in (

let uu____2120 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow uu____1965 uu____2120)))
in (

let uu____2123 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env2 expected_k)
in (match (uu____2123) with
| (expected_k1, uu____2131, uu____2132) -> begin
(

let env3 = (FStar_TypeChecker_Env.set_range env2 (FStar_Pervasives_Native.snd ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos)
in (

let env4 = (

let uu___70_2139 = env3
in {FStar_TypeChecker_Env.solver = uu___70_2139.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___70_2139.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___70_2139.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___70_2139.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___70_2139.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___70_2139.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___70_2139.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___70_2139.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___70_2139.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___70_2139.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___70_2139.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___70_2139.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___70_2139.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___70_2139.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___70_2139.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___70_2139.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___70_2139.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___70_2139.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___70_2139.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___70_2139.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___70_2139.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___70_2139.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___70_2139.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___70_2139.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___70_2139.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___70_2139.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___70_2139.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___70_2139.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___70_2139.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___70_2139.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___70_2139.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___70_2139.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___70_2139.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___70_2139.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___70_2139.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___70_2139.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___70_2139.FStar_TypeChecker_Env.dep_graph})
in (

let br = (check_and_gen' env4 ed2.FStar_Syntax_Syntax.bind_repr expected_k1)
in br)))
end))))))))))
end)))
in (

let return_repr = (

let x_a = (

let uu____2151 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" FStar_Pervasives_Native.None uu____2151))
in (

let res = (

let wp = (

let uu____2158 = (

let uu____2163 = (

let uu____2164 = (FStar_TypeChecker_Env.inst_tscheme return_wp)
in (FStar_All.pipe_right uu____2164 FStar_Pervasives_Native.snd))
in (

let uu____2173 = (

let uu____2174 = (

let uu____2177 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____2178 = (

let uu____2181 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (uu____2181)::[])
in (uu____2177)::uu____2178))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____2174))
in (FStar_Syntax_Syntax.mk_Tm_app uu____2163 uu____2173)))
in (uu____2158 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (mk_repr a wp))
in (

let expected_k = (

let uu____2193 = (

let uu____2200 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____2205 = (

let uu____2212 = (FStar_Syntax_Syntax.mk_binder x_a)
in (uu____2212)::[])
in (uu____2200)::uu____2205))
in (

let uu____2229 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow uu____2193 uu____2229)))
in (

let uu____2232 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env2 expected_k)
in (match (uu____2232) with
| (expected_k1, uu____2248, uu____2249) -> begin
(

let env3 = (FStar_TypeChecker_Env.set_range env2 (FStar_Pervasives_Native.snd ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos)
in (

let uu____2255 = (check_and_gen' env3 ed2.FStar_Syntax_Syntax.return_repr expected_k1)
in (match (uu____2255) with
| (univs1, repr1) -> begin
(match (univs1) with
| [] -> begin
(([]), (repr1))
end
| uu____2286 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn), ("Unexpected universe-polymorphic return for effect")) repr1.FStar_Syntax_Syntax.pos)
end)
end)))
end)))))
in (

let actions = (

let check_action = (fun act -> (

let uu____2307 = (match ((Prims.op_Equality act.FStar_Syntax_Syntax.action_univs [])) with
| true -> begin
((env2), (act))
end
| uu____2316 -> begin
(

let uu____2317 = (FStar_Syntax_Subst.univ_var_opening act.FStar_Syntax_Syntax.action_univs)
in (match (uu____2317) with
| (usubst, uvs) -> begin
(

let uu____2340 = (FStar_TypeChecker_Env.push_univ_vars env2 uvs)
in (

let uu____2341 = (

let uu___71_2342 = act
in (

let uu____2343 = (FStar_Syntax_Subst.subst_binders usubst act.FStar_Syntax_Syntax.action_params)
in (

let uu____2344 = (FStar_Syntax_Subst.subst usubst act.FStar_Syntax_Syntax.action_defn)
in (

let uu____2345 = (FStar_Syntax_Subst.subst usubst act.FStar_Syntax_Syntax.action_typ)
in {FStar_Syntax_Syntax.action_name = uu___71_2342.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___71_2342.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uvs; FStar_Syntax_Syntax.action_params = uu____2343; FStar_Syntax_Syntax.action_defn = uu____2344; FStar_Syntax_Syntax.action_typ = uu____2345}))))
in ((uu____2340), (uu____2341))))
end))
end)
in (match (uu____2307) with
| (env3, act1) -> begin
(

let act_typ = (

let uu____2349 = (

let uu____2350 = (FStar_Syntax_Subst.compress act1.FStar_Syntax_Syntax.action_typ)
in uu____2350.FStar_Syntax_Syntax.n)
in (match (uu____2349) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let c1 = (FStar_Syntax_Util.comp_to_comp_typ c)
in (

let uu____2372 = (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name ed2.FStar_Syntax_Syntax.mname)
in (match (uu____2372) with
| true -> begin
(

let uu____2373 = (

let uu____2376 = (

let uu____2377 = (

let uu____2378 = (FStar_List.hd c1.FStar_Syntax_Syntax.effect_args)
in (FStar_Pervasives_Native.fst uu____2378))
in (mk_repr' c1.FStar_Syntax_Syntax.result_typ uu____2377))
in (FStar_Syntax_Syntax.mk_Total uu____2376))
in (FStar_Syntax_Util.arrow bs uu____2373))
end
| uu____2393 -> begin
act1.FStar_Syntax_Syntax.action_typ
end)))
end
| uu____2394 -> begin
act1.FStar_Syntax_Syntax.action_typ
end))
in (

let uu____2395 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env3 act_typ)
in (match (uu____2395) with
| (act_typ1, uu____2403, g_t) -> begin
(

let env' = (

let uu___72_2406 = (FStar_TypeChecker_Env.set_expected_typ env3 act_typ1)
in {FStar_TypeChecker_Env.solver = uu___72_2406.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___72_2406.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___72_2406.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___72_2406.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___72_2406.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___72_2406.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___72_2406.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___72_2406.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___72_2406.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___72_2406.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = uu___72_2406.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___72_2406.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___72_2406.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___72_2406.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___72_2406.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___72_2406.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___72_2406.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___72_2406.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___72_2406.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___72_2406.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___72_2406.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___72_2406.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___72_2406.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___72_2406.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___72_2406.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___72_2406.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___72_2406.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___72_2406.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___72_2406.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___72_2406.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___72_2406.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___72_2406.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___72_2406.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___72_2406.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___72_2406.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___72_2406.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___72_2406.FStar_TypeChecker_Env.dep_graph})
in ((

let uu____2408 = (FStar_TypeChecker_Env.debug env3 (FStar_Options.Other ("ED")))
in (match (uu____2408) with
| true -> begin
(

let uu____2409 = (FStar_Ident.text_of_lid act1.FStar_Syntax_Syntax.action_name)
in (

let uu____2410 = (FStar_Syntax_Print.term_to_string act1.FStar_Syntax_Syntax.action_defn)
in (

let uu____2411 = (FStar_Syntax_Print.term_to_string act_typ1)
in (FStar_Util.print3 "Checking action %s:\n[definition]: %s\n[cps\'d type]: %s\n" uu____2409 uu____2410 uu____2411))))
end
| uu____2412 -> begin
()
end));
(

let uu____2413 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' act1.FStar_Syntax_Syntax.action_defn)
in (match (uu____2413) with
| (act_defn, uu____2421, g_a) -> begin
(

let act_defn1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env3 act_defn)
in (

let act_typ2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::[]) env3 act_typ1)
in (

let uu____2425 = (

let act_typ3 = (FStar_Syntax_Subst.compress act_typ2)
in (match (act_typ3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____2453 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____2453) with
| (bs1, uu____2463) -> begin
(

let res = (mk_repr' FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun)
in (

let k = (

let uu____2470 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs1 uu____2470))
in (

let uu____2473 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env3 k)
in (match (uu____2473) with
| (k1, uu____2485, g) -> begin
((k1), (g))
end))))
end))
end
| uu____2487 -> begin
(

let uu____2488 = (

let uu____2493 = (

let uu____2494 = (FStar_Syntax_Print.term_to_string act_typ3)
in (

let uu____2495 = (FStar_Syntax_Print.tag_of_term act_typ3)
in (FStar_Util.format2 "Actions must have function types (not: %s, a.k.a. %s)" uu____2494 uu____2495)))
in ((FStar_Errors.Fatal_ActionMustHaveFunctionType), (uu____2493)))
in (FStar_Errors.raise_error uu____2488 act_defn1.FStar_Syntax_Syntax.pos))
end))
in (match (uu____2425) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env3 act_typ2 expected_k)
in ((

let uu____2504 = (

let uu____2505 = (

let uu____2506 = (FStar_TypeChecker_Rel.conj_guard g_t g)
in (FStar_TypeChecker_Rel.conj_guard g_k uu____2506))
in (FStar_TypeChecker_Rel.conj_guard g_a uu____2505))
in (FStar_TypeChecker_Rel.force_trivial_guard env3 uu____2504));
(

let act_typ3 = (

let uu____2508 = (

let uu____2509 = (FStar_Syntax_Subst.compress expected_k)
in uu____2509.FStar_Syntax_Syntax.n)
in (match (uu____2508) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____2530 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____2530) with
| (bs1, c1) -> begin
(

let uu____2537 = (destruct_repr (FStar_Syntax_Util.comp_result c1))
in (match (uu____2537) with
| (a1, wp) -> begin
(

let c2 = (

let uu____2557 = (

let uu____2558 = (env3.FStar_TypeChecker_Env.universe_of env3 a1)
in (uu____2558)::[])
in (

let uu____2559 = (

let uu____2568 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____2568)::[])
in {FStar_Syntax_Syntax.comp_univs = uu____2557; FStar_Syntax_Syntax.effect_name = ed2.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a1; FStar_Syntax_Syntax.effect_args = uu____2559; FStar_Syntax_Syntax.flags = []}))
in (

let uu____2587 = (FStar_Syntax_Syntax.mk_Comp c2)
in (FStar_Syntax_Util.arrow bs1 uu____2587)))
end))
end))
end
| uu____2590 -> begin
(failwith "Impossible (expected_k is an arrow)")
end))
in (

let uu____2591 = (match ((Prims.op_Equality act1.FStar_Syntax_Syntax.action_univs [])) with
| true -> begin
(FStar_TypeChecker_Util.generalize_universes env3 act_defn1)
end
| uu____2602 -> begin
(

let uu____2603 = (FStar_Syntax_Subst.close_univ_vars act1.FStar_Syntax_Syntax.action_univs act_defn1)
in ((act1.FStar_Syntax_Syntax.action_univs), (uu____2603)))
end)
in (match (uu____2591) with
| (univs1, act_defn2) -> begin
(

let act_typ4 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env3 act_typ3)
in (

let act_typ5 = (FStar_Syntax_Subst.close_univ_vars univs1 act_typ4)
in (

let uu___73_2608 = act1
in {FStar_Syntax_Syntax.action_name = uu___73_2608.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___73_2608.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs1; FStar_Syntax_Syntax.action_params = uu___73_2608.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = act_defn2; FStar_Syntax_Syntax.action_typ = act_typ5})))
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
in (match (uu____1538) with
| (repr, bind_repr, return_repr, actions) -> begin
(

let t0 = (

let uu____2638 = (FStar_Syntax_Syntax.mk_Total ed2.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed2.FStar_Syntax_Syntax.binders uu____2638))
in (

let uu____2641 = (

let uu____2650 = (FStar_TypeChecker_Util.generalize_universes env0 t0)
in (match (uu____2650) with
| (gen_univs, t) -> begin
(match (annotated_univ_names) with
| [] -> begin
((gen_univs), (t))
end
| uu____2681 -> begin
(

let uu____2684 = ((Prims.op_Equality (FStar_List.length gen_univs) (FStar_List.length annotated_univ_names)) && (FStar_List.forall2 (fun u1 u2 -> (

let uu____2690 = (FStar_Syntax_Syntax.order_univ_name u1 u2)
in (Prims.op_Equality uu____2690 (Prims.parse_int "0")))) gen_univs annotated_univ_names))
in (match (uu____2684) with
| true -> begin
((gen_univs), (t))
end
| uu____2703 -> begin
(

let uu____2704 = (

let uu____2709 = (

let uu____2710 = (FStar_Util.string_of_int (FStar_List.length annotated_univ_names))
in (

let uu____2711 = (FStar_Util.string_of_int (FStar_List.length gen_univs))
in (FStar_Util.format2 "Expected an effect definition with %s universes; but found %s" uu____2710 uu____2711)))
in ((FStar_Errors.Fatal_UnexpectedNumberOfUniverse), (uu____2709)))
in (FStar_Errors.raise_error uu____2704 ed2.FStar_Syntax_Syntax.signature.FStar_Syntax_Syntax.pos))
end))
end)
end))
in (match (uu____2641) with
| (univs1, t) -> begin
(

let signature1 = (

let uu____2731 = (

let uu____2742 = (

let uu____2743 = (FStar_Syntax_Subst.compress t)
in uu____2743.FStar_Syntax_Syntax.n)
in ((effect_params), (uu____2742)))
in (match (uu____2731) with
| ([], uu____2752) -> begin
t
end
| (uu____2763, FStar_Syntax_Syntax.Tm_arrow (uu____2764, c)) -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____2794 -> begin
(failwith "Impossible : t is an arrow")
end))
in (

let close1 = (fun n1 ts -> (

let ts1 = (

let uu____2823 = (FStar_Syntax_Subst.close_tscheme effect_params ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs1 uu____2823))
in (

let m = (FStar_List.length (FStar_Pervasives_Native.fst ts1))
in ((

let uu____2830 = (((n1 >= (Prims.parse_int "0")) && (

let uu____2838 = (FStar_Syntax_Util.is_unknown (FStar_Pervasives_Native.snd ts1))
in (not (uu____2838)))) && (Prims.op_disEquality m n1))
in (match (uu____2830) with
| true -> begin
(

let error = (match ((m < n1)) with
| true -> begin
"not universe-polymorphic enough"
end
| uu____2862 -> begin
"too universe-polymorphic"
end)
in (

let err_msg = (

let uu____2864 = (FStar_Util.string_of_int m)
in (

let uu____2871 = (FStar_Util.string_of_int n1)
in (

let uu____2878 = (FStar_Syntax_Print.tscheme_to_string ts1)
in (FStar_Util.format4 "The effect combinator is %s (m,n=%s,%s) (%s)" error uu____2864 uu____2871 uu____2878))))
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_MismatchUniversePolymorphic), (err_msg)) (FStar_Pervasives_Native.snd ts1).FStar_Syntax_Syntax.pos)))
end
| uu____2883 -> begin
()
end));
ts1;
))))
in (

let close_action = (fun act -> (

let uu____2890 = (close1 (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_defn)))
in (match (uu____2890) with
| (univs2, defn) -> begin
(

let uu____2905 = (close1 (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_typ)))
in (match (uu____2905) with
| (univs', typ) -> begin
(

let uu___74_2921 = act
in {FStar_Syntax_Syntax.action_name = uu___74_2921.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___74_2921.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs2; FStar_Syntax_Syntax.action_params = uu___74_2921.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = defn; FStar_Syntax_Syntax.action_typ = typ})
end))
end)))
in (

let ed3 = (

let uu___75_2924 = ed2
in (

let uu____2925 = (close1 (Prims.parse_int "0") return_wp)
in (

let uu____2926 = (close1 (Prims.parse_int "1") bind_wp)
in (

let uu____2927 = (close1 (Prims.parse_int "0") if_then_else1)
in (

let uu____2928 = (close1 (Prims.parse_int "0") ite_wp)
in (

let uu____2929 = (close1 (Prims.parse_int "0") stronger)
in (

let uu____2930 = (close1 (Prims.parse_int "1") close_wp)
in (

let uu____2931 = (close1 (Prims.parse_int "0") assert_p)
in (

let uu____2932 = (close1 (Prims.parse_int "0") assume_p)
in (

let uu____2933 = (close1 (Prims.parse_int "0") null_wp)
in (

let uu____2934 = (close1 (Prims.parse_int "0") trivial_wp)
in (

let uu____2935 = (

let uu____2936 = (close1 (Prims.parse_int "0") (([]), (repr)))
in (FStar_Pervasives_Native.snd uu____2936))
in (

let uu____2953 = (close1 (Prims.parse_int "0") return_repr)
in (

let uu____2954 = (close1 (Prims.parse_int "1") bind_repr)
in (

let uu____2955 = (FStar_List.map close_action actions)
in {FStar_Syntax_Syntax.cattributes = uu___75_2924.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___75_2924.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs1; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature1; FStar_Syntax_Syntax.ret_wp = uu____2925; FStar_Syntax_Syntax.bind_wp = uu____2926; FStar_Syntax_Syntax.if_then_else = uu____2927; FStar_Syntax_Syntax.ite_wp = uu____2928; FStar_Syntax_Syntax.stronger = uu____2929; FStar_Syntax_Syntax.close_wp = uu____2930; FStar_Syntax_Syntax.assert_p = uu____2931; FStar_Syntax_Syntax.assume_p = uu____2932; FStar_Syntax_Syntax.null_wp = uu____2933; FStar_Syntax_Syntax.trivial = uu____2934; FStar_Syntax_Syntax.repr = uu____2935; FStar_Syntax_Syntax.return_repr = uu____2953; FStar_Syntax_Syntax.bind_repr = uu____2954; FStar_Syntax_Syntax.actions = uu____2955; FStar_Syntax_Syntax.eff_attrs = uu___75_2924.FStar_Syntax_Syntax.eff_attrs})))))))))))))))
in ((

let uu____2959 = ((FStar_TypeChecker_Env.debug env2 FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("ED"))))
in (match (uu____2959) with
| true -> begin
(

let uu____2960 = (FStar_Syntax_Print.eff_decl_to_string false ed3)
in (FStar_Util.print_string uu____2960))
end
| uu____2961 -> begin
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

let uu____2982 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____2982) with
| (effect_binders_un, signature_un) -> begin
(

let uu____2999 = (FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un)
in (match (uu____2999) with
| (effect_binders, env1, uu____3018) -> begin
(

let uu____3019 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un)
in (match (uu____3019) with
| (signature, uu____3035) -> begin
(

let raise_error1 = (fun uu____3050 -> (match (uu____3050) with
| (e, err_msg) -> begin
(FStar_Errors.raise_error ((e), (err_msg)) signature.FStar_Syntax_Syntax.pos)
end))
in (

let effect_binders1 = (FStar_List.map (fun uu____3076 -> (match (uu____3076) with
| (bv, qual) -> begin
(

let uu____3087 = (

let uu___76_3088 = bv
in (

let uu____3089 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env1 bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___76_3088.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___76_3088.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3089}))
in ((uu____3087), (qual)))
end)) effect_binders)
in (

let uu____3092 = (

let uu____3099 = (

let uu____3100 = (FStar_Syntax_Subst.compress signature_un)
in uu____3100.FStar_Syntax_Syntax.n)
in (match (uu____3099) with
| FStar_Syntax_Syntax.Tm_arrow (((a, uu____3110))::[], effect_marker) -> begin
((a), (effect_marker))
end
| uu____3132 -> begin
(raise_error1 ((FStar_Errors.Fatal_BadSignatureShape), ("bad shape for effect-for-free signature")))
end))
in (match (uu____3092) with
| (a, effect_marker) -> begin
(

let a1 = (

let uu____3156 = (FStar_Syntax_Syntax.is_null_bv a)
in (match (uu____3156) with
| true -> begin
(

let uu____3157 = (

let uu____3160 = (FStar_Syntax_Syntax.range_of_bv a)
in FStar_Pervasives_Native.Some (uu____3160))
in (FStar_Syntax_Syntax.gen_bv "a" uu____3157 a.FStar_Syntax_Syntax.sort))
end
| uu____3161 -> begin
a
end))
in (

let open_and_check = (fun env2 other_binders t -> (

let subst1 = (FStar_Syntax_Subst.opening_of_binders (FStar_List.append effect_binders1 other_binders))
in (

let t1 = (FStar_Syntax_Subst.subst subst1 t)
in (

let uu____3200 = (FStar_TypeChecker_TcTerm.tc_term env2 t1)
in (match (uu____3200) with
| (t2, comp, uu____3213) -> begin
((t2), (comp))
end)))))
in (

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None signature.FStar_Syntax_Syntax.pos))
in (

let uu____3222 = (open_and_check env1 [] ed.FStar_Syntax_Syntax.repr)
in (match (uu____3222) with
| (repr, _comp) -> begin
((

let uu____3244 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____3244) with
| true -> begin
(

let uu____3245 = (FStar_Syntax_Print.term_to_string repr)
in (FStar_Util.print1 "Representation is: %s\n" uu____3245))
end
| uu____3246 -> begin
()
end));
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env1 (FStar_TypeChecker_TcTerm.tc_constant env1 FStar_Range.dummyRange))
in (

let wp_type = (FStar_TypeChecker_DMFF.star_type dmff_env repr)
in (

let uu____3249 = (recheck_debug "*" env1 wp_type)
in (

let wp_a = (

let uu____3251 = (

let uu____3252 = (

let uu____3253 = (

let uu____3268 = (

let uu____3277 = (

let uu____3282 = (FStar_Syntax_Syntax.bv_to_name a1)
in (

let uu____3283 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____3282), (uu____3283))))
in (uu____3277)::[])
in ((wp_type), (uu____3268)))
in FStar_Syntax_Syntax.Tm_app (uu____3253))
in (mk1 uu____3252))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env1 uu____3251))
in (

let effect_signature = (

let binders = (

let uu____3312 = (

let uu____3317 = (FStar_Syntax_Syntax.as_implicit false)
in ((a1), (uu____3317)))
in (

let uu____3318 = (

let uu____3325 = (

let uu____3330 = (FStar_Syntax_Syntax.gen_bv "dijkstra_wp" FStar_Pervasives_Native.None wp_a)
in (FStar_All.pipe_right uu____3330 FStar_Syntax_Syntax.mk_binder))
in (uu____3325)::[])
in (uu____3312)::uu____3318))
in (

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in (mk1 (FStar_Syntax_Syntax.Tm_arrow (((binders1), (effect_marker)))))))
in (

let uu____3356 = (recheck_debug "turned into the effect signature" env1 effect_signature)
in (

let sigelts = (FStar_Util.mk_ref [])
in (

let mk_lid = (fun name -> (FStar_Syntax_Util.dm4f_lid ed name))
in (

let elaborate_and_star = (fun dmff_env1 other_binders item -> (

let env2 = (FStar_TypeChecker_DMFF.get_env dmff_env1)
in (

let uu____3419 = item
in (match (uu____3419) with
| (u_item, item1) -> begin
(

let uu____3440 = (open_and_check env2 other_binders item1)
in (match (uu____3440) with
| (item2, item_comp) -> begin
((

let uu____3456 = (

let uu____3457 = (FStar_Syntax_Util.is_total_lcomp item_comp)
in (not (uu____3457)))
in (match (uu____3456) with
| true -> begin
(

let uu____3458 = (

let uu____3463 = (

let uu____3464 = (FStar_Syntax_Print.term_to_string item2)
in (

let uu____3465 = (FStar_Syntax_Print.lcomp_to_string item_comp)
in (FStar_Util.format2 "Computation for [%s] is not total : %s !" uu____3464 uu____3465)))
in ((FStar_Errors.Fatal_ComputationNotTotal), (uu____3463)))
in (FStar_Errors.raise_err uu____3458))
end
| uu____3466 -> begin
()
end));
(

let uu____3467 = (FStar_TypeChecker_DMFF.star_expr dmff_env1 item2)
in (match (uu____3467) with
| (item_t, item_wp, item_elab) -> begin
(

let uu____3485 = (recheck_debug "*" env2 item_wp)
in (

let uu____3486 = (recheck_debug "_" env2 item_elab)
in ((dmff_env1), (item_t), (item_wp), (item_elab))))
end));
)
end))
end))))
in (

let uu____3487 = (elaborate_and_star dmff_env [] ed.FStar_Syntax_Syntax.bind_repr)
in (match (uu____3487) with
| (dmff_env1, uu____3511, bind_wp, bind_elab) -> begin
(

let uu____3514 = (elaborate_and_star dmff_env1 [] ed.FStar_Syntax_Syntax.return_repr)
in (match (uu____3514) with
| (dmff_env2, uu____3538, return_wp, return_elab) -> begin
(

let rc_gtot = {FStar_Syntax_Syntax.residual_effect = FStar_Parser_Const.effect_GTot_lid; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.None; FStar_Syntax_Syntax.residual_flags = []}
in (

let lift_from_pure_wp = (

let uu____3547 = (

let uu____3548 = (FStar_Syntax_Subst.compress return_wp)
in uu____3548.FStar_Syntax_Syntax.n)
in (match (uu____3547) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(

let uu____3594 = (

let uu____3609 = (

let uu____3614 = (FStar_Syntax_Util.abs bs body FStar_Pervasives_Native.None)
in (FStar_Syntax_Subst.open_term ((b1)::(b2)::[]) uu____3614))
in (match (uu____3609) with
| ((b11)::(b21)::[], body1) -> begin
((b11), (b21), (body1))
end
| uu____3672 -> begin
(failwith "Impossible : open_term not preserving binders arity")
end))
in (match (uu____3594) with
| (b11, b21, body1) -> begin
(

let env0 = (

let uu____3713 = (FStar_TypeChecker_DMFF.get_env dmff_env2)
in (FStar_TypeChecker_Env.push_binders uu____3713 ((b11)::(b21)::[])))
in (

let wp_b1 = (

let raw_wp_b1 = (

let uu____3730 = (

let uu____3731 = (

let uu____3746 = (

let uu____3755 = (

let uu____3760 = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst b11))
in (

let uu____3761 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____3760), (uu____3761))))
in (uu____3755)::[])
in ((wp_type), (uu____3746)))
in FStar_Syntax_Syntax.Tm_app (uu____3731))
in (mk1 uu____3730))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env0 raw_wp_b1))
in (

let uu____3780 = (

let uu____3789 = (

let uu____3790 = (FStar_Syntax_Util.unascribe wp_b1)
in (FStar_TypeChecker_Normalize.eta_expand_with_type env0 body1 uu____3790))
in (FStar_All.pipe_left FStar_Syntax_Util.abs_formals uu____3789))
in (match (uu____3780) with
| (bs1, body2, what') -> begin
(

let fail1 = (fun uu____3813 -> (

let error_msg = (

let uu____3815 = (FStar_Syntax_Print.term_to_string body2)
in (

let uu____3816 = (match (what') with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (rc) -> begin
(FStar_Ident.text_of_lid rc.FStar_Syntax_Syntax.residual_effect)
end)
in (FStar_Util.format2 "The body of return_wp (%s) should be of type Type0 but is of type %s" uu____3815 uu____3816)))
in (raise_error1 ((FStar_Errors.Fatal_WrongBodyTypeForReturnWP), (error_msg)))))
in ((match (what') with
| FStar_Pervasives_Native.None -> begin
(fail1 ())
end
| FStar_Pervasives_Native.Some (rc) -> begin
((

let uu____3821 = (

let uu____3822 = (FStar_Syntax_Util.is_pure_effect rc.FStar_Syntax_Syntax.residual_effect)
in (not (uu____3822)))
in (match (uu____3821) with
| true -> begin
(fail1 ())
end
| uu____3823 -> begin
()
end));
(

let uu____3824 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun rt -> (

let g_opt = (FStar_TypeChecker_Rel.try_teq true env1 rt FStar_Syntax_Util.ktype0)
in (match (g_opt) with
| FStar_Pervasives_Native.Some (g') -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env1 g')
end
| FStar_Pervasives_Native.None -> begin
(fail1 ())
end))))
in (FStar_All.pipe_right uu____3824 (fun a238 -> ())));
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

let uu____3849 = (

let uu____3854 = (FStar_Syntax_Syntax.bv_to_name wp)
in (

let uu____3855 = (

let uu____3856 = (

let uu____3863 = (FStar_Syntax_Util.abs ((b21)::[]) body2 what')
in ((uu____3863), (FStar_Pervasives_Native.None)))
in (uu____3856)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____3854 uu____3855)))
in (uu____3849 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let uu____3892 = (

let uu____3893 = (

let uu____3900 = (FStar_Syntax_Syntax.mk_binder wp)
in (uu____3900)::[])
in (b11)::uu____3893)
in (

let uu____3917 = (FStar_Syntax_Util.abs bs1 body3 what)
in (FStar_Syntax_Util.abs uu____3892 uu____3917 (FStar_Pervasives_Native.Some (rc_gtot)))))));
))
end))))
end))
end
| uu____3920 -> begin
(raise_error1 ((FStar_Errors.Fatal_UnexpectedReturnShape), ("unexpected shape for return")))
end))
in (

let return_wp1 = (

let uu____3926 = (

let uu____3927 = (FStar_Syntax_Subst.compress return_wp)
in uu____3927.FStar_Syntax_Syntax.n)
in (match (uu____3926) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(

let uu____3973 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs ((b1)::(b2)::[]) uu____3973 (FStar_Pervasives_Native.Some (rc_gtot))))
end
| uu____3988 -> begin
(raise_error1 ((FStar_Errors.Fatal_UnexpectedReturnShape), ("unexpected shape for return")))
end))
in (

let bind_wp1 = (

let uu____3994 = (

let uu____3995 = (FStar_Syntax_Subst.compress bind_wp)
in uu____3995.FStar_Syntax_Syntax.n)
in (match (uu____3994) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let r = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.range_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let uu____4024 = (

let uu____4025 = (

let uu____4032 = (

let uu____4037 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (r)))
in (FStar_Syntax_Syntax.null_binder uu____4037))
in (uu____4032)::[])
in (FStar_List.append uu____4025 binders))
in (FStar_Syntax_Util.abs uu____4024 body what)))
end
| uu____4050 -> begin
(raise_error1 ((FStar_Errors.Fatal_UnexpectedBindShape), ("unexpected shape for bind")))
end))
in (

let apply_close = (fun t -> (match ((Prims.op_Equality (FStar_List.length effect_binders1) (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____4067 -> begin
(

let uu____4068 = (

let uu____4069 = (

let uu____4070 = (

let uu____4085 = (

let uu____4094 = (FStar_Syntax_Util.args_of_binders effect_binders1)
in (FStar_Pervasives_Native.snd uu____4094))
in ((t), (uu____4085)))
in FStar_Syntax_Syntax.Tm_app (uu____4070))
in (mk1 uu____4069))
in (FStar_Syntax_Subst.close effect_binders1 uu____4068))
end))
in (

let rec apply_last1 = (fun f l -> (match (l) with
| [] -> begin
(failwith "empty path..")
end
| (a2)::[] -> begin
(

let uu____4136 = (f a2)
in (uu____4136)::[])
end
| (x)::xs -> begin
(

let uu____4141 = (apply_last1 f xs)
in (x)::uu____4141)
end))
in (

let register = (fun name item -> (

let p = (FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname)
in (

let p' = (apply_last1 (fun s -> (Prims.strcat "__" (Prims.strcat s (Prims.strcat "_eff_override_" name)))) p)
in (

let l' = (FStar_Ident.lid_of_path p' FStar_Range.dummyRange)
in (

let uu____4167 = (FStar_TypeChecker_Env.try_lookup_lid env1 l')
in (match (uu____4167) with
| FStar_Pervasives_Native.Some (_us, _t) -> begin
((

let uu____4197 = (FStar_Options.debug_any ())
in (match (uu____4197) with
| true -> begin
(

let uu____4198 = (FStar_Ident.string_of_lid l')
in (FStar_Util.print1 "DM4F: Applying override %s\n" uu____4198))
end
| uu____4199 -> begin
()
end));
(

let uu____4200 = (FStar_Syntax_Syntax.lid_as_fv l' FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____4200));
)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4209 = (

let uu____4214 = (mk_lid name)
in (

let uu____4215 = (FStar_Syntax_Util.abs effect_binders1 item FStar_Pervasives_Native.None)
in (FStar_TypeChecker_Util.mk_toplevel_definition env1 uu____4214 uu____4215)))
in (match (uu____4209) with
| (sigelt, fv) -> begin
((

let uu____4219 = (

let uu____4222 = (FStar_ST.op_Bang sigelts)
in (sigelt)::uu____4222)
in (FStar_ST.op_Colon_Equals sigelts uu____4219));
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

let uu____4327 = (

let uu____4330 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true"))))
in (

let uu____4331 = (FStar_ST.op_Bang sigelts)
in (uu____4330)::uu____4331))
in (FStar_ST.op_Colon_Equals sigelts uu____4327));
(

let return_elab1 = (register "return_elab" return_elab)
in ((FStar_Options.pop ());
(

let bind_wp2 = (register "bind_wp" bind_wp1)
in ((FStar_Options.push ());
(

let uu____4437 = (

let uu____4440 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true"))))
in (

let uu____4441 = (FStar_ST.op_Bang sigelts)
in (uu____4440)::uu____4441))
in (FStar_ST.op_Colon_Equals sigelts uu____4437));
(

let bind_elab1 = (register "bind_elab" bind_elab)
in ((FStar_Options.pop ());
(

let uu____4544 = (FStar_List.fold_left (fun uu____4584 action -> (match (uu____4584) with
| (dmff_env3, actions) -> begin
(

let params_un = (FStar_Syntax_Subst.open_binders action.FStar_Syntax_Syntax.action_params)
in (

let uu____4605 = (

let uu____4612 = (FStar_TypeChecker_DMFF.get_env dmff_env3)
in (FStar_TypeChecker_TcTerm.tc_tparams uu____4612 params_un))
in (match (uu____4605) with
| (action_params, env', uu____4621) -> begin
(

let action_params1 = (FStar_List.map (fun uu____4641 -> (match (uu____4641) with
| (bv, qual) -> begin
(

let uu____4652 = (

let uu___77_4653 = bv
in (

let uu____4654 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env' bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___77_4653.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___77_4653.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____4654}))
in ((uu____4652), (qual)))
end)) action_params)
in (

let dmff_env' = (FStar_TypeChecker_DMFF.set_env dmff_env3 env')
in (

let uu____4658 = (elaborate_and_star dmff_env' action_params1 ((action.FStar_Syntax_Syntax.action_univs), (action.FStar_Syntax_Syntax.action_defn)))
in (match (uu____4658) with
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
| uu____4692 -> begin
(

let uu____4693 = (FStar_Syntax_Syntax.mk_Total action_typ_with_wp1)
in (FStar_Syntax_Util.flat_arrow action_params2 uu____4693))
end)
in ((

let uu____4697 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("ED")))
in (match (uu____4697) with
| true -> begin
(

let uu____4698 = (FStar_Syntax_Print.binders_to_string "," params_un)
in (

let uu____4699 = (FStar_Syntax_Print.binders_to_string "," action_params2)
in (

let uu____4700 = (FStar_Syntax_Print.term_to_string action_typ_with_wp2)
in (

let uu____4701 = (FStar_Syntax_Print.term_to_string action_elab2)
in (FStar_Util.print4 "original action_params %s, end action_params %s, type %s, term %s\n" uu____4698 uu____4699 uu____4700 uu____4701)))))
end
| uu____4702 -> begin
()
end));
(

let action_elab3 = (register (Prims.strcat name "_elab") action_elab2)
in (

let action_typ_with_wp3 = (register (Prims.strcat name "_complete_type") action_typ_with_wp2)
in (

let uu____4705 = (

let uu____4708 = (

let uu___78_4709 = action
in (

let uu____4710 = (apply_close action_elab3)
in (

let uu____4711 = (apply_close action_typ_with_wp3)
in {FStar_Syntax_Syntax.action_name = uu___78_4709.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___78_4709.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___78_4709.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = []; FStar_Syntax_Syntax.action_defn = uu____4710; FStar_Syntax_Syntax.action_typ = uu____4711})))
in (uu____4708)::actions)
in ((dmff_env4), (uu____4705)))));
))))))))
end))))
end)))
end)) ((dmff_env2), ([])) ed.FStar_Syntax_Syntax.actions)
in (match (uu____4544) with
| (dmff_env3, actions) -> begin
(

let actions1 = (FStar_List.rev actions)
in (

let repr1 = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp_a" FStar_Pervasives_Native.None wp_a)
in (

let binders = (

let uu____4750 = (FStar_Syntax_Syntax.mk_binder a1)
in (

let uu____4755 = (

let uu____4762 = (FStar_Syntax_Syntax.mk_binder wp)
in (uu____4762)::[])
in (uu____4750)::uu____4755))
in (

let uu____4779 = (

let uu____4782 = (

let uu____4783 = (

let uu____4784 = (

let uu____4799 = (

let uu____4808 = (

let uu____4813 = (FStar_Syntax_Syntax.bv_to_name a1)
in (

let uu____4814 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____4813), (uu____4814))))
in (uu____4808)::[])
in ((repr), (uu____4799)))
in FStar_Syntax_Syntax.Tm_app (uu____4784))
in (mk1 uu____4783))
in (

let uu____4833 = (FStar_Syntax_Syntax.bv_to_name wp)
in (FStar_TypeChecker_DMFF.trans_F dmff_env3 uu____4782 uu____4833)))
in (FStar_Syntax_Util.abs binders uu____4779 FStar_Pervasives_Native.None))))
in (

let uu____4834 = (recheck_debug "FC" env1 repr1)
in (

let repr2 = (register "repr" repr1)
in (

let uu____4836 = (

let uu____4845 = (

let uu____4846 = (

let uu____4849 = (FStar_Syntax_Subst.compress wp_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____4849))
in uu____4846.FStar_Syntax_Syntax.n)
in (match (uu____4845) with
| FStar_Syntax_Syntax.Tm_abs ((type_param)::effect_param, arrow1, uu____4863) -> begin
(

let uu____4892 = (

let uu____4909 = (FStar_Syntax_Subst.open_term ((type_param)::effect_param) arrow1)
in (match (uu____4909) with
| ((b)::bs, body) -> begin
((b), (bs), (body))
end
| uu____4961 -> begin
(failwith "Impossible : open_term nt preserving binders arity")
end))
in (match (uu____4892) with
| (type_param1, effect_param1, arrow2) -> begin
(

let uu____5013 = (

let uu____5014 = (

let uu____5017 = (FStar_Syntax_Subst.compress arrow2)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____5017))
in uu____5014.FStar_Syntax_Syntax.n)
in (match (uu____5013) with
| FStar_Syntax_Syntax.Tm_arrow (wp_binders, c) -> begin
(

let uu____5046 = (FStar_Syntax_Subst.open_comp wp_binders c)
in (match (uu____5046) with
| (wp_binders1, c1) -> begin
(

let uu____5061 = (FStar_List.partition (fun uu____5086 -> (match (uu____5086) with
| (bv, uu____5092) -> begin
(

let uu____5093 = (

let uu____5094 = (FStar_Syntax_Free.names bv.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____5094 (FStar_Util.set_mem (FStar_Pervasives_Native.fst type_param1))))
in (FStar_All.pipe_right uu____5093 Prims.op_Negation))
end)) wp_binders1)
in (match (uu____5061) with
| (pre_args, post_args) -> begin
(

let post = (match (post_args) with
| (post)::[] -> begin
post
end
| [] -> begin
(

let err_msg = (

let uu____5160 = (FStar_Syntax_Print.term_to_string arrow2)
in (FStar_Util.format1 "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)" uu____5160))
in (FStar_Errors.raise_err ((FStar_Errors.Fatal_ImpossibleToGenerateDMEffect), (err_msg))))
end
| uu____5165 -> begin
(

let err_msg = (

let uu____5173 = (FStar_Syntax_Print.term_to_string arrow2)
in (FStar_Util.format1 "Impossible to generate DM effect: multiple post candidates %s" uu____5173))
in (FStar_Errors.raise_err ((FStar_Errors.Fatal_ImpossibleToGenerateDMEffect), (err_msg))))
end)
in (

let uu____5178 = (FStar_Syntax_Util.arrow pre_args c1)
in (

let uu____5181 = (FStar_Syntax_Util.abs ((type_param1)::effect_param1) (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort FStar_Pervasives_Native.None)
in ((uu____5178), (uu____5181)))))
end))
end))
end
| uu____5192 -> begin
(

let uu____5193 = (

let uu____5198 = (

let uu____5199 = (FStar_Syntax_Print.term_to_string arrow2)
in (FStar_Util.format1 "Impossible: pre/post arrow %s" uu____5199))
in ((FStar_Errors.Fatal_ImpossiblePrePostArrow), (uu____5198)))
in (raise_error1 uu____5193))
end))
end))
end
| uu____5208 -> begin
(

let uu____5209 = (

let uu____5214 = (

let uu____5215 = (FStar_Syntax_Print.term_to_string wp_type)
in (FStar_Util.format1 "Impossible: pre/post abs %s" uu____5215))
in ((FStar_Errors.Fatal_ImpossiblePrePostAbs), (uu____5214)))
in (raise_error1 uu____5209))
end))
in (match (uu____4836) with
| (pre, post) -> begin
((

let uu____5245 = (register "pre" pre)
in ());
(

let uu____5247 = (register "post" post)
in ());
(

let uu____5249 = (register "wp" wp_type)
in ());
(

let ed1 = (

let uu___79_5251 = ed
in (

let uu____5252 = (FStar_Syntax_Subst.close_binders effect_binders1)
in (

let uu____5253 = (FStar_Syntax_Subst.close effect_binders1 effect_signature)
in (

let uu____5254 = (

let uu____5255 = (apply_close return_wp2)
in (([]), (uu____5255)))
in (

let uu____5262 = (

let uu____5263 = (apply_close bind_wp2)
in (([]), (uu____5263)))
in (

let uu____5270 = (apply_close repr2)
in (

let uu____5271 = (

let uu____5272 = (apply_close return_elab1)
in (([]), (uu____5272)))
in (

let uu____5279 = (

let uu____5280 = (apply_close bind_elab1)
in (([]), (uu____5280)))
in {FStar_Syntax_Syntax.cattributes = uu___79_5251.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___79_5251.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___79_5251.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu____5252; FStar_Syntax_Syntax.signature = uu____5253; FStar_Syntax_Syntax.ret_wp = uu____5254; FStar_Syntax_Syntax.bind_wp = uu____5262; FStar_Syntax_Syntax.if_then_else = uu___79_5251.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = uu___79_5251.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = uu___79_5251.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = uu___79_5251.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = uu___79_5251.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = uu___79_5251.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = uu___79_5251.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = uu___79_5251.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = uu____5270; FStar_Syntax_Syntax.return_repr = uu____5271; FStar_Syntax_Syntax.bind_repr = uu____5279; FStar_Syntax_Syntax.actions = actions1; FStar_Syntax_Syntax.eff_attrs = uu___79_5251.FStar_Syntax_Syntax.eff_attrs}))))))))
in (

let uu____5287 = (FStar_TypeChecker_DMFF.gen_wps_for_free env1 effect_binders1 a1 wp_a ed1)
in (match (uu____5287) with
| (sigelts', ed2) -> begin
((

let uu____5305 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____5305) with
| true -> begin
(

let uu____5306 = (FStar_Syntax_Print.eff_decl_to_string true ed2)
in (FStar_Util.print_string uu____5306))
end
| uu____5307 -> begin
()
end));
(

let lift_from_pure_opt = (match ((Prims.op_Equality (FStar_List.length effect_binders1) (Prims.parse_int "0"))) with
| true -> begin
(

let lift_from_pure = (

let uu____5318 = (

let uu____5321 = (

let uu____5322 = (apply_close lift_from_pure_wp1)
in (([]), (uu____5322)))
in FStar_Pervasives_Native.Some (uu____5321))
in {FStar_Syntax_Syntax.source = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.target = ed2.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.lift_wp = uu____5318; FStar_Syntax_Syntax.lift = FStar_Pervasives_Native.None})
in (

let uu____5325 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_sub_effect (lift_from_pure)))
in FStar_Pervasives_Native.Some (uu____5325)))
end
| uu____5326 -> begin
FStar_Pervasives_Native.None
end)
in (

let uu____5327 = (

let uu____5330 = (

let uu____5333 = (FStar_ST.op_Bang sigelts)
in (FStar_List.rev uu____5333))
in (FStar_List.append uu____5330 sigelts'))
in ((uu____5327), (ed2), (lift_from_pure_opt))));
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


let tc_lex_t : 'Auu____5399 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  'Auu____5399 Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (

let err_range = (

let uu____5434 = (FStar_List.hd ses)
in uu____5434.FStar_Syntax_Syntax.sigrng)
in ((match (lids) with
| (lex_t1)::(lex_top1)::(lex_cons)::[] when (((FStar_Ident.lid_equals lex_t1 FStar_Parser_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top1 FStar_Parser_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Parser_Const.lexcons_lid)) -> begin
()
end
| uu____5439 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_InvalidRedefinitionOfLexT), ("Invalid (partial) redefinition of lex_t")) err_range)
end);
(match (ses) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (lex_t1, uu____5443, [], t, uu____5445, uu____5446); FStar_Syntax_Syntax.sigrng = r; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = uu____5448; FStar_Syntax_Syntax.sigattrs = uu____5449})::({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (lex_top1, uu____5451, _t_top, _lex_t_top, _0_17, uu____5454); FStar_Syntax_Syntax.sigrng = r1; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = uu____5456; FStar_Syntax_Syntax.sigattrs = uu____5457})::({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (lex_cons, uu____5459, _t_cons, _lex_t_cons, _0_18, uu____5462); FStar_Syntax_Syntax.sigrng = r2; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = uu____5464; FStar_Syntax_Syntax.sigattrs = uu____5465})::[] when (((_0_17 = (Prims.parse_int "0")) && (_0_18 = (Prims.parse_int "0"))) && (((FStar_Ident.lid_equals lex_t1 FStar_Parser_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top1 FStar_Parser_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Parser_Const.lexcons_lid))) -> begin
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

let uu____5510 = (

let uu____5517 = (

let uu____5518 = (

let uu____5525 = (

let uu____5528 = (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar uu____5528 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))
in ((uu____5525), ((FStar_Syntax_Syntax.U_name (utop))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____5518))
in (FStar_Syntax_Syntax.mk uu____5517))
in (uu____5510 FStar_Pervasives_Native.None r1))
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

let uu____5544 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) FStar_Pervasives_Native.None r2)
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (r2)) uu____5544))
in (

let hd1 = (

let uu____5546 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (r2)) uu____5546))
in (

let tl1 = (

let uu____5548 = (

let uu____5549 = (

let uu____5556 = (

let uu____5557 = (

let uu____5564 = (

let uu____5567 = (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar uu____5567 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))
in ((uu____5564), ((FStar_Syntax_Syntax.U_name (ucons2))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____5557))
in (FStar_Syntax_Syntax.mk uu____5556))
in (uu____5549 FStar_Pervasives_Native.None r2))
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (r2)) uu____5548))
in (

let res = (

let uu____5576 = (

let uu____5583 = (

let uu____5584 = (

let uu____5591 = (

let uu____5594 = (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar uu____5594 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))
in ((uu____5591), ((FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____5584))
in (FStar_Syntax_Syntax.mk uu____5583))
in (uu____5576 FStar_Pervasives_Native.None r2))
in (

let uu____5600 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow ((((a), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::(((hd1), (FStar_Pervasives_Native.None)))::(((tl1), (FStar_Pervasives_Native.None)))::[]) uu____5600))))))
in (

let lex_cons_t1 = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((lex_cons), ((ucons1)::(ucons2)::[]), (lex_cons_t1), (FStar_Parser_Const.lex_t_lid), ((Prims.parse_int "0")), ([]))); FStar_Syntax_Syntax.sigrng = r2; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (

let uu____5629 = (FStar_TypeChecker_Env.get_range env)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle ((((tc)::(dc_lextop)::(dc_lexcons)::[]), (lids))); FStar_Syntax_Syntax.sigrng = uu____5629; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))))))))))))))
end
| uu____5634 -> begin
(

let err_msg = (

let uu____5638 = (

let uu____5639 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_bundle (((ses), (lids)))))
in (FStar_Syntax_Print.sigelt_to_string uu____5639))
in (FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n" uu____5638))
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_InvalidRedefinitionOfLexT), (err_msg)) err_range))
end);
)))


let tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun env phi r -> (

let env1 = (FStar_TypeChecker_Env.set_range env r)
in (

let uu____5660 = (FStar_Syntax_Util.type_u ())
in (match (uu____5660) with
| (k, uu____5666) -> begin
(

let phi1 = (

let uu____5668 = (tc_check_trivial_guard env1 phi k)
in (FStar_All.pipe_right uu____5668 (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env1)))
in ((FStar_TypeChecker_Util.check_uvars r phi1);
phi1;
))
end))))


let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env ses quals lids -> (

let env1 = (FStar_TypeChecker_Env.push env "tc_inductive")
in (

let uu____5709 = (FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1 ses quals lids)
in (match (uu____5709) with
| (sig_bndle, tcs, datas) -> begin
(

let data_ops_ses = (

let uu____5740 = (FStar_List.map (FStar_TypeChecker_TcInductive.mk_data_operations quals env1 tcs) datas)
in (FStar_All.pipe_right uu____5740 FStar_List.flatten))
in ((

let uu____5754 = ((FStar_Options.no_positivity ()) || (

let uu____5756 = (FStar_TypeChecker_Env.should_verify env1)
in (not (uu____5756))))
in (match (uu____5754) with
| true -> begin
()
end
| uu____5757 -> begin
(

let env2 = (FStar_TypeChecker_Env.push_sigelt env1 sig_bndle)
in (FStar_List.iter (fun ty -> (

let b = (FStar_TypeChecker_TcInductive.check_positivity ty env2)
in (match ((not (b))) with
| true -> begin
(

let uu____5767 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____5777, uu____5778, uu____5779, uu____5780, uu____5781) -> begin
((lid), (ty.FStar_Syntax_Syntax.sigrng))
end
| uu____5790 -> begin
(failwith "Impossible!")
end)
in (match (uu____5767) with
| (lid, r) -> begin
(FStar_Errors.log_issue r ((FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition), ((Prims.strcat "Inductive type " (Prims.strcat lid.FStar_Ident.str " does not satisfy the positivity condition")))))
end))
end
| uu____5797 -> begin
()
end))) tcs))
end));
(

let skip_prims_type = (fun uu____5803 -> (

let lid = (

let ty = (FStar_List.hd tcs)
in (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____5807, uu____5808, uu____5809, uu____5810, uu____5811) -> begin
lid
end
| uu____5820 -> begin
(failwith "Impossible")
end))
in (FStar_List.existsb (fun s -> (Prims.op_Equality s lid.FStar_Ident.ident.FStar_Ident.idText)) FStar_TypeChecker_TcInductive.early_prims_inductives)))
in (

let is_noeq = (FStar_List.existsb (fun q -> (Prims.op_Equality q FStar_Syntax_Syntax.Noeq)) quals)
in (

let res = (

let uu____5833 = (((Prims.op_Equality (FStar_List.length tcs) (Prims.parse_int "0")) || ((FStar_Ident.lid_equals env1.FStar_TypeChecker_Env.curmodule FStar_Parser_Const.prims_lid) && (skip_prims_type ()))) || is_noeq)
in (match (uu____5833) with
| true -> begin
((sig_bndle), (data_ops_ses))
end
| uu____5842 -> begin
(

let is_unopteq = (FStar_List.existsb (fun q -> (Prims.op_Equality q FStar_Syntax_Syntax.Unopteq)) quals)
in (

let ses1 = (match (is_unopteq) with
| true -> begin
(FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme sig_bndle tcs datas env1)
end
| uu____5851 -> begin
(FStar_TypeChecker_TcInductive.optimized_haseq_scheme sig_bndle tcs datas env1)
end)
in ((sig_bndle), ((FStar_List.append ses1 data_ops_ses)))))
end))
in ((

let uu____5855 = (FStar_TypeChecker_Env.pop env1 "tc_inductive")
in ());
res;
))));
))
end))))


let z3_reset_options : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun en -> (

let env = (

let uu____5862 = (FStar_Options.using_facts_from ())
in (FStar_TypeChecker_Env.set_proof_ns uu____5862 en))
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
env;
)))


let tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env se -> (

let env1 = (set_hint_correlator env se)
in ((FStar_TypeChecker_Util.check_sigelt_quals env1 se);
(

let r = se.FStar_Syntax_Syntax.sigrng
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____5901) -> begin
(failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____5926) -> begin
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

let ses1 = (

let uu____5981 = ((FStar_Options.use_two_phase_tc ()) && (FStar_TypeChecker_Env.should_verify env2))
in (match (uu____5981) with
| true -> begin
(

let ses1 = (

let uu____5987 = (

let uu____5988 = (

let uu____5989 = (tc_inductive (

let uu___80_5998 = env2
in {FStar_TypeChecker_Env.solver = uu___80_5998.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___80_5998.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___80_5998.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___80_5998.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___80_5998.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___80_5998.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___80_5998.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___80_5998.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___80_5998.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___80_5998.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___80_5998.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___80_5998.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___80_5998.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___80_5998.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___80_5998.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___80_5998.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___80_5998.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___80_5998.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___80_5998.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___80_5998.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___80_5998.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___80_5998.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___80_5998.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___80_5998.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___80_5998.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___80_5998.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___80_5998.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___80_5998.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___80_5998.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___80_5998.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___80_5998.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___80_5998.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___80_5998.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___80_5998.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___80_5998.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___80_5998.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___80_5998.FStar_TypeChecker_Env.dep_graph}) ses se.FStar_Syntax_Syntax.sigquals lids)
in (FStar_All.pipe_right uu____5989 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____5988 (FStar_TypeChecker_Normalize.elim_uvars env2)))
in (FStar_All.pipe_right uu____5987 FStar_Syntax_Util.ses_of_sigbundle))
in ((

let uu____6010 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("TwoPhases")))
in (match (uu____6010) with
| true -> begin
(

let uu____6011 = (FStar_Syntax_Print.sigelt_to_string (

let uu___81_6014 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (((ses1), (lids))); FStar_Syntax_Syntax.sigrng = uu___81_6014.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___81_6014.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___81_6014.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___81_6014.FStar_Syntax_Syntax.sigattrs}))
in (FStar_Util.print1 "Inductive after phase 1: %s\n" uu____6011))
end
| uu____6019 -> begin
()
end));
ses1;
))
end
| uu____6020 -> begin
ses
end))
in (

let uu____6021 = (tc_inductive env2 ses1 se.FStar_Syntax_Syntax.sigquals lids)
in (match (uu____6021) with
| (sigbndle, projectors_ses) -> begin
(((sigbndle)::[]), (projectors_ses))
end))))
end
| FStar_Syntax_Syntax.Sig_pragma (p) -> begin
((FStar_Syntax_Util.process_pragma p r);
(((se)::[]), ([]));
)
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne) -> begin
(

let uu____6053 = (cps_and_elaborate env1 ne)
in (match (uu____6053) with
| (ses, ne1, lift_from_pure_opt) -> begin
(

let effect_and_lift_ses = (match (lift_from_pure_opt) with
| FStar_Pervasives_Native.Some (lift) -> begin
((

let uu___82_6090 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne1); FStar_Syntax_Syntax.sigrng = uu___82_6090.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___82_6090.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___82_6090.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___82_6090.FStar_Syntax_Syntax.sigattrs}))::(lift)::[]
end
| FStar_Pervasives_Native.None -> begin
((

let uu___83_6092 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne1); FStar_Syntax_Syntax.sigrng = uu___83_6092.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___83_6092.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___83_6092.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___83_6092.FStar_Syntax_Syntax.sigattrs}))::[]
end)
in (([]), ((FStar_List.append ses effect_and_lift_ses))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let ne1 = (

let uu____6099 = ((FStar_Options.use_two_phase_tc ()) && (FStar_TypeChecker_Env.should_verify env1))
in (match (uu____6099) with
| true -> begin
(

let ne1 = (

let uu____6101 = (

let uu____6102 = (

let uu____6103 = (tc_eff_decl (

let uu___84_6106 = env1
in {FStar_TypeChecker_Env.solver = uu___84_6106.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___84_6106.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___84_6106.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___84_6106.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___84_6106.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___84_6106.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___84_6106.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___84_6106.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___84_6106.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___84_6106.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___84_6106.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___84_6106.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___84_6106.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___84_6106.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___84_6106.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___84_6106.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___84_6106.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___84_6106.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___84_6106.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___84_6106.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___84_6106.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___84_6106.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___84_6106.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___84_6106.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___84_6106.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___84_6106.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___84_6106.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___84_6106.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___84_6106.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___84_6106.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___84_6106.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___84_6106.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___84_6106.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___84_6106.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___84_6106.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___84_6106.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___84_6106.FStar_TypeChecker_Env.dep_graph}) ne)
in (FStar_All.pipe_right uu____6103 (fun ne1 -> (

let uu___85_6110 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne1); FStar_Syntax_Syntax.sigrng = uu___85_6110.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___85_6110.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___85_6110.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___85_6110.FStar_Syntax_Syntax.sigattrs}))))
in (FStar_All.pipe_right uu____6102 (FStar_TypeChecker_Normalize.elim_uvars env1)))
in (FStar_All.pipe_right uu____6101 FStar_Syntax_Util.eff_decl_of_new_effect))
in ((

let uu____6112 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("TwoPhases")))
in (match (uu____6112) with
| true -> begin
(

let uu____6113 = (FStar_Syntax_Print.sigelt_to_string (

let uu___86_6116 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne1); FStar_Syntax_Syntax.sigrng = uu___86_6116.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___86_6116.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___86_6116.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___86_6116.FStar_Syntax_Syntax.sigattrs}))
in (FStar_Util.print1 "Effect decl after phase 1: %s\n" uu____6113))
end
| uu____6117 -> begin
()
end));
ne1;
))
end
| uu____6118 -> begin
ne
end))
in (

let ne2 = (tc_eff_decl env1 ne1)
in (

let se1 = (

let uu___87_6121 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne2); FStar_Syntax_Syntax.sigrng = uu___87_6121.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___87_6121.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___87_6121.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___87_6121.FStar_Syntax_Syntax.sigattrs})
in (((se1)::[]), ([])))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub1) -> begin
(

let ed_src = (FStar_TypeChecker_Env.get_effect_decl env1 sub1.FStar_Syntax_Syntax.source)
in (

let ed_tgt = (FStar_TypeChecker_Env.get_effect_decl env1 sub1.FStar_Syntax_Syntax.target)
in (

let uu____6129 = (

let uu____6136 = (FStar_TypeChecker_Env.lookup_effect_lid env1 sub1.FStar_Syntax_Syntax.source)
in (monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____6136))
in (match (uu____6129) with
| (a, wp_a_src) -> begin
(

let uu____6151 = (

let uu____6158 = (FStar_TypeChecker_Env.lookup_effect_lid env1 sub1.FStar_Syntax_Syntax.target)
in (monad_signature env1 sub1.FStar_Syntax_Syntax.target uu____6158))
in (match (uu____6151) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (

let uu____6174 = (

let uu____6177 = (

let uu____6178 = (

let uu____6185 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (uu____6185)))
in FStar_Syntax_Syntax.NT (uu____6178))
in (uu____6177)::[])
in (FStar_Syntax_Subst.subst uu____6174 wp_b_tgt))
in (

let expected_k = (

let uu____6193 = (

let uu____6200 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____6205 = (

let uu____6212 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (uu____6212)::[])
in (uu____6200)::uu____6205))
in (

let uu____6229 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow uu____6193 uu____6229)))
in (

let repr_type = (fun eff_name a1 wp -> (

let no_reify = (fun l -> (

let uu____6258 = (

let uu____6263 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((FStar_Errors.Fatal_EffectCannotBeReified), (uu____6263)))
in (

let uu____6264 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error uu____6258 uu____6264))))
in (

let uu____6267 = (FStar_TypeChecker_Env.effect_decl_opt env1 eff_name)
in (match (uu____6267) with
| FStar_Pervasives_Native.None -> begin
(no_reify eff_name)
end
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((FStar_Syntax_Syntax.U_unknown)::[]) env1 ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let uu____6301 = (

let uu____6302 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (not (uu____6302)))
in (match (uu____6301) with
| true -> begin
(no_reify eff_name)
end
| uu____6307 -> begin
(

let uu____6308 = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____6309 = (

let uu____6316 = (

let uu____6317 = (

let uu____6332 = (

let uu____6341 = (FStar_Syntax_Syntax.as_arg a1)
in (

let uu____6342 = (

let uu____6345 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____6345)::[])
in (uu____6341)::uu____6342))
in ((repr), (uu____6332)))
in FStar_Syntax_Syntax.Tm_app (uu____6317))
in (FStar_Syntax_Syntax.mk uu____6316))
in (uu____6309 FStar_Pervasives_Native.None uu____6308)))
end)))
end))))
in (

let uu____6359 = (match (((sub1.FStar_Syntax_Syntax.lift), (sub1.FStar_Syntax_Syntax.lift_wp))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(failwith "Impossible (parser)")
end
| (lift, FStar_Pervasives_Native.Some (uvs, lift_wp)) -> begin
(

let uu____6501 = (match (((FStar_List.length uvs) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____6510 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____6510) with
| (usubst, uvs1) -> begin
(

let uu____6533 = (FStar_TypeChecker_Env.push_univ_vars env1 uvs1)
in (

let uu____6534 = (FStar_Syntax_Subst.subst usubst lift_wp)
in ((uu____6533), (uu____6534))))
end))
end
| uu____6535 -> begin
((env1), (lift_wp))
end)
in (match (uu____6501) with
| (env2, lift_wp1) -> begin
(

let lift_wp2 = (match ((Prims.op_Equality (FStar_List.length uvs) (Prims.parse_int "0"))) with
| true -> begin
(check_and_gen env2 lift_wp1 expected_k)
end
| uu____6559 -> begin
(

let lift_wp2 = (tc_check_trivial_guard env2 lift_wp1 expected_k)
in (

let uu____6561 = (FStar_Syntax_Subst.close_univ_vars uvs lift_wp2)
in ((uvs), (uu____6561))))
end)
in ((lift), (lift_wp2)))
end))
end
| (FStar_Pervasives_Native.Some (what, lift), FStar_Pervasives_Native.None) -> begin
(

let uu____6606 = (match (((FStar_List.length what) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____6619 = (FStar_Syntax_Subst.univ_var_opening what)
in (match (uu____6619) with
| (usubst, uvs) -> begin
(

let uu____6644 = (FStar_Syntax_Subst.subst usubst lift)
in ((uvs), (uu____6644)))
end))
end
| uu____6647 -> begin
(([]), (lift))
end)
in (match (uu____6606) with
| (uvs, lift1) -> begin
((

let uu____6677 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____6677) with
| true -> begin
(

let uu____6678 = (FStar_Syntax_Print.term_to_string lift1)
in (FStar_Util.print1 "Lift for free : %s\n" uu____6678))
end
| uu____6679 -> begin
()
end));
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env1 (FStar_TypeChecker_TcTerm.tc_constant env1 FStar_Range.dummyRange))
in (

let uu____6681 = (

let uu____6688 = (FStar_TypeChecker_Env.push_univ_vars env1 uvs)
in (FStar_TypeChecker_TcTerm.tc_term uu____6688 lift1))
in (match (uu____6681) with
| (lift2, comp, uu____6711) -> begin
(

let uu____6712 = (FStar_TypeChecker_DMFF.star_expr dmff_env lift2)
in (match (uu____6712) with
| (uu____6739, lift_wp, lift_elab) -> begin
(

let lift_wp1 = (recheck_debug "lift-wp" env1 lift_wp)
in (

let lift_elab1 = (recheck_debug "lift-elab" env1 lift_elab)
in (match ((Prims.op_Equality (FStar_List.length uvs) (Prims.parse_int "0"))) with
| true -> begin
(

let uu____6764 = (

let uu____6767 = (FStar_TypeChecker_Util.generalize_universes env1 lift_elab1)
in FStar_Pervasives_Native.Some (uu____6767))
in (

let uu____6768 = (FStar_TypeChecker_Util.generalize_universes env1 lift_wp1)
in ((uu____6764), (uu____6768))))
end
| uu____6771 -> begin
(

let uu____6772 = (

let uu____6781 = (

let uu____6788 = (FStar_Syntax_Subst.close_univ_vars uvs lift_elab1)
in ((uvs), (uu____6788)))
in FStar_Pervasives_Native.Some (uu____6781))
in (

let uu____6797 = (

let uu____6804 = (FStar_Syntax_Subst.close_univ_vars uvs lift_wp1)
in ((uvs), (uu____6804)))
in ((uu____6772), (uu____6797))))
end)))
end))
end)));
)
end))
end)
in (match (uu____6359) with
| (lift, lift_wp) -> begin
(

let env2 = (

let uu___88_6864 = env1
in {FStar_TypeChecker_Env.solver = uu___88_6864.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___88_6864.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___88_6864.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___88_6864.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___88_6864.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___88_6864.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___88_6864.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___88_6864.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___88_6864.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___88_6864.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___88_6864.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___88_6864.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___88_6864.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___88_6864.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___88_6864.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___88_6864.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___88_6864.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___88_6864.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___88_6864.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___88_6864.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___88_6864.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___88_6864.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___88_6864.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___88_6864.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___88_6864.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___88_6864.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___88_6864.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___88_6864.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___88_6864.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___88_6864.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___88_6864.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___88_6864.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___88_6864.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___88_6864.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___88_6864.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___88_6864.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___88_6864.FStar_TypeChecker_Env.dep_graph})
in (

let lift1 = (match (lift) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (uvs, lift1) -> begin
(

let uu____6912 = (

let uu____6917 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____6917) with
| (usubst, uvs1) -> begin
(

let uu____6940 = (FStar_TypeChecker_Env.push_univ_vars env2 uvs1)
in (

let uu____6941 = (FStar_Syntax_Subst.subst usubst lift1)
in ((uu____6940), (uu____6941))))
end))
in (match (uu____6912) with
| (env3, lift2) -> begin
(

let uu____6954 = (

let uu____6961 = (FStar_TypeChecker_Env.lookup_effect_lid env3 sub1.FStar_Syntax_Syntax.source)
in (monad_signature env3 sub1.FStar_Syntax_Syntax.source uu____6961))
in (match (uu____6954) with
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

let lift_wp1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env3 (FStar_Pervasives_Native.snd lift_wp))
in (

let lift_wp_a = (

let uu____6993 = (FStar_TypeChecker_Env.get_range env3)
in (

let uu____6994 = (

let uu____7001 = (

let uu____7002 = (

let uu____7017 = (

let uu____7026 = (FStar_Syntax_Syntax.as_arg a_typ)
in (

let uu____7027 = (

let uu____7030 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (uu____7030)::[])
in (uu____7026)::uu____7027))
in ((lift_wp1), (uu____7017)))
in FStar_Syntax_Syntax.Tm_app (uu____7002))
in (FStar_Syntax_Syntax.mk uu____7001))
in (uu____6994 FStar_Pervasives_Native.None uu____6993)))
in (repr_type sub1.FStar_Syntax_Syntax.target a_typ lift_wp_a)))
in (

let expected_k1 = (

let uu____7047 = (

let uu____7054 = (FStar_Syntax_Syntax.mk_binder a1)
in (

let uu____7059 = (

let uu____7066 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (

let uu____7071 = (

let uu____7078 = (FStar_Syntax_Syntax.null_binder repr_f)
in (uu____7078)::[])
in (uu____7066)::uu____7071))
in (uu____7054)::uu____7059))
in (

let uu____7099 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow uu____7047 uu____7099)))
in (

let uu____7102 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env3 expected_k1)
in (match (uu____7102) with
| (expected_k2, uu____7120, uu____7121) -> begin
(

let lift3 = (match ((Prims.op_Equality (FStar_List.length uvs) (Prims.parse_int "0"))) with
| true -> begin
(check_and_gen env3 lift2 expected_k2)
end
| uu____7123 -> begin
(

let lift3 = (tc_check_trivial_guard env3 lift2 expected_k2)
in (

let uu____7125 = (FStar_Syntax_Subst.close_univ_vars uvs lift3)
in ((uvs), (uu____7125))))
end)
in FStar_Pervasives_Native.Some (lift3))
end))))))))
end))
end))
end)
in ((

let uu____7129 = (

let uu____7130 = (

let uu____7131 = (FStar_All.pipe_right lift_wp FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____7131 FStar_List.length))
in (Prims.op_disEquality uu____7130 (Prims.parse_int "1")))
in (match (uu____7129) with
| true -> begin
(

let uu____7150 = (

let uu____7155 = (

let uu____7156 = (FStar_Syntax_Print.lid_to_string sub1.FStar_Syntax_Syntax.source)
in (

let uu____7157 = (FStar_Syntax_Print.lid_to_string sub1.FStar_Syntax_Syntax.target)
in (

let uu____7158 = (

let uu____7159 = (

let uu____7160 = (FStar_All.pipe_right lift_wp FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____7160 FStar_List.length))
in (FStar_All.pipe_right uu____7159 FStar_Util.string_of_int))
in (FStar_Util.format3 "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes" uu____7156 uu____7157 uu____7158))))
in ((FStar_Errors.Fatal_TooManyUniverse), (uu____7155)))
in (FStar_Errors.raise_error uu____7150 r))
end
| uu____7179 -> begin
()
end));
(

let uu____7181 = ((FStar_Util.is_some lift1) && (

let uu____7191 = (

let uu____7192 = (

let uu____7195 = (FStar_All.pipe_right lift1 FStar_Util.must)
in (FStar_All.pipe_right uu____7195 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____7192 FStar_List.length))
in (Prims.op_disEquality uu____7191 (Prims.parse_int "1"))))
in (match (uu____7181) with
| true -> begin
(

let uu____7246 = (

let uu____7251 = (

let uu____7252 = (FStar_Syntax_Print.lid_to_string sub1.FStar_Syntax_Syntax.source)
in (

let uu____7253 = (FStar_Syntax_Print.lid_to_string sub1.FStar_Syntax_Syntax.target)
in (

let uu____7254 = (

let uu____7255 = (

let uu____7256 = (

let uu____7259 = (FStar_All.pipe_right lift1 FStar_Util.must)
in (FStar_All.pipe_right uu____7259 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____7256 FStar_List.length))
in (FStar_All.pipe_right uu____7255 FStar_Util.string_of_int))
in (FStar_Util.format3 "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes" uu____7252 uu____7253 uu____7254))))
in ((FStar_Errors.Fatal_TooManyUniverse), (uu____7251)))
in (FStar_Errors.raise_error uu____7246 r))
end
| uu____7310 -> begin
()
end));
(

let sub2 = (

let uu___89_7312 = sub1
in {FStar_Syntax_Syntax.source = uu___89_7312.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = uu___89_7312.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = FStar_Pervasives_Native.Some (lift_wp); FStar_Syntax_Syntax.lift = lift1})
in (

let se1 = (

let uu___90_7314 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_sub_effect (sub2); FStar_Syntax_Syntax.sigrng = uu___90_7314.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___90_7314.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___90_7314.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___90_7314.FStar_Syntax_Syntax.sigattrs})
in (((se1)::[]), ([]))));
)))
end)))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, flags1) -> begin
(

let env0 = env1
in (

let uu____7329 = (match ((Prims.op_Equality (FStar_List.length uvs) (Prims.parse_int "0"))) with
| true -> begin
((env1), (uvs), (tps), (c))
end
| uu____7346 -> begin
(

let uu____7347 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____7347) with
| (usubst, uvs1) -> begin
(

let tps1 = (FStar_Syntax_Subst.subst_binders usubst tps)
in (

let c1 = (

let uu____7376 = (FStar_Syntax_Subst.shift_subst (FStar_List.length tps1) usubst)
in (FStar_Syntax_Subst.subst_comp uu____7376 c))
in (

let uu____7383 = (FStar_TypeChecker_Env.push_univ_vars env1 uvs1)
in ((uu____7383), (uvs1), (tps1), (c1)))))
end))
end)
in (match (uu____7329) with
| (env2, uvs1, tps1, c1) -> begin
(

let env3 = (FStar_TypeChecker_Env.set_range env2 r)
in (

let uu____7399 = (FStar_Syntax_Subst.open_comp tps1 c1)
in (match (uu____7399) with
| (tps2, c2) -> begin
(

let uu____7414 = (FStar_TypeChecker_TcTerm.tc_tparams env3 tps2)
in (match (uu____7414) with
| (tps3, env4, us) -> begin
(

let uu____7432 = (FStar_TypeChecker_TcTerm.tc_comp env4 c2)
in (match (uu____7432) with
| (c3, u, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env4 g);
(

let tps4 = (FStar_Syntax_Subst.close_binders tps3)
in (

let c4 = (FStar_Syntax_Subst.close_comp tps4 c3)
in (

let uu____7453 = (

let uu____7454 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps4), (c4)))) FStar_Pervasives_Native.None r)
in (FStar_TypeChecker_Util.generalize_universes env0 uu____7454))
in (match (uu____7453) with
| (uvs2, t) -> begin
(

let uu____7481 = (

let uu____7486 = (

let uu____7497 = (

let uu____7498 = (FStar_Syntax_Subst.compress t)
in uu____7498.FStar_Syntax_Syntax.n)
in ((tps4), (uu____7497)))
in (match (uu____7486) with
| ([], FStar_Syntax_Syntax.Tm_arrow (uu____7511, c5)) -> begin
(([]), (c5))
end
| (uu____7551, FStar_Syntax_Syntax.Tm_arrow (tps5, c5)) -> begin
((tps5), (c5))
end
| uu____7590 -> begin
(failwith "Impossible (t is an arrow)")
end))
in (match (uu____7481) with
| (tps5, c5) -> begin
((match ((Prims.op_disEquality (FStar_List.length uvs2) (Prims.parse_int "1"))) with
| true -> begin
(

let uu____7616 = (FStar_Syntax_Subst.open_univ_vars uvs2 t)
in (match (uu____7616) with
| (uu____7621, t1) -> begin
(

let uu____7623 = (

let uu____7628 = (

let uu____7629 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____7630 = (FStar_All.pipe_right (FStar_List.length uvs2) FStar_Util.string_of_int)
in (

let uu____7631 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)" uu____7629 uu____7630 uu____7631))))
in ((FStar_Errors.Fatal_TooManyUniverse), (uu____7628)))
in (FStar_Errors.raise_error uu____7623 r))
end))
end
| uu____7632 -> begin
()
end);
(

let se1 = (

let uu___91_7634 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (((lid), (uvs2), (tps5), (c5), (flags1))); FStar_Syntax_Syntax.sigrng = uu___91_7634.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___91_7634.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___91_7634.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___91_7634.FStar_Syntax_Syntax.sigattrs})
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
| FStar_Syntax_Syntax.Sig_declare_typ (uu____7641, uu____7642, uu____7643) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___60_7647 -> (match (uu___60_7647) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____7648 -> begin
false
end)))) -> begin
(([]), ([]))
end
| FStar_Syntax_Syntax.Sig_let (uu____7653, uu____7654) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___60_7662 -> (match (uu___60_7662) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____7663 -> begin
false
end)))) -> begin
(([]), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_range env1 r)
in ((

let uu____7673 = (FStar_TypeChecker_Env.lid_exists env2 lid)
in (match (uu____7673) with
| true -> begin
(

let uu____7674 = (

let uu____7679 = (

let uu____7680 = (FStar_Ident.text_of_lid lid)
in (FStar_Util.format1 "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module" uu____7680))
in ((FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration), (uu____7679)))
in (FStar_Errors.raise_error uu____7674 r))
end
| uu____7681 -> begin
()
end));
(

let uu____7682 = (match ((Prims.op_Equality uvs [])) with
| true -> begin
(

let uu____7691 = (

let uu____7692 = (FStar_Syntax_Util.type_u ())
in (FStar_Pervasives_Native.fst uu____7692))
in (check_and_gen env2 t uu____7691))
end
| uu____7697 -> begin
(

let uu____7698 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____7698) with
| (uvs1, t1) -> begin
(

let env3 = (FStar_TypeChecker_Env.push_univ_vars env2 uvs1)
in (

let t2 = (

let uu____7711 = (

let uu____7712 = (FStar_Syntax_Util.type_u ())
in (FStar_Pervasives_Native.fst uu____7712))
in (tc_check_trivial_guard env3 t1 uu____7711))
in (

let t3 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.DoNotUnfoldPureLets)::[]) env3 t2)
in (

let uu____7718 = (FStar_Syntax_Subst.close_univ_vars uvs1 t3)
in ((uvs1), (uu____7718))))))
end))
end)
in (match (uu____7682) with
| (uvs1, t1) -> begin
(

let se1 = (

let uu___92_7730 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (uvs1), (t1))); FStar_Syntax_Syntax.sigrng = uu___92_7730.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___92_7730.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___92_7730.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___92_7730.FStar_Syntax_Syntax.sigattrs})
in (((se1)::[]), ([])))
end));
))
end
| FStar_Syntax_Syntax.Sig_assume (lid, us, phi) -> begin
(

let uu____7738 = (FStar_Syntax_Subst.open_univ_vars us phi)
in (match (uu____7738) with
| (us1, phi1) -> begin
(

let env2 = (FStar_TypeChecker_Env.push_univ_vars env1 us1)
in (

let phi2 = (

let uu____7755 = ((FStar_Options.use_two_phase_tc ()) && (FStar_TypeChecker_Env.should_verify env2))
in (match (uu____7755) with
| true -> begin
(

let phi2 = (

let uu____7757 = (tc_assume (

let uu___93_7760 = env2
in {FStar_TypeChecker_Env.solver = uu___93_7760.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___93_7760.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___93_7760.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___93_7760.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___93_7760.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___93_7760.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___93_7760.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___93_7760.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___93_7760.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___93_7760.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___93_7760.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___93_7760.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___93_7760.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___93_7760.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___93_7760.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___93_7760.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___93_7760.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___93_7760.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___93_7760.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___93_7760.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___93_7760.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___93_7760.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___93_7760.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___93_7760.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___93_7760.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___93_7760.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___93_7760.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___93_7760.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___93_7760.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___93_7760.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___93_7760.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___93_7760.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___93_7760.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___93_7760.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___93_7760.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___93_7760.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___93_7760.FStar_TypeChecker_Env.dep_graph}) phi1 r)
in (FStar_All.pipe_right uu____7757 (FStar_TypeChecker_Normalize.remove_uvar_solutions env2)))
in ((

let uu____7762 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("TwoPhases")))
in (match (uu____7762) with
| true -> begin
(

let uu____7763 = (FStar_Syntax_Print.term_to_string phi2)
in (FStar_Util.print1 "Assume after phase 1: %s\n" uu____7763))
end
| uu____7764 -> begin
()
end));
phi2;
))
end
| uu____7765 -> begin
phi1
end))
in (

let phi3 = (tc_assume env2 phi2 r)
in (

let uu____7767 = (match ((Prims.op_Equality us1 [])) with
| true -> begin
(FStar_TypeChecker_Util.generalize_universes env2 phi3)
end
| uu____7778 -> begin
(

let uu____7779 = (FStar_Syntax_Subst.close_univ_vars us1 phi3)
in ((us1), (uu____7779)))
end)
in (match (uu____7767) with
| (us2, phi4) -> begin
((({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_assume (((lid), (us2), (phi4))); FStar_Syntax_Syntax.sigrng = r; FStar_Syntax_Syntax.sigquals = se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})::[]), ([]))
end)))))
end))
end
| FStar_Syntax_Syntax.Sig_main (e) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_range env1 r)
in (

let env3 = (FStar_TypeChecker_Env.set_expected_typ env2 FStar_Syntax_Syntax.t_unit)
in (

let uu____7797 = (FStar_TypeChecker_TcTerm.tc_term env3 e)
in (match (uu____7797) with
| (e1, c, g1) -> begin
(

let uu____7815 = (

let uu____7822 = (

let uu____7825 = (FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r)
in FStar_Pervasives_Native.Some (uu____7825))
in (

let uu____7826 = (

let uu____7831 = (FStar_Syntax_Syntax.lcomp_comp c)
in ((e1), (uu____7831)))
in (FStar_TypeChecker_TcTerm.check_expected_effect env3 uu____7822 uu____7826)))
in (match (uu____7815) with
| (e2, uu____7841, g) -> begin
((

let uu____7844 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env3 uu____7844));
(

let se1 = (

let uu___94_7846 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_main (e2); FStar_Syntax_Syntax.sigrng = uu___94_7846.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___94_7846.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___94_7846.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___94_7846.FStar_Syntax_Syntax.sigattrs})
in (((se1)::[]), ([])));
)
end))
end))))
end
| FStar_Syntax_Syntax.Sig_splice (lids, t) -> begin
((

let uu____7858 = (FStar_Options.debug_any ())
in (match (uu____7858) with
| true -> begin
(

let uu____7859 = (FStar_Ident.string_of_lid env1.FStar_TypeChecker_Env.curmodule)
in (

let uu____7860 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "%s: Found splice of (%s)\n" uu____7859 uu____7860)))
end
| uu____7861 -> begin
()
end));
(

let ses = (env1.FStar_TypeChecker_Env.splice env1 t)
in (

let lids' = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses)
in ((FStar_List.iter (fun lid -> (

let uu____7873 = (FStar_List.tryFind (FStar_Ident.lid_equals lid) lids')
in (match (uu____7873) with
| FStar_Pervasives_Native.Some (uu____7876) -> begin
()
end
| FStar_Pervasives_Native.None -> begin
(

let uu____7877 = (

let uu____7882 = (

let uu____7883 = (FStar_Ident.string_of_lid lid)
in (

let uu____7884 = (

let uu____7885 = (FStar_List.map FStar_Ident.string_of_lid lids')
in (FStar_All.pipe_left (FStar_String.concat ", ") uu____7885))
in (FStar_Util.format2 "Splice declared the name %s but it was not defined.\nThose defined were: %s" uu____7883 uu____7884)))
in ((FStar_Errors.Fatal_SplicedUndef), (uu____7882)))
in (FStar_Errors.raise_error uu____7877 r))
end))) lids);
(([]), (ses));
)));
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

let uu____7946 = ((Prims.op_Equality (FStar_List.length q) (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q'))
in (match (uu____7946) with
| true -> begin
FStar_Pervasives_Native.Some (q)
end
| uu____7953 -> begin
(

let uu____7954 = (

let uu____7959 = (

let uu____7960 = (FStar_Syntax_Print.lid_to_string l)
in (

let uu____7961 = (FStar_Syntax_Print.quals_to_string q)
in (

let uu____7962 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" uu____7960 uu____7961 uu____7962))))
in ((FStar_Errors.Fatal_InconsistentQualifierAnnotation), (uu____7959)))
in (FStar_Errors.raise_error uu____7954 r))
end))
end))
in (

let rename_parameters = (fun lb -> (

let rename_in_typ = (fun def typ -> (

let typ1 = (FStar_Syntax_Subst.compress typ)
in (

let def_bs = (

let uu____7994 = (

let uu____7995 = (FStar_Syntax_Subst.compress def)
in uu____7995.FStar_Syntax_Syntax.n)
in (match (uu____7994) with
| FStar_Syntax_Syntax.Tm_abs (binders, uu____8005, uu____8006) -> begin
binders
end
| uu____8027 -> begin
[]
end))
in (match (typ1) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow (val_bs, c); FStar_Syntax_Syntax.pos = r1; FStar_Syntax_Syntax.vars = uu____8037} -> begin
(

let has_auto_name = (fun bv -> (FStar_Util.starts_with bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Ident.reserved_prefix))
in (

let rec rename_binders1 = (fun def_bs1 val_bs1 -> (match (((def_bs1), (val_bs1))) with
| ([], uu____8121) -> begin
val_bs1
end
| (uu____8144, []) -> begin
val_bs1
end
| (((body_bv, uu____8168))::bt, ((val_bv, aqual))::vt) -> begin
(

let uu____8205 = (rename_binders1 bt vt)
in ((match ((((has_auto_name body_bv)), ((has_auto_name val_bv)))) with
| (true, uu____8221) -> begin
((val_bv), (aqual))
end
| (false, true) -> begin
(((

let uu___95_8223 = val_bv
in {FStar_Syntax_Syntax.ppname = (

let uu___96_8226 = val_bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = body_bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText; FStar_Ident.idRange = uu___96_8226.FStar_Ident.idRange}); FStar_Syntax_Syntax.index = uu___95_8223.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___95_8223.FStar_Syntax_Syntax.sort})), (aqual))
end
| (false, false) -> begin
((val_bv), (aqual))
end))::uu____8205)
end))
in (

let uu____8227 = (

let uu____8234 = (

let uu____8235 = (

let uu____8248 = (rename_binders1 def_bs val_bs)
in ((uu____8248), (c)))
in FStar_Syntax_Syntax.Tm_arrow (uu____8235))
in (FStar_Syntax_Syntax.mk uu____8234))
in (uu____8227 FStar_Pervasives_Native.None r1))))
end
| uu____8266 -> begin
typ1
end))))
in (

let uu___97_8267 = lb
in (

let uu____8268 = (rename_in_typ lb.FStar_Syntax_Syntax.lbdef lb.FStar_Syntax_Syntax.lbtyp)
in {FStar_Syntax_Syntax.lbname = uu___97_8267.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___97_8267.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____8268; FStar_Syntax_Syntax.lbeff = uu___97_8267.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___97_8267.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___97_8267.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___97_8267.FStar_Syntax_Syntax.lbpos}))))
in (

let uu____8271 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.fold_left (fun uu____8322 lb -> (match (uu____8322) with
| (gen1, lbs1, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____8364 = (

let uu____8375 = (FStar_TypeChecker_Env.try_lookup_val_decl env2 lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____8375) with
| FStar_Pervasives_Native.None -> begin
(match ((Prims.op_disEquality lb.FStar_Syntax_Syntax.lbunivs [])) with
| true -> begin
((false), (lb), (quals_opt))
end
| uu____8416 -> begin
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
| uu____8448 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((lb.FStar_Syntax_Syntax.lbdef), (((FStar_Util.Inl (lb.FStar_Syntax_Syntax.lbtyp)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.pos)
end)
in ((match (((Prims.op_disEquality lb.FStar_Syntax_Syntax.lbunivs []) && (Prims.op_disEquality (FStar_List.length lb.FStar_Syntax_Syntax.lbunivs) (FStar_List.length uvs)))) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_IncoherentInlineUniverse), ("Inline universes are incoherent with annotation from val declaration")) r)
end
| uu____8490 -> begin
()
end);
(

let uu____8491 = (FStar_Syntax_Syntax.mk_lb ((FStar_Util.Inr (lbname)), (uvs), (FStar_Parser_Const.effect_ALL_lid), (tval), (def), (lb.FStar_Syntax_Syntax.lbpos)))
in ((false), (uu____8491), (quals_opt1)));
)))
end))
in (match (uu____8364) with
| (gen2, lb1, quals_opt1) -> begin
((gen2), ((lb1)::lbs1), (quals_opt1))
end)))
end)) ((true), ([]), ((match ((Prims.op_Equality se.FStar_Syntax_Syntax.sigquals [])) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____8541 -> begin
FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
end)))))
in (match (uu____8271) with
| (should_generalize, lbs', quals_opt) -> begin
(

let quals = (match (quals_opt) with
| FStar_Pervasives_Native.None -> begin
(FStar_Syntax_Syntax.Visible_default)::[]
end
| FStar_Pervasives_Native.Some (q) -> begin
(

let uu____8579 = (FStar_All.pipe_right q (FStar_Util.for_some (fun uu___61_8583 -> (match (uu___61_8583) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| FStar_Syntax_Syntax.Visible_default -> begin
true
end
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____8584 -> begin
false
end))))
in (match (uu____8579) with
| true -> begin
q
end
| uu____8587 -> begin
(FStar_Syntax_Syntax.Visible_default)::q
end))
end)
in (

let lbs'1 = (FStar_List.rev lbs')
in (

let e = (

let uu____8594 = (

let uu____8601 = (

let uu____8602 = (

let uu____8615 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) FStar_Pervasives_Native.None r)
in (((((FStar_Pervasives_Native.fst lbs)), (lbs'1))), (uu____8615)))
in FStar_Syntax_Syntax.Tm_let (uu____8602))
in (FStar_Syntax_Syntax.mk uu____8601))
in (uu____8594 FStar_Pervasives_Native.None r))
in (

let env0 = (

let uu___98_8634 = env2
in {FStar_TypeChecker_Env.solver = uu___98_8634.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___98_8634.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___98_8634.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___98_8634.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___98_8634.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___98_8634.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___98_8634.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___98_8634.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___98_8634.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___98_8634.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___98_8634.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___98_8634.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = uu___98_8634.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = uu___98_8634.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___98_8634.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___98_8634.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___98_8634.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___98_8634.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___98_8634.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___98_8634.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___98_8634.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___98_8634.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___98_8634.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___98_8634.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___98_8634.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___98_8634.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___98_8634.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___98_8634.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___98_8634.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___98_8634.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___98_8634.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___98_8634.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___98_8634.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___98_8634.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___98_8634.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___98_8634.FStar_TypeChecker_Env.dep_graph})
in (

let e1 = (

let uu____8636 = ((FStar_Options.use_two_phase_tc ()) && (FStar_TypeChecker_Env.should_verify env0))
in (match (uu____8636) with
| true -> begin
(

let drop_lbtyp = (fun e_lax -> (

let uu____8643 = (

let uu____8644 = (FStar_Syntax_Subst.compress e_lax)
in uu____8644.FStar_Syntax_Syntax.n)
in (match (uu____8643) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let lb_unannotated = (

let uu____8662 = (

let uu____8663 = (FStar_Syntax_Subst.compress e)
in uu____8663.FStar_Syntax_Syntax.n)
in (match (uu____8662) with
| FStar_Syntax_Syntax.Tm_let ((uu____8666, (lb1)::[]), uu____8668) -> begin
(

let uu____8681 = (

let uu____8682 = (FStar_Syntax_Subst.compress lb1.FStar_Syntax_Syntax.lbtyp)
in uu____8682.FStar_Syntax_Syntax.n)
in (Prims.op_Equality uu____8681 FStar_Syntax_Syntax.Tm_unknown))
end
| uu____8685 -> begin
(failwith "Impossible: first phase lb and second phase lb differ in structure!")
end))
in (match (lb_unannotated) with
| true -> begin
(

let uu___99_8686 = e_lax
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (((((false), (((

let uu___100_8698 = lb
in {FStar_Syntax_Syntax.lbname = uu___100_8698.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___100_8698.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = uu___100_8698.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___100_8698.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___100_8698.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___100_8698.FStar_Syntax_Syntax.lbpos}))::[]))), (e2))); FStar_Syntax_Syntax.pos = uu___99_8686.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___99_8686.FStar_Syntax_Syntax.vars})
end
| uu____8699 -> begin
e_lax
end))
end
| uu____8700 -> begin
e_lax
end)))
in (

let e1 = (

let uu____8702 = (

let uu____8703 = (

let uu____8704 = (FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term (

let uu___101_8713 = env0
in {FStar_TypeChecker_Env.solver = uu___101_8713.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___101_8713.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___101_8713.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___101_8713.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___101_8713.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___101_8713.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___101_8713.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___101_8713.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___101_8713.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___101_8713.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___101_8713.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___101_8713.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___101_8713.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___101_8713.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___101_8713.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___101_8713.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___101_8713.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___101_8713.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___101_8713.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___101_8713.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___101_8713.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___101_8713.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___101_8713.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___101_8713.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___101_8713.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___101_8713.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___101_8713.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___101_8713.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___101_8713.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___101_8713.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___101_8713.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___101_8713.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___101_8713.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___101_8713.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___101_8713.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___101_8713.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___101_8713.FStar_TypeChecker_Env.dep_graph}) e)
in (FStar_All.pipe_right uu____8704 (fun uu____8724 -> (match (uu____8724) with
| (e1, uu____8732, uu____8733) -> begin
e1
end))))
in (FStar_All.pipe_right uu____8703 (FStar_TypeChecker_Normalize.remove_uvar_solutions env0)))
in (FStar_All.pipe_right uu____8702 drop_lbtyp))
in ((

let uu____8735 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("TwoPhases")))
in (match (uu____8735) with
| true -> begin
(

let uu____8736 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.print1 "Let binding after phase 1: %s\n" uu____8736))
end
| uu____8737 -> begin
()
end));
e1;
)))
end
| uu____8738 -> begin
e
end))
in (

let uu____8739 = (

let uu____8750 = (FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term env0 e1)
in (match (uu____8750) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs1, e2); FStar_Syntax_Syntax.pos = uu____8769; FStar_Syntax_Syntax.vars = uu____8770}, uu____8771, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let lbs2 = (

let uu____8798 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1) (FStar_List.map rename_parameters))
in (((FStar_Pervasives_Native.fst lbs1)), (uu____8798)))
in (

let quals1 = (match (e2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (uu____8816, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| uu____8821 -> begin
quals
end)
in (((

let uu___102_8829 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((lbs2), (lids))); FStar_Syntax_Syntax.sigrng = uu___102_8829.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = uu___102_8829.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___102_8829.FStar_Syntax_Syntax.sigattrs})), (lbs2))))
end
| uu____8832 -> begin
(failwith "impossible (typechecking should preserve Tm_let)")
end))
in (match (uu____8739) with
| (se1, lbs1) -> begin
((FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1) (FStar_List.iter (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (FStar_TypeChecker_Env.insert_fv_info env2 fv lb.FStar_Syntax_Syntax.lbtyp)))));
(

let uu____8881 = (log env2)
in (match (uu____8881) with
| true -> begin
(

let uu____8882 = (

let uu____8883 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1) (FStar_List.map (fun lb -> (

let should_log = (

let uu____8898 = (

let uu____8907 = (

let uu____8908 = (

let uu____8911 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____8911.FStar_Syntax_Syntax.fv_name)
in uu____8908.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env2 uu____8907))
in (match (uu____8898) with
| FStar_Pervasives_Native.None -> begin
true
end
| uu____8918 -> begin
false
end))
in (match (should_log) with
| true -> begin
(

let uu____8927 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____8928 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" uu____8927 uu____8928)))
end
| uu____8929 -> begin
""
end)))))
in (FStar_All.pipe_right uu____8883 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" uu____8882))
end
| uu____8932 -> begin
()
end));
(((se1)::[]), ([]));
)
end)))))))
end)))))
end));
)))


let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___62_8980 -> (match (uu___62_8980) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| uu____8981 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| FStar_Syntax_Syntax.Projector (l, uu____8989) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| FStar_Syntax_Syntax.Discriminator (l) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| uu____8995 -> begin
false
end))
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_pragma (uu____9004) -> begin
(([]), (hidden))
end
| FStar_Syntax_Syntax.Sig_splice (uu____9009) -> begin
(failwith "Impossible (Already handled)")
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____9024) -> begin
(failwith "Impossible (Already handled)")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____9049) -> begin
(failwith "Impossible (Already handled)")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____9073) -> begin
(

let uu____9082 = (is_abstract se.FStar_Syntax_Syntax.sigquals)
in (match (uu____9082) with
| true -> begin
(

let for_export_bundle = (fun se1 uu____9117 -> (match (uu____9117) with
| (out, hidden1) -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, uu____9156, uu____9157) -> begin
(

let dec = (

let uu___103_9167 = se1
in (

let uu____9168 = (

let uu____9169 = (

let uu____9176 = (

let uu____9177 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow bs uu____9177))
in ((l), (us), (uu____9176)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____9169))
in {FStar_Syntax_Syntax.sigel = uu____9168; FStar_Syntax_Syntax.sigrng = uu___103_9167.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::se1.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___103_9167.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___103_9167.FStar_Syntax_Syntax.sigattrs}))
in (((dec)::out), (hidden1)))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, uu____9187, uu____9188, uu____9189) -> begin
(

let dec = (

let uu___104_9195 = se1
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t))); FStar_Syntax_Syntax.sigrng = uu___104_9195.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::[]; FStar_Syntax_Syntax.sigmeta = uu___104_9195.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___104_9195.FStar_Syntax_Syntax.sigattrs})
in (((dec)::out), ((l)::hidden1)))
end
| uu____9200 -> begin
((out), (hidden1))
end)
end))
in (FStar_List.fold_right for_export_bundle ses (([]), (hidden))))
end
| uu____9217 -> begin
(((se)::[]), (hidden))
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____9222, uu____9223, uu____9224) -> begin
(

let uu____9225 = (is_abstract se.FStar_Syntax_Syntax.sigquals)
in (match (uu____9225) with
| true -> begin
(([]), (hidden))
end
| uu____9238 -> begin
(((se)::[]), (hidden))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, us, t) -> begin
(

let uu____9246 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some is_hidden_proj_or_disc))
in (match (uu____9246) with
| true -> begin
((((

let uu___105_9262 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t))); FStar_Syntax_Syntax.sigrng = uu___105_9262.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::[]; FStar_Syntax_Syntax.sigmeta = uu___105_9262.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___105_9262.FStar_Syntax_Syntax.sigattrs}))::[]), ((l)::hidden))
end
| uu____9263 -> begin
(

let uu____9264 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___63_9268 -> (match (uu___63_9268) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____9269) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____9274) -> begin
true
end
| uu____9275 -> begin
false
end))))
in (match (uu____9264) with
| true -> begin
(((se)::[]), (hidden))
end
| uu____9288 -> begin
(([]), (hidden))
end))
end))
end
| FStar_Syntax_Syntax.Sig_main (uu____9293) -> begin
(([]), (hidden))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____9298) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____9303) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____9308) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____9313) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____9331) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____9342 = (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
in (match (uu____9342) with
| true -> begin
(([]), (hidden))
end
| uu____9357 -> begin
(

let dec = (

let uu____9359 = (FStar_Ident.range_of_lid lid)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu____9359; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::[]; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (((dec)::[]), ((lid)::hidden)))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, l) -> begin
(

let uu____9370 = (is_abstract se.FStar_Syntax_Syntax.sigquals)
in (match (uu____9370) with
| true -> begin
(

let uu____9379 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let uu___106_9392 = se
in (

let uu____9393 = (

let uu____9394 = (

let uu____9401 = (

let uu____9402 = (

let uu____9405 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____9405.FStar_Syntax_Syntax.fv_name)
in uu____9402.FStar_Syntax_Syntax.v)
in ((uu____9401), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____9394))
in {FStar_Syntax_Syntax.sigel = uu____9393; FStar_Syntax_Syntax.sigrng = uu___106_9392.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___106_9392.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___106_9392.FStar_Syntax_Syntax.sigattrs})))))
in ((uu____9379), (hidden)))
end
| uu____9410 -> begin
(((se)::[]), (hidden))
end))
end))))


let add_sigelt_to_env : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____9425) -> begin
(failwith "add_sigelt_to_env: Impossible, bare data constructor")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____9442) -> begin
(failwith "add_sigelt_to_env: Impossible, bare data constructor")
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (uu____9457)) -> begin
(z3_reset_options env)
end
| FStar_Syntax_Syntax.Sig_pragma (uu____9460) -> begin
env
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____9461) -> begin
env
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_sigelt env se)
in (FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun env2 a -> (

let uu____9471 = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Env.push_sigelt env2 uu____9471))) env1)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____9472, uu____9473, uu____9474) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___64_9478 -> (match (uu___64_9478) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____9479 -> begin
false
end)))) -> begin
env
end
| FStar_Syntax_Syntax.Sig_let (uu____9480, uu____9481) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___64_9489 -> (match (uu___64_9489) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____9490 -> begin
false
end)))) -> begin
env
end
| uu____9491 -> begin
(FStar_TypeChecker_Env.push_sigelt env se)
end))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let rec process_one_decl = (fun uu____9559 se -> (match (uu____9559) with
| (ses1, exports, env1, hidden) -> begin
((

let uu____9612 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____9612) with
| true -> begin
(

let uu____9613 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____9613))
end
| uu____9614 -> begin
()
end));
(

let uu____9615 = (tc_decl env1 se)
in (match (uu____9615) with
| (ses', ses_elaborated) -> begin
(

let ses'1 = (FStar_All.pipe_right ses' (FStar_List.map (fun se1 -> ((

let uu____9665 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("UF")))
in (match (uu____9665) with
| true -> begin
(

let uu____9666 = (FStar_Syntax_Print.sigelt_to_string se1)
in (FStar_Util.print1 "About to elim vars from %s" uu____9666))
end
| uu____9667 -> begin
()
end));
(FStar_TypeChecker_Normalize.elim_uvars env1 se1);
))))
in (

let ses_elaborated1 = (FStar_All.pipe_right ses_elaborated (FStar_List.map (fun se1 -> (FStar_TypeChecker_Normalize.elim_uvars env1 se1))))
in ((FStar_TypeChecker_Env.promote_id_info env1 (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.CheckNoUvars)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.DoNotUnfoldPureLets)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Iota))::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env1 t)));
(

let env2 = (FStar_All.pipe_right ses'1 (FStar_List.fold_left (fun env2 se1 -> (add_sigelt_to_env env2 se1)) env1))
in ((FStar_Syntax_Unionfind.reset ());
(

let uu____9689 = ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("LogTypes"))))
in (match (uu____9689) with
| true -> begin
(

let uu____9690 = (FStar_List.fold_left (fun s se1 -> (

let uu____9696 = (

let uu____9697 = (FStar_Syntax_Print.sigelt_to_string se1)
in (Prims.strcat uu____9697 "\n"))
in (Prims.strcat s uu____9696))) "" ses'1)
in (FStar_Util.print1 "Checked: %s\n" uu____9690))
end
| uu____9698 -> begin
()
end));
(FStar_List.iter (fun se1 -> (env2.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env2 se1)) ses'1);
(

let uu____9702 = (

let uu____9711 = (FStar_Options.use_extracted_interfaces ())
in (match (uu____9711) with
| true -> begin
(([]), ([]))
end
| uu____9724 -> begin
(

let accum_exports_hidden = (fun uu____9750 se1 -> (match (uu____9750) with
| (exports1, hidden1) -> begin
(

let uu____9778 = (for_export hidden1 se1)
in (match (uu____9778) with
| (se_exported, hidden2) -> begin
(((FStar_List.rev_append se_exported exports1)), (hidden2))
end))
end))
in (FStar_List.fold_left accum_exports_hidden ((exports), (hidden)) ses'1))
end))
in (match (uu____9702) with
| (exports1, hidden1) -> begin
(

let ses'2 = (FStar_List.map (fun s -> (

let uu___107_9857 = s
in {FStar_Syntax_Syntax.sigel = uu___107_9857.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___107_9857.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___107_9857.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___107_9857.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = se.FStar_Syntax_Syntax.sigattrs})) ses'1)
in (((((FStar_List.rev_append ses'2 ses1)), (exports1), (env2), (hidden1))), (ses_elaborated1)))
end));
));
)))
end));
)
end))
in (

let process_one_decl_timed = (fun acc se -> (

let uu____9939 = acc
in (match (uu____9939) with
| (uu____9974, uu____9975, env1, uu____9977) -> begin
(

let uu____9990 = (FStar_Util.record_time (fun uu____10036 -> (process_one_decl acc se)))
in (match (uu____9990) with
| (r, ms_elapsed) -> begin
((

let uu____10100 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("TCDeclTime")))
in (match (uu____10100) with
| true -> begin
(

let uu____10101 = (FStar_Syntax_Print.sigelt_to_string_short se)
in (

let uu____10102 = (FStar_Util.string_of_int ms_elapsed)
in (FStar_Util.print2 "Checked %s in %s milliseconds\n" uu____10101 uu____10102)))
end
| uu____10103 -> begin
()
end));
r;
)
end))
end)))
in (

let uu____10104 = (FStar_Util.fold_flatten process_one_decl_timed (([]), ([]), (env), ([])) ses)
in (match (uu____10104) with
| (ses1, exports, env1, uu____10152) -> begin
(((FStar_List.rev_append ses1 [])), ((FStar_List.rev_append exports [])), (env1))
end)))))


let check_exports : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  unit = (fun env modul exports -> (

let env1 = (

let uu___108_10189 = env
in {FStar_TypeChecker_Env.solver = uu___108_10189.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___108_10189.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___108_10189.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___108_10189.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___108_10189.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___108_10189.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___108_10189.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___108_10189.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___108_10189.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___108_10189.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___108_10189.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___108_10189.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___108_10189.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___108_10189.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = uu___108_10189.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___108_10189.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___108_10189.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___108_10189.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = true; FStar_TypeChecker_Env.failhard = uu___108_10189.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___108_10189.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___108_10189.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___108_10189.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___108_10189.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___108_10189.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___108_10189.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___108_10189.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___108_10189.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___108_10189.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___108_10189.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___108_10189.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___108_10189.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___108_10189.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___108_10189.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___108_10189.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___108_10189.FStar_TypeChecker_Env.dep_graph})
in (

let check_term = (fun lid univs1 t -> (

let uu____10206 = (FStar_Syntax_Subst.open_univ_vars univs1 t)
in (match (uu____10206) with
| (univs2, t1) -> begin
((

let uu____10214 = (

let uu____10215 = (

let uu____10220 = (FStar_TypeChecker_Env.set_current_module env1 modul.FStar_Syntax_Syntax.name)
in (FStar_TypeChecker_Env.debug uu____10220))
in (FStar_All.pipe_left uu____10215 (FStar_Options.Other ("Exports"))))
in (match (uu____10214) with
| true -> begin
(

let uu____10221 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____10222 = (

let uu____10223 = (FStar_All.pipe_right univs2 (FStar_List.map (fun x -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (x))))))
in (FStar_All.pipe_right uu____10223 (FStar_String.concat ", ")))
in (

let uu____10234 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Checking for export %s <%s> : %s\n" uu____10221 uu____10222 uu____10234))))
end
| uu____10235 -> begin
()
end));
(

let env2 = (FStar_TypeChecker_Env.push_univ_vars env1 univs2)
in (

let uu____10237 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1)
in (FStar_All.pipe_right uu____10237 (fun a239 -> ()))));
)
end)))
in (

let check_term1 = (fun lid univs1 t -> ((

let uu____10263 = (

let uu____10264 = (FStar_Syntax_Print.lid_to_string modul.FStar_Syntax_Syntax.name)
in (

let uu____10265 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Interface of %s violates its abstraction (add a \'private\' qualifier to \'%s\'?)" uu____10264 uu____10265)))
in (FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____10263));
(check_term lid univs1 t);
(FStar_Errors.message_prefix.FStar_Errors.clear_prefix ());
))
in (

let rec check_sigelt = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____10274) -> begin
(

let uu____10283 = (

let uu____10284 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____10284)))
in (match (uu____10283) with
| true -> begin
(FStar_All.pipe_right ses (FStar_List.iter check_sigelt))
end
| uu____10289 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (l, univs1, binders, typ, uu____10294, uu____10295) -> begin
(

let t = (

let uu____10307 = (

let uu____10314 = (

let uu____10315 = (

let uu____10328 = (FStar_Syntax_Syntax.mk_Total typ)
in ((binders), (uu____10328)))
in FStar_Syntax_Syntax.Tm_arrow (uu____10315))
in (FStar_Syntax_Syntax.mk uu____10314))
in (uu____10307 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng))
in (check_term1 l univs1 t))
end
| FStar_Syntax_Syntax.Sig_datacon (l, univs1, t, uu____10345, uu____10346, uu____10347) -> begin
(check_term1 l univs1 t)
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, univs1, t) -> begin
(

let uu____10355 = (

let uu____10356 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____10356)))
in (match (uu____10355) with
| true -> begin
(check_term1 l univs1 t)
end
| uu____10359 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_let ((uu____10360, lbs), uu____10362) -> begin
(

let uu____10371 = (

let uu____10372 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____10372)))
in (match (uu____10371) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (check_term1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp)))))
end
| uu____10381 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs1, binders, comp, flags1) -> begin
(

let uu____10391 = (

let uu____10392 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____10392)))
in (match (uu____10391) with
| true -> begin
(

let arrow1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))) FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng)
in (check_term1 l univs1 arrow1))
end
| uu____10406 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_main (uu____10407) -> begin
()
end
| FStar_Syntax_Syntax.Sig_assume (uu____10408) -> begin
()
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____10415) -> begin
()
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____10416) -> begin
()
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____10417) -> begin
()
end
| FStar_Syntax_Syntax.Sig_splice (uu____10418) -> begin
()
end
| FStar_Syntax_Syntax.Sig_pragma (uu____10425) -> begin
()
end))
in (

let uu____10426 = (FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Parser_Const.prims_lid)
in (match (uu____10426) with
| true -> begin
()
end
| uu____10427 -> begin
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
| FStar_Syntax_Syntax.Projector (l, uu____10521) -> begin
true
end
| uu____10522 -> begin
false
end)) quals))
in (

let vals_of_abstract_inductive = (fun s -> (

let mk_typ_for_abstract_inductive = (fun bs t r -> (match (bs) with
| [] -> begin
t
end
| uu____10549 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs', c) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((((FStar_List.append bs bs')), (c)))) FStar_Pervasives_Native.None r)
end
| uu____10580 -> begin
(

let uu____10581 = (

let uu____10588 = (

let uu____10589 = (

let uu____10602 = (FStar_Syntax_Syntax.mk_Total t)
in ((bs), (uu____10602)))
in FStar_Syntax_Syntax.Tm_arrow (uu____10589))
in (FStar_Syntax_Syntax.mk uu____10588))
in (uu____10581 FStar_Pervasives_Native.None r))
end)
end))
in (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, bs, t, uu____10620, uu____10621) -> begin
(

let s1 = (

let uu___109_10631 = s
in (

let uu____10632 = (

let uu____10633 = (

let uu____10640 = (mk_typ_for_abstract_inductive bs t s.FStar_Syntax_Syntax.sigrng)
in ((lid), (uvs), (uu____10640)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____10633))
in (

let uu____10641 = (

let uu____10644 = (

let uu____10647 = (filter_out_abstract_and_noeq s.FStar_Syntax_Syntax.sigquals)
in (FStar_Syntax_Syntax.New)::uu____10647)
in (FStar_Syntax_Syntax.Assumption)::uu____10644)
in {FStar_Syntax_Syntax.sigel = uu____10632; FStar_Syntax_Syntax.sigrng = uu___109_10631.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu____10641; FStar_Syntax_Syntax.sigmeta = uu___109_10631.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___109_10631.FStar_Syntax_Syntax.sigattrs})))
in (s1)::[])
end
| uu____10650 -> begin
(failwith "Impossible!")
end)))
in (

let val_of_lb = (fun s lid uu____10674 lbdef -> (match (uu____10674) with
| (uvs, t) -> begin
(

let attrs = (

let uu____10685 = (FStar_TypeChecker_Util.must_erase_for_extraction en lbdef)
in (match (uu____10685) with
| true -> begin
(

let uu____10688 = (

let uu____10689 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.must_erase_for_extraction_attr FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_All.pipe_right uu____10689 FStar_Syntax_Syntax.fv_to_tm))
in (uu____10688)::s.FStar_Syntax_Syntax.sigattrs)
end
| uu____10690 -> begin
s.FStar_Syntax_Syntax.sigattrs
end))
in (

let uu___110_10691 = s
in (

let uu____10692 = (

let uu____10695 = (filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals)
in (FStar_Syntax_Syntax.Assumption)::uu____10695)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (uvs), (t))); FStar_Syntax_Syntax.sigrng = uu___110_10691.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu____10692; FStar_Syntax_Syntax.sigmeta = uu___110_10691.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = attrs})))
end))
in (

let should_keep_lbdef = (fun t -> (

let comp_effect_name1 = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
c1.FStar_Syntax_Syntax.effect_name
end
| uu____10711 -> begin
(failwith "Impossible!")
end))
in (

let c_opt = (

let uu____10717 = (FStar_Syntax_Util.is_unit t)
in (match (uu____10717) with
| true -> begin
(

let uu____10722 = (FStar_Syntax_Syntax.mk_Total t)
in FStar_Pervasives_Native.Some (uu____10722))
end
| uu____10723 -> begin
(

let uu____10724 = (

let uu____10725 = (FStar_Syntax_Subst.compress t)
in uu____10725.FStar_Syntax_Syntax.n)
in (match (uu____10724) with
| FStar_Syntax_Syntax.Tm_arrow (uu____10732, c) -> begin
FStar_Pervasives_Native.Some (c)
end
| uu____10752 -> begin
FStar_Pervasives_Native.None
end))
end))
in ((Prims.op_Equality c_opt FStar_Pervasives_Native.None) || (

let c = (FStar_All.pipe_right c_opt FStar_Util.must)
in (

let uu____10775 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (match (uu____10775) with
| true -> begin
(

let uu____10776 = (

let uu____10777 = (FStar_All.pipe_right c FStar_Syntax_Util.comp_result)
in (FStar_All.pipe_right uu____10777 FStar_Syntax_Util.is_unit))
in (not (uu____10776)))
end
| uu____10780 -> begin
(

let uu____10781 = (comp_effect_name1 c)
in (FStar_TypeChecker_Env.is_reifiable_effect en uu____10781))
end)))))))
in (

let extract_sigelt = (fun s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____10792) -> begin
(failwith "Impossible! extract_interface: bare data constructor")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____10811) -> begin
(failwith "Impossible! extract_interface: bare data constructor")
end
| FStar_Syntax_Syntax.Sig_splice (uu____10828) -> begin
(failwith "Impossible! extract_interface: trying to extract splice")
end
| FStar_Syntax_Syntax.Sig_bundle (sigelts, lidents1) -> begin
(match ((is_abstract s.FStar_Syntax_Syntax.sigquals)) with
| true -> begin
(FStar_All.pipe_right sigelts (FStar_List.fold_left (fun sigelts1 s1 -> (match (s1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____10872, uu____10873, uu____10874, uu____10875, uu____10876) -> begin
((

let uu____10886 = (

let uu____10889 = (FStar_ST.op_Bang abstract_inductive_tycons)
in (lid)::uu____10889)
in (FStar_ST.op_Colon_Equals abstract_inductive_tycons uu____10886));
(

let uu____10990 = (vals_of_abstract_inductive s1)
in (FStar_List.append uu____10990 sigelts1));
)
end
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____10994, uu____10995, uu____10996, uu____10997, uu____10998) -> begin
((

let uu____11004 = (

let uu____11007 = (FStar_ST.op_Bang abstract_inductive_datacons)
in (lid)::uu____11007)
in (FStar_ST.op_Colon_Equals abstract_inductive_datacons uu____11004));
sigelts1;
)
end
| uu____11108 -> begin
(failwith "Impossible! extract_interface: Sig_bundle can\'t have anything other than Sig_inductive_typ and Sig_datacon")
end)) []))
end
| uu____11111 -> begin
(s)::[]
end)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) -> begin
(

let uu____11115 = (is_projector_or_discriminator_of_an_abstract_inductive s.FStar_Syntax_Syntax.sigquals)
in (match (uu____11115) with
| true -> begin
[]
end
| uu____11118 -> begin
(match ((is_assume s.FStar_Syntax_Syntax.sigquals)) with
| true -> begin
(

let uu____11121 = (

let uu___111_11122 = s
in (

let uu____11123 = (filter_out_abstract s.FStar_Syntax_Syntax.sigquals)
in {FStar_Syntax_Syntax.sigel = uu___111_11122.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___111_11122.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu____11123; FStar_Syntax_Syntax.sigmeta = uu___111_11122.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___111_11122.FStar_Syntax_Syntax.sigattrs}))
in (uu____11121)::[])
end
| uu____11126 -> begin
[]
end)
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, lids) -> begin
(

let uu____11133 = (is_projector_or_discriminator_of_an_abstract_inductive s.FStar_Syntax_Syntax.sigquals)
in (match (uu____11133) with
| true -> begin
[]
end
| uu____11136 -> begin
(

let uu____11137 = lbs
in (match (uu____11137) with
| (flbs, slbs) -> begin
(

let typs_and_defs = (FStar_All.pipe_right slbs (FStar_List.map (fun lb -> ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (lb.FStar_Syntax_Syntax.lbdef)))))
in (

let is_lemma1 = (FStar_List.existsML (fun uu____11196 -> (match (uu____11196) with
| (uu____11203, t, uu____11205) -> begin
(FStar_All.pipe_right t FStar_Syntax_Util.is_lemma)
end)) typs_and_defs)
in (

let vals = (FStar_List.map2 (fun lid uu____11221 -> (match (uu____11221) with
| (u, t, d) -> begin
(val_of_lb s lid ((u), (t)) d)
end)) lids typs_and_defs)
in (match ((((is_abstract s.FStar_Syntax_Syntax.sigquals) || (is_irreducible1 s.FStar_Syntax_Syntax.sigquals)) || is_lemma1)) with
| true -> begin
vals
end
| uu____11233 -> begin
(

let should_keep_defs = (FStar_List.existsML (fun uu____11245 -> (match (uu____11245) with
| (uu____11252, t, uu____11254) -> begin
(FStar_All.pipe_right t should_keep_lbdef)
end)) typs_and_defs)
in (match (should_keep_defs) with
| true -> begin
(s)::[]
end
| uu____11257 -> begin
vals
end))
end))))
end))
end))
end
| FStar_Syntax_Syntax.Sig_main (t) -> begin
(failwith "Did not anticipate main would arise when extracting interfaces!")
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____11262, uu____11263) -> begin
(

let is_haseq = (FStar_TypeChecker_TcInductive.is_haseq_lid lid)
in (match (is_haseq) with
| true -> begin
(

let is_haseq_of_abstract_inductive = (

let uu____11268 = (FStar_ST.op_Bang abstract_inductive_tycons)
in (FStar_List.existsML (fun l -> (

let uu____11323 = (FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l)
in (FStar_Ident.lid_equals lid uu____11323))) uu____11268))
in (match (is_haseq_of_abstract_inductive) with
| true -> begin
(

let uu____11326 = (

let uu___112_11327 = s
in (

let uu____11328 = (filter_out_abstract s.FStar_Syntax_Syntax.sigquals)
in {FStar_Syntax_Syntax.sigel = uu___112_11327.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___112_11327.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu____11328; FStar_Syntax_Syntax.sigmeta = uu___112_11327.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___112_11327.FStar_Syntax_Syntax.sigattrs}))
in (uu____11326)::[])
end
| uu____11331 -> begin
[]
end))
end
| uu____11332 -> begin
(

let uu____11333 = (

let uu___113_11334 = s
in (

let uu____11335 = (filter_out_abstract s.FStar_Syntax_Syntax.sigquals)
in {FStar_Syntax_Syntax.sigel = uu___113_11334.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___113_11334.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu____11335; FStar_Syntax_Syntax.sigmeta = uu___113_11334.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___113_11334.FStar_Syntax_Syntax.sigattrs}))
in (uu____11333)::[])
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____11338) -> begin
(s)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____11339) -> begin
(s)::[]
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____11340) -> begin
(s)::[]
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____11341) -> begin
(s)::[]
end
| FStar_Syntax_Syntax.Sig_pragma (uu____11354) -> begin
(s)::[]
end))
in (

let uu___114_11355 = m
in (

let uu____11356 = (

let uu____11357 = (FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations (FStar_List.map extract_sigelt))
in (FStar_All.pipe_right uu____11357 FStar_List.flatten))
in {FStar_Syntax_Syntax.name = uu___114_11355.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu____11356; FStar_Syntax_Syntax.exports = uu___114_11355.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = true}))))))))))))))))


let pop_context : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Env.env = (fun env msg -> ((

let uu____11385 = (FStar_Syntax_DsEnv.pop ())
in (FStar_All.pipe_right uu____11385 (fun a240 -> ())));
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

let uu___115_11400 = env1
in {FStar_TypeChecker_Env.solver = uu___115_11400.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___115_11400.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___115_11400.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___115_11400.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___115_11400.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___115_11400.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___115_11400.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___115_11400.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___115_11400.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___115_11400.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___115_11400.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___115_11400.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___115_11400.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___115_11400.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___115_11400.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___115_11400.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___115_11400.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___115_11400.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___115_11400.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___115_11400.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___115_11400.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___115_11400.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___115_11400.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___115_11400.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___115_11400.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___115_11400.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___115_11400.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___115_11400.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___115_11400.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___115_11400.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___115_11400.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___115_11400.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___115_11400.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___115_11400.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___115_11400.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___115_11400.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = dsenv1; FStar_TypeChecker_Env.dep_graph = uu___115_11400.FStar_TypeChecker_Env.dep_graph}))))


let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (

let verify = (FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let action = (match (verify) with
| true -> begin
"Verifying"
end
| uu____11421 -> begin
"Lax-checking"
end)
in (

let label1 = (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____11423 -> begin
"implementation"
end)
in ((

let uu____11425 = (FStar_Options.debug_any ())
in (match (uu____11425) with
| true -> begin
(FStar_Util.print3 "%s %s of %s\n" action label1 modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
end
| uu____11426 -> begin
()
end));
(

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____11428 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let env1 = (

let uu___116_11430 = env
in {FStar_TypeChecker_Env.solver = uu___116_11430.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___116_11430.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___116_11430.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___116_11430.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___116_11430.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___116_11430.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___116_11430.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___116_11430.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___116_11430.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___116_11430.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___116_11430.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___116_11430.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___116_11430.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___116_11430.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___116_11430.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___116_11430.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___116_11430.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = (not (verify)); FStar_TypeChecker_Env.lax = uu___116_11430.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___116_11430.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___116_11430.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___116_11430.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___116_11430.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___116_11430.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___116_11430.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___116_11430.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___116_11430.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___116_11430.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___116_11430.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___116_11430.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___116_11430.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___116_11430.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___116_11430.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___116_11430.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___116_11430.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___116_11430.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___116_11430.FStar_TypeChecker_Env.dep_graph})
in (

let env2 = (FStar_TypeChecker_Env.set_current_module env1 modul.FStar_Syntax_Syntax.name)
in (

let uu____11432 = (tc_decls env2 modul.FStar_Syntax_Syntax.declarations)
in (match (uu____11432) with
| (ses, exports, env3) -> begin
(((

let uu___117_11465 = modul
in {FStar_Syntax_Syntax.name = uu___117_11465.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = uu___117_11465.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___117_11465.FStar_Syntax_Syntax.is_interface})), (exports), (env3))
end)))));
)))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let uu____11493 = (tc_decls env decls)
in (match (uu____11493) with
| (ses, exports, env1) -> begin
(

let modul1 = (

let uu___118_11524 = modul
in {FStar_Syntax_Syntax.name = uu___118_11524.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = uu___118_11524.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___118_11524.FStar_Syntax_Syntax.is_interface})
in ((modul1), (exports), (env1)))
end)))


let rec tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_TypeChecker_Env.env) = (fun env0 m -> (

let msg = (Prims.strcat "Internals for " m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let env01 = (push_context env0 msg)
in (

let uu____11581 = (tc_partial_modul env01 m)
in (match (uu____11581) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul false env modul non_private_decls)
end)))))
and finish_partial_modul : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_TypeChecker_Env.env) = (fun loading_from_cache en m exports -> (

let uu____11619 = (((not (loading_from_cache)) && (FStar_Options.use_extracted_interfaces ())) && (not (m.FStar_Syntax_Syntax.is_interface)))
in (match (uu____11619) with
| true -> begin
(

let modul_iface = (extract_interface en m)
in ((

let uu____11630 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug en) FStar_Options.Low)
in (match (uu____11630) with
| true -> begin
(

let uu____11631 = (

let uu____11632 = (FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____11632) with
| true -> begin
""
end
| uu____11633 -> begin
" (in lax mode) "
end))
in (

let uu____11634 = (

let uu____11635 = (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____11635) with
| true -> begin
(

let uu____11636 = (

let uu____11637 = (FStar_Syntax_Print.modul_to_string m)
in (Prims.strcat uu____11637 "\n"))
in (Prims.strcat "\nfrom: " uu____11636))
end
| uu____11638 -> begin
""
end))
in (

let uu____11639 = (

let uu____11640 = (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____11640) with
| true -> begin
(

let uu____11641 = (

let uu____11642 = (FStar_Syntax_Print.modul_to_string modul_iface)
in (Prims.strcat uu____11642 "\n"))
in (Prims.strcat "\nto: " uu____11641))
end
| uu____11643 -> begin
""
end))
in (FStar_Util.print4 "Extracting and type checking module %s interface%s%s%s\n" m.FStar_Syntax_Syntax.name.FStar_Ident.str uu____11631 uu____11634 uu____11639))))
end
| uu____11644 -> begin
()
end));
(

let en0 = (

let en0 = (pop_context en (Prims.strcat "Ending modul " m.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (

let en01 = (

let uu___119_11648 = en0
in (

let uu____11649 = (

let uu____11662 = (FStar_All.pipe_right en.FStar_TypeChecker_Env.qtbl_name_and_index FStar_Pervasives_Native.fst)
in ((uu____11662), (FStar_Pervasives_Native.None)))
in {FStar_TypeChecker_Env.solver = uu___119_11648.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___119_11648.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___119_11648.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___119_11648.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___119_11648.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___119_11648.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___119_11648.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___119_11648.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___119_11648.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___119_11648.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___119_11648.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___119_11648.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___119_11648.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___119_11648.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___119_11648.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___119_11648.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___119_11648.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___119_11648.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___119_11648.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___119_11648.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___119_11648.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___119_11648.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___119_11648.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___119_11648.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___119_11648.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___119_11648.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___119_11648.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___119_11648.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu____11649; FStar_TypeChecker_Env.normalized_eff_names = uu___119_11648.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___119_11648.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___119_11648.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___119_11648.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___119_11648.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___119_11648.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___119_11648.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___119_11648.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___119_11648.FStar_TypeChecker_Env.dep_graph}))
in (

let uu____11699 = (

let uu____11700 = (FStar_Options.interactive ())
in (not (uu____11700)))
in (match (uu____11699) with
| true -> begin
((

let uu____11702 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right uu____11702 (fun a241 -> ())));
(z3_reset_options en01);
)
end
| uu____11703 -> begin
en01
end))))
in (

let uu____11704 = (tc_modul en0 modul_iface)
in (match (uu____11704) with
| (modul_iface1, must_be_none, env) -> begin
(match ((Prims.op_disEquality must_be_none FStar_Pervasives_Native.None)) with
| true -> begin
(failwith "Impossible! finish_partial_module: expected the second component to be None")
end
| uu____11746 -> begin
(((

let uu___120_11750 = m
in {FStar_Syntax_Syntax.name = uu___120_11750.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu___120_11750.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = modul_iface1.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___120_11750.FStar_Syntax_Syntax.is_interface})), (FStar_Pervasives_Native.Some (modul_iface1)), (env))
end)
end)));
))
end
| uu____11751 -> begin
(

let modul = (

let uu____11753 = (FStar_Options.use_extracted_interfaces ())
in (match (uu____11753) with
| true -> begin
(

let uu___121_11754 = m
in {FStar_Syntax_Syntax.name = uu___121_11754.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu___121_11754.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = m.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.is_interface = uu___121_11754.FStar_Syntax_Syntax.is_interface})
end
| uu____11755 -> begin
(

let uu___122_11756 = m
in {FStar_Syntax_Syntax.name = uu___122_11756.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu___122_11756.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = uu___122_11756.FStar_Syntax_Syntax.is_interface})
end))
in (

let env = (FStar_TypeChecker_Env.finish_module en modul)
in ((

let uu____11759 = (FStar_All.pipe_right env.FStar_TypeChecker_Env.qtbl_name_and_index FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____11759 FStar_Util.smap_clear));
(

let uu____11787 = (((

let uu____11790 = (FStar_Options.lax ())
in (not (uu____11790))) && (

let uu____11792 = (FStar_Options.use_extracted_interfaces ())
in (not (uu____11792)))) && (not (loading_from_cache)))
in (match (uu____11787) with
| true -> begin
(check_exports env modul exports)
end
| uu____11793 -> begin
()
end));
(

let uu____11795 = (pop_context env (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (FStar_All.pipe_right uu____11795 (fun a242 -> ())));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul);
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
(

let uu____11799 = (

let uu____11800 = (FStar_Options.interactive ())
in (not (uu____11800)))
in (match (uu____11799) with
| true -> begin
(

let uu____11801 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right uu____11801 (fun a243 -> ())))
end
| uu____11802 -> begin
()
end));
((modul), (FStar_Pervasives_Native.None), (env));
)))
end)))


let load_checked_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_TypeChecker_Env.env = (fun en m -> (

let env = (FStar_TypeChecker_Env.set_current_module en m.FStar_Syntax_Syntax.name)
in (

let env1 = (

let uu____11817 = (

let uu____11818 = (FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name)
in (Prims.strcat "Internals for " uu____11818))
in (push_context env uu____11817))
in (

let env2 = (FStar_List.fold_left (fun env2 se -> (

let env3 = (FStar_TypeChecker_Env.push_sigelt env2 se)
in (

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in ((FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (

let uu____11837 = (FStar_TypeChecker_Env.try_lookup_lid env3 lid)
in ()))));
env3;
)))) env1 m.FStar_Syntax_Syntax.declarations)
in (

let uu____11848 = (finish_partial_modul true env2 m m.FStar_Syntax_Syntax.exports)
in (match (uu____11848) with
| (uu____11857, uu____11858, env3) -> begin
env3
end))))))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_TypeChecker_Env.env) = (fun env m -> ((

let uu____11883 = (FStar_Options.debug_any ())
in (match (uu____11883) with
| true -> begin
(

let uu____11884 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (match (m.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"i\'face"
end
| uu____11885 -> begin
"module"
end) uu____11884))
end
| uu____11886 -> begin
()
end));
(

let env1 = (

let uu___123_11888 = env
in (

let uu____11889 = (

let uu____11890 = (FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (not (uu____11890)))
in {FStar_TypeChecker_Env.solver = uu___123_11888.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___123_11888.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___123_11888.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___123_11888.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___123_11888.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___123_11888.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___123_11888.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___123_11888.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___123_11888.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___123_11888.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___123_11888.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___123_11888.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___123_11888.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___123_11888.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___123_11888.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___123_11888.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___123_11888.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___123_11888.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___123_11888.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu____11889; FStar_TypeChecker_Env.lax_universes = uu___123_11888.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___123_11888.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___123_11888.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___123_11888.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___123_11888.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___123_11888.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___123_11888.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___123_11888.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___123_11888.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___123_11888.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___123_11888.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___123_11888.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___123_11888.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___123_11888.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___123_11888.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___123_11888.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___123_11888.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___123_11888.FStar_TypeChecker_Env.dep_graph}))
in (

let uu____11891 = (tc_modul env1 m)
in (match (uu____11891) with
| (m1, m_iface_opt, env2) -> begin
((

let uu____11916 = (FStar_Options.dump_module m1.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____11916) with
| true -> begin
(

let uu____11917 = (FStar_Syntax_Print.modul_to_string m1)
in (FStar_Util.print1 "Module after type checking:\n%s\n" uu____11917))
end
| uu____11918 -> begin
()
end));
(

let uu____11920 = ((FStar_Options.dump_module m1.FStar_Syntax_Syntax.name.FStar_Ident.str) && (FStar_Options.debug_at_level m1.FStar_Syntax_Syntax.name.FStar_Ident.str (FStar_Options.Other ("Normalize"))))
in (match (uu____11920) with
| true -> begin
(

let normalize_toplevel_lets = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((b, lbs), ids) -> begin
(

let n1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]))
in (

let update = (fun lb -> (

let uu____11953 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____11953) with
| (univnames1, e) -> begin
(

let uu___124_11960 = lb
in (

let uu____11961 = (

let uu____11964 = (FStar_TypeChecker_Env.push_univ_vars env2 univnames1)
in (n1 uu____11964 e))
in {FStar_Syntax_Syntax.lbname = uu___124_11960.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___124_11960.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___124_11960.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___124_11960.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____11961; FStar_Syntax_Syntax.lbattrs = uu___124_11960.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___124_11960.FStar_Syntax_Syntax.lbpos}))
end)))
in (

let uu___125_11965 = se
in (

let uu____11966 = (

let uu____11967 = (

let uu____11974 = (

let uu____11975 = (FStar_List.map update lbs)
in ((b), (uu____11975)))
in ((uu____11974), (ids)))
in FStar_Syntax_Syntax.Sig_let (uu____11967))
in {FStar_Syntax_Syntax.sigel = uu____11966; FStar_Syntax_Syntax.sigrng = uu___125_11965.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___125_11965.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___125_11965.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___125_11965.FStar_Syntax_Syntax.sigattrs}))))
end
| uu____11982 -> begin
se
end))
in (

let normalized_module = (

let uu___126_11984 = m1
in (

let uu____11985 = (FStar_List.map normalize_toplevel_lets m1.FStar_Syntax_Syntax.declarations)
in {FStar_Syntax_Syntax.name = uu___126_11984.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu____11985; FStar_Syntax_Syntax.exports = uu___126_11984.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___126_11984.FStar_Syntax_Syntax.is_interface}))
in (

let uu____11986 = (FStar_Syntax_Print.modul_to_string normalized_module)
in (FStar_Util.print1 "%s\n" uu____11986))))
end
| uu____11987 -> begin
()
end));
((m1), (m_iface_opt), (env2));
)
end)));
))




