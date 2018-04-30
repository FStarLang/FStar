
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

let check_and_gen' = (fun env3 uu____815 k -> (match (uu____815) with
| (us, t) -> begin
(match (annotated_univ_names) with
| [] -> begin
(check_and_gen env3 t k)
end
| (uu____851)::uu____852 -> begin
(

let uu____855 = (FStar_Syntax_Subst.subst_tscheme open_annotated_univs ((us), (t)))
in (match (uu____855) with
| (us1, t1) -> begin
(

let uu____878 = (FStar_Syntax_Subst.open_univ_vars us1 t1)
in (match (uu____878) with
| (us2, t2) -> begin
(

let uu____893 = (

let uu____894 = (FStar_TypeChecker_Env.push_univ_vars env3 us2)
in (tc_check_trivial_guard uu____894 t2 k))
in (

let uu____895 = (FStar_Syntax_Subst.close_univ_vars us2 t2)
in ((us2), (uu____895))))
end))
end))
end)
end))
in (

let return_wp = (

let expected_k = (

let uu____908 = (

let uu____915 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____920 = (

let uu____927 = (

let uu____932 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____932))
in (uu____927)::[])
in (uu____915)::uu____920))
in (

let uu____945 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow uu____908 uu____945)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.ret_wp expected_k))
in (

let bind_wp = (

let uu____957 = (fresh_effect_signature ())
in (match (uu____957) with
| (b, wp_b) -> begin
(

let a_wp_b = (

let uu____981 = (

let uu____988 = (

let uu____993 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____993))
in (uu____988)::[])
in (

let uu____1002 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____981 uu____1002)))
in (

let expected_k = (

let uu____1008 = (

let uu____1015 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Syntax.t_range)
in (

let uu____1020 = (

let uu____1027 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1032 = (

let uu____1039 = (FStar_Syntax_Syntax.mk_binder b)
in (

let uu____1044 = (

let uu____1051 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____1056 = (

let uu____1063 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (uu____1063)::[])
in (uu____1051)::uu____1056))
in (uu____1039)::uu____1044))
in (uu____1027)::uu____1032))
in (uu____1015)::uu____1020))
in (

let uu____1092 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____1008 uu____1092)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else1 = (

let p = (

let uu____1105 = (

let uu____1108 = (FStar_Ident.range_of_lid ed2.FStar_Syntax_Syntax.mname)
in FStar_Pervasives_Native.Some (uu____1108))
in (

let uu____1109 = (

let uu____1110 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____1110 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.new_bv uu____1105 uu____1109)))
in (

let expected_k = (

let uu____1122 = (

let uu____1129 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1134 = (

let uu____1141 = (FStar_Syntax_Syntax.mk_binder p)
in (

let uu____1146 = (

let uu____1153 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____1158 = (

let uu____1165 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1165)::[])
in (uu____1153)::uu____1158))
in (uu____1141)::uu____1146))
in (uu____1129)::uu____1134))
in (

let uu____1190 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1122 uu____1190)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (

let uu____1205 = (

let uu____1212 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1217 = (

let uu____1224 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1224)::[])
in (uu____1212)::uu____1217))
in (

let uu____1241 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1205 uu____1241)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let uu____1253 = (FStar_Syntax_Util.type_u ())
in (match (uu____1253) with
| (t, uu____1267) -> begin
(

let expected_k = (

let uu____1271 = (

let uu____1278 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1283 = (

let uu____1290 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____1295 = (

let uu____1302 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1302)::[])
in (uu____1290)::uu____1295))
in (uu____1278)::uu____1283))
in (

let uu____1323 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow uu____1271 uu____1323)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (

let uu____1336 = (

let uu____1339 = (FStar_Ident.range_of_lid ed2.FStar_Syntax_Syntax.mname)
in FStar_Pervasives_Native.Some (uu____1339))
in (

let uu____1340 = (

let uu____1341 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____1341 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.new_bv uu____1336 uu____1340)))
in (

let b_wp_a = (

let uu____1353 = (

let uu____1360 = (

let uu____1365 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder uu____1365))
in (uu____1360)::[])
in (

let uu____1374 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1353 uu____1374)))
in (

let expected_k = (

let uu____1380 = (

let uu____1387 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1392 = (

let uu____1399 = (FStar_Syntax_Syntax.mk_binder b)
in (

let uu____1404 = (

let uu____1411 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (uu____1411)::[])
in (uu____1399)::uu____1404))
in (uu____1387)::uu____1392))
in (

let uu____1432 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1380 uu____1432)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (

let uu____1447 = (

let uu____1454 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1459 = (

let uu____1466 = (

let uu____1471 = (

let uu____1472 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____1472 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.null_binder uu____1471))
in (

let uu____1481 = (

let uu____1488 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1488)::[])
in (uu____1466)::uu____1481))
in (uu____1454)::uu____1459))
in (

let uu____1509 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1447 uu____1509)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (

let uu____1524 = (

let uu____1531 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1536 = (

let uu____1543 = (

let uu____1548 = (

let uu____1549 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____1549 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.null_binder uu____1548))
in (

let uu____1558 = (

let uu____1565 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1565)::[])
in (uu____1543)::uu____1558))
in (uu____1531)::uu____1536))
in (

let uu____1586 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1524 uu____1586)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (

let uu____1601 = (

let uu____1608 = (FStar_Syntax_Syntax.mk_binder a)
in (uu____1608)::[])
in (

let uu____1621 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1601 uu____1621)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let uu____1633 = (FStar_Syntax_Util.type_u ())
in (match (uu____1633) with
| (t, uu____1647) -> begin
(

let expected_k = (

let uu____1651 = (

let uu____1658 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1663 = (

let uu____1670 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1670)::[])
in (uu____1658)::uu____1663))
in (

let uu____1687 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow uu____1651 uu____1687)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let uu____1690 = (

let uu____1717 = (

let uu____1718 = (FStar_Syntax_Subst.compress ed2.FStar_Syntax_Syntax.repr)
in uu____1718.FStar_Syntax_Syntax.n)
in (match (uu____1717) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((ed2.FStar_Syntax_Syntax.repr), (ed2.FStar_Syntax_Syntax.bind_repr), (ed2.FStar_Syntax_Syntax.return_repr), (ed2.FStar_Syntax_Syntax.actions))
end
| uu____1765 -> begin
(

let repr = (

let uu____1767 = (FStar_Syntax_Util.type_u ())
in (match (uu____1767) with
| (t, uu____1773) -> begin
(

let expected_k = (

let uu____1777 = (

let uu____1784 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1789 = (

let uu____1796 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1796)::[])
in (uu____1784)::uu____1789))
in (

let uu____1813 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow uu____1777 uu____1813)))
in (tc_check_trivial_guard env2 ed2.FStar_Syntax_Syntax.repr expected_k))
end))
in (

let mk_repr' = (fun t wp -> (

let repr1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env2 repr)
in (

let uu____1830 = (

let uu____1837 = (

let uu____1838 = (

let uu____1853 = (

let uu____1862 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____1869 = (

let uu____1878 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____1878)::[])
in (uu____1862)::uu____1869))
in ((repr1), (uu____1853)))
in FStar_Syntax_Syntax.Tm_app (uu____1838))
in (FStar_Syntax_Syntax.mk uu____1837))
in (uu____1830 FStar_Pervasives_Native.None FStar_Range.dummyRange))))
in (

let mk_repr = (fun a1 wp -> (

let uu____1929 = (FStar_Syntax_Syntax.bv_to_name a1)
in (mk_repr' uu____1929 wp)))
in (

let destruct_repr = (fun t -> (

let uu____1944 = (

let uu____1945 = (FStar_Syntax_Subst.compress t)
in uu____1945.FStar_Syntax_Syntax.n)
in (match (uu____1944) with
| FStar_Syntax_Syntax.Tm_app (uu____1956, ((t1, uu____1958))::((wp, uu____1960))::[]) -> begin
((t1), (wp))
end
| uu____2003 -> begin
(failwith "Unexpected repr type")
end)))
in (

let bind_repr = (

let r = (

let uu____2022 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.range_0 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_All.pipe_right uu____2022 FStar_Syntax_Syntax.fv_to_tm))
in (

let uu____2023 = (fresh_effect_signature ())
in (match (uu____2023) with
| (b, wp_b) -> begin
(

let a_wp_b = (

let uu____2047 = (

let uu____2054 = (

let uu____2059 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____2059))
in (uu____2054)::[])
in (

let uu____2068 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____2047 uu____2068)))
in (

let wp_f = (FStar_Syntax_Syntax.gen_bv "wp_f" FStar_Pervasives_Native.None wp_a)
in (

let wp_g = (FStar_Syntax_Syntax.gen_bv "wp_g" FStar_Pervasives_Native.None a_wp_b)
in (

let x_a = (

let uu____2074 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" FStar_Pervasives_Native.None uu____2074))
in (

let wp_g_x = (

let uu____2078 = (

let uu____2083 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (

let uu____2084 = (

let uu____2085 = (

let uu____2092 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____2092))
in (uu____2085)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____2083 uu____2084)))
in (uu____2078 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let res = (

let wp = (

let uu____2119 = (

let uu____2124 = (

let uu____2125 = (FStar_TypeChecker_Env.inst_tscheme bind_wp)
in (FStar_All.pipe_right uu____2125 FStar_Pervasives_Native.snd))
in (

let uu____2134 = (

let uu____2135 = (

let uu____2138 = (

let uu____2141 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____2142 = (

let uu____2145 = (FStar_Syntax_Syntax.bv_to_name b)
in (

let uu____2146 = (

let uu____2149 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (

let uu____2150 = (

let uu____2153 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (uu____2153)::[])
in (uu____2149)::uu____2150))
in (uu____2145)::uu____2146))
in (uu____2141)::uu____2142))
in (r)::uu____2138)
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____2135))
in (FStar_Syntax_Syntax.mk_Tm_app uu____2124 uu____2134)))
in (uu____2119 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (mk_repr b wp))
in (

let maybe_range_arg = (

let uu____2169 = (FStar_Util.for_some (FStar_Syntax_Util.attr_eq FStar_Syntax_Util.dm4f_bind_range_attr) ed2.FStar_Syntax_Syntax.eff_attrs)
in (match (uu____2169) with
| true -> begin
(

let uu____2176 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Syntax.t_range)
in (

let uu____2181 = (

let uu____2188 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Syntax.t_range)
in (uu____2188)::[])
in (uu____2176)::uu____2181))
end
| uu____2205 -> begin
[]
end))
in (

let expected_k = (

let uu____2213 = (

let uu____2220 = (

let uu____2227 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____2232 = (

let uu____2239 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____2239)::[])
in (uu____2227)::uu____2232))
in (

let uu____2256 = (

let uu____2263 = (

let uu____2270 = (FStar_Syntax_Syntax.mk_binder wp_f)
in (

let uu____2275 = (

let uu____2282 = (

let uu____2287 = (

let uu____2288 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (mk_repr a uu____2288))
in (FStar_Syntax_Syntax.null_binder uu____2287))
in (

let uu____2289 = (

let uu____2296 = (FStar_Syntax_Syntax.mk_binder wp_g)
in (

let uu____2301 = (

let uu____2308 = (

let uu____2313 = (

let uu____2314 = (

let uu____2321 = (FStar_Syntax_Syntax.mk_binder x_a)
in (uu____2321)::[])
in (

let uu____2334 = (

let uu____2337 = (mk_repr b wp_g_x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____2337))
in (FStar_Syntax_Util.arrow uu____2314 uu____2334)))
in (FStar_Syntax_Syntax.null_binder uu____2313))
in (uu____2308)::[])
in (uu____2296)::uu____2301))
in (uu____2282)::uu____2289))
in (uu____2270)::uu____2275))
in (FStar_List.append maybe_range_arg uu____2263))
in (FStar_List.append uu____2220 uu____2256)))
in (

let uu____2368 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow uu____2213 uu____2368)))
in (

let uu____2371 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env2 expected_k)
in (match (uu____2371) with
| (expected_k1, uu____2387, uu____2388) -> begin
(

let env3 = (FStar_TypeChecker_Env.set_range env2 (FStar_Pervasives_Native.snd ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos)
in (

let env4 = (

let uu___70_2395 = env3
in {FStar_TypeChecker_Env.solver = uu___70_2395.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___70_2395.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___70_2395.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___70_2395.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___70_2395.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___70_2395.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___70_2395.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___70_2395.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___70_2395.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___70_2395.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___70_2395.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___70_2395.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___70_2395.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___70_2395.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___70_2395.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___70_2395.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___70_2395.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___70_2395.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___70_2395.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___70_2395.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___70_2395.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___70_2395.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___70_2395.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___70_2395.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___70_2395.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___70_2395.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___70_2395.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___70_2395.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___70_2395.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___70_2395.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___70_2395.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___70_2395.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___70_2395.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___70_2395.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___70_2395.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___70_2395.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___70_2395.FStar_TypeChecker_Env.dep_graph})
in (

let br = (check_and_gen' env4 ed2.FStar_Syntax_Syntax.bind_repr expected_k1)
in br)))
end))))))))))
end)))
in (

let return_repr = (

let x_a = (

let uu____2415 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" FStar_Pervasives_Native.None uu____2415))
in (

let res = (

let wp = (

let uu____2422 = (

let uu____2427 = (

let uu____2428 = (FStar_TypeChecker_Env.inst_tscheme return_wp)
in (FStar_All.pipe_right uu____2428 FStar_Pervasives_Native.snd))
in (

let uu____2437 = (

let uu____2438 = (

let uu____2441 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____2442 = (

let uu____2445 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (uu____2445)::[])
in (uu____2441)::uu____2442))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____2438))
in (FStar_Syntax_Syntax.mk_Tm_app uu____2427 uu____2437)))
in (uu____2422 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (mk_repr a wp))
in (

let expected_k = (

let uu____2457 = (

let uu____2464 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____2469 = (

let uu____2476 = (FStar_Syntax_Syntax.mk_binder x_a)
in (uu____2476)::[])
in (uu____2464)::uu____2469))
in (

let uu____2493 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow uu____2457 uu____2493)))
in (

let uu____2496 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env2 expected_k)
in (match (uu____2496) with
| (expected_k1, uu____2512, uu____2513) -> begin
(

let env3 = (FStar_TypeChecker_Env.set_range env2 (FStar_Pervasives_Native.snd ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos)
in (

let uu____2519 = (check_and_gen' env3 ed2.FStar_Syntax_Syntax.return_repr expected_k1)
in (match (uu____2519) with
| (univs1, repr1) -> begin
(match (univs1) with
| [] -> begin
(([]), (repr1))
end
| uu____2558 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn), ("Unexpected universe-polymorphic return for effect")) repr1.FStar_Syntax_Syntax.pos)
end)
end)))
end)))))
in (

let actions = (

let check_action = (fun act -> (

let uu____2579 = (match ((Prims.op_Equality act.FStar_Syntax_Syntax.action_univs [])) with
| true -> begin
((env2), (act))
end
| uu____2590 -> begin
(

let uu____2591 = (FStar_Syntax_Subst.univ_var_opening act.FStar_Syntax_Syntax.action_univs)
in (match (uu____2591) with
| (usubst, uvs) -> begin
(

let uu____2614 = (FStar_TypeChecker_Env.push_univ_vars env2 uvs)
in (

let uu____2615 = (

let uu___71_2616 = act
in (

let uu____2617 = (FStar_Syntax_Subst.subst_binders usubst act.FStar_Syntax_Syntax.action_params)
in (

let uu____2618 = (FStar_Syntax_Subst.subst usubst act.FStar_Syntax_Syntax.action_defn)
in (

let uu____2619 = (FStar_Syntax_Subst.subst usubst act.FStar_Syntax_Syntax.action_typ)
in {FStar_Syntax_Syntax.action_name = uu___71_2616.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___71_2616.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uvs; FStar_Syntax_Syntax.action_params = uu____2617; FStar_Syntax_Syntax.action_defn = uu____2618; FStar_Syntax_Syntax.action_typ = uu____2619}))))
in ((uu____2614), (uu____2615))))
end))
end)
in (match (uu____2579) with
| (env3, act1) -> begin
(

let act_typ = (

let uu____2623 = (

let uu____2624 = (FStar_Syntax_Subst.compress act1.FStar_Syntax_Syntax.action_typ)
in uu____2624.FStar_Syntax_Syntax.n)
in (match (uu____2623) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let c1 = (FStar_Syntax_Util.comp_to_comp_typ c)
in (

let uu____2646 = (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name ed2.FStar_Syntax_Syntax.mname)
in (match (uu____2646) with
| true -> begin
(

let uu____2647 = (

let uu____2650 = (

let uu____2651 = (

let uu____2652 = (FStar_List.hd c1.FStar_Syntax_Syntax.effect_args)
in (FStar_Pervasives_Native.fst uu____2652))
in (mk_repr' c1.FStar_Syntax_Syntax.result_typ uu____2651))
in (FStar_Syntax_Syntax.mk_Total uu____2650))
in (FStar_Syntax_Util.arrow bs uu____2647))
end
| uu____2667 -> begin
act1.FStar_Syntax_Syntax.action_typ
end)))
end
| uu____2668 -> begin
act1.FStar_Syntax_Syntax.action_typ
end))
in (

let uu____2669 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env3 act_typ)
in (match (uu____2669) with
| (act_typ1, uu____2677, g_t) -> begin
(

let env' = (

let uu___72_2680 = (FStar_TypeChecker_Env.set_expected_typ env3 act_typ1)
in {FStar_TypeChecker_Env.solver = uu___72_2680.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___72_2680.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___72_2680.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___72_2680.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___72_2680.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___72_2680.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___72_2680.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___72_2680.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___72_2680.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___72_2680.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = uu___72_2680.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___72_2680.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___72_2680.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___72_2680.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___72_2680.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___72_2680.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___72_2680.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___72_2680.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___72_2680.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___72_2680.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___72_2680.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___72_2680.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___72_2680.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___72_2680.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___72_2680.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___72_2680.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___72_2680.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___72_2680.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___72_2680.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___72_2680.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___72_2680.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___72_2680.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___72_2680.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___72_2680.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___72_2680.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___72_2680.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___72_2680.FStar_TypeChecker_Env.dep_graph})
in ((

let uu____2682 = (FStar_TypeChecker_Env.debug env3 (FStar_Options.Other ("ED")))
in (match (uu____2682) with
| true -> begin
(

let uu____2683 = (FStar_Ident.text_of_lid act1.FStar_Syntax_Syntax.action_name)
in (

let uu____2684 = (FStar_Syntax_Print.term_to_string act1.FStar_Syntax_Syntax.action_defn)
in (

let uu____2685 = (FStar_Syntax_Print.term_to_string act_typ1)
in (FStar_Util.print3 "Checking action %s:\n[definition]: %s\n[cps\'d type]: %s\n" uu____2683 uu____2684 uu____2685))))
end
| uu____2686 -> begin
()
end));
(

let uu____2687 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' act1.FStar_Syntax_Syntax.action_defn)
in (match (uu____2687) with
| (act_defn, uu____2695, g_a) -> begin
(

let act_defn1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env3 act_defn)
in (

let act_typ2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::[]) env3 act_typ1)
in (

let uu____2699 = (

let act_typ3 = (FStar_Syntax_Subst.compress act_typ2)
in (match (act_typ3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____2727 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____2727) with
| (bs1, uu____2737) -> begin
(

let res = (mk_repr' FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun)
in (

let k = (

let uu____2744 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs1 uu____2744))
in (

let uu____2747 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env3 k)
in (match (uu____2747) with
| (k1, uu____2759, g) -> begin
((k1), (g))
end))))
end))
end
| uu____2761 -> begin
(

let uu____2762 = (

let uu____2767 = (

let uu____2768 = (FStar_Syntax_Print.term_to_string act_typ3)
in (

let uu____2769 = (FStar_Syntax_Print.tag_of_term act_typ3)
in (FStar_Util.format2 "Actions must have function types (not: %s, a.k.a. %s)" uu____2768 uu____2769)))
in ((FStar_Errors.Fatal_ActionMustHaveFunctionType), (uu____2767)))
in (FStar_Errors.raise_error uu____2762 act_defn1.FStar_Syntax_Syntax.pos))
end))
in (match (uu____2699) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env3 act_typ2 expected_k)
in ((

let uu____2778 = (

let uu____2779 = (

let uu____2780 = (FStar_TypeChecker_Rel.conj_guard g_t g)
in (FStar_TypeChecker_Rel.conj_guard g_k uu____2780))
in (FStar_TypeChecker_Rel.conj_guard g_a uu____2779))
in (FStar_TypeChecker_Rel.force_trivial_guard env3 uu____2778));
(

let act_typ3 = (

let uu____2782 = (

let uu____2783 = (FStar_Syntax_Subst.compress expected_k)
in uu____2783.FStar_Syntax_Syntax.n)
in (match (uu____2782) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____2804 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____2804) with
| (bs1, c1) -> begin
(

let uu____2811 = (destruct_repr (FStar_Syntax_Util.comp_result c1))
in (match (uu____2811) with
| (a1, wp) -> begin
(

let c2 = (

let uu____2831 = (

let uu____2832 = (env3.FStar_TypeChecker_Env.universe_of env3 a1)
in (uu____2832)::[])
in (

let uu____2833 = (

let uu____2842 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____2842)::[])
in {FStar_Syntax_Syntax.comp_univs = uu____2831; FStar_Syntax_Syntax.effect_name = ed2.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a1; FStar_Syntax_Syntax.effect_args = uu____2833; FStar_Syntax_Syntax.flags = []}))
in (

let uu____2861 = (FStar_Syntax_Syntax.mk_Comp c2)
in (FStar_Syntax_Util.arrow bs1 uu____2861)))
end))
end))
end
| uu____2864 -> begin
(failwith "Impossible (expected_k is an arrow)")
end))
in (

let uu____2865 = (match ((Prims.op_Equality act1.FStar_Syntax_Syntax.action_univs [])) with
| true -> begin
(FStar_TypeChecker_Util.generalize_universes env3 act_defn1)
end
| uu____2884 -> begin
(

let uu____2885 = (FStar_Syntax_Subst.close_univ_vars act1.FStar_Syntax_Syntax.action_univs act_defn1)
in ((act1.FStar_Syntax_Syntax.action_univs), (uu____2885)))
end)
in (match (uu____2865) with
| (univs1, act_defn2) -> begin
(

let act_typ4 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env3 act_typ3)
in (

let act_typ5 = (FStar_Syntax_Subst.close_univ_vars univs1 act_typ4)
in (

let uu___73_2898 = act1
in {FStar_Syntax_Syntax.action_name = uu___73_2898.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___73_2898.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs1; FStar_Syntax_Syntax.action_params = uu___73_2898.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = act_defn2; FStar_Syntax_Syntax.action_typ = act_typ5})))
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
in (match (uu____1690) with
| (repr, bind_repr, return_repr, actions) -> begin
(

let t0 = (

let uu____2964 = (FStar_Syntax_Syntax.mk_Total ed2.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed2.FStar_Syntax_Syntax.binders uu____2964))
in (

let uu____2967 = (

let uu____2976 = (FStar_TypeChecker_Util.generalize_universes env0 t0)
in (match (uu____2976) with
| (gen_univs, t) -> begin
(match (annotated_univ_names) with
| [] -> begin
((gen_univs), (t))
end
| uu____3007 -> begin
(

let uu____3010 = ((Prims.op_Equality (FStar_List.length gen_univs) (FStar_List.length annotated_univ_names)) && (FStar_List.forall2 (fun u1 u2 -> (

let uu____3016 = (FStar_Syntax_Syntax.order_univ_name u1 u2)
in (Prims.op_Equality uu____3016 (Prims.parse_int "0")))) gen_univs annotated_univ_names))
in (match (uu____3010) with
| true -> begin
((gen_univs), (t))
end
| uu____3029 -> begin
(

let uu____3030 = (

let uu____3035 = (

let uu____3036 = (FStar_Util.string_of_int (FStar_List.length annotated_univ_names))
in (

let uu____3037 = (FStar_Util.string_of_int (FStar_List.length gen_univs))
in (FStar_Util.format2 "Expected an effect definition with %s universes; but found %s" uu____3036 uu____3037)))
in ((FStar_Errors.Fatal_UnexpectedNumberOfUniverse), (uu____3035)))
in (FStar_Errors.raise_error uu____3030 ed2.FStar_Syntax_Syntax.signature.FStar_Syntax_Syntax.pos))
end))
end)
end))
in (match (uu____2967) with
| (univs1, t) -> begin
(

let signature1 = (

let uu____3057 = (

let uu____3068 = (

let uu____3069 = (FStar_Syntax_Subst.compress t)
in uu____3069.FStar_Syntax_Syntax.n)
in ((effect_params), (uu____3068)))
in (match (uu____3057) with
| ([], uu____3078) -> begin
t
end
| (uu____3089, FStar_Syntax_Syntax.Tm_arrow (uu____3090, c)) -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____3120 -> begin
(failwith "Impossible : t is an arrow")
end))
in (

let close1 = (fun n1 ts -> (

let ts1 = (

let uu____3149 = (FStar_Syntax_Subst.close_tscheme effect_params ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs1 uu____3149))
in (

let m = (FStar_List.length (FStar_Pervasives_Native.fst ts1))
in ((

let uu____3156 = (((n1 >= (Prims.parse_int "0")) && (

let uu____3164 = (FStar_Syntax_Util.is_unknown (FStar_Pervasives_Native.snd ts1))
in (not (uu____3164)))) && (Prims.op_disEquality m n1))
in (match (uu____3156) with
| true -> begin
(

let error = (match ((m < n1)) with
| true -> begin
"not universe-polymorphic enough"
end
| uu____3188 -> begin
"too universe-polymorphic"
end)
in (

let err_msg = (

let uu____3190 = (FStar_Util.string_of_int m)
in (

let uu____3197 = (FStar_Util.string_of_int n1)
in (

let uu____3204 = (FStar_Syntax_Print.tscheme_to_string ts1)
in (FStar_Util.format4 "The effect combinator is %s (m,n=%s,%s) (%s)" error uu____3190 uu____3197 uu____3204))))
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_MismatchUniversePolymorphic), (err_msg)) (FStar_Pervasives_Native.snd ts1).FStar_Syntax_Syntax.pos)))
end
| uu____3209 -> begin
()
end));
ts1;
))))
in (

let close_action = (fun act -> (

let uu____3216 = (close1 (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_defn)))
in (match (uu____3216) with
| (univs2, defn) -> begin
(

let uu____3231 = (close1 (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_typ)))
in (match (uu____3231) with
| (univs', typ) -> begin
(

let uu___74_3247 = act
in {FStar_Syntax_Syntax.action_name = uu___74_3247.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___74_3247.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs2; FStar_Syntax_Syntax.action_params = uu___74_3247.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = defn; FStar_Syntax_Syntax.action_typ = typ})
end))
end)))
in (

let ed3 = (

let uu___75_3250 = ed2
in (

let uu____3251 = (close1 (Prims.parse_int "0") return_wp)
in (

let uu____3252 = (close1 (Prims.parse_int "1") bind_wp)
in (

let uu____3253 = (close1 (Prims.parse_int "0") if_then_else1)
in (

let uu____3254 = (close1 (Prims.parse_int "0") ite_wp)
in (

let uu____3255 = (close1 (Prims.parse_int "0") stronger)
in (

let uu____3256 = (close1 (Prims.parse_int "1") close_wp)
in (

let uu____3257 = (close1 (Prims.parse_int "0") assert_p)
in (

let uu____3258 = (close1 (Prims.parse_int "0") assume_p)
in (

let uu____3259 = (close1 (Prims.parse_int "0") null_wp)
in (

let uu____3260 = (close1 (Prims.parse_int "0") trivial_wp)
in (

let uu____3261 = (

let uu____3262 = (close1 (Prims.parse_int "0") (([]), (repr)))
in (FStar_Pervasives_Native.snd uu____3262))
in (

let uu____3279 = (close1 (Prims.parse_int "0") return_repr)
in (

let uu____3280 = (close1 (Prims.parse_int "1") bind_repr)
in (

let uu____3281 = (FStar_List.map close_action actions)
in {FStar_Syntax_Syntax.cattributes = uu___75_3250.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___75_3250.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs1; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature1; FStar_Syntax_Syntax.ret_wp = uu____3251; FStar_Syntax_Syntax.bind_wp = uu____3252; FStar_Syntax_Syntax.if_then_else = uu____3253; FStar_Syntax_Syntax.ite_wp = uu____3254; FStar_Syntax_Syntax.stronger = uu____3255; FStar_Syntax_Syntax.close_wp = uu____3256; FStar_Syntax_Syntax.assert_p = uu____3257; FStar_Syntax_Syntax.assume_p = uu____3258; FStar_Syntax_Syntax.null_wp = uu____3259; FStar_Syntax_Syntax.trivial = uu____3260; FStar_Syntax_Syntax.repr = uu____3261; FStar_Syntax_Syntax.return_repr = uu____3279; FStar_Syntax_Syntax.bind_repr = uu____3280; FStar_Syntax_Syntax.actions = uu____3281; FStar_Syntax_Syntax.eff_attrs = uu___75_3250.FStar_Syntax_Syntax.eff_attrs})))))))))))))))
in ((

let uu____3285 = ((FStar_TypeChecker_Env.debug env2 FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("ED"))))
in (match (uu____3285) with
| true -> begin
(

let uu____3286 = (FStar_Syntax_Print.eff_decl_to_string false ed3)
in (FStar_Util.print_string uu____3286))
end
| uu____3287 -> begin
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

let uu____3308 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____3308) with
| (effect_binders_un, signature_un) -> begin
(

let uu____3325 = (FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un)
in (match (uu____3325) with
| (effect_binders, env1, uu____3344) -> begin
(

let uu____3345 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un)
in (match (uu____3345) with
| (signature, uu____3361) -> begin
(

let raise_error1 = (fun uu____3376 -> (match (uu____3376) with
| (e, err_msg) -> begin
(FStar_Errors.raise_error ((e), (err_msg)) signature.FStar_Syntax_Syntax.pos)
end))
in (

let effect_binders1 = (FStar_List.map (fun uu____3402 -> (match (uu____3402) with
| (bv, qual) -> begin
(

let uu____3413 = (

let uu___76_3414 = bv
in (

let uu____3415 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env1 bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___76_3414.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___76_3414.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3415}))
in ((uu____3413), (qual)))
end)) effect_binders)
in (

let uu____3418 = (

let uu____3425 = (

let uu____3426 = (FStar_Syntax_Subst.compress signature_un)
in uu____3426.FStar_Syntax_Syntax.n)
in (match (uu____3425) with
| FStar_Syntax_Syntax.Tm_arrow (((a, uu____3436))::[], effect_marker) -> begin
((a), (effect_marker))
end
| uu____3458 -> begin
(raise_error1 ((FStar_Errors.Fatal_BadSignatureShape), ("bad shape for effect-for-free signature")))
end))
in (match (uu____3418) with
| (a, effect_marker) -> begin
(

let a1 = (

let uu____3482 = (FStar_Syntax_Syntax.is_null_bv a)
in (match (uu____3482) with
| true -> begin
(

let uu____3483 = (

let uu____3486 = (FStar_Syntax_Syntax.range_of_bv a)
in FStar_Pervasives_Native.Some (uu____3486))
in (FStar_Syntax_Syntax.gen_bv "a" uu____3483 a.FStar_Syntax_Syntax.sort))
end
| uu____3487 -> begin
a
end))
in (

let open_and_check = (fun env2 other_binders t -> (

let subst1 = (FStar_Syntax_Subst.opening_of_binders (FStar_List.append effect_binders1 other_binders))
in (

let t1 = (FStar_Syntax_Subst.subst subst1 t)
in (

let uu____3526 = (FStar_TypeChecker_TcTerm.tc_term env2 t1)
in (match (uu____3526) with
| (t2, comp, uu____3539) -> begin
((t2), (comp))
end)))))
in (

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None signature.FStar_Syntax_Syntax.pos))
in (

let uu____3548 = (open_and_check env1 [] ed.FStar_Syntax_Syntax.repr)
in (match (uu____3548) with
| (repr, _comp) -> begin
((

let uu____3570 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____3570) with
| true -> begin
(

let uu____3571 = (FStar_Syntax_Print.term_to_string repr)
in (FStar_Util.print1 "Representation is: %s\n" uu____3571))
end
| uu____3572 -> begin
()
end));
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env1 (FStar_TypeChecker_TcTerm.tc_constant env1 FStar_Range.dummyRange))
in (

let wp_type = (FStar_TypeChecker_DMFF.star_type dmff_env repr)
in (

let uu____3575 = (recheck_debug "*" env1 wp_type)
in (

let wp_a = (

let uu____3577 = (

let uu____3578 = (

let uu____3579 = (

let uu____3594 = (

let uu____3603 = (

let uu____3610 = (FStar_Syntax_Syntax.bv_to_name a1)
in (

let uu____3613 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____3610), (uu____3613))))
in (uu____3603)::[])
in ((wp_type), (uu____3594)))
in FStar_Syntax_Syntax.Tm_app (uu____3579))
in (mk1 uu____3578))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env1 uu____3577))
in (

let effect_signature = (

let binders = (

let uu____3648 = (

let uu____3653 = (FStar_Syntax_Syntax.as_implicit false)
in ((a1), (uu____3653)))
in (

let uu____3654 = (

let uu____3661 = (

let uu____3666 = (FStar_Syntax_Syntax.gen_bv "dijkstra_wp" FStar_Pervasives_Native.None wp_a)
in (FStar_All.pipe_right uu____3666 FStar_Syntax_Syntax.mk_binder))
in (uu____3661)::[])
in (uu____3648)::uu____3654))
in (

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in (mk1 (FStar_Syntax_Syntax.Tm_arrow (((binders1), (effect_marker)))))))
in (

let uu____3692 = (recheck_debug "turned into the effect signature" env1 effect_signature)
in (

let sigelts = (FStar_Util.mk_ref [])
in (

let mk_lid = (fun name -> (FStar_Syntax_Util.dm4f_lid ed name))
in (

let elaborate_and_star = (fun dmff_env1 other_binders item -> (

let env2 = (FStar_TypeChecker_DMFF.get_env dmff_env1)
in (

let uu____3755 = item
in (match (uu____3755) with
| (u_item, item1) -> begin
(

let uu____3776 = (open_and_check env2 other_binders item1)
in (match (uu____3776) with
| (item2, item_comp) -> begin
((

let uu____3792 = (

let uu____3793 = (FStar_Syntax_Util.is_total_lcomp item_comp)
in (not (uu____3793)))
in (match (uu____3792) with
| true -> begin
(

let uu____3794 = (

let uu____3799 = (

let uu____3800 = (FStar_Syntax_Print.term_to_string item2)
in (

let uu____3801 = (FStar_Syntax_Print.lcomp_to_string item_comp)
in (FStar_Util.format2 "Computation for [%s] is not total : %s !" uu____3800 uu____3801)))
in ((FStar_Errors.Fatal_ComputationNotTotal), (uu____3799)))
in (FStar_Errors.raise_err uu____3794))
end
| uu____3802 -> begin
()
end));
(

let uu____3803 = (FStar_TypeChecker_DMFF.star_expr dmff_env1 item2)
in (match (uu____3803) with
| (item_t, item_wp, item_elab) -> begin
(

let uu____3821 = (recheck_debug "*" env2 item_wp)
in (

let uu____3822 = (recheck_debug "_" env2 item_elab)
in ((dmff_env1), (item_t), (item_wp), (item_elab))))
end));
)
end))
end))))
in (

let uu____3823 = (elaborate_and_star dmff_env [] ed.FStar_Syntax_Syntax.bind_repr)
in (match (uu____3823) with
| (dmff_env1, uu____3847, bind_wp, bind_elab) -> begin
(

let uu____3850 = (elaborate_and_star dmff_env1 [] ed.FStar_Syntax_Syntax.return_repr)
in (match (uu____3850) with
| (dmff_env2, uu____3874, return_wp, return_elab) -> begin
(

let rc_gtot = {FStar_Syntax_Syntax.residual_effect = FStar_Parser_Const.effect_GTot_lid; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.None; FStar_Syntax_Syntax.residual_flags = []}
in (

let lift_from_pure_wp = (

let uu____3883 = (

let uu____3884 = (FStar_Syntax_Subst.compress return_wp)
in uu____3884.FStar_Syntax_Syntax.n)
in (match (uu____3883) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(

let uu____3930 = (

let uu____3945 = (

let uu____3950 = (FStar_Syntax_Util.abs bs body FStar_Pervasives_Native.None)
in (FStar_Syntax_Subst.open_term ((b1)::(b2)::[]) uu____3950))
in (match (uu____3945) with
| ((b11)::(b21)::[], body1) -> begin
((b11), (b21), (body1))
end
| uu____4008 -> begin
(failwith "Impossible : open_term not preserving binders arity")
end))
in (match (uu____3930) with
| (b11, b21, body1) -> begin
(

let env0 = (

let uu____4049 = (FStar_TypeChecker_DMFF.get_env dmff_env2)
in (FStar_TypeChecker_Env.push_binders uu____4049 ((b11)::(b21)::[])))
in (

let wp_b1 = (

let raw_wp_b1 = (

let uu____4066 = (

let uu____4067 = (

let uu____4082 = (

let uu____4091 = (

let uu____4098 = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst b11))
in (

let uu____4101 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____4098), (uu____4101))))
in (uu____4091)::[])
in ((wp_type), (uu____4082)))
in FStar_Syntax_Syntax.Tm_app (uu____4067))
in (mk1 uu____4066))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env0 raw_wp_b1))
in (

let uu____4126 = (

let uu____4135 = (

let uu____4136 = (FStar_Syntax_Util.unascribe wp_b1)
in (FStar_TypeChecker_Normalize.eta_expand_with_type env0 body1 uu____4136))
in (FStar_All.pipe_left FStar_Syntax_Util.abs_formals uu____4135))
in (match (uu____4126) with
| (bs1, body2, what') -> begin
(

let fail1 = (fun uu____4159 -> (

let error_msg = (

let uu____4161 = (FStar_Syntax_Print.term_to_string body2)
in (

let uu____4162 = (match (what') with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (rc) -> begin
(FStar_Ident.text_of_lid rc.FStar_Syntax_Syntax.residual_effect)
end)
in (FStar_Util.format2 "The body of return_wp (%s) should be of type Type0 but is of type %s" uu____4161 uu____4162)))
in (raise_error1 ((FStar_Errors.Fatal_WrongBodyTypeForReturnWP), (error_msg)))))
in ((match (what') with
| FStar_Pervasives_Native.None -> begin
(fail1 ())
end
| FStar_Pervasives_Native.Some (rc) -> begin
((

let uu____4167 = (

let uu____4168 = (FStar_Syntax_Util.is_pure_effect rc.FStar_Syntax_Syntax.residual_effect)
in (not (uu____4168)))
in (match (uu____4167) with
| true -> begin
(fail1 ())
end
| uu____4169 -> begin
()
end));
(

let uu____4170 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun rt -> (

let g_opt = (FStar_TypeChecker_Rel.try_teq true env1 rt FStar_Syntax_Util.ktype0)
in (match (g_opt) with
| FStar_Pervasives_Native.Some (g') -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env1 g')
end
| FStar_Pervasives_Native.None -> begin
(fail1 ())
end))))
in (FStar_All.pipe_right uu____4170 (fun a238 -> ())));
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

let uu____4195 = (

let uu____4200 = (FStar_Syntax_Syntax.bv_to_name wp)
in (

let uu____4201 = (

let uu____4202 = (

let uu____4209 = (FStar_Syntax_Util.abs ((b21)::[]) body2 what')
in ((uu____4209), (FStar_Pervasives_Native.None)))
in (uu____4202)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____4200 uu____4201)))
in (uu____4195 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let uu____4236 = (

let uu____4237 = (

let uu____4244 = (FStar_Syntax_Syntax.mk_binder wp)
in (uu____4244)::[])
in (b11)::uu____4237)
in (

let uu____4261 = (FStar_Syntax_Util.abs bs1 body3 what)
in (FStar_Syntax_Util.abs uu____4236 uu____4261 (FStar_Pervasives_Native.Some (rc_gtot)))))));
))
end))))
end))
end
| uu____4264 -> begin
(raise_error1 ((FStar_Errors.Fatal_UnexpectedReturnShape), ("unexpected shape for return")))
end))
in (

let return_wp1 = (

let uu____4270 = (

let uu____4271 = (FStar_Syntax_Subst.compress return_wp)
in uu____4271.FStar_Syntax_Syntax.n)
in (match (uu____4270) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(

let uu____4317 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs ((b1)::(b2)::[]) uu____4317 (FStar_Pervasives_Native.Some (rc_gtot))))
end
| uu____4332 -> begin
(raise_error1 ((FStar_Errors.Fatal_UnexpectedReturnShape), ("unexpected shape for return")))
end))
in (

let bind_wp1 = (

let uu____4338 = (

let uu____4339 = (FStar_Syntax_Subst.compress bind_wp)
in uu____4339.FStar_Syntax_Syntax.n)
in (match (uu____4338) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let r = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.range_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let uu____4368 = (

let uu____4369 = (

let uu____4376 = (

let uu____4381 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (r)))
in (FStar_Syntax_Syntax.null_binder uu____4381))
in (uu____4376)::[])
in (FStar_List.append uu____4369 binders))
in (FStar_Syntax_Util.abs uu____4368 body what)))
end
| uu____4394 -> begin
(raise_error1 ((FStar_Errors.Fatal_UnexpectedBindShape), ("unexpected shape for bind")))
end))
in (

let apply_close = (fun t -> (match ((Prims.op_Equality (FStar_List.length effect_binders1) (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____4416 -> begin
(

let uu____4417 = (

let uu____4418 = (

let uu____4419 = (

let uu____4434 = (

let uu____4443 = (FStar_Syntax_Util.args_of_binders effect_binders1)
in (FStar_Pervasives_Native.snd uu____4443))
in ((t), (uu____4434)))
in FStar_Syntax_Syntax.Tm_app (uu____4419))
in (mk1 uu____4418))
in (FStar_Syntax_Subst.close effect_binders1 uu____4417))
end))
in (

let rec apply_last1 = (fun f l -> (match (l) with
| [] -> begin
(failwith "empty path..")
end
| (a2)::[] -> begin
(

let uu____4485 = (f a2)
in (uu____4485)::[])
end
| (x)::xs -> begin
(

let uu____4490 = (apply_last1 f xs)
in (x)::uu____4490)
end))
in (

let register = (fun name item -> (

let p = (FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname)
in (

let p' = (apply_last1 (fun s -> (Prims.strcat "__" (Prims.strcat s (Prims.strcat "_eff_override_" name)))) p)
in (

let l' = (FStar_Ident.lid_of_path p' FStar_Range.dummyRange)
in (

let uu____4516 = (FStar_TypeChecker_Env.try_lookup_lid env1 l')
in (match (uu____4516) with
| FStar_Pervasives_Native.Some (_us, _t) -> begin
((

let uu____4546 = (FStar_Options.debug_any ())
in (match (uu____4546) with
| true -> begin
(

let uu____4547 = (FStar_Ident.string_of_lid l')
in (FStar_Util.print1 "DM4F: Applying override %s\n" uu____4547))
end
| uu____4548 -> begin
()
end));
(

let uu____4549 = (FStar_Syntax_Syntax.lid_as_fv l' FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____4549));
)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4558 = (

let uu____4563 = (mk_lid name)
in (

let uu____4564 = (FStar_Syntax_Util.abs effect_binders1 item FStar_Pervasives_Native.None)
in (FStar_TypeChecker_Util.mk_toplevel_definition env1 uu____4563 uu____4564)))
in (match (uu____4558) with
| (sigelt, fv) -> begin
((

let uu____4568 = (

let uu____4571 = (FStar_ST.op_Bang sigelts)
in (sigelt)::uu____4571)
in (FStar_ST.op_Colon_Equals sigelts uu____4568));
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

let uu____4676 = (

let uu____4679 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true"))))
in (

let uu____4680 = (FStar_ST.op_Bang sigelts)
in (uu____4679)::uu____4680))
in (FStar_ST.op_Colon_Equals sigelts uu____4676));
(

let return_elab1 = (register "return_elab" return_elab)
in ((FStar_Options.pop ());
(

let bind_wp2 = (register "bind_wp" bind_wp1)
in ((FStar_Options.push ());
(

let uu____4786 = (

let uu____4789 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true"))))
in (

let uu____4790 = (FStar_ST.op_Bang sigelts)
in (uu____4789)::uu____4790))
in (FStar_ST.op_Colon_Equals sigelts uu____4786));
(

let bind_elab1 = (register "bind_elab" bind_elab)
in ((FStar_Options.pop ());
(

let uu____4893 = (FStar_List.fold_left (fun uu____4933 action -> (match (uu____4933) with
| (dmff_env3, actions) -> begin
(

let params_un = (FStar_Syntax_Subst.open_binders action.FStar_Syntax_Syntax.action_params)
in (

let uu____4954 = (

let uu____4961 = (FStar_TypeChecker_DMFF.get_env dmff_env3)
in (FStar_TypeChecker_TcTerm.tc_tparams uu____4961 params_un))
in (match (uu____4954) with
| (action_params, env', uu____4970) -> begin
(

let action_params1 = (FStar_List.map (fun uu____4990 -> (match (uu____4990) with
| (bv, qual) -> begin
(

let uu____5001 = (

let uu___77_5002 = bv
in (

let uu____5003 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env' bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___77_5002.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___77_5002.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5003}))
in ((uu____5001), (qual)))
end)) action_params)
in (

let dmff_env' = (FStar_TypeChecker_DMFF.set_env dmff_env3 env')
in (

let uu____5007 = (elaborate_and_star dmff_env' action_params1 ((action.FStar_Syntax_Syntax.action_univs), (action.FStar_Syntax_Syntax.action_defn)))
in (match (uu____5007) with
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
| uu____5045 -> begin
(

let uu____5046 = (FStar_Syntax_Syntax.mk_Total action_typ_with_wp1)
in (FStar_Syntax_Util.flat_arrow action_params2 uu____5046))
end)
in ((

let uu____5050 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("ED")))
in (match (uu____5050) with
| true -> begin
(

let uu____5051 = (FStar_Syntax_Print.binders_to_string "," params_un)
in (

let uu____5052 = (FStar_Syntax_Print.binders_to_string "," action_params2)
in (

let uu____5053 = (FStar_Syntax_Print.term_to_string action_typ_with_wp2)
in (

let uu____5054 = (FStar_Syntax_Print.term_to_string action_elab2)
in (FStar_Util.print4 "original action_params %s, end action_params %s, type %s, term %s\n" uu____5051 uu____5052 uu____5053 uu____5054)))))
end
| uu____5055 -> begin
()
end));
(

let action_elab3 = (register (Prims.strcat name "_elab") action_elab2)
in (

let action_typ_with_wp3 = (register (Prims.strcat name "_complete_type") action_typ_with_wp2)
in (

let uu____5058 = (

let uu____5061 = (

let uu___78_5062 = action
in (

let uu____5063 = (apply_close action_elab3)
in (

let uu____5064 = (apply_close action_typ_with_wp3)
in {FStar_Syntax_Syntax.action_name = uu___78_5062.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___78_5062.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___78_5062.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = []; FStar_Syntax_Syntax.action_defn = uu____5063; FStar_Syntax_Syntax.action_typ = uu____5064})))
in (uu____5061)::actions)
in ((dmff_env4), (uu____5058)))));
))))))))
end))))
end)))
end)) ((dmff_env2), ([])) ed.FStar_Syntax_Syntax.actions)
in (match (uu____4893) with
| (dmff_env3, actions) -> begin
(

let actions1 = (FStar_List.rev actions)
in (

let repr1 = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp_a" FStar_Pervasives_Native.None wp_a)
in (

let binders = (

let uu____5103 = (FStar_Syntax_Syntax.mk_binder a1)
in (

let uu____5108 = (

let uu____5115 = (FStar_Syntax_Syntax.mk_binder wp)
in (uu____5115)::[])
in (uu____5103)::uu____5108))
in (

let uu____5132 = (

let uu____5135 = (

let uu____5136 = (

let uu____5137 = (

let uu____5152 = (

let uu____5161 = (

let uu____5168 = (FStar_Syntax_Syntax.bv_to_name a1)
in (

let uu____5171 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____5168), (uu____5171))))
in (uu____5161)::[])
in ((repr), (uu____5152)))
in FStar_Syntax_Syntax.Tm_app (uu____5137))
in (mk1 uu____5136))
in (

let uu____5196 = (FStar_Syntax_Syntax.bv_to_name wp)
in (FStar_TypeChecker_DMFF.trans_F dmff_env3 uu____5135 uu____5196)))
in (FStar_Syntax_Util.abs binders uu____5132 FStar_Pervasives_Native.None))))
in (

let uu____5197 = (recheck_debug "FC" env1 repr1)
in (

let repr2 = (register "repr" repr1)
in (

let uu____5199 = (

let uu____5208 = (

let uu____5209 = (

let uu____5212 = (FStar_Syntax_Subst.compress wp_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____5212))
in uu____5209.FStar_Syntax_Syntax.n)
in (match (uu____5208) with
| FStar_Syntax_Syntax.Tm_abs ((type_param)::effect_param, arrow1, uu____5226) -> begin
(

let uu____5255 = (

let uu____5272 = (FStar_Syntax_Subst.open_term ((type_param)::effect_param) arrow1)
in (match (uu____5272) with
| ((b)::bs, body) -> begin
((b), (bs), (body))
end
| uu____5324 -> begin
(failwith "Impossible : open_term nt preserving binders arity")
end))
in (match (uu____5255) with
| (type_param1, effect_param1, arrow2) -> begin
(

let uu____5376 = (

let uu____5377 = (

let uu____5380 = (FStar_Syntax_Subst.compress arrow2)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____5380))
in uu____5377.FStar_Syntax_Syntax.n)
in (match (uu____5376) with
| FStar_Syntax_Syntax.Tm_arrow (wp_binders, c) -> begin
(

let uu____5409 = (FStar_Syntax_Subst.open_comp wp_binders c)
in (match (uu____5409) with
| (wp_binders1, c1) -> begin
(

let uu____5424 = (FStar_List.partition (fun uu____5449 -> (match (uu____5449) with
| (bv, uu____5455) -> begin
(

let uu____5456 = (

let uu____5457 = (FStar_Syntax_Free.names bv.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____5457 (FStar_Util.set_mem (FStar_Pervasives_Native.fst type_param1))))
in (FStar_All.pipe_right uu____5456 Prims.op_Negation))
end)) wp_binders1)
in (match (uu____5424) with
| (pre_args, post_args) -> begin
(

let post = (match (post_args) with
| (post)::[] -> begin
post
end
| [] -> begin
(

let err_msg = (

let uu____5523 = (FStar_Syntax_Print.term_to_string arrow2)
in (FStar_Util.format1 "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)" uu____5523))
in (FStar_Errors.raise_err ((FStar_Errors.Fatal_ImpossibleToGenerateDMEffect), (err_msg))))
end
| uu____5528 -> begin
(

let err_msg = (

let uu____5536 = (FStar_Syntax_Print.term_to_string arrow2)
in (FStar_Util.format1 "Impossible to generate DM effect: multiple post candidates %s" uu____5536))
in (FStar_Errors.raise_err ((FStar_Errors.Fatal_ImpossibleToGenerateDMEffect), (err_msg))))
end)
in (

let uu____5541 = (FStar_Syntax_Util.arrow pre_args c1)
in (

let uu____5544 = (FStar_Syntax_Util.abs ((type_param1)::effect_param1) (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort FStar_Pervasives_Native.None)
in ((uu____5541), (uu____5544)))))
end))
end))
end
| uu____5555 -> begin
(

let uu____5556 = (

let uu____5561 = (

let uu____5562 = (FStar_Syntax_Print.term_to_string arrow2)
in (FStar_Util.format1 "Impossible: pre/post arrow %s" uu____5562))
in ((FStar_Errors.Fatal_ImpossiblePrePostArrow), (uu____5561)))
in (raise_error1 uu____5556))
end))
end))
end
| uu____5571 -> begin
(

let uu____5572 = (

let uu____5577 = (

let uu____5578 = (FStar_Syntax_Print.term_to_string wp_type)
in (FStar_Util.format1 "Impossible: pre/post abs %s" uu____5578))
in ((FStar_Errors.Fatal_ImpossiblePrePostAbs), (uu____5577)))
in (raise_error1 uu____5572))
end))
in (match (uu____5199) with
| (pre, post) -> begin
((

let uu____5608 = (register "pre" pre)
in ());
(

let uu____5610 = (register "post" post)
in ());
(

let uu____5612 = (register "wp" wp_type)
in ());
(

let ed1 = (

let uu___79_5614 = ed
in (

let uu____5615 = (FStar_Syntax_Subst.close_binders effect_binders1)
in (

let uu____5616 = (FStar_Syntax_Subst.close effect_binders1 effect_signature)
in (

let uu____5617 = (

let uu____5618 = (apply_close return_wp2)
in (([]), (uu____5618)))
in (

let uu____5625 = (

let uu____5626 = (apply_close bind_wp2)
in (([]), (uu____5626)))
in (

let uu____5633 = (apply_close repr2)
in (

let uu____5634 = (

let uu____5635 = (apply_close return_elab1)
in (([]), (uu____5635)))
in (

let uu____5642 = (

let uu____5643 = (apply_close bind_elab1)
in (([]), (uu____5643)))
in {FStar_Syntax_Syntax.cattributes = uu___79_5614.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___79_5614.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___79_5614.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu____5615; FStar_Syntax_Syntax.signature = uu____5616; FStar_Syntax_Syntax.ret_wp = uu____5617; FStar_Syntax_Syntax.bind_wp = uu____5625; FStar_Syntax_Syntax.if_then_else = uu___79_5614.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = uu___79_5614.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = uu___79_5614.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = uu___79_5614.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = uu___79_5614.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = uu___79_5614.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = uu___79_5614.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = uu___79_5614.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = uu____5633; FStar_Syntax_Syntax.return_repr = uu____5634; FStar_Syntax_Syntax.bind_repr = uu____5642; FStar_Syntax_Syntax.actions = actions1; FStar_Syntax_Syntax.eff_attrs = uu___79_5614.FStar_Syntax_Syntax.eff_attrs}))))))))
in (

let uu____5650 = (FStar_TypeChecker_DMFF.gen_wps_for_free env1 effect_binders1 a1 wp_a ed1)
in (match (uu____5650) with
| (sigelts', ed2) -> begin
((

let uu____5668 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____5668) with
| true -> begin
(

let uu____5669 = (FStar_Syntax_Print.eff_decl_to_string true ed2)
in (FStar_Util.print_string uu____5669))
end
| uu____5670 -> begin
()
end));
(

let lift_from_pure_opt = (match ((Prims.op_Equality (FStar_List.length effect_binders1) (Prims.parse_int "0"))) with
| true -> begin
(

let lift_from_pure = (

let uu____5682 = (

let uu____5685 = (

let uu____5686 = (apply_close lift_from_pure_wp1)
in (([]), (uu____5686)))
in FStar_Pervasives_Native.Some (uu____5685))
in {FStar_Syntax_Syntax.source = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.target = ed2.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.lift_wp = uu____5682; FStar_Syntax_Syntax.lift = FStar_Pervasives_Native.None})
in (

let uu____5693 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_sub_effect (lift_from_pure)))
in FStar_Pervasives_Native.Some (uu____5693)))
end
| uu____5694 -> begin
FStar_Pervasives_Native.None
end)
in (

let uu____5695 = (

let uu____5698 = (

let uu____5701 = (FStar_ST.op_Bang sigelts)
in (FStar_List.rev uu____5701))
in (FStar_List.append uu____5698 sigelts'))
in ((uu____5695), (ed2), (lift_from_pure_opt))));
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


let tc_lex_t : 'Auu____5767 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  'Auu____5767 Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (

let err_range = (

let uu____5802 = (FStar_List.hd ses)
in uu____5802.FStar_Syntax_Syntax.sigrng)
in ((match (lids) with
| (lex_t1)::(lex_top1)::(lex_cons)::[] when (((FStar_Ident.lid_equals lex_t1 FStar_Parser_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top1 FStar_Parser_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Parser_Const.lexcons_lid)) -> begin
()
end
| uu____5807 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_InvalidRedefinitionOfLexT), ("Invalid (partial) redefinition of lex_t")) err_range)
end);
(match (ses) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (lex_t1, uu____5811, [], t, uu____5813, uu____5814); FStar_Syntax_Syntax.sigrng = r; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = uu____5816; FStar_Syntax_Syntax.sigattrs = uu____5817})::({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (lex_top1, uu____5819, _t_top, _lex_t_top, _0_17, uu____5822); FStar_Syntax_Syntax.sigrng = r1; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = uu____5824; FStar_Syntax_Syntax.sigattrs = uu____5825})::({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (lex_cons, uu____5827, _t_cons, _lex_t_cons, _0_18, uu____5830); FStar_Syntax_Syntax.sigrng = r2; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = uu____5832; FStar_Syntax_Syntax.sigattrs = uu____5833})::[] when (((_0_17 = (Prims.parse_int "0")) && (_0_18 = (Prims.parse_int "0"))) && (((FStar_Ident.lid_equals lex_t1 FStar_Parser_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top1 FStar_Parser_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Parser_Const.lexcons_lid))) -> begin
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

let uu____5878 = (

let uu____5885 = (

let uu____5886 = (

let uu____5893 = (

let uu____5896 = (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar uu____5896 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))
in ((uu____5893), ((FStar_Syntax_Syntax.U_name (utop))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____5886))
in (FStar_Syntax_Syntax.mk uu____5885))
in (uu____5878 FStar_Pervasives_Native.None r1))
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

let uu____5912 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) FStar_Pervasives_Native.None r2)
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (r2)) uu____5912))
in (

let hd1 = (

let uu____5914 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (r2)) uu____5914))
in (

let tl1 = (

let uu____5916 = (

let uu____5917 = (

let uu____5924 = (

let uu____5925 = (

let uu____5932 = (

let uu____5935 = (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar uu____5935 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))
in ((uu____5932), ((FStar_Syntax_Syntax.U_name (ucons2))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____5925))
in (FStar_Syntax_Syntax.mk uu____5924))
in (uu____5917 FStar_Pervasives_Native.None r2))
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (r2)) uu____5916))
in (

let res = (

let uu____5944 = (

let uu____5951 = (

let uu____5952 = (

let uu____5959 = (

let uu____5962 = (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar uu____5962 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))
in ((uu____5959), ((FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____5952))
in (FStar_Syntax_Syntax.mk uu____5951))
in (uu____5944 FStar_Pervasives_Native.None r2))
in (

let uu____5968 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow ((((a), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::(((hd1), (FStar_Pervasives_Native.None)))::(((tl1), (FStar_Pervasives_Native.None)))::[]) uu____5968))))))
in (

let lex_cons_t1 = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((lex_cons), ((ucons1)::(ucons2)::[]), (lex_cons_t1), (FStar_Parser_Const.lex_t_lid), ((Prims.parse_int "0")), ([]))); FStar_Syntax_Syntax.sigrng = r2; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (

let uu____5991 = (FStar_TypeChecker_Env.get_range env)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle ((((tc)::(dc_lextop)::(dc_lexcons)::[]), (lids))); FStar_Syntax_Syntax.sigrng = uu____5991; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))))))))))))))
end
| uu____5996 -> begin
(

let err_msg = (

let uu____6000 = (

let uu____6001 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_bundle (((ses), (lids)))))
in (FStar_Syntax_Print.sigelt_to_string uu____6001))
in (FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n" uu____6000))
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_InvalidRedefinitionOfLexT), (err_msg)) err_range))
end);
)))


let tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun env phi r -> (

let env1 = (FStar_TypeChecker_Env.set_range env r)
in (

let uu____6022 = (FStar_Syntax_Util.type_u ())
in (match (uu____6022) with
| (k, uu____6028) -> begin
(

let phi1 = (

let uu____6032 = (tc_check_trivial_guard env1 phi k)
in (FStar_All.pipe_right uu____6032 (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env1)))
in ((FStar_TypeChecker_Util.check_uvars r phi1);
phi1;
))
end))))


let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env ses quals lids -> (

let env1 = (FStar_TypeChecker_Env.push env "tc_inductive")
in (

let uu____6075 = (FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1 ses quals lids)
in (match (uu____6075) with
| (sig_bndle, tcs, datas) -> begin
(

let data_ops_ses = (

let uu____6106 = (FStar_List.map (FStar_TypeChecker_TcInductive.mk_data_operations quals env1 tcs) datas)
in (FStar_All.pipe_right uu____6106 FStar_List.flatten))
in ((

let uu____6120 = ((FStar_Options.no_positivity ()) || (

let uu____6122 = (FStar_TypeChecker_Env.should_verify env1)
in (not (uu____6122))))
in (match (uu____6120) with
| true -> begin
()
end
| uu____6123 -> begin
(

let env2 = (FStar_TypeChecker_Env.push_sigelt env1 sig_bndle)
in (FStar_List.iter (fun ty -> (

let b = (FStar_TypeChecker_TcInductive.check_positivity ty env2)
in (match ((not (b))) with
| true -> begin
(

let uu____6133 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____6143, uu____6144, uu____6145, uu____6146, uu____6147) -> begin
((lid), (ty.FStar_Syntax_Syntax.sigrng))
end
| uu____6156 -> begin
(failwith "Impossible!")
end)
in (match (uu____6133) with
| (lid, r) -> begin
(FStar_Errors.log_issue r ((FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition), ((Prims.strcat "Inductive type " (Prims.strcat lid.FStar_Ident.str " does not satisfy the positivity condition")))))
end))
end
| uu____6163 -> begin
()
end))) tcs))
end));
(

let skip_prims_type = (fun uu____6169 -> (

let lid = (

let ty = (FStar_List.hd tcs)
in (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____6173, uu____6174, uu____6175, uu____6176, uu____6177) -> begin
lid
end
| uu____6186 -> begin
(failwith "Impossible")
end))
in (FStar_List.existsb (fun s -> (Prims.op_Equality s lid.FStar_Ident.ident.FStar_Ident.idText)) FStar_TypeChecker_TcInductive.early_prims_inductives)))
in (

let is_noeq = (FStar_List.existsb (fun q -> (Prims.op_Equality q FStar_Syntax_Syntax.Noeq)) quals)
in (

let res = (

let uu____6199 = (((Prims.op_Equality (FStar_List.length tcs) (Prims.parse_int "0")) || ((FStar_Ident.lid_equals env1.FStar_TypeChecker_Env.curmodule FStar_Parser_Const.prims_lid) && (skip_prims_type ()))) || is_noeq)
in (match (uu____6199) with
| true -> begin
((sig_bndle), (data_ops_ses))
end
| uu____6209 -> begin
(

let is_unopteq = (FStar_List.existsb (fun q -> (Prims.op_Equality q FStar_Syntax_Syntax.Unopteq)) quals)
in (

let ses1 = (match (is_unopteq) with
| true -> begin
(FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme sig_bndle tcs datas env1)
end
| uu____6218 -> begin
(FStar_TypeChecker_TcInductive.optimized_haseq_scheme sig_bndle tcs datas env1)
end)
in ((sig_bndle), ((FStar_List.append ses1 data_ops_ses)))))
end))
in ((

let uu____6222 = (FStar_TypeChecker_Env.pop env1 "tc_inductive")
in ());
res;
))));
))
end))))


let z3_reset_options : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun en -> (

let env = (

let uu____6229 = (FStar_Options.using_facts_from ())
in (FStar_TypeChecker_Env.set_proof_ns uu____6229 en))
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
env;
)))


let tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env se -> (

let env1 = (set_hint_correlator env se)
in ((FStar_TypeChecker_Util.check_sigelt_quals env1 se);
(

let r = se.FStar_Syntax_Syntax.sigrng
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____6268) -> begin
(failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____6293) -> begin
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

let uu____6348 = ((FStar_Options.use_two_phase_tc ()) && (FStar_TypeChecker_Env.should_verify env2))
in (match (uu____6348) with
| true -> begin
(

let ses1 = (

let uu____6354 = (

let uu____6355 = (

let uu____6356 = (tc_inductive (

let uu___80_6365 = env2
in {FStar_TypeChecker_Env.solver = uu___80_6365.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___80_6365.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___80_6365.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___80_6365.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___80_6365.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___80_6365.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___80_6365.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___80_6365.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___80_6365.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___80_6365.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___80_6365.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___80_6365.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___80_6365.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___80_6365.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___80_6365.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___80_6365.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___80_6365.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___80_6365.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___80_6365.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___80_6365.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___80_6365.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___80_6365.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___80_6365.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___80_6365.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___80_6365.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___80_6365.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___80_6365.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___80_6365.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___80_6365.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___80_6365.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___80_6365.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___80_6365.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___80_6365.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___80_6365.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___80_6365.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___80_6365.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___80_6365.FStar_TypeChecker_Env.dep_graph}) ses se.FStar_Syntax_Syntax.sigquals lids)
in (FStar_All.pipe_right uu____6356 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____6355 (FStar_TypeChecker_Normalize.elim_uvars env2)))
in (FStar_All.pipe_right uu____6354 FStar_Syntax_Util.ses_of_sigbundle))
in ((

let uu____6377 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("TwoPhases")))
in (match (uu____6377) with
| true -> begin
(

let uu____6378 = (FStar_Syntax_Print.sigelt_to_string (

let uu___81_6381 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (((ses1), (lids))); FStar_Syntax_Syntax.sigrng = uu___81_6381.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___81_6381.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___81_6381.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___81_6381.FStar_Syntax_Syntax.sigattrs}))
in (FStar_Util.print1 "Inductive after phase 1: %s\n" uu____6378))
end
| uu____6386 -> begin
()
end));
ses1;
))
end
| uu____6387 -> begin
ses
end))
in (

let uu____6388 = (tc_inductive env2 ses1 se.FStar_Syntax_Syntax.sigquals lids)
in (match (uu____6388) with
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

let uu____6420 = (cps_and_elaborate env1 ne)
in (match (uu____6420) with
| (ses, ne1, lift_from_pure_opt) -> begin
(

let effect_and_lift_ses = (match (lift_from_pure_opt) with
| FStar_Pervasives_Native.Some (lift) -> begin
((

let uu___82_6457 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne1); FStar_Syntax_Syntax.sigrng = uu___82_6457.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___82_6457.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___82_6457.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___82_6457.FStar_Syntax_Syntax.sigattrs}))::(lift)::[]
end
| FStar_Pervasives_Native.None -> begin
((

let uu___83_6459 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne1); FStar_Syntax_Syntax.sigrng = uu___83_6459.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___83_6459.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___83_6459.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___83_6459.FStar_Syntax_Syntax.sigattrs}))::[]
end)
in (([]), ((FStar_List.append ses effect_and_lift_ses))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let ne1 = (

let uu____6466 = ((FStar_Options.use_two_phase_tc ()) && (FStar_TypeChecker_Env.should_verify env1))
in (match (uu____6466) with
| true -> begin
(

let ne1 = (

let uu____6468 = (

let uu____6469 = (

let uu____6470 = (tc_eff_decl (

let uu___84_6473 = env1
in {FStar_TypeChecker_Env.solver = uu___84_6473.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___84_6473.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___84_6473.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___84_6473.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___84_6473.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___84_6473.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___84_6473.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___84_6473.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___84_6473.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___84_6473.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___84_6473.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___84_6473.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___84_6473.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___84_6473.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___84_6473.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___84_6473.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___84_6473.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___84_6473.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___84_6473.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___84_6473.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___84_6473.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___84_6473.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___84_6473.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___84_6473.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___84_6473.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___84_6473.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___84_6473.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___84_6473.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___84_6473.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___84_6473.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___84_6473.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___84_6473.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___84_6473.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___84_6473.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___84_6473.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___84_6473.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___84_6473.FStar_TypeChecker_Env.dep_graph}) ne)
in (FStar_All.pipe_right uu____6470 (fun ne1 -> (

let uu___85_6477 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne1); FStar_Syntax_Syntax.sigrng = uu___85_6477.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___85_6477.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___85_6477.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___85_6477.FStar_Syntax_Syntax.sigattrs}))))
in (FStar_All.pipe_right uu____6469 (FStar_TypeChecker_Normalize.elim_uvars env1)))
in (FStar_All.pipe_right uu____6468 FStar_Syntax_Util.eff_decl_of_new_effect))
in ((

let uu____6479 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("TwoPhases")))
in (match (uu____6479) with
| true -> begin
(

let uu____6480 = (FStar_Syntax_Print.sigelt_to_string (

let uu___86_6483 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne1); FStar_Syntax_Syntax.sigrng = uu___86_6483.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___86_6483.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___86_6483.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___86_6483.FStar_Syntax_Syntax.sigattrs}))
in (FStar_Util.print1 "Effect decl after phase 1: %s\n" uu____6480))
end
| uu____6484 -> begin
()
end));
ne1;
))
end
| uu____6485 -> begin
ne
end))
in (

let ne2 = (tc_eff_decl env1 ne1)
in (

let se1 = (

let uu___87_6488 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne2); FStar_Syntax_Syntax.sigrng = uu___87_6488.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___87_6488.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___87_6488.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___87_6488.FStar_Syntax_Syntax.sigattrs})
in (((se1)::[]), ([])))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub1) -> begin
(

let ed_src = (FStar_TypeChecker_Env.get_effect_decl env1 sub1.FStar_Syntax_Syntax.source)
in (

let ed_tgt = (FStar_TypeChecker_Env.get_effect_decl env1 sub1.FStar_Syntax_Syntax.target)
in (

let uu____6496 = (

let uu____6503 = (FStar_TypeChecker_Env.lookup_effect_lid env1 sub1.FStar_Syntax_Syntax.source)
in (monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____6503))
in (match (uu____6496) with
| (a, wp_a_src) -> begin
(

let uu____6518 = (

let uu____6525 = (FStar_TypeChecker_Env.lookup_effect_lid env1 sub1.FStar_Syntax_Syntax.target)
in (monad_signature env1 sub1.FStar_Syntax_Syntax.target uu____6525))
in (match (uu____6518) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (

let uu____6541 = (

let uu____6544 = (

let uu____6545 = (

let uu____6552 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (uu____6552)))
in FStar_Syntax_Syntax.NT (uu____6545))
in (uu____6544)::[])
in (FStar_Syntax_Subst.subst uu____6541 wp_b_tgt))
in (

let expected_k = (

let uu____6560 = (

let uu____6567 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____6572 = (

let uu____6579 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (uu____6579)::[])
in (uu____6567)::uu____6572))
in (

let uu____6596 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow uu____6560 uu____6596)))
in (

let repr_type = (fun eff_name a1 wp -> (

let no_reify = (fun l -> (

let uu____6625 = (

let uu____6630 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((FStar_Errors.Fatal_EffectCannotBeReified), (uu____6630)))
in (

let uu____6631 = (FStar_TypeChecker_Env.get_range env1)
in (FStar_Errors.raise_error uu____6625 uu____6631))))
in (

let uu____6634 = (FStar_TypeChecker_Env.effect_decl_opt env1 eff_name)
in (match (uu____6634) with
| FStar_Pervasives_Native.None -> begin
(no_reify eff_name)
end
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((FStar_Syntax_Syntax.U_unknown)::[]) env1 ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let uu____6668 = (

let uu____6669 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (not (uu____6669)))
in (match (uu____6668) with
| true -> begin
(no_reify eff_name)
end
| uu____6674 -> begin
(

let uu____6675 = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____6676 = (

let uu____6683 = (

let uu____6684 = (

let uu____6699 = (

let uu____6708 = (FStar_Syntax_Syntax.as_arg a1)
in (

let uu____6715 = (

let uu____6724 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____6724)::[])
in (uu____6708)::uu____6715))
in ((repr), (uu____6699)))
in FStar_Syntax_Syntax.Tm_app (uu____6684))
in (FStar_Syntax_Syntax.mk uu____6683))
in (uu____6676 FStar_Pervasives_Native.None uu____6675)))
end)))
end))))
in (

let uu____6762 = (match (((sub1.FStar_Syntax_Syntax.lift), (sub1.FStar_Syntax_Syntax.lift_wp))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(failwith "Impossible (parser)")
end
| (lift, FStar_Pervasives_Native.Some (uvs, lift_wp)) -> begin
(

let uu____6898 = (match (((FStar_List.length uvs) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____6907 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____6907) with
| (usubst, uvs1) -> begin
(

let uu____6930 = (FStar_TypeChecker_Env.push_univ_vars env1 uvs1)
in (

let uu____6931 = (FStar_Syntax_Subst.subst usubst lift_wp)
in ((uu____6930), (uu____6931))))
end))
end
| uu____6932 -> begin
((env1), (lift_wp))
end)
in (match (uu____6898) with
| (env2, lift_wp1) -> begin
(

let lift_wp2 = (match ((Prims.op_Equality (FStar_List.length uvs) (Prims.parse_int "0"))) with
| true -> begin
(check_and_gen env2 lift_wp1 expected_k)
end
| uu____6967 -> begin
(

let lift_wp2 = (tc_check_trivial_guard env2 lift_wp1 expected_k)
in (

let uu____6969 = (FStar_Syntax_Subst.close_univ_vars uvs lift_wp2)
in ((uvs), (uu____6969))))
end)
in ((lift), (lift_wp2)))
end))
end
| (FStar_Pervasives_Native.Some (what, lift), FStar_Pervasives_Native.None) -> begin
(

let uu____7020 = (match (((FStar_List.length what) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____7033 = (FStar_Syntax_Subst.univ_var_opening what)
in (match (uu____7033) with
| (usubst, uvs) -> begin
(

let uu____7058 = (FStar_Syntax_Subst.subst usubst lift)
in ((uvs), (uu____7058)))
end))
end
| uu____7061 -> begin
(([]), (lift))
end)
in (match (uu____7020) with
| (uvs, lift1) -> begin
((

let uu____7089 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____7089) with
| true -> begin
(

let uu____7090 = (FStar_Syntax_Print.term_to_string lift1)
in (FStar_Util.print1 "Lift for free : %s\n" uu____7090))
end
| uu____7091 -> begin
()
end));
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env1 (FStar_TypeChecker_TcTerm.tc_constant env1 FStar_Range.dummyRange))
in (

let uu____7093 = (

let uu____7100 = (FStar_TypeChecker_Env.push_univ_vars env1 uvs)
in (FStar_TypeChecker_TcTerm.tc_term uu____7100 lift1))
in (match (uu____7093) with
| (lift2, comp, uu____7121) -> begin
(

let uu____7122 = (FStar_TypeChecker_DMFF.star_expr dmff_env lift2)
in (match (uu____7122) with
| (uu____7147, lift_wp, lift_elab) -> begin
(

let lift_wp1 = (recheck_debug "lift-wp" env1 lift_wp)
in (

let lift_elab1 = (recheck_debug "lift-elab" env1 lift_elab)
in (match ((Prims.op_Equality (FStar_List.length uvs) (Prims.parse_int "0"))) with
| true -> begin
(

let uu____7171 = (

let uu____7174 = (FStar_TypeChecker_Util.generalize_universes env1 lift_elab1)
in FStar_Pervasives_Native.Some (uu____7174))
in (

let uu____7175 = (FStar_TypeChecker_Util.generalize_universes env1 lift_wp1)
in ((uu____7171), (uu____7175))))
end
| uu____7178 -> begin
(

let uu____7179 = (

let uu____7188 = (

let uu____7195 = (FStar_Syntax_Subst.close_univ_vars uvs lift_elab1)
in ((uvs), (uu____7195)))
in FStar_Pervasives_Native.Some (uu____7188))
in (

let uu____7204 = (

let uu____7211 = (FStar_Syntax_Subst.close_univ_vars uvs lift_wp1)
in ((uvs), (uu____7211)))
in ((uu____7179), (uu____7204))))
end)))
end))
end)));
)
end))
end)
in (match (uu____6762) with
| (lift, lift_wp) -> begin
(

let env2 = (

let uu___88_7267 = env1
in {FStar_TypeChecker_Env.solver = uu___88_7267.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___88_7267.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___88_7267.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___88_7267.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___88_7267.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___88_7267.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___88_7267.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___88_7267.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___88_7267.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___88_7267.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___88_7267.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___88_7267.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___88_7267.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___88_7267.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___88_7267.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___88_7267.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___88_7267.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___88_7267.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___88_7267.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___88_7267.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___88_7267.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___88_7267.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___88_7267.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___88_7267.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___88_7267.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___88_7267.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___88_7267.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___88_7267.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___88_7267.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___88_7267.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___88_7267.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___88_7267.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___88_7267.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___88_7267.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___88_7267.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___88_7267.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___88_7267.FStar_TypeChecker_Env.dep_graph})
in (

let lift1 = (match (lift) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (uvs, lift1) -> begin
(

let uu____7309 = (

let uu____7314 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____7314) with
| (usubst, uvs1) -> begin
(

let uu____7337 = (FStar_TypeChecker_Env.push_univ_vars env2 uvs1)
in (

let uu____7338 = (FStar_Syntax_Subst.subst usubst lift1)
in ((uu____7337), (uu____7338))))
end))
in (match (uu____7309) with
| (env3, lift2) -> begin
(

let uu____7349 = (

let uu____7356 = (FStar_TypeChecker_Env.lookup_effect_lid env3 sub1.FStar_Syntax_Syntax.source)
in (monad_signature env3 sub1.FStar_Syntax_Syntax.source uu____7356))
in (match (uu____7349) with
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

let uu____7386 = (FStar_TypeChecker_Env.get_range env3)
in (

let uu____7387 = (

let uu____7394 = (

let uu____7395 = (

let uu____7410 = (

let uu____7419 = (FStar_Syntax_Syntax.as_arg a_typ)
in (

let uu____7426 = (

let uu____7435 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (uu____7435)::[])
in (uu____7419)::uu____7426))
in ((lift_wp1), (uu____7410)))
in FStar_Syntax_Syntax.Tm_app (uu____7395))
in (FStar_Syntax_Syntax.mk uu____7394))
in (uu____7387 FStar_Pervasives_Native.None uu____7386)))
in (repr_type sub1.FStar_Syntax_Syntax.target a_typ lift_wp_a)))
in (

let expected_k1 = (

let uu____7476 = (

let uu____7483 = (FStar_Syntax_Syntax.mk_binder a1)
in (

let uu____7488 = (

let uu____7495 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (

let uu____7500 = (

let uu____7507 = (FStar_Syntax_Syntax.null_binder repr_f)
in (uu____7507)::[])
in (uu____7495)::uu____7500))
in (uu____7483)::uu____7488))
in (

let uu____7528 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow uu____7476 uu____7528)))
in (

let uu____7531 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env3 expected_k1)
in (match (uu____7531) with
| (expected_k2, uu____7547, uu____7548) -> begin
(

let lift3 = (match ((Prims.op_Equality (FStar_List.length uvs) (Prims.parse_int "0"))) with
| true -> begin
(check_and_gen env3 lift2 expected_k2)
end
| uu____7563 -> begin
(

let lift3 = (tc_check_trivial_guard env3 lift2 expected_k2)
in (

let uu____7565 = (FStar_Syntax_Subst.close_univ_vars uvs lift3)
in ((uvs), (uu____7565))))
end)
in FStar_Pervasives_Native.Some (lift3))
end))))))))
end))
end))
end)
in ((

let uu____7575 = (

let uu____7576 = (

let uu____7577 = (FStar_All.pipe_right lift_wp FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____7577 FStar_List.length))
in (Prims.op_disEquality uu____7576 (Prims.parse_int "1")))
in (match (uu____7575) with
| true -> begin
(

let uu____7592 = (

let uu____7597 = (

let uu____7598 = (FStar_Syntax_Print.lid_to_string sub1.FStar_Syntax_Syntax.source)
in (

let uu____7599 = (FStar_Syntax_Print.lid_to_string sub1.FStar_Syntax_Syntax.target)
in (

let uu____7600 = (

let uu____7601 = (

let uu____7602 = (FStar_All.pipe_right lift_wp FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____7602 FStar_List.length))
in (FStar_All.pipe_right uu____7601 FStar_Util.string_of_int))
in (FStar_Util.format3 "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes" uu____7598 uu____7599 uu____7600))))
in ((FStar_Errors.Fatal_TooManyUniverse), (uu____7597)))
in (FStar_Errors.raise_error uu____7592 r))
end
| uu____7617 -> begin
()
end));
(

let uu____7619 = ((FStar_Util.is_some lift1) && (

let uu____7627 = (

let uu____7629 = (

let uu____7632 = (FStar_All.pipe_right lift1 FStar_Util.must)
in (FStar_All.pipe_right uu____7632 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____7629 FStar_List.length))
in (Prims.op_disEquality uu____7627 (Prims.parse_int "1"))))
in (match (uu____7619) with
| true -> begin
(

let uu____7672 = (

let uu____7677 = (

let uu____7678 = (FStar_Syntax_Print.lid_to_string sub1.FStar_Syntax_Syntax.source)
in (

let uu____7679 = (FStar_Syntax_Print.lid_to_string sub1.FStar_Syntax_Syntax.target)
in (

let uu____7680 = (

let uu____7681 = (

let uu____7682 = (

let uu____7685 = (FStar_All.pipe_right lift1 FStar_Util.must)
in (FStar_All.pipe_right uu____7685 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____7682 FStar_List.length))
in (FStar_All.pipe_right uu____7681 FStar_Util.string_of_int))
in (FStar_Util.format3 "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes" uu____7678 uu____7679 uu____7680))))
in ((FStar_Errors.Fatal_TooManyUniverse), (uu____7677)))
in (FStar_Errors.raise_error uu____7672 r))
end
| uu____7724 -> begin
()
end));
(

let sub2 = (

let uu___89_7726 = sub1
in {FStar_Syntax_Syntax.source = uu___89_7726.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = uu___89_7726.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = FStar_Pervasives_Native.Some (lift_wp); FStar_Syntax_Syntax.lift = lift1})
in (

let se1 = (

let uu___90_7728 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_sub_effect (sub2); FStar_Syntax_Syntax.sigrng = uu___90_7728.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___90_7728.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___90_7728.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___90_7728.FStar_Syntax_Syntax.sigattrs})
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

let uu____7743 = (match ((Prims.op_Equality (FStar_List.length uvs) (Prims.parse_int "0"))) with
| true -> begin
((env1), (uvs), (tps), (c))
end
| uu____7767 -> begin
(

let uu____7768 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____7768) with
| (usubst, uvs1) -> begin
(

let tps1 = (FStar_Syntax_Subst.subst_binders usubst tps)
in (

let c1 = (

let uu____7799 = (FStar_Syntax_Subst.shift_subst (FStar_List.length tps1) usubst)
in (FStar_Syntax_Subst.subst_comp uu____7799 c))
in (

let uu____7806 = (FStar_TypeChecker_Env.push_univ_vars env1 uvs1)
in ((uu____7806), (uvs1), (tps1), (c1)))))
end))
end)
in (match (uu____7743) with
| (env2, uvs1, tps1, c1) -> begin
(

let env3 = (FStar_TypeChecker_Env.set_range env2 r)
in (

let uu____7826 = (FStar_Syntax_Subst.open_comp tps1 c1)
in (match (uu____7826) with
| (tps2, c2) -> begin
(

let uu____7841 = (FStar_TypeChecker_TcTerm.tc_tparams env3 tps2)
in (match (uu____7841) with
| (tps3, env4, us) -> begin
(

let uu____7859 = (FStar_TypeChecker_TcTerm.tc_comp env4 c2)
in (match (uu____7859) with
| (c3, u, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env4 g);
(

let tps4 = (FStar_Syntax_Subst.close_binders tps3)
in (

let c4 = (FStar_Syntax_Subst.close_comp tps4 c3)
in (

let uu____7880 = (

let uu____7881 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps4), (c4)))) FStar_Pervasives_Native.None r)
in (FStar_TypeChecker_Util.generalize_universes env0 uu____7881))
in (match (uu____7880) with
| (uvs2, t) -> begin
(

let uu____7908 = (

let uu____7921 = (

let uu____7932 = (

let uu____7933 = (FStar_Syntax_Subst.compress t)
in uu____7933.FStar_Syntax_Syntax.n)
in ((tps4), (uu____7932)))
in (match (uu____7921) with
| ([], FStar_Syntax_Syntax.Tm_arrow (uu____7954, c5)) -> begin
(([]), (c5))
end
| (uu____7994, FStar_Syntax_Syntax.Tm_arrow (tps5, c5)) -> begin
((tps5), (c5))
end
| uu____8033 -> begin
(failwith "Impossible (t is an arrow)")
end))
in (match (uu____7908) with
| (tps5, c5) -> begin
((match ((Prims.op_disEquality (FStar_List.length uvs2) (Prims.parse_int "1"))) with
| true -> begin
(

let uu____8084 = (FStar_Syntax_Subst.open_univ_vars uvs2 t)
in (match (uu____8084) with
| (uu____8089, t1) -> begin
(

let uu____8091 = (

let uu____8096 = (

let uu____8097 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____8098 = (FStar_All.pipe_right (FStar_List.length uvs2) FStar_Util.string_of_int)
in (

let uu____8099 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)" uu____8097 uu____8098 uu____8099))))
in ((FStar_Errors.Fatal_TooManyUniverse), (uu____8096)))
in (FStar_Errors.raise_error uu____8091 r))
end))
end
| uu____8100 -> begin
()
end);
(

let se1 = (

let uu___91_8102 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (((lid), (uvs2), (tps5), (c5), (flags1))); FStar_Syntax_Syntax.sigrng = uu___91_8102.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___91_8102.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___91_8102.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___91_8102.FStar_Syntax_Syntax.sigattrs})
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
| FStar_Syntax_Syntax.Sig_declare_typ (uu____8109, uu____8110, uu____8111) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___60_8115 -> (match (uu___60_8115) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____8116 -> begin
false
end)))) -> begin
(([]), ([]))
end
| FStar_Syntax_Syntax.Sig_let (uu____8121, uu____8122) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___60_8130 -> (match (uu___60_8130) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____8131 -> begin
false
end)))) -> begin
(([]), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_range env1 r)
in ((

let uu____8141 = (FStar_TypeChecker_Env.lid_exists env2 lid)
in (match (uu____8141) with
| true -> begin
(

let uu____8142 = (

let uu____8147 = (

let uu____8148 = (FStar_Ident.text_of_lid lid)
in (FStar_Util.format1 "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module" uu____8148))
in ((FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration), (uu____8147)))
in (FStar_Errors.raise_error uu____8142 r))
end
| uu____8149 -> begin
()
end));
(

let uu____8150 = (match ((Prims.op_Equality uvs [])) with
| true -> begin
(

let uu____8169 = (

let uu____8170 = (FStar_Syntax_Util.type_u ())
in (FStar_Pervasives_Native.fst uu____8170))
in (check_and_gen env2 t uu____8169))
end
| uu____8175 -> begin
(

let uu____8176 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____8176) with
| (uvs1, t1) -> begin
(

let env3 = (FStar_TypeChecker_Env.push_univ_vars env2 uvs1)
in (

let t2 = (

let uu____8193 = (

let uu____8194 = (FStar_Syntax_Util.type_u ())
in (FStar_Pervasives_Native.fst uu____8194))
in (tc_check_trivial_guard env3 t1 uu____8193))
in (

let t3 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.DoNotUnfoldPureLets)::[]) env3 t2)
in (

let uu____8200 = (FStar_Syntax_Subst.close_univ_vars uvs1 t3)
in ((uvs1), (uu____8200))))))
end))
end)
in (match (uu____8150) with
| (uvs1, t1) -> begin
(

let se1 = (

let uu___92_8220 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (uvs1), (t1))); FStar_Syntax_Syntax.sigrng = uu___92_8220.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___92_8220.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___92_8220.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___92_8220.FStar_Syntax_Syntax.sigattrs})
in (((se1)::[]), ([])))
end));
))
end
| FStar_Syntax_Syntax.Sig_assume (lid, us, phi) -> begin
(

let uu____8228 = (FStar_Syntax_Subst.open_univ_vars us phi)
in (match (uu____8228) with
| (us1, phi1) -> begin
(

let env2 = (FStar_TypeChecker_Env.push_univ_vars env1 us1)
in (

let phi2 = (

let uu____8245 = ((FStar_Options.use_two_phase_tc ()) && (FStar_TypeChecker_Env.should_verify env2))
in (match (uu____8245) with
| true -> begin
(

let phi2 = (

let uu____8247 = (tc_assume (

let uu___93_8250 = env2
in {FStar_TypeChecker_Env.solver = uu___93_8250.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___93_8250.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___93_8250.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___93_8250.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___93_8250.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___93_8250.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___93_8250.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___93_8250.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___93_8250.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___93_8250.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___93_8250.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___93_8250.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___93_8250.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___93_8250.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___93_8250.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___93_8250.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___93_8250.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___93_8250.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___93_8250.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___93_8250.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___93_8250.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___93_8250.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___93_8250.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___93_8250.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___93_8250.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___93_8250.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___93_8250.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___93_8250.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___93_8250.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___93_8250.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___93_8250.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___93_8250.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___93_8250.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___93_8250.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___93_8250.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___93_8250.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___93_8250.FStar_TypeChecker_Env.dep_graph}) phi1 r)
in (FStar_All.pipe_right uu____8247 (FStar_TypeChecker_Normalize.remove_uvar_solutions env2)))
in ((

let uu____8252 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("TwoPhases")))
in (match (uu____8252) with
| true -> begin
(

let uu____8253 = (FStar_Syntax_Print.term_to_string phi2)
in (FStar_Util.print1 "Assume after phase 1: %s\n" uu____8253))
end
| uu____8254 -> begin
()
end));
phi2;
))
end
| uu____8255 -> begin
phi1
end))
in (

let phi3 = (tc_assume env2 phi2 r)
in (

let uu____8257 = (match ((Prims.op_Equality us1 [])) with
| true -> begin
(FStar_TypeChecker_Util.generalize_universes env2 phi3)
end
| uu____8276 -> begin
(

let uu____8277 = (FStar_Syntax_Subst.close_univ_vars us1 phi3)
in ((us1), (uu____8277)))
end)
in (match (uu____8257) with
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

let uu____8303 = (FStar_TypeChecker_TcTerm.tc_term env3 e)
in (match (uu____8303) with
| (e1, c, g1) -> begin
(

let uu____8321 = (

let uu____8328 = (

let uu____8331 = (FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r)
in FStar_Pervasives_Native.Some (uu____8331))
in (

let uu____8332 = (

let uu____8337 = (FStar_Syntax_Syntax.lcomp_comp c)
in ((e1), (uu____8337)))
in (FStar_TypeChecker_TcTerm.check_expected_effect env3 uu____8328 uu____8332)))
in (match (uu____8321) with
| (e2, uu____8347, g) -> begin
((

let uu____8350 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env3 uu____8350));
(

let se1 = (

let uu___94_8352 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_main (e2); FStar_Syntax_Syntax.sigrng = uu___94_8352.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___94_8352.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___94_8352.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___94_8352.FStar_Syntax_Syntax.sigattrs})
in (((se1)::[]), ([])));
)
end))
end))))
end
| FStar_Syntax_Syntax.Sig_splice (lids, t) -> begin
((

let uu____8364 = (FStar_Options.debug_any ())
in (match (uu____8364) with
| true -> begin
(

let uu____8365 = (FStar_Ident.string_of_lid env1.FStar_TypeChecker_Env.curmodule)
in (

let uu____8366 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "%s: Found splice of (%s)\n" uu____8365 uu____8366)))
end
| uu____8367 -> begin
()
end));
(

let ses = (env1.FStar_TypeChecker_Env.splice env1 t)
in (

let lids' = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses)
in ((FStar_List.iter (fun lid -> (

let uu____8379 = (FStar_List.tryFind (FStar_Ident.lid_equals lid) lids')
in (match (uu____8379) with
| FStar_Pervasives_Native.Some (uu____8382) -> begin
()
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8383 = (

let uu____8388 = (

let uu____8389 = (FStar_Ident.string_of_lid lid)
in (

let uu____8390 = (

let uu____8391 = (FStar_List.map FStar_Ident.string_of_lid lids')
in (FStar_All.pipe_left (FStar_String.concat ", ") uu____8391))
in (FStar_Util.format2 "Splice declared the name %s but it was not defined.\nThose defined were: %s" uu____8389 uu____8390)))
in ((FStar_Errors.Fatal_SplicedUndef), (uu____8388)))
in (FStar_Errors.raise_error uu____8383 r))
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

let uu____8452 = ((Prims.op_Equality (FStar_List.length q) (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q'))
in (match (uu____8452) with
| true -> begin
FStar_Pervasives_Native.Some (q)
end
| uu____8459 -> begin
(

let uu____8460 = (

let uu____8465 = (

let uu____8466 = (FStar_Syntax_Print.lid_to_string l)
in (

let uu____8467 = (FStar_Syntax_Print.quals_to_string q)
in (

let uu____8468 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" uu____8466 uu____8467 uu____8468))))
in ((FStar_Errors.Fatal_InconsistentQualifierAnnotation), (uu____8465)))
in (FStar_Errors.raise_error uu____8460 r))
end))
end))
in (

let rename_parameters = (fun lb -> (

let rename_in_typ = (fun def typ -> (

let typ1 = (FStar_Syntax_Subst.compress typ)
in (

let def_bs = (

let uu____8500 = (

let uu____8501 = (FStar_Syntax_Subst.compress def)
in uu____8501.FStar_Syntax_Syntax.n)
in (match (uu____8500) with
| FStar_Syntax_Syntax.Tm_abs (binders, uu____8511, uu____8512) -> begin
binders
end
| uu____8533 -> begin
[]
end))
in (match (typ1) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow (val_bs, c); FStar_Syntax_Syntax.pos = r1; FStar_Syntax_Syntax.vars = uu____8543} -> begin
(

let has_auto_name = (fun bv -> (FStar_Util.starts_with bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Ident.reserved_prefix))
in (

let rec rename_binders1 = (fun def_bs1 val_bs1 -> (match (((def_bs1), (val_bs1))) with
| ([], uu____8627) -> begin
val_bs1
end
| (uu____8650, []) -> begin
val_bs1
end
| (((body_bv, uu____8674))::bt, ((val_bv, aqual))::vt) -> begin
(

let uu____8711 = (rename_binders1 bt vt)
in ((match ((((has_auto_name body_bv)), ((has_auto_name val_bv)))) with
| (true, uu____8727) -> begin
((val_bv), (aqual))
end
| (false, true) -> begin
(((

let uu___95_8729 = val_bv
in {FStar_Syntax_Syntax.ppname = (

let uu___96_8732 = val_bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = body_bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText; FStar_Ident.idRange = uu___96_8732.FStar_Ident.idRange}); FStar_Syntax_Syntax.index = uu___95_8729.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___95_8729.FStar_Syntax_Syntax.sort})), (aqual))
end
| (false, false) -> begin
((val_bv), (aqual))
end))::uu____8711)
end))
in (

let uu____8733 = (

let uu____8740 = (

let uu____8741 = (

let uu____8754 = (rename_binders1 def_bs val_bs)
in ((uu____8754), (c)))
in FStar_Syntax_Syntax.Tm_arrow (uu____8741))
in (FStar_Syntax_Syntax.mk uu____8740))
in (uu____8733 FStar_Pervasives_Native.None r1))))
end
| uu____8772 -> begin
typ1
end))))
in (

let uu___97_8773 = lb
in (

let uu____8774 = (rename_in_typ lb.FStar_Syntax_Syntax.lbdef lb.FStar_Syntax_Syntax.lbtyp)
in {FStar_Syntax_Syntax.lbname = uu___97_8773.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___97_8773.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____8774; FStar_Syntax_Syntax.lbeff = uu___97_8773.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___97_8773.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___97_8773.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___97_8773.FStar_Syntax_Syntax.lbpos}))))
in (

let uu____8777 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.fold_left (fun uu____8828 lb -> (match (uu____8828) with
| (gen1, lbs1, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____8870 = (

let uu____8881 = (FStar_TypeChecker_Env.try_lookup_val_decl env2 lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____8881) with
| FStar_Pervasives_Native.None -> begin
(match ((Prims.op_disEquality lb.FStar_Syntax_Syntax.lbunivs [])) with
| true -> begin
((false), (lb), (quals_opt))
end
| uu____8922 -> begin
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
| uu____8954 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((lb.FStar_Syntax_Syntax.lbdef), (((FStar_Util.Inl (lb.FStar_Syntax_Syntax.lbtyp)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.pos)
end)
in ((match (((Prims.op_disEquality lb.FStar_Syntax_Syntax.lbunivs []) && (Prims.op_disEquality (FStar_List.length lb.FStar_Syntax_Syntax.lbunivs) (FStar_List.length uvs)))) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_IncoherentInlineUniverse), ("Inline universes are incoherent with annotation from val declaration")) r)
end
| uu____8996 -> begin
()
end);
(

let uu____8997 = (FStar_Syntax_Syntax.mk_lb ((FStar_Util.Inr (lbname)), (uvs), (FStar_Parser_Const.effect_ALL_lid), (tval), (def), (lb.FStar_Syntax_Syntax.lbpos)))
in ((false), (uu____8997), (quals_opt1)));
)))
end))
in (match (uu____8870) with
| (gen2, lb1, quals_opt1) -> begin
((gen2), ((lb1)::lbs1), (quals_opt1))
end)))
end)) ((true), ([]), ((match ((Prims.op_Equality se.FStar_Syntax_Syntax.sigquals [])) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____9047 -> begin
FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
end)))))
in (match (uu____8777) with
| (should_generalize, lbs', quals_opt) -> begin
(

let quals = (match (quals_opt) with
| FStar_Pervasives_Native.None -> begin
(FStar_Syntax_Syntax.Visible_default)::[]
end
| FStar_Pervasives_Native.Some (q) -> begin
(

let uu____9085 = (FStar_All.pipe_right q (FStar_Util.for_some (fun uu___61_9089 -> (match (uu___61_9089) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| FStar_Syntax_Syntax.Visible_default -> begin
true
end
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____9090 -> begin
false
end))))
in (match (uu____9085) with
| true -> begin
q
end
| uu____9093 -> begin
(FStar_Syntax_Syntax.Visible_default)::q
end))
end)
in (

let lbs'1 = (FStar_List.rev lbs')
in (

let e = (

let uu____9100 = (

let uu____9107 = (

let uu____9108 = (

let uu____9121 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) FStar_Pervasives_Native.None r)
in (((((FStar_Pervasives_Native.fst lbs)), (lbs'1))), (uu____9121)))
in FStar_Syntax_Syntax.Tm_let (uu____9108))
in (FStar_Syntax_Syntax.mk uu____9107))
in (uu____9100 FStar_Pervasives_Native.None r))
in (

let env0 = (

let uu___98_9140 = env2
in {FStar_TypeChecker_Env.solver = uu___98_9140.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___98_9140.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___98_9140.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___98_9140.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___98_9140.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___98_9140.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___98_9140.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___98_9140.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___98_9140.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___98_9140.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___98_9140.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___98_9140.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = uu___98_9140.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = uu___98_9140.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___98_9140.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___98_9140.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___98_9140.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___98_9140.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___98_9140.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___98_9140.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___98_9140.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___98_9140.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___98_9140.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___98_9140.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___98_9140.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___98_9140.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___98_9140.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___98_9140.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___98_9140.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___98_9140.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___98_9140.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___98_9140.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___98_9140.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___98_9140.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___98_9140.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___98_9140.FStar_TypeChecker_Env.dep_graph})
in (

let e1 = (

let uu____9142 = ((FStar_Options.use_two_phase_tc ()) && (FStar_TypeChecker_Env.should_verify env0))
in (match (uu____9142) with
| true -> begin
(

let drop_lbtyp = (fun e_lax -> (

let uu____9149 = (

let uu____9150 = (FStar_Syntax_Subst.compress e_lax)
in uu____9150.FStar_Syntax_Syntax.n)
in (match (uu____9149) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let lb_unannotated = (

let uu____9168 = (

let uu____9169 = (FStar_Syntax_Subst.compress e)
in uu____9169.FStar_Syntax_Syntax.n)
in (match (uu____9168) with
| FStar_Syntax_Syntax.Tm_let ((uu____9172, (lb1)::[]), uu____9174) -> begin
(

let uu____9187 = (

let uu____9188 = (FStar_Syntax_Subst.compress lb1.FStar_Syntax_Syntax.lbtyp)
in uu____9188.FStar_Syntax_Syntax.n)
in (Prims.op_Equality uu____9187 FStar_Syntax_Syntax.Tm_unknown))
end
| uu____9191 -> begin
(failwith "Impossible: first phase lb and second phase lb differ in structure!")
end))
in (match (lb_unannotated) with
| true -> begin
(

let uu___99_9192 = e_lax
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (((((false), (((

let uu___100_9204 = lb
in {FStar_Syntax_Syntax.lbname = uu___100_9204.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___100_9204.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = uu___100_9204.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___100_9204.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___100_9204.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___100_9204.FStar_Syntax_Syntax.lbpos}))::[]))), (e2))); FStar_Syntax_Syntax.pos = uu___99_9192.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___99_9192.FStar_Syntax_Syntax.vars})
end
| uu____9205 -> begin
e_lax
end))
end
| uu____9206 -> begin
e_lax
end)))
in (

let e1 = (

let uu____9208 = (

let uu____9209 = (

let uu____9210 = (FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term (

let uu___101_9219 = env0
in {FStar_TypeChecker_Env.solver = uu___101_9219.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___101_9219.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___101_9219.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___101_9219.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___101_9219.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___101_9219.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___101_9219.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___101_9219.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___101_9219.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___101_9219.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___101_9219.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___101_9219.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___101_9219.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___101_9219.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___101_9219.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___101_9219.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___101_9219.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___101_9219.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___101_9219.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___101_9219.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___101_9219.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___101_9219.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___101_9219.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___101_9219.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___101_9219.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___101_9219.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___101_9219.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___101_9219.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___101_9219.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___101_9219.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___101_9219.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___101_9219.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___101_9219.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___101_9219.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___101_9219.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___101_9219.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___101_9219.FStar_TypeChecker_Env.dep_graph}) e)
in (FStar_All.pipe_right uu____9210 (fun uu____9230 -> (match (uu____9230) with
| (e1, uu____9238, uu____9239) -> begin
e1
end))))
in (FStar_All.pipe_right uu____9209 (FStar_TypeChecker_Normalize.remove_uvar_solutions env0)))
in (FStar_All.pipe_right uu____9208 drop_lbtyp))
in ((

let uu____9241 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("TwoPhases")))
in (match (uu____9241) with
| true -> begin
(

let uu____9242 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.print1 "Let binding after phase 1: %s\n" uu____9242))
end
| uu____9243 -> begin
()
end));
e1;
)))
end
| uu____9244 -> begin
e
end))
in (

let uu____9245 = (

let uu____9256 = (FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term env0 e1)
in (match (uu____9256) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs1, e2); FStar_Syntax_Syntax.pos = uu____9275; FStar_Syntax_Syntax.vars = uu____9276}, uu____9277, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let lbs2 = (

let uu____9304 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1) (FStar_List.map rename_parameters))
in (((FStar_Pervasives_Native.fst lbs1)), (uu____9304)))
in (

let quals1 = (match (e2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (uu____9322, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| uu____9327 -> begin
quals
end)
in (((

let uu___102_9335 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((lbs2), (lids))); FStar_Syntax_Syntax.sigrng = uu___102_9335.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = uu___102_9335.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___102_9335.FStar_Syntax_Syntax.sigattrs})), (lbs2))))
end
| uu____9338 -> begin
(failwith "impossible (typechecking should preserve Tm_let)")
end))
in (match (uu____9245) with
| (se1, lbs1) -> begin
((FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1) (FStar_List.iter (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (FStar_TypeChecker_Env.insert_fv_info env2 fv lb.FStar_Syntax_Syntax.lbtyp)))));
(

let uu____9387 = (log env2)
in (match (uu____9387) with
| true -> begin
(

let uu____9388 = (

let uu____9389 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1) (FStar_List.map (fun lb -> (

let should_log = (

let uu____9404 = (

let uu____9413 = (

let uu____9414 = (

let uu____9417 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____9417.FStar_Syntax_Syntax.fv_name)
in uu____9414.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env2 uu____9413))
in (match (uu____9404) with
| FStar_Pervasives_Native.None -> begin
true
end
| uu____9424 -> begin
false
end))
in (match (should_log) with
| true -> begin
(

let uu____9433 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____9434 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" uu____9433 uu____9434)))
end
| uu____9435 -> begin
""
end)))))
in (FStar_All.pipe_right uu____9389 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" uu____9388))
end
| uu____9438 -> begin
()
end));
(((se1)::[]), ([]));
)
end)))))))
end)))))
end));
)))


let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___62_9486 -> (match (uu___62_9486) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| uu____9487 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| FStar_Syntax_Syntax.Projector (l, uu____9495) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| FStar_Syntax_Syntax.Discriminator (l) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| uu____9501 -> begin
false
end))
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_pragma (uu____9510) -> begin
(([]), (hidden))
end
| FStar_Syntax_Syntax.Sig_splice (uu____9515) -> begin
(failwith "Impossible (Already handled)")
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____9530) -> begin
(failwith "Impossible (Already handled)")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____9555) -> begin
(failwith "Impossible (Already handled)")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____9579) -> begin
(

let uu____9588 = (is_abstract se.FStar_Syntax_Syntax.sigquals)
in (match (uu____9588) with
| true -> begin
(

let for_export_bundle = (fun se1 uu____9623 -> (match (uu____9623) with
| (out, hidden1) -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, uu____9662, uu____9663) -> begin
(

let dec = (

let uu___103_9673 = se1
in (

let uu____9674 = (

let uu____9675 = (

let uu____9682 = (

let uu____9683 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow bs uu____9683))
in ((l), (us), (uu____9682)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____9675))
in {FStar_Syntax_Syntax.sigel = uu____9674; FStar_Syntax_Syntax.sigrng = uu___103_9673.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::se1.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___103_9673.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___103_9673.FStar_Syntax_Syntax.sigattrs}))
in (((dec)::out), (hidden1)))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, uu____9693, uu____9694, uu____9695) -> begin
(

let dec = (

let uu___104_9701 = se1
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t))); FStar_Syntax_Syntax.sigrng = uu___104_9701.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::[]; FStar_Syntax_Syntax.sigmeta = uu___104_9701.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___104_9701.FStar_Syntax_Syntax.sigattrs})
in (((dec)::out), ((l)::hidden1)))
end
| uu____9706 -> begin
((out), (hidden1))
end)
end))
in (FStar_List.fold_right for_export_bundle ses (([]), (hidden))))
end
| uu____9723 -> begin
(((se)::[]), (hidden))
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____9728, uu____9729, uu____9730) -> begin
(

let uu____9731 = (is_abstract se.FStar_Syntax_Syntax.sigquals)
in (match (uu____9731) with
| true -> begin
(([]), (hidden))
end
| uu____9744 -> begin
(((se)::[]), (hidden))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, us, t) -> begin
(

let uu____9752 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some is_hidden_proj_or_disc))
in (match (uu____9752) with
| true -> begin
((((

let uu___105_9768 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t))); FStar_Syntax_Syntax.sigrng = uu___105_9768.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::[]; FStar_Syntax_Syntax.sigmeta = uu___105_9768.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___105_9768.FStar_Syntax_Syntax.sigattrs}))::[]), ((l)::hidden))
end
| uu____9769 -> begin
(

let uu____9770 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___63_9774 -> (match (uu___63_9774) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____9775) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____9780) -> begin
true
end
| uu____9781 -> begin
false
end))))
in (match (uu____9770) with
| true -> begin
(((se)::[]), (hidden))
end
| uu____9794 -> begin
(([]), (hidden))
end))
end))
end
| FStar_Syntax_Syntax.Sig_main (uu____9799) -> begin
(([]), (hidden))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____9804) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____9809) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____9814) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____9819) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____9837) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____9848 = (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
in (match (uu____9848) with
| true -> begin
(([]), (hidden))
end
| uu____9863 -> begin
(

let dec = (

let uu____9865 = (FStar_Ident.range_of_lid lid)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu____9865; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::[]; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (((dec)::[]), ((lid)::hidden)))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, l) -> begin
(

let uu____9876 = (is_abstract se.FStar_Syntax_Syntax.sigquals)
in (match (uu____9876) with
| true -> begin
(

let uu____9885 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let uu___106_9898 = se
in (

let uu____9899 = (

let uu____9900 = (

let uu____9907 = (

let uu____9908 = (

let uu____9911 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____9911.FStar_Syntax_Syntax.fv_name)
in uu____9908.FStar_Syntax_Syntax.v)
in ((uu____9907), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____9900))
in {FStar_Syntax_Syntax.sigel = uu____9899; FStar_Syntax_Syntax.sigrng = uu___106_9898.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___106_9898.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___106_9898.FStar_Syntax_Syntax.sigattrs})))))
in ((uu____9885), (hidden)))
end
| uu____9916 -> begin
(((se)::[]), (hidden))
end))
end))))


let add_sigelt_to_env : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____9931) -> begin
(failwith "add_sigelt_to_env: Impossible, bare data constructor")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____9948) -> begin
(failwith "add_sigelt_to_env: Impossible, bare data constructor")
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (uu____9963)) -> begin
(z3_reset_options env)
end
| FStar_Syntax_Syntax.Sig_pragma (uu____9966) -> begin
env
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____9967) -> begin
env
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_sigelt env se)
in (FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun env2 a -> (

let uu____9977 = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Env.push_sigelt env2 uu____9977))) env1)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____9978, uu____9979, uu____9980) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___64_9984 -> (match (uu___64_9984) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____9985 -> begin
false
end)))) -> begin
env
end
| FStar_Syntax_Syntax.Sig_let (uu____9986, uu____9987) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___64_9995 -> (match (uu___64_9995) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____9996 -> begin
false
end)))) -> begin
env
end
| uu____9997 -> begin
(FStar_TypeChecker_Env.push_sigelt env se)
end))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let rec process_one_decl = (fun uu____10065 se -> (match (uu____10065) with
| (ses1, exports, env1, hidden) -> begin
((

let uu____10118 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____10118) with
| true -> begin
(

let uu____10119 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____10119))
end
| uu____10120 -> begin
()
end));
(

let uu____10121 = (tc_decl env1 se)
in (match (uu____10121) with
| (ses', ses_elaborated) -> begin
(

let ses'1 = (FStar_All.pipe_right ses' (FStar_List.map (fun se1 -> ((

let uu____10171 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("UF")))
in (match (uu____10171) with
| true -> begin
(

let uu____10172 = (FStar_Syntax_Print.sigelt_to_string se1)
in (FStar_Util.print1 "About to elim vars from %s" uu____10172))
end
| uu____10173 -> begin
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

let uu____10195 = ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("LogTypes"))))
in (match (uu____10195) with
| true -> begin
(

let uu____10196 = (FStar_List.fold_left (fun s se1 -> (

let uu____10202 = (

let uu____10203 = (FStar_Syntax_Print.sigelt_to_string se1)
in (Prims.strcat uu____10203 "\n"))
in (Prims.strcat s uu____10202))) "" ses'1)
in (FStar_Util.print1 "Checked: %s\n" uu____10196))
end
| uu____10204 -> begin
()
end));
(FStar_List.iter (fun se1 -> (env2.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env2 se1)) ses'1);
(

let uu____10208 = (

let uu____10217 = (FStar_Options.use_extracted_interfaces ())
in (match (uu____10217) with
| true -> begin
(([]), ([]))
end
| uu____10230 -> begin
(

let accum_exports_hidden = (fun uu____10256 se1 -> (match (uu____10256) with
| (exports1, hidden1) -> begin
(

let uu____10284 = (for_export hidden1 se1)
in (match (uu____10284) with
| (se_exported, hidden2) -> begin
(((FStar_List.rev_append se_exported exports1)), (hidden2))
end))
end))
in (FStar_List.fold_left accum_exports_hidden ((exports), (hidden)) ses'1))
end))
in (match (uu____10208) with
| (exports1, hidden1) -> begin
(

let ses'2 = (FStar_List.map (fun s -> (

let uu___107_10363 = s
in {FStar_Syntax_Syntax.sigel = uu___107_10363.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___107_10363.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___107_10363.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___107_10363.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = se.FStar_Syntax_Syntax.sigattrs})) ses'1)
in (((((FStar_List.rev_append ses'2 ses1)), (exports1), (env2), (hidden1))), (ses_elaborated1)))
end));
));
)))
end));
)
end))
in (

let process_one_decl_timed = (fun acc se -> (

let uu____10445 = acc
in (match (uu____10445) with
| (uu____10480, uu____10481, env1, uu____10483) -> begin
(

let uu____10496 = (FStar_Util.record_time (fun uu____10542 -> (process_one_decl acc se)))
in (match (uu____10496) with
| (r, ms_elapsed) -> begin
((

let uu____10606 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("TCDeclTime")))
in (match (uu____10606) with
| true -> begin
(

let uu____10607 = (FStar_Syntax_Print.sigelt_to_string_short se)
in (

let uu____10608 = (FStar_Util.string_of_int ms_elapsed)
in (FStar_Util.print2 "Checked %s in %s milliseconds\n" uu____10607 uu____10608)))
end
| uu____10609 -> begin
()
end));
r;
)
end))
end)))
in (

let uu____10610 = (FStar_Util.fold_flatten process_one_decl_timed (([]), ([]), (env), ([])) ses)
in (match (uu____10610) with
| (ses1, exports, env1, uu____10658) -> begin
(((FStar_List.rev_append ses1 [])), ((FStar_List.rev_append exports [])), (env1))
end)))))


let check_exports : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  unit = (fun env modul exports -> (

let env1 = (

let uu___108_10695 = env
in {FStar_TypeChecker_Env.solver = uu___108_10695.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___108_10695.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___108_10695.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___108_10695.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___108_10695.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___108_10695.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___108_10695.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___108_10695.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___108_10695.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___108_10695.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___108_10695.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___108_10695.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___108_10695.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___108_10695.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = uu___108_10695.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___108_10695.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___108_10695.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___108_10695.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = true; FStar_TypeChecker_Env.failhard = uu___108_10695.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___108_10695.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___108_10695.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___108_10695.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___108_10695.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___108_10695.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___108_10695.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___108_10695.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___108_10695.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___108_10695.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___108_10695.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___108_10695.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___108_10695.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___108_10695.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___108_10695.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___108_10695.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___108_10695.FStar_TypeChecker_Env.dep_graph})
in (

let check_term = (fun lid univs1 t -> (

let uu____10712 = (FStar_Syntax_Subst.open_univ_vars univs1 t)
in (match (uu____10712) with
| (univs2, t1) -> begin
((

let uu____10720 = (

let uu____10721 = (

let uu____10726 = (FStar_TypeChecker_Env.set_current_module env1 modul.FStar_Syntax_Syntax.name)
in (FStar_TypeChecker_Env.debug uu____10726))
in (FStar_All.pipe_left uu____10721 (FStar_Options.Other ("Exports"))))
in (match (uu____10720) with
| true -> begin
(

let uu____10727 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____10728 = (

let uu____10729 = (FStar_All.pipe_right univs2 (FStar_List.map (fun x -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (x))))))
in (FStar_All.pipe_right uu____10729 (FStar_String.concat ", ")))
in (

let uu____10740 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Checking for export %s <%s> : %s\n" uu____10727 uu____10728 uu____10740))))
end
| uu____10741 -> begin
()
end));
(

let env2 = (FStar_TypeChecker_Env.push_univ_vars env1 univs2)
in (

let uu____10743 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1)
in (FStar_All.pipe_right uu____10743 (fun a239 -> ()))));
)
end)))
in (

let check_term1 = (fun lid univs1 t -> ((

let uu____10769 = (

let uu____10770 = (FStar_Syntax_Print.lid_to_string modul.FStar_Syntax_Syntax.name)
in (

let uu____10771 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Interface of %s violates its abstraction (add a \'private\' qualifier to \'%s\'?)" uu____10770 uu____10771)))
in (FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____10769));
(check_term lid univs1 t);
(FStar_Errors.message_prefix.FStar_Errors.clear_prefix ());
))
in (

let rec check_sigelt = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____10780) -> begin
(

let uu____10789 = (

let uu____10790 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____10790)))
in (match (uu____10789) with
| true -> begin
(FStar_All.pipe_right ses (FStar_List.iter check_sigelt))
end
| uu____10795 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (l, univs1, binders, typ, uu____10800, uu____10801) -> begin
(

let t = (

let uu____10813 = (

let uu____10820 = (

let uu____10821 = (

let uu____10834 = (FStar_Syntax_Syntax.mk_Total typ)
in ((binders), (uu____10834)))
in FStar_Syntax_Syntax.Tm_arrow (uu____10821))
in (FStar_Syntax_Syntax.mk uu____10820))
in (uu____10813 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng))
in (check_term1 l univs1 t))
end
| FStar_Syntax_Syntax.Sig_datacon (l, univs1, t, uu____10851, uu____10852, uu____10853) -> begin
(check_term1 l univs1 t)
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, univs1, t) -> begin
(

let uu____10861 = (

let uu____10862 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____10862)))
in (match (uu____10861) with
| true -> begin
(check_term1 l univs1 t)
end
| uu____10865 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_let ((uu____10866, lbs), uu____10868) -> begin
(

let uu____10877 = (

let uu____10878 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____10878)))
in (match (uu____10877) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (check_term1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp)))))
end
| uu____10887 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs1, binders, comp, flags1) -> begin
(

let uu____10897 = (

let uu____10898 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____10898)))
in (match (uu____10897) with
| true -> begin
(

let arrow1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))) FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng)
in (check_term1 l univs1 arrow1))
end
| uu____10912 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_main (uu____10913) -> begin
()
end
| FStar_Syntax_Syntax.Sig_assume (uu____10914) -> begin
()
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____10921) -> begin
()
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____10922) -> begin
()
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____10923) -> begin
()
end
| FStar_Syntax_Syntax.Sig_splice (uu____10924) -> begin
()
end
| FStar_Syntax_Syntax.Sig_pragma (uu____10931) -> begin
()
end))
in (

let uu____10932 = (FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Parser_Const.prims_lid)
in (match (uu____10932) with
| true -> begin
()
end
| uu____10933 -> begin
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
| FStar_Syntax_Syntax.Projector (l, uu____11027) -> begin
true
end
| uu____11028 -> begin
false
end)) quals))
in (

let vals_of_abstract_inductive = (fun s -> (

let mk_typ_for_abstract_inductive = (fun bs t r -> (match (bs) with
| [] -> begin
t
end
| uu____11055 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs', c) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((((FStar_List.append bs bs')), (c)))) FStar_Pervasives_Native.None r)
end
| uu____11086 -> begin
(

let uu____11087 = (

let uu____11094 = (

let uu____11095 = (

let uu____11108 = (FStar_Syntax_Syntax.mk_Total t)
in ((bs), (uu____11108)))
in FStar_Syntax_Syntax.Tm_arrow (uu____11095))
in (FStar_Syntax_Syntax.mk uu____11094))
in (uu____11087 FStar_Pervasives_Native.None r))
end)
end))
in (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, bs, t, uu____11126, uu____11127) -> begin
(

let s1 = (

let uu___109_11137 = s
in (

let uu____11138 = (

let uu____11139 = (

let uu____11146 = (mk_typ_for_abstract_inductive bs t s.FStar_Syntax_Syntax.sigrng)
in ((lid), (uvs), (uu____11146)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____11139))
in (

let uu____11147 = (

let uu____11150 = (

let uu____11153 = (filter_out_abstract_and_noeq s.FStar_Syntax_Syntax.sigquals)
in (FStar_Syntax_Syntax.New)::uu____11153)
in (FStar_Syntax_Syntax.Assumption)::uu____11150)
in {FStar_Syntax_Syntax.sigel = uu____11138; FStar_Syntax_Syntax.sigrng = uu___109_11137.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu____11147; FStar_Syntax_Syntax.sigmeta = uu___109_11137.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___109_11137.FStar_Syntax_Syntax.sigattrs})))
in (s1)::[])
end
| uu____11156 -> begin
(failwith "Impossible!")
end)))
in (

let val_of_lb = (fun s lid uu____11180 lbdef -> (match (uu____11180) with
| (uvs, t) -> begin
(

let attrs = (

let uu____11191 = (FStar_TypeChecker_Util.must_erase_for_extraction en lbdef)
in (match (uu____11191) with
| true -> begin
(

let uu____11194 = (

let uu____11195 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.must_erase_for_extraction_attr FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_All.pipe_right uu____11195 FStar_Syntax_Syntax.fv_to_tm))
in (uu____11194)::s.FStar_Syntax_Syntax.sigattrs)
end
| uu____11196 -> begin
s.FStar_Syntax_Syntax.sigattrs
end))
in (

let uu___110_11197 = s
in (

let uu____11198 = (

let uu____11201 = (filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals)
in (FStar_Syntax_Syntax.Assumption)::uu____11201)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (uvs), (t))); FStar_Syntax_Syntax.sigrng = uu___110_11197.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu____11198; FStar_Syntax_Syntax.sigmeta = uu___110_11197.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = attrs})))
end))
in (

let should_keep_lbdef = (fun t -> (

let comp_effect_name1 = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
c1.FStar_Syntax_Syntax.effect_name
end
| uu____11217 -> begin
(failwith "Impossible!")
end))
in (

let c_opt = (

let uu____11223 = (FStar_Syntax_Util.is_unit t)
in (match (uu____11223) with
| true -> begin
(

let uu____11228 = (FStar_Syntax_Syntax.mk_Total t)
in FStar_Pervasives_Native.Some (uu____11228))
end
| uu____11233 -> begin
(

let uu____11234 = (

let uu____11235 = (FStar_Syntax_Subst.compress t)
in uu____11235.FStar_Syntax_Syntax.n)
in (match (uu____11234) with
| FStar_Syntax_Syntax.Tm_arrow (uu____11242, c) -> begin
FStar_Pervasives_Native.Some (c)
end
| uu____11262 -> begin
FStar_Pervasives_Native.None
end))
end))
in ((Prims.op_Equality c_opt FStar_Pervasives_Native.None) || (

let c = (FStar_All.pipe_right c_opt FStar_Util.must)
in (

let uu____11285 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (match (uu____11285) with
| true -> begin
(

let uu____11286 = (

let uu____11287 = (FStar_All.pipe_right c FStar_Syntax_Util.comp_result)
in (FStar_All.pipe_right uu____11287 FStar_Syntax_Util.is_unit))
in (not (uu____11286)))
end
| uu____11290 -> begin
(

let uu____11291 = (comp_effect_name1 c)
in (FStar_TypeChecker_Env.is_reifiable_effect en uu____11291))
end)))))))
in (

let extract_sigelt = (fun s -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____11302) -> begin
(failwith "Impossible! extract_interface: bare data constructor")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____11321) -> begin
(failwith "Impossible! extract_interface: bare data constructor")
end
| FStar_Syntax_Syntax.Sig_splice (uu____11338) -> begin
(failwith "Impossible! extract_interface: trying to extract splice")
end
| FStar_Syntax_Syntax.Sig_bundle (sigelts, lidents1) -> begin
(match ((is_abstract s.FStar_Syntax_Syntax.sigquals)) with
| true -> begin
(FStar_All.pipe_right sigelts (FStar_List.fold_left (fun sigelts1 s1 -> (match (s1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____11382, uu____11383, uu____11384, uu____11385, uu____11386) -> begin
((

let uu____11396 = (

let uu____11399 = (FStar_ST.op_Bang abstract_inductive_tycons)
in (lid)::uu____11399)
in (FStar_ST.op_Colon_Equals abstract_inductive_tycons uu____11396));
(

let uu____11500 = (vals_of_abstract_inductive s1)
in (FStar_List.append uu____11500 sigelts1));
)
end
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____11504, uu____11505, uu____11506, uu____11507, uu____11508) -> begin
((

let uu____11514 = (

let uu____11517 = (FStar_ST.op_Bang abstract_inductive_datacons)
in (lid)::uu____11517)
in (FStar_ST.op_Colon_Equals abstract_inductive_datacons uu____11514));
sigelts1;
)
end
| uu____11618 -> begin
(failwith "Impossible! extract_interface: Sig_bundle can\'t have anything other than Sig_inductive_typ and Sig_datacon")
end)) []))
end
| uu____11621 -> begin
(s)::[]
end)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) -> begin
(

let uu____11625 = (is_projector_or_discriminator_of_an_abstract_inductive s.FStar_Syntax_Syntax.sigquals)
in (match (uu____11625) with
| true -> begin
[]
end
| uu____11628 -> begin
(match ((is_assume s.FStar_Syntax_Syntax.sigquals)) with
| true -> begin
(

let uu____11631 = (

let uu___111_11632 = s
in (

let uu____11633 = (filter_out_abstract s.FStar_Syntax_Syntax.sigquals)
in {FStar_Syntax_Syntax.sigel = uu___111_11632.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___111_11632.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu____11633; FStar_Syntax_Syntax.sigmeta = uu___111_11632.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___111_11632.FStar_Syntax_Syntax.sigattrs}))
in (uu____11631)::[])
end
| uu____11636 -> begin
[]
end)
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, lids) -> begin
(

let uu____11643 = (is_projector_or_discriminator_of_an_abstract_inductive s.FStar_Syntax_Syntax.sigquals)
in (match (uu____11643) with
| true -> begin
[]
end
| uu____11646 -> begin
(

let uu____11647 = lbs
in (match (uu____11647) with
| (flbs, slbs) -> begin
(

let typs_and_defs = (FStar_All.pipe_right slbs (FStar_List.map (fun lb -> ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (lb.FStar_Syntax_Syntax.lbdef)))))
in (

let is_lemma1 = (FStar_List.existsML (fun uu____11706 -> (match (uu____11706) with
| (uu____11713, t, uu____11715) -> begin
(FStar_All.pipe_right t FStar_Syntax_Util.is_lemma)
end)) typs_and_defs)
in (

let vals = (FStar_List.map2 (fun lid uu____11731 -> (match (uu____11731) with
| (u, t, d) -> begin
(val_of_lb s lid ((u), (t)) d)
end)) lids typs_and_defs)
in (match ((((is_abstract s.FStar_Syntax_Syntax.sigquals) || (is_irreducible1 s.FStar_Syntax_Syntax.sigquals)) || is_lemma1)) with
| true -> begin
vals
end
| uu____11743 -> begin
(

let should_keep_defs = (FStar_List.existsML (fun uu____11755 -> (match (uu____11755) with
| (uu____11762, t, uu____11764) -> begin
(FStar_All.pipe_right t should_keep_lbdef)
end)) typs_and_defs)
in (match (should_keep_defs) with
| true -> begin
(s)::[]
end
| uu____11767 -> begin
vals
end))
end))))
end))
end))
end
| FStar_Syntax_Syntax.Sig_main (t) -> begin
(failwith "Did not anticipate main would arise when extracting interfaces!")
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____11772, uu____11773) -> begin
(

let is_haseq = (FStar_TypeChecker_TcInductive.is_haseq_lid lid)
in (match (is_haseq) with
| true -> begin
(

let is_haseq_of_abstract_inductive = (

let uu____11778 = (FStar_ST.op_Bang abstract_inductive_tycons)
in (FStar_List.existsML (fun l -> (

let uu____11833 = (FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l)
in (FStar_Ident.lid_equals lid uu____11833))) uu____11778))
in (match (is_haseq_of_abstract_inductive) with
| true -> begin
(

let uu____11836 = (

let uu___112_11837 = s
in (

let uu____11838 = (filter_out_abstract s.FStar_Syntax_Syntax.sigquals)
in {FStar_Syntax_Syntax.sigel = uu___112_11837.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___112_11837.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu____11838; FStar_Syntax_Syntax.sigmeta = uu___112_11837.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___112_11837.FStar_Syntax_Syntax.sigattrs}))
in (uu____11836)::[])
end
| uu____11841 -> begin
[]
end))
end
| uu____11842 -> begin
(

let uu____11843 = (

let uu___113_11844 = s
in (

let uu____11845 = (filter_out_abstract s.FStar_Syntax_Syntax.sigquals)
in {FStar_Syntax_Syntax.sigel = uu___113_11844.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___113_11844.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu____11845; FStar_Syntax_Syntax.sigmeta = uu___113_11844.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___113_11844.FStar_Syntax_Syntax.sigattrs}))
in (uu____11843)::[])
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____11848) -> begin
(s)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____11849) -> begin
(s)::[]
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____11850) -> begin
(s)::[]
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____11851) -> begin
(s)::[]
end
| FStar_Syntax_Syntax.Sig_pragma (uu____11864) -> begin
(s)::[]
end))
in (

let uu___114_11865 = m
in (

let uu____11866 = (

let uu____11867 = (FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations (FStar_List.map extract_sigelt))
in (FStar_All.pipe_right uu____11867 FStar_List.flatten))
in {FStar_Syntax_Syntax.name = uu___114_11865.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu____11866; FStar_Syntax_Syntax.exports = uu___114_11865.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = true}))))))))))))))))


let pop_context : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Env.env = (fun env msg -> ((

let uu____11895 = (FStar_Syntax_DsEnv.pop ())
in (FStar_All.pipe_right uu____11895 (fun a240 -> ())));
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

let uu___115_11910 = env1
in {FStar_TypeChecker_Env.solver = uu___115_11910.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___115_11910.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___115_11910.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___115_11910.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___115_11910.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___115_11910.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___115_11910.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___115_11910.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___115_11910.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___115_11910.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___115_11910.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___115_11910.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___115_11910.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___115_11910.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___115_11910.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___115_11910.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___115_11910.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___115_11910.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___115_11910.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___115_11910.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___115_11910.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___115_11910.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___115_11910.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___115_11910.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___115_11910.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___115_11910.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___115_11910.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___115_11910.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___115_11910.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___115_11910.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___115_11910.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___115_11910.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___115_11910.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___115_11910.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___115_11910.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___115_11910.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = dsenv1; FStar_TypeChecker_Env.dep_graph = uu___115_11910.FStar_TypeChecker_Env.dep_graph}))))


let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (

let verify = (FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let action = (match (verify) with
| true -> begin
"Verifying"
end
| uu____11931 -> begin
"Lax-checking"
end)
in (

let label1 = (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____11933 -> begin
"implementation"
end)
in ((

let uu____11935 = (FStar_Options.debug_any ())
in (match (uu____11935) with
| true -> begin
(FStar_Util.print3 "%s %s of %s\n" action label1 modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
end
| uu____11936 -> begin
()
end));
(

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____11938 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let env1 = (

let uu___116_11940 = env
in {FStar_TypeChecker_Env.solver = uu___116_11940.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___116_11940.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___116_11940.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___116_11940.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___116_11940.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___116_11940.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___116_11940.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___116_11940.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___116_11940.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___116_11940.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___116_11940.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___116_11940.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___116_11940.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___116_11940.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___116_11940.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___116_11940.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___116_11940.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = (not (verify)); FStar_TypeChecker_Env.lax = uu___116_11940.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___116_11940.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___116_11940.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___116_11940.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___116_11940.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___116_11940.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___116_11940.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___116_11940.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___116_11940.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___116_11940.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___116_11940.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___116_11940.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___116_11940.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___116_11940.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___116_11940.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___116_11940.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___116_11940.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___116_11940.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___116_11940.FStar_TypeChecker_Env.dep_graph})
in (

let env2 = (FStar_TypeChecker_Env.set_current_module env1 modul.FStar_Syntax_Syntax.name)
in (

let uu____11942 = (tc_decls env2 modul.FStar_Syntax_Syntax.declarations)
in (match (uu____11942) with
| (ses, exports, env3) -> begin
(((

let uu___117_11975 = modul
in {FStar_Syntax_Syntax.name = uu___117_11975.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = uu___117_11975.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___117_11975.FStar_Syntax_Syntax.is_interface})), (exports), (env3))
end)))));
)))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let uu____12003 = (tc_decls env decls)
in (match (uu____12003) with
| (ses, exports, env1) -> begin
(

let modul1 = (

let uu___118_12034 = modul
in {FStar_Syntax_Syntax.name = uu___118_12034.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = uu___118_12034.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___118_12034.FStar_Syntax_Syntax.is_interface})
in ((modul1), (exports), (env1)))
end)))


let rec tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_TypeChecker_Env.env) = (fun env0 m -> (

let msg = (Prims.strcat "Internals for " m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let env01 = (push_context env0 msg)
in (

let uu____12091 = (tc_partial_modul env01 m)
in (match (uu____12091) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul false env modul non_private_decls)
end)))))
and finish_partial_modul : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_TypeChecker_Env.env) = (fun loading_from_cache en m exports -> (

let uu____12129 = (((not (loading_from_cache)) && (FStar_Options.use_extracted_interfaces ())) && (not (m.FStar_Syntax_Syntax.is_interface)))
in (match (uu____12129) with
| true -> begin
(

let modul_iface = (extract_interface en m)
in ((

let uu____12140 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug en) FStar_Options.Low)
in (match (uu____12140) with
| true -> begin
(

let uu____12141 = (

let uu____12142 = (FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____12142) with
| true -> begin
""
end
| uu____12143 -> begin
" (in lax mode) "
end))
in (

let uu____12144 = (

let uu____12145 = (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____12145) with
| true -> begin
(

let uu____12146 = (

let uu____12147 = (FStar_Syntax_Print.modul_to_string m)
in (Prims.strcat uu____12147 "\n"))
in (Prims.strcat "\nfrom: " uu____12146))
end
| uu____12148 -> begin
""
end))
in (

let uu____12149 = (

let uu____12150 = (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____12150) with
| true -> begin
(

let uu____12151 = (

let uu____12152 = (FStar_Syntax_Print.modul_to_string modul_iface)
in (Prims.strcat uu____12152 "\n"))
in (Prims.strcat "\nto: " uu____12151))
end
| uu____12153 -> begin
""
end))
in (FStar_Util.print4 "Extracting and type checking module %s interface%s%s%s\n" m.FStar_Syntax_Syntax.name.FStar_Ident.str uu____12141 uu____12144 uu____12149))))
end
| uu____12154 -> begin
()
end));
(

let en0 = (

let en0 = (pop_context en (Prims.strcat "Ending modul " m.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (

let en01 = (

let uu___119_12158 = en0
in (

let uu____12159 = (

let uu____12172 = (FStar_All.pipe_right en.FStar_TypeChecker_Env.qtbl_name_and_index FStar_Pervasives_Native.fst)
in ((uu____12172), (FStar_Pervasives_Native.None)))
in {FStar_TypeChecker_Env.solver = uu___119_12158.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___119_12158.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___119_12158.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___119_12158.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___119_12158.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___119_12158.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___119_12158.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___119_12158.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___119_12158.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___119_12158.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___119_12158.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___119_12158.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___119_12158.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___119_12158.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___119_12158.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___119_12158.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___119_12158.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___119_12158.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___119_12158.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___119_12158.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___119_12158.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___119_12158.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___119_12158.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___119_12158.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___119_12158.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___119_12158.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___119_12158.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___119_12158.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu____12159; FStar_TypeChecker_Env.normalized_eff_names = uu___119_12158.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___119_12158.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___119_12158.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___119_12158.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___119_12158.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___119_12158.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___119_12158.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___119_12158.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___119_12158.FStar_TypeChecker_Env.dep_graph}))
in (

let uu____12209 = (

let uu____12210 = (FStar_Options.interactive ())
in (not (uu____12210)))
in (match (uu____12209) with
| true -> begin
((

let uu____12212 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right uu____12212 (fun a241 -> ())));
(z3_reset_options en01);
)
end
| uu____12213 -> begin
en01
end))))
in (

let uu____12214 = (tc_modul en0 modul_iface)
in (match (uu____12214) with
| (modul_iface1, must_be_none, env) -> begin
(match ((Prims.op_disEquality must_be_none FStar_Pervasives_Native.None)) with
| true -> begin
(failwith "Impossible! finish_partial_module: expected the second component to be None")
end
| uu____12256 -> begin
(((

let uu___120_12260 = m
in {FStar_Syntax_Syntax.name = uu___120_12260.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu___120_12260.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = modul_iface1.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___120_12260.FStar_Syntax_Syntax.is_interface})), (FStar_Pervasives_Native.Some (modul_iface1)), (env))
end)
end)));
))
end
| uu____12261 -> begin
(

let modul = (

let uu____12263 = (FStar_Options.use_extracted_interfaces ())
in (match (uu____12263) with
| true -> begin
(

let uu___121_12264 = m
in {FStar_Syntax_Syntax.name = uu___121_12264.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu___121_12264.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = m.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.is_interface = uu___121_12264.FStar_Syntax_Syntax.is_interface})
end
| uu____12265 -> begin
(

let uu___122_12266 = m
in {FStar_Syntax_Syntax.name = uu___122_12266.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu___122_12266.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = uu___122_12266.FStar_Syntax_Syntax.is_interface})
end))
in (

let env = (FStar_TypeChecker_Env.finish_module en modul)
in ((

let uu____12269 = (FStar_All.pipe_right env.FStar_TypeChecker_Env.qtbl_name_and_index FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____12269 FStar_Util.smap_clear));
(

let uu____12297 = (((

let uu____12300 = (FStar_Options.lax ())
in (not (uu____12300))) && (

let uu____12302 = (FStar_Options.use_extracted_interfaces ())
in (not (uu____12302)))) && (not (loading_from_cache)))
in (match (uu____12297) with
| true -> begin
(check_exports env modul exports)
end
| uu____12303 -> begin
()
end));
(

let uu____12305 = (pop_context env (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (FStar_All.pipe_right uu____12305 (fun a242 -> ())));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul);
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
(

let uu____12309 = (

let uu____12310 = (FStar_Options.interactive ())
in (not (uu____12310)))
in (match (uu____12309) with
| true -> begin
(

let uu____12311 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right uu____12311 (fun a243 -> ())))
end
| uu____12312 -> begin
()
end));
((modul), (FStar_Pervasives_Native.None), (env));
)))
end)))


let load_checked_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_TypeChecker_Env.env = (fun en m -> (

let env = (FStar_TypeChecker_Env.set_current_module en m.FStar_Syntax_Syntax.name)
in (

let env1 = (

let uu____12327 = (

let uu____12328 = (FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name)
in (Prims.strcat "Internals for " uu____12328))
in (push_context env uu____12327))
in (

let env2 = (FStar_List.fold_left (fun env2 se -> (

let env3 = (FStar_TypeChecker_Env.push_sigelt env2 se)
in (

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in ((FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (

let uu____12347 = (FStar_TypeChecker_Env.try_lookup_lid env3 lid)
in ()))));
env3;
)))) env1 m.FStar_Syntax_Syntax.declarations)
in (

let uu____12358 = (finish_partial_modul true env2 m m.FStar_Syntax_Syntax.exports)
in (match (uu____12358) with
| (uu____12367, uu____12368, env3) -> begin
env3
end))))))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_TypeChecker_Env.env) = (fun env m -> ((

let uu____12393 = (FStar_Options.debug_any ())
in (match (uu____12393) with
| true -> begin
(

let uu____12394 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (match (m.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"i\'face"
end
| uu____12395 -> begin
"module"
end) uu____12394))
end
| uu____12396 -> begin
()
end));
(

let env1 = (

let uu___123_12398 = env
in (

let uu____12399 = (

let uu____12400 = (FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (not (uu____12400)))
in {FStar_TypeChecker_Env.solver = uu___123_12398.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___123_12398.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___123_12398.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___123_12398.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___123_12398.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___123_12398.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___123_12398.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___123_12398.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___123_12398.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___123_12398.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___123_12398.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___123_12398.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___123_12398.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___123_12398.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___123_12398.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___123_12398.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___123_12398.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___123_12398.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___123_12398.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu____12399; FStar_TypeChecker_Env.lax_universes = uu___123_12398.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___123_12398.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___123_12398.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___123_12398.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___123_12398.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___123_12398.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___123_12398.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___123_12398.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___123_12398.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___123_12398.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___123_12398.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___123_12398.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___123_12398.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___123_12398.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___123_12398.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___123_12398.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___123_12398.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___123_12398.FStar_TypeChecker_Env.dep_graph}))
in (

let uu____12401 = (tc_modul env1 m)
in (match (uu____12401) with
| (m1, m_iface_opt, env2) -> begin
((

let uu____12426 = (FStar_Options.dump_module m1.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____12426) with
| true -> begin
(

let uu____12427 = (FStar_Syntax_Print.modul_to_string m1)
in (FStar_Util.print1 "Module after type checking:\n%s\n" uu____12427))
end
| uu____12428 -> begin
()
end));
(

let uu____12430 = ((FStar_Options.dump_module m1.FStar_Syntax_Syntax.name.FStar_Ident.str) && (FStar_Options.debug_at_level m1.FStar_Syntax_Syntax.name.FStar_Ident.str (FStar_Options.Other ("Normalize"))))
in (match (uu____12430) with
| true -> begin
(

let normalize_toplevel_lets = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((b, lbs), ids) -> begin
(

let n1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]))
in (

let update = (fun lb -> (

let uu____12463 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____12463) with
| (univnames1, e) -> begin
(

let uu___124_12470 = lb
in (

let uu____12471 = (

let uu____12474 = (FStar_TypeChecker_Env.push_univ_vars env2 univnames1)
in (n1 uu____12474 e))
in {FStar_Syntax_Syntax.lbname = uu___124_12470.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___124_12470.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___124_12470.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___124_12470.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____12471; FStar_Syntax_Syntax.lbattrs = uu___124_12470.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___124_12470.FStar_Syntax_Syntax.lbpos}))
end)))
in (

let uu___125_12475 = se
in (

let uu____12476 = (

let uu____12477 = (

let uu____12484 = (

let uu____12485 = (FStar_List.map update lbs)
in ((b), (uu____12485)))
in ((uu____12484), (ids)))
in FStar_Syntax_Syntax.Sig_let (uu____12477))
in {FStar_Syntax_Syntax.sigel = uu____12476; FStar_Syntax_Syntax.sigrng = uu___125_12475.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___125_12475.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___125_12475.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___125_12475.FStar_Syntax_Syntax.sigattrs}))))
end
| uu____12492 -> begin
se
end))
in (

let normalized_module = (

let uu___126_12494 = m1
in (

let uu____12495 = (FStar_List.map normalize_toplevel_lets m1.FStar_Syntax_Syntax.declarations)
in {FStar_Syntax_Syntax.name = uu___126_12494.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu____12495; FStar_Syntax_Syntax.exports = uu___126_12494.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___126_12494.FStar_Syntax_Syntax.is_interface}))
in (

let uu____12496 = (FStar_Syntax_Print.modul_to_string normalized_module)
in (FStar_Util.print1 "%s\n" uu____12496))))
end
| uu____12497 -> begin
()
end));
((m1), (m_iface_opt), (env2));
)
end)));
))




