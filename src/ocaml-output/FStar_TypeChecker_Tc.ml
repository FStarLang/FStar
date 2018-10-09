
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

let uu___379_54 = env
in (

let uu____55 = (

let uu____68 = (

let uu____75 = (

let uu____80 = (get_n lid)
in ((lid), (uu____80)))
in FStar_Pervasives_Native.Some (uu____75))
in ((tbl), (uu____68)))
in {FStar_TypeChecker_Env.solver = uu___379_54.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___379_54.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___379_54.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___379_54.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___379_54.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___379_54.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___379_54.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___379_54.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___379_54.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___379_54.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___379_54.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___379_54.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___379_54.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___379_54.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___379_54.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___379_54.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___379_54.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___379_54.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___379_54.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___379_54.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___379_54.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___379_54.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___379_54.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___379_54.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___379_54.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___379_54.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___379_54.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___379_54.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___379_54.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___379_54.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___379_54.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu____55; FStar_TypeChecker_Env.normalized_eff_names = uu___379_54.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___379_54.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___379_54.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___379_54.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___379_54.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___379_54.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___379_54.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___379_54.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___379_54.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___379_54.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___379_54.FStar_TypeChecker_Env.nbe})))
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

let uu___380_104 = env
in (

let uu____105 = (

let uu____118 = (

let uu____125 = (

let uu____130 = (get_n lid)
in ((lid), (uu____130)))
in FStar_Pervasives_Native.Some (uu____125))
in ((tbl), (uu____118)))
in {FStar_TypeChecker_Env.solver = uu___380_104.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___380_104.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___380_104.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___380_104.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___380_104.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___380_104.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___380_104.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___380_104.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___380_104.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___380_104.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___380_104.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___380_104.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___380_104.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___380_104.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___380_104.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___380_104.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___380_104.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___380_104.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___380_104.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___380_104.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___380_104.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___380_104.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___380_104.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___380_104.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___380_104.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___380_104.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___380_104.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___380_104.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___380_104.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___380_104.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___380_104.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu____105; FStar_TypeChecker_Env.normalized_eff_names = uu___380_104.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___380_104.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___380_104.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___380_104.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___380_104.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___380_104.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___380_104.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___380_104.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___380_104.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___380_104.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___380_104.FStar_TypeChecker_Env.nbe}))))
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

let uu____257 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::[]) env t1)
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
| ((a, uu____342))::((wp, uu____344))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____373 -> begin
(fail1 ())
end))
end
| uu____374 -> begin
(fail1 ())
end))))


let tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (

let uu____385 = (FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs)
in (match (uu____385) with
| (open_annotated_univs, annotated_univ_names) -> begin
(

let open_univs = (fun n_binders t -> (

let uu____415 = (FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs)
in (FStar_Syntax_Subst.subst uu____415 t)))
in (

let open_univs_binders = (fun n_binders bs -> (

let uu____429 = (FStar_Syntax_Subst.shift_subst n_binders open_annotated_univs)
in (FStar_Syntax_Subst.subst_binders uu____429 bs)))
in (

let n_effect_params = (FStar_List.length ed.FStar_Syntax_Syntax.binders)
in (

let uu____439 = (

let uu____446 = (open_univs_binders (Prims.parse_int "0") ed.FStar_Syntax_Syntax.binders)
in (

let uu____447 = (open_univs n_effect_params ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Subst.open_term' uu____446 uu____447)))
in (match (uu____439) with
| (effect_params_un, signature_un, opening) -> begin
(

let env = (FStar_TypeChecker_Env.push_univ_vars env0 annotated_univ_names)
in (

let uu____458 = (FStar_TypeChecker_TcTerm.tc_tparams env effect_params_un)
in (match (uu____458) with
| (effect_params, env1, uu____467) -> begin
(

let uu____468 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un)
in (match (uu____468) with
| (signature, uu____474) -> begin
(

let ed1 = (

let uu___381_476 = ed
in {FStar_Syntax_Syntax.cattributes = uu___381_476.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___381_476.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___381_476.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = uu___381_476.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = uu___381_476.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = uu___381_476.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = uu___381_476.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = uu___381_476.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = uu___381_476.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = uu___381_476.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = uu___381_476.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = uu___381_476.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = uu___381_476.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = uu___381_476.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = uu___381_476.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = uu___381_476.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = uu___381_476.FStar_Syntax_Syntax.actions; FStar_Syntax_Syntax.eff_attrs = uu___381_476.FStar_Syntax_Syntax.eff_attrs})
in (

let ed2 = (match (((effect_params), (annotated_univ_names))) with
| ([], []) -> begin
ed1
end
| uu____504 -> begin
(

let op = (fun uu____536 -> (match (uu____536) with
| (us, t) -> begin
(

let n_us = (FStar_List.length us)
in (

let uu____556 = (

let uu____557 = (FStar_Syntax_Subst.shift_subst n_us opening)
in (

let uu____566 = (open_univs n_us t)
in (FStar_Syntax_Subst.subst uu____557 uu____566)))
in ((us), (uu____556))))
end))
in (

let uu___382_575 = ed1
in (

let uu____576 = (op ed1.FStar_Syntax_Syntax.ret_wp)
in (

let uu____577 = (op ed1.FStar_Syntax_Syntax.bind_wp)
in (

let uu____578 = (op ed1.FStar_Syntax_Syntax.if_then_else)
in (

let uu____579 = (op ed1.FStar_Syntax_Syntax.ite_wp)
in (

let uu____580 = (op ed1.FStar_Syntax_Syntax.stronger)
in (

let uu____581 = (op ed1.FStar_Syntax_Syntax.close_wp)
in (

let uu____582 = (op ed1.FStar_Syntax_Syntax.assert_p)
in (

let uu____583 = (op ed1.FStar_Syntax_Syntax.assume_p)
in (

let uu____584 = (op ed1.FStar_Syntax_Syntax.null_wp)
in (

let uu____585 = (op ed1.FStar_Syntax_Syntax.trivial)
in (

let uu____586 = (

let uu____587 = (op (([]), (ed1.FStar_Syntax_Syntax.repr)))
in (FStar_Pervasives_Native.snd uu____587))
in (

let uu____598 = (op ed1.FStar_Syntax_Syntax.return_repr)
in (

let uu____599 = (op ed1.FStar_Syntax_Syntax.bind_repr)
in (

let uu____600 = (FStar_List.map (fun a -> (

let uu___383_608 = a
in (

let uu____609 = (

let uu____610 = (op ((a.FStar_Syntax_Syntax.action_univs), (a.FStar_Syntax_Syntax.action_defn)))
in (FStar_Pervasives_Native.snd uu____610))
in (

let uu____621 = (

let uu____622 = (op ((a.FStar_Syntax_Syntax.action_univs), (a.FStar_Syntax_Syntax.action_typ)))
in (FStar_Pervasives_Native.snd uu____622))
in {FStar_Syntax_Syntax.action_name = uu___383_608.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___383_608.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___383_608.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = uu___383_608.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = uu____609; FStar_Syntax_Syntax.action_typ = uu____621})))) ed1.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.cattributes = uu___382_575.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___382_575.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = annotated_univ_names; FStar_Syntax_Syntax.binders = uu___382_575.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = uu___382_575.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = uu____576; FStar_Syntax_Syntax.bind_wp = uu____577; FStar_Syntax_Syntax.if_then_else = uu____578; FStar_Syntax_Syntax.ite_wp = uu____579; FStar_Syntax_Syntax.stronger = uu____580; FStar_Syntax_Syntax.close_wp = uu____581; FStar_Syntax_Syntax.assert_p = uu____582; FStar_Syntax_Syntax.assume_p = uu____583; FStar_Syntax_Syntax.null_wp = uu____584; FStar_Syntax_Syntax.trivial = uu____585; FStar_Syntax_Syntax.repr = uu____586; FStar_Syntax_Syntax.return_repr = uu____598; FStar_Syntax_Syntax.bind_repr = uu____599; FStar_Syntax_Syntax.actions = uu____600; FStar_Syntax_Syntax.eff_attrs = uu___382_575.FStar_Syntax_Syntax.eff_attrs}))))))))))))))))
end)
in (

let wp_with_fresh_result_type = (fun env2 mname signature1 -> (

let fail1 = (fun t -> (

let uu____667 = (FStar_TypeChecker_Err.unexpected_signature_for_monad env2 mname t)
in (

let uu____672 = (FStar_Ident.range_of_lid mname)
in (FStar_Errors.raise_error uu____667 uu____672))))
in (

let uu____679 = (

let uu____680 = (FStar_Syntax_Subst.compress signature1)
in uu____680.FStar_Syntax_Syntax.n)
in (match (uu____679) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs1 = (FStar_Syntax_Subst.open_binders bs)
in (match (bs1) with
| ((a, uu____719))::((wp, uu____721))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____750 -> begin
(fail1 signature1)
end))
end
| uu____751 -> begin
(fail1 signature1)
end))))
in (

let uu____752 = (wp_with_fresh_result_type env1 ed2.FStar_Syntax_Syntax.mname ed2.FStar_Syntax_Syntax.signature)
in (match (uu____752) with
| (a, wp_a) -> begin
(

let fresh_effect_signature = (fun uu____776 -> (match (annotated_univ_names) with
| [] -> begin
(

let uu____783 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un)
in (match (uu____783) with
| (signature1, uu____795) -> begin
(wp_with_fresh_result_type env1 ed2.FStar_Syntax_Syntax.mname signature1)
end))
end
| uu____796 -> begin
(

let uu____799 = (

let uu____804 = (

let uu____805 = (FStar_Syntax_Subst.close_univ_vars annotated_univ_names signature)
in ((annotated_univ_names), (uu____805)))
in (FStar_TypeChecker_Env.inst_tscheme uu____804))
in (match (uu____799) with
| (uu____818, signature1) -> begin
(wp_with_fresh_result_type env1 ed2.FStar_Syntax_Syntax.mname signature1)
end))
end))
in (

let env2 = (

let uu____821 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None ed2.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env1 uu____821))
in ((

let uu____823 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED")))
in (match (uu____823) with
| true -> begin
(

let uu____824 = (FStar_Syntax_Print.lid_to_string ed2.FStar_Syntax_Syntax.mname)
in (

let uu____825 = (FStar_Syntax_Print.binders_to_string " " ed2.FStar_Syntax_Syntax.binders)
in (

let uu____826 = (FStar_Syntax_Print.term_to_string ed2.FStar_Syntax_Syntax.signature)
in (

let uu____827 = (

let uu____828 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Print.term_to_string uu____828))
in (

let uu____829 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.sort)
in (FStar_Util.print5 "Checking effect signature: %s %s : %s\n(a is %s:%s)\n" uu____824 uu____825 uu____826 uu____827 uu____829))))))
end
| uu____830 -> begin
()
end));
(

let check_and_gen' = (fun env3 uu____861 k -> (match (uu____861) with
| (us, t) -> begin
(match (annotated_univ_names) with
| [] -> begin
(check_and_gen env3 t k)
end
| (uu____897)::uu____898 -> begin
(

let uu____901 = (FStar_Syntax_Subst.subst_tscheme open_annotated_univs ((us), (t)))
in (match (uu____901) with
| (us1, t1) -> begin
(

let uu____924 = (FStar_Syntax_Subst.open_univ_vars us1 t1)
in (match (uu____924) with
| (us2, t2) -> begin
(

let uu____939 = (

let uu____940 = (FStar_TypeChecker_Env.push_univ_vars env3 us2)
in (tc_check_trivial_guard uu____940 t2 k))
in (

let uu____941 = (FStar_Syntax_Subst.close_univ_vars us2 t2)
in ((us2), (uu____941))))
end))
end))
end)
end))
in (

let return_wp = (

let expected_k = (

let uu____960 = (

let uu____969 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____976 = (

let uu____985 = (

let uu____992 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____992))
in (uu____985)::[])
in (uu____969)::uu____976))
in (

let uu____1011 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow uu____960 uu____1011)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.ret_wp expected_k))
in (

let bind_wp = (

let uu____1015 = (fresh_effect_signature ())
in (match (uu____1015) with
| (b, wp_b) -> begin
(

let a_wp_b = (

let uu____1031 = (

let uu____1040 = (

let uu____1047 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____1047))
in (uu____1040)::[])
in (

let uu____1060 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____1031 uu____1060)))
in (

let expected_k = (

let uu____1066 = (

let uu____1075 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Syntax.t_range)
in (

let uu____1082 = (

let uu____1091 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1098 = (

let uu____1107 = (FStar_Syntax_Syntax.mk_binder b)
in (

let uu____1114 = (

let uu____1123 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____1130 = (

let uu____1139 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (uu____1139)::[])
in (uu____1123)::uu____1130))
in (uu____1107)::uu____1114))
in (uu____1091)::uu____1098))
in (uu____1075)::uu____1082))
in (

let uu____1182 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____1066 uu____1182)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else1 = (

let p = (

let uu____1195 = (

let uu____1198 = (FStar_Ident.range_of_lid ed2.FStar_Syntax_Syntax.mname)
in FStar_Pervasives_Native.Some (uu____1198))
in (

let uu____1199 = (

let uu____1200 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____1200 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.new_bv uu____1195 uu____1199)))
in (

let expected_k = (

let uu____1212 = (

let uu____1221 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1228 = (

let uu____1237 = (FStar_Syntax_Syntax.mk_binder p)
in (

let uu____1244 = (

let uu____1253 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____1260 = (

let uu____1269 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1269)::[])
in (uu____1253)::uu____1260))
in (uu____1237)::uu____1244))
in (uu____1221)::uu____1228))
in (

let uu____1306 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1212 uu____1306)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (

let uu____1321 = (

let uu____1330 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1337 = (

let uu____1346 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1346)::[])
in (uu____1330)::uu____1337))
in (

let uu____1371 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1321 uu____1371)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let uu____1375 = (FStar_Syntax_Util.type_u ())
in (match (uu____1375) with
| (t, uu____1381) -> begin
(

let expected_k = (

let uu____1385 = (

let uu____1394 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1401 = (

let uu____1410 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____1417 = (

let uu____1426 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1426)::[])
in (uu____1410)::uu____1417))
in (uu____1394)::uu____1401))
in (

let uu____1457 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow uu____1385 uu____1457)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (

let uu____1470 = (

let uu____1473 = (FStar_Ident.range_of_lid ed2.FStar_Syntax_Syntax.mname)
in FStar_Pervasives_Native.Some (uu____1473))
in (

let uu____1474 = (

let uu____1475 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____1475 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.new_bv uu____1470 uu____1474)))
in (

let b_wp_a = (

let uu____1487 = (

let uu____1496 = (

let uu____1503 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder uu____1503))
in (uu____1496)::[])
in (

let uu____1516 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1487 uu____1516)))
in (

let expected_k = (

let uu____1522 = (

let uu____1531 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1538 = (

let uu____1547 = (FStar_Syntax_Syntax.mk_binder b)
in (

let uu____1554 = (

let uu____1563 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (uu____1563)::[])
in (uu____1547)::uu____1554))
in (uu____1531)::uu____1538))
in (

let uu____1594 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1522 uu____1594)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (

let uu____1609 = (

let uu____1618 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1625 = (

let uu____1634 = (

let uu____1641 = (

let uu____1642 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____1642 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.null_binder uu____1641))
in (

let uu____1651 = (

let uu____1660 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1660)::[])
in (uu____1634)::uu____1651))
in (uu____1618)::uu____1625))
in (

let uu____1691 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1609 uu____1691)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (

let uu____1706 = (

let uu____1715 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1722 = (

let uu____1731 = (

let uu____1738 = (

let uu____1739 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____1739 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.null_binder uu____1738))
in (

let uu____1748 = (

let uu____1757 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1757)::[])
in (uu____1731)::uu____1748))
in (uu____1715)::uu____1722))
in (

let uu____1788 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1706 uu____1788)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (

let uu____1803 = (

let uu____1812 = (FStar_Syntax_Syntax.mk_binder a)
in (uu____1812)::[])
in (

let uu____1831 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____1803 uu____1831)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let uu____1835 = (FStar_Syntax_Util.type_u ())
in (match (uu____1835) with
| (t, uu____1841) -> begin
(

let expected_k = (

let uu____1845 = (

let uu____1854 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1861 = (

let uu____1870 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1870)::[])
in (uu____1854)::uu____1861))
in (

let uu____1895 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow uu____1845 uu____1895)))
in (check_and_gen' env2 ed2.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let uu____1898 = (

let uu____1911 = (

let uu____1912 = (FStar_Syntax_Subst.compress ed2.FStar_Syntax_Syntax.repr)
in uu____1912.FStar_Syntax_Syntax.n)
in (match (uu____1911) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((ed2.FStar_Syntax_Syntax.repr), (ed2.FStar_Syntax_Syntax.bind_repr), (ed2.FStar_Syntax_Syntax.return_repr), (ed2.FStar_Syntax_Syntax.actions))
end
| uu____1931 -> begin
(

let repr = (

let uu____1933 = (FStar_Syntax_Util.type_u ())
in (match (uu____1933) with
| (t, uu____1939) -> begin
(

let expected_k = (

let uu____1943 = (

let uu____1952 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1959 = (

let uu____1968 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____1968)::[])
in (uu____1952)::uu____1959))
in (

let uu____1993 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow uu____1943 uu____1993)))
in (tc_check_trivial_guard env2 ed2.FStar_Syntax_Syntax.repr expected_k))
end))
in (

let mk_repr' = (fun t wp -> (

let repr1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.EraseUniverses)::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]) env2 repr)
in (

let uu____2010 = (

let uu____2017 = (

let uu____2018 = (

let uu____2035 = (

let uu____2046 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____2055 = (

let uu____2066 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____2066)::[])
in (uu____2046)::uu____2055))
in ((repr1), (uu____2035)))
in FStar_Syntax_Syntax.Tm_app (uu____2018))
in (FStar_Syntax_Syntax.mk uu____2017))
in (uu____2010 FStar_Pervasives_Native.None FStar_Range.dummyRange))))
in (

let mk_repr = (fun a1 wp -> (

let uu____2127 = (FStar_Syntax_Syntax.bv_to_name a1)
in (mk_repr' uu____2127 wp)))
in (

let destruct_repr = (fun t -> (

let uu____2142 = (

let uu____2143 = (FStar_Syntax_Subst.compress t)
in uu____2143.FStar_Syntax_Syntax.n)
in (match (uu____2142) with
| FStar_Syntax_Syntax.Tm_app (uu____2154, ((t1, uu____2156))::((wp, uu____2158))::[]) -> begin
((t1), (wp))
end
| uu____2217 -> begin
(failwith "Unexpected repr type")
end)))
in (

let bind_repr = (

let r = (

let uu____2228 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.range_0 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_All.pipe_right uu____2228 FStar_Syntax_Syntax.fv_to_tm))
in (

let uu____2229 = (fresh_effect_signature ())
in (match (uu____2229) with
| (b, wp_b) -> begin
(

let a_wp_b = (

let uu____2245 = (

let uu____2254 = (

let uu____2261 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____2261))
in (uu____2254)::[])
in (

let uu____2274 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____2245 uu____2274)))
in (

let wp_f = (FStar_Syntax_Syntax.gen_bv "wp_f" FStar_Pervasives_Native.None wp_a)
in (

let wp_g = (FStar_Syntax_Syntax.gen_bv "wp_g" FStar_Pervasives_Native.None a_wp_b)
in (

let x_a = (

let uu____2280 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" FStar_Pervasives_Native.None uu____2280))
in (

let wp_g_x = (

let uu____2284 = (

let uu____2289 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (

let uu____2290 = (

let uu____2291 = (

let uu____2300 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____2300))
in (uu____2291)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____2289 uu____2290)))
in (uu____2284 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let res = (

let wp = (

let uu____2333 = (

let uu____2338 = (

let uu____2339 = (FStar_TypeChecker_Env.inst_tscheme bind_wp)
in (FStar_All.pipe_right uu____2339 FStar_Pervasives_Native.snd))
in (

let uu____2348 = (

let uu____2349 = (

let uu____2352 = (

let uu____2355 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____2356 = (

let uu____2359 = (FStar_Syntax_Syntax.bv_to_name b)
in (

let uu____2360 = (

let uu____2363 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (

let uu____2364 = (

let uu____2367 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (uu____2367)::[])
in (uu____2363)::uu____2364))
in (uu____2359)::uu____2360))
in (uu____2355)::uu____2356))
in (r)::uu____2352)
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____2349))
in (FStar_Syntax_Syntax.mk_Tm_app uu____2338 uu____2348)))
in (uu____2333 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (mk_repr b wp))
in (

let maybe_range_arg = (

let uu____2387 = (FStar_Util.for_some (FStar_Syntax_Util.attr_eq FStar_Syntax_Util.dm4f_bind_range_attr) ed2.FStar_Syntax_Syntax.eff_attrs)
in (match (uu____2387) with
| true -> begin
(

let uu____2396 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Syntax.t_range)
in (

let uu____2403 = (

let uu____2412 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Syntax.t_range)
in (uu____2412)::[])
in (uu____2396)::uu____2403))
end
| uu____2437 -> begin
[]
end))
in (

let expected_k = (

let uu____2447 = (

let uu____2456 = (

let uu____2465 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____2472 = (

let uu____2481 = (FStar_Syntax_Syntax.mk_binder b)
in (uu____2481)::[])
in (uu____2465)::uu____2472))
in (

let uu____2506 = (

let uu____2515 = (

let uu____2524 = (FStar_Syntax_Syntax.mk_binder wp_f)
in (

let uu____2531 = (

let uu____2540 = (

let uu____2547 = (

let uu____2548 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (mk_repr a uu____2548))
in (FStar_Syntax_Syntax.null_binder uu____2547))
in (

let uu____2549 = (

let uu____2558 = (FStar_Syntax_Syntax.mk_binder wp_g)
in (

let uu____2565 = (

let uu____2574 = (

let uu____2581 = (

let uu____2582 = (

let uu____2591 = (FStar_Syntax_Syntax.mk_binder x_a)
in (uu____2591)::[])
in (

let uu____2610 = (

let uu____2613 = (mk_repr b wp_g_x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____2613))
in (FStar_Syntax_Util.arrow uu____2582 uu____2610)))
in (FStar_Syntax_Syntax.null_binder uu____2581))
in (uu____2574)::[])
in (uu____2558)::uu____2565))
in (uu____2540)::uu____2549))
in (uu____2524)::uu____2531))
in (FStar_List.append maybe_range_arg uu____2515))
in (FStar_List.append uu____2456 uu____2506)))
in (

let uu____2658 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow uu____2447 uu____2658)))
in (

let uu____2661 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env2 expected_k)
in (match (uu____2661) with
| (expected_k1, uu____2669, uu____2670) -> begin
(

let env3 = (FStar_TypeChecker_Env.set_range env2 (FStar_Pervasives_Native.snd ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos)
in (

let env4 = (

let uu___384_2677 = env3
in {FStar_TypeChecker_Env.solver = uu___384_2677.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___384_2677.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___384_2677.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___384_2677.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___384_2677.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___384_2677.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___384_2677.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___384_2677.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___384_2677.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___384_2677.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___384_2677.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___384_2677.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___384_2677.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___384_2677.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___384_2677.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___384_2677.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___384_2677.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___384_2677.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___384_2677.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___384_2677.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___384_2677.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___384_2677.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___384_2677.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___384_2677.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___384_2677.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___384_2677.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___384_2677.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___384_2677.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___384_2677.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___384_2677.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___384_2677.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___384_2677.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___384_2677.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___384_2677.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___384_2677.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___384_2677.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___384_2677.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___384_2677.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___384_2677.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___384_2677.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___384_2677.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___384_2677.FStar_TypeChecker_Env.nbe})
in (

let br = (check_and_gen' env4 ed2.FStar_Syntax_Syntax.bind_repr expected_k1)
in br)))
end))))))))))
end)))
in (

let return_repr = (

let x_a = (

let uu____2689 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" FStar_Pervasives_Native.None uu____2689))
in (

let res = (

let wp = (

let uu____2696 = (

let uu____2701 = (

let uu____2702 = (FStar_TypeChecker_Env.inst_tscheme return_wp)
in (FStar_All.pipe_right uu____2702 FStar_Pervasives_Native.snd))
in (

let uu____2711 = (

let uu____2712 = (

let uu____2715 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____2716 = (

let uu____2719 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (uu____2719)::[])
in (uu____2715)::uu____2716))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____2712))
in (FStar_Syntax_Syntax.mk_Tm_app uu____2701 uu____2711)))
in (uu____2696 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (mk_repr a wp))
in (

let expected_k = (

let uu____2733 = (

let uu____2742 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____2749 = (

let uu____2758 = (FStar_Syntax_Syntax.mk_binder x_a)
in (uu____2758)::[])
in (uu____2742)::uu____2749))
in (

let uu____2783 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow uu____2733 uu____2783)))
in (

let uu____2786 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env2 expected_k)
in (match (uu____2786) with
| (expected_k1, uu____2794, uu____2795) -> begin
(

let env3 = (FStar_TypeChecker_Env.set_range env2 (FStar_Pervasives_Native.snd ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos)
in (

let uu____2801 = (check_and_gen' env3 ed2.FStar_Syntax_Syntax.return_repr expected_k1)
in (match (uu____2801) with
| (univs1, repr1) -> begin
(match (univs1) with
| [] -> begin
(([]), (repr1))
end
| uu____2824 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedUniversePolymorphicReturn), ("Unexpected universe-polymorphic return for effect")) repr1.FStar_Syntax_Syntax.pos)
end)
end)))
end)))))
in (

let actions = (

let check_action = (fun act -> (

let uu____2837 = (match ((Prims.op_Equality act.FStar_Syntax_Syntax.action_univs [])) with
| true -> begin
((env2), (act))
end
| uu____2848 -> begin
(

let uu____2849 = (FStar_Syntax_Subst.univ_var_opening act.FStar_Syntax_Syntax.action_univs)
in (match (uu____2849) with
| (usubst, uvs) -> begin
(

let uu____2872 = (FStar_TypeChecker_Env.push_univ_vars env2 uvs)
in (

let uu____2873 = (

let uu___385_2874 = act
in (

let uu____2875 = (FStar_Syntax_Subst.subst_binders usubst act.FStar_Syntax_Syntax.action_params)
in (

let uu____2876 = (FStar_Syntax_Subst.subst usubst act.FStar_Syntax_Syntax.action_defn)
in (

let uu____2877 = (FStar_Syntax_Subst.subst usubst act.FStar_Syntax_Syntax.action_typ)
in {FStar_Syntax_Syntax.action_name = uu___385_2874.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___385_2874.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uvs; FStar_Syntax_Syntax.action_params = uu____2875; FStar_Syntax_Syntax.action_defn = uu____2876; FStar_Syntax_Syntax.action_typ = uu____2877}))))
in ((uu____2872), (uu____2873))))
end))
end)
in (match (uu____2837) with
| (env3, act1) -> begin
(

let act_typ = (

let uu____2881 = (

let uu____2882 = (FStar_Syntax_Subst.compress act1.FStar_Syntax_Syntax.action_typ)
in uu____2882.FStar_Syntax_Syntax.n)
in (match (uu____2881) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let c1 = (FStar_Syntax_Util.comp_to_comp_typ c)
in (

let uu____2908 = (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name ed2.FStar_Syntax_Syntax.mname)
in (match (uu____2908) with
| true -> begin
(

let uu____2909 = (

let uu____2912 = (

let uu____2913 = (

let uu____2914 = (FStar_List.hd c1.FStar_Syntax_Syntax.effect_args)
in (FStar_Pervasives_Native.fst uu____2914))
in (mk_repr' c1.FStar_Syntax_Syntax.result_typ uu____2913))
in (FStar_Syntax_Syntax.mk_Total uu____2912))
in (FStar_Syntax_Util.arrow bs uu____2909))
end
| uu____2935 -> begin
act1.FStar_Syntax_Syntax.action_typ
end)))
end
| uu____2936 -> begin
act1.FStar_Syntax_Syntax.action_typ
end))
in (

let uu____2937 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env3 act_typ)
in (match (uu____2937) with
| (act_typ1, uu____2945, g_t) -> begin
(

let env' = (

let uu___386_2948 = (FStar_TypeChecker_Env.set_expected_typ env3 act_typ1)
in {FStar_TypeChecker_Env.solver = uu___386_2948.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___386_2948.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___386_2948.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___386_2948.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___386_2948.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___386_2948.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___386_2948.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___386_2948.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___386_2948.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___386_2948.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___386_2948.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = uu___386_2948.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___386_2948.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___386_2948.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___386_2948.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___386_2948.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___386_2948.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___386_2948.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___386_2948.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___386_2948.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___386_2948.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___386_2948.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___386_2948.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___386_2948.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___386_2948.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___386_2948.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___386_2948.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___386_2948.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___386_2948.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___386_2948.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___386_2948.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___386_2948.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___386_2948.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___386_2948.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___386_2948.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___386_2948.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___386_2948.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___386_2948.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___386_2948.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___386_2948.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___386_2948.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___386_2948.FStar_TypeChecker_Env.nbe})
in ((

let uu____2950 = (FStar_TypeChecker_Env.debug env3 (FStar_Options.Other ("ED")))
in (match (uu____2950) with
| true -> begin
(

let uu____2951 = (FStar_Ident.text_of_lid act1.FStar_Syntax_Syntax.action_name)
in (

let uu____2952 = (FStar_Syntax_Print.term_to_string act1.FStar_Syntax_Syntax.action_defn)
in (

let uu____2953 = (FStar_Syntax_Print.term_to_string act_typ1)
in (FStar_Util.print3 "Checking action %s:\n[definition]: %s\n[cps\'d type]: %s\n" uu____2951 uu____2952 uu____2953))))
end
| uu____2954 -> begin
()
end));
(

let uu____2955 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' act1.FStar_Syntax_Syntax.action_defn)
in (match (uu____2955) with
| (act_defn, uu____2963, g_a) -> begin
(

let act_defn1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::[]) env3 act_defn)
in (

let act_typ2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Beta)::[]) env3 act_typ1)
in (

let uu____2967 = (

let act_typ3 = (FStar_Syntax_Subst.compress act_typ2)
in (match (act_typ3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____3003 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____3003) with
| (bs1, uu____3015) -> begin
(

let res = (mk_repr' FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun)
in (

let k = (

let uu____3022 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs1 uu____3022))
in (

let uu____3025 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env3 k)
in (match (uu____3025) with
| (k1, uu____3039, g) -> begin
((k1), (g))
end))))
end))
end
| uu____3043 -> begin
(

let uu____3044 = (

let uu____3049 = (

let uu____3050 = (FStar_Syntax_Print.term_to_string act_typ3)
in (

let uu____3051 = (FStar_Syntax_Print.tag_of_term act_typ3)
in (FStar_Util.format2 "Actions must have function types (not: %s, a.k.a. %s)" uu____3050 uu____3051)))
in ((FStar_Errors.Fatal_ActionMustHaveFunctionType), (uu____3049)))
in (FStar_Errors.raise_error uu____3044 act_defn1.FStar_Syntax_Syntax.pos))
end))
in (match (uu____2967) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env3 act_typ2 expected_k)
in ((

let uu____3066 = (

let uu____3067 = (

let uu____3068 = (FStar_TypeChecker_Env.conj_guard g_t g)
in (FStar_TypeChecker_Env.conj_guard g_k uu____3068))
in (FStar_TypeChecker_Env.conj_guard g_a uu____3067))
in (FStar_TypeChecker_Rel.force_trivial_guard env3 uu____3066));
(

let act_typ3 = (

let uu____3070 = (

let uu____3071 = (FStar_Syntax_Subst.compress expected_k)
in uu____3071.FStar_Syntax_Syntax.n)
in (match (uu____3070) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____3096 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____3096) with
| (bs1, c1) -> begin
(

let uu____3103 = (destruct_repr (FStar_Syntax_Util.comp_result c1))
in (match (uu____3103) with
| (a1, wp) -> begin
(

let c2 = (

let uu____3123 = (

let uu____3124 = (env3.FStar_TypeChecker_Env.universe_of env3 a1)
in (uu____3124)::[])
in (

let uu____3125 = (

let uu____3136 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____3136)::[])
in {FStar_Syntax_Syntax.comp_univs = uu____3123; FStar_Syntax_Syntax.effect_name = ed2.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a1; FStar_Syntax_Syntax.effect_args = uu____3125; FStar_Syntax_Syntax.flags = []}))
in (

let uu____3161 = (FStar_Syntax_Syntax.mk_Comp c2)
in (FStar_Syntax_Util.arrow bs1 uu____3161)))
end))
end))
end
| uu____3164 -> begin
(failwith "Impossible (expected_k is an arrow)")
end))
in (

let uu____3165 = (match ((Prims.op_Equality act1.FStar_Syntax_Syntax.action_univs [])) with
| true -> begin
(FStar_TypeChecker_Util.generalize_universes env3 act_defn1)
end
| uu____3184 -> begin
(

let uu____3185 = (FStar_Syntax_Subst.close_univ_vars act1.FStar_Syntax_Syntax.action_univs act_defn1)
in ((act1.FStar_Syntax_Syntax.action_univs), (uu____3185)))
end)
in (match (uu____3165) with
| (univs1, act_defn2) -> begin
(

let act_typ4 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::[]) env3 act_typ3)
in (

let act_typ5 = (FStar_Syntax_Subst.close_univ_vars univs1 act_typ4)
in (

let uu___387_3204 = act1
in {FStar_Syntax_Syntax.action_name = uu___387_3204.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___387_3204.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs1; FStar_Syntax_Syntax.action_params = uu___387_3204.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = act_defn2; FStar_Syntax_Syntax.action_typ = act_typ5})))
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
in (match (uu____1898) with
| (repr, bind_repr, return_repr, actions) -> begin
(

let t0 = (

let uu____3228 = (FStar_Syntax_Syntax.mk_Total ed2.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed2.FStar_Syntax_Syntax.binders uu____3228))
in (

let uu____3231 = (

let uu____3236 = (FStar_TypeChecker_Util.generalize_universes env0 t0)
in (match (uu____3236) with
| (gen_univs, t) -> begin
(match (annotated_univ_names) with
| [] -> begin
((gen_univs), (t))
end
| uu____3255 -> begin
(

let uu____3258 = ((Prims.op_Equality (FStar_List.length gen_univs) (FStar_List.length annotated_univ_names)) && (FStar_List.forall2 (fun u1 u2 -> (

let uu____3264 = (FStar_Syntax_Syntax.order_univ_name u1 u2)
in (Prims.op_Equality uu____3264 (Prims.parse_int "0")))) gen_univs annotated_univ_names))
in (match (uu____3258) with
| true -> begin
((gen_univs), (t))
end
| uu____3269 -> begin
(

let uu____3270 = (

let uu____3275 = (

let uu____3276 = (FStar_Util.string_of_int (FStar_List.length annotated_univ_names))
in (

let uu____3277 = (FStar_Util.string_of_int (FStar_List.length gen_univs))
in (FStar_Util.format2 "Expected an effect definition with %s universes; but found %s" uu____3276 uu____3277)))
in ((FStar_Errors.Fatal_UnexpectedNumberOfUniverse), (uu____3275)))
in (FStar_Errors.raise_error uu____3270 ed2.FStar_Syntax_Syntax.signature.FStar_Syntax_Syntax.pos))
end))
end)
end))
in (match (uu____3231) with
| (univs1, t) -> begin
(

let signature1 = (

let uu____3285 = (

let uu____3298 = (

let uu____3299 = (FStar_Syntax_Subst.compress t)
in uu____3299.FStar_Syntax_Syntax.n)
in ((effect_params), (uu____3298)))
in (match (uu____3285) with
| ([], uu____3310) -> begin
t
end
| (uu____3325, FStar_Syntax_Syntax.Tm_arrow (uu____3326, c)) -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____3364 -> begin
(failwith "Impossible : t is an arrow")
end))
in (

let close1 = (fun n1 ts -> (

let ts1 = (

let uu____3389 = (FStar_Syntax_Subst.close_tscheme effect_params ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs1 uu____3389))
in (

let m = (FStar_List.length (FStar_Pervasives_Native.fst ts1))
in ((

let uu____3396 = (((n1 >= (Prims.parse_int "0")) && (

let uu____3398 = (FStar_Syntax_Util.is_unknown (FStar_Pervasives_Native.snd ts1))
in (not (uu____3398)))) && (Prims.op_disEquality m n1))
in (match (uu____3396) with
| true -> begin
(

let error = (match ((m < n1)) with
| true -> begin
"not universe-polymorphic enough"
end
| uu____3414 -> begin
"too universe-polymorphic"
end)
in (

let err_msg = (

let uu____3416 = (FStar_Util.string_of_int m)
in (

let uu____3423 = (FStar_Util.string_of_int n1)
in (

let uu____3424 = (FStar_Syntax_Print.tscheme_to_string ts1)
in (FStar_Util.format4 "The effect combinator is %s (m,n=%s,%s) (%s)" error uu____3416 uu____3423 uu____3424))))
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_MismatchUniversePolymorphic), (err_msg)) (FStar_Pervasives_Native.snd ts1).FStar_Syntax_Syntax.pos)))
end
| uu____3429 -> begin
()
end));
ts1;
))))
in (

let close_action = (fun act -> (

let uu____3436 = (close1 (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_defn)))
in (match (uu____3436) with
| (univs2, defn) -> begin
(

let uu____3451 = (close1 (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_typ)))
in (match (uu____3451) with
| (univs', typ) -> begin
(

let uu___388_3467 = act
in {FStar_Syntax_Syntax.action_name = uu___388_3467.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___388_3467.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs2; FStar_Syntax_Syntax.action_params = uu___388_3467.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = defn; FStar_Syntax_Syntax.action_typ = typ})
end))
end)))
in (

let ed3 = (

let uu___389_3470 = ed2
in (

let uu____3471 = (close1 (Prims.parse_int "0") return_wp)
in (

let uu____3472 = (close1 (Prims.parse_int "1") bind_wp)
in (

let uu____3473 = (close1 (Prims.parse_int "0") if_then_else1)
in (

let uu____3474 = (close1 (Prims.parse_int "0") ite_wp)
in (

let uu____3475 = (close1 (Prims.parse_int "0") stronger)
in (

let uu____3476 = (close1 (Prims.parse_int "1") close_wp)
in (

let uu____3477 = (close1 (Prims.parse_int "0") assert_p)
in (

let uu____3478 = (close1 (Prims.parse_int "0") assume_p)
in (

let uu____3479 = (close1 (Prims.parse_int "0") null_wp)
in (

let uu____3480 = (close1 (Prims.parse_int "0") trivial_wp)
in (

let uu____3481 = (

let uu____3482 = (close1 (Prims.parse_int "0") (([]), (repr)))
in (FStar_Pervasives_Native.snd uu____3482))
in (

let uu____3499 = (close1 (Prims.parse_int "0") return_repr)
in (

let uu____3500 = (close1 (Prims.parse_int "1") bind_repr)
in (

let uu____3501 = (FStar_List.map close_action actions)
in {FStar_Syntax_Syntax.cattributes = uu___389_3470.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___389_3470.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs1; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature1; FStar_Syntax_Syntax.ret_wp = uu____3471; FStar_Syntax_Syntax.bind_wp = uu____3472; FStar_Syntax_Syntax.if_then_else = uu____3473; FStar_Syntax_Syntax.ite_wp = uu____3474; FStar_Syntax_Syntax.stronger = uu____3475; FStar_Syntax_Syntax.close_wp = uu____3476; FStar_Syntax_Syntax.assert_p = uu____3477; FStar_Syntax_Syntax.assume_p = uu____3478; FStar_Syntax_Syntax.null_wp = uu____3479; FStar_Syntax_Syntax.trivial = uu____3480; FStar_Syntax_Syntax.repr = uu____3481; FStar_Syntax_Syntax.return_repr = uu____3499; FStar_Syntax_Syntax.bind_repr = uu____3500; FStar_Syntax_Syntax.actions = uu____3501; FStar_Syntax_Syntax.eff_attrs = uu___389_3470.FStar_Syntax_Syntax.eff_attrs})))))))))))))))
in ((

let uu____3505 = ((FStar_TypeChecker_Env.debug env2 FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("ED"))))
in (match (uu____3505) with
| true -> begin
(

let uu____3506 = (FStar_Syntax_Print.eff_decl_to_string false ed3)
in (FStar_Util.print_string uu____3506))
end
| uu____3507 -> begin
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

let uu____3528 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____3528) with
| (effect_binders_un, signature_un) -> begin
(

let uu____3545 = (FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un)
in (match (uu____3545) with
| (effect_binders, env1, uu____3564) -> begin
(

let uu____3565 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un)
in (match (uu____3565) with
| (signature, uu____3581) -> begin
(

let raise_error1 = (fun uu____3596 -> (match (uu____3596) with
| (e, err_msg) -> begin
(FStar_Errors.raise_error ((e), (err_msg)) signature.FStar_Syntax_Syntax.pos)
end))
in (

let effect_binders1 = (FStar_List.map (fun uu____3628 -> (match (uu____3628) with
| (bv, qual) -> begin
(

let uu____3647 = (

let uu___390_3648 = bv
in (

let uu____3649 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.EraseUniverses)::[]) env1 bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___390_3648.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___390_3648.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3649}))
in ((uu____3647), (qual)))
end)) effect_binders)
in (

let uu____3654 = (

let uu____3661 = (

let uu____3662 = (FStar_Syntax_Subst.compress signature_un)
in uu____3662.FStar_Syntax_Syntax.n)
in (match (uu____3661) with
| FStar_Syntax_Syntax.Tm_arrow (((a, uu____3672))::[], effect_marker) -> begin
((a), (effect_marker))
end
| uu____3704 -> begin
(raise_error1 ((FStar_Errors.Fatal_BadSignatureShape), ("bad shape for effect-for-free signature")))
end))
in (match (uu____3654) with
| (a, effect_marker) -> begin
(

let a1 = (

let uu____3728 = (FStar_Syntax_Syntax.is_null_bv a)
in (match (uu____3728) with
| true -> begin
(

let uu____3729 = (

let uu____3732 = (FStar_Syntax_Syntax.range_of_bv a)
in FStar_Pervasives_Native.Some (uu____3732))
in (FStar_Syntax_Syntax.gen_bv "a" uu____3729 a.FStar_Syntax_Syntax.sort))
end
| uu____3733 -> begin
a
end))
in (

let open_and_check = (fun env2 other_binders t -> (

let subst1 = (FStar_Syntax_Subst.opening_of_binders (FStar_List.append effect_binders1 other_binders))
in (

let t1 = (FStar_Syntax_Subst.subst subst1 t)
in (

let uu____3778 = (FStar_TypeChecker_TcTerm.tc_term env2 t1)
in (match (uu____3778) with
| (t2, comp, uu____3791) -> begin
((t2), (comp))
end)))))
in (

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None signature.FStar_Syntax_Syntax.pos))
in (

let uu____3800 = (open_and_check env1 [] ed.FStar_Syntax_Syntax.repr)
in (match (uu____3800) with
| (repr, _comp) -> begin
((

let uu____3824 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____3824) with
| true -> begin
(

let uu____3825 = (FStar_Syntax_Print.term_to_string repr)
in (FStar_Util.print1 "Representation is: %s\n" uu____3825))
end
| uu____3826 -> begin
()
end));
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env1 (FStar_TypeChecker_TcTerm.tc_constant env1 FStar_Range.dummyRange))
in (

let wp_type = (FStar_TypeChecker_DMFF.star_type dmff_env repr)
in (

let uu____3829 = (recheck_debug "*" env1 wp_type)
in (

let wp_a = (

let uu____3831 = (

let uu____3832 = (

let uu____3833 = (

let uu____3850 = (

let uu____3861 = (

let uu____3870 = (FStar_Syntax_Syntax.bv_to_name a1)
in (

let uu____3873 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____3870), (uu____3873))))
in (uu____3861)::[])
in ((wp_type), (uu____3850)))
in FStar_Syntax_Syntax.Tm_app (uu____3833))
in (mk1 uu____3832))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::[]) env1 uu____3831))
in (

let effect_signature = (

let binders = (

let uu____3920 = (

let uu____3927 = (FStar_Syntax_Syntax.as_implicit false)
in ((a1), (uu____3927)))
in (

let uu____3932 = (

let uu____3941 = (

let uu____3948 = (FStar_Syntax_Syntax.gen_bv "dijkstra_wp" FStar_Pervasives_Native.None wp_a)
in (FStar_All.pipe_right uu____3948 FStar_Syntax_Syntax.mk_binder))
in (uu____3941)::[])
in (uu____3920)::uu____3932))
in (

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in (mk1 (FStar_Syntax_Syntax.Tm_arrow (((binders1), (effect_marker)))))))
in (

let uu____3984 = (recheck_debug "turned into the effect signature" env1 effect_signature)
in (

let sigelts = (FStar_Util.mk_ref [])
in (

let mk_lid = (fun name -> (FStar_Syntax_Util.dm4f_lid ed name))
in (

let elaborate_and_star = (fun dmff_env1 other_binders item -> (

let env2 = (FStar_TypeChecker_DMFF.get_env dmff_env1)
in (

let uu____4047 = item
in (match (uu____4047) with
| (u_item, item1) -> begin
(

let uu____4062 = (open_and_check env2 other_binders item1)
in (match (uu____4062) with
| (item2, item_comp) -> begin
((

let uu____4078 = (

let uu____4079 = (FStar_Syntax_Util.is_total_lcomp item_comp)
in (not (uu____4079)))
in (match (uu____4078) with
| true -> begin
(

let uu____4080 = (

let uu____4085 = (

let uu____4086 = (FStar_Syntax_Print.term_to_string item2)
in (

let uu____4087 = (FStar_Syntax_Print.lcomp_to_string item_comp)
in (FStar_Util.format2 "Computation for [%s] is not total : %s !" uu____4086 uu____4087)))
in ((FStar_Errors.Fatal_ComputationNotTotal), (uu____4085)))
in (FStar_Errors.raise_err uu____4080))
end
| uu____4088 -> begin
()
end));
(

let uu____4089 = (FStar_TypeChecker_DMFF.star_expr dmff_env1 item2)
in (match (uu____4089) with
| (item_t, item_wp, item_elab) -> begin
(

let uu____4107 = (recheck_debug "*" env2 item_wp)
in (

let uu____4108 = (recheck_debug "_" env2 item_elab)
in ((dmff_env1), (item_t), (item_wp), (item_elab))))
end));
)
end))
end))))
in (

let uu____4109 = (elaborate_and_star dmff_env [] ed.FStar_Syntax_Syntax.bind_repr)
in (match (uu____4109) with
| (dmff_env1, uu____4135, bind_wp, bind_elab) -> begin
(

let uu____4138 = (elaborate_and_star dmff_env1 [] ed.FStar_Syntax_Syntax.return_repr)
in (match (uu____4138) with
| (dmff_env2, uu____4164, return_wp, return_elab) -> begin
(

let rc_gtot = {FStar_Syntax_Syntax.residual_effect = FStar_Parser_Const.effect_GTot_lid; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.None; FStar_Syntax_Syntax.residual_flags = []}
in (

let lift_from_pure_wp = (

let uu____4173 = (

let uu____4174 = (FStar_Syntax_Subst.compress return_wp)
in uu____4174.FStar_Syntax_Syntax.n)
in (match (uu____4173) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(

let uu____4232 = (

let uu____4251 = (

let uu____4256 = (FStar_Syntax_Util.abs bs body FStar_Pervasives_Native.None)
in (FStar_Syntax_Subst.open_term ((b1)::(b2)::[]) uu____4256))
in (match (uu____4251) with
| ((b11)::(b21)::[], body1) -> begin
((b11), (b21), (body1))
end
| uu____4338 -> begin
(failwith "Impossible : open_term not preserving binders arity")
end))
in (match (uu____4232) with
| (b11, b21, body1) -> begin
(

let env0 = (

let uu____4391 = (FStar_TypeChecker_DMFF.get_env dmff_env2)
in (FStar_TypeChecker_Env.push_binders uu____4391 ((b11)::(b21)::[])))
in (

let wp_b1 = (

let raw_wp_b1 = (

let uu____4414 = (

let uu____4415 = (

let uu____4432 = (

let uu____4443 = (

let uu____4452 = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst b11))
in (

let uu____4457 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____4452), (uu____4457))))
in (uu____4443)::[])
in ((wp_type), (uu____4432)))
in FStar_Syntax_Syntax.Tm_app (uu____4415))
in (mk1 uu____4414))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::[]) env0 raw_wp_b1))
in (

let uu____4492 = (

let uu____4501 = (

let uu____4502 = (FStar_Syntax_Util.unascribe wp_b1)
in (FStar_TypeChecker_Normalize.eta_expand_with_type env0 body1 uu____4502))
in (FStar_All.pipe_left FStar_Syntax_Util.abs_formals uu____4501))
in (match (uu____4492) with
| (bs1, body2, what') -> begin
(

let fail1 = (fun uu____4525 -> (

let error_msg = (

let uu____4527 = (FStar_Syntax_Print.term_to_string body2)
in (

let uu____4528 = (match (what') with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (rc) -> begin
(FStar_Ident.text_of_lid rc.FStar_Syntax_Syntax.residual_effect)
end)
in (FStar_Util.format2 "The body of return_wp (%s) should be of type Type0 but is of type %s" uu____4527 uu____4528)))
in (raise_error1 ((FStar_Errors.Fatal_WrongBodyTypeForReturnWP), (error_msg)))))
in ((match (what') with
| FStar_Pervasives_Native.None -> begin
(fail1 ())
end
| FStar_Pervasives_Native.Some (rc) -> begin
((

let uu____4533 = (

let uu____4534 = (FStar_Syntax_Util.is_pure_effect rc.FStar_Syntax_Syntax.residual_effect)
in (not (uu____4534)))
in (match (uu____4533) with
| true -> begin
(fail1 ())
end
| uu____4535 -> begin
()
end));
(

let uu____4536 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun rt -> (

let g_opt = (FStar_TypeChecker_Rel.try_teq true env1 rt FStar_Syntax_Util.ktype0)
in (match (g_opt) with
| FStar_Pervasives_Native.Some (g') -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env1 g')
end
| FStar_Pervasives_Native.None -> begin
(fail1 ())
end))))
in (FStar_All.pipe_right uu____4536 (fun a1 -> ())));
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

let uu____4563 = (

let uu____4568 = (FStar_Syntax_Syntax.bv_to_name wp)
in (

let uu____4569 = (

let uu____4570 = (

let uu____4579 = (FStar_Syntax_Util.abs ((b21)::[]) body2 what')
in ((uu____4579), (FStar_Pervasives_Native.None)))
in (uu____4570)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____4568 uu____4569)))
in (uu____4563 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let uu____4616 = (

let uu____4617 = (

let uu____4626 = (FStar_Syntax_Syntax.mk_binder wp)
in (uu____4626)::[])
in (b11)::uu____4617)
in (

let uu____4651 = (FStar_Syntax_Util.abs bs1 body3 what)
in (FStar_Syntax_Util.abs uu____4616 uu____4651 (FStar_Pervasives_Native.Some (rc_gtot)))))));
))
end))))
end))
end
| uu____4654 -> begin
(raise_error1 ((FStar_Errors.Fatal_UnexpectedReturnShape), ("unexpected shape for return")))
end))
in (

let return_wp1 = (

let uu____4660 = (

let uu____4661 = (FStar_Syntax_Subst.compress return_wp)
in uu____4661.FStar_Syntax_Syntax.n)
in (match (uu____4660) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(

let uu____4719 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs ((b1)::(b2)::[]) uu____4719 (FStar_Pervasives_Native.Some (rc_gtot))))
end
| uu____4740 -> begin
(raise_error1 ((FStar_Errors.Fatal_UnexpectedReturnShape), ("unexpected shape for return")))
end))
in (

let bind_wp1 = (

let uu____4746 = (

let uu____4747 = (FStar_Syntax_Subst.compress bind_wp)
in uu____4747.FStar_Syntax_Syntax.n)
in (match (uu____4746) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let r = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.range_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let uu____4780 = (

let uu____4781 = (

let uu____4790 = (

let uu____4797 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (r)))
in (FStar_Syntax_Syntax.null_binder uu____4797))
in (uu____4790)::[])
in (FStar_List.append uu____4781 binders))
in (FStar_Syntax_Util.abs uu____4780 body what)))
end
| uu____4816 -> begin
(raise_error1 ((FStar_Errors.Fatal_UnexpectedBindShape), ("unexpected shape for bind")))
end))
in (

let apply_close = (fun t -> (match ((Prims.op_Equality (FStar_List.length effect_binders1) (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____4839 -> begin
(

let uu____4840 = (

let uu____4841 = (

let uu____4842 = (

let uu____4859 = (

let uu____4870 = (FStar_Syntax_Util.args_of_binders effect_binders1)
in (FStar_Pervasives_Native.snd uu____4870))
in ((t), (uu____4859)))
in FStar_Syntax_Syntax.Tm_app (uu____4842))
in (mk1 uu____4841))
in (FStar_Syntax_Subst.close effect_binders1 uu____4840))
end))
in (

let rec apply_last1 = (fun f l -> (match (l) with
| [] -> begin
(failwith "empty path..")
end
| (a2)::[] -> begin
(

let uu____4914 = (f a2)
in (uu____4914)::[])
end
| (x)::xs -> begin
(

let uu____4919 = (apply_last1 f xs)
in (x)::uu____4919)
end))
in (

let register = (fun name item -> (

let p = (FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname)
in (

let p' = (apply_last1 (fun s -> (Prims.strcat "__" (Prims.strcat s (Prims.strcat "_eff_override_" name)))) p)
in (

let l' = (FStar_Ident.lid_of_path p' FStar_Range.dummyRange)
in (

let uu____4945 = (FStar_TypeChecker_Env.try_lookup_lid env1 l')
in (match (uu____4945) with
| FStar_Pervasives_Native.Some (_us, _t) -> begin
((

let uu____4975 = (FStar_Options.debug_any ())
in (match (uu____4975) with
| true -> begin
(

let uu____4976 = (FStar_Ident.string_of_lid l')
in (FStar_Util.print1 "DM4F: Applying override %s\n" uu____4976))
end
| uu____4977 -> begin
()
end));
(

let uu____4978 = (FStar_Syntax_Syntax.lid_as_fv l' FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____4978));
)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4987 = (

let uu____4992 = (mk_lid name)
in (

let uu____4993 = (FStar_Syntax_Util.abs effect_binders1 item FStar_Pervasives_Native.None)
in (FStar_TypeChecker_Util.mk_toplevel_definition env1 uu____4992 uu____4993)))
in (match (uu____4987) with
| (sigelt, fv) -> begin
((

let uu____4997 = (

let uu____5000 = (FStar_ST.op_Bang sigelts)
in (sigelt)::uu____5000)
in (FStar_ST.op_Colon_Equals sigelts uu____4997));
fv;
)
end))
end))))))
in (

let lift_from_pure_wp1 = (register "lift_from_pure" lift_from_pure_wp)
in (

let return_wp2 = (register "return_wp" return_wp1)
in ((

let uu____5096 = (

let uu____5099 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions (FStar_Pervasives_Native.Some ("--admit_smt_queries true")))))
in (

let uu____5100 = (FStar_ST.op_Bang sigelts)
in (uu____5099)::uu____5100))
in (FStar_ST.op_Colon_Equals sigelts uu____5096));
(

let return_elab1 = (register "return_elab" return_elab)
in ((

let uu____5195 = (

let uu____5198 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions)))
in (

let uu____5199 = (FStar_ST.op_Bang sigelts)
in (uu____5198)::uu____5199))
in (FStar_ST.op_Colon_Equals sigelts uu____5195));
(

let bind_wp2 = (register "bind_wp" bind_wp1)
in ((

let uu____5294 = (

let uu____5297 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions (FStar_Pervasives_Native.Some ("--admit_smt_queries true")))))
in (

let uu____5298 = (FStar_ST.op_Bang sigelts)
in (uu____5297)::uu____5298))
in (FStar_ST.op_Colon_Equals sigelts uu____5294));
(

let bind_elab1 = (register "bind_elab" bind_elab)
in ((

let uu____5393 = (

let uu____5396 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions)))
in (

let uu____5397 = (FStar_ST.op_Bang sigelts)
in (uu____5396)::uu____5397))
in (FStar_ST.op_Colon_Equals sigelts uu____5393));
(

let uu____5490 = (FStar_List.fold_left (fun uu____5530 action -> (match (uu____5530) with
| (dmff_env3, actions) -> begin
(

let params_un = (FStar_Syntax_Subst.open_binders action.FStar_Syntax_Syntax.action_params)
in (

let uu____5551 = (

let uu____5558 = (FStar_TypeChecker_DMFF.get_env dmff_env3)
in (FStar_TypeChecker_TcTerm.tc_tparams uu____5558 params_un))
in (match (uu____5551) with
| (action_params, env', uu____5567) -> begin
(

let action_params1 = (FStar_List.map (fun uu____5593 -> (match (uu____5593) with
| (bv, qual) -> begin
(

let uu____5612 = (

let uu___391_5613 = bv
in (

let uu____5614 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.EraseUniverses)::[]) env' bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___391_5613.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___391_5613.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5614}))
in ((uu____5612), (qual)))
end)) action_params)
in (

let dmff_env' = (FStar_TypeChecker_DMFF.set_env dmff_env3 env')
in (

let uu____5620 = (elaborate_and_star dmff_env' action_params1 ((action.FStar_Syntax_Syntax.action_univs), (action.FStar_Syntax_Syntax.action_defn)))
in (match (uu____5620) with
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
| uu____5658 -> begin
(

let uu____5659 = (FStar_Syntax_Syntax.mk_Total action_typ_with_wp1)
in (FStar_Syntax_Util.flat_arrow action_params2 uu____5659))
end)
in ((

let uu____5663 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("ED")))
in (match (uu____5663) with
| true -> begin
(

let uu____5664 = (FStar_Syntax_Print.binders_to_string "," params_un)
in (

let uu____5665 = (FStar_Syntax_Print.binders_to_string "," action_params2)
in (

let uu____5666 = (FStar_Syntax_Print.term_to_string action_typ_with_wp2)
in (

let uu____5667 = (FStar_Syntax_Print.term_to_string action_elab2)
in (FStar_Util.print4 "original action_params %s, end action_params %s, type %s, term %s\n" uu____5664 uu____5665 uu____5666 uu____5667)))))
end
| uu____5668 -> begin
()
end));
(

let action_elab3 = (register (Prims.strcat name "_elab") action_elab2)
in (

let action_typ_with_wp3 = (register (Prims.strcat name "_complete_type") action_typ_with_wp2)
in (

let uu____5671 = (

let uu____5674 = (

let uu___392_5675 = action
in (

let uu____5676 = (apply_close action_elab3)
in (

let uu____5677 = (apply_close action_typ_with_wp3)
in {FStar_Syntax_Syntax.action_name = uu___392_5675.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___392_5675.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___392_5675.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = []; FStar_Syntax_Syntax.action_defn = uu____5676; FStar_Syntax_Syntax.action_typ = uu____5677})))
in (uu____5674)::actions)
in ((dmff_env4), (uu____5671)))));
))))))))
end))))
end)))
end)) ((dmff_env2), ([])) ed.FStar_Syntax_Syntax.actions)
in (match (uu____5490) with
| (dmff_env3, actions) -> begin
(

let actions1 = (FStar_List.rev actions)
in (

let repr1 = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp_a" FStar_Pervasives_Native.None wp_a)
in (

let binders = (

let uu____5720 = (FStar_Syntax_Syntax.mk_binder a1)
in (

let uu____5727 = (

let uu____5736 = (FStar_Syntax_Syntax.mk_binder wp)
in (uu____5736)::[])
in (uu____5720)::uu____5727))
in (

let uu____5761 = (

let uu____5764 = (

let uu____5765 = (

let uu____5766 = (

let uu____5783 = (

let uu____5794 = (

let uu____5803 = (FStar_Syntax_Syntax.bv_to_name a1)
in (

let uu____5806 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____5803), (uu____5806))))
in (uu____5794)::[])
in ((repr), (uu____5783)))
in FStar_Syntax_Syntax.Tm_app (uu____5766))
in (mk1 uu____5765))
in (

let uu____5841 = (FStar_Syntax_Syntax.bv_to_name wp)
in (FStar_TypeChecker_DMFF.trans_F dmff_env3 uu____5764 uu____5841)))
in (FStar_Syntax_Util.abs binders uu____5761 FStar_Pervasives_Native.None))))
in (

let uu____5842 = (recheck_debug "FC" env1 repr1)
in (

let repr2 = (register "repr" repr1)
in (

let uu____5844 = (

let uu____5853 = (

let uu____5854 = (

let uu____5857 = (FStar_Syntax_Subst.compress wp_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____5857))
in uu____5854.FStar_Syntax_Syntax.n)
in (match (uu____5853) with
| FStar_Syntax_Syntax.Tm_abs ((type_param)::effect_param, arrow1, uu____5871) -> begin
(

let uu____5908 = (

let uu____5929 = (FStar_Syntax_Subst.open_term ((type_param)::effect_param) arrow1)
in (match (uu____5929) with
| ((b)::bs, body) -> begin
((b), (bs), (body))
end
| uu____5997 -> begin
(failwith "Impossible : open_term nt preserving binders arity")
end))
in (match (uu____5908) with
| (type_param1, effect_param1, arrow2) -> begin
(

let uu____6061 = (

let uu____6062 = (

let uu____6065 = (FStar_Syntax_Subst.compress arrow2)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____6065))
in uu____6062.FStar_Syntax_Syntax.n)
in (match (uu____6061) with
| FStar_Syntax_Syntax.Tm_arrow (wp_binders, c) -> begin
(

let uu____6098 = (FStar_Syntax_Subst.open_comp wp_binders c)
in (match (uu____6098) with
| (wp_binders1, c1) -> begin
(

let uu____6113 = (FStar_List.partition (fun uu____6144 -> (match (uu____6144) with
| (bv, uu____6152) -> begin
(

let uu____6157 = (

let uu____6158 = (FStar_Syntax_Free.names bv.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____6158 (FStar_Util.set_mem (FStar_Pervasives_Native.fst type_param1))))
in (FStar_All.pipe_right uu____6157 Prims.op_Negation))
end)) wp_binders1)
in (match (uu____6113) with
| (pre_args, post_args) -> begin
(

let post = (match (post_args) with
| (post)::[] -> begin
post
end
| [] -> begin
(

let err_msg = (

let uu____6246 = (FStar_Syntax_Print.term_to_string arrow2)
in (FStar_Util.format1 "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)" uu____6246))
in (FStar_Errors.raise_err ((FStar_Errors.Fatal_ImpossibleToGenerateDMEffect), (err_msg))))
end
| uu____6253 -> begin
(

let err_msg = (

let uu____6263 = (FStar_Syntax_Print.term_to_string arrow2)
in (FStar_Util.format1 "Impossible to generate DM effect: multiple post candidates %s" uu____6263))
in (FStar_Errors.raise_err ((FStar_Errors.Fatal_ImpossibleToGenerateDMEffect), (err_msg))))
end)
in (

let uu____6270 = (FStar_Syntax_Util.arrow pre_args c1)
in (

let uu____6273 = (FStar_Syntax_Util.abs ((type_param1)::effect_param1) (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort FStar_Pervasives_Native.None)
in ((uu____6270), (uu____6273)))))
end))
end))
end
| uu____6288 -> begin
(

let uu____6289 = (

let uu____6294 = (

let uu____6295 = (FStar_Syntax_Print.term_to_string arrow2)
in (FStar_Util.format1 "Impossible: pre/post arrow %s" uu____6295))
in ((FStar_Errors.Fatal_ImpossiblePrePostArrow), (uu____6294)))
in (raise_error1 uu____6289))
end))
end))
end
| uu____6304 -> begin
(

let uu____6305 = (

let uu____6310 = (

let uu____6311 = (FStar_Syntax_Print.term_to_string wp_type)
in (FStar_Util.format1 "Impossible: pre/post abs %s" uu____6311))
in ((FStar_Errors.Fatal_ImpossiblePrePostAbs), (uu____6310)))
in (raise_error1 uu____6305))
end))
in (match (uu____5844) with
| (pre, post) -> begin
((

let uu____6341 = (register "pre" pre)
in ());
(

let uu____6343 = (register "post" post)
in ());
(

let uu____6345 = (register "wp" wp_type)
in ());
(

let ed1 = (

let uu___393_6347 = ed
in (

let uu____6348 = (FStar_Syntax_Subst.close_binders effect_binders1)
in (

let uu____6349 = (FStar_Syntax_Subst.close effect_binders1 effect_signature)
in (

let uu____6350 = (

let uu____6351 = (apply_close return_wp2)
in (([]), (uu____6351)))
in (

let uu____6358 = (

let uu____6359 = (apply_close bind_wp2)
in (([]), (uu____6359)))
in (

let uu____6366 = (apply_close repr2)
in (

let uu____6367 = (

let uu____6368 = (apply_close return_elab1)
in (([]), (uu____6368)))
in (

let uu____6375 = (

let uu____6376 = (apply_close bind_elab1)
in (([]), (uu____6376)))
in {FStar_Syntax_Syntax.cattributes = uu___393_6347.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___393_6347.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___393_6347.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu____6348; FStar_Syntax_Syntax.signature = uu____6349; FStar_Syntax_Syntax.ret_wp = uu____6350; FStar_Syntax_Syntax.bind_wp = uu____6358; FStar_Syntax_Syntax.if_then_else = uu___393_6347.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = uu___393_6347.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = uu___393_6347.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = uu___393_6347.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = uu___393_6347.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = uu___393_6347.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = uu___393_6347.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = uu___393_6347.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = uu____6366; FStar_Syntax_Syntax.return_repr = uu____6367; FStar_Syntax_Syntax.bind_repr = uu____6375; FStar_Syntax_Syntax.actions = actions1; FStar_Syntax_Syntax.eff_attrs = uu___393_6347.FStar_Syntax_Syntax.eff_attrs}))))))))
in (

let uu____6383 = (FStar_TypeChecker_DMFF.gen_wps_for_free env1 effect_binders1 a1 wp_a ed1)
in (match (uu____6383) with
| (sigelts', ed2) -> begin
((

let uu____6401 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____6401) with
| true -> begin
(

let uu____6402 = (FStar_Syntax_Print.eff_decl_to_string true ed2)
in (FStar_Util.print_string uu____6402))
end
| uu____6403 -> begin
()
end));
(

let lift_from_pure_opt = (match ((Prims.op_Equality (FStar_List.length effect_binders1) (Prims.parse_int "0"))) with
| true -> begin
(

let lift_from_pure = (

let uu____6416 = (

let uu____6419 = (

let uu____6420 = (apply_close lift_from_pure_wp1)
in (([]), (uu____6420)))
in FStar_Pervasives_Native.Some (uu____6419))
in {FStar_Syntax_Syntax.source = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.target = ed2.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.lift_wp = uu____6416; FStar_Syntax_Syntax.lift = FStar_Pervasives_Native.None})
in (

let uu____6427 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_sub_effect (lift_from_pure)))
in FStar_Pervasives_Native.Some (uu____6427)))
end
| uu____6428 -> begin
FStar_Pervasives_Native.None
end)
in (

let uu____6429 = (

let uu____6432 = (

let uu____6435 = (FStar_ST.op_Bang sigelts)
in (FStar_List.rev uu____6435))
in (FStar_List.append uu____6432 sigelts'))
in ((uu____6429), (ed2), (lift_from_pure_opt))));
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


let tc_lex_t : 'Auu____6497 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  'Auu____6497 Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (

let err_range = (

let uu____6532 = (FStar_List.hd ses)
in uu____6532.FStar_Syntax_Syntax.sigrng)
in ((match (lids) with
| (lex_t1)::(lex_top1)::(lex_cons)::[] when (((FStar_Ident.lid_equals lex_t1 FStar_Parser_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top1 FStar_Parser_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Parser_Const.lexcons_lid)) -> begin
()
end
| uu____6537 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_InvalidRedefinitionOfLexT), ("Invalid (partial) redefinition of lex_t")) err_range)
end);
(match (ses) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (lex_t1, uu____6541, [], t, uu____6543, uu____6544); FStar_Syntax_Syntax.sigrng = r; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = uu____6546; FStar_Syntax_Syntax.sigattrs = uu____6547})::({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (lex_top1, uu____6549, _t_top, _lex_t_top, _0_1, uu____6552); FStar_Syntax_Syntax.sigrng = r1; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = uu____6554; FStar_Syntax_Syntax.sigattrs = uu____6555})::({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (lex_cons, uu____6557, _t_cons, _lex_t_cons, _0_2, uu____6560); FStar_Syntax_Syntax.sigrng = r2; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = uu____6562; FStar_Syntax_Syntax.sigattrs = uu____6563})::[] when (((_0_1 = (Prims.parse_int "0")) && (_0_2 = (Prims.parse_int "0"))) && (((FStar_Ident.lid_equals lex_t1 FStar_Parser_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top1 FStar_Parser_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Parser_Const.lexcons_lid))) -> begin
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

let uu____6612 = (

let uu____6619 = (

let uu____6620 = (

let uu____6627 = (

let uu____6630 = (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar uu____6630 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None))
in ((uu____6627), ((FStar_Syntax_Syntax.U_name (utop))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____6620))
in (FStar_Syntax_Syntax.mk uu____6619))
in (uu____6612 FStar_Pervasives_Native.None r1))
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

let uu____6646 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) FStar_Pervasives_Native.None r2)
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (r2)) uu____6646))
in (

let hd1 = (

let uu____6648 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (r2)) uu____6648))
in (

let tl1 = (

let uu____6650 = (

let uu____6651 = (

let uu____6658 = (

let uu____6659 = (

let uu____6666 = (

let uu____6669 = (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar uu____6669 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None))
in ((uu____6666), ((FStar_Syntax_Syntax.U_name (ucons2))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____6659))
in (FStar_Syntax_Syntax.mk uu____6658))
in (uu____6651 FStar_Pervasives_Native.None r2))
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (r2)) uu____6650))
in (

let res = (

let uu____6678 = (

let uu____6685 = (

let uu____6686 = (

let uu____6693 = (

let uu____6696 = (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar uu____6696 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None))
in ((uu____6693), ((FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____6686))
in (FStar_Syntax_Syntax.mk uu____6685))
in (uu____6678 FStar_Pervasives_Native.None r2))
in (

let uu____6702 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow ((((a), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::(((hd1), (FStar_Pervasives_Native.None)))::(((tl1), (FStar_Pervasives_Native.None)))::[]) uu____6702))))))
in (

let lex_cons_t1 = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((lex_cons), ((ucons1)::(ucons2)::[]), (lex_cons_t1), (FStar_Parser_Const.lex_t_lid), ((Prims.parse_int "0")), ([]))); FStar_Syntax_Syntax.sigrng = r2; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (

let uu____6739 = (FStar_TypeChecker_Env.get_range env)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle ((((tc)::(dc_lextop)::(dc_lexcons)::[]), (lids))); FStar_Syntax_Syntax.sigrng = uu____6739; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))))))))))))))
end
| uu____6744 -> begin
(

let err_msg = (

let uu____6748 = (

let uu____6749 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_bundle (((ses), (lids)))))
in (FStar_Syntax_Print.sigelt_to_string uu____6749))
in (FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n" uu____6748))
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_InvalidRedefinitionOfLexT), (err_msg)) err_range))
end);
)))


let tc_type_common : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.typ  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.tscheme = (fun env uu____6771 expected_typ1 r -> (match (uu____6771) with
| (uvs, t) -> begin
(

let uu____6784 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____6784) with
| (uvs1, t1) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env uvs1)
in (

let t2 = (tc_check_trivial_guard env1 t1 expected_typ1)
in (match ((Prims.op_Equality uvs1 [])) with
| true -> begin
(

let uu____6795 = (FStar_TypeChecker_Util.generalize_universes env1 t2)
in (match (uu____6795) with
| (uvs2, t3) -> begin
((FStar_TypeChecker_Util.check_uvars r t3);
((uvs2), (t3));
)
end))
end
| uu____6811 -> begin
(

let uu____6812 = (

let uu____6815 = (FStar_All.pipe_right t2 (FStar_TypeChecker_Normalize.remove_uvar_solutions env1))
in (FStar_All.pipe_right uu____6815 (FStar_Syntax_Subst.close_univ_vars uvs1)))
in ((uvs1), (uu____6812)))
end)))
end))
end))


let tc_declare_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.tscheme = (fun env ts r -> (

let uu____6837 = (

let uu____6838 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____6838 FStar_Pervasives_Native.fst))
in (tc_type_common env ts uu____6837 r)))


let tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.tscheme = (fun env ts r -> (

let uu____6862 = (

let uu____6863 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____6863 FStar_Pervasives_Native.fst))
in (tc_type_common env ts uu____6862 r)))


let tc_inductive' : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env ses quals lids -> ((

let uu____6911 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____6911) with
| true -> begin
(

let uu____6912 = (FStar_Common.string_of_list FStar_Syntax_Print.sigelt_to_string ses)
in (FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____6912))
end
| uu____6913 -> begin
()
end));
(

let uu____6914 = (FStar_TypeChecker_TcInductive.check_inductive_well_typedness env ses quals lids)
in (match (uu____6914) with
| (sig_bndle, tcs, datas) -> begin
(

let data_ops_ses = (

let uu____6945 = (FStar_List.map (FStar_TypeChecker_TcInductive.mk_data_operations quals env tcs) datas)
in (FStar_All.pipe_right uu____6945 FStar_List.flatten))
in ((

let uu____6959 = ((FStar_Options.no_positivity ()) || (

let uu____6961 = (FStar_TypeChecker_Env.should_verify env)
in (not (uu____6961))))
in (match (uu____6959) with
| true -> begin
()
end
| uu____6962 -> begin
(

let env1 = (FStar_TypeChecker_Env.push_sigelt env sig_bndle)
in ((FStar_List.iter (fun ty -> (

let b = (FStar_TypeChecker_TcInductive.check_positivity ty env1)
in (match ((not (b))) with
| true -> begin
(

let uu____6972 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____6982, uu____6983, uu____6984, uu____6985, uu____6986) -> begin
((lid), (ty.FStar_Syntax_Syntax.sigrng))
end
| uu____6995 -> begin
(failwith "Impossible!")
end)
in (match (uu____6972) with
| (lid, r) -> begin
(FStar_Errors.log_issue r ((FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition), ((Prims.strcat "Inductive type " (Prims.strcat lid.FStar_Ident.str " does not satisfy the positivity condition")))))
end))
end
| uu____7002 -> begin
()
end))) tcs);
(FStar_List.iter (fun d -> (

let uu____7009 = (match (d.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (data_lid, uu____7019, uu____7020, ty_lid, uu____7022, uu____7023) -> begin
((data_lid), (ty_lid))
end
| uu____7028 -> begin
(failwith "Impossible")
end)
in (match (uu____7009) with
| (data_lid, ty_lid) -> begin
(

let uu____7035 = ((FStar_Ident.lid_equals ty_lid FStar_Parser_Const.exn_lid) && (

let uu____7037 = (FStar_TypeChecker_TcInductive.check_exn_positivity data_lid env1)
in (not (uu____7037))))
in (match (uu____7035) with
| true -> begin
(FStar_Errors.log_issue d.FStar_Syntax_Syntax.sigrng ((FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition), ((Prims.strcat "Exception " (Prims.strcat data_lid.FStar_Ident.str " does not satisfy the positivity condition")))))
end
| uu____7038 -> begin
()
end))
end))) datas);
))
end));
(

let skip_prims_type = (fun uu____7044 -> (

let lid = (

let ty = (FStar_List.hd tcs)
in (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____7048, uu____7049, uu____7050, uu____7051, uu____7052) -> begin
lid
end
| uu____7061 -> begin
(failwith "Impossible")
end))
in (FStar_List.existsb (fun s -> (Prims.op_Equality s lid.FStar_Ident.ident.FStar_Ident.idText)) FStar_TypeChecker_TcInductive.early_prims_inductives)))
in (

let is_noeq = (FStar_List.existsb (fun q -> (Prims.op_Equality q FStar_Syntax_Syntax.Noeq)) quals)
in (

let res = (

let uu____7074 = (((Prims.op_Equality (FStar_List.length tcs) (Prims.parse_int "0")) || ((FStar_Ident.lid_equals env.FStar_TypeChecker_Env.curmodule FStar_Parser_Const.prims_lid) && (skip_prims_type ()))) || is_noeq)
in (match (uu____7074) with
| true -> begin
((sig_bndle), (data_ops_ses))
end
| uu____7083 -> begin
(

let is_unopteq = (FStar_List.existsb (fun q -> (Prims.op_Equality q FStar_Syntax_Syntax.Unopteq)) quals)
in (

let ses1 = (match (is_unopteq) with
| true -> begin
(FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme sig_bndle tcs datas env)
end
| uu____7092 -> begin
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

let pop1 = (fun uu____7139 -> (

let uu____7140 = (FStar_TypeChecker_Env.pop env1 "tc_inductive")
in ()))
in (FStar_All.try_with (fun uu___395_7149 -> (match (()) with
| () -> begin
(

let uu____7156 = (tc_inductive' env1 ses quals lids)
in (FStar_All.pipe_right uu____7156 (fun r -> ((pop1 ());
r;
))))
end)) (fun uu___394_7187 -> ((pop1 ());
(FStar_Exn.raise uu___394_7187);
))))))


let z3_reset_options : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun en -> (

let env = (

let uu____7207 = (FStar_Options.using_facts_from ())
in (FStar_TypeChecker_Env.set_proof_ns uu____7207 en))
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
| uu____7437 -> begin
FStar_Pervasives_Native.None
end))
in (FStar_List.fold_right (fun at acc -> (

let uu____7485 = (FStar_ToSyntax_ToSyntax.get_fail_attr true at)
in (comb uu____7485 acc))) se.FStar_Syntax_Syntax.sigattrs FStar_Pervasives_Native.None)))


let list_of_option : 'Auu____7504 . 'Auu____7504 FStar_Pervasives_Native.option  ->  'Auu____7504 Prims.list = (fun uu___373_7513 -> (match (uu___373_7513) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (x) -> begin
(x)::[]
end))


let check_multi_contained : Prims.int Prims.list  ->  Prims.int Prims.list  ->  (Prims.int * Prims.int * Prims.int) FStar_Pervasives_Native.option = (fun l1 l2 -> (

let rec collect1 = (fun l -> (match (l) with
| [] -> begin
[]
end
| (hd1)::tl1 -> begin
(

let uu____7580 = (collect1 tl1)
in (match (uu____7580) with
| [] -> begin
(((hd1), ((Prims.parse_int "1"))))::[]
end
| ((h, n1))::t -> begin
(match ((Prims.op_Equality h hd1)) with
| true -> begin
(((h), ((n1 + (Prims.parse_int "1")))))::t
end
| uu____7628 -> begin
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
| (((e, n1))::uu____7758, []) -> begin
FStar_Pervasives_Native.Some (((e), (n1), ((Prims.parse_int "0"))))
end
| ([], ((e, n1))::uu____7793) -> begin
FStar_Pervasives_Native.Some (((e), ((Prims.parse_int "0")), (n1)))
end
| (((hd1, n1))::tl1, ((hd2, n2))::tl2) when (Prims.op_disEquality hd1 hd2) -> begin
FStar_Pervasives_Native.Some (((hd1), (n1), ((Prims.parse_int "0"))))
end
| (((hd1, n1))::tl1, ((hd2, n2))::tl2) -> begin
(match ((Prims.op_disEquality n1 n2)) with
| true -> begin
FStar_Pervasives_Native.Some (((hd1), (n1), (n2)))
end
| uu____7922 -> begin
(aux tl1 tl2)
end)
end))
in (aux l11 l21)))))))


let tc_decl' : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env0 se -> (

let env = env0
in ((FStar_TypeChecker_Util.check_sigelt_quals env se);
(

let r = se.FStar_Syntax_Syntax.sigrng
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____7966) -> begin
(failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____7993) -> begin
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

let uu____8050 = ((FStar_Options.use_two_phase_tc ()) && (FStar_TypeChecker_Env.should_verify env1))
in (match (uu____8050) with
| true -> begin
(

let ses1 = (

let uu____8056 = (

let uu____8057 = (

let uu____8058 = (tc_inductive (

let uu___396_8067 = env1
in {FStar_TypeChecker_Env.solver = uu___396_8067.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___396_8067.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___396_8067.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___396_8067.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___396_8067.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___396_8067.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___396_8067.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___396_8067.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___396_8067.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___396_8067.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___396_8067.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___396_8067.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___396_8067.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___396_8067.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___396_8067.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___396_8067.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___396_8067.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___396_8067.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___396_8067.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___396_8067.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___396_8067.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = true; FStar_TypeChecker_Env.failhard = uu___396_8067.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___396_8067.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___396_8067.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___396_8067.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___396_8067.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___396_8067.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___396_8067.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___396_8067.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___396_8067.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___396_8067.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___396_8067.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___396_8067.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___396_8067.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___396_8067.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___396_8067.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___396_8067.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___396_8067.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___396_8067.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___396_8067.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___396_8067.FStar_TypeChecker_Env.nbe}) ses se.FStar_Syntax_Syntax.sigquals lids)
in (FStar_All.pipe_right uu____8058 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____8057 (FStar_TypeChecker_Normalize.elim_uvars env1)))
in (FStar_All.pipe_right uu____8056 FStar_Syntax_Util.ses_of_sigbundle))
in ((

let uu____8079 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("TwoPhases")))
in (match (uu____8079) with
| true -> begin
(

let uu____8080 = (FStar_Syntax_Print.sigelt_to_string (

let uu___397_8083 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (((ses1), (lids))); FStar_Syntax_Syntax.sigrng = uu___397_8083.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___397_8083.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___397_8083.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___397_8083.FStar_Syntax_Syntax.sigattrs}))
in (FStar_Util.print1 "Inductive after phase 1: %s\n" uu____8080))
end
| uu____8088 -> begin
()
end));
ses1;
))
end
| uu____8089 -> begin
ses
end))
in (

let uu____8090 = (tc_inductive env1 ses1 se.FStar_Syntax_Syntax.sigquals lids)
in (match (uu____8090) with
| (sigbndle, projectors_ses) -> begin
(

let sigbndle1 = (

let uu___398_8114 = sigbndle
in {FStar_Syntax_Syntax.sigel = uu___398_8114.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___398_8114.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___398_8114.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___398_8114.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = se.FStar_Syntax_Syntax.sigattrs})
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

let uu____8126 = (cps_and_elaborate env ne)
in (match (uu____8126) with
| (ses, ne1, lift_from_pure_opt) -> begin
(

let effect_and_lift_ses = (match (lift_from_pure_opt) with
| FStar_Pervasives_Native.Some (lift) -> begin
((

let uu___399_8165 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne1); FStar_Syntax_Syntax.sigrng = uu___399_8165.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___399_8165.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___399_8165.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___399_8165.FStar_Syntax_Syntax.sigattrs}))::(lift)::[]
end
| FStar_Pervasives_Native.None -> begin
((

let uu___400_8167 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne1); FStar_Syntax_Syntax.sigrng = uu___400_8167.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___400_8167.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___400_8167.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___400_8167.FStar_Syntax_Syntax.sigattrs}))::[]
end)
in (([]), ((FStar_List.append ses effect_and_lift_ses)), (env0)))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let ne1 = (

let uu____8174 = ((FStar_Options.use_two_phase_tc ()) && (FStar_TypeChecker_Env.should_verify env))
in (match (uu____8174) with
| true -> begin
(

let ne1 = (

let uu____8176 = (

let uu____8177 = (

let uu____8178 = (tc_eff_decl (

let uu___401_8181 = env
in {FStar_TypeChecker_Env.solver = uu___401_8181.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___401_8181.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___401_8181.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___401_8181.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___401_8181.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___401_8181.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___401_8181.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___401_8181.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___401_8181.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___401_8181.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___401_8181.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___401_8181.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___401_8181.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___401_8181.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___401_8181.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___401_8181.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___401_8181.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___401_8181.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___401_8181.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___401_8181.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___401_8181.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = true; FStar_TypeChecker_Env.failhard = uu___401_8181.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___401_8181.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___401_8181.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___401_8181.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___401_8181.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___401_8181.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___401_8181.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___401_8181.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___401_8181.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___401_8181.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___401_8181.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___401_8181.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___401_8181.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___401_8181.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___401_8181.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___401_8181.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___401_8181.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___401_8181.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___401_8181.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___401_8181.FStar_TypeChecker_Env.nbe}) ne)
in (FStar_All.pipe_right uu____8178 (fun ne1 -> (

let uu___402_8185 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne1); FStar_Syntax_Syntax.sigrng = uu___402_8185.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___402_8185.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___402_8185.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___402_8185.FStar_Syntax_Syntax.sigattrs}))))
in (FStar_All.pipe_right uu____8177 (FStar_TypeChecker_Normalize.elim_uvars env)))
in (FStar_All.pipe_right uu____8176 FStar_Syntax_Util.eff_decl_of_new_effect))
in ((

let uu____8187 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("TwoPhases")))
in (match (uu____8187) with
| true -> begin
(

let uu____8188 = (FStar_Syntax_Print.sigelt_to_string (

let uu___403_8191 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne1); FStar_Syntax_Syntax.sigrng = uu___403_8191.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___403_8191.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___403_8191.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___403_8191.FStar_Syntax_Syntax.sigattrs}))
in (FStar_Util.print1 "Effect decl after phase 1: %s\n" uu____8188))
end
| uu____8192 -> begin
()
end));
ne1;
))
end
| uu____8193 -> begin
ne
end))
in (

let ne2 = (tc_eff_decl env ne1)
in (

let se1 = (

let uu___404_8196 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne2); FStar_Syntax_Syntax.sigrng = uu___404_8196.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___404_8196.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___404_8196.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___404_8196.FStar_Syntax_Syntax.sigattrs})
in (((se1)::[]), ([]), (env0)))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub1) -> begin
(

let ed_src = (FStar_TypeChecker_Env.get_effect_decl env sub1.FStar_Syntax_Syntax.source)
in (

let ed_tgt = (FStar_TypeChecker_Env.get_effect_decl env sub1.FStar_Syntax_Syntax.target)
in (

let uu____8204 = (

let uu____8211 = (FStar_TypeChecker_Env.lookup_effect_lid env sub1.FStar_Syntax_Syntax.source)
in (monad_signature env sub1.FStar_Syntax_Syntax.source uu____8211))
in (match (uu____8204) with
| (a, wp_a_src) -> begin
(

let uu____8228 = (

let uu____8235 = (FStar_TypeChecker_Env.lookup_effect_lid env sub1.FStar_Syntax_Syntax.target)
in (monad_signature env sub1.FStar_Syntax_Syntax.target uu____8235))
in (match (uu____8228) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (

let uu____8253 = (

let uu____8256 = (

let uu____8257 = (

let uu____8264 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (uu____8264)))
in FStar_Syntax_Syntax.NT (uu____8257))
in (uu____8256)::[])
in (FStar_Syntax_Subst.subst uu____8253 wp_b_tgt))
in (

let expected_k = (

let uu____8272 = (

let uu____8281 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____8288 = (

let uu____8297 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (uu____8297)::[])
in (uu____8281)::uu____8288))
in (

let uu____8322 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow uu____8272 uu____8322)))
in (

let repr_type = (fun eff_name a1 wp -> ((

let uu____8344 = (

let uu____8345 = (FStar_TypeChecker_Env.is_reifiable_effect env eff_name)
in (not (uu____8345)))
in (match (uu____8344) with
| true -> begin
(

let uu____8346 = (

let uu____8351 = (FStar_Util.format1 "Effect %s cannot be reified" eff_name.FStar_Ident.str)
in ((FStar_Errors.Fatal_EffectCannotBeReified), (uu____8351)))
in (

let uu____8352 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Errors.raise_error uu____8346 uu____8352)))
end
| uu____8353 -> begin
()
end));
(

let uu____8354 = (FStar_TypeChecker_Env.effect_decl_opt env eff_name)
in (match (uu____8354) with
| FStar_Pervasives_Native.None -> begin
(failwith "internal error: reifiable effect has no decl?")
end
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((FStar_Syntax_Syntax.U_unknown)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let uu____8390 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____8391 = (

let uu____8398 = (

let uu____8399 = (

let uu____8416 = (

let uu____8427 = (FStar_Syntax_Syntax.as_arg a1)
in (

let uu____8436 = (

let uu____8447 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____8447)::[])
in (uu____8427)::uu____8436))
in ((repr), (uu____8416)))
in FStar_Syntax_Syntax.Tm_app (uu____8399))
in (FStar_Syntax_Syntax.mk uu____8398))
in (uu____8391 FStar_Pervasives_Native.None uu____8390))))
end));
))
in (

let uu____8495 = (match (((sub1.FStar_Syntax_Syntax.lift), (sub1.FStar_Syntax_Syntax.lift_wp))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(failwith "Impossible (parser)")
end
| (lift, FStar_Pervasives_Native.Some (uvs, lift_wp)) -> begin
(

let uu____8667 = (match (((FStar_List.length uvs) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____8676 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____8676) with
| (usubst, uvs1) -> begin
(

let uu____8699 = (FStar_TypeChecker_Env.push_univ_vars env uvs1)
in (

let uu____8700 = (FStar_Syntax_Subst.subst usubst lift_wp)
in ((uu____8699), (uu____8700))))
end))
end
| uu____8701 -> begin
((env), (lift_wp))
end)
in (match (uu____8667) with
| (env1, lift_wp1) -> begin
(

let lift_wp2 = (match ((Prims.op_Equality (FStar_List.length uvs) (Prims.parse_int "0"))) with
| true -> begin
(check_and_gen env1 lift_wp1 expected_k)
end
| uu____8743 -> begin
(

let lift_wp2 = (tc_check_trivial_guard env1 lift_wp1 expected_k)
in (

let uu____8745 = (FStar_Syntax_Subst.close_univ_vars uvs lift_wp2)
in ((uvs), (uu____8745))))
end)
in ((lift), (lift_wp2)))
end))
end
| (FStar_Pervasives_Native.Some (what, lift), FStar_Pervasives_Native.None) -> begin
(

let uu____8816 = (match (((FStar_List.length what) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____8829 = (FStar_Syntax_Subst.univ_var_opening what)
in (match (uu____8829) with
| (usubst, uvs) -> begin
(

let uu____8854 = (FStar_Syntax_Subst.subst usubst lift)
in ((uvs), (uu____8854)))
end))
end
| uu____8857 -> begin
(([]), (lift))
end)
in (match (uu____8816) with
| (uvs, lift1) -> begin
((

let uu____8889 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____8889) with
| true -> begin
(

let uu____8890 = (FStar_Syntax_Print.term_to_string lift1)
in (FStar_Util.print1 "Lift for free : %s\n" uu____8890))
end
| uu____8891 -> begin
()
end));
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env (FStar_TypeChecker_TcTerm.tc_constant env FStar_Range.dummyRange))
in (

let uu____8893 = (

let uu____8900 = (FStar_TypeChecker_Env.push_univ_vars env uvs)
in (FStar_TypeChecker_TcTerm.tc_term uu____8900 lift1))
in (match (uu____8893) with
| (lift2, comp, uu____8925) -> begin
(

let uu____8926 = (FStar_TypeChecker_DMFF.star_expr dmff_env lift2)
in (match (uu____8926) with
| (uu____8955, lift_wp, lift_elab) -> begin
(

let lift_wp1 = (recheck_debug "lift-wp" env lift_wp)
in (

let lift_elab1 = (recheck_debug "lift-elab" env lift_elab)
in (match ((Prims.op_Equality (FStar_List.length uvs) (Prims.parse_int "0"))) with
| true -> begin
(

let uu____8982 = (

let uu____8993 = (FStar_TypeChecker_Util.generalize_universes env lift_elab1)
in FStar_Pervasives_Native.Some (uu____8993))
in (

let uu____9010 = (FStar_TypeChecker_Util.generalize_universes env lift_wp1)
in ((uu____8982), (uu____9010))))
end
| uu____9037 -> begin
(

let uu____9038 = (

let uu____9049 = (

let uu____9058 = (FStar_Syntax_Subst.close_univ_vars uvs lift_elab1)
in ((uvs), (uu____9058)))
in FStar_Pervasives_Native.Some (uu____9049))
in (

let uu____9073 = (

let uu____9082 = (FStar_Syntax_Subst.close_univ_vars uvs lift_wp1)
in ((uvs), (uu____9082)))
in ((uu____9038), (uu____9073))))
end)))
end))
end)));
)
end))
end)
in (match (uu____8495) with
| (lift, lift_wp) -> begin
(

let env1 = (

let uu___405_9156 = env
in {FStar_TypeChecker_Env.solver = uu___405_9156.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___405_9156.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___405_9156.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___405_9156.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___405_9156.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___405_9156.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___405_9156.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___405_9156.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___405_9156.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___405_9156.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___405_9156.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___405_9156.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___405_9156.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___405_9156.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___405_9156.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___405_9156.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___405_9156.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___405_9156.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___405_9156.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___405_9156.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___405_9156.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___405_9156.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___405_9156.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___405_9156.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___405_9156.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___405_9156.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___405_9156.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___405_9156.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___405_9156.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___405_9156.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___405_9156.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___405_9156.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___405_9156.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___405_9156.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___405_9156.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___405_9156.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___405_9156.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___405_9156.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___405_9156.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___405_9156.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___405_9156.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___405_9156.FStar_TypeChecker_Env.nbe})
in (

let lift1 = (match (lift) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (uvs, lift1) -> begin
(

let uu____9188 = (

let uu____9193 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____9193) with
| (usubst, uvs1) -> begin
(

let uu____9216 = (FStar_TypeChecker_Env.push_univ_vars env1 uvs1)
in (

let uu____9217 = (FStar_Syntax_Subst.subst usubst lift1)
in ((uu____9216), (uu____9217))))
end))
in (match (uu____9188) with
| (env2, lift2) -> begin
(

let uu____9222 = (

let uu____9229 = (FStar_TypeChecker_Env.lookup_effect_lid env2 sub1.FStar_Syntax_Syntax.source)
in (monad_signature env2 sub1.FStar_Syntax_Syntax.source uu____9229))
in (match (uu____9222) with
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

let uu____9255 = (FStar_TypeChecker_Env.get_range env2)
in (

let uu____9256 = (

let uu____9263 = (

let uu____9264 = (

let uu____9281 = (

let uu____9292 = (FStar_Syntax_Syntax.as_arg a_typ)
in (

let uu____9301 = (

let uu____9312 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (uu____9312)::[])
in (uu____9292)::uu____9301))
in ((lift_wp1), (uu____9281)))
in FStar_Syntax_Syntax.Tm_app (uu____9264))
in (FStar_Syntax_Syntax.mk uu____9263))
in (uu____9256 FStar_Pervasives_Native.None uu____9255)))
in (repr_type sub1.FStar_Syntax_Syntax.target a_typ lift_wp_a)))
in (

let expected_k1 = (

let uu____9363 = (

let uu____9372 = (FStar_Syntax_Syntax.mk_binder a1)
in (

let uu____9379 = (

let uu____9388 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (

let uu____9395 = (

let uu____9404 = (FStar_Syntax_Syntax.null_binder repr_f)
in (uu____9404)::[])
in (uu____9388)::uu____9395))
in (uu____9372)::uu____9379))
in (

let uu____9435 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow uu____9363 uu____9435)))
in (

let uu____9438 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env2 expected_k1)
in (match (uu____9438) with
| (expected_k2, uu____9448, uu____9449) -> begin
(

let lift3 = (match ((Prims.op_Equality (FStar_List.length uvs) (Prims.parse_int "0"))) with
| true -> begin
(check_and_gen env2 lift2 expected_k2)
end
| uu____9451 -> begin
(

let lift3 = (tc_check_trivial_guard env2 lift2 expected_k2)
in (

let uu____9453 = (FStar_Syntax_Subst.close_univ_vars uvs lift3)
in ((uvs), (uu____9453))))
end)
in FStar_Pervasives_Native.Some (lift3))
end))))))))
end))
end))
end)
in ((

let uu____9461 = (

let uu____9462 = (

let uu____9463 = (FStar_All.pipe_right lift_wp FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____9463 FStar_List.length))
in (Prims.op_disEquality uu____9462 (Prims.parse_int "1")))
in (match (uu____9461) with
| true -> begin
(

let uu____9482 = (

let uu____9487 = (

let uu____9488 = (FStar_Syntax_Print.lid_to_string sub1.FStar_Syntax_Syntax.source)
in (

let uu____9489 = (FStar_Syntax_Print.lid_to_string sub1.FStar_Syntax_Syntax.target)
in (

let uu____9490 = (

let uu____9491 = (

let uu____9492 = (FStar_All.pipe_right lift_wp FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____9492 FStar_List.length))
in (FStar_All.pipe_right uu____9491 FStar_Util.string_of_int))
in (FStar_Util.format3 "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes" uu____9488 uu____9489 uu____9490))))
in ((FStar_Errors.Fatal_TooManyUniverse), (uu____9487)))
in (FStar_Errors.raise_error uu____9482 r))
end
| uu____9511 -> begin
()
end));
(

let uu____9513 = ((FStar_Util.is_some lift1) && (

let uu____9515 = (

let uu____9516 = (

let uu____9519 = (FStar_All.pipe_right lift1 FStar_Util.must)
in (FStar_All.pipe_right uu____9519 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____9516 FStar_List.length))
in (Prims.op_disEquality uu____9515 (Prims.parse_int "1"))))
in (match (uu____9513) with
| true -> begin
(

let uu____9554 = (

let uu____9559 = (

let uu____9560 = (FStar_Syntax_Print.lid_to_string sub1.FStar_Syntax_Syntax.source)
in (

let uu____9561 = (FStar_Syntax_Print.lid_to_string sub1.FStar_Syntax_Syntax.target)
in (

let uu____9562 = (

let uu____9563 = (

let uu____9564 = (

let uu____9567 = (FStar_All.pipe_right lift1 FStar_Util.must)
in (FStar_All.pipe_right uu____9567 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____9564 FStar_List.length))
in (FStar_All.pipe_right uu____9563 FStar_Util.string_of_int))
in (FStar_Util.format3 "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes" uu____9560 uu____9561 uu____9562))))
in ((FStar_Errors.Fatal_TooManyUniverse), (uu____9559)))
in (FStar_Errors.raise_error uu____9554 r))
end
| uu____9602 -> begin
()
end));
(

let sub2 = (

let uu___406_9604 = sub1
in {FStar_Syntax_Syntax.source = uu___406_9604.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = uu___406_9604.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = FStar_Pervasives_Native.Some (lift_wp); FStar_Syntax_Syntax.lift = lift1})
in (

let se1 = (

let uu___407_9606 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_sub_effect (sub2); FStar_Syntax_Syntax.sigrng = uu___407_9606.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___407_9606.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___407_9606.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___407_9606.FStar_Syntax_Syntax.sigattrs})
in (((se1)::[]), ([]), (env0))));
)))
end)))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, flags1) -> begin
(

let uu____9620 = (match ((Prims.op_Equality (FStar_List.length uvs) (Prims.parse_int "0"))) with
| true -> begin
((env), (uvs), (tps), (c))
end
| uu____9643 -> begin
(

let uu____9644 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____9644) with
| (usubst, uvs1) -> begin
(

let tps1 = (FStar_Syntax_Subst.subst_binders usubst tps)
in (

let c1 = (

let uu____9675 = (FStar_Syntax_Subst.shift_subst (FStar_List.length tps1) usubst)
in (FStar_Syntax_Subst.subst_comp uu____9675 c))
in (

let uu____9684 = (FStar_TypeChecker_Env.push_univ_vars env uvs1)
in ((uu____9684), (uvs1), (tps1), (c1)))))
end))
end)
in (match (uu____9620) with
| (env1, uvs1, tps1, c1) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_range env1 r)
in (

let uu____9706 = (FStar_Syntax_Subst.open_comp tps1 c1)
in (match (uu____9706) with
| (tps2, c2) -> begin
(

let uu____9723 = (FStar_TypeChecker_TcTerm.tc_tparams env2 tps2)
in (match (uu____9723) with
| (tps3, env3, us) -> begin
(

let uu____9743 = (FStar_TypeChecker_TcTerm.tc_comp env3 c2)
in (match (uu____9743) with
| (c3, u, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env3 g);
(

let expected_result_typ = (match (tps3) with
| ((x, uu____9771))::uu____9772 -> begin
(FStar_Syntax_Syntax.bv_to_name x)
end
| uu____9791 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_NotEnoughArgumentsForEffect), ("Effect abbreviations must bind at least the result type")) r)
end)
in (

let def_result_typ = (FStar_Syntax_Util.comp_result c3)
in (

let uu____9797 = (

let uu____9798 = (FStar_TypeChecker_Rel.teq_nosmt_force env3 expected_result_typ def_result_typ)
in (not (uu____9798)))
in (match (uu____9797) with
| true -> begin
(

let uu____9799 = (

let uu____9804 = (

let uu____9805 = (FStar_Syntax_Print.term_to_string expected_result_typ)
in (

let uu____9806 = (FStar_Syntax_Print.term_to_string def_result_typ)
in (FStar_Util.format2 "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`" uu____9805 uu____9806)))
in ((FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch), (uu____9804)))
in (FStar_Errors.raise_error uu____9799 r))
end
| uu____9807 -> begin
()
end))));
(

let tps4 = (FStar_Syntax_Subst.close_binders tps3)
in (

let c4 = (FStar_Syntax_Subst.close_comp tps4 c3)
in (

let uu____9810 = (

let uu____9811 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps4), (c4)))) FStar_Pervasives_Native.None r)
in (FStar_TypeChecker_Util.generalize_universes env0 uu____9811))
in (match (uu____9810) with
| (uvs2, t) -> begin
(

let uu____9842 = (

let uu____9847 = (

let uu____9860 = (

let uu____9861 = (FStar_Syntax_Subst.compress t)
in uu____9861.FStar_Syntax_Syntax.n)
in ((tps4), (uu____9860)))
in (match (uu____9847) with
| ([], FStar_Syntax_Syntax.Tm_arrow (uu____9876, c5)) -> begin
(([]), (c5))
end
| (uu____9918, FStar_Syntax_Syntax.Tm_arrow (tps5, c5)) -> begin
((tps5), (c5))
end
| uu____9957 -> begin
(failwith "Impossible (t is an arrow)")
end))
in (match (uu____9842) with
| (tps5, c5) -> begin
((match ((Prims.op_disEquality (FStar_List.length uvs2) (Prims.parse_int "1"))) with
| true -> begin
(

let uu____9987 = (FStar_Syntax_Subst.open_univ_vars uvs2 t)
in (match (uu____9987) with
| (uu____9992, t1) -> begin
(

let uu____9994 = (

let uu____9999 = (

let uu____10000 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____10001 = (FStar_All.pipe_right (FStar_List.length uvs2) FStar_Util.string_of_int)
in (

let uu____10002 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)" uu____10000 uu____10001 uu____10002))))
in ((FStar_Errors.Fatal_TooManyUniverse), (uu____9999)))
in (FStar_Errors.raise_error uu____9994 r))
end))
end
| uu____10003 -> begin
()
end);
(

let se1 = (

let uu___408_10005 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (((lid), (uvs2), (tps5), (c5), (flags1))); FStar_Syntax_Syntax.sigrng = uu___408_10005.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___408_10005.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___408_10005.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___408_10005.FStar_Syntax_Syntax.sigattrs})
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
| FStar_Syntax_Syntax.Sig_declare_typ (uu____10012, uu____10013, uu____10014) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___374_10018 -> (match (uu___374_10018) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____10019 -> begin
false
end)))) -> begin
(([]), ([]), (env0))
end
| FStar_Syntax_Syntax.Sig_let (uu____10024, uu____10025) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___374_10033 -> (match (uu___374_10033) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____10034 -> begin
false
end)))) -> begin
(([]), ([]), (env0))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) -> begin
(

let env1 = (FStar_TypeChecker_Env.set_range env r)
in ((

let uu____10044 = (FStar_TypeChecker_Env.lid_exists env1 lid)
in (match (uu____10044) with
| true -> begin
(

let uu____10045 = (

let uu____10050 = (

let uu____10051 = (FStar_Ident.text_of_lid lid)
in (FStar_Util.format1 "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module" uu____10051))
in ((FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration), (uu____10050)))
in (FStar_Errors.raise_error uu____10045 r))
end
| uu____10052 -> begin
()
end));
(

let uu____10053 = (

let uu____10062 = ((FStar_Options.use_two_phase_tc ()) && (FStar_TypeChecker_Env.should_verify env1))
in (match (uu____10062) with
| true -> begin
(

let uu____10071 = (tc_declare_typ (

let uu___409_10074 = env1
in {FStar_TypeChecker_Env.solver = uu___409_10074.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___409_10074.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___409_10074.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___409_10074.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___409_10074.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___409_10074.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___409_10074.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___409_10074.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___409_10074.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___409_10074.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___409_10074.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___409_10074.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___409_10074.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___409_10074.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___409_10074.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___409_10074.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___409_10074.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___409_10074.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___409_10074.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___409_10074.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___409_10074.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___409_10074.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___409_10074.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___409_10074.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___409_10074.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___409_10074.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___409_10074.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___409_10074.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___409_10074.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___409_10074.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___409_10074.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___409_10074.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___409_10074.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___409_10074.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___409_10074.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___409_10074.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___409_10074.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___409_10074.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___409_10074.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___409_10074.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___409_10074.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___409_10074.FStar_TypeChecker_Env.nbe}) ((uvs), (t)) se.FStar_Syntax_Syntax.sigrng)
in (match (uu____10071) with
| (uvs1, t1) -> begin
((

let uu____10098 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("TwoPhases")))
in (match (uu____10098) with
| true -> begin
(

let uu____10099 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____10100 = (FStar_Syntax_Print.univ_names_to_string uvs1)
in (FStar_Util.print2 "Val declaration after phase 1: %s and uvs: %s\n" uu____10099 uu____10100)))
end
| uu____10101 -> begin
()
end));
((uvs1), (t1));
)
end))
end
| uu____10106 -> begin
((uvs), (t))
end))
in (match (uu____10053) with
| (uvs1, t1) -> begin
(

let uu____10131 = (tc_declare_typ env1 ((uvs1), (t1)) se.FStar_Syntax_Syntax.sigrng)
in (match (uu____10131) with
| (uvs2, t2) -> begin
((((

let uu___410_10161 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (uvs2), (t2))); FStar_Syntax_Syntax.sigrng = uu___410_10161.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___410_10161.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___410_10161.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___410_10161.FStar_Syntax_Syntax.sigattrs}))::[]), ([]), (env0))
end))
end));
))
end
| FStar_Syntax_Syntax.Sig_assume (lid, uvs, t) -> begin
(

let env1 = (FStar_TypeChecker_Env.set_range env r)
in (

let uu____10166 = (

let uu____10175 = ((FStar_Options.use_two_phase_tc ()) && (FStar_TypeChecker_Env.should_verify env1))
in (match (uu____10175) with
| true -> begin
(

let uu____10184 = (tc_assume (

let uu___411_10187 = env1
in {FStar_TypeChecker_Env.solver = uu___411_10187.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___411_10187.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___411_10187.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___411_10187.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___411_10187.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___411_10187.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___411_10187.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___411_10187.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___411_10187.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___411_10187.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___411_10187.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___411_10187.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___411_10187.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___411_10187.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___411_10187.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___411_10187.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___411_10187.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___411_10187.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___411_10187.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___411_10187.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___411_10187.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = true; FStar_TypeChecker_Env.failhard = uu___411_10187.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___411_10187.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___411_10187.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___411_10187.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___411_10187.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___411_10187.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___411_10187.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___411_10187.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___411_10187.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___411_10187.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___411_10187.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___411_10187.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___411_10187.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___411_10187.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___411_10187.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___411_10187.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___411_10187.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___411_10187.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___411_10187.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___411_10187.FStar_TypeChecker_Env.nbe}) ((uvs), (t)) se.FStar_Syntax_Syntax.sigrng)
in (match (uu____10184) with
| (uvs1, t1) -> begin
((

let uu____10211 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("TwoPhases")))
in (match (uu____10211) with
| true -> begin
(

let uu____10212 = (FStar_Syntax_Print.term_to_string t1)
in (

let uu____10213 = (FStar_Syntax_Print.univ_names_to_string uvs1)
in (FStar_Util.print2 "Assume after phase 1: %s and uvs: %s\n" uu____10212 uu____10213)))
end
| uu____10214 -> begin
()
end));
((uvs1), (t1));
)
end))
end
| uu____10219 -> begin
((uvs), (t))
end))
in (match (uu____10166) with
| (uvs1, t1) -> begin
(

let uu____10244 = (tc_assume env1 ((uvs1), (t1)) se.FStar_Syntax_Syntax.sigrng)
in (match (uu____10244) with
| (uvs2, t2) -> begin
((((

let uu___412_10274 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_assume (((lid), (uvs2), (t2))); FStar_Syntax_Syntax.sigrng = uu___412_10274.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___412_10274.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___412_10274.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___412_10274.FStar_Syntax_Syntax.sigattrs}))::[]), ([]), (env0))
end))
end)))
end
| FStar_Syntax_Syntax.Sig_main (e) -> begin
(

let env1 = (FStar_TypeChecker_Env.set_range env r)
in (

let env2 = (FStar_TypeChecker_Env.set_expected_typ env1 FStar_Syntax_Syntax.t_unit)
in (

let uu____10278 = (FStar_TypeChecker_TcTerm.tc_term env2 e)
in (match (uu____10278) with
| (e1, c, g1) -> begin
(

let uu____10298 = (

let uu____10305 = (

let uu____10308 = (FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r)
in FStar_Pervasives_Native.Some (uu____10308))
in (

let uu____10309 = (

let uu____10314 = (FStar_Syntax_Syntax.lcomp_comp c)
in ((e1), (uu____10314)))
in (FStar_TypeChecker_TcTerm.check_expected_effect env2 uu____10305 uu____10309)))
in (match (uu____10298) with
| (e2, uu____10326, g) -> begin
((

let uu____10329 = (FStar_TypeChecker_Env.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env2 uu____10329));
(

let se1 = (

let uu___413_10331 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_main (e2); FStar_Syntax_Syntax.sigrng = uu___413_10331.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___413_10331.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___413_10331.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___413_10331.FStar_Syntax_Syntax.sigattrs})
in (((se1)::[]), ([]), (env0)));
)
end))
end))))
end
| FStar_Syntax_Syntax.Sig_splice (lids, t) -> begin
((

let uu____10343 = (FStar_Options.debug_any ())
in (match (uu____10343) with
| true -> begin
(

let uu____10344 = (FStar_Ident.string_of_lid env.FStar_TypeChecker_Env.curmodule)
in (

let uu____10345 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "%s: Found splice of (%s)\n" uu____10344 uu____10345)))
end
| uu____10346 -> begin
()
end));
(

let uu____10347 = (FStar_TypeChecker_TcTerm.tc_tactic env t)
in (match (uu____10347) with
| (t1, uu____10365, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
(

let ses = (env.FStar_TypeChecker_Env.splice env t1)
in (

let lids' = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt ses)
in ((FStar_List.iter (fun lid -> (

let uu____10379 = (FStar_List.tryFind (FStar_Ident.lid_equals lid) lids')
in (match (uu____10379) with
| FStar_Pervasives_Native.None when (not (env.FStar_TypeChecker_Env.nosynth)) -> begin
(

let uu____10382 = (

let uu____10387 = (

let uu____10388 = (FStar_Ident.string_of_lid lid)
in (

let uu____10389 = (

let uu____10390 = (FStar_List.map FStar_Ident.string_of_lid lids')
in (FStar_All.pipe_left (FStar_String.concat ", ") uu____10390))
in (FStar_Util.format2 "Splice declared the name %s but it was not defined.\nThose defined were: %s" uu____10388 uu____10389)))
in ((FStar_Errors.Fatal_SplicedUndef), (uu____10387)))
in (FStar_Errors.raise_error uu____10382 r))
end
| uu____10395 -> begin
()
end))) lids);
(

let dsenv1 = (FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt_force env.FStar_TypeChecker_Env.dsenv ses)
in (

let env1 = (

let uu___414_10400 = env
in {FStar_TypeChecker_Env.solver = uu___414_10400.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___414_10400.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___414_10400.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___414_10400.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___414_10400.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___414_10400.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___414_10400.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___414_10400.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___414_10400.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___414_10400.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___414_10400.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___414_10400.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___414_10400.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___414_10400.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___414_10400.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___414_10400.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___414_10400.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___414_10400.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___414_10400.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___414_10400.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___414_10400.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___414_10400.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___414_10400.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___414_10400.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___414_10400.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___414_10400.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___414_10400.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___414_10400.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___414_10400.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___414_10400.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___414_10400.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___414_10400.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___414_10400.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___414_10400.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___414_10400.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___414_10400.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___414_10400.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___414_10400.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___414_10400.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___414_10400.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___414_10400.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = dsenv1; FStar_TypeChecker_Env.nbe = uu___414_10400.FStar_TypeChecker_Env.nbe})
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

let check_quals_eq = (fun l qopt q -> (match (qopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (q)
end
| FStar_Pervasives_Native.Some (q') -> begin
(

let drop_logic = (FStar_List.filter (fun x -> (not ((Prims.op_Equality x FStar_Syntax_Syntax.Logic)))))
in (

let uu____10468 = (

let uu____10477 = (drop_logic q)
in (

let uu____10480 = (drop_logic q')
in ((uu____10477), (uu____10480))))
in (match (uu____10468) with
| (q1, q'1) -> begin
(

let uu____10501 = ((Prims.op_Equality (FStar_List.length q1) (FStar_List.length q'1)) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q1 q'1))
in (match (uu____10501) with
| true -> begin
FStar_Pervasives_Native.Some (q1)
end
| uu____10508 -> begin
(

let uu____10509 = (

let uu____10514 = (

let uu____10515 = (FStar_Syntax_Print.lid_to_string l)
in (

let uu____10516 = (FStar_Syntax_Print.quals_to_string q1)
in (

let uu____10517 = (FStar_Syntax_Print.quals_to_string q'1)
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" uu____10515 uu____10516 uu____10517))))
in ((FStar_Errors.Fatal_InconsistentQualifierAnnotation), (uu____10514)))
in (FStar_Errors.raise_error uu____10509 r))
end))
end)))
end))
in (

let rename_parameters = (fun lb -> (

let rename_in_typ = (fun def typ -> (

let typ1 = (FStar_Syntax_Subst.compress typ)
in (

let def_bs = (

let uu____10551 = (

let uu____10552 = (FStar_Syntax_Subst.compress def)
in uu____10552.FStar_Syntax_Syntax.n)
in (match (uu____10551) with
| FStar_Syntax_Syntax.Tm_abs (binders, uu____10564, uu____10565) -> begin
binders
end
| uu____10590 -> begin
[]
end))
in (match (typ1) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow (val_bs, c); FStar_Syntax_Syntax.pos = r1; FStar_Syntax_Syntax.vars = uu____10602} -> begin
(

let has_auto_name = (fun bv -> (FStar_Util.starts_with bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Ident.reserved_prefix))
in (

let rec rename_binders1 = (fun def_bs1 val_bs1 -> (match (((def_bs1), (val_bs1))) with
| ([], uu____10706) -> begin
val_bs1
end
| (uu____10737, []) -> begin
val_bs1
end
| (((body_bv, uu____10769))::bt, ((val_bv, aqual))::vt) -> begin
(

let uu____10826 = (rename_binders1 bt vt)
in ((match ((((has_auto_name body_bv)), ((has_auto_name val_bv)))) with
| (true, uu____10848) -> begin
((val_bv), (aqual))
end
| (false, true) -> begin
(((

let uu___415_10854 = val_bv
in {FStar_Syntax_Syntax.ppname = (

let uu___416_10857 = val_bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = body_bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText; FStar_Ident.idRange = uu___416_10857.FStar_Ident.idRange}); FStar_Syntax_Syntax.index = uu___415_10854.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___415_10854.FStar_Syntax_Syntax.sort})), (aqual))
end
| (false, false) -> begin
((val_bv), (aqual))
end))::uu____10826)
end))
in (

let uu____10860 = (

let uu____10867 = (

let uu____10868 = (

let uu____10883 = (rename_binders1 def_bs val_bs)
in ((uu____10883), (c)))
in FStar_Syntax_Syntax.Tm_arrow (uu____10868))
in (FStar_Syntax_Syntax.mk uu____10867))
in (uu____10860 FStar_Pervasives_Native.None r1))))
end
| uu____10905 -> begin
typ1
end))))
in (

let uu___417_10906 = lb
in (

let uu____10907 = (rename_in_typ lb.FStar_Syntax_Syntax.lbdef lb.FStar_Syntax_Syntax.lbtyp)
in {FStar_Syntax_Syntax.lbname = uu___417_10906.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___417_10906.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____10907; FStar_Syntax_Syntax.lbeff = uu___417_10906.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___417_10906.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___417_10906.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___417_10906.FStar_Syntax_Syntax.lbpos}))))
in (

let uu____10910 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.fold_left (fun uu____10961 lb -> (match (uu____10961) with
| (gen1, lbs1, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____11003 = (

let uu____11014 = (FStar_TypeChecker_Env.try_lookup_val_decl env1 lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____11014) with
| FStar_Pervasives_Native.None -> begin
(match ((Prims.op_disEquality lb.FStar_Syntax_Syntax.lbunivs [])) with
| true -> begin
((false), (lb), (quals_opt))
end
| uu____11055 -> begin
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
| uu____11087 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((lb.FStar_Syntax_Syntax.lbdef), (((FStar_Util.Inl (lb.FStar_Syntax_Syntax.lbtyp)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.pos)
end)
in ((match (((Prims.op_disEquality lb.FStar_Syntax_Syntax.lbunivs []) && (Prims.op_disEquality (FStar_List.length lb.FStar_Syntax_Syntax.lbunivs) (FStar_List.length uvs)))) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_IncoherentInlineUniverse), ("Inline universes are incoherent with annotation from val declaration")) r)
end
| uu____11129 -> begin
()
end);
(

let uu____11130 = (FStar_Syntax_Syntax.mk_lb ((FStar_Util.Inr (lbname)), (uvs), (FStar_Parser_Const.effect_ALL_lid), (tval), (def), (lb.FStar_Syntax_Syntax.lbpos)))
in ((false), (uu____11130), (quals_opt1)));
)))
end))
in (match (uu____11003) with
| (gen2, lb1, quals_opt1) -> begin
((gen2), ((lb1)::lbs1), (quals_opt1))
end)))
end)) ((true), ([]), ((match ((Prims.op_Equality se.FStar_Syntax_Syntax.sigquals [])) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____11180 -> begin
FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
end)))))
in (match (uu____10910) with
| (should_generalize, lbs', quals_opt) -> begin
(

let quals = (match (quals_opt) with
| FStar_Pervasives_Native.None -> begin
(FStar_Syntax_Syntax.Visible_default)::[]
end
| FStar_Pervasives_Native.Some (q) -> begin
(

let uu____11220 = (FStar_All.pipe_right q (FStar_Util.for_some (fun uu___375_11224 -> (match (uu___375_11224) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| FStar_Syntax_Syntax.Visible_default -> begin
true
end
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____11225 -> begin
false
end))))
in (match (uu____11220) with
| true -> begin
q
end
| uu____11228 -> begin
(FStar_Syntax_Syntax.Visible_default)::q
end))
end)
in (

let lbs'1 = (FStar_List.rev lbs')
in (

let e = (

let uu____11235 = (

let uu____11242 = (

let uu____11243 = (

let uu____11256 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) FStar_Pervasives_Native.None r)
in (((((FStar_Pervasives_Native.fst lbs)), (lbs'1))), (uu____11256)))
in FStar_Syntax_Syntax.Tm_let (uu____11243))
in (FStar_Syntax_Syntax.mk uu____11242))
in (uu____11235 FStar_Pervasives_Native.None r))
in (

let env' = (

let uu___418_11275 = env1
in {FStar_TypeChecker_Env.solver = uu___418_11275.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___418_11275.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___418_11275.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___418_11275.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___418_11275.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___418_11275.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___418_11275.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___418_11275.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___418_11275.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___418_11275.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___418_11275.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___418_11275.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___418_11275.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = uu___418_11275.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = uu___418_11275.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___418_11275.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___418_11275.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___418_11275.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___418_11275.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___418_11275.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___418_11275.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___418_11275.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___418_11275.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___418_11275.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___418_11275.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___418_11275.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___418_11275.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___418_11275.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___418_11275.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___418_11275.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___418_11275.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___418_11275.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___418_11275.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___418_11275.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___418_11275.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___418_11275.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___418_11275.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___418_11275.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___418_11275.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___418_11275.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___418_11275.FStar_TypeChecker_Env.nbe})
in (

let e1 = (

let uu____11277 = ((FStar_Options.use_two_phase_tc ()) && (FStar_TypeChecker_Env.should_verify env'))
in (match (uu____11277) with
| true -> begin
(

let drop_lbtyp = (fun e_lax -> (

let uu____11284 = (

let uu____11285 = (FStar_Syntax_Subst.compress e_lax)
in uu____11285.FStar_Syntax_Syntax.n)
in (match (uu____11284) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let lb_unannotated = (

let uu____11303 = (

let uu____11304 = (FStar_Syntax_Subst.compress e)
in uu____11304.FStar_Syntax_Syntax.n)
in (match (uu____11303) with
| FStar_Syntax_Syntax.Tm_let ((uu____11307, (lb1)::[]), uu____11309) -> begin
(

let uu____11322 = (

let uu____11323 = (FStar_Syntax_Subst.compress lb1.FStar_Syntax_Syntax.lbtyp)
in uu____11323.FStar_Syntax_Syntax.n)
in (match (uu____11322) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| uu____11326 -> begin
false
end))
end
| uu____11327 -> begin
(failwith "Impossible: first phase lb and second phase lb differ in structure!")
end))
in (match (lb_unannotated) with
| true -> begin
(

let uu___419_11328 = e_lax
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (((((false), (((

let uu___420_11340 = lb
in {FStar_Syntax_Syntax.lbname = uu___420_11340.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___420_11340.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = uu___420_11340.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___420_11340.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___420_11340.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___420_11340.FStar_Syntax_Syntax.lbpos}))::[]))), (e2))); FStar_Syntax_Syntax.pos = uu___419_11328.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___419_11328.FStar_Syntax_Syntax.vars})
end
| uu____11341 -> begin
e_lax
end))
end
| uu____11342 -> begin
e_lax
end)))
in (

let e1 = (

let uu____11344 = (

let uu____11345 = (

let uu____11346 = (FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term (

let uu___421_11355 = env'
in {FStar_TypeChecker_Env.solver = uu___421_11355.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___421_11355.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___421_11355.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___421_11355.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___421_11355.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___421_11355.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___421_11355.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___421_11355.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___421_11355.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___421_11355.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___421_11355.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___421_11355.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___421_11355.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___421_11355.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___421_11355.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___421_11355.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___421_11355.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___421_11355.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___421_11355.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___421_11355.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___421_11355.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = true; FStar_TypeChecker_Env.failhard = uu___421_11355.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___421_11355.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___421_11355.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___421_11355.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___421_11355.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___421_11355.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___421_11355.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___421_11355.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___421_11355.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___421_11355.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___421_11355.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___421_11355.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___421_11355.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___421_11355.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___421_11355.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___421_11355.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___421_11355.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___421_11355.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___421_11355.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___421_11355.FStar_TypeChecker_Env.nbe}) e)
in (FStar_All.pipe_right uu____11346 (fun uu____11366 -> (match (uu____11366) with
| (e1, uu____11374, uu____11375) -> begin
e1
end))))
in (FStar_All.pipe_right uu____11345 (FStar_TypeChecker_Normalize.remove_uvar_solutions env')))
in (FStar_All.pipe_right uu____11344 drop_lbtyp))
in ((

let uu____11377 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("TwoPhases")))
in (match (uu____11377) with
| true -> begin
(

let uu____11378 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.print1 "Let binding after phase 1: %s\n" uu____11378))
end
| uu____11379 -> begin
()
end));
e1;
)))
end
| uu____11380 -> begin
e
end))
in (

let uu____11381 = (

let uu____11390 = (FStar_Syntax_Util.extract_attr' FStar_Parser_Const.postprocess_with se.FStar_Syntax_Syntax.sigattrs)
in (match (uu____11390) with
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
in (match (uu____11381) with
| (attrs, post_tau) -> begin
(

let se1 = (

let uu___422_11493 = se
in {FStar_Syntax_Syntax.sigel = uu___422_11493.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___422_11493.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___422_11493.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___422_11493.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = attrs})
in (

let postprocess_lb = (fun tau lb -> (

let lbdef = (env1.FStar_TypeChecker_Env.postprocess env1 tau lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (

let uu___423_11506 = lb
in {FStar_Syntax_Syntax.lbname = uu___423_11506.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___423_11506.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___423_11506.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___423_11506.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef; FStar_Syntax_Syntax.lbattrs = uu___423_11506.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___423_11506.FStar_Syntax_Syntax.lbpos})))
in (

let uu____11507 = (

let uu____11518 = (FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term env' e1)
in (match (uu____11518) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs1, e2); FStar_Syntax_Syntax.pos = uu____11537; FStar_Syntax_Syntax.vars = uu____11538}, uu____11539, g) when (FStar_TypeChecker_Env.is_trivial g) -> begin
(

let lbs2 = (

let uu____11566 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1) (FStar_List.map rename_parameters))
in (((FStar_Pervasives_Native.fst lbs1)), (uu____11566)))
in (

let lbs3 = (

let uu____11586 = (match (post_tau) with
| FStar_Pervasives_Native.Some (tau) -> begin
(FStar_List.map (postprocess_lb tau) (FStar_Pervasives_Native.snd lbs2))
end
| FStar_Pervasives_Native.None -> begin
(FStar_Pervasives_Native.snd lbs2)
end)
in (((FStar_Pervasives_Native.fst lbs2)), (uu____11586)))
in (

let quals1 = (match (e2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (uu____11605, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| uu____11610 -> begin
quals
end)
in (((

let uu___424_11618 = se1
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((lbs3), (lids))); FStar_Syntax_Syntax.sigrng = uu___424_11618.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = uu___424_11618.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___424_11618.FStar_Syntax_Syntax.sigattrs})), (lbs3)))))
end
| uu____11621 -> begin
(failwith "impossible (typechecking should preserve Tm_let)")
end))
in (match (uu____11507) with
| (se2, lbs1) -> begin
((FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1) (FStar_List.iter (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (FStar_TypeChecker_Env.insert_fv_info env1 fv lb.FStar_Syntax_Syntax.lbtyp)))));
(

let uu____11672 = (log env1)
in (match (uu____11672) with
| true -> begin
(

let uu____11673 = (

let uu____11674 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1) (FStar_List.map (fun lb -> (

let should_log = (

let uu____11689 = (

let uu____11698 = (

let uu____11699 = (

let uu____11702 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____11702.FStar_Syntax_Syntax.fv_name)
in uu____11699.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env1 uu____11698))
in (match (uu____11689) with
| FStar_Pervasives_Native.None -> begin
true
end
| uu____11709 -> begin
false
end))
in (match (should_log) with
| true -> begin
(

let uu____11718 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____11719 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" uu____11718 uu____11719)))
end
| uu____11720 -> begin
""
end)))))
in (FStar_All.pipe_right uu____11674 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" uu____11673))
end
| uu____11723 -> begin
()
end));
(((se2)::[]), ([]), (env0));
)
end))))
end)))))))
end)))))
end));
)))


let tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env se -> (

let env1 = (set_hint_correlator env se)
in ((

let uu____11760 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____11760) with
| true -> begin
(

let uu____11761 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____11761))
end
| uu____11762 -> begin
()
end));
(

let uu____11763 = (get_fail_se se)
in (match (uu____11763) with
| FStar_Pervasives_Native.Some (uu____11782, false) when (

let uu____11793 = (FStar_TypeChecker_Env.should_verify env1)
in (not (uu____11793))) -> begin
(([]), ([]), (env1))
end
| FStar_Pervasives_Native.Some (errnos, lax1) -> begin
(

let env' = (match (lax1) with
| true -> begin
(

let uu___425_11811 = env1
in {FStar_TypeChecker_Env.solver = uu___425_11811.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___425_11811.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___425_11811.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___425_11811.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___425_11811.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___425_11811.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___425_11811.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___425_11811.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___425_11811.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___425_11811.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___425_11811.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___425_11811.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___425_11811.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___425_11811.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___425_11811.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___425_11811.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___425_11811.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___425_11811.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___425_11811.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___425_11811.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___425_11811.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___425_11811.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___425_11811.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___425_11811.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___425_11811.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___425_11811.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___425_11811.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___425_11811.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___425_11811.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___425_11811.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___425_11811.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___425_11811.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___425_11811.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___425_11811.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___425_11811.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___425_11811.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___425_11811.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___425_11811.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___425_11811.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___425_11811.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___425_11811.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___425_11811.FStar_TypeChecker_Env.nbe})
end
| uu____11812 -> begin
env1
end)
in ((

let uu____11814 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____11814) with
| true -> begin
(

let uu____11815 = (

let uu____11816 = (FStar_List.map FStar_Util.string_of_int errnos)
in (FStar_All.pipe_left (FStar_String.concat "; ") uu____11816))
in (FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____11815))
end
| uu____11821 -> begin
()
end));
(

let uu____11822 = (FStar_Errors.catch_errors (fun uu____11852 -> (FStar_Options.with_saved_options (fun uu____11864 -> (tc_decl' env' se)))))
in (match (uu____11822) with
| (errs, uu____11876) -> begin
((

let uu____11906 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____11906) with
| true -> begin
((FStar_Util.print_string ">> Got issues: [\n");
(FStar_List.iter FStar_Errors.print_issue errs);
(FStar_Util.print_string ">>]\n");
)
end
| uu____11909 -> begin
()
end));
(

let sort = (FStar_List.sortWith (fun x y -> (x - y)))
in (

let errnos1 = (sort errnos)
in (

let actual = (

let uu____11929 = (FStar_List.concatMap (fun i -> (list_of_option i.FStar_Errors.issue_number)) errs)
in (sort uu____11929))
in ((match (errs) with
| [] -> begin
((FStar_List.iter FStar_Errors.print_issue errs);
(FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng ((FStar_Errors.Error_DidNotFail), ("This top-level definition was expected to fail, but it succeeded")));
)
end
| uu____11936 -> begin
(match (((Prims.op_disEquality errnos1 []) && (Prims.op_disEquality errnos1 actual))) with
| true -> begin
(

let uu____11943 = (

let uu____11950 = (check_multi_contained errnos1 actual)
in (match (uu____11950) with
| FStar_Pervasives_Native.Some (r) -> begin
r
end
| FStar_Pervasives_Native.None -> begin
(((~- ((Prims.parse_int "1")))), ((~- ((Prims.parse_int "1")))), ((~- ((Prims.parse_int "1")))))
end))
in (match (uu____11943) with
| (e, n1, n2) -> begin
((FStar_List.iter FStar_Errors.print_issue errs);
(

let uu____11988 = (

let uu____11993 = (

let uu____11994 = (FStar_Common.string_of_list FStar_Util.string_of_int errnos1)
in (

let uu____11995 = (FStar_Common.string_of_list FStar_Util.string_of_int actual)
in (

let uu____11996 = (FStar_Util.string_of_int e)
in (

let uu____11997 = (FStar_Util.string_of_int n2)
in (

let uu____11998 = (FStar_Util.string_of_int n1)
in (FStar_Util.format5 "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s." uu____11994 uu____11995 uu____11996 uu____11997 uu____11998))))))
in ((FStar_Errors.Error_DidNotFail), (uu____11993)))
in (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng uu____11988));
)
end))
end
| uu____11999 -> begin
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


let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___376_12053 -> (match (uu___376_12053) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| uu____12054 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| FStar_Syntax_Syntax.Projector (l, uu____12062) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| FStar_Syntax_Syntax.Discriminator (l) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| uu____12068 -> begin
false
end))
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_pragma (uu____12077) -> begin
(([]), (hidden))
end
| FStar_Syntax_Syntax.Sig_splice (uu____12082) -> begin
(failwith "Impossible (Already handled)")
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____12097) -> begin
(failwith "Impossible (Already handled)")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____12122) -> begin
(failwith "Impossible (Already handled)")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____12146) -> begin
(

let uu____12155 = (is_abstract se.FStar_Syntax_Syntax.sigquals)
in (match (uu____12155) with
| true -> begin
(

let for_export_bundle = (fun se1 uu____12190 -> (match (uu____12190) with
| (out, hidden1) -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, uu____12229, uu____12230) -> begin
(

let dec = (

let uu___426_12240 = se1
in (

let uu____12241 = (

let uu____12242 = (

let uu____12249 = (

let uu____12250 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow bs uu____12250))
in ((l), (us), (uu____12249)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____12242))
in {FStar_Syntax_Syntax.sigel = uu____12241; FStar_Syntax_Syntax.sigrng = uu___426_12240.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::se1.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___426_12240.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___426_12240.FStar_Syntax_Syntax.sigattrs}))
in (((dec)::out), (hidden1)))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, uu____12260, uu____12261, uu____12262) -> begin
(

let dec = (

let uu___427_12268 = se1
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t))); FStar_Syntax_Syntax.sigrng = uu___427_12268.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::[]; FStar_Syntax_Syntax.sigmeta = uu___427_12268.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___427_12268.FStar_Syntax_Syntax.sigattrs})
in (((dec)::out), ((l)::hidden1)))
end
| uu____12273 -> begin
((out), (hidden1))
end)
end))
in (FStar_List.fold_right for_export_bundle ses (([]), (hidden))))
end
| uu____12290 -> begin
(((se)::[]), (hidden))
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____12295, uu____12296, uu____12297) -> begin
(

let uu____12298 = (is_abstract se.FStar_Syntax_Syntax.sigquals)
in (match (uu____12298) with
| true -> begin
(([]), (hidden))
end
| uu____12311 -> begin
(((se)::[]), (hidden))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, us, t) -> begin
(

let uu____12319 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some is_hidden_proj_or_disc))
in (match (uu____12319) with
| true -> begin
((((

let uu___428_12335 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t))); FStar_Syntax_Syntax.sigrng = uu___428_12335.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::[]; FStar_Syntax_Syntax.sigmeta = uu___428_12335.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___428_12335.FStar_Syntax_Syntax.sigattrs}))::[]), ((l)::hidden))
end
| uu____12336 -> begin
(

let uu____12337 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___377_12341 -> (match (uu___377_12341) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____12342) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____12347) -> begin
true
end
| uu____12348 -> begin
false
end))))
in (match (uu____12337) with
| true -> begin
(((se)::[]), (hidden))
end
| uu____12361 -> begin
(([]), (hidden))
end))
end))
end
| FStar_Syntax_Syntax.Sig_main (uu____12366) -> begin
(([]), (hidden))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____12371) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____12376) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____12381) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____12386) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____12404) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____12415 = (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
in (match (uu____12415) with
| true -> begin
(([]), (hidden))
end
| uu____12430 -> begin
(

let dec = (

let uu____12432 = (FStar_Ident.range_of_lid lid)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu____12432; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::[]; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (((dec)::[]), ((lid)::hidden)))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, l) -> begin
(

let uu____12443 = (is_abstract se.FStar_Syntax_Syntax.sigquals)
in (match (uu____12443) with
| true -> begin
(

let uu____12452 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let uu___429_12465 = se
in (

let uu____12466 = (

let uu____12467 = (

let uu____12474 = (

let uu____12475 = (

let uu____12478 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____12478.FStar_Syntax_Syntax.fv_name)
in uu____12475.FStar_Syntax_Syntax.v)
in ((uu____12474), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____12467))
in {FStar_Syntax_Syntax.sigel = uu____12466; FStar_Syntax_Syntax.sigrng = uu___429_12465.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___429_12465.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___429_12465.FStar_Syntax_Syntax.sigattrs})))))
in ((uu____12452), (hidden)))
end
| uu____12483 -> begin
(((se)::[]), (hidden))
end))
end))))


let add_sigelt_to_env : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env = (fun env se -> ((

let uu____12499 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____12499) with
| true -> begin
(

let uu____12500 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Adding top-level decl to environment: %s\n" uu____12500))
end
| uu____12501 -> begin
()
end));
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____12502) -> begin
(failwith "add_sigelt_to_env: Impossible, bare data constructor")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____12519) -> begin
(failwith "add_sigelt_to_env: Impossible, bare data constructor")
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (uu____12534)) -> begin
(z3_reset_options env)
end
| FStar_Syntax_Syntax.Sig_pragma (uu____12537) -> begin
env
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____12538) -> begin
env
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_sigelt env se)
in (FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun env2 a -> (

let uu____12548 = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Env.push_sigelt env2 uu____12548))) env1)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____12549, uu____12550, uu____12551) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___378_12555 -> (match (uu___378_12555) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____12556 -> begin
false
end)))) -> begin
env
end
| FStar_Syntax_Syntax.Sig_let (uu____12557, uu____12558) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___378_12566 -> (match (uu___378_12566) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____12567 -> begin
false
end)))) -> begin
env
end
| uu____12568 -> begin
(FStar_TypeChecker_Env.push_sigelt env se)
end);
))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let rec process_one_decl = (fun uu____12636 se -> (match (uu____12636) with
| (ses1, exports, env1, hidden) -> begin
((

let uu____12689 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____12689) with
| true -> begin
(

let uu____12690 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____12690))
end
| uu____12691 -> begin
()
end));
(

let uu____12692 = (tc_decl env1 se)
in (match (uu____12692) with
| (ses', ses_elaborated, env2) -> begin
(

let ses'1 = (FStar_All.pipe_right ses' (FStar_List.map (fun se1 -> ((

let uu____12745 = (FStar_TypeChecker_Env.debug env2 (FStar_Options.Other ("UF")))
in (match (uu____12745) with
| true -> begin
(

let uu____12746 = (FStar_Syntax_Print.sigelt_to_string se1)
in (FStar_Util.print1 "About to elim vars from %s\n" uu____12746))
end
| uu____12747 -> begin
()
end));
(FStar_TypeChecker_Normalize.elim_uvars env2 se1);
))))
in (

let ses_elaborated1 = (FStar_All.pipe_right ses_elaborated (FStar_List.map (fun se1 -> ((

let uu____12759 = (FStar_TypeChecker_Env.debug env2 (FStar_Options.Other ("UF")))
in (match (uu____12759) with
| true -> begin
(

let uu____12760 = (FStar_Syntax_Print.sigelt_to_string se1)
in (FStar_Util.print1 "About to elim vars from (elaborated) %s\\m" uu____12760))
end
| uu____12761 -> begin
()
end));
(FStar_TypeChecker_Normalize.elim_uvars env2 se1);
))))
in ((FStar_TypeChecker_Env.promote_id_info env2 (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.AllowUnboundUniverses)::(FStar_TypeChecker_Env.CheckNoUvars)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.DoNotUnfoldPureLets)::(FStar_TypeChecker_Env.CompressUvars)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Iota))::(FStar_TypeChecker_Env.NoFullNorm)::[]) env2 t)));
(

let env3 = (FStar_All.pipe_right ses'1 (FStar_List.fold_left (fun env3 se1 -> (add_sigelt_to_env env3 se1)) env2))
in ((FStar_Syntax_Unionfind.reset ());
(

let uu____12774 = ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env3) (FStar_Options.Other ("LogTypes"))))
in (match (uu____12774) with
| true -> begin
(

let uu____12775 = (FStar_List.fold_left (fun s se1 -> (

let uu____12781 = (

let uu____12782 = (FStar_Syntax_Print.sigelt_to_string se1)
in (Prims.strcat uu____12782 "\n"))
in (Prims.strcat s uu____12781))) "" ses'1)
in (FStar_Util.print1 "Checked: %s\n" uu____12775))
end
| uu____12783 -> begin
()
end));
(FStar_List.iter (fun se1 -> (env3.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env3 se1)) ses'1);
(

let uu____12787 = (

let uu____12796 = (FStar_Options.use_extracted_interfaces ())
in (match (uu____12796) with
| true -> begin
(((FStar_List.rev_append ses'1 exports)), ([]))
end
| uu____12809 -> begin
(

let accum_exports_hidden = (fun uu____12835 se1 -> (match (uu____12835) with
| (exports1, hidden1) -> begin
(

let uu____12863 = (for_export hidden1 se1)
in (match (uu____12863) with
| (se_exported, hidden2) -> begin
(((FStar_List.rev_append se_exported exports1)), (hidden2))
end))
end))
in (FStar_List.fold_left accum_exports_hidden ((exports), (hidden)) ses'1))
end))
in (match (uu____12787) with
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

let uu____13017 = acc
in (match (uu____13017) with
| (uu____13052, uu____13053, env1, uu____13055) -> begin
(

let uu____13068 = (FStar_Util.record_time (fun uu____13114 -> (process_one_decl acc se)))
in (match (uu____13068) with
| (r, ms_elapsed) -> begin
((

let uu____13178 = (((FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("TCDeclTime"))) || (FStar_Util.for_some (FStar_Syntax_Util.attr_eq FStar_Syntax_Util.tcdecltime_attr) se.FStar_Syntax_Syntax.sigattrs)) || (FStar_Options.timing ()))
in (match (uu____13178) with
| true -> begin
(

let uu____13179 = (FStar_Syntax_Print.sigelt_to_string_short se)
in (

let uu____13180 = (FStar_Util.string_of_int ms_elapsed)
in (FStar_Util.print2 "Checked %s in %s milliseconds\n" uu____13179 uu____13180)))
end
| uu____13181 -> begin
()
end));
r;
)
end))
end)))
in (

let uu____13182 = (FStar_Util.fold_flatten process_one_decl_timed (([]), ([]), (env), ([])) ses)
in (match (uu____13182) with
| (ses1, exports, env1, uu____13230) -> begin
(((FStar_List.rev_append ses1 [])), ((FStar_List.rev_append exports [])), (env1))
end)))))


let check_exports : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  unit = (fun env modul exports -> (

let env1 = (

let uu___430_13267 = env
in {FStar_TypeChecker_Env.solver = uu___430_13267.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___430_13267.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___430_13267.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___430_13267.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___430_13267.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___430_13267.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___430_13267.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___430_13267.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___430_13267.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___430_13267.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___430_13267.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___430_13267.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___430_13267.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___430_13267.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___430_13267.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = uu___430_13267.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___430_13267.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___430_13267.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___430_13267.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = true; FStar_TypeChecker_Env.phase1 = uu___430_13267.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___430_13267.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___430_13267.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___430_13267.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___430_13267.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___430_13267.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___430_13267.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___430_13267.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___430_13267.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___430_13267.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___430_13267.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___430_13267.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___430_13267.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___430_13267.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___430_13267.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___430_13267.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___430_13267.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___430_13267.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___430_13267.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___430_13267.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___430_13267.FStar_TypeChecker_Env.nbe})
in (

let check_term = (fun lid univs1 t -> (

let uu____13284 = (FStar_Syntax_Subst.open_univ_vars univs1 t)
in (match (uu____13284) with
| (univs2, t1) -> begin
((

let uu____13292 = (

let uu____13293 = (

let uu____13298 = (FStar_TypeChecker_Env.set_current_module env1 modul.FStar_Syntax_Syntax.name)
in (FStar_TypeChecker_Env.debug uu____13298))
in (FStar_All.pipe_left uu____13293 (FStar_Options.Other ("Exports"))))
in (match (uu____13292) with
| true -> begin
(

let uu____13299 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____13300 = (

let uu____13301 = (FStar_All.pipe_right univs2 (FStar_List.map (fun x -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (x))))))
in (FStar_All.pipe_right uu____13301 (FStar_String.concat ", ")))
in (

let uu____13312 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Checking for export %s <%s> : %s\n" uu____13299 uu____13300 uu____13312))))
end
| uu____13313 -> begin
()
end));
(

let env2 = (FStar_TypeChecker_Env.push_univ_vars env1 univs2)
in (

let uu____13315 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1)
in (FStar_All.pipe_right uu____13315 (fun a2 -> ()))));
)
end)))
in (

let check_term1 = (fun lid univs1 t -> ((

let uu____13341 = (

let uu____13342 = (FStar_Syntax_Print.lid_to_string modul.FStar_Syntax_Syntax.name)
in (

let uu____13343 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Interface of %s violates its abstraction (add a \'private\' qualifier to \'%s\'?)" uu____13342 uu____13343)))
in (FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____13341));
(check_term lid univs1 t);
(FStar_Errors.message_prefix.FStar_Errors.clear_prefix ());
))
in (

let rec check_sigelt = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____13352) -> begin
(

let uu____13361 = (

let uu____13362 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____13362)))
in (match (uu____13361) with
| true -> begin
(FStar_All.pipe_right ses (FStar_List.iter check_sigelt))
end
| uu____13367 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (l, univs1, binders, typ, uu____13372, uu____13373) -> begin
(

let t = (

let uu____13385 = (

let uu____13392 = (

let uu____13393 = (

let uu____13408 = (FStar_Syntax_Syntax.mk_Total typ)
in ((binders), (uu____13408)))
in FStar_Syntax_Syntax.Tm_arrow (uu____13393))
in (FStar_Syntax_Syntax.mk uu____13392))
in (uu____13385 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng))
in (check_term1 l univs1 t))
end
| FStar_Syntax_Syntax.Sig_datacon (l, univs1, t, uu____13427, uu____13428, uu____13429) -> begin
(check_term1 l univs1 t)
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, univs1, t) -> begin
(

let uu____13437 = (

let uu____13438 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____13438)))
in (match (uu____13437) with
| true -> begin
(check_term1 l univs1 t)
end
| uu____13441 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_let ((uu____13442, lbs), uu____13444) -> begin
(

let uu____13453 = (

let uu____13454 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____13454)))
in (match (uu____13453) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (check_term1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp)))))
end
| uu____13463 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs1, binders, comp, flags1) -> begin
(

let uu____13473 = (

let uu____13474 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____13474)))
in (match (uu____13473) with
| true -> begin
(

let arrow1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))) FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng)
in (check_term1 l univs1 arrow1))
end
| uu____13490 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_main (uu____13491) -> begin
()
end
| FStar_Syntax_Syntax.Sig_assume (uu____13492) -> begin
()
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____13499) -> begin
()
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____13500) -> begin
()
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____13501) -> begin
()
end
| FStar_Syntax_Syntax.Sig_splice (uu____13502) -> begin
()
end
| FStar_Syntax_Syntax.Sig_pragma (uu____13509) -> begin
()
end))
in (

let uu____13510 = (FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Parser_Const.prims_lid)
in (match (uu____13510) with
| true -> begin
()
end
| uu____13511 -> begin
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
| FStar_Syntax_Syntax.Projector (l, uu____13605) -> begin
true
end
| uu____13606 -> begin
false
end)) quals))
in (

let vals_of_abstract_inductive = (fun s -> (

let mk_typ_for_abstract_inductive = (fun bs t r -> (match (bs) with
| [] -> begin
t
end
| uu____13635 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs', c) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((((FStar_List.append bs bs')), (c)))) FStar_Pervasives_Native.None r)
end
| uu____13674 -> begin
(

let uu____13675 = (

let uu____13682 = (

let uu____13683 = (

let uu____13698 = (FStar_Syntax_Syntax.mk_Total t)
in ((bs), (uu____13698)))
in FStar_Syntax_Syntax.Tm_arrow (uu____13683))
in (FStar_Syntax_Syntax.mk uu____13682))
in (uu____13675 FStar_Pervasives_Native.None r))
end)
end))
in (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uvs, bs, t, uu____13718, uu____13719) -> begin
(

let s1 = (

let uu___431_13729 = s
in (

let uu____13730 = (

let uu____13731 = (

let uu____13738 = (mk_typ_for_abstract_inductive bs t s.FStar_Syntax_Syntax.sigrng)
in ((lid), (uvs), (uu____13738)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____13731))
in (

let uu____13739 = (

let uu____13742 = (

let uu____13745 = (filter_out_abstract_and_noeq s.FStar_Syntax_Syntax.sigquals)
in (FStar_Syntax_Syntax.New)::uu____13745)
in (FStar_Syntax_Syntax.Assumption)::uu____13742)
in {FStar_Syntax_Syntax.sigel = uu____13730; FStar_Syntax_Syntax.sigrng = uu___431_13729.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu____13739; FStar_Syntax_Syntax.sigmeta = uu___431_13729.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___431_13729.FStar_Syntax_Syntax.sigattrs})))
in (s1)::[])
end
| uu____13748 -> begin
(failwith "Impossible!")
end)))
in (

let val_of_lb = (fun s lid uu____13772 lbdef -> (match (uu____13772) with
| (uvs, t) -> begin
(

let attrs = (

let uu____13783 = (FStar_TypeChecker_Util.must_erase_for_extraction en lbdef)
in (match (uu____13783) with
| true -> begin
(

let uu____13786 = (

let uu____13787 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.must_erase_for_extraction_attr FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_All.pipe_right uu____13787 FStar_Syntax_Syntax.fv_to_tm))
in (uu____13786)::s.FStar_Syntax_Syntax.sigattrs)
end
| uu____13788 -> begin
s.FStar_Syntax_Syntax.sigattrs
end))
in (

let uu___432_13789 = s
in (

let uu____13790 = (

let uu____13793 = (filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals)
in (FStar_Syntax_Syntax.Assumption)::uu____13793)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (uvs), (t))); FStar_Syntax_Syntax.sigrng = uu___432_13789.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu____13790; FStar_Syntax_Syntax.sigmeta = uu___432_13789.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = attrs})))
end))
in (

let should_keep_lbdef = (fun t -> (

let comp_effect_name1 = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c1) -> begin
c1.FStar_Syntax_Syntax.effect_name
end
| uu____13809 -> begin
(failwith "Impossible!")
end))
in (

let c_opt = (

let uu____13815 = (FStar_Syntax_Util.is_unit t)
in (match (uu____13815) with
| true -> begin
(

let uu____13820 = (FStar_Syntax_Syntax.mk_Total t)
in FStar_Pervasives_Native.Some (uu____13820))
end
| uu____13825 -> begin
(

let uu____13826 = (

let uu____13827 = (FStar_Syntax_Subst.compress t)
in uu____13827.FStar_Syntax_Syntax.n)
in (match (uu____13826) with
| FStar_Syntax_Syntax.Tm_arrow (uu____13834, c) -> begin
FStar_Pervasives_Native.Some (c)
end
| uu____13858 -> begin
FStar_Pervasives_Native.None
end))
end))
in (match (c_opt) with
| FStar_Pervasives_Native.None -> begin
true
end
| FStar_Pervasives_Native.Some (c) -> begin
(

let uu____13868 = (FStar_Syntax_Util.is_lemma_comp c)
in (match (uu____13868) with
| true -> begin
false
end
| uu____13869 -> begin
(

let uu____13870 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (match (uu____13870) with
| true -> begin
true
end
| uu____13871 -> begin
(

let uu____13872 = (comp_effect_name1 c)
in (FStar_TypeChecker_Env.is_reifiable_effect en uu____13872))
end))
end))
end))))
in (

let extract_sigelt = (fun s -> ((

let uu____13884 = (FStar_TypeChecker_Env.debug en FStar_Options.Extreme)
in (match (uu____13884) with
| true -> begin
(

let uu____13885 = (FStar_Syntax_Print.sigelt_to_string s)
in (FStar_Util.print1 "Extracting interface for %s\n" uu____13885))
end
| uu____13886 -> begin
()
end));
(match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____13889) -> begin
(failwith "Impossible! extract_interface: bare data constructor")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____13908) -> begin
(failwith "Impossible! extract_interface: bare data constructor")
end
| FStar_Syntax_Syntax.Sig_splice (uu____13925) -> begin
(failwith "Impossible! extract_interface: trying to extract splice")
end
| FStar_Syntax_Syntax.Sig_bundle (sigelts, lidents1) -> begin
(match ((is_abstract s.FStar_Syntax_Syntax.sigquals)) with
| true -> begin
(FStar_All.pipe_right sigelts (FStar_List.fold_left (fun sigelts1 s1 -> (match (s1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____13969, uu____13970, uu____13971, uu____13972, uu____13973) -> begin
((

let uu____13983 = (

let uu____13986 = (FStar_ST.op_Bang abstract_inductive_tycons)
in (lid)::uu____13986)
in (FStar_ST.op_Colon_Equals abstract_inductive_tycons uu____13983));
(

let uu____14079 = (vals_of_abstract_inductive s1)
in (FStar_List.append uu____14079 sigelts1));
)
end
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____14083, uu____14084, uu____14085, uu____14086, uu____14087) -> begin
((

let uu____14093 = (

let uu____14096 = (FStar_ST.op_Bang abstract_inductive_datacons)
in (lid)::uu____14096)
in (FStar_ST.op_Colon_Equals abstract_inductive_datacons uu____14093));
sigelts1;
)
end
| uu____14189 -> begin
(failwith "Impossible! extract_interface: Sig_bundle can\'t have anything other than Sig_inductive_typ and Sig_datacon")
end)) []))
end
| uu____14192 -> begin
(s)::[]
end)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) -> begin
(

let uu____14196 = (is_projector_or_discriminator_of_an_abstract_inductive s.FStar_Syntax_Syntax.sigquals)
in (match (uu____14196) with
| true -> begin
[]
end
| uu____14199 -> begin
(match ((is_assume s.FStar_Syntax_Syntax.sigquals)) with
| true -> begin
(

let uu____14202 = (

let uu___433_14203 = s
in (

let uu____14204 = (filter_out_abstract s.FStar_Syntax_Syntax.sigquals)
in {FStar_Syntax_Syntax.sigel = uu___433_14203.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___433_14203.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu____14204; FStar_Syntax_Syntax.sigmeta = uu___433_14203.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___433_14203.FStar_Syntax_Syntax.sigattrs}))
in (uu____14202)::[])
end
| uu____14207 -> begin
[]
end)
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, lids) -> begin
(

let uu____14214 = (is_projector_or_discriminator_of_an_abstract_inductive s.FStar_Syntax_Syntax.sigquals)
in (match (uu____14214) with
| true -> begin
[]
end
| uu____14217 -> begin
(

let uu____14218 = lbs
in (match (uu____14218) with
| (flbs, slbs) -> begin
(

let typs_and_defs = (FStar_All.pipe_right slbs (FStar_List.map (fun lb -> ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (lb.FStar_Syntax_Syntax.lbdef)))))
in (

let is_lemma1 = (FStar_List.existsML (fun uu____14277 -> (match (uu____14277) with
| (uu____14284, t, uu____14286) -> begin
(FStar_All.pipe_right t FStar_Syntax_Util.is_lemma)
end)) typs_and_defs)
in (

let vals = (FStar_List.map2 (fun lid uu____14302 -> (match (uu____14302) with
| (u, t, d) -> begin
(val_of_lb s lid ((u), (t)) d)
end)) lids typs_and_defs)
in (match ((((is_abstract s.FStar_Syntax_Syntax.sigquals) || (is_irreducible1 s.FStar_Syntax_Syntax.sigquals)) || is_lemma1)) with
| true -> begin
vals
end
| uu____14314 -> begin
(

let should_keep_defs = (FStar_List.existsML (fun uu____14326 -> (match (uu____14326) with
| (uu____14333, t, uu____14335) -> begin
(FStar_All.pipe_right t should_keep_lbdef)
end)) typs_and_defs)
in (match (should_keep_defs) with
| true -> begin
(s)::[]
end
| uu____14338 -> begin
vals
end))
end))))
end))
end))
end
| FStar_Syntax_Syntax.Sig_main (t) -> begin
(failwith "Did not anticipate main would arise when extracting interfaces!")
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____14343, uu____14344) -> begin
(

let is_haseq = (FStar_TypeChecker_TcInductive.is_haseq_lid lid)
in (match (is_haseq) with
| true -> begin
(

let is_haseq_of_abstract_inductive = (

let uu____14349 = (FStar_ST.op_Bang abstract_inductive_tycons)
in (FStar_List.existsML (fun l -> (

let uu____14400 = (FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l)
in (FStar_Ident.lid_equals lid uu____14400))) uu____14349))
in (match (is_haseq_of_abstract_inductive) with
| true -> begin
(

let uu____14403 = (

let uu___434_14404 = s
in (

let uu____14405 = (filter_out_abstract s.FStar_Syntax_Syntax.sigquals)
in {FStar_Syntax_Syntax.sigel = uu___434_14404.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___434_14404.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu____14405; FStar_Syntax_Syntax.sigmeta = uu___434_14404.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___434_14404.FStar_Syntax_Syntax.sigattrs}))
in (uu____14403)::[])
end
| uu____14408 -> begin
[]
end))
end
| uu____14409 -> begin
(

let uu____14410 = (

let uu___435_14411 = s
in (

let uu____14412 = (filter_out_abstract s.FStar_Syntax_Syntax.sigquals)
in {FStar_Syntax_Syntax.sigel = uu___435_14411.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___435_14411.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu____14412; FStar_Syntax_Syntax.sigmeta = uu___435_14411.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___435_14411.FStar_Syntax_Syntax.sigattrs}))
in (uu____14410)::[])
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____14415) -> begin
(s)::[]
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____14416) -> begin
(s)::[]
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____14417) -> begin
(s)::[]
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____14418) -> begin
(s)::[]
end
| FStar_Syntax_Syntax.Sig_pragma (uu____14431) -> begin
(s)::[]
end);
))
in (

let uu___436_14432 = m
in (

let uu____14433 = (

let uu____14434 = (FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations (FStar_List.map extract_sigelt))
in (FStar_All.pipe_right uu____14434 FStar_List.flatten))
in {FStar_Syntax_Syntax.name = uu___436_14432.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu____14433; FStar_Syntax_Syntax.exports = uu___436_14432.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = true}))))))))))))))))


let snapshot_context : FStar_TypeChecker_Env.env  ->  Prims.string  ->  ((Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t * Prims.int) * FStar_TypeChecker_Env.env) = (fun env msg -> (FStar_Util.atomically (fun uu____14478 -> (FStar_TypeChecker_Env.snapshot env msg))))


let rollback_context : FStar_TypeChecker_Env.solver_t  ->  Prims.string  ->  (Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t * Prims.int) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env = (fun solver msg depth -> (FStar_Util.atomically (fun uu____14517 -> (

let env = (FStar_TypeChecker_Env.rollback solver msg depth)
in ((solver.FStar_TypeChecker_Env.refresh ());
env;
)))))


let push_context : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Env.env = (fun env msg -> (

let uu____14530 = (snapshot_context env msg)
in (FStar_Pervasives_Native.snd uu____14530)))


let pop_context : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Env.env = (fun env msg -> (rollback_context env.FStar_TypeChecker_Env.solver msg FStar_Pervasives_Native.None))


let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (

let verify = (FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let action = (match (verify) with
| true -> begin
"Verifying"
end
| uu____14589 -> begin
"Lax-checking"
end)
in (

let label1 = (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____14591 -> begin
"implementation"
end)
in ((

let uu____14593 = (FStar_Options.debug_any ())
in (match (uu____14593) with
| true -> begin
(FStar_Util.print3 "%s %s of %s\n" action label1 modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
end
| uu____14594 -> begin
()
end));
(

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____14596 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let env1 = (

let uu___437_14598 = env
in {FStar_TypeChecker_Env.solver = uu___437_14598.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___437_14598.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___437_14598.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___437_14598.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___437_14598.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___437_14598.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___437_14598.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___437_14598.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___437_14598.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___437_14598.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___437_14598.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___437_14598.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___437_14598.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___437_14598.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___437_14598.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___437_14598.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___437_14598.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___437_14598.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = (not (verify)); FStar_TypeChecker_Env.lax = uu___437_14598.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___437_14598.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___437_14598.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___437_14598.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___437_14598.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___437_14598.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___437_14598.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___437_14598.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___437_14598.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___437_14598.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___437_14598.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___437_14598.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___437_14598.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___437_14598.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___437_14598.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___437_14598.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___437_14598.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___437_14598.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___437_14598.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___437_14598.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___437_14598.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___437_14598.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___437_14598.FStar_TypeChecker_Env.nbe})
in (

let env2 = (FStar_TypeChecker_Env.set_current_module env1 modul.FStar_Syntax_Syntax.name)
in (

let uu____14600 = (tc_decls env2 modul.FStar_Syntax_Syntax.declarations)
in (match (uu____14600) with
| (ses, exports, env3) -> begin
(((

let uu___438_14633 = modul
in {FStar_Syntax_Syntax.name = uu___438_14633.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = uu___438_14633.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___438_14633.FStar_Syntax_Syntax.is_interface})), (exports), (env3))
end)))));
)))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let uu____14661 = (tc_decls env decls)
in (match (uu____14661) with
| (ses, exports, env1) -> begin
(

let modul1 = (

let uu___439_14692 = modul
in {FStar_Syntax_Syntax.name = uu___439_14692.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = uu___439_14692.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___439_14692.FStar_Syntax_Syntax.is_interface})
in ((modul1), (exports), (env1)))
end)))


let rec tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.bool  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_TypeChecker_Env.env) = (fun env0 m iface_exists -> (

let msg = (Prims.strcat "Internals for " m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let env01 = (push_context env0 msg)
in (

let uu____14758 = (tc_partial_modul env01 m)
in (match (uu____14758) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul false iface_exists env modul non_private_decls)
end)))))
and finish_partial_modul : Prims.bool  ->  Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_TypeChecker_Env.env) = (fun loading_from_cache iface_exists en m exports -> (

let should_extract_interface = (((((not (loading_from_cache)) && (not (iface_exists))) && (FStar_Options.use_extracted_interfaces ())) && (not (m.FStar_Syntax_Syntax.is_interface))) && (

let uu____14799 = (FStar_Errors.get_err_count ())
in (Prims.op_Equality uu____14799 (Prims.parse_int "0"))))
in (match (should_extract_interface) with
| true -> begin
(

let modul_iface = (extract_interface en m)
in ((

let uu____14810 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug en) FStar_Options.Low)
in (match (uu____14810) with
| true -> begin
(

let uu____14811 = (

let uu____14812 = (FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____14812) with
| true -> begin
""
end
| uu____14813 -> begin
" (in lax mode) "
end))
in (

let uu____14814 = (

let uu____14815 = (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____14815) with
| true -> begin
(

let uu____14816 = (

let uu____14817 = (FStar_Syntax_Print.modul_to_string m)
in (Prims.strcat uu____14817 "\n"))
in (Prims.strcat "\nfrom: " uu____14816))
end
| uu____14818 -> begin
""
end))
in (

let uu____14819 = (

let uu____14820 = (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____14820) with
| true -> begin
(

let uu____14821 = (

let uu____14822 = (FStar_Syntax_Print.modul_to_string modul_iface)
in (Prims.strcat uu____14822 "\n"))
in (Prims.strcat "\nto: " uu____14821))
end
| uu____14823 -> begin
""
end))
in (FStar_Util.print4 "Extracting and type checking module %s interface%s%s%s\n" m.FStar_Syntax_Syntax.name.FStar_Ident.str uu____14811 uu____14814 uu____14819))))
end
| uu____14824 -> begin
()
end));
(

let en0 = (

let en0 = (pop_context en (Prims.strcat "Ending modul " m.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (

let en01 = (

let uu___440_14828 = en0
in (

let uu____14829 = (

let uu____14842 = (FStar_All.pipe_right en.FStar_TypeChecker_Env.qtbl_name_and_index FStar_Pervasives_Native.fst)
in ((uu____14842), (FStar_Pervasives_Native.None)))
in {FStar_TypeChecker_Env.solver = uu___440_14828.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___440_14828.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___440_14828.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___440_14828.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___440_14828.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___440_14828.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___440_14828.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___440_14828.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___440_14828.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___440_14828.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___440_14828.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___440_14828.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___440_14828.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___440_14828.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___440_14828.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___440_14828.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___440_14828.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___440_14828.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___440_14828.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___440_14828.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___440_14828.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___440_14828.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___440_14828.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___440_14828.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___440_14828.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___440_14828.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___440_14828.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___440_14828.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___440_14828.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___440_14828.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___440_14828.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu____14829; FStar_TypeChecker_Env.normalized_eff_names = uu___440_14828.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___440_14828.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___440_14828.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___440_14828.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___440_14828.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___440_14828.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___440_14828.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___440_14828.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___440_14828.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___440_14828.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___440_14828.FStar_TypeChecker_Env.nbe}))
in (

let uu____14879 = (

let uu____14880 = (FStar_Options.interactive ())
in (not (uu____14880)))
in (match (uu____14879) with
| true -> begin
((

let uu____14882 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right uu____14882 (fun a3 -> ())));
(z3_reset_options en01);
)
end
| uu____14883 -> begin
en01
end))))
in (

let uu____14884 = (tc_modul en0 modul_iface true)
in (match (uu____14884) with
| (modul_iface1, must_be_none, env) -> begin
(match ((FStar_Option.isSome must_be_none)) with
| true -> begin
(failwith "Impossible! finish_partial_module: expected the second component to be None")
end
| uu____14924 -> begin
(((

let uu___441_14928 = m
in {FStar_Syntax_Syntax.name = uu___441_14928.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu___441_14928.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = modul_iface1.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___441_14928.FStar_Syntax_Syntax.is_interface})), (FStar_Pervasives_Native.Some (modul_iface1)), (env))
end)
end)));
))
end
| uu____14929 -> begin
(

let modul = (

let uu___442_14931 = m
in {FStar_Syntax_Syntax.name = uu___442_14931.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu___442_14931.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = uu___442_14931.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module en modul)
in ((

let uu____14934 = (FStar_All.pipe_right env.FStar_TypeChecker_Env.qtbl_name_and_index FStar_Pervasives_Native.fst)
in (FStar_All.pipe_right uu____14934 FStar_Util.smap_clear));
(

let uu____14962 = (((

let uu____14965 = (FStar_Options.lax ())
in (not (uu____14965))) && (not (loading_from_cache))) && (

let uu____14967 = (FStar_Options.use_extracted_interfaces ())
in (not (uu____14967))))
in (match (uu____14962) with
| true -> begin
(check_exports env modul exports)
end
| uu____14968 -> begin
()
end));
(

let uu____14970 = (pop_context env (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (FStar_All.pipe_right uu____14970 (fun a4 -> ())));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul);
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
(

let uu____14974 = (

let uu____14975 = (FStar_Options.interactive ())
in (not (uu____14975)))
in (match (uu____14974) with
| true -> begin
(

let uu____14976 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right uu____14976 (fun a5 -> ())))
end
| uu____14977 -> begin
()
end));
((modul), (FStar_Pervasives_Native.None), (env));
)))
end)))


let load_checked_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_TypeChecker_Env.env = (fun en m -> (

let env = (FStar_TypeChecker_Env.set_current_module en m.FStar_Syntax_Syntax.name)
in (

let env1 = (

let uu____14992 = (

let uu____14993 = (FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name)
in (Prims.strcat "Internals for " uu____14993))
in (push_context env uu____14992))
in (

let env2 = (FStar_List.fold_left (fun env2 se -> (

let env3 = (FStar_TypeChecker_Env.push_sigelt env2 se)
in (

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in ((FStar_All.pipe_right lids (FStar_List.iter (fun lid -> (

let uu____15012 = (FStar_TypeChecker_Env.try_lookup_lid env3 lid)
in ()))));
env3;
)))) env1 m.FStar_Syntax_Syntax.declarations)
in (

let uu____15023 = (finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports)
in (match (uu____15023) with
| (uu____15032, uu____15033, env3) -> begin
env3
end))))))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.bool  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option * FStar_TypeChecker_Env.env) = (fun env m b -> ((

let uu____15063 = (FStar_Options.debug_any ())
in (match (uu____15063) with
| true -> begin
(

let uu____15064 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (match (m.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"i\'face"
end
| uu____15065 -> begin
"module"
end) uu____15064))
end
| uu____15066 -> begin
()
end));
(

let uu____15068 = (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____15068) with
| true -> begin
(

let uu____15069 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "Module before type checking:\n%s\n" uu____15069))
end
| uu____15070 -> begin
()
end));
(

let env1 = (

let uu___443_15072 = env
in (

let uu____15073 = (

let uu____15074 = (FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (not (uu____15074)))
in {FStar_TypeChecker_Env.solver = uu___443_15072.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___443_15072.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___443_15072.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___443_15072.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___443_15072.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___443_15072.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___443_15072.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___443_15072.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___443_15072.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___443_15072.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___443_15072.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___443_15072.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___443_15072.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___443_15072.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___443_15072.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___443_15072.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___443_15072.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___443_15072.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___443_15072.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___443_15072.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu____15073; FStar_TypeChecker_Env.lax_universes = uu___443_15072.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___443_15072.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___443_15072.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___443_15072.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___443_15072.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___443_15072.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___443_15072.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___443_15072.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___443_15072.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___443_15072.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___443_15072.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___443_15072.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___443_15072.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___443_15072.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___443_15072.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___443_15072.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___443_15072.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___443_15072.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___443_15072.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___443_15072.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___443_15072.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___443_15072.FStar_TypeChecker_Env.nbe}))
in (

let uu____15075 = (tc_modul env1 m b)
in (match (uu____15075) with
| (m1, m_iface_opt, env2) -> begin
((

let uu____15100 = (FStar_Options.dump_module m1.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____15100) with
| true -> begin
(

let uu____15101 = (FStar_Syntax_Print.modul_to_string m1)
in (FStar_Util.print1 "Module after type checking:\n%s\n" uu____15101))
end
| uu____15102 -> begin
()
end));
(

let uu____15104 = ((FStar_Options.dump_module m1.FStar_Syntax_Syntax.name.FStar_Ident.str) && (FStar_Options.debug_at_level m1.FStar_Syntax_Syntax.name.FStar_Ident.str (FStar_Options.Other ("Normalize"))))
in (match (uu____15104) with
| true -> begin
(

let normalize_toplevel_lets = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((b1, lbs), ids) -> begin
(

let n1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Reify)::(FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.AllowUnboundUniverses)::[]))
in (

let update = (fun lb -> (

let uu____15137 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____15137) with
| (univnames1, e) -> begin
(

let uu___444_15144 = lb
in (

let uu____15145 = (

let uu____15148 = (FStar_TypeChecker_Env.push_univ_vars env2 univnames1)
in (n1 uu____15148 e))
in {FStar_Syntax_Syntax.lbname = uu___444_15144.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___444_15144.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___444_15144.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___444_15144.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____15145; FStar_Syntax_Syntax.lbattrs = uu___444_15144.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___444_15144.FStar_Syntax_Syntax.lbpos}))
end)))
in (

let uu___445_15149 = se
in (

let uu____15150 = (

let uu____15151 = (

let uu____15158 = (

let uu____15159 = (FStar_List.map update lbs)
in ((b1), (uu____15159)))
in ((uu____15158), (ids)))
in FStar_Syntax_Syntax.Sig_let (uu____15151))
in {FStar_Syntax_Syntax.sigel = uu____15150; FStar_Syntax_Syntax.sigrng = uu___445_15149.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___445_15149.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___445_15149.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___445_15149.FStar_Syntax_Syntax.sigattrs}))))
end
| uu____15166 -> begin
se
end))
in (

let normalized_module = (

let uu___446_15168 = m1
in (

let uu____15169 = (FStar_List.map normalize_toplevel_lets m1.FStar_Syntax_Syntax.declarations)
in {FStar_Syntax_Syntax.name = uu___446_15168.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu____15169; FStar_Syntax_Syntax.exports = uu___446_15168.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___446_15168.FStar_Syntax_Syntax.is_interface}))
in (

let uu____15170 = (FStar_Syntax_Print.modul_to_string normalized_module)
in (FStar_Util.print1 "%s\n" uu____15170))))
end
| uu____15171 -> begin
()
end));
((m1), (m_iface_opt), (env2));
)
end)));
))




