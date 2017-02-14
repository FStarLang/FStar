
open Prims

let set_hint_correlator : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env = (fun env se -> (

let uu____7 = (FStar_Options.reuse_hint_for ())
in (match (uu____7) with
| Some (l) -> begin
(

let lid = (

let uu____11 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_add_suffix uu____11 l))
in (

let uu___83_12 = env
in {FStar_TypeChecker_Env.solver = uu___83_12.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___83_12.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___83_12.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___83_12.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___83_12.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___83_12.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___83_12.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___83_12.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___83_12.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___83_12.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___83_12.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___83_12.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___83_12.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___83_12.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___83_12.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___83_12.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___83_12.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___83_12.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___83_12.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___83_12.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___83_12.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___83_12.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___83_12.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), ((Prims.parse_int "0"))))}))
end
| None -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (

let lid = (match (lids) with
| [] -> begin
(

let uu____18 = (FStar_TypeChecker_Env.current_module env)
in (

let uu____19 = (

let uu____20 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_right uu____20 FStar_Util.string_of_int))
in (FStar_Ident.lid_add_suffix uu____18 uu____19)))
end
| (l)::uu____22 -> begin
l
end)
in (

let uu___84_24 = env
in {FStar_TypeChecker_Env.solver = uu___84_24.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___84_24.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___84_24.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___84_24.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___84_24.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___84_24.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___84_24.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___84_24.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___84_24.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___84_24.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___84_24.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___84_24.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___84_24.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___84_24.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___84_24.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___84_24.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___84_24.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___84_24.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___84_24.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___84_24.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___84_24.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___84_24.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___84_24.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), ((Prims.parse_int "0"))))})))
end)))


let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_Options.log_types ()) && (

let uu____30 = (

let uu____31 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____31))
in (not (uu____30)))))


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let uu____41 = (FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k)
in (match (uu____41) with
| (t, c, g) -> begin
((FStar_ST.write t.FStar_Syntax_Syntax.tk (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)));
(FStar_TypeChecker_Rel.force_trivial_guard env g);
t;
)
end)))


let recheck_debug : Prims.string  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s env t -> ((

let uu____63 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____63) with
| true -> begin
(

let uu____64 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Term has been %s-transformed to:\n%s\n----------\n" s uu____64))
end
| uu____65 -> begin
()
end));
(

let uu____66 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (uu____66) with
| (t', uu____71, uu____72) -> begin
((

let uu____74 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____74) with
| true -> begin
(

let uu____75 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print1 "Re-checked; got:\n%s\n----------\n" uu____75))
end
| uu____76 -> begin
()
end));
t;
)
end));
))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (

let uu____86 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env uu____86)))


let check_nogen = (fun env t k -> (

let t = (tc_check_trivial_guard env t k)
in (

let uu____108 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (([]), (uu____108)))))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun env m s -> (

let fail = (fun uu____130 -> (

let uu____131 = (

let uu____132 = (

let uu____135 = (FStar_TypeChecker_Err.unexpected_signature_for_monad env m s)
in ((uu____135), ((FStar_Ident.range_of_lid m))))
in FStar_Errors.Error (uu____132))
in (Prims.raise uu____131)))
in (

let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, uu____163))::((wp, uu____165))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____174 -> begin
(fail ())
end))
end
| uu____175 -> begin
(fail ())
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let uu____205 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (uu____205) with
| (uvs, c) -> begin
((uvs), ([]), (c))
end))
end
| uu____221 -> begin
(

let t' = (FStar_Syntax_Util.arrow binders c)
in (

let uu____228 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (uu____228) with
| (uvs, t') -> begin
(

let uu____239 = (

let uu____240 = (FStar_Syntax_Subst.compress t')
in uu____240.FStar_Syntax_Syntax.n)
in (match (uu____239) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
((uvs), (binders), (c))
end
| uu____266 -> begin
(failwith "Impossible")
end))
end)))
end))


let rec tc_eff_decl : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (

let uu____335 = (FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____335) with
| (effect_params_un, signature_un, opening) -> begin
(

let uu____342 = (FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un)
in (match (uu____342) with
| (effect_params, env, uu____348) -> begin
(

let uu____349 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (uu____349) with
| (signature, uu____353) -> begin
(

let ed = (

let uu___85_355 = ed
in {FStar_Syntax_Syntax.qualifiers = uu___85_355.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___85_355.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___85_355.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___85_355.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = uu___85_355.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = uu___85_355.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = uu___85_355.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = uu___85_355.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = uu___85_355.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = uu___85_355.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = uu___85_355.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = uu___85_355.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = uu___85_355.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = uu___85_355.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = uu___85_355.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = uu___85_355.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = uu___85_355.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = uu___85_355.FStar_Syntax_Syntax.actions})
in (

let ed = (match (effect_params) with
| [] -> begin
ed
end
| uu____359 -> begin
(

let op = (fun ts -> (

let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in (([]), (t1))))
in (

let uu___86_377 = ed
in (

let uu____378 = (op ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____379 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____380 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____381 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____382 = (op ed.FStar_Syntax_Syntax.stronger)
in (

let uu____383 = (op ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____384 = (op ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____385 = (op ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____386 = (op ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____387 = (op ed.FStar_Syntax_Syntax.trivial)
in (

let uu____388 = (

let uu____389 = (op (([]), (ed.FStar_Syntax_Syntax.repr)))
in (Prims.snd uu____389))
in (

let uu____395 = (op ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____396 = (op ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____397 = (FStar_List.map (fun a -> (

let uu___87_400 = a
in (

let uu____401 = (

let uu____402 = (op (([]), (a.FStar_Syntax_Syntax.action_defn)))
in (Prims.snd uu____402))
in (

let uu____408 = (

let uu____409 = (op (([]), (a.FStar_Syntax_Syntax.action_typ)))
in (Prims.snd uu____409))
in {FStar_Syntax_Syntax.action_name = uu___87_400.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___87_400.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___87_400.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = uu____401; FStar_Syntax_Syntax.action_typ = uu____408})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.qualifiers = uu___86_377.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___86_377.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___86_377.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___86_377.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu___86_377.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = uu___86_377.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = uu____378; FStar_Syntax_Syntax.bind_wp = uu____379; FStar_Syntax_Syntax.if_then_else = uu____380; FStar_Syntax_Syntax.ite_wp = uu____381; FStar_Syntax_Syntax.stronger = uu____382; FStar_Syntax_Syntax.close_wp = uu____383; FStar_Syntax_Syntax.assert_p = uu____384; FStar_Syntax_Syntax.assume_p = uu____385; FStar_Syntax_Syntax.null_wp = uu____386; FStar_Syntax_Syntax.trivial = uu____387; FStar_Syntax_Syntax.repr = uu____388; FStar_Syntax_Syntax.return_repr = uu____395; FStar_Syntax_Syntax.bind_repr = uu____396; FStar_Syntax_Syntax.actions = uu____397}))))))))))))))))
end)
in (

let wp_with_fresh_result_type = (fun env mname signature -> (

let fail = (fun t -> (

let uu____437 = (

let uu____438 = (

let uu____441 = (FStar_TypeChecker_Err.unexpected_signature_for_monad env mname t)
in ((uu____441), ((FStar_Ident.range_of_lid mname))))
in FStar_Errors.Error (uu____438))
in (Prims.raise uu____437)))
in (

let uu____446 = (

let uu____447 = (FStar_Syntax_Subst.compress signature)
in uu____447.FStar_Syntax_Syntax.n)
in (match (uu____446) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, uu____472))::((wp, uu____474))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____483 -> begin
(fail signature)
end))
end
| uu____484 -> begin
(fail signature)
end))))
in (

let uu____485 = (wp_with_fresh_result_type env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (uu____485) with
| (a, wp_a) -> begin
(

let fresh_effect_signature = (fun uu____503 -> (

let uu____504 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (uu____504) with
| (signature, uu____512) -> begin
(wp_with_fresh_result_type env ed.FStar_Syntax_Syntax.mname signature)
end)))
in (

let env = (

let uu____514 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env uu____514))
in ((

let uu____516 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED")))
in (match (uu____516) with
| true -> begin
(

let uu____517 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____518 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (

let uu____519 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (

let uu____520 = (

let uu____521 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Print.term_to_string uu____521))
in (

let uu____522 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.sort)
in (FStar_Util.print5 "Checking effect signature: %s %s : %s\n(a is %s:%s)\n" uu____517 uu____518 uu____519 uu____520 uu____522))))))
end
| uu____523 -> begin
()
end));
(

let check_and_gen' = (fun env uu____535 k -> (match (uu____535) with
| (uu____540, t) -> begin
(check_and_gen env t k)
end))
in (

let return_wp = (

let expected_k = (

let uu____548 = (

let uu____552 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____553 = (

let uu____555 = (

let uu____556 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____556))
in (uu____555)::[])
in (uu____552)::uu____553))
in (

let uu____557 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow uu____548 uu____557)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret_wp expected_k))
in (

let bind_wp = (

let uu____561 = (fresh_effect_signature ())
in (match (uu____561) with
| (b, wp_b) -> begin
(

let a_wp_b = (

let uu____575 = (

let uu____579 = (

let uu____580 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____580))
in (uu____579)::[])
in (

let uu____581 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____575 uu____581)))
in (

let expected_k = (

let uu____587 = (

let uu____591 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (

let uu____592 = (

let uu____594 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____595 = (

let uu____597 = (FStar_Syntax_Syntax.mk_binder b)
in (

let uu____598 = (

let uu____600 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____601 = (

let uu____603 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (uu____603)::[])
in (uu____600)::uu____601))
in (uu____597)::uu____598))
in (uu____594)::uu____595))
in (uu____591)::uu____592))
in (

let uu____604 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____587 uu____604)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else = (

let p = (

let uu____609 = (

let uu____610 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____610 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) uu____609))
in (

let expected_k = (

let uu____618 = (

let uu____622 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____623 = (

let uu____625 = (FStar_Syntax_Syntax.mk_binder p)
in (

let uu____626 = (

let uu____628 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____629 = (

let uu____631 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____631)::[])
in (uu____628)::uu____629))
in (uu____625)::uu____626))
in (uu____622)::uu____623))
in (

let uu____632 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____618 uu____632)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (

let uu____639 = (

let uu____643 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____644 = (

let uu____646 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____646)::[])
in (uu____643)::uu____644))
in (

let uu____647 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____639 uu____647)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let uu____651 = (FStar_Syntax_Util.type_u ())
in (match (uu____651) with
| (t, uu____655) -> begin
(

let expected_k = (

let uu____659 = (

let uu____663 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____664 = (

let uu____666 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____667 = (

let uu____669 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____669)::[])
in (uu____666)::uu____667))
in (uu____663)::uu____664))
in (

let uu____670 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow uu____659 uu____670)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (

let uu____675 = (

let uu____676 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____676 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) uu____675))
in (

let b_wp_a = (

let uu____684 = (

let uu____688 = (

let uu____689 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder uu____689))
in (uu____688)::[])
in (

let uu____690 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____684 uu____690)))
in (

let expected_k = (

let uu____696 = (

let uu____700 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____701 = (

let uu____703 = (FStar_Syntax_Syntax.mk_binder b)
in (

let uu____704 = (

let uu____706 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (uu____706)::[])
in (uu____703)::uu____704))
in (uu____700)::uu____701))
in (

let uu____707 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____696 uu____707)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (

let uu____714 = (

let uu____718 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____719 = (

let uu____721 = (

let uu____722 = (

let uu____723 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____723 Prims.fst))
in (FStar_Syntax_Syntax.null_binder uu____722))
in (

let uu____728 = (

let uu____730 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____730)::[])
in (uu____721)::uu____728))
in (uu____718)::uu____719))
in (

let uu____731 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____714 uu____731)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (

let uu____738 = (

let uu____742 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____743 = (

let uu____745 = (

let uu____746 = (

let uu____747 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____747 Prims.fst))
in (FStar_Syntax_Syntax.null_binder uu____746))
in (

let uu____752 = (

let uu____754 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____754)::[])
in (uu____745)::uu____752))
in (uu____742)::uu____743))
in (

let uu____755 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____738 uu____755)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (

let uu____762 = (

let uu____766 = (FStar_Syntax_Syntax.mk_binder a)
in (uu____766)::[])
in (

let uu____767 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____762 uu____767)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let uu____771 = (FStar_Syntax_Util.type_u ())
in (match (uu____771) with
| (t, uu____775) -> begin
(

let expected_k = (

let uu____779 = (

let uu____783 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____784 = (

let uu____786 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____786)::[])
in (uu____783)::uu____784))
in (

let uu____787 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow uu____779 uu____787)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let uu____790 = (

let uu____796 = (

let uu____797 = (FStar_Syntax_Subst.compress ed.FStar_Syntax_Syntax.repr)
in uu____797.FStar_Syntax_Syntax.n)
in (match (uu____796) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((ed.FStar_Syntax_Syntax.repr), (ed.FStar_Syntax_Syntax.bind_repr), (ed.FStar_Syntax_Syntax.return_repr), (ed.FStar_Syntax_Syntax.actions))
end
| uu____806 -> begin
(

let repr = (

let uu____808 = (FStar_Syntax_Util.type_u ())
in (match (uu____808) with
| (t, uu____812) -> begin
(

let expected_k = (

let uu____816 = (

let uu____820 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____821 = (

let uu____823 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____823)::[])
in (uu____820)::uu____821))
in (

let uu____824 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow uu____816 uu____824)))
in (tc_check_trivial_guard env ed.FStar_Syntax_Syntax.repr expected_k))
end))
in (

let mk_repr' = (fun t wp -> (

let repr = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env repr)
in (

let uu____837 = (

let uu____840 = (

let uu____841 = (

let uu____851 = (

let uu____853 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____854 = (

let uu____856 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____856)::[])
in (uu____853)::uu____854))
in ((repr), (uu____851)))
in FStar_Syntax_Syntax.Tm_app (uu____841))
in (FStar_Syntax_Syntax.mk uu____840))
in (uu____837 None FStar_Range.dummyRange))))
in (

let mk_repr = (fun a wp -> (

let uu____875 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_repr' uu____875 wp)))
in (

let destruct_repr = (fun t -> (

let uu____886 = (

let uu____887 = (FStar_Syntax_Subst.compress t)
in uu____887.FStar_Syntax_Syntax.n)
in (match (uu____886) with
| FStar_Syntax_Syntax.Tm_app (uu____896, ((t, uu____898))::((wp, uu____900))::[]) -> begin
((t), (wp))
end
| uu____934 -> begin
(failwith "Unexpected repr type")
end)))
in (

let bind_repr = (

let r = (

let uu____943 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_0 FStar_Syntax_Syntax.Delta_constant None)
in (FStar_All.pipe_right uu____943 FStar_Syntax_Syntax.fv_to_tm))
in (

let uu____944 = (fresh_effect_signature ())
in (match (uu____944) with
| (b, wp_b) -> begin
(

let a_wp_b = (

let uu____958 = (

let uu____962 = (

let uu____963 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____963))
in (uu____962)::[])
in (

let uu____964 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____958 uu____964)))
in (

let wp_f = (FStar_Syntax_Syntax.gen_bv "wp_f" None wp_a)
in (

let wp_g = (FStar_Syntax_Syntax.gen_bv "wp_g" None a_wp_b)
in (

let x_a = (

let uu____970 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None uu____970))
in (

let wp_g_x = (

let uu____974 = (

let uu____975 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (

let uu____976 = (

let uu____977 = (

let uu____978 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____978))
in (uu____977)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____975 uu____976)))
in (uu____974 None FStar_Range.dummyRange))
in (

let res = (

let wp = (

let uu____989 = (

let uu____990 = (

let uu____991 = (FStar_TypeChecker_Env.inst_tscheme bind_wp)
in (FStar_All.pipe_right uu____991 Prims.snd))
in (

let uu____996 = (

let uu____997 = (

let uu____999 = (

let uu____1001 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____1002 = (

let uu____1004 = (FStar_Syntax_Syntax.bv_to_name b)
in (

let uu____1005 = (

let uu____1007 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (

let uu____1008 = (

let uu____1010 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (uu____1010)::[])
in (uu____1007)::uu____1008))
in (uu____1004)::uu____1005))
in (uu____1001)::uu____1002))
in (r)::uu____999)
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____997))
in (FStar_Syntax_Syntax.mk_Tm_app uu____990 uu____996)))
in (uu____989 None FStar_Range.dummyRange))
in (mk_repr b wp))
in (

let expected_k = (

let uu____1018 = (

let uu____1022 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1023 = (

let uu____1025 = (FStar_Syntax_Syntax.mk_binder b)
in (

let uu____1026 = (

let uu____1028 = (FStar_Syntax_Syntax.mk_binder wp_f)
in (

let uu____1029 = (

let uu____1031 = (

let uu____1032 = (

let uu____1033 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (mk_repr a uu____1033))
in (FStar_Syntax_Syntax.null_binder uu____1032))
in (

let uu____1034 = (

let uu____1036 = (FStar_Syntax_Syntax.mk_binder wp_g)
in (

let uu____1037 = (

let uu____1039 = (

let uu____1040 = (

let uu____1041 = (

let uu____1045 = (FStar_Syntax_Syntax.mk_binder x_a)
in (uu____1045)::[])
in (

let uu____1046 = (

let uu____1049 = (mk_repr b wp_g_x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____1049))
in (FStar_Syntax_Util.arrow uu____1041 uu____1046)))
in (FStar_Syntax_Syntax.null_binder uu____1040))
in (uu____1039)::[])
in (uu____1036)::uu____1037))
in (uu____1031)::uu____1034))
in (uu____1028)::uu____1029))
in (uu____1025)::uu____1026))
in (uu____1022)::uu____1023))
in (

let uu____1050 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow uu____1018 uu____1050)))
in (

let uu____1053 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (uu____1053) with
| (expected_k, uu____1058, uu____1059) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos)
in (

let env = (

let uu___88_1063 = env
in {FStar_TypeChecker_Env.solver = uu___88_1063.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___88_1063.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___88_1063.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___88_1063.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___88_1063.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___88_1063.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___88_1063.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___88_1063.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___88_1063.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___88_1063.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___88_1063.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___88_1063.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___88_1063.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___88_1063.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___88_1063.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___88_1063.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___88_1063.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___88_1063.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___88_1063.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___88_1063.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___88_1063.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___88_1063.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___88_1063.FStar_TypeChecker_Env.qname_and_index})
in (

let br = (check_and_gen' env ed.FStar_Syntax_Syntax.bind_repr expected_k)
in br)))
end)))))))))
end)))
in (

let return_repr = (

let x_a = (

let uu____1070 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None uu____1070))
in (

let res = (

let wp = (

let uu____1077 = (

let uu____1078 = (

let uu____1079 = (FStar_TypeChecker_Env.inst_tscheme return_wp)
in (FStar_All.pipe_right uu____1079 Prims.snd))
in (

let uu____1084 = (

let uu____1085 = (

let uu____1087 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____1088 = (

let uu____1090 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (uu____1090)::[])
in (uu____1087)::uu____1088))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1085))
in (FStar_Syntax_Syntax.mk_Tm_app uu____1078 uu____1084)))
in (uu____1077 None FStar_Range.dummyRange))
in (mk_repr a wp))
in (

let expected_k = (

let uu____1098 = (

let uu____1102 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1103 = (

let uu____1105 = (FStar_Syntax_Syntax.mk_binder x_a)
in (uu____1105)::[])
in (uu____1102)::uu____1103))
in (

let uu____1106 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow uu____1098 uu____1106)))
in (

let uu____1109 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (uu____1109) with
| (expected_k, uu____1117, uu____1118) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos)
in (

let uu____1121 = (check_and_gen' env ed.FStar_Syntax_Syntax.return_repr expected_k)
in (match (uu____1121) with
| (univs, repr) -> begin
(match (univs) with
| [] -> begin
(([]), (repr))
end
| uu____1133 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected universe-polymorphic return for effect"), (repr.FStar_Syntax_Syntax.pos)))))
end)
end)))
end)))))
in (

let actions = (

let check_action = (fun act -> (

let uu____1144 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env act.FStar_Syntax_Syntax.action_typ)
in (match (uu____1144) with
| (act_typ, uu____1149, g_t) -> begin
(

let env' = (FStar_TypeChecker_Env.set_expected_typ env act_typ)
in ((

let uu____1153 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____1153) with
| true -> begin
(

let uu____1154 = (FStar_Syntax_Print.term_to_string act.FStar_Syntax_Syntax.action_defn)
in (

let uu____1155 = (FStar_Syntax_Print.term_to_string act_typ)
in (FStar_Util.print3 "Checking action %s:\n[definition]: %s\n[cps\'d type]: %s\n" (FStar_Ident.text_of_lid act.FStar_Syntax_Syntax.action_name) uu____1154 uu____1155)))
end
| uu____1156 -> begin
()
end));
(

let uu____1157 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' act.FStar_Syntax_Syntax.action_defn)
in (match (uu____1157) with
| (act_defn, uu____1162, g_a) -> begin
(

let act_defn = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env act_defn)
in (

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
in (

let uu____1166 = (

let act_typ = (FStar_Syntax_Subst.compress act_typ)
in (match (act_typ.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____1184 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____1184) with
| (bs, uu____1190) -> begin
(

let res = (mk_repr' FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun)
in (

let k = (

let uu____1197 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs uu____1197))
in (

let uu____1200 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env k)
in (match (uu____1200) with
| (k, uu____1207, g) -> begin
((k), (g))
end))))
end))
end
| uu____1209 -> begin
(

let uu____1210 = (

let uu____1211 = (

let uu____1214 = (

let uu____1215 = (FStar_Syntax_Print.term_to_string act_typ)
in (

let uu____1216 = (FStar_Syntax_Print.tag_of_term act_typ)
in (FStar_Util.format2 "Actions must have function types (not: %s, a.k.a. %s)" uu____1215 uu____1216)))
in ((uu____1214), (act_defn.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____1211))
in (Prims.raise uu____1210))
end))
in (match (uu____1166) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env act_typ expected_k)
in ((

let uu____1223 = (

let uu____1224 = (

let uu____1225 = (FStar_TypeChecker_Rel.conj_guard g_t g)
in (FStar_TypeChecker_Rel.conj_guard g_k uu____1225))
in (FStar_TypeChecker_Rel.conj_guard g_a uu____1224))
in (FStar_TypeChecker_Rel.force_trivial_guard env uu____1223));
(

let act_typ = (

let uu____1229 = (

let uu____1230 = (FStar_Syntax_Subst.compress expected_k)
in uu____1230.FStar_Syntax_Syntax.n)
in (match (uu____1229) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____1247 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____1247) with
| (bs, c) -> begin
(

let uu____1254 = (destruct_repr (FStar_Syntax_Util.comp_result c))
in (match (uu____1254) with
| (a, wp) -> begin
(

let c = (

let uu____1274 = (

let uu____1275 = (env.FStar_TypeChecker_Env.universe_of env a)
in (uu____1275)::[])
in (

let uu____1276 = (

let uu____1282 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____1282)::[])
in {FStar_Syntax_Syntax.comp_univs = uu____1274; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a; FStar_Syntax_Syntax.effect_args = uu____1276; FStar_Syntax_Syntax.flags = []}))
in (

let uu____1283 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Util.arrow bs uu____1283)))
end))
end))
end
| uu____1286 -> begin
(failwith "")
end))
in (

let uu____1289 = (FStar_TypeChecker_Util.generalize_universes env act_defn)
in (match (uu____1289) with
| (univs, act_defn) -> begin
(

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
in (

let uu___89_1295 = act
in {FStar_Syntax_Syntax.action_name = uu___89_1295.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___89_1295.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = act_defn; FStar_Syntax_Syntax.action_typ = act_typ}))
end)));
))
end))))
end));
))
end)))
in (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.map check_action)))
in ((repr), (bind_repr), (return_repr), (actions)))))))))
end))
in (match (uu____790) with
| (repr, bind_repr, return_repr, actions) -> begin
(

let t = (

let uu____1311 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders uu____1311))
in (

let uu____1314 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (uu____1314) with
| (univs, t) -> begin
(

let signature = (

let uu____1320 = (

let uu____1323 = (

let uu____1324 = (FStar_Syntax_Subst.compress t)
in uu____1324.FStar_Syntax_Syntax.n)
in ((effect_params), (uu____1323)))
in (match (uu____1320) with
| ([], uu____1327) -> begin
t
end
| (uu____1333, FStar_Syntax_Syntax.Tm_arrow (uu____1334, c)) -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____1346 -> begin
(failwith "Impossible")
end))
in (

let close = (fun n ts -> (

let ts = (

let uu____1357 = (FStar_Syntax_Subst.close_tscheme effect_params ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs uu____1357))
in (

let m = (FStar_List.length (Prims.fst ts))
in ((

let uu____1362 = (((n >= (Prims.parse_int "0")) && (

let uu____1363 = (FStar_Syntax_Util.is_unknown (Prims.snd ts))
in (not (uu____1363)))) && (m <> n))
in (match (uu____1362) with
| true -> begin
(

let error = (match ((m < n)) with
| true -> begin
"not universe-polymorphic enough"
end
| uu____1371 -> begin
"too universe-polymorphic"
end)
in (

let uu____1372 = (

let uu____1373 = (FStar_Util.string_of_int n)
in (

let uu____1374 = (FStar_Syntax_Print.tscheme_to_string ts)
in (FStar_Util.format3 "The effect combinator is %s (n=%s) (%s)" error uu____1373 uu____1374)))
in (failwith uu____1372)))
end
| uu____1375 -> begin
()
end));
ts;
))))
in (

let close_action = (fun act -> (

let uu____1380 = (close (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_defn)))
in (match (uu____1380) with
| (univs, defn) -> begin
(

let uu____1385 = (close (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_typ)))
in (match (uu____1385) with
| (univs', typ) -> begin
(

let uu___90_1391 = act
in {FStar_Syntax_Syntax.action_name = uu___90_1391.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___90_1391.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = defn; FStar_Syntax_Syntax.action_typ = typ})
end))
end)))
in (

let nunivs = (FStar_List.length univs)
in (

let ed = (

let uu___91_1396 = ed
in (

let uu____1397 = (close (Prims.parse_int "0") return_wp)
in (

let uu____1398 = (close (Prims.parse_int "1") bind_wp)
in (

let uu____1399 = (close (Prims.parse_int "0") if_then_else)
in (

let uu____1400 = (close (Prims.parse_int "0") ite_wp)
in (

let uu____1401 = (close (Prims.parse_int "0") stronger)
in (

let uu____1402 = (close (Prims.parse_int "1") close_wp)
in (

let uu____1403 = (close (Prims.parse_int "0") assert_p)
in (

let uu____1404 = (close (Prims.parse_int "0") assume_p)
in (

let uu____1405 = (close (Prims.parse_int "0") null_wp)
in (

let uu____1406 = (close (Prims.parse_int "0") trivial_wp)
in (

let uu____1407 = (

let uu____1408 = (close (Prims.parse_int "0") (([]), (repr)))
in (Prims.snd uu____1408))
in (

let uu____1414 = (close (Prims.parse_int "0") return_repr)
in (

let uu____1415 = (close (Prims.parse_int "1") bind_repr)
in (

let uu____1416 = (FStar_List.map close_action actions)
in {FStar_Syntax_Syntax.qualifiers = uu___91_1396.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___91_1396.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___91_1396.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = uu____1397; FStar_Syntax_Syntax.bind_wp = uu____1398; FStar_Syntax_Syntax.if_then_else = uu____1399; FStar_Syntax_Syntax.ite_wp = uu____1400; FStar_Syntax_Syntax.stronger = uu____1401; FStar_Syntax_Syntax.close_wp = uu____1402; FStar_Syntax_Syntax.assert_p = uu____1403; FStar_Syntax_Syntax.assume_p = uu____1404; FStar_Syntax_Syntax.null_wp = uu____1405; FStar_Syntax_Syntax.trivial = uu____1406; FStar_Syntax_Syntax.repr = uu____1407; FStar_Syntax_Syntax.return_repr = uu____1414; FStar_Syntax_Syntax.bind_repr = uu____1415; FStar_Syntax_Syntax.actions = uu____1416})))))))))))))))
in ((

let uu____1419 = ((FStar_TypeChecker_Env.debug env FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ED"))))
in (match (uu____1419) with
| true -> begin
(

let uu____1420 = (FStar_Syntax_Print.eff_decl_to_string false ed)
in (FStar_Util.print_string uu____1420))
end
| uu____1421 -> begin
()
end));
ed;
))))))
end)))
end)))))))))))));
)))
end)))))
end))
end))
end)))
and cps_and_elaborate : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.sigelt Prims.option) = (fun env ed -> (

let uu____1424 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____1424) with
| (effect_binders_un, signature_un) -> begin
(

let uu____1434 = (FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un)
in (match (uu____1434) with
| (effect_binders, env, uu____1445) -> begin
(

let uu____1446 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (uu____1446) with
| (signature, uu____1455) -> begin
(

let effect_binders = (FStar_List.map (fun uu____1464 -> (match (uu____1464) with
| (bv, qual) -> begin
(

let uu____1471 = (

let uu___92_1472 = bv
in (

let uu____1473 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___92_1472.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___92_1472.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1473}))
in ((uu____1471), (qual)))
end)) effect_binders)
in (

let uu____1476 = (

let uu____1481 = (

let uu____1482 = (FStar_Syntax_Subst.compress signature_un)
in uu____1482.FStar_Syntax_Syntax.n)
in (match (uu____1481) with
| FStar_Syntax_Syntax.Tm_arrow (((a, uu____1490))::[], effect_marker) -> begin
((a), (effect_marker))
end
| uu____1505 -> begin
(failwith "bad shape for effect-for-free signature")
end))
in (match (uu____1476) with
| (a, effect_marker) -> begin
(

let a = (

let uu____1522 = (FStar_Syntax_Syntax.is_null_bv a)
in (match (uu____1522) with
| true -> begin
(

let uu____1523 = (

let uu____1525 = (FStar_Syntax_Syntax.range_of_bv a)
in Some (uu____1525))
in (FStar_Syntax_Syntax.gen_bv "a" uu____1523 a.FStar_Syntax_Syntax.sort))
end
| uu____1526 -> begin
a
end))
in (

let open_and_check = (fun t -> (

let subst = (FStar_Syntax_Subst.opening_of_binders effect_binders)
in (

let t = (FStar_Syntax_Subst.subst subst t)
in (

let uu____1535 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (uu____1535) with
| (t, comp, uu____1543) -> begin
((t), (comp))
end)))))
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None signature.FStar_Syntax_Syntax.pos))
in (

let uu____1554 = (open_and_check ed.FStar_Syntax_Syntax.repr)
in (match (uu____1554) with
| (repr, _comp) -> begin
((

let uu____1565 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____1565) with
| true -> begin
(

let uu____1566 = (FStar_Syntax_Print.term_to_string repr)
in (FStar_Util.print1 "Representation is: %s\n" uu____1566))
end
| uu____1567 -> begin
()
end));
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange))
in (

let wp_type = (FStar_TypeChecker_DMFF.star_type dmff_env repr)
in (

let wp_type = (recheck_debug "*" env wp_type)
in (

let wp_a = (

let uu____1572 = (

let uu____1573 = (

let uu____1574 = (

let uu____1584 = (

let uu____1588 = (

let uu____1591 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____1592 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____1591), (uu____1592))))
in (uu____1588)::[])
in ((wp_type), (uu____1584)))
in FStar_Syntax_Syntax.Tm_app (uu____1574))
in (mk uu____1573))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env uu____1572))
in (

let effect_signature = (

let binders = (

let uu____1607 = (

let uu____1610 = (FStar_Syntax_Syntax.as_implicit false)
in ((a), (uu____1610)))
in (

let uu____1611 = (

let uu____1615 = (

let uu____1616 = (FStar_Syntax_Syntax.gen_bv "dijkstra_wp" None wp_a)
in (FStar_All.pipe_right uu____1616 FStar_Syntax_Syntax.mk_binder))
in (uu____1615)::[])
in (uu____1607)::uu____1611))
in (

let binders = (FStar_Syntax_Subst.close_binders binders)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (effect_marker)))))))
in (

let effect_signature = (recheck_debug "turned into the effect signature" env effect_signature)
in (

let sigelts = (FStar_Util.mk_ref [])
in (

let mk_lid = (fun name -> (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" name))) FStar_Range.dummyRange))
in (

let elaborate_and_star = (fun dmff_env item -> (

let uu____1649 = item
in (match (uu____1649) with
| (u_item, item) -> begin
(

let uu____1661 = (open_and_check item)
in (match (uu____1661) with
| (item, item_comp) -> begin
((

let uu____1671 = (

let uu____1672 = (FStar_Syntax_Util.is_total_lcomp item_comp)
in (not (uu____1672)))
in (match (uu____1671) with
| true -> begin
(

let uu____1673 = (

let uu____1674 = (

let uu____1675 = (FStar_Syntax_Print.term_to_string item)
in (

let uu____1676 = (FStar_Syntax_Print.lcomp_to_string item_comp)
in (FStar_Util.format2 "Computation for [%s] is not total : %s !" uu____1675 uu____1676)))
in FStar_Errors.Err (uu____1674))
in (Prims.raise uu____1673))
end
| uu____1677 -> begin
()
end));
(

let uu____1678 = (FStar_TypeChecker_DMFF.star_expr dmff_env item)
in (match (uu____1678) with
| (item_t, item_wp, item_elab) -> begin
(

let item_wp = (recheck_debug "*" env item_wp)
in (

let item_elab = (recheck_debug "_" env item_elab)
in ((dmff_env), (item_t), (item_wp), (item_elab))))
end));
)
end))
end)))
in (

let uu____1691 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.bind_repr)
in (match (uu____1691) with
| (dmff_env, uu____1702, bind_wp, bind_elab) -> begin
(

let uu____1705 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.return_repr)
in (match (uu____1705) with
| (dmff_env, uu____1716, return_wp, return_elab) -> begin
(

let lift_from_pure_wp = (

let uu____1720 = (

let uu____1721 = (FStar_Syntax_Subst.compress return_wp)
in uu____1721.FStar_Syntax_Syntax.n)
in (match (uu____1720) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(

let uu____1759 = (

let uu____1767 = (

let uu____1770 = (FStar_Syntax_Util.abs bs body None)
in (FStar_Syntax_Subst.open_term ((b1)::(b2)::[]) uu____1770))
in (match (uu____1767) with
| ((b1)::(b2)::[], body) -> begin
((b1), (b2), (body))
end
| uu____1809 -> begin
(failwith "Impossible : open_term not preserving binders arity")
end))
in (match (uu____1759) with
| (b1, b2, body) -> begin
(

let env0 = (

let uu____1831 = (FStar_TypeChecker_DMFF.get_env dmff_env)
in (FStar_TypeChecker_Env.push_binders uu____1831 ((b1)::(b2)::[])))
in (

let wp_b1 = (

let uu____1839 = (

let uu____1840 = (

let uu____1841 = (

let uu____1851 = (

let uu____1855 = (

let uu____1858 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b1))
in (

let uu____1859 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____1858), (uu____1859))))
in (uu____1855)::[])
in ((wp_type), (uu____1851)))
in FStar_Syntax_Syntax.Tm_app (uu____1841))
in (mk uu____1840))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env0 uu____1839))
in (

let uu____1867 = (

let uu____1877 = (

let uu____1878 = (FStar_Syntax_Util.unascribe wp_b1)
in (FStar_TypeChecker_Normalize.eta_expand_with_type body uu____1878))
in (FStar_All.pipe_left FStar_Syntax_Util.abs_formals uu____1877))
in (match (uu____1867) with
| (bs, body, what') -> begin
(

let t2 = (Prims.fst b2).FStar_Syntax_Syntax.sort
in (

let pure_wp_type = (FStar_TypeChecker_DMFF.double_star t2)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None pure_wp_type)
in (

let body = (

let uu____1911 = (

let uu____1912 = (FStar_Syntax_Syntax.bv_to_name wp)
in (

let uu____1913 = (

let uu____1914 = (

let uu____1918 = (FStar_Syntax_Util.abs ((b2)::[]) body what')
in ((uu____1918), (None)))
in (uu____1914)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____1912 uu____1913)))
in (uu____1911 None FStar_Range.dummyRange))
in (

let uu____1934 = (

let uu____1938 = (

let uu____1942 = (FStar_Syntax_Syntax.mk_binder wp)
in (uu____1942)::[])
in (b1)::uu____1938)
in (

let uu____1945 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs uu____1934 uu____1945 (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_GTot_lid), ([]))))))))))))
end))))
end))
end
| uu____1955 -> begin
(failwith "unexpected shape for return")
end))
in (

let return_wp = (

let uu____1957 = (

let uu____1958 = (FStar_Syntax_Subst.compress return_wp)
in uu____1958.FStar_Syntax_Syntax.n)
in (match (uu____1957) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(

let uu____1996 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs ((b1)::(b2)::[]) uu____1996 (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_GTot_lid), ([])))))))
end
| uu____2012 -> begin
(failwith "unexpected shape for return")
end))
in (

let bind_wp = (

let uu____2014 = (

let uu____2015 = (FStar_Syntax_Subst.compress bind_wp)
in uu____2015.FStar_Syntax_Syntax.n)
in (match (uu____2014) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let r = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (

let uu____2044 = (

let uu____2048 = (

let uu____2050 = (

let uu____2051 = (mk (FStar_Syntax_Syntax.Tm_fvar (r)))
in (FStar_Syntax_Syntax.null_binder uu____2051))
in (uu____2050)::[])
in (FStar_List.append uu____2048 binders))
in (FStar_Syntax_Util.abs uu____2044 body what)))
end
| uu____2052 -> begin
(failwith "unexpected shape for bind")
end))
in (

let apply_close = (fun t -> (match (((FStar_List.length effect_binders) = (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____2069 -> begin
(

let uu____2070 = (

let uu____2071 = (

let uu____2072 = (

let uu____2082 = (

let uu____2083 = (FStar_Syntax_Util.args_of_binders effect_binders)
in (Prims.snd uu____2083))
in ((t), (uu____2082)))
in FStar_Syntax_Syntax.Tm_app (uu____2072))
in (mk uu____2071))
in (FStar_Syntax_Subst.close effect_binders uu____2070))
end))
in (

let register = (fun name item -> (

let uu____2095 = (

let uu____2098 = (mk_lid name)
in (

let uu____2099 = (FStar_Syntax_Util.abs effect_binders item None)
in (FStar_TypeChecker_Util.mk_toplevel_definition env uu____2098 uu____2099)))
in (match (uu____2095) with
| (sigelt, fv) -> begin
((

let uu____2108 = (

let uu____2110 = (FStar_ST.read sigelts)
in (sigelt)::uu____2110)
in (FStar_ST.write sigelts uu____2108));
fv;
)
end)))
in (

let lift_from_pure_wp = (register "lift_from_pure" lift_from_pure_wp)
in (

let return_wp = (register "return_wp" return_wp)
in ((

let uu____2121 = (

let uu____2123 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true")), (FStar_Range.dummyRange))))::uu____2123)
in (FStar_ST.write sigelts uu____2121));
(

let return_elab = (register "return_elab" return_elab)
in ((

let uu____2133 = (

let uu____2135 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false")), (FStar_Range.dummyRange))))::uu____2135)
in (FStar_ST.write sigelts uu____2133));
(

let bind_wp = (register "bind_wp" bind_wp)
in ((

let uu____2145 = (

let uu____2147 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true")), (FStar_Range.dummyRange))))::uu____2147)
in (FStar_ST.write sigelts uu____2145));
(

let bind_elab = (register "bind_elab" bind_elab)
in ((

let uu____2157 = (

let uu____2159 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false")), (FStar_Range.dummyRange))))::uu____2159)
in (FStar_ST.write sigelts uu____2157));
(

let uu____2167 = (FStar_List.fold_left (fun uu____2174 action -> (match (uu____2174) with
| (dmff_env, actions) -> begin
(

let uu____2186 = (elaborate_and_star dmff_env ((action.FStar_Syntax_Syntax.action_univs), (action.FStar_Syntax_Syntax.action_defn)))
in (match (uu____2186) with
| (dmff_env, action_t, action_wp, action_elab) -> begin
(

let name = action.FStar_Syntax_Syntax.action_name.FStar_Ident.ident.FStar_Ident.idText
in (

let action_typ_with_wp = (FStar_TypeChecker_DMFF.trans_F dmff_env action_t action_wp)
in (

let action_elab = (register (Prims.strcat name "_elab") action_elab)
in (

let action_typ_with_wp = (register (Prims.strcat name "_complete_type") action_typ_with_wp)
in (

let uu____2202 = (

let uu____2204 = (

let uu___93_2205 = action
in (

let uu____2206 = (apply_close action_elab)
in (

let uu____2207 = (apply_close action_typ_with_wp)
in {FStar_Syntax_Syntax.action_name = uu___93_2205.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___93_2205.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___93_2205.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = uu____2206; FStar_Syntax_Syntax.action_typ = uu____2207})))
in (uu____2204)::actions)
in ((dmff_env), (uu____2202)))))))
end))
end)) ((dmff_env), ([])) ed.FStar_Syntax_Syntax.actions)
in (match (uu____2167) with
| (dmff_env, actions) -> begin
(

let actions = (FStar_List.rev actions)
in (

let repr = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp_a" None wp_a)
in (

let binders = (

let uu____2225 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____2226 = (

let uu____2228 = (FStar_Syntax_Syntax.mk_binder wp)
in (uu____2228)::[])
in (uu____2225)::uu____2226))
in (

let uu____2229 = (

let uu____2230 = (

let uu____2231 = (

let uu____2232 = (

let uu____2242 = (

let uu____2246 = (

let uu____2249 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____2250 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____2249), (uu____2250))))
in (uu____2246)::[])
in ((repr), (uu____2242)))
in FStar_Syntax_Syntax.Tm_app (uu____2232))
in (mk uu____2231))
in (

let uu____2258 = (FStar_Syntax_Syntax.bv_to_name wp)
in (FStar_TypeChecker_DMFF.trans_F dmff_env uu____2230 uu____2258)))
in (FStar_Syntax_Util.abs binders uu____2229 None))))
in (

let repr = (recheck_debug "FC" env repr)
in (

let repr = (register "repr" repr)
in (

let uu____2266 = (

let uu____2271 = (

let uu____2272 = (

let uu____2275 = (FStar_Syntax_Subst.compress wp_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____2275))
in uu____2272.FStar_Syntax_Syntax.n)
in (match (uu____2271) with
| FStar_Syntax_Syntax.Tm_abs ((type_param)::effect_param, arrow, uu____2283) -> begin
(

let uu____2310 = (

let uu____2319 = (FStar_Syntax_Subst.open_term ((type_param)::effect_param) arrow)
in (match (uu____2319) with
| ((b)::bs, body) -> begin
((b), (bs), (body))
end
| uu____2350 -> begin
(failwith "Impossible : open_term nt preserving binders arity")
end))
in (match (uu____2310) with
| (type_param, effect_param, arrow) -> begin
(

let uu____2378 = (

let uu____2379 = (

let uu____2382 = (FStar_Syntax_Subst.compress arrow)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____2382))
in uu____2379.FStar_Syntax_Syntax.n)
in (match (uu____2378) with
| FStar_Syntax_Syntax.Tm_arrow (wp_binders, c) -> begin
(

let uu____2399 = (FStar_Syntax_Subst.open_comp wp_binders c)
in (match (uu____2399) with
| (wp_binders, c) -> begin
(

let uu____2408 = (FStar_List.partition (fun uu____2419 -> (match (uu____2419) with
| (bv, uu____2423) -> begin
(

let uu____2424 = (

let uu____2425 = (FStar_Syntax_Free.names bv.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____2425 (FStar_Util.set_mem (Prims.fst type_param))))
in (FStar_All.pipe_right uu____2424 Prims.op_Negation))
end)) wp_binders)
in (match (uu____2408) with
| (pre_args, post_args) -> begin
(

let post = (match (post_args) with
| (post)::[] -> begin
post
end
| uu____2458 -> begin
(

let uu____2462 = (

let uu____2463 = (FStar_Syntax_Print.term_to_string arrow)
in (FStar_Util.format1 "Impossible: multiple post candidates %s" uu____2463))
in (failwith uu____2462))
end)
in (

let uu____2466 = (FStar_Syntax_Util.arrow pre_args c)
in (

let uu____2469 = (FStar_Syntax_Util.abs ((type_param)::effect_param) (Prims.fst post).FStar_Syntax_Syntax.sort None)
in ((uu____2466), (uu____2469)))))
end))
end))
end
| uu____2479 -> begin
(

let uu____2480 = (

let uu____2481 = (FStar_Syntax_Print.term_to_string arrow)
in (FStar_Util.format1 "Impossible: pre/post arrow %s" uu____2481))
in (failwith uu____2480))
end))
end))
end
| uu____2486 -> begin
(

let uu____2487 = (

let uu____2488 = (FStar_Syntax_Print.term_to_string wp_type)
in (FStar_Util.format1 "Impossible: pre/post abs %s" uu____2488))
in (failwith uu____2487))
end))
in (match (uu____2266) with
| (pre, post) -> begin
((

let uu____2505 = (register "pre" pre)
in ());
(

let uu____2507 = (register "post" post)
in ());
(

let uu____2509 = (register "wp" wp_type)
in ());
(

let ed = (

let uu___94_2511 = ed
in (

let uu____2512 = (FStar_Syntax_Subst.close_binders effect_binders)
in (

let uu____2513 = (FStar_Syntax_Subst.close effect_binders effect_signature)
in (

let uu____2514 = (

let uu____2515 = (apply_close return_wp)
in (([]), (uu____2515)))
in (

let uu____2521 = (

let uu____2522 = (apply_close bind_wp)
in (([]), (uu____2522)))
in (

let uu____2528 = (apply_close repr)
in (

let uu____2529 = (

let uu____2530 = (apply_close return_elab)
in (([]), (uu____2530)))
in (

let uu____2536 = (

let uu____2537 = (apply_close bind_elab)
in (([]), (uu____2537)))
in {FStar_Syntax_Syntax.qualifiers = uu___94_2511.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___94_2511.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___94_2511.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___94_2511.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu____2512; FStar_Syntax_Syntax.signature = uu____2513; FStar_Syntax_Syntax.ret_wp = uu____2514; FStar_Syntax_Syntax.bind_wp = uu____2521; FStar_Syntax_Syntax.if_then_else = uu___94_2511.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = uu___94_2511.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = uu___94_2511.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = uu___94_2511.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = uu___94_2511.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = uu___94_2511.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = uu___94_2511.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = uu___94_2511.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = uu____2528; FStar_Syntax_Syntax.return_repr = uu____2529; FStar_Syntax_Syntax.bind_repr = uu____2536; FStar_Syntax_Syntax.actions = actions}))))))))
in (

let uu____2543 = (FStar_TypeChecker_DMFF.gen_wps_for_free env effect_binders a wp_a ed)
in (match (uu____2543) with
| (sigelts', ed) -> begin
((

let uu____2554 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____2554) with
| true -> begin
(

let uu____2555 = (FStar_Syntax_Print.eff_decl_to_string true ed)
in (FStar_Util.print_string uu____2555))
end
| uu____2556 -> begin
()
end));
(

let lift_from_pure_opt = (match (((FStar_List.length effect_binders) = (Prims.parse_int "0"))) with
| true -> begin
(

let lift_from_pure = (

let uu____2565 = (

let uu____2567 = (

let uu____2573 = (apply_close lift_from_pure_wp)
in (([]), (uu____2573)))
in Some (uu____2567))
in {FStar_Syntax_Syntax.source = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.target = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.lift_wp = uu____2565; FStar_Syntax_Syntax.lift = None})
in Some (FStar_Syntax_Syntax.Sig_sub_effect (((lift_from_pure), (FStar_Range.dummyRange)))))
end
| uu____2584 -> begin
None
end)
in (

let uu____2585 = (

let uu____2587 = (

let uu____2589 = (FStar_ST.read sigelts)
in (FStar_List.rev uu____2589))
in (FStar_List.append uu____2587 sigelts'))
in ((uu____2585), (ed), (lift_from_pure_opt))));
)
end)));
)
end))))))
end));
));
));
));
))))))))
end))
end)))))))))));
)
end)))))
end)))
end))
end))
end)))
and tc_lex_t : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (match (ses) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, uu____2612, uu____2613, [], r))::(FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, _0_28, [], uu____2618, r1))::(FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, _0_29, [], uu____2623, r2))::[] when (((_0_28 = (Prims.parse_int "0")) && (_0_29 = (Prims.parse_int "0"))) && (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid))) -> begin
(

let u = (FStar_Syntax_Syntax.new_univ_name (Some (r)))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) None r)
in (

let t = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t)
in (

let tc = FStar_Syntax_Syntax.Sig_inductive_typ (((lex_t), ((u)::[]), ([]), (t), ([]), ((FStar_Syntax_Const.lextop_lid)::(FStar_Syntax_Const.lexcons_lid)::[]), ([]), (r)))
in (

let utop = (FStar_Syntax_Syntax.new_univ_name (Some (r1)))
in (

let lex_top_t = (

let uu____2667 = (

let uu____2670 = (

let uu____2671 = (

let uu____2676 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1) FStar_Syntax_Syntax.Delta_constant None)
in ((uu____2676), ((FStar_Syntax_Syntax.U_name (utop))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____2671))
in (FStar_Syntax_Syntax.mk uu____2670))
in (uu____2667 None r1))
in (

let lex_top_t = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (

let dc_lextop = FStar_Syntax_Syntax.Sig_datacon (((lex_top), ((utop)::[]), (lex_top_t), (FStar_Syntax_Const.lex_t_lid), ((Prims.parse_int "0")), ([]), ([]), (r1)))
in (

let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (

let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (

let lex_cons_t = (

let a = (

let uu____2697 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) uu____2697))
in (

let hd = (

let uu____2703 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) uu____2703))
in (

let tl = (

let uu____2705 = (

let uu____2706 = (

let uu____2709 = (

let uu____2710 = (

let uu____2715 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2) FStar_Syntax_Syntax.Delta_constant None)
in ((uu____2715), ((FStar_Syntax_Syntax.U_name (ucons2))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____2710))
in (FStar_Syntax_Syntax.mk uu____2709))
in (uu____2706 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) uu____2705))
in (

let res = (

let uu____2728 = (

let uu____2731 = (

let uu____2732 = (

let uu____2737 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2) FStar_Syntax_Syntax.Delta_constant None)
in ((uu____2737), ((FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____2732))
in (FStar_Syntax_Syntax.mk uu____2731))
in (uu____2728 None r2))
in (

let uu____2747 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow ((((a), (Some (FStar_Syntax_Syntax.imp_tag))))::(((hd), (None)))::(((tl), (None)))::[]) uu____2747))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon (((lex_cons), ((ucons1)::(ucons2)::[]), (lex_cons_t), (FStar_Syntax_Const.lex_t_lid), ((Prims.parse_int "0")), ([]), ([]), (r2)))
in (

let uu____2770 = (

let uu____2778 = (FStar_TypeChecker_Env.get_range env)
in (((tc)::(dc_lextop)::(dc_lexcons)::[]), ([]), (lids), (uu____2778)))
in FStar_Syntax_Syntax.Sig_bundle (uu____2770)))))))))))))))
end
| uu____2782 -> begin
(

let uu____2784 = (

let uu____2785 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle (((ses), ([]), (lids), (FStar_Range.dummyRange)))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" uu____2785))
in (failwith uu____2784))
end))
and tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let uu____2796 = (FStar_Syntax_Util.type_u ())
in (match (uu____2796) with
| (k, uu____2800) -> begin
(

let phi = (

let uu____2802 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right uu____2802 (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env)))
in ((FStar_TypeChecker_Util.check_uvars r phi);
FStar_Syntax_Syntax.Sig_assume (((lid), (phi), (quals), (r)));
))
end))))
and tc_inductive : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env ses quals lids -> (

let env0 = env
in (

let uu____2813 = (FStar_TypeChecker_TcInductive.check_inductive_well_typedness env ses quals lids)
in (match (uu____2813) with
| (sig_bndle, tcs, datas) -> begin
(

let data_ops_ses = (

let uu____2832 = (FStar_List.map (FStar_TypeChecker_Util.mk_data_operations quals env tcs) datas)
in (FStar_All.pipe_right uu____2832 FStar_List.flatten))
in ((

let uu____2840 = ((FStar_Options.no_positivity ()) || (FStar_Options.lax ()))
in (match (uu____2840) with
| true -> begin
()
end
| uu____2841 -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (FStar_List.iter (fun ty -> (

let b = (FStar_TypeChecker_TcInductive.check_positivity ty env)
in (match ((not (b))) with
| true -> begin
(

let uu____2846 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____2852, uu____2853, uu____2854, uu____2855, uu____2856, uu____2857, r) -> begin
((lid), (r))
end
| uu____2865 -> begin
(failwith "Impossible!")
end)
in (match (uu____2846) with
| (lid, r) -> begin
(FStar_Errors.report r (Prims.strcat "Inductive type " (Prims.strcat lid.FStar_Ident.str " does not satisfy the positivity condition")))
end))
end
| uu____2870 -> begin
()
end))) tcs))
end));
(

let skip_prims_type = (fun uu____2874 -> (

let lid = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____2878, uu____2879, uu____2880, uu____2881, uu____2882, uu____2883, uu____2884) -> begin
lid
end
| uu____2891 -> begin
(failwith "Impossible")
end))
in (

let types_to_skip = ("c_False")::("c_True")::("equals")::("h_equals")::("c_and")::("c_or")::[]
in (FStar_List.existsb (fun s -> (s = lid.FStar_Ident.ident.FStar_Ident.idText)) types_to_skip))))
in (

let is_noeq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Noeq)) quals)
in (

let uu____2897 = ((((FStar_List.length tcs) = (Prims.parse_int "0")) || ((FStar_Ident.lid_equals env.FStar_TypeChecker_Env.curmodule FStar_Syntax_Const.prims_lid) && (skip_prims_type ()))) || is_noeq)
in (match (uu____2897) with
| true -> begin
(((sig_bndle)::[]), (data_ops_ses))
end
| uu____2906 -> begin
(

let is_unopteq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Unopteq)) quals)
in (

let ses = (match (is_unopteq) with
| true -> begin
(FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme sig_bndle tcs datas env0 tc_assume)
end
| uu____2912 -> begin
(FStar_TypeChecker_TcInductive.optimized_haseq_scheme sig_bndle tcs datas env0 tc_assume)
end)
in (

let uu____2913 = (

let uu____2915 = (

let uu____2916 = (

let uu____2924 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (uu____2924)))
in FStar_Syntax_Syntax.Sig_bundle (uu____2916))
in (uu____2915)::ses)
in ((uu____2913), (data_ops_ses)))))
end))));
))
end))))
and tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env se -> (

let env = (set_hint_correlator env se)
in ((FStar_TypeChecker_Util.check_sigelt_quals env se);
(match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let se = (tc_lex_t env ses quals lids)
in (

let uu____2964 = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (uu____2964), ([])))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let uu____2978 = (tc_inductive env ses quals lids)
in (match (uu____2978) with
| (ses, projectors_ses) -> begin
(

let env = (FStar_List.fold_left (fun env' se -> (FStar_TypeChecker_Env.push_sigelt env' se)) env ses)
in ((ses), (env), (projectors_ses)))
end)))
end
| FStar_Syntax_Syntax.Sig_pragma (p, r) -> begin
(

let set_options = (fun t s -> (

let uu____3008 = (FStar_Options.set_options t s)
in (match (uu____3008) with
| FStar_Getopt.Success -> begin
()
end
| FStar_Getopt.Help -> begin
(Prims.raise (FStar_Errors.Error ((("Failed to process pragma: use \'fstar --help\' to see which options are available"), (r)))))
end
| FStar_Getopt.Error (s) -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Failed to process pragma: " s)), (r)))))
end)))
in (match (p) with
| FStar_Syntax_Syntax.LightOff -> begin
((match ((p = FStar_Syntax_Syntax.LightOff)) with
| true -> begin
(FStar_Options.set_ml_ish ())
end
| uu____3016 -> begin
()
end);
(((se)::[]), (env), ([]));
)
end
| FStar_Syntax_Syntax.SetOptions (o) -> begin
((set_options FStar_Options.Set o);
(((se)::[]), (env), ([]));
)
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
((

let uu____3026 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____3026 Prims.ignore));
(match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end);
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
(((se)::[]), (env), ([]));
)
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____3032) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(

let ne = (tc_eff_decl env ne)
in (

let se = FStar_Syntax_Syntax.Sig_new_effect (((ne), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (

let uu____3045 = (FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun uu____3056 a -> (match (uu____3056) with
| (env, ses) -> begin
(

let se_let = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a)
in (

let uu____3069 = (FStar_TypeChecker_Env.push_sigelt env se_let)
in ((uu____3069), ((se_let)::ses))))
end)) ((env), ((se)::[]))))
in (match (uu____3045) with
| (env, ses) -> begin
(((se)::[]), (env), ([]))
end)))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(

let ed_src = (FStar_TypeChecker_Env.get_effect_decl env sub.FStar_Syntax_Syntax.source)
in (

let ed_tgt = (FStar_TypeChecker_Env.get_effect_decl env sub.FStar_Syntax_Syntax.target)
in (

let uu____3087 = (

let uu____3092 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source uu____3092))
in (match (uu____3087) with
| (a, wp_a_src) -> begin
(

let uu____3104 = (

let uu____3109 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target uu____3109))
in (match (uu____3104) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (

let uu____3122 = (

let uu____3124 = (

let uu____3125 = (

let uu____3130 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (uu____3130)))
in FStar_Syntax_Syntax.NT (uu____3125))
in (uu____3124)::[])
in (FStar_Syntax_Subst.subst uu____3122 wp_b_tgt))
in (

let expected_k = (

let uu____3134 = (

let uu____3138 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____3139 = (

let uu____3141 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (uu____3141)::[])
in (uu____3138)::uu____3139))
in (

let uu____3142 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow uu____3134 uu____3142)))
in (

let repr_type = (fun eff_name a wp -> (

let no_reify = (fun l -> (

let uu____3163 = (

let uu____3164 = (

let uu____3167 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (

let uu____3168 = (FStar_TypeChecker_Env.get_range env)
in ((uu____3167), (uu____3168))))
in FStar_Errors.Error (uu____3164))
in (Prims.raise uu____3163)))
in (

let uu____3171 = (FStar_TypeChecker_Env.effect_decl_opt env eff_name)
in (match (uu____3171) with
| None -> begin
(no_reify eff_name)
end
| Some (ed) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((FStar_Syntax_Syntax.U_unknown)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let uu____3178 = (

let uu____3179 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (not (uu____3179)))
in (match (uu____3178) with
| true -> begin
(no_reify eff_name)
end
| uu____3183 -> begin
(

let uu____3184 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____3185 = (

let uu____3188 = (

let uu____3189 = (

let uu____3199 = (

let uu____3201 = (FStar_Syntax_Syntax.as_arg a)
in (

let uu____3202 = (

let uu____3204 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____3204)::[])
in (uu____3201)::uu____3202))
in ((repr), (uu____3199)))
in FStar_Syntax_Syntax.Tm_app (uu____3189))
in (FStar_Syntax_Syntax.mk uu____3188))
in (uu____3185 None uu____3184)))
end)))
end))))
in (

let uu____3214 = (match (((sub.FStar_Syntax_Syntax.lift), (sub.FStar_Syntax_Syntax.lift_wp))) with
| (None, None) -> begin
(failwith "Impossible")
end
| (lift, Some (uu____3229, lift_wp)) -> begin
(

let uu____3242 = (check_and_gen env lift_wp expected_k)
in ((lift), (uu____3242)))
end
| (Some (what, lift), None) -> begin
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange))
in (

let uu____3257 = (FStar_TypeChecker_DMFF.star_expr dmff_env lift)
in (match (uu____3257) with
| (uu____3264, lift_wp, lift_elab) -> begin
(

let uu____3267 = (recheck_debug "lift-wp" env lift_wp)
in (

let uu____3268 = (recheck_debug "lift-elab" env lift_elab)
in ((Some ((([]), (lift_elab)))), ((([]), (lift_wp))))))
end)))
end)
in (match (uu____3214) with
| (lift, lift_wp) -> begin
(

let lax = env.FStar_TypeChecker_Env.lax
in (

let env = (

let uu___95_3292 = env
in {FStar_TypeChecker_Env.solver = uu___95_3292.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___95_3292.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___95_3292.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___95_3292.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___95_3292.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___95_3292.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___95_3292.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___95_3292.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___95_3292.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___95_3292.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___95_3292.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___95_3292.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___95_3292.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___95_3292.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___95_3292.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___95_3292.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___95_3292.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___95_3292.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___95_3292.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___95_3292.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___95_3292.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___95_3292.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___95_3292.FStar_TypeChecker_Env.qname_and_index})
in (

let lift = (match (lift) with
| None -> begin
None
end
| Some (uu____3296, lift) -> begin
(

let uu____3303 = (

let uu____3308 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source uu____3308))
in (match (uu____3303) with
| (a, wp_a_src) -> begin
(

let wp_a = (FStar_Syntax_Syntax.new_bv None wp_a_src)
in (

let a_typ = (FStar_Syntax_Syntax.bv_to_name a)
in (

let wp_a_typ = (FStar_Syntax_Syntax.bv_to_name wp_a)
in (

let repr_f = (repr_type sub.FStar_Syntax_Syntax.source a_typ wp_a_typ)
in (

let repr_result = (

let lift_wp = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env (Prims.snd lift_wp))
in (

let lift_wp_a = (

let uu____3330 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____3331 = (

let uu____3334 = (

let uu____3335 = (

let uu____3345 = (

let uu____3347 = (FStar_Syntax_Syntax.as_arg a_typ)
in (

let uu____3348 = (

let uu____3350 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (uu____3350)::[])
in (uu____3347)::uu____3348))
in ((lift_wp), (uu____3345)))
in FStar_Syntax_Syntax.Tm_app (uu____3335))
in (FStar_Syntax_Syntax.mk uu____3334))
in (uu____3331 None uu____3330)))
in (repr_type sub.FStar_Syntax_Syntax.target a_typ lift_wp_a)))
in (

let expected_k = (

let uu____3363 = (

let uu____3367 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____3368 = (

let uu____3370 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (

let uu____3371 = (

let uu____3373 = (FStar_Syntax_Syntax.null_binder repr_f)
in (uu____3373)::[])
in (uu____3370)::uu____3371))
in (uu____3367)::uu____3368))
in (

let uu____3374 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow uu____3363 uu____3374)))
in (

let uu____3377 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (uu____3377) with
| (expected_k, uu____3383, uu____3384) -> begin
(

let lift = (check_and_gen env lift expected_k)
in Some (lift))
end))))))))
end))
end)
in (

let env = (

let uu___96_3387 = env
in {FStar_TypeChecker_Env.solver = uu___96_3387.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___96_3387.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___96_3387.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___96_3387.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___96_3387.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___96_3387.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___96_3387.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___96_3387.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___96_3387.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___96_3387.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___96_3387.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___96_3387.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___96_3387.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___96_3387.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___96_3387.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___96_3387.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___96_3387.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___96_3387.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = lax; FStar_TypeChecker_Env.lax_universes = uu___96_3387.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___96_3387.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___96_3387.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___96_3387.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___96_3387.FStar_TypeChecker_Env.qname_and_index})
in (

let sub = (

let uu___97_3389 = sub
in {FStar_Syntax_Syntax.source = uu___97_3389.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = uu___97_3389.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = Some (lift_wp); FStar_Syntax_Syntax.lift = lift})
in (

let se = FStar_Syntax_Syntax.Sig_sub_effect (((sub), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env), ([])))))))))
end)))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, flags, r) -> begin
(

let env0 = env
in (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let uu____3408 = (FStar_Syntax_Subst.open_comp tps c)
in (match (uu____3408) with
| (tps, c) -> begin
(

let uu____3418 = (FStar_TypeChecker_TcTerm.tc_tparams env tps)
in (match (uu____3418) with
| (tps, env, us) -> begin
(

let uu____3430 = (FStar_TypeChecker_TcTerm.tc_comp env c)
in (match (uu____3430) with
| (c, u, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
(

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

let uu____3445 = (

let uu____3446 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 uu____3446))
in (match (uu____3445) with
| (uvs, t) -> begin
(

let uu____3460 = (

let uu____3468 = (

let uu____3471 = (

let uu____3472 = (FStar_Syntax_Subst.compress t)
in uu____3472.FStar_Syntax_Syntax.n)
in ((tps), (uu____3471)))
in (match (uu____3468) with
| ([], FStar_Syntax_Syntax.Tm_arrow (uu____3482, c)) -> begin
(([]), (c))
end
| (uu____3506, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
((tps), (c))
end
| uu____3524 -> begin
(failwith "Impossible")
end))
in (match (uu____3460) with
| (tps, c) -> begin
((match ((((FStar_List.length uvs) <> (Prims.parse_int "1")) && (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))))) with
| true -> begin
(

let uu____3554 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____3554) with
| (uu____3557, t) -> begin
(

let uu____3559 = (

let uu____3560 = (

let uu____3563 = (

let uu____3564 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____3565 = (FStar_All.pipe_right (FStar_List.length uvs) FStar_Util.string_of_int)
in (

let uu____3568 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)" uu____3564 uu____3565 uu____3568))))
in ((uu____3563), (r)))
in FStar_Errors.Error (uu____3560))
in (Prims.raise uu____3559))
end))
end
| uu____3569 -> begin
()
end);
(

let se = FStar_Syntax_Syntax.Sig_effect_abbrev (((lid), (uvs), (tps), (c), (tags), (flags), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env0 se)
in (((se)::[]), (env), ([]))));
)
end))
end))));
)
end))
end))
end))))
end
| (FStar_Syntax_Syntax.Sig_declare_typ (_, _, _, quals, _)) | (FStar_Syntax_Syntax.Sig_let (_, _, _, quals, _)) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___77_3598 -> (match (uu___77_3598) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____3599 -> begin
false
end)))) -> begin
(([]), (env), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t, quals, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let uu____3610 = (match ((uvs = [])) with
| true -> begin
(

let uu____3611 = (

let uu____3612 = (FStar_Syntax_Util.type_u ())
in (Prims.fst uu____3612))
in (check_and_gen env t uu____3611))
end
| uu____3615 -> begin
(

let uu____3616 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____3616) with
| (uvs, t) -> begin
(

let uu____3621 = (

let uu____3622 = (

let uu____3623 = (

let uu____3624 = (FStar_Syntax_Util.type_u ())
in (Prims.fst uu____3624))
in (tc_check_trivial_guard env t uu____3623))
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) uu____3622))
in ((uvs), (uu____3621)))
end))
end)
in (match (uu____3610) with
| (uvs, t) -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (uvs), (t), (quals), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env), ([]))))
end)))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(

let se = (tc_assume env lid phi quals r)
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env), ([]))))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (

let uu____3656 = (FStar_TypeChecker_TcTerm.tc_term env e)
in (match (uu____3656) with
| (e, c, g1) -> begin
(

let uu____3668 = (

let uu____3672 = (

let uu____3674 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (uu____3674))
in (

let uu____3675 = (

let uu____3678 = (c.FStar_Syntax_Syntax.comp ())
in ((e), (uu____3678)))
in (FStar_TypeChecker_TcTerm.check_expected_effect env uu____3672 uu____3675)))
in (match (uu____3668) with
| (e, uu____3689, g) -> begin
((

let uu____3692 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env uu____3692));
(

let se = FStar_Syntax_Syntax.Sig_main (((e), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env), ([]))));
)
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, lids, quals, attrs) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let check_quals_eq = (fun l qopt q -> (match (qopt) with
| None -> begin
Some (q)
end
| Some (q') -> begin
(

let uu____3734 = (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q'))
in (match (uu____3734) with
| true -> begin
Some (q)
end
| uu____3742 -> begin
(

let uu____3743 = (

let uu____3744 = (

let uu____3747 = (

let uu____3748 = (FStar_Syntax_Print.lid_to_string l)
in (

let uu____3749 = (FStar_Syntax_Print.quals_to_string q)
in (

let uu____3750 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" uu____3748 uu____3749 uu____3750))))
in ((uu____3747), (r)))
in FStar_Errors.Error (uu____3744))
in (Prims.raise uu____3743))
end))
end))
in (

let uu____3753 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun uu____3774 lb -> (match (uu____3774) with
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____3798 = (

let uu____3804 = (FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____3804) with
| None -> begin
(match ((lb.FStar_Syntax_Syntax.lbunivs <> [])) with
| true -> begin
((false), (lb), (quals_opt))
end
| uu____3829 -> begin
((gen), (lb), (quals_opt))
end)
end
| Some ((uvs, tval), quals) -> begin
(

let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in ((match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| uu____3856 -> begin
(FStar_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end);
(match (((lb.FStar_Syntax_Syntax.lbunivs <> []) && ((FStar_List.length lb.FStar_Syntax_Syntax.lbunivs) <> (FStar_List.length uvs)))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Inline universes are incoherent with annotation from val declaration"), (r)))))
end
| uu____3863 -> begin
()
end);
(

let uu____3864 = (FStar_Syntax_Syntax.mk_lb ((FStar_Util.Inr (lbname)), (uvs), (FStar_Syntax_Const.effect_ALL_lid), (tval), (lb.FStar_Syntax_Syntax.lbdef)))
in ((false), (uu____3864), (quals_opt)));
))
end))
in (match (uu____3798) with
| (gen, lb, quals_opt) -> begin
((gen), ((lb)::lbs), (quals_opt))
end)))
end)) ((true), ([]), ((match ((quals = [])) with
| true -> begin
None
end
| uu____3895 -> begin
Some (quals)
end)))))
in (match (uu____3753) with
| (should_generalize, lbs', quals_opt) -> begin
(

let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Visible_default)::[]
end
| Some (q) -> begin
(

let uu____3918 = (FStar_All.pipe_right q (FStar_Util.for_some (fun uu___78_3920 -> (match (uu___78_3920) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Visible_default) | (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> begin
true
end
| uu____3921 -> begin
false
end))))
in (match (uu____3918) with
| true -> begin
q
end
| uu____3923 -> begin
(FStar_Syntax_Syntax.Visible_default)::q
end))
end)
in (

let lbs' = (FStar_List.rev lbs')
in (

let e = (

let uu____3929 = (

let uu____3932 = (

let uu____3933 = (

let uu____3941 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((((Prims.fst lbs)), (lbs'))), (uu____3941)))
in FStar_Syntax_Syntax.Tm_let (uu____3933))
in (FStar_Syntax_Syntax.mk uu____3932))
in (uu____3929 None r))
in (

let uu____3963 = (

let uu____3969 = (FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term (

let uu___98_3973 = env
in {FStar_TypeChecker_Env.solver = uu___98_3973.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___98_3973.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___98_3973.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___98_3973.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___98_3973.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___98_3973.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___98_3973.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___98_3973.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___98_3973.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___98_3973.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___98_3973.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = uu___98_3973.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = uu___98_3973.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___98_3973.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___98_3973.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___98_3973.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___98_3973.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___98_3973.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___98_3973.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___98_3973.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___98_3973.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___98_3973.FStar_TypeChecker_Env.qname_and_index}) e)
in (match (uu____3969) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = uu____3981; FStar_Syntax_Syntax.pos = uu____3982; FStar_Syntax_Syntax.vars = uu____3983}, uu____3984, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (uu____4003, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| uu____4008 -> begin
quals
end)
in ((FStar_Syntax_Syntax.Sig_let (((lbs), (r), (lids), (quals), (attrs)))), (lbs)))
end
| uu____4018 -> begin
(failwith "impossible")
end))
in (match (uu____3963) with
| (se, lbs) -> begin
((

let uu____4041 = (log env)
in (match (uu____4041) with
| true -> begin
(

let uu____4042 = (

let uu____4043 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (

let uu____4050 = (

let uu____4055 = (

let uu____4056 = (

let uu____4061 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____4061.FStar_Syntax_Syntax.fv_name)
in uu____4056.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env uu____4055))
in (match (uu____4050) with
| None -> begin
true
end
| uu____4068 -> begin
false
end))
in (match (should_log) with
| true -> begin
(

let uu____4073 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____4074 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" uu____4073 uu____4074)))
end
| uu____4075 -> begin
""
end)))))
in (FStar_All.pipe_right uu____4043 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" uu____4042))
end
| uu____4077 -> begin
()
end));
(

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env), ([])));
)
end)))))
end))))
end);
)))


let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___79_4104 -> (match (uu___79_4104) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| uu____4105 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| uu____4113 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (uu____4118) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, uu____4131, r) -> begin
(

let uu____4139 = (is_abstract quals)
in (match (uu____4139) with
| true -> begin
(FStar_List.fold_right (fun se uu____4149 -> (match (uu____4149) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, uu____4172, uu____4173, quals, r) -> begin
(

let dec = (

let uu____4183 = (

let uu____4190 = (

let uu____4193 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow bs uu____4193))
in ((l), (us), (uu____4190), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____4183))
in (((dec)::out), (hidden)))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, uu____4204, uu____4205, uu____4206, uu____4207, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]), (r)))
in (((dec)::out), ((l)::hidden)))
end
| uu____4217 -> begin
((out), (hidden))
end)
end)) ses (([]), (hidden)))
end
| uu____4222 -> begin
(((se)::[]), (hidden))
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____4225, uu____4226, quals, uu____4228) -> begin
(

let uu____4231 = (is_abstract quals)
in (match (uu____4231) with
| true -> begin
(([]), (hidden))
end
| uu____4238 -> begin
(((se)::[]), (hidden))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, us, t, quals, r) -> begin
(

let uu____4248 = (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc))
in (match (uu____4248) with
| true -> begin
(((FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]), (r))))::[]), ((l)::hidden))
end
| uu____4257 -> begin
(

let uu____4258 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___80_4260 -> (match (uu___80_4260) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| uu____4263 -> begin
false
end))))
in (match (uu____4258) with
| true -> begin
(((se)::[]), (hidden))
end
| uu____4270 -> begin
(([]), (hidden))
end))
end))
end
| FStar_Syntax_Syntax.Sig_main (uu____4273) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____4285, uu____4286, quals, uu____4288) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____4306 = (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
in (match (uu____4306) with
| true -> begin
(([]), (hidden))
end
| uu____4314 -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::[]), ((FStar_Ident.range_of_lid lid))))
in (((dec)::[]), ((lid)::hidden)))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals, uu____4330) -> begin
(

let uu____4337 = (is_abstract quals)
in (match (uu____4337) with
| true -> begin
(

let uu____4342 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let uu____4348 = (

let uu____4355 = (

let uu____4356 = (

let uu____4361 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____4361.FStar_Syntax_Syntax.fv_name)
in uu____4356.FStar_Syntax_Syntax.v)
in ((uu____4355), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____4348)))))
in ((uu____4342), (hidden)))
end
| uu____4371 -> begin
(((se)::[]), (hidden))
end))
end))))


let tc_decls : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env_t) = (fun env ses -> (

let rec process_one_decl = (fun uu____4408 se -> (match (uu____4408) with
| (ses, exports, env, hidden) -> begin
((

let uu____4439 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____4439) with
| true -> begin
(

let uu____4440 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____4440))
end
| uu____4441 -> begin
()
end));
(

let uu____4442 = (tc_decl env se)
in (match (uu____4442) with
| (ses', env, ses_elaborated) -> begin
((

let uu____4464 = ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes"))))
in (match (uu____4464) with
| true -> begin
(

let uu____4465 = (FStar_List.fold_left (fun s se -> (

let uu____4468 = (

let uu____4469 = (FStar_Syntax_Print.sigelt_to_string se)
in (Prims.strcat uu____4469 "\n"))
in (Prims.strcat s uu____4468))) "" ses')
in (FStar_Util.print1 "Checked: %s\n" uu____4465))
end
| uu____4470 -> begin
()
end));
(FStar_List.iter (fun se -> (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)) ses');
(

let uu____4473 = (FStar_List.fold_left (fun uu____4482 se -> (match (uu____4482) with
| (le, lh) -> begin
(

let tup = (for_export hidden se)
in (((FStar_List.rev_append (Prims.fst tup) le)), ((FStar_List.rev_append (Prims.snd tup) lh))))
end)) (([]), ([])) ses')
in (match (uu____4473) with
| (exported, hidden) -> begin
(FStar_List.fold_left process_one_decl (((FStar_List.rev_append ses' ses)), (((FStar_List.rev_append exported []))::exports), (env), (hidden)) ses_elaborated)
end));
)
end));
)
end))
in (

let uu____4538 = (FStar_List.fold_left (fun acc se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, r) -> begin
(

let uu____4575 = acc
in (match (uu____4575) with
| (uu____4592, uu____4593, env, uu____4595) -> begin
(

let uu____4604 = (cps_and_elaborate env ne)
in (match (uu____4604) with
| (ses, ne, lift_from_pure_opt) -> begin
(

let ses = (match (lift_from_pure_opt) with
| Some (lift) -> begin
(FStar_List.append ses ((FStar_Syntax_Syntax.Sig_new_effect (((ne), (r))))::(lift)::[]))
end
| None -> begin
(FStar_List.append ses ((FStar_Syntax_Syntax.Sig_new_effect (((ne), (r))))::[]))
end)
in (FStar_List.fold_left process_one_decl acc ses))
end))
end))
end
| uu____4637 -> begin
(process_one_decl acc se)
end)) (([]), ([]), (env), ([])) ses)
in (match (uu____4538) with
| (ses, exports, env, uu____4651) -> begin
(

let uu____4660 = (FStar_All.pipe_right (FStar_List.rev_append exports []) FStar_List.flatten)
in (((FStar_List.rev_append ses [])), (uu____4660), (env)))
end))))


let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (

let verify = (FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let action = (match (verify) with
| true -> begin
"Verifying"
end
| uu____4681 -> begin
"Lax-checking"
end)
in (

let label = (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____4683 -> begin
"implementation"
end)
in ((

let uu____4685 = (FStar_Options.debug_any ())
in (match (uu____4685) with
| true -> begin
(FStar_Util.print3 "%s %s of %s\n" action label modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
end
| uu____4686 -> begin
()
end));
(

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____4688 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let msg = (Prims.strcat "Internals for " name)
in (

let env = (

let uu___99_4691 = env
in {FStar_TypeChecker_Env.solver = uu___99_4691.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___99_4691.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___99_4691.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___99_4691.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___99_4691.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___99_4691.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___99_4691.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___99_4691.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___99_4691.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___99_4691.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___99_4691.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___99_4691.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___99_4691.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___99_4691.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___99_4691.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___99_4691.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = (not (verify)); FStar_TypeChecker_Env.lax = uu___99_4691.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___99_4691.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___99_4691.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___99_4691.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___99_4691.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___99_4691.FStar_TypeChecker_Env.qname_and_index})
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg);
(

let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

let uu____4694 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (uu____4694) with
| (ses, exports, env) -> begin
(((

let uu___100_4712 = modul
in {FStar_Syntax_Syntax.name = uu___100_4712.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = uu___100_4712.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___100_4712.FStar_Syntax_Syntax.is_interface})), (exports), (env))
end)));
))));
)))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let uu____4728 = (tc_decls env decls)
in (match (uu____4728) with
| (ses, exports, env) -> begin
(

let modul = (

let uu___101_4746 = modul
in {FStar_Syntax_Syntax.name = uu___101_4746.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = uu___101_4746.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___101_4746.FStar_Syntax_Syntax.is_interface})
in ((modul), (exports), (env)))
end)))


let check_exports : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env modul exports -> (

let env = (

let uu___102_4760 = env
in {FStar_TypeChecker_Env.solver = uu___102_4760.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___102_4760.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___102_4760.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___102_4760.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___102_4760.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___102_4760.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___102_4760.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___102_4760.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___102_4760.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___102_4760.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___102_4760.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___102_4760.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___102_4760.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = uu___102_4760.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___102_4760.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___102_4760.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___102_4760.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = true; FStar_TypeChecker_Env.type_of = uu___102_4760.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___102_4760.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___102_4760.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___102_4760.FStar_TypeChecker_Env.qname_and_index})
in (

let check_term = (fun lid univs t -> (

let uu____4771 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (uu____4771) with
| (univs, t) -> begin
((

let uu____4777 = (

let uu____4778 = (

let uu____4781 = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (FStar_TypeChecker_Env.debug uu____4781))
in (FStar_All.pipe_left uu____4778 (FStar_Options.Other ("Exports"))))
in (match (uu____4777) with
| true -> begin
(

let uu____4782 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____4783 = (

let uu____4784 = (FStar_All.pipe_right univs (FStar_List.map (fun x -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (x))))))
in (FStar_All.pipe_right uu____4784 (FStar_String.concat ", ")))
in (

let uu____4789 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print3 "Checking for export %s <%s> : %s\n" uu____4782 uu____4783 uu____4789))))
end
| uu____4790 -> begin
()
end));
(

let env = (FStar_TypeChecker_Env.push_univ_vars env univs)
in (

let uu____4792 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env t)
in (FStar_All.pipe_right uu____4792 Prims.ignore)));
)
end)))
in (

let check_term = (fun lid univs t -> ((

let uu____4810 = (

let uu____4811 = (FStar_Syntax_Print.lid_to_string modul.FStar_Syntax_Syntax.name)
in (

let uu____4812 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Interface of %s violates its abstraction (add a \'private\' qualifier to \'%s\'?)" uu____4811 uu____4812)))
in (FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____4810));
(check_term lid univs t);
(FStar_Errors.message_prefix.FStar_Errors.clear_prefix ());
))
in (

let rec check_sigelt = (fun uu___81_4817 -> (match (uu___81_4817) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, uu____4820, uu____4821) -> begin
(

let uu____4828 = (

let uu____4829 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____4829)))
in (match (uu____4828) with
| true -> begin
(FStar_All.pipe_right ses (FStar_List.iter check_sigelt))
end
| uu____4832 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (l, univs, binders, typ, uu____4837, uu____4838, uu____4839, r) -> begin
(

let t = (

let uu____4850 = (

let uu____4853 = (

let uu____4854 = (

let uu____4862 = (FStar_Syntax_Syntax.mk_Total typ)
in ((binders), (uu____4862)))
in FStar_Syntax_Syntax.Tm_arrow (uu____4854))
in (FStar_Syntax_Syntax.mk uu____4853))
in (uu____4850 None r))
in (check_term l univs t))
end
| FStar_Syntax_Syntax.Sig_datacon (l, univs, t, uu____4874, uu____4875, uu____4876, uu____4877, uu____4878) -> begin
(check_term l univs t)
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, univs, t, quals, uu____4887) -> begin
(

let uu____4890 = (

let uu____4891 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____4891)))
in (match (uu____4890) with
| true -> begin
(check_term l univs t)
end
| uu____4893 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_let ((uu____4894, lbs), uu____4896, uu____4897, quals, uu____4899) -> begin
(

let uu____4911 = (

let uu____4912 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____4912)))
in (match (uu____4911) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (check_term fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp)))))
end
| uu____4921 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, binders, comp, quals, flags, r) -> begin
(

let uu____4933 = (

let uu____4934 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____4934)))
in (match (uu____4933) with
| true -> begin
(

let arrow = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp))))) None r)
in (check_term l univs arrow))
end
| uu____4947 -> begin
()
end))
end
| (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_assume (_)) | (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) -> begin
()
end))
in (match ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid)) with
| true -> begin
()
end
| uu____4954 -> begin
(FStar_List.iter check_sigelt exports)
end))))))


let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (

let modul = (

let uu___103_4967 = modul
in {FStar_Syntax_Syntax.name = uu___103_4967.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu___103_4967.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module env modul)
in ((

let uu____4970 = (

let uu____4971 = (FStar_Options.lax ())
in (not (uu____4971)))
in (match (uu____4970) with
| true -> begin
(check_exports env modul exports)
end
| uu____4972 -> begin
()
end));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul);
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
(

let uu____4977 = (

let uu____4978 = (FStar_Options.interactive ())
in (not (uu____4978)))
in (match (uu____4977) with
| true -> begin
(

let uu____4979 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right uu____4979 Prims.ignore))
end
| uu____4980 -> begin
()
end));
((modul), (env));
))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let uu____4989 = (tc_partial_modul env modul)
in (match (uu____4989) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> ((

let uu____5010 = (FStar_Options.debug_any ())
in (match (uu____5010) with
| true -> begin
(

let uu____5011 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (match (m.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"i\'face"
end
| uu____5012 -> begin
"module"
end) uu____5011))
end
| uu____5013 -> begin
()
end));
(

let env = (

let uu___104_5015 = env
in (

let uu____5016 = (

let uu____5017 = (FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (not (uu____5017)))
in {FStar_TypeChecker_Env.solver = uu___104_5015.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___104_5015.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___104_5015.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___104_5015.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___104_5015.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___104_5015.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___104_5015.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___104_5015.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___104_5015.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___104_5015.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___104_5015.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___104_5015.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___104_5015.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___104_5015.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___104_5015.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___104_5015.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___104_5015.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___104_5015.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu____5016; FStar_TypeChecker_Env.lax_universes = uu___104_5015.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___104_5015.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___104_5015.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___104_5015.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___104_5015.FStar_TypeChecker_Env.qname_and_index}))
in (

let uu____5018 = (tc_modul env m)
in (match (uu____5018) with
| (m, env) -> begin
((

let uu____5026 = (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____5026) with
| true -> begin
(

let uu____5027 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" uu____5027))
end
| uu____5028 -> begin
()
end));
(

let uu____5030 = ((FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) && (FStar_Options.debug_at_level m.FStar_Syntax_Syntax.name.FStar_Ident.str (FStar_Options.Other ("Normalize"))))
in (match (uu____5030) with
| true -> begin
(

let normalize_toplevel_lets = (fun uu___82_5034 -> (match (uu___82_5034) with
| FStar_Syntax_Syntax.Sig_let ((b, lbs), r, ids, qs, attrs) -> begin
(

let n = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]))
in (

let update = (fun lb -> (

let uu____5061 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____5061) with
| (univnames, e) -> begin
(

let uu___105_5066 = lb
in (

let uu____5067 = (

let uu____5070 = (FStar_TypeChecker_Env.push_univ_vars env univnames)
in (n uu____5070 e))
in {FStar_Syntax_Syntax.lbname = uu___105_5066.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___105_5066.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___105_5066.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___105_5066.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____5067}))
end)))
in (

let uu____5071 = (

let uu____5080 = (

let uu____5084 = (FStar_List.map update lbs)
in ((b), (uu____5084)))
in ((uu____5080), (r), (ids), (qs), (attrs)))
in FStar_Syntax_Syntax.Sig_let (uu____5071))))
end
| se -> begin
se
end))
in (

let normalized_module = (

let uu___106_5095 = m
in (

let uu____5096 = (FStar_List.map normalize_toplevel_lets m.FStar_Syntax_Syntax.declarations)
in {FStar_Syntax_Syntax.name = uu___106_5095.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu____5096; FStar_Syntax_Syntax.exports = uu___106_5095.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___106_5095.FStar_Syntax_Syntax.is_interface}))
in (

let uu____5097 = (FStar_Syntax_Print.modul_to_string normalized_module)
in (FStar_Util.print1 "%s\n" uu____5097))))
end
| uu____5098 -> begin
()
end));
((m), (env));
)
end)));
))




