
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

let uu___84_12 = env
in {FStar_TypeChecker_Env.solver = uu___84_12.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___84_12.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___84_12.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___84_12.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___84_12.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___84_12.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___84_12.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___84_12.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___84_12.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___84_12.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___84_12.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___84_12.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___84_12.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___84_12.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___84_12.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___84_12.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___84_12.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___84_12.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___84_12.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___84_12.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___84_12.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___84_12.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___84_12.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), ((Prims.parse_int "0"))))}))
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

let uu___85_24 = env
in {FStar_TypeChecker_Env.solver = uu___85_24.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___85_24.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___85_24.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___85_24.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___85_24.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___85_24.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___85_24.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___85_24.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___85_24.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___85_24.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___85_24.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___85_24.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___85_24.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___85_24.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___85_24.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___85_24.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___85_24.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___85_24.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___85_24.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___85_24.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___85_24.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___85_24.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___85_24.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), ((Prims.parse_int "0"))))})))
end)))


let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_Options.log_types ()) && (

let uu____30 = (

let uu____31 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____31))
in (not (uu____30)))))


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let uu____41 = (FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k)
in (match (uu____41) with
| (t1, c, g) -> begin
((FStar_ST.write t1.FStar_Syntax_Syntax.tk (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)));
(FStar_TypeChecker_Rel.force_trivial_guard env g);
t1;
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

let t1 = (tc_check_trivial_guard env t k)
in (

let uu____108 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t1)
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

let s1 = (FStar_Syntax_Subst.compress s)
in (match (s1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs1 = (FStar_Syntax_Subst.open_binders bs)
in (match (bs1) with
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


let rec tc_eff_decl : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (

let uu____238 = (FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____238) with
| (effect_params_un, signature_un, opening) -> begin
(

let uu____245 = (FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un)
in (match (uu____245) with
| (effect_params, env, uu____251) -> begin
(

let uu____252 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (uu____252) with
| (signature, uu____256) -> begin
(

let ed1 = (

let uu___86_258 = ed
in {FStar_Syntax_Syntax.qualifiers = uu___86_258.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___86_258.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___86_258.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___86_258.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = uu___86_258.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = uu___86_258.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = uu___86_258.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = uu___86_258.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = uu___86_258.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = uu___86_258.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = uu___86_258.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = uu___86_258.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = uu___86_258.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = uu___86_258.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = uu___86_258.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = uu___86_258.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = uu___86_258.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = uu___86_258.FStar_Syntax_Syntax.actions})
in (

let ed2 = (match (effect_params) with
| [] -> begin
ed1
end
| uu____262 -> begin
(

let op = (fun ts -> (

let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in (([]), (t1))))
in (

let uu___87_280 = ed1
in (

let uu____281 = (op ed1.FStar_Syntax_Syntax.ret_wp)
in (

let uu____282 = (op ed1.FStar_Syntax_Syntax.bind_wp)
in (

let uu____283 = (op ed1.FStar_Syntax_Syntax.if_then_else)
in (

let uu____284 = (op ed1.FStar_Syntax_Syntax.ite_wp)
in (

let uu____285 = (op ed1.FStar_Syntax_Syntax.stronger)
in (

let uu____286 = (op ed1.FStar_Syntax_Syntax.close_wp)
in (

let uu____287 = (op ed1.FStar_Syntax_Syntax.assert_p)
in (

let uu____288 = (op ed1.FStar_Syntax_Syntax.assume_p)
in (

let uu____289 = (op ed1.FStar_Syntax_Syntax.null_wp)
in (

let uu____290 = (op ed1.FStar_Syntax_Syntax.trivial)
in (

let uu____291 = (

let uu____292 = (op (([]), (ed1.FStar_Syntax_Syntax.repr)))
in (Prims.snd uu____292))
in (

let uu____298 = (op ed1.FStar_Syntax_Syntax.return_repr)
in (

let uu____299 = (op ed1.FStar_Syntax_Syntax.bind_repr)
in (

let uu____300 = (FStar_List.map (fun a -> (

let uu___88_303 = a
in (

let uu____304 = (

let uu____305 = (op (([]), (a.FStar_Syntax_Syntax.action_defn)))
in (Prims.snd uu____305))
in (

let uu____311 = (

let uu____312 = (op (([]), (a.FStar_Syntax_Syntax.action_typ)))
in (Prims.snd uu____312))
in {FStar_Syntax_Syntax.action_name = uu___88_303.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___88_303.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___88_303.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = uu____304; FStar_Syntax_Syntax.action_typ = uu____311})))) ed1.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.qualifiers = uu___87_280.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___87_280.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___87_280.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___87_280.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu___87_280.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = uu___87_280.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = uu____281; FStar_Syntax_Syntax.bind_wp = uu____282; FStar_Syntax_Syntax.if_then_else = uu____283; FStar_Syntax_Syntax.ite_wp = uu____284; FStar_Syntax_Syntax.stronger = uu____285; FStar_Syntax_Syntax.close_wp = uu____286; FStar_Syntax_Syntax.assert_p = uu____287; FStar_Syntax_Syntax.assume_p = uu____288; FStar_Syntax_Syntax.null_wp = uu____289; FStar_Syntax_Syntax.trivial = uu____290; FStar_Syntax_Syntax.repr = uu____291; FStar_Syntax_Syntax.return_repr = uu____298; FStar_Syntax_Syntax.bind_repr = uu____299; FStar_Syntax_Syntax.actions = uu____300}))))))))))))))))
end)
in (

let wp_with_fresh_result_type = (fun env1 mname signature1 -> (

let fail = (fun t -> (

let uu____340 = (

let uu____341 = (

let uu____344 = (FStar_TypeChecker_Err.unexpected_signature_for_monad env1 mname t)
in ((uu____344), ((FStar_Ident.range_of_lid mname))))
in FStar_Errors.Error (uu____341))
in (Prims.raise uu____340)))
in (

let uu____349 = (

let uu____350 = (FStar_Syntax_Subst.compress signature1)
in uu____350.FStar_Syntax_Syntax.n)
in (match (uu____349) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs1 = (FStar_Syntax_Subst.open_binders bs)
in (match (bs1) with
| ((a, uu____375))::((wp, uu____377))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____386 -> begin
(fail signature1)
end))
end
| uu____387 -> begin
(fail signature1)
end))))
in (

let uu____388 = (wp_with_fresh_result_type env ed2.FStar_Syntax_Syntax.mname ed2.FStar_Syntax_Syntax.signature)
in (match (uu____388) with
| (a, wp_a) -> begin
(

let fresh_effect_signature = (fun uu____406 -> (

let uu____407 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (uu____407) with
| (signature1, uu____415) -> begin
(wp_with_fresh_result_type env ed2.FStar_Syntax_Syntax.mname signature1)
end)))
in (

let env1 = (

let uu____417 = (FStar_Syntax_Syntax.new_bv None ed2.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env uu____417))
in ((

let uu____419 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED")))
in (match (uu____419) with
| true -> begin
(

let uu____420 = (FStar_Syntax_Print.lid_to_string ed2.FStar_Syntax_Syntax.mname)
in (

let uu____421 = (FStar_Syntax_Print.binders_to_string " " ed2.FStar_Syntax_Syntax.binders)
in (

let uu____422 = (FStar_Syntax_Print.term_to_string ed2.FStar_Syntax_Syntax.signature)
in (

let uu____423 = (

let uu____424 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Print.term_to_string uu____424))
in (

let uu____425 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.sort)
in (FStar_Util.print5 "Checking effect signature: %s %s : %s\n(a is %s:%s)\n" uu____420 uu____421 uu____422 uu____423 uu____425))))))
end
| uu____426 -> begin
()
end));
(

let check_and_gen' = (fun env2 uu____438 k -> (match (uu____438) with
| (uu____443, t) -> begin
(check_and_gen env2 t k)
end))
in (

let return_wp = (

let expected_k = (

let uu____451 = (

let uu____455 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____456 = (

let uu____458 = (

let uu____459 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____459))
in (uu____458)::[])
in (uu____455)::uu____456))
in (

let uu____460 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow uu____451 uu____460)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.ret_wp expected_k))
in (

let bind_wp = (

let uu____464 = (fresh_effect_signature ())
in (match (uu____464) with
| (b, wp_b) -> begin
(

let a_wp_b = (

let uu____478 = (

let uu____482 = (

let uu____483 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____483))
in (uu____482)::[])
in (

let uu____484 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____478 uu____484)))
in (

let expected_k = (

let uu____490 = (

let uu____494 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (

let uu____495 = (

let uu____497 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____498 = (

let uu____500 = (FStar_Syntax_Syntax.mk_binder b)
in (

let uu____501 = (

let uu____503 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____504 = (

let uu____506 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (uu____506)::[])
in (uu____503)::uu____504))
in (uu____500)::uu____501))
in (uu____497)::uu____498))
in (uu____494)::uu____495))
in (

let uu____507 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____490 uu____507)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else1 = (

let p = (

let uu____512 = (

let uu____513 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____513 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed2.FStar_Syntax_Syntax.mname))) uu____512))
in (

let expected_k = (

let uu____521 = (

let uu____525 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____526 = (

let uu____528 = (FStar_Syntax_Syntax.mk_binder p)
in (

let uu____529 = (

let uu____531 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____532 = (

let uu____534 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____534)::[])
in (uu____531)::uu____532))
in (uu____528)::uu____529))
in (uu____525)::uu____526))
in (

let uu____535 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____521 uu____535)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (

let uu____542 = (

let uu____546 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____547 = (

let uu____549 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____549)::[])
in (uu____546)::uu____547))
in (

let uu____550 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____542 uu____550)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let uu____554 = (FStar_Syntax_Util.type_u ())
in (match (uu____554) with
| (t, uu____558) -> begin
(

let expected_k = (

let uu____562 = (

let uu____566 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____567 = (

let uu____569 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____570 = (

let uu____572 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____572)::[])
in (uu____569)::uu____570))
in (uu____566)::uu____567))
in (

let uu____573 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow uu____562 uu____573)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (

let uu____578 = (

let uu____579 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____579 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed2.FStar_Syntax_Syntax.mname))) uu____578))
in (

let b_wp_a = (

let uu____587 = (

let uu____591 = (

let uu____592 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder uu____592))
in (uu____591)::[])
in (

let uu____593 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____587 uu____593)))
in (

let expected_k = (

let uu____599 = (

let uu____603 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____604 = (

let uu____606 = (FStar_Syntax_Syntax.mk_binder b)
in (

let uu____607 = (

let uu____609 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (uu____609)::[])
in (uu____606)::uu____607))
in (uu____603)::uu____604))
in (

let uu____610 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____599 uu____610)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (

let uu____617 = (

let uu____621 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____622 = (

let uu____624 = (

let uu____625 = (

let uu____626 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____626 Prims.fst))
in (FStar_Syntax_Syntax.null_binder uu____625))
in (

let uu____631 = (

let uu____633 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____633)::[])
in (uu____624)::uu____631))
in (uu____621)::uu____622))
in (

let uu____634 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____617 uu____634)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (

let uu____641 = (

let uu____645 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____646 = (

let uu____648 = (

let uu____649 = (

let uu____650 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____650 Prims.fst))
in (FStar_Syntax_Syntax.null_binder uu____649))
in (

let uu____655 = (

let uu____657 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____657)::[])
in (uu____648)::uu____655))
in (uu____645)::uu____646))
in (

let uu____658 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____641 uu____658)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (

let uu____665 = (

let uu____669 = (FStar_Syntax_Syntax.mk_binder a)
in (uu____669)::[])
in (

let uu____670 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____665 uu____670)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let uu____674 = (FStar_Syntax_Util.type_u ())
in (match (uu____674) with
| (t, uu____678) -> begin
(

let expected_k = (

let uu____682 = (

let uu____686 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____687 = (

let uu____689 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____689)::[])
in (uu____686)::uu____687))
in (

let uu____690 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow uu____682 uu____690)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let uu____693 = (

let uu____699 = (

let uu____700 = (FStar_Syntax_Subst.compress ed2.FStar_Syntax_Syntax.repr)
in uu____700.FStar_Syntax_Syntax.n)
in (match (uu____699) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((ed2.FStar_Syntax_Syntax.repr), (ed2.FStar_Syntax_Syntax.bind_repr), (ed2.FStar_Syntax_Syntax.return_repr), (ed2.FStar_Syntax_Syntax.actions))
end
| uu____709 -> begin
(

let repr = (

let uu____711 = (FStar_Syntax_Util.type_u ())
in (match (uu____711) with
| (t, uu____715) -> begin
(

let expected_k = (

let uu____719 = (

let uu____723 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____724 = (

let uu____726 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____726)::[])
in (uu____723)::uu____724))
in (

let uu____727 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow uu____719 uu____727)))
in (tc_check_trivial_guard env1 ed2.FStar_Syntax_Syntax.repr expected_k))
end))
in (

let mk_repr' = (fun t wp -> (

let repr1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env1 repr)
in (

let uu____740 = (

let uu____743 = (

let uu____744 = (

let uu____754 = (

let uu____756 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____757 = (

let uu____759 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____759)::[])
in (uu____756)::uu____757))
in ((repr1), (uu____754)))
in FStar_Syntax_Syntax.Tm_app (uu____744))
in (FStar_Syntax_Syntax.mk uu____743))
in (uu____740 None FStar_Range.dummyRange))))
in (

let mk_repr = (fun a1 wp -> (

let uu____778 = (FStar_Syntax_Syntax.bv_to_name a1)
in (mk_repr' uu____778 wp)))
in (

let destruct_repr = (fun t -> (

let uu____789 = (

let uu____790 = (FStar_Syntax_Subst.compress t)
in uu____790.FStar_Syntax_Syntax.n)
in (match (uu____789) with
| FStar_Syntax_Syntax.Tm_app (uu____799, ((t1, uu____801))::((wp, uu____803))::[]) -> begin
((t1), (wp))
end
| uu____837 -> begin
(failwith "Unexpected repr type")
end)))
in (

let bind_repr = (

let r = (

let uu____846 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_0 FStar_Syntax_Syntax.Delta_constant None)
in (FStar_All.pipe_right uu____846 FStar_Syntax_Syntax.fv_to_tm))
in (

let uu____847 = (fresh_effect_signature ())
in (match (uu____847) with
| (b, wp_b) -> begin
(

let a_wp_b = (

let uu____861 = (

let uu____865 = (

let uu____866 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____866))
in (uu____865)::[])
in (

let uu____867 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____861 uu____867)))
in (

let wp_f = (FStar_Syntax_Syntax.gen_bv "wp_f" None wp_a)
in (

let wp_g = (FStar_Syntax_Syntax.gen_bv "wp_g" None a_wp_b)
in (

let x_a = (

let uu____873 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None uu____873))
in (

let wp_g_x = (

let uu____877 = (

let uu____878 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (

let uu____879 = (

let uu____880 = (

let uu____881 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____881))
in (uu____880)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____878 uu____879)))
in (uu____877 None FStar_Range.dummyRange))
in (

let res = (

let wp = (

let uu____892 = (

let uu____893 = (

let uu____894 = (FStar_TypeChecker_Env.inst_tscheme bind_wp)
in (FStar_All.pipe_right uu____894 Prims.snd))
in (

let uu____899 = (

let uu____900 = (

let uu____902 = (

let uu____904 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____905 = (

let uu____907 = (FStar_Syntax_Syntax.bv_to_name b)
in (

let uu____908 = (

let uu____910 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (

let uu____911 = (

let uu____913 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (uu____913)::[])
in (uu____910)::uu____911))
in (uu____907)::uu____908))
in (uu____904)::uu____905))
in (r)::uu____902)
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____900))
in (FStar_Syntax_Syntax.mk_Tm_app uu____893 uu____899)))
in (uu____892 None FStar_Range.dummyRange))
in (mk_repr b wp))
in (

let expected_k = (

let uu____921 = (

let uu____925 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____926 = (

let uu____928 = (FStar_Syntax_Syntax.mk_binder b)
in (

let uu____929 = (

let uu____931 = (FStar_Syntax_Syntax.mk_binder wp_f)
in (

let uu____932 = (

let uu____934 = (

let uu____935 = (

let uu____936 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (mk_repr a uu____936))
in (FStar_Syntax_Syntax.null_binder uu____935))
in (

let uu____937 = (

let uu____939 = (FStar_Syntax_Syntax.mk_binder wp_g)
in (

let uu____940 = (

let uu____942 = (

let uu____943 = (

let uu____944 = (

let uu____948 = (FStar_Syntax_Syntax.mk_binder x_a)
in (uu____948)::[])
in (

let uu____949 = (

let uu____952 = (mk_repr b wp_g_x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____952))
in (FStar_Syntax_Util.arrow uu____944 uu____949)))
in (FStar_Syntax_Syntax.null_binder uu____943))
in (uu____942)::[])
in (uu____939)::uu____940))
in (uu____934)::uu____937))
in (uu____931)::uu____932))
in (uu____928)::uu____929))
in (uu____925)::uu____926))
in (

let uu____953 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow uu____921 uu____953)))
in (

let uu____956 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1 expected_k)
in (match (uu____956) with
| (expected_k1, uu____961, uu____962) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_range env1 (Prims.snd ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos)
in (

let env3 = (

let uu___89_966 = env2
in {FStar_TypeChecker_Env.solver = uu___89_966.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___89_966.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___89_966.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___89_966.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___89_966.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___89_966.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___89_966.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___89_966.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___89_966.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___89_966.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___89_966.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___89_966.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___89_966.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___89_966.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___89_966.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___89_966.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___89_966.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___89_966.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___89_966.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___89_966.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___89_966.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___89_966.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___89_966.FStar_TypeChecker_Env.qname_and_index})
in (

let br = (check_and_gen' env3 ed2.FStar_Syntax_Syntax.bind_repr expected_k1)
in br)))
end)))))))))
end)))
in (

let return_repr = (

let x_a = (

let uu____973 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None uu____973))
in (

let res = (

let wp = (

let uu____980 = (

let uu____981 = (

let uu____982 = (FStar_TypeChecker_Env.inst_tscheme return_wp)
in (FStar_All.pipe_right uu____982 Prims.snd))
in (

let uu____987 = (

let uu____988 = (

let uu____990 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____991 = (

let uu____993 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (uu____993)::[])
in (uu____990)::uu____991))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____988))
in (FStar_Syntax_Syntax.mk_Tm_app uu____981 uu____987)))
in (uu____980 None FStar_Range.dummyRange))
in (mk_repr a wp))
in (

let expected_k = (

let uu____1001 = (

let uu____1005 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1006 = (

let uu____1008 = (FStar_Syntax_Syntax.mk_binder x_a)
in (uu____1008)::[])
in (uu____1005)::uu____1006))
in (

let uu____1009 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow uu____1001 uu____1009)))
in (

let uu____1012 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1 expected_k)
in (match (uu____1012) with
| (expected_k1, uu____1020, uu____1021) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_range env1 (Prims.snd ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos)
in (

let uu____1024 = (check_and_gen' env2 ed2.FStar_Syntax_Syntax.return_repr expected_k1)
in (match (uu____1024) with
| (univs1, repr1) -> begin
(match (univs1) with
| [] -> begin
(([]), (repr1))
end
| uu____1036 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected universe-polymorphic return for effect"), (repr1.FStar_Syntax_Syntax.pos)))))
end)
end)))
end)))))
in (

let actions = (

let check_action = (fun act -> (

let uu____1047 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1 act.FStar_Syntax_Syntax.action_typ)
in (match (uu____1047) with
| (act_typ, uu____1052, g_t) -> begin
(

let env' = (FStar_TypeChecker_Env.set_expected_typ env1 act_typ)
in ((

let uu____1056 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____1056) with
| true -> begin
(

let uu____1057 = (FStar_Syntax_Print.term_to_string act.FStar_Syntax_Syntax.action_defn)
in (

let uu____1058 = (FStar_Syntax_Print.term_to_string act_typ)
in (FStar_Util.print3 "Checking action %s:\n[definition]: %s\n[cps\'d type]: %s\n" (FStar_Ident.text_of_lid act.FStar_Syntax_Syntax.action_name) uu____1057 uu____1058)))
end
| uu____1059 -> begin
()
end));
(

let uu____1060 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' act.FStar_Syntax_Syntax.action_defn)
in (match (uu____1060) with
| (act_defn, uu____1065, g_a) -> begin
(

let act_defn1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env1 act_defn)
in (

let act_typ1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::[]) env1 act_typ)
in (

let uu____1069 = (

let act_typ2 = (FStar_Syntax_Subst.compress act_typ1)
in (match (act_typ2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____1087 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____1087) with
| (bs1, uu____1093) -> begin
(

let res = (mk_repr' FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun)
in (

let k = (

let uu____1100 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs1 uu____1100))
in (

let uu____1103 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1 k)
in (match (uu____1103) with
| (k1, uu____1110, g) -> begin
((k1), (g))
end))))
end))
end
| uu____1112 -> begin
(

let uu____1113 = (

let uu____1114 = (

let uu____1117 = (

let uu____1118 = (FStar_Syntax_Print.term_to_string act_typ2)
in (

let uu____1119 = (FStar_Syntax_Print.tag_of_term act_typ2)
in (FStar_Util.format2 "Actions must have function types (not: %s, a.k.a. %s)" uu____1118 uu____1119)))
in ((uu____1117), (act_defn1.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____1114))
in (Prims.raise uu____1113))
end))
in (match (uu____1069) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env1 act_typ1 expected_k)
in ((

let uu____1126 = (

let uu____1127 = (

let uu____1128 = (FStar_TypeChecker_Rel.conj_guard g_t g)
in (FStar_TypeChecker_Rel.conj_guard g_k uu____1128))
in (FStar_TypeChecker_Rel.conj_guard g_a uu____1127))
in (FStar_TypeChecker_Rel.force_trivial_guard env1 uu____1126));
(

let act_typ2 = (

let uu____1132 = (

let uu____1133 = (FStar_Syntax_Subst.compress expected_k)
in uu____1133.FStar_Syntax_Syntax.n)
in (match (uu____1132) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____1150 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____1150) with
| (bs1, c1) -> begin
(

let uu____1157 = (destruct_repr (FStar_Syntax_Util.comp_result c1))
in (match (uu____1157) with
| (a1, wp) -> begin
(

let c2 = (

let uu____1177 = (

let uu____1178 = (env1.FStar_TypeChecker_Env.universe_of env1 a1)
in (uu____1178)::[])
in (

let uu____1179 = (

let uu____1185 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____1185)::[])
in {FStar_Syntax_Syntax.comp_univs = uu____1177; FStar_Syntax_Syntax.effect_name = ed2.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a1; FStar_Syntax_Syntax.effect_args = uu____1179; FStar_Syntax_Syntax.flags = []}))
in (

let uu____1186 = (FStar_Syntax_Syntax.mk_Comp c2)
in (FStar_Syntax_Util.arrow bs1 uu____1186)))
end))
end))
end
| uu____1189 -> begin
(failwith "")
end))
in (

let uu____1192 = (FStar_TypeChecker_Util.generalize_universes env1 act_defn1)
in (match (uu____1192) with
| (univs1, act_defn2) -> begin
(

let act_typ3 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env1 act_typ2)
in (

let uu___90_1198 = act
in {FStar_Syntax_Syntax.action_name = uu___90_1198.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___90_1198.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs1; FStar_Syntax_Syntax.action_defn = act_defn2; FStar_Syntax_Syntax.action_typ = act_typ3}))
end)));
))
end))))
end));
))
end)))
in (FStar_All.pipe_right ed2.FStar_Syntax_Syntax.actions (FStar_List.map check_action)))
in ((repr), (bind_repr), (return_repr), (actions)))))))))
end))
in (match (uu____693) with
| (repr, bind_repr, return_repr, actions) -> begin
(

let t = (

let uu____1214 = (FStar_Syntax_Syntax.mk_Total ed2.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed2.FStar_Syntax_Syntax.binders uu____1214))
in (

let uu____1217 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (uu____1217) with
| (univs1, t1) -> begin
(

let signature1 = (

let uu____1223 = (

let uu____1226 = (

let uu____1227 = (FStar_Syntax_Subst.compress t1)
in uu____1227.FStar_Syntax_Syntax.n)
in ((effect_params), (uu____1226)))
in (match (uu____1223) with
| ([], uu____1230) -> begin
t1
end
| (uu____1236, FStar_Syntax_Syntax.Tm_arrow (uu____1237, c)) -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____1249 -> begin
(failwith "Impossible")
end))
in (

let close1 = (fun n1 ts -> (

let ts1 = (

let uu____1260 = (FStar_Syntax_Subst.close_tscheme effect_params ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs1 uu____1260))
in (

let m = (FStar_List.length (Prims.fst ts1))
in ((

let uu____1265 = (((n1 >= (Prims.parse_int "0")) && (

let uu____1266 = (FStar_Syntax_Util.is_unknown (Prims.snd ts1))
in (not (uu____1266)))) && (m <> n1))
in (match (uu____1265) with
| true -> begin
(

let error = (match ((m < n1)) with
| true -> begin
"not universe-polymorphic enough"
end
| uu____1274 -> begin
"too universe-polymorphic"
end)
in (

let uu____1275 = (

let uu____1276 = (FStar_Util.string_of_int n1)
in (

let uu____1277 = (FStar_Syntax_Print.tscheme_to_string ts1)
in (FStar_Util.format3 "The effect combinator is %s (n=%s) (%s)" error uu____1276 uu____1277)))
in (failwith uu____1275)))
end
| uu____1278 -> begin
()
end));
ts1;
))))
in (

let close_action = (fun act -> (

let uu____1283 = (close1 (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_defn)))
in (match (uu____1283) with
| (univs2, defn) -> begin
(

let uu____1288 = (close1 (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_typ)))
in (match (uu____1288) with
| (univs', typ) -> begin
(

let uu___91_1294 = act
in {FStar_Syntax_Syntax.action_name = uu___91_1294.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___91_1294.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs2; FStar_Syntax_Syntax.action_defn = defn; FStar_Syntax_Syntax.action_typ = typ})
end))
end)))
in (

let nunivs = (FStar_List.length univs1)
in (

let ed3 = (

let uu___92_1299 = ed2
in (

let uu____1300 = (close1 (Prims.parse_int "0") return_wp)
in (

let uu____1301 = (close1 (Prims.parse_int "1") bind_wp)
in (

let uu____1302 = (close1 (Prims.parse_int "0") if_then_else1)
in (

let uu____1303 = (close1 (Prims.parse_int "0") ite_wp)
in (

let uu____1304 = (close1 (Prims.parse_int "0") stronger)
in (

let uu____1305 = (close1 (Prims.parse_int "1") close_wp)
in (

let uu____1306 = (close1 (Prims.parse_int "0") assert_p)
in (

let uu____1307 = (close1 (Prims.parse_int "0") assume_p)
in (

let uu____1308 = (close1 (Prims.parse_int "0") null_wp)
in (

let uu____1309 = (close1 (Prims.parse_int "0") trivial_wp)
in (

let uu____1310 = (

let uu____1311 = (close1 (Prims.parse_int "0") (([]), (repr)))
in (Prims.snd uu____1311))
in (

let uu____1317 = (close1 (Prims.parse_int "0") return_repr)
in (

let uu____1318 = (close1 (Prims.parse_int "1") bind_repr)
in (

let uu____1319 = (FStar_List.map close_action actions)
in {FStar_Syntax_Syntax.qualifiers = uu___92_1299.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___92_1299.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___92_1299.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs1; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature1; FStar_Syntax_Syntax.ret_wp = uu____1300; FStar_Syntax_Syntax.bind_wp = uu____1301; FStar_Syntax_Syntax.if_then_else = uu____1302; FStar_Syntax_Syntax.ite_wp = uu____1303; FStar_Syntax_Syntax.stronger = uu____1304; FStar_Syntax_Syntax.close_wp = uu____1305; FStar_Syntax_Syntax.assert_p = uu____1306; FStar_Syntax_Syntax.assume_p = uu____1307; FStar_Syntax_Syntax.null_wp = uu____1308; FStar_Syntax_Syntax.trivial = uu____1309; FStar_Syntax_Syntax.repr = uu____1310; FStar_Syntax_Syntax.return_repr = uu____1317; FStar_Syntax_Syntax.bind_repr = uu____1318; FStar_Syntax_Syntax.actions = uu____1319})))))))))))))))
in ((

let uu____1322 = ((FStar_TypeChecker_Env.debug env1 FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("ED"))))
in (match (uu____1322) with
| true -> begin
(

let uu____1323 = (FStar_Syntax_Print.eff_decl_to_string false ed3)
in (FStar_Util.print_string uu____1323))
end
| uu____1324 -> begin
()
end));
ed3;
))))))
end)))
end)))))))))))));
)))
end)))))
end))
end))
end)))
and cps_and_elaborate : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.sigelt Prims.option) = (fun env ed -> (

let uu____1327 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____1327) with
| (effect_binders_un, signature_un) -> begin
(

let uu____1337 = (FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un)
in (match (uu____1337) with
| (effect_binders, env1, uu____1348) -> begin
(

let uu____1349 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un)
in (match (uu____1349) with
| (signature, uu____1358) -> begin
(

let effect_binders1 = (FStar_List.map (fun uu____1367 -> (match (uu____1367) with
| (bv, qual) -> begin
(

let uu____1374 = (

let uu___93_1375 = bv
in (

let uu____1376 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env1 bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___93_1375.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___93_1375.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1376}))
in ((uu____1374), (qual)))
end)) effect_binders)
in (

let uu____1379 = (

let uu____1384 = (

let uu____1385 = (FStar_Syntax_Subst.compress signature_un)
in uu____1385.FStar_Syntax_Syntax.n)
in (match (uu____1384) with
| FStar_Syntax_Syntax.Tm_arrow (((a, uu____1393))::[], effect_marker) -> begin
((a), (effect_marker))
end
| uu____1408 -> begin
(failwith "bad shape for effect-for-free signature")
end))
in (match (uu____1379) with
| (a, effect_marker) -> begin
(

let a1 = (

let uu____1425 = (FStar_Syntax_Syntax.is_null_bv a)
in (match (uu____1425) with
| true -> begin
(

let uu____1426 = (

let uu____1428 = (FStar_Syntax_Syntax.range_of_bv a)
in Some (uu____1428))
in (FStar_Syntax_Syntax.gen_bv "a" uu____1426 a.FStar_Syntax_Syntax.sort))
end
| uu____1429 -> begin
a
end))
in (

let open_and_check = (fun t -> (

let subst1 = (FStar_Syntax_Subst.opening_of_binders effect_binders1)
in (

let t1 = (FStar_Syntax_Subst.subst subst1 t)
in (

let uu____1438 = (FStar_TypeChecker_TcTerm.tc_term env1 t1)
in (match (uu____1438) with
| (t2, comp, uu____1446) -> begin
((t2), (comp))
end)))))
in (

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x None signature.FStar_Syntax_Syntax.pos))
in (

let uu____1457 = (open_and_check ed.FStar_Syntax_Syntax.repr)
in (match (uu____1457) with
| (repr, _comp) -> begin
((

let uu____1468 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____1468) with
| true -> begin
(

let uu____1469 = (FStar_Syntax_Print.term_to_string repr)
in (FStar_Util.print1 "Representation is: %s\n" uu____1469))
end
| uu____1470 -> begin
()
end));
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env1 (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange))
in (

let wp_type = (FStar_TypeChecker_DMFF.star_type dmff_env repr)
in (

let wp_type1 = (recheck_debug "*" env1 wp_type)
in (

let wp_a = (

let uu____1475 = (

let uu____1476 = (

let uu____1477 = (

let uu____1487 = (

let uu____1491 = (

let uu____1494 = (FStar_Syntax_Syntax.bv_to_name a1)
in (

let uu____1495 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____1494), (uu____1495))))
in (uu____1491)::[])
in ((wp_type1), (uu____1487)))
in FStar_Syntax_Syntax.Tm_app (uu____1477))
in (mk1 uu____1476))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env1 uu____1475))
in (

let effect_signature = (

let binders = (

let uu____1510 = (

let uu____1513 = (FStar_Syntax_Syntax.as_implicit false)
in ((a1), (uu____1513)))
in (

let uu____1514 = (

let uu____1518 = (

let uu____1519 = (FStar_Syntax_Syntax.gen_bv "dijkstra_wp" None wp_a)
in (FStar_All.pipe_right uu____1519 FStar_Syntax_Syntax.mk_binder))
in (uu____1518)::[])
in (uu____1510)::uu____1514))
in (

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in (mk1 (FStar_Syntax_Syntax.Tm_arrow (((binders1), (effect_marker)))))))
in (

let effect_signature1 = (recheck_debug "turned into the effect signature" env1 effect_signature)
in (

let sigelts = (FStar_Util.mk_ref [])
in (

let mk_lid = (fun name -> (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" name))) FStar_Range.dummyRange))
in (

let elaborate_and_star = (fun dmff_env1 item -> (

let uu____1552 = item
in (match (uu____1552) with
| (u_item, item1) -> begin
(

let uu____1564 = (open_and_check item1)
in (match (uu____1564) with
| (item2, item_comp) -> begin
((

let uu____1574 = (

let uu____1575 = (FStar_Syntax_Util.is_total_lcomp item_comp)
in (not (uu____1575)))
in (match (uu____1574) with
| true -> begin
(

let uu____1576 = (

let uu____1577 = (

let uu____1578 = (FStar_Syntax_Print.term_to_string item2)
in (

let uu____1579 = (FStar_Syntax_Print.lcomp_to_string item_comp)
in (FStar_Util.format2 "Computation for [%s] is not total : %s !" uu____1578 uu____1579)))
in FStar_Errors.Err (uu____1577))
in (Prims.raise uu____1576))
end
| uu____1580 -> begin
()
end));
(

let uu____1581 = (FStar_TypeChecker_DMFF.star_expr dmff_env1 item2)
in (match (uu____1581) with
| (item_t, item_wp, item_elab) -> begin
(

let item_wp1 = (recheck_debug "*" env1 item_wp)
in (

let item_elab1 = (recheck_debug "_" env1 item_elab)
in ((dmff_env1), (item_t), (item_wp1), (item_elab1))))
end));
)
end))
end)))
in (

let uu____1594 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.bind_repr)
in (match (uu____1594) with
| (dmff_env1, uu____1605, bind_wp, bind_elab) -> begin
(

let uu____1608 = (elaborate_and_star dmff_env1 ed.FStar_Syntax_Syntax.return_repr)
in (match (uu____1608) with
| (dmff_env2, uu____1619, return_wp, return_elab) -> begin
(

let lift_from_pure_wp = (

let uu____1623 = (

let uu____1624 = (FStar_Syntax_Subst.compress return_wp)
in uu____1624.FStar_Syntax_Syntax.n)
in (match (uu____1623) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(

let uu____1662 = (

let uu____1670 = (

let uu____1673 = (FStar_Syntax_Util.abs bs body None)
in (FStar_Syntax_Subst.open_term ((b1)::(b2)::[]) uu____1673))
in (match (uu____1670) with
| ((b11)::(b21)::[], body1) -> begin
((b11), (b21), (body1))
end
| uu____1712 -> begin
(failwith "Impossible : open_term not preserving binders arity")
end))
in (match (uu____1662) with
| (b11, b21, body1) -> begin
(

let env0 = (

let uu____1734 = (FStar_TypeChecker_DMFF.get_env dmff_env2)
in (FStar_TypeChecker_Env.push_binders uu____1734 ((b11)::(b21)::[])))
in (

let wp_b1 = (

let raw_wp_b1 = (

let uu____1745 = (

let uu____1746 = (

let uu____1756 = (

let uu____1760 = (

let uu____1763 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b11))
in (

let uu____1764 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____1763), (uu____1764))))
in (uu____1760)::[])
in ((wp_type1), (uu____1756)))
in FStar_Syntax_Syntax.Tm_app (uu____1746))
in (mk1 uu____1745))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env0 raw_wp_b1))
in (

let uu____1772 = (

let uu____1782 = (

let uu____1783 = (FStar_Syntax_Util.unascribe wp_b1)
in (FStar_TypeChecker_Normalize.eta_expand_with_type body1 uu____1783))
in (FStar_All.pipe_left FStar_Syntax_Util.abs_formals uu____1782))
in (match (uu____1772) with
| (bs1, body2, what') -> begin
(

let fail = (fun uu____1811 -> (

let error_msg = (

let uu____1813 = (FStar_Syntax_Print.term_to_string body2)
in (

let uu____1814 = (match (what') with
| None -> begin
"None"
end
| Some (FStar_Util.Inl (lc)) -> begin
(FStar_Syntax_Print.lcomp_to_string lc)
end
| Some (FStar_Util.Inr (lid, uu____1830)) -> begin
(FStar_Ident.text_of_lid lid)
end)
in (FStar_Util.format2 "The body of return_wp (%s) should be of type Type0 but is of type %s" uu____1813 uu____1814)))
in (failwith error_msg)))
in ((match (what') with
| None -> begin
(fail ())
end
| Some (FStar_Util.Inl (lc)) -> begin
(

let uu____1856 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)
in (match (uu____1856) with
| true -> begin
(

let g_opt = (FStar_TypeChecker_Rel.try_teq true env1 lc.FStar_Syntax_Syntax.res_typ FStar_Syntax_Util.ktype0)
in (match (g_opt) with
| Some (g') -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env1 g')
end
| None -> begin
(fail ())
end))
end
| uu____1860 -> begin
(fail ())
end))
end
| Some (FStar_Util.Inr (lid, uu____1862)) -> begin
(match ((not ((FStar_Syntax_Util.is_pure_effect lid)))) with
| true -> begin
(fail ())
end
| uu____1873 -> begin
()
end)
end);
(

let wp = (

let t2 = (Prims.fst b21).FStar_Syntax_Syntax.sort
in (

let pure_wp_type = (FStar_TypeChecker_DMFF.double_star t2)
in (FStar_Syntax_Syntax.gen_bv "wp" None pure_wp_type)))
in (

let body3 = (

let uu____1882 = (

let uu____1883 = (FStar_Syntax_Syntax.bv_to_name wp)
in (

let uu____1884 = (

let uu____1885 = (

let uu____1889 = (FStar_Syntax_Util.abs ((b21)::[]) body2 what')
in ((uu____1889), (None)))
in (uu____1885)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____1883 uu____1884)))
in (uu____1882 None FStar_Range.dummyRange))
in (

let uu____1905 = (

let uu____1909 = (

let uu____1913 = (FStar_Syntax_Syntax.mk_binder wp)
in (uu____1913)::[])
in (b11)::uu____1909)
in (

let uu____1916 = (FStar_Syntax_Util.abs bs1 body3 what)
in (FStar_Syntax_Util.abs uu____1905 uu____1916 (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_GTot_lid), ([]))))))))));
))
end))))
end))
end
| uu____1926 -> begin
(failwith "unexpected shape for return")
end))
in (

let return_wp1 = (

let uu____1928 = (

let uu____1929 = (FStar_Syntax_Subst.compress return_wp)
in uu____1929.FStar_Syntax_Syntax.n)
in (match (uu____1928) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(

let uu____1967 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs ((b1)::(b2)::[]) uu____1967 (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_GTot_lid), ([])))))))
end
| uu____1983 -> begin
(failwith "unexpected shape for return")
end))
in (

let bind_wp1 = (

let uu____1985 = (

let uu____1986 = (FStar_Syntax_Subst.compress bind_wp)
in uu____1986.FStar_Syntax_Syntax.n)
in (match (uu____1985) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let r = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (

let uu____2015 = (

let uu____2019 = (

let uu____2021 = (

let uu____2022 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (r)))
in (FStar_Syntax_Syntax.null_binder uu____2022))
in (uu____2021)::[])
in (FStar_List.append uu____2019 binders))
in (FStar_Syntax_Util.abs uu____2015 body what)))
end
| uu____2023 -> begin
(failwith "unexpected shape for bind")
end))
in (

let apply_close = (fun t -> (match (((FStar_List.length effect_binders1) = (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____2040 -> begin
(

let uu____2041 = (

let uu____2042 = (

let uu____2043 = (

let uu____2053 = (

let uu____2054 = (FStar_Syntax_Util.args_of_binders effect_binders1)
in (Prims.snd uu____2054))
in ((t), (uu____2053)))
in FStar_Syntax_Syntax.Tm_app (uu____2043))
in (mk1 uu____2042))
in (FStar_Syntax_Subst.close effect_binders1 uu____2041))
end))
in (

let register = (fun name item -> (

let uu____2066 = (

let uu____2069 = (mk_lid name)
in (

let uu____2070 = (FStar_Syntax_Util.abs effect_binders1 item None)
in (FStar_TypeChecker_Util.mk_toplevel_definition env1 uu____2069 uu____2070)))
in (match (uu____2066) with
| (sigelt, fv) -> begin
((

let uu____2079 = (

let uu____2081 = (FStar_ST.read sigelts)
in (sigelt)::uu____2081)
in (FStar_ST.write sigelts uu____2079));
fv;
)
end)))
in (

let lift_from_pure_wp1 = (register "lift_from_pure" lift_from_pure_wp)
in (

let return_wp2 = (register "return_wp" return_wp1)
in ((

let uu____2092 = (

let uu____2094 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true"))))
in (

let uu____2095 = (FStar_ST.read sigelts)
in (uu____2094)::uu____2095))
in (FStar_ST.write sigelts uu____2092));
(

let return_elab1 = (register "return_elab" return_elab)
in ((

let uu____2105 = (

let uu____2107 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false"))))
in (

let uu____2108 = (FStar_ST.read sigelts)
in (uu____2107)::uu____2108))
in (FStar_ST.write sigelts uu____2105));
(

let bind_wp2 = (register "bind_wp" bind_wp1)
in ((

let uu____2118 = (

let uu____2120 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true"))))
in (

let uu____2121 = (FStar_ST.read sigelts)
in (uu____2120)::uu____2121))
in (FStar_ST.write sigelts uu____2118));
(

let bind_elab1 = (register "bind_elab" bind_elab)
in ((

let uu____2131 = (

let uu____2133 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false"))))
in (

let uu____2134 = (FStar_ST.read sigelts)
in (uu____2133)::uu____2134))
in (FStar_ST.write sigelts uu____2131));
(

let uu____2142 = (FStar_List.fold_left (fun uu____2149 action -> (match (uu____2149) with
| (dmff_env3, actions) -> begin
(

let uu____2161 = (elaborate_and_star dmff_env3 ((action.FStar_Syntax_Syntax.action_univs), (action.FStar_Syntax_Syntax.action_defn)))
in (match (uu____2161) with
| (dmff_env4, action_t, action_wp, action_elab) -> begin
(

let name = action.FStar_Syntax_Syntax.action_name.FStar_Ident.ident.FStar_Ident.idText
in (

let action_typ_with_wp = (FStar_TypeChecker_DMFF.trans_F dmff_env4 action_t action_wp)
in (

let action_elab1 = (register (Prims.strcat name "_elab") action_elab)
in (

let action_typ_with_wp1 = (register (Prims.strcat name "_complete_type") action_typ_with_wp)
in (

let uu____2177 = (

let uu____2179 = (

let uu___94_2180 = action
in (

let uu____2181 = (apply_close action_elab1)
in (

let uu____2182 = (apply_close action_typ_with_wp1)
in {FStar_Syntax_Syntax.action_name = uu___94_2180.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___94_2180.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___94_2180.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = uu____2181; FStar_Syntax_Syntax.action_typ = uu____2182})))
in (uu____2179)::actions)
in ((dmff_env4), (uu____2177)))))))
end))
end)) ((dmff_env2), ([])) ed.FStar_Syntax_Syntax.actions)
in (match (uu____2142) with
| (dmff_env3, actions) -> begin
(

let actions1 = (FStar_List.rev actions)
in (

let repr1 = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp_a" None wp_a)
in (

let binders = (

let uu____2200 = (FStar_Syntax_Syntax.mk_binder a1)
in (

let uu____2201 = (

let uu____2203 = (FStar_Syntax_Syntax.mk_binder wp)
in (uu____2203)::[])
in (uu____2200)::uu____2201))
in (

let uu____2204 = (

let uu____2205 = (

let uu____2206 = (

let uu____2207 = (

let uu____2217 = (

let uu____2221 = (

let uu____2224 = (FStar_Syntax_Syntax.bv_to_name a1)
in (

let uu____2225 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____2224), (uu____2225))))
in (uu____2221)::[])
in ((repr), (uu____2217)))
in FStar_Syntax_Syntax.Tm_app (uu____2207))
in (mk1 uu____2206))
in (

let uu____2233 = (FStar_Syntax_Syntax.bv_to_name wp)
in (FStar_TypeChecker_DMFF.trans_F dmff_env3 uu____2205 uu____2233)))
in (FStar_Syntax_Util.abs binders uu____2204 None))))
in (

let repr2 = (recheck_debug "FC" env1 repr1)
in (

let repr3 = (register "repr" repr2)
in (

let uu____2241 = (

let uu____2246 = (

let uu____2247 = (

let uu____2250 = (FStar_Syntax_Subst.compress wp_type1)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____2250))
in uu____2247.FStar_Syntax_Syntax.n)
in (match (uu____2246) with
| FStar_Syntax_Syntax.Tm_abs ((type_param)::effect_param, arrow1, uu____2258) -> begin
(

let uu____2285 = (

let uu____2294 = (FStar_Syntax_Subst.open_term ((type_param)::effect_param) arrow1)
in (match (uu____2294) with
| ((b)::bs, body) -> begin
((b), (bs), (body))
end
| uu____2325 -> begin
(failwith "Impossible : open_term nt preserving binders arity")
end))
in (match (uu____2285) with
| (type_param1, effect_param1, arrow2) -> begin
(

let uu____2353 = (

let uu____2354 = (

let uu____2357 = (FStar_Syntax_Subst.compress arrow2)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____2357))
in uu____2354.FStar_Syntax_Syntax.n)
in (match (uu____2353) with
| FStar_Syntax_Syntax.Tm_arrow (wp_binders, c) -> begin
(

let uu____2374 = (FStar_Syntax_Subst.open_comp wp_binders c)
in (match (uu____2374) with
| (wp_binders1, c1) -> begin
(

let uu____2383 = (FStar_List.partition (fun uu____2394 -> (match (uu____2394) with
| (bv, uu____2398) -> begin
(

let uu____2399 = (

let uu____2400 = (FStar_Syntax_Free.names bv.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____2400 (FStar_Util.set_mem (Prims.fst type_param1))))
in (FStar_All.pipe_right uu____2399 Prims.op_Negation))
end)) wp_binders1)
in (match (uu____2383) with
| (pre_args, post_args) -> begin
(

let post = (match (post_args) with
| (post)::[] -> begin
post
end
| uu____2433 -> begin
(

let uu____2437 = (

let uu____2438 = (FStar_Syntax_Print.term_to_string arrow2)
in (FStar_Util.format1 "Impossible: multiple post candidates %s" uu____2438))
in (failwith uu____2437))
end)
in (

let uu____2441 = (FStar_Syntax_Util.arrow pre_args c1)
in (

let uu____2444 = (FStar_Syntax_Util.abs ((type_param1)::effect_param1) (Prims.fst post).FStar_Syntax_Syntax.sort None)
in ((uu____2441), (uu____2444)))))
end))
end))
end
| uu____2454 -> begin
(

let uu____2455 = (

let uu____2456 = (FStar_Syntax_Print.term_to_string arrow2)
in (FStar_Util.format1 "Impossible: pre/post arrow %s" uu____2456))
in (failwith uu____2455))
end))
end))
end
| uu____2461 -> begin
(

let uu____2462 = (

let uu____2463 = (FStar_Syntax_Print.term_to_string wp_type1)
in (FStar_Util.format1 "Impossible: pre/post abs %s" uu____2463))
in (failwith uu____2462))
end))
in (match (uu____2241) with
| (pre, post) -> begin
((

let uu____2480 = (register "pre" pre)
in ());
(

let uu____2482 = (register "post" post)
in ());
(

let uu____2484 = (register "wp" wp_type1)
in ());
(

let ed1 = (

let uu___95_2486 = ed
in (

let uu____2487 = (FStar_Syntax_Subst.close_binders effect_binders1)
in (

let uu____2488 = (FStar_Syntax_Subst.close effect_binders1 effect_signature1)
in (

let uu____2489 = (

let uu____2490 = (apply_close return_wp2)
in (([]), (uu____2490)))
in (

let uu____2496 = (

let uu____2497 = (apply_close bind_wp2)
in (([]), (uu____2497)))
in (

let uu____2503 = (apply_close repr3)
in (

let uu____2504 = (

let uu____2505 = (apply_close return_elab1)
in (([]), (uu____2505)))
in (

let uu____2511 = (

let uu____2512 = (apply_close bind_elab1)
in (([]), (uu____2512)))
in {FStar_Syntax_Syntax.qualifiers = uu___95_2486.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___95_2486.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___95_2486.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___95_2486.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu____2487; FStar_Syntax_Syntax.signature = uu____2488; FStar_Syntax_Syntax.ret_wp = uu____2489; FStar_Syntax_Syntax.bind_wp = uu____2496; FStar_Syntax_Syntax.if_then_else = uu___95_2486.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = uu___95_2486.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = uu___95_2486.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = uu___95_2486.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = uu___95_2486.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = uu___95_2486.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = uu___95_2486.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = uu___95_2486.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = uu____2503; FStar_Syntax_Syntax.return_repr = uu____2504; FStar_Syntax_Syntax.bind_repr = uu____2511; FStar_Syntax_Syntax.actions = actions1}))))))))
in (

let uu____2518 = (FStar_TypeChecker_DMFF.gen_wps_for_free env1 effect_binders1 a1 wp_a ed1)
in (match (uu____2518) with
| (sigelts', ed2) -> begin
((

let uu____2529 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____2529) with
| true -> begin
(

let uu____2530 = (FStar_Syntax_Print.eff_decl_to_string true ed2)
in (FStar_Util.print_string uu____2530))
end
| uu____2531 -> begin
()
end));
(

let lift_from_pure_opt = (match (((FStar_List.length effect_binders1) = (Prims.parse_int "0"))) with
| true -> begin
(

let lift_from_pure = (

let uu____2540 = (

let uu____2542 = (

let uu____2548 = (apply_close lift_from_pure_wp1)
in (([]), (uu____2548)))
in Some (uu____2542))
in {FStar_Syntax_Syntax.source = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.target = ed2.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.lift_wp = uu____2540; FStar_Syntax_Syntax.lift = None})
in (

let uu____2559 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_sub_effect (lift_from_pure)))
in Some (uu____2559)))
end
| uu____2560 -> begin
None
end)
in (

let uu____2561 = (

let uu____2563 = (

let uu____2565 = (FStar_ST.read sigelts)
in (FStar_List.rev uu____2565))
in (FStar_List.append uu____2563 sigelts'))
in ((uu____2561), (ed2), (lift_from_pure_opt))));
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
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (lex_t1, [], [], t, uu____2588, uu____2589, []); FStar_Syntax_Syntax.sigdoc = d; FStar_Syntax_Syntax.sigrng = r})::({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (lex_top1, [], _t_top, _lex_t_top, _0_28, [], uu____2595); FStar_Syntax_Syntax.sigdoc = d1; FStar_Syntax_Syntax.sigrng = r1})::({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, _0_29, [], uu____2601); FStar_Syntax_Syntax.sigdoc = d2; FStar_Syntax_Syntax.sigrng = r2})::[] when (((_0_28 = (Prims.parse_int "0")) && (_0_29 = (Prims.parse_int "0"))) && (((FStar_Ident.lid_equals lex_t1 FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top1 FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid))) -> begin
(

let u = (FStar_Syntax_Syntax.new_univ_name (Some (r)))
in (

let t1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) None r)
in (

let t2 = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t1)
in (

let tc = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((lex_t1), ((u)::[]), ([]), (t2), ([]), ((FStar_Syntax_Const.lextop_lid)::(FStar_Syntax_Const.lexcons_lid)::[]), ([]))); FStar_Syntax_Syntax.sigdoc = d; FStar_Syntax_Syntax.sigrng = r}
in (

let utop = (FStar_Syntax_Syntax.new_univ_name (Some (r1)))
in (

let lex_top_t = (

let uu____2649 = (

let uu____2652 = (

let uu____2653 = (

let uu____2658 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1) FStar_Syntax_Syntax.Delta_constant None)
in ((uu____2658), ((FStar_Syntax_Syntax.U_name (utop))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____2653))
in (FStar_Syntax_Syntax.mk uu____2652))
in (uu____2649 None r1))
in (

let lex_top_t1 = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (

let dc_lextop = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((lex_top1), ((utop)::[]), (lex_top_t1), (FStar_Syntax_Const.lex_t_lid), ((Prims.parse_int "0")), ([]), ([]))); FStar_Syntax_Syntax.sigdoc = d1; FStar_Syntax_Syntax.sigrng = r1}
in (

let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (

let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (

let lex_cons_t = (

let a = (

let uu____2679 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) uu____2679))
in (

let hd1 = (

let uu____2685 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) uu____2685))
in (

let tl1 = (

let uu____2687 = (

let uu____2688 = (

let uu____2691 = (

let uu____2692 = (

let uu____2697 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2) FStar_Syntax_Syntax.Delta_constant None)
in ((uu____2697), ((FStar_Syntax_Syntax.U_name (ucons2))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____2692))
in (FStar_Syntax_Syntax.mk uu____2691))
in (uu____2688 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) uu____2687))
in (

let res = (

let uu____2710 = (

let uu____2713 = (

let uu____2714 = (

let uu____2719 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2) FStar_Syntax_Syntax.Delta_constant None)
in ((uu____2719), ((FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____2714))
in (FStar_Syntax_Syntax.mk uu____2713))
in (uu____2710 None r2))
in (

let uu____2729 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow ((((a), (Some (FStar_Syntax_Syntax.imp_tag))))::(((hd1), (None)))::(((tl1), (None)))::[]) uu____2729))))))
in (

let lex_cons_t1 = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((lex_cons), ((ucons1)::(ucons2)::[]), (lex_cons_t1), (FStar_Syntax_Const.lex_t_lid), ((Prims.parse_int "0")), ([]), ([]))); FStar_Syntax_Syntax.sigdoc = d2; FStar_Syntax_Syntax.sigrng = r2}
in (

let uu____2752 = (FStar_TypeChecker_Env.get_range env)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle ((((tc)::(dc_lextop)::(dc_lexcons)::[]), ([]), (lids))); FStar_Syntax_Syntax.sigdoc = None; FStar_Syntax_Syntax.sigrng = uu____2752}))))))))))))))
end
| uu____2756 -> begin
(

let uu____2758 = (

let uu____2759 = (

let uu____2760 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_bundle (((ses), ([]), (lids)))))
in (FStar_Syntax_Print.sigelt_to_string uu____2760))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" uu____2759))
in (failwith uu____2758))
end))
and tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env1 = (FStar_TypeChecker_Env.set_range env r)
in (

let uu____2771 = (FStar_Syntax_Util.type_u ())
in (match (uu____2771) with
| (k, uu____2775) -> begin
(

let phi1 = (

let uu____2777 = (tc_check_trivial_guard env1 phi k)
in (FStar_All.pipe_right uu____2777 (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env1)))
in ((FStar_TypeChecker_Util.check_uvars r phi1);
{FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_assume (((lid), (phi1), (quals))); FStar_Syntax_Syntax.sigdoc = None; FStar_Syntax_Syntax.sigrng = r};
))
end))))
and tc_inductive : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env ses quals lids -> (

let env0 = env
in (

let uu____2788 = (FStar_TypeChecker_TcInductive.check_inductive_well_typedness env ses quals lids)
in (match (uu____2788) with
| (sig_bndle, tcs, datas) -> begin
(

let data_ops_ses = (

let uu____2807 = (FStar_List.map (FStar_TypeChecker_Util.mk_data_operations quals env tcs) datas)
in (FStar_All.pipe_right uu____2807 FStar_List.flatten))
in ((

let uu____2815 = ((FStar_Options.no_positivity ()) || (FStar_Options.lax ()))
in (match (uu____2815) with
| true -> begin
()
end
| uu____2816 -> begin
(

let env1 = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (FStar_List.iter (fun ty -> (

let b = (FStar_TypeChecker_TcInductive.check_positivity ty env1)
in (match ((not (b))) with
| true -> begin
(

let uu____2821 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____2827, uu____2828, uu____2829, uu____2830, uu____2831, uu____2832) -> begin
((lid), (ty.FStar_Syntax_Syntax.sigrng))
end
| uu____2839 -> begin
(failwith "Impossible!")
end)
in (match (uu____2821) with
| (lid, r) -> begin
(FStar_Errors.report r (Prims.strcat "Inductive type " (Prims.strcat lid.FStar_Ident.str " does not satisfy the positivity condition")))
end))
end
| uu____2844 -> begin
()
end))) tcs))
end));
(

let skip_prims_type = (fun uu____2848 -> (

let lid = (

let ty = (FStar_List.hd tcs)
in (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____2852, uu____2853, uu____2854, uu____2855, uu____2856, uu____2857) -> begin
lid
end
| uu____2864 -> begin
(failwith "Impossible")
end))
in (

let types_to_skip = ("c_False")::("c_True")::("equals")::("h_equals")::("c_and")::("c_or")::[]
in (FStar_List.existsb (fun s -> (s = lid.FStar_Ident.ident.FStar_Ident.idText)) types_to_skip))))
in (

let is_noeq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Noeq)) quals)
in (

let uu____2870 = ((((FStar_List.length tcs) = (Prims.parse_int "0")) || ((FStar_Ident.lid_equals env.FStar_TypeChecker_Env.curmodule FStar_Syntax_Const.prims_lid) && (skip_prims_type ()))) || is_noeq)
in (match (uu____2870) with
| true -> begin
(((sig_bndle)::[]), (data_ops_ses))
end
| uu____2879 -> begin
(

let is_unopteq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Unopteq)) quals)
in (

let ses1 = (match (is_unopteq) with
| true -> begin
(FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme sig_bndle tcs datas env0 tc_assume)
end
| uu____2885 -> begin
(FStar_TypeChecker_TcInductive.optimized_haseq_scheme sig_bndle tcs datas env0 tc_assume)
end)
in (

let uu____2886 = (

let uu____2888 = (

let uu____2889 = (FStar_TypeChecker_Env.get_range env0)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle ((((FStar_List.append tcs datas)), (quals), (lids))); FStar_Syntax_Syntax.sigdoc = None; FStar_Syntax_Syntax.sigrng = uu____2889})
in (uu____2888)::ses1)
in ((uu____2886), (data_ops_ses)))))
end))));
))
end))))
and tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env se -> (

let env1 = (set_hint_correlator env se)
in ((FStar_TypeChecker_Util.check_sigelt_quals env1 se);
(

let r = se.FStar_Syntax_Syntax.sigrng
in (match (se.FStar_Syntax_Syntax.sigel) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_range env1 r)
in (

let se1 = (tc_lex_t env2 ses quals lids)
in (

let uu____2929 = (FStar_TypeChecker_Env.push_sigelt env2 se1)
in (((se1)::[]), (uu____2929), ([])))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_range env1 r)
in (

let uu____2942 = (tc_inductive env2 ses quals lids)
in (match (uu____2942) with
| (ses1, projectors_ses) -> begin
(

let env3 = (FStar_List.fold_left (fun env' se1 -> (FStar_TypeChecker_Env.push_sigelt env' se1)) env2 ses1)
in ((ses1), (env3), (projectors_ses)))
end)))
end
| FStar_Syntax_Syntax.Sig_pragma (p) -> begin
(

let set_options1 = (fun t s -> (

let uu____2971 = (FStar_Options.set_options t s)
in (match (uu____2971) with
| FStar_Getopt.Success -> begin
()
end
| FStar_Getopt.Help -> begin
(Prims.raise (FStar_Errors.Error ((("Failed to process pragma: use \'fstar --help\' to see which options are available"), (r)))))
end
| FStar_Getopt.Error (s1) -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Failed to process pragma: " s1)), (r)))))
end)))
in (match (p) with
| FStar_Syntax_Syntax.LightOff -> begin
((match ((p = FStar_Syntax_Syntax.LightOff)) with
| true -> begin
(FStar_Options.set_ml_ish ())
end
| uu____2979 -> begin
()
end);
(((se)::[]), (env1), ([]));
)
end
| FStar_Syntax_Syntax.SetOptions (o) -> begin
((set_options1 FStar_Options.Set o);
(((se)::[]), (env1), ([]));
)
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
((

let uu____2989 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____2989 Prims.ignore));
(match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options1 FStar_Options.Reset s)
end);
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
(((se)::[]), (env1), ([]));
)
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne) -> begin
(

let uu____2996 = (cps_and_elaborate env1 ne)
in (match (uu____2996) with
| (ses, ne1, lift_from_pure_opt) -> begin
(

let effect_and_lift_ses = (match (lift_from_pure_opt) with
| Some (lift) -> begin
((

let uu___96_3018 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne1); FStar_Syntax_Syntax.sigdoc = uu___96_3018.FStar_Syntax_Syntax.sigdoc; FStar_Syntax_Syntax.sigrng = uu___96_3018.FStar_Syntax_Syntax.sigrng}))::(lift)::[]
end
| None -> begin
((

let uu___97_3019 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne1); FStar_Syntax_Syntax.sigdoc = uu___97_3019.FStar_Syntax_Syntax.sigdoc; FStar_Syntax_Syntax.sigrng = uu___97_3019.FStar_Syntax_Syntax.sigrng}))::[]
end)
in (([]), (env1), ((FStar_List.append ses effect_and_lift_ses))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let ne1 = (tc_eff_decl env1 ne)
in (

let se1 = (

let uu___98_3025 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne1); FStar_Syntax_Syntax.sigdoc = uu___98_3025.FStar_Syntax_Syntax.sigdoc; FStar_Syntax_Syntax.sigrng = uu___98_3025.FStar_Syntax_Syntax.sigrng})
in (

let env2 = (FStar_TypeChecker_Env.push_sigelt env1 se1)
in (

let uu____3027 = (FStar_All.pipe_right ne1.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun uu____3038 a -> (match (uu____3038) with
| (env3, ses) -> begin
(

let se_let = (FStar_Syntax_Util.action_as_lb ne1.FStar_Syntax_Syntax.mname a)
in (

let uu____3051 = (FStar_TypeChecker_Env.push_sigelt env3 se_let)
in ((uu____3051), ((se_let)::ses))))
end)) ((env2), ((se1)::[]))))
in (match (uu____3027) with
| (env3, ses) -> begin
(((se1)::[]), (env3), ([]))
end)))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub1) -> begin
(

let ed_src = (FStar_TypeChecker_Env.get_effect_decl env1 sub1.FStar_Syntax_Syntax.source)
in (

let ed_tgt = (FStar_TypeChecker_Env.get_effect_decl env1 sub1.FStar_Syntax_Syntax.target)
in (

let uu____3068 = (

let uu____3073 = (FStar_TypeChecker_Env.lookup_effect_lid env1 sub1.FStar_Syntax_Syntax.source)
in (monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____3073))
in (match (uu____3068) with
| (a, wp_a_src) -> begin
(

let uu____3085 = (

let uu____3090 = (FStar_TypeChecker_Env.lookup_effect_lid env1 sub1.FStar_Syntax_Syntax.target)
in (monad_signature env1 sub1.FStar_Syntax_Syntax.target uu____3090))
in (match (uu____3085) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (

let uu____3103 = (

let uu____3105 = (

let uu____3106 = (

let uu____3111 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (uu____3111)))
in FStar_Syntax_Syntax.NT (uu____3106))
in (uu____3105)::[])
in (FStar_Syntax_Subst.subst uu____3103 wp_b_tgt))
in (

let expected_k = (

let uu____3115 = (

let uu____3119 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____3120 = (

let uu____3122 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (uu____3122)::[])
in (uu____3119)::uu____3120))
in (

let uu____3123 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow uu____3115 uu____3123)))
in (

let repr_type = (fun eff_name a1 wp -> (

let no_reify = (fun l -> (

let uu____3144 = (

let uu____3145 = (

let uu____3148 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (

let uu____3149 = (FStar_TypeChecker_Env.get_range env1)
in ((uu____3148), (uu____3149))))
in FStar_Errors.Error (uu____3145))
in (Prims.raise uu____3144)))
in (

let uu____3152 = (FStar_TypeChecker_Env.effect_decl_opt env1 eff_name)
in (match (uu____3152) with
| None -> begin
(no_reify eff_name)
end
| Some (ed) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((FStar_Syntax_Syntax.U_unknown)::[]) env1 ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let uu____3159 = (

let uu____3160 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (not (uu____3160)))
in (match (uu____3159) with
| true -> begin
(no_reify eff_name)
end
| uu____3164 -> begin
(

let uu____3165 = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____3166 = (

let uu____3169 = (

let uu____3170 = (

let uu____3180 = (

let uu____3182 = (FStar_Syntax_Syntax.as_arg a1)
in (

let uu____3183 = (

let uu____3185 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____3185)::[])
in (uu____3182)::uu____3183))
in ((repr), (uu____3180)))
in FStar_Syntax_Syntax.Tm_app (uu____3170))
in (FStar_Syntax_Syntax.mk uu____3169))
in (uu____3166 None uu____3165)))
end)))
end))))
in (

let uu____3195 = (match (((sub1.FStar_Syntax_Syntax.lift), (sub1.FStar_Syntax_Syntax.lift_wp))) with
| (None, None) -> begin
(failwith "Impossible")
end
| (lift, Some (uu____3210, lift_wp)) -> begin
(

let uu____3223 = (check_and_gen env1 lift_wp expected_k)
in ((lift), (uu____3223)))
end
| (Some (what, lift), None) -> begin
((

let uu____3238 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____3238) with
| true -> begin
(

let uu____3239 = (FStar_Syntax_Print.term_to_string lift)
in (FStar_Util.print1 "Lift for free : %s\n" uu____3239))
end
| uu____3240 -> begin
()
end));
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env1 (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange))
in (

let uu____3242 = (FStar_TypeChecker_TcTerm.tc_term env1 lift)
in (match (uu____3242) with
| (lift1, comp, uu____3251) -> begin
(

let uu____3252 = (FStar_TypeChecker_DMFF.star_expr dmff_env lift1)
in (match (uu____3252) with
| (uu____3259, lift_wp, lift_elab) -> begin
(

let uu____3262 = (recheck_debug "lift-wp" env1 lift_wp)
in (

let uu____3263 = (recheck_debug "lift-elab" env1 lift_elab)
in ((Some ((([]), (lift_elab)))), ((([]), (lift_wp))))))
end))
end)));
)
end)
in (match (uu____3195) with
| (lift, lift_wp) -> begin
(

let lax1 = env1.FStar_TypeChecker_Env.lax
in (

let env2 = (

let uu___99_3287 = env1
in {FStar_TypeChecker_Env.solver = uu___99_3287.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___99_3287.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___99_3287.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___99_3287.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___99_3287.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___99_3287.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___99_3287.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___99_3287.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___99_3287.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___99_3287.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___99_3287.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___99_3287.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___99_3287.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___99_3287.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___99_3287.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___99_3287.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___99_3287.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___99_3287.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___99_3287.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___99_3287.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___99_3287.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___99_3287.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___99_3287.FStar_TypeChecker_Env.qname_and_index})
in (

let lift1 = (match (lift) with
| None -> begin
None
end
| Some (uu____3291, lift1) -> begin
(

let uu____3298 = (

let uu____3303 = (FStar_TypeChecker_Env.lookup_effect_lid env2 sub1.FStar_Syntax_Syntax.source)
in (monad_signature env2 sub1.FStar_Syntax_Syntax.source uu____3303))
in (match (uu____3298) with
| (a1, wp_a_src1) -> begin
(

let wp_a = (FStar_Syntax_Syntax.new_bv None wp_a_src1)
in (

let a_typ = (FStar_Syntax_Syntax.bv_to_name a1)
in (

let wp_a_typ = (FStar_Syntax_Syntax.bv_to_name wp_a)
in (

let repr_f = (repr_type sub1.FStar_Syntax_Syntax.source a_typ wp_a_typ)
in (

let repr_result = (

let lift_wp1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env2 (Prims.snd lift_wp))
in (

let lift_wp_a = (

let uu____3325 = (FStar_TypeChecker_Env.get_range env2)
in (

let uu____3326 = (

let uu____3329 = (

let uu____3330 = (

let uu____3340 = (

let uu____3342 = (FStar_Syntax_Syntax.as_arg a_typ)
in (

let uu____3343 = (

let uu____3345 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (uu____3345)::[])
in (uu____3342)::uu____3343))
in ((lift_wp1), (uu____3340)))
in FStar_Syntax_Syntax.Tm_app (uu____3330))
in (FStar_Syntax_Syntax.mk uu____3329))
in (uu____3326 None uu____3325)))
in (repr_type sub1.FStar_Syntax_Syntax.target a_typ lift_wp_a)))
in (

let expected_k1 = (

let uu____3358 = (

let uu____3362 = (FStar_Syntax_Syntax.mk_binder a1)
in (

let uu____3363 = (

let uu____3365 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (

let uu____3366 = (

let uu____3368 = (FStar_Syntax_Syntax.null_binder repr_f)
in (uu____3368)::[])
in (uu____3365)::uu____3366))
in (uu____3362)::uu____3363))
in (

let uu____3369 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow uu____3358 uu____3369)))
in (

let uu____3372 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env2 expected_k1)
in (match (uu____3372) with
| (expected_k2, uu____3378, uu____3379) -> begin
(

let lift2 = (check_and_gen env2 lift1 expected_k2)
in Some (lift2))
end))))))))
end))
end)
in (

let env3 = (

let uu___100_3382 = env2
in {FStar_TypeChecker_Env.solver = uu___100_3382.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___100_3382.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___100_3382.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___100_3382.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___100_3382.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___100_3382.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___100_3382.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___100_3382.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___100_3382.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___100_3382.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___100_3382.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___100_3382.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___100_3382.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___100_3382.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___100_3382.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___100_3382.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___100_3382.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___100_3382.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = lax1; FStar_TypeChecker_Env.lax_universes = uu___100_3382.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___100_3382.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___100_3382.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___100_3382.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___100_3382.FStar_TypeChecker_Env.qname_and_index})
in (

let sub2 = (

let uu___101_3384 = sub1
in {FStar_Syntax_Syntax.source = uu___101_3384.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = uu___101_3384.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = Some (lift_wp); FStar_Syntax_Syntax.lift = lift1})
in (

let se1 = (

let uu___102_3386 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_sub_effect (sub2); FStar_Syntax_Syntax.sigdoc = uu___102_3386.FStar_Syntax_Syntax.sigdoc; FStar_Syntax_Syntax.sigrng = uu___102_3386.FStar_Syntax_Syntax.sigrng})
in (

let env4 = (FStar_TypeChecker_Env.push_sigelt env3 se1)
in (((se1)::[]), (env4), ([])))))))))
end)))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, flags) -> begin
(

let env0 = env1
in (

let env2 = (FStar_TypeChecker_Env.set_range env1 r)
in (

let uu____3403 = (FStar_Syntax_Subst.open_comp tps c)
in (match (uu____3403) with
| (tps1, c1) -> begin
(

let uu____3413 = (FStar_TypeChecker_TcTerm.tc_tparams env2 tps1)
in (match (uu____3413) with
| (tps2, env3, us) -> begin
(

let uu____3425 = (FStar_TypeChecker_TcTerm.tc_comp env3 c1)
in (match (uu____3425) with
| (c2, u, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env3 g);
(

let tps3 = (FStar_Syntax_Subst.close_binders tps2)
in (

let c3 = (FStar_Syntax_Subst.close_comp tps3 c2)
in (

let uu____3440 = (

let uu____3441 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps3), (c3)))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 uu____3441))
in (match (uu____3440) with
| (uvs1, t) -> begin
(

let uu____3455 = (

let uu____3463 = (

let uu____3466 = (

let uu____3467 = (FStar_Syntax_Subst.compress t)
in uu____3467.FStar_Syntax_Syntax.n)
in ((tps3), (uu____3466)))
in (match (uu____3463) with
| ([], FStar_Syntax_Syntax.Tm_arrow (uu____3477, c4)) -> begin
(([]), (c4))
end
| (uu____3501, FStar_Syntax_Syntax.Tm_arrow (tps4, c4)) -> begin
((tps4), (c4))
end
| uu____3519 -> begin
(failwith "Impossible")
end))
in (match (uu____3455) with
| (tps4, c4) -> begin
((match ((((FStar_List.length uvs1) <> (Prims.parse_int "1")) && (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))))) with
| true -> begin
(

let uu____3549 = (FStar_Syntax_Subst.open_univ_vars uvs1 t)
in (match (uu____3549) with
| (uu____3552, t1) -> begin
(

let uu____3554 = (

let uu____3555 = (

let uu____3558 = (

let uu____3559 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____3560 = (FStar_All.pipe_right (FStar_List.length uvs1) FStar_Util.string_of_int)
in (

let uu____3563 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)" uu____3559 uu____3560 uu____3563))))
in ((uu____3558), (r)))
in FStar_Errors.Error (uu____3555))
in (Prims.raise uu____3554))
end))
end
| uu____3564 -> begin
()
end);
(

let se1 = (

let uu___103_3566 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (((lid), (uvs1), (tps4), (c4), (tags), (flags))); FStar_Syntax_Syntax.sigdoc = uu___103_3566.FStar_Syntax_Syntax.sigdoc; FStar_Syntax_Syntax.sigrng = uu___103_3566.FStar_Syntax_Syntax.sigrng})
in (

let env4 = (FStar_TypeChecker_Env.push_sigelt env0 se1)
in (((se1)::[]), (env4), ([]))));
)
end))
end))));
)
end))
end))
end))))
end
| (FStar_Syntax_Syntax.Sig_declare_typ (_, _, _, quals)) | (FStar_Syntax_Syntax.Sig_let (_, _, quals, _)) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___79_3592 -> (match (uu___79_3592) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____3593 -> begin
false
end)))) -> begin
(([]), (env1), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t, quals) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_range env1 r)
in (

let uu____3603 = (match ((uvs = [])) with
| true -> begin
(

let uu____3604 = (

let uu____3605 = (FStar_Syntax_Util.type_u ())
in (Prims.fst uu____3605))
in (check_and_gen env2 t uu____3604))
end
| uu____3608 -> begin
(

let uu____3609 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____3609) with
| (uvs1, t1) -> begin
(

let t2 = (

let uu____3615 = (

let uu____3616 = (FStar_Syntax_Util.type_u ())
in (Prims.fst uu____3616))
in (tc_check_trivial_guard env2 t1 uu____3615))
in (

let t3 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Beta)::[]) env2 t2)
in (

let uu____3620 = (FStar_Syntax_Subst.close_univ_vars uvs1 t3)
in ((uvs1), (uu____3620)))))
end))
end)
in (match (uu____3603) with
| (uvs1, t1) -> begin
(

let se1 = (

let uu___104_3631 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (uvs1), (t1), (quals))); FStar_Syntax_Syntax.sigdoc = uu___104_3631.FStar_Syntax_Syntax.sigdoc; FStar_Syntax_Syntax.sigrng = uu___104_3631.FStar_Syntax_Syntax.sigrng})
in (

let env3 = (FStar_TypeChecker_Env.push_sigelt env2 se1)
in (((se1)::[]), (env3), ([]))))
end)))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals) -> begin
(

let se1 = (tc_assume env1 lid phi quals r)
in (

let env2 = (FStar_TypeChecker_Env.push_sigelt env1 se1)
in (((se1)::[]), (env2), ([]))))
end
| FStar_Syntax_Syntax.Sig_main (e) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_range env1 r)
in (

let env3 = (FStar_TypeChecker_Env.set_expected_typ env2 FStar_TypeChecker_Common.t_unit)
in (

let uu____3649 = (FStar_TypeChecker_TcTerm.tc_term env3 e)
in (match (uu____3649) with
| (e1, c, g1) -> begin
(

let uu____3661 = (

let uu____3665 = (

let uu____3667 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (uu____3667))
in (

let uu____3668 = (

let uu____3671 = (c.FStar_Syntax_Syntax.comp ())
in ((e1), (uu____3671)))
in (FStar_TypeChecker_TcTerm.check_expected_effect env3 uu____3665 uu____3668)))
in (match (uu____3661) with
| (e2, uu____3682, g) -> begin
((

let uu____3685 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env3 uu____3685));
(

let se1 = (

let uu___105_3687 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_main (e2); FStar_Syntax_Syntax.sigdoc = uu___105_3687.FStar_Syntax_Syntax.sigdoc; FStar_Syntax_Syntax.sigrng = uu___105_3687.FStar_Syntax_Syntax.sigrng})
in (

let env4 = (FStar_TypeChecker_Env.push_sigelt env3 se1)
in (((se1)::[]), (env4), ([]))));
)
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, lids, quals, attrs) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_range env1 r)
in (

let check_quals_eq = (fun l qopt q -> (match (qopt) with
| None -> begin
Some (q)
end
| Some (q') -> begin
(

let uu____3727 = (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q'))
in (match (uu____3727) with
| true -> begin
Some (q)
end
| uu____3735 -> begin
(

let uu____3736 = (

let uu____3737 = (

let uu____3740 = (

let uu____3741 = (FStar_Syntax_Print.lid_to_string l)
in (

let uu____3742 = (FStar_Syntax_Print.quals_to_string q)
in (

let uu____3743 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" uu____3741 uu____3742 uu____3743))))
in ((uu____3740), (r)))
in FStar_Errors.Error (uu____3737))
in (Prims.raise uu____3736))
end))
end))
in (

let uu____3746 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun uu____3767 lb -> (match (uu____3767) with
| (gen1, lbs1, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____3791 = (

let uu____3797 = (FStar_TypeChecker_Env.try_lookup_val_decl env2 lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____3797) with
| None -> begin
(match ((lb.FStar_Syntax_Syntax.lbunivs <> [])) with
| true -> begin
((false), (lb), (quals_opt))
end
| uu____3822 -> begin
((gen1), (lb), (quals_opt))
end)
end
| Some ((uvs, tval), quals1) -> begin
(

let quals_opt1 = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals1)
in ((match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| uu____3849 -> begin
(FStar_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end);
(match (((lb.FStar_Syntax_Syntax.lbunivs <> []) && ((FStar_List.length lb.FStar_Syntax_Syntax.lbunivs) <> (FStar_List.length uvs)))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Inline universes are incoherent with annotation from val declaration"), (r)))))
end
| uu____3856 -> begin
()
end);
(

let uu____3857 = (FStar_Syntax_Syntax.mk_lb ((FStar_Util.Inr (lbname)), (uvs), (FStar_Syntax_Const.effect_ALL_lid), (tval), (lb.FStar_Syntax_Syntax.lbdef)))
in ((false), (uu____3857), (quals_opt1)));
))
end))
in (match (uu____3791) with
| (gen2, lb1, quals_opt1) -> begin
((gen2), ((lb1)::lbs1), (quals_opt1))
end)))
end)) ((true), ([]), ((match ((quals = [])) with
| true -> begin
None
end
| uu____3888 -> begin
Some (quals)
end)))))
in (match (uu____3746) with
| (should_generalize, lbs', quals_opt) -> begin
(

let quals1 = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Visible_default)::[]
end
| Some (q) -> begin
(

let uu____3911 = (FStar_All.pipe_right q (FStar_Util.for_some (fun uu___80_3913 -> (match (uu___80_3913) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Visible_default) | (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> begin
true
end
| uu____3914 -> begin
false
end))))
in (match (uu____3911) with
| true -> begin
q
end
| uu____3916 -> begin
(FStar_Syntax_Syntax.Visible_default)::q
end))
end)
in (

let lbs'1 = (FStar_List.rev lbs')
in (

let e = (

let uu____3922 = (

let uu____3925 = (

let uu____3926 = (

let uu____3934 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((((Prims.fst lbs)), (lbs'1))), (uu____3934)))
in FStar_Syntax_Syntax.Tm_let (uu____3926))
in (FStar_Syntax_Syntax.mk uu____3925))
in (uu____3922 None r))
in (

let uu____3956 = (

let uu____3962 = (FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term (

let uu___106_3966 = env2
in {FStar_TypeChecker_Env.solver = uu___106_3966.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___106_3966.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___106_3966.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___106_3966.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___106_3966.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___106_3966.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___106_3966.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___106_3966.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___106_3966.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___106_3966.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___106_3966.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = uu___106_3966.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = uu___106_3966.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___106_3966.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___106_3966.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___106_3966.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___106_3966.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___106_3966.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___106_3966.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___106_3966.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___106_3966.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___106_3966.FStar_TypeChecker_Env.qname_and_index}) e)
in (match (uu____3962) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs1, e1); FStar_Syntax_Syntax.tk = uu____3974; FStar_Syntax_Syntax.pos = uu____3975; FStar_Syntax_Syntax.vars = uu____3976}, uu____3977, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals2 = (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (uu____3996, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals1
end
| uu____4001 -> begin
quals1
end)
in (

let quals3 = (FStar_List.choose (fun uu___81_4004 -> (match (uu___81_4004) with
| FStar_Syntax_Syntax.Inline_for_extraction -> begin
(

let uu____4006 = (

let uu____4007 = (FStar_List.for_all (fun lb -> (

let ok = (FStar_Syntax_Util.is_pure_or_ghost_function lb.FStar_Syntax_Syntax.lbtyp)
in ((match ((not (ok))) with
| true -> begin
(

let uu____4011 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (FStar_Util.print1_warning "Dropping inline_for_extraction from %s because it is not a pure function\n" uu____4011))
end
| uu____4012 -> begin
()
end);
ok;
))) (Prims.snd lbs1))
in (not (uu____4007)))
in (match (uu____4006) with
| true -> begin
None
end
| uu____4015 -> begin
Some (FStar_Syntax_Syntax.Inline_for_extraction)
end))
end
| q -> begin
Some (q)
end)) quals2)
in (((

let uu___107_4020 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((lbs1), (lids), (quals3), (attrs))); FStar_Syntax_Syntax.sigdoc = uu___107_4020.FStar_Syntax_Syntax.sigdoc; FStar_Syntax_Syntax.sigrng = uu___107_4020.FStar_Syntax_Syntax.sigrng})), (lbs1))))
end
| uu____4027 -> begin
(failwith "impossible")
end))
in (match (uu____3956) with
| (se1, lbs1) -> begin
((FStar_All.pipe_right (Prims.snd lbs1) (FStar_List.iter (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____4054 = (FStar_Syntax_Syntax.range_of_fv fv)
in (FStar_TypeChecker_Common.insert_identifier_info (FStar_Util.Inr (fv)) lb.FStar_Syntax_Syntax.lbtyp uu____4054))))));
(

let uu____4056 = (log env2)
in (match (uu____4056) with
| true -> begin
(

let uu____4057 = (

let uu____4058 = (FStar_All.pipe_right (Prims.snd lbs1) (FStar_List.map (fun lb -> (

let should_log = (

let uu____4065 = (

let uu____4070 = (

let uu____4071 = (

let uu____4076 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____4076.FStar_Syntax_Syntax.fv_name)
in uu____4071.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env2 uu____4070))
in (match (uu____4065) with
| None -> begin
true
end
| uu____4083 -> begin
false
end))
in (match (should_log) with
| true -> begin
(

let uu____4088 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____4089 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" uu____4088 uu____4089)))
end
| uu____4090 -> begin
""
end)))))
in (FStar_All.pipe_right uu____4058 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" uu____4057))
end
| uu____4092 -> begin
()
end));
(

let env3 = (FStar_TypeChecker_Env.push_sigelt env2 se1)
in (((se1)::[]), (env3), ([])));
)
end)))))
end))))
end));
)))


let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___82_4119 -> (match (uu___82_4119) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| uu____4120 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| uu____4128 -> begin
false
end))
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_pragma (uu____4133) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, uu____4144) -> begin
(

let uu____4151 = (is_abstract quals)
in (match (uu____4151) with
| true -> begin
(

let for_export_bundle = (fun se1 uu____4170 -> (match (uu____4170) with
| (out, hidden1) -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, uu____4193, uu____4194, quals1) -> begin
(

let dec = (

let uu___108_4203 = se1
in (

let uu____4204 = (

let uu____4205 = (

let uu____4211 = (

let uu____4214 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow bs uu____4214))
in ((l), (us), (uu____4211), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals1)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____4205))
in {FStar_Syntax_Syntax.sigel = uu____4204; FStar_Syntax_Syntax.sigdoc = uu___108_4203.FStar_Syntax_Syntax.sigdoc; FStar_Syntax_Syntax.sigrng = uu___108_4203.FStar_Syntax_Syntax.sigrng}))
in (((dec)::out), (hidden1)))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, uu____4225, uu____4226, uu____4227, uu____4228) -> begin
(

let dec = (

let uu___109_4234 = se1
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]))); FStar_Syntax_Syntax.sigdoc = uu___109_4234.FStar_Syntax_Syntax.sigdoc; FStar_Syntax_Syntax.sigrng = uu___109_4234.FStar_Syntax_Syntax.sigrng})
in (((dec)::out), ((l)::hidden1)))
end
| uu____4238 -> begin
((out), (hidden1))
end)
end))
in (FStar_List.fold_right for_export_bundle ses (([]), (hidden))))
end
| uu____4247 -> begin
(((se)::[]), (hidden))
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____4250, uu____4251, quals) -> begin
(

let uu____4255 = (is_abstract quals)
in (match (uu____4255) with
| true -> begin
(([]), (hidden))
end
| uu____4262 -> begin
(((se)::[]), (hidden))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, us, t, quals) -> begin
(

let uu____4271 = (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc))
in (match (uu____4271) with
| true -> begin
((((

let uu___110_4279 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]))); FStar_Syntax_Syntax.sigdoc = uu___110_4279.FStar_Syntax_Syntax.sigdoc; FStar_Syntax_Syntax.sigrng = uu___110_4279.FStar_Syntax_Syntax.sigrng}))::[]), ((l)::hidden))
end
| uu____4281 -> begin
(

let uu____4282 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___83_4284 -> (match (uu___83_4284) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| uu____4287 -> begin
false
end))))
in (match (uu____4282) with
| true -> begin
(((se)::[]), (hidden))
end
| uu____4294 -> begin
(([]), (hidden))
end))
end))
end
| FStar_Syntax_Syntax.Sig_main (uu____4297) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____4307, quals, uu____4309) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____4327 = (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
in (match (uu____4327) with
| true -> begin
(([]), (hidden))
end
| uu____4335 -> begin
(

let dec = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::[]))); FStar_Syntax_Syntax.sigdoc = se.FStar_Syntax_Syntax.sigdoc; FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid lid)}
in (((dec)::[]), ((lid)::hidden)))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, l, quals, uu____4350) -> begin
(

let uu____4357 = (is_abstract quals)
in (match (uu____4357) with
| true -> begin
(

let uu____4362 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let uu___111_4368 = se
in (

let uu____4369 = (

let uu____4370 = (

let uu____4376 = (

let uu____4377 = (

let uu____4382 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____4382.FStar_Syntax_Syntax.fv_name)
in uu____4377.FStar_Syntax_Syntax.v)
in ((uu____4376), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____4370))
in {FStar_Syntax_Syntax.sigel = uu____4369; FStar_Syntax_Syntax.sigdoc = uu___111_4368.FStar_Syntax_Syntax.sigdoc; FStar_Syntax_Syntax.sigrng = uu___111_4368.FStar_Syntax_Syntax.sigrng})))))
in ((uu____4362), (hidden)))
end
| uu____4392 -> begin
(((se)::[]), (hidden))
end))
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let rec process_one_decl = (fun uu____4430 se -> (match (uu____4430) with
| (ses1, exports, env1, hidden) -> begin
((

let uu____4460 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____4460) with
| true -> begin
(

let uu____4461 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____4461))
end
| uu____4462 -> begin
()
end));
(

let uu____4463 = (tc_decl env1 se)
in (match (uu____4463) with
| (ses', env2, ses_elaborated) -> begin
((

let uu____4487 = ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("LogTypes"))))
in (match (uu____4487) with
| true -> begin
(

let uu____4488 = (FStar_List.fold_left (fun s se1 -> (

let uu____4491 = (

let uu____4492 = (FStar_Syntax_Print.sigelt_to_string se1)
in (Prims.strcat uu____4492 "\n"))
in (Prims.strcat s uu____4491))) "" ses')
in (FStar_Util.print1 "Checked: %s\n" uu____4488))
end
| uu____4493 -> begin
()
end));
(FStar_List.iter (fun se1 -> (env2.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env2 se1)) ses');
(

let uu____4496 = (

let accum_exports_hidden = (fun uu____4514 se1 -> (match (uu____4514) with
| (exports1, hidden1) -> begin
(

let uu____4530 = (for_export hidden1 se1)
in (match (uu____4530) with
| (se_exported, hidden2) -> begin
(((FStar_List.rev_append se_exported exports1)), (hidden2))
end))
end))
in (FStar_List.fold_left accum_exports_hidden ((exports), (hidden)) ses'))
in (match (uu____4496) with
| (exports1, hidden1) -> begin
(((((FStar_List.rev_append ses' ses1)), (exports1), (env2), (hidden1))), (ses_elaborated))
end));
)
end));
)
end))
in (

let uu____4580 = (FStar_Util.fold_flatten process_one_decl (([]), ([]), (env), ([])) ses)
in (match (uu____4580) with
| (ses1, exports, env1, uu____4606) -> begin
(((FStar_List.rev_append ses1 [])), ((FStar_List.rev_append exports [])), (env1))
end))))


let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (

let verify = (FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let action = (match (verify) with
| true -> begin
"Verifying"
end
| uu____4627 -> begin
"Lax-checking"
end)
in (

let label1 = (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____4629 -> begin
"implementation"
end)
in ((

let uu____4631 = (FStar_Options.debug_any ())
in (match (uu____4631) with
| true -> begin
(FStar_Util.print3 "%s %s of %s\n" action label1 modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
end
| uu____4632 -> begin
()
end));
(

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____4634 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let msg = (Prims.strcat "Internals for " name)
in (

let env1 = (

let uu___112_4637 = env
in {FStar_TypeChecker_Env.solver = uu___112_4637.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___112_4637.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___112_4637.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___112_4637.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___112_4637.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___112_4637.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___112_4637.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___112_4637.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___112_4637.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___112_4637.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___112_4637.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___112_4637.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___112_4637.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___112_4637.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___112_4637.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___112_4637.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = (not (verify)); FStar_TypeChecker_Env.lax = uu___112_4637.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___112_4637.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___112_4637.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___112_4637.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___112_4637.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___112_4637.FStar_TypeChecker_Env.qname_and_index})
in ((env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg);
(

let env2 = (FStar_TypeChecker_Env.set_current_module env1 modul.FStar_Syntax_Syntax.name)
in (

let uu____4640 = (tc_decls env2 modul.FStar_Syntax_Syntax.declarations)
in (match (uu____4640) with
| (ses, exports, env3) -> begin
(((

let uu___113_4658 = modul
in {FStar_Syntax_Syntax.name = uu___113_4658.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = uu___113_4658.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___113_4658.FStar_Syntax_Syntax.is_interface})), (exports), (env3))
end)));
))));
)))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let uu____4674 = (tc_decls env decls)
in (match (uu____4674) with
| (ses, exports, env1) -> begin
(

let modul1 = (

let uu___114_4692 = modul
in {FStar_Syntax_Syntax.name = uu___114_4692.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = uu___114_4692.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___114_4692.FStar_Syntax_Syntax.is_interface})
in ((modul1), (exports), (env1)))
end)))


let check_exports : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env modul exports -> (

let env1 = (

let uu___115_4706 = env
in {FStar_TypeChecker_Env.solver = uu___115_4706.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___115_4706.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___115_4706.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___115_4706.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___115_4706.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___115_4706.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___115_4706.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___115_4706.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___115_4706.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___115_4706.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___115_4706.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___115_4706.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___115_4706.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = uu___115_4706.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___115_4706.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___115_4706.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___115_4706.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = true; FStar_TypeChecker_Env.type_of = uu___115_4706.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___115_4706.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___115_4706.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___115_4706.FStar_TypeChecker_Env.qname_and_index})
in (

let check_term = (fun lid univs1 t -> (

let uu____4717 = (FStar_Syntax_Subst.open_univ_vars univs1 t)
in (match (uu____4717) with
| (univs2, t1) -> begin
((

let uu____4723 = (

let uu____4724 = (

let uu____4727 = (FStar_TypeChecker_Env.set_current_module env1 modul.FStar_Syntax_Syntax.name)
in (FStar_TypeChecker_Env.debug uu____4727))
in (FStar_All.pipe_left uu____4724 (FStar_Options.Other ("Exports"))))
in (match (uu____4723) with
| true -> begin
(

let uu____4728 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____4729 = (

let uu____4730 = (FStar_All.pipe_right univs2 (FStar_List.map (fun x -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (x))))))
in (FStar_All.pipe_right uu____4730 (FStar_String.concat ", ")))
in (

let uu____4735 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Checking for export %s <%s> : %s\n" uu____4728 uu____4729 uu____4735))))
end
| uu____4736 -> begin
()
end));
(

let env2 = (FStar_TypeChecker_Env.push_univ_vars env1 univs2)
in (

let uu____4738 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1)
in (FStar_All.pipe_right uu____4738 Prims.ignore)));
)
end)))
in (

let check_term1 = (fun lid univs1 t -> ((

let uu____4756 = (

let uu____4757 = (FStar_Syntax_Print.lid_to_string modul.FStar_Syntax_Syntax.name)
in (

let uu____4758 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Interface of %s violates its abstraction (add a \'private\' qualifier to \'%s\'?)" uu____4757 uu____4758)))
in (FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____4756));
(check_term lid univs1 t);
(FStar_Errors.message_prefix.FStar_Errors.clear_prefix ());
))
in (

let rec check_sigelt = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, uu____4766) -> begin
(

let uu____4773 = (

let uu____4774 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____4774)))
in (match (uu____4773) with
| true -> begin
(FStar_All.pipe_right ses (FStar_List.iter check_sigelt))
end
| uu____4777 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (l, univs1, binders, typ, uu____4782, uu____4783, uu____4784) -> begin
(

let t = (

let uu____4794 = (

let uu____4797 = (

let uu____4798 = (

let uu____4806 = (FStar_Syntax_Syntax.mk_Total typ)
in ((binders), (uu____4806)))
in FStar_Syntax_Syntax.Tm_arrow (uu____4798))
in (FStar_Syntax_Syntax.mk uu____4797))
in (uu____4794 None se.FStar_Syntax_Syntax.sigrng))
in (check_term1 l univs1 t))
end
| FStar_Syntax_Syntax.Sig_datacon (l, univs1, t, uu____4818, uu____4819, uu____4820, uu____4821) -> begin
(check_term1 l univs1 t)
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, univs1, t, quals) -> begin
(

let uu____4832 = (

let uu____4833 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____4833)))
in (match (uu____4832) with
| true -> begin
(check_term1 l univs1 t)
end
| uu____4835 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_let ((uu____4836, lbs), uu____4838, quals, uu____4840) -> begin
(

let uu____4852 = (

let uu____4853 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____4853)))
in (match (uu____4852) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (check_term1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp)))))
end
| uu____4862 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs1, binders, comp, quals, flags) -> begin
(

let uu____4873 = (

let uu____4874 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____4874)))
in (match (uu____4873) with
| true -> begin
(

let arrow1 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp))))) None se.FStar_Syntax_Syntax.sigrng)
in (check_term1 l univs1 arrow1))
end
| uu____4887 -> begin
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
| uu____4894 -> begin
(FStar_List.iter check_sigelt exports)
end))))))


let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (

let modul1 = (

let uu___116_4907 = modul
in {FStar_Syntax_Syntax.name = uu___116_4907.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu___116_4907.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env1 = (FStar_TypeChecker_Env.finish_module env modul1)
in ((

let uu____4910 = (

let uu____4911 = (FStar_Options.lax ())
in (not (uu____4911)))
in (match (uu____4910) with
| true -> begin
(check_exports env1 modul1 exports)
end
| uu____4912 -> begin
()
end));
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul1.FStar_Syntax_Syntax.name.FStar_Ident.str));
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env1 modul1);
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
(

let uu____4917 = (

let uu____4918 = (FStar_Options.interactive ())
in (not (uu____4918)))
in (match (uu____4917) with
| true -> begin
(

let uu____4919 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right uu____4919 Prims.ignore))
end
| uu____4920 -> begin
()
end));
((modul1), (env1));
))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let uu____4929 = (tc_partial_modul env modul)
in (match (uu____4929) with
| (modul1, non_private_decls, env1) -> begin
(finish_partial_modul env1 modul1 non_private_decls)
end)))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> ((

let uu____4950 = (FStar_Options.debug_any ())
in (match (uu____4950) with
| true -> begin
(

let uu____4951 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (match (m.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"i\'face"
end
| uu____4952 -> begin
"module"
end) uu____4951))
end
| uu____4953 -> begin
()
end));
(

let env1 = (

let uu___117_4955 = env
in (

let uu____4956 = (

let uu____4957 = (FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (not (uu____4957)))
in {FStar_TypeChecker_Env.solver = uu___117_4955.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___117_4955.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___117_4955.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___117_4955.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___117_4955.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___117_4955.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___117_4955.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___117_4955.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___117_4955.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___117_4955.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___117_4955.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___117_4955.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___117_4955.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___117_4955.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___117_4955.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___117_4955.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___117_4955.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___117_4955.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu____4956; FStar_TypeChecker_Env.lax_universes = uu___117_4955.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___117_4955.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___117_4955.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___117_4955.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___117_4955.FStar_TypeChecker_Env.qname_and_index}))
in (

let uu____4958 = (tc_modul env1 m)
in (match (uu____4958) with
| (m1, env2) -> begin
((

let uu____4966 = (FStar_Options.dump_module m1.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____4966) with
| true -> begin
(

let uu____4967 = (FStar_Syntax_Print.modul_to_string m1)
in (FStar_Util.print1 "%s\n" uu____4967))
end
| uu____4968 -> begin
()
end));
(

let uu____4970 = ((FStar_Options.dump_module m1.FStar_Syntax_Syntax.name.FStar_Ident.str) && (FStar_Options.debug_at_level m1.FStar_Syntax_Syntax.name.FStar_Ident.str (FStar_Options.Other ("Normalize"))))
in (match (uu____4970) with
| true -> begin
(

let normalize_toplevel_lets = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((b, lbs), ids, qs, attrs) -> begin
(

let n1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]))
in (

let update = (fun lb -> (

let uu____5000 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____5000) with
| (univnames1, e) -> begin
(

let uu___118_5005 = lb
in (

let uu____5006 = (

let uu____5009 = (FStar_TypeChecker_Env.push_univ_vars env2 univnames1)
in (n1 uu____5009 e))
in {FStar_Syntax_Syntax.lbname = uu___118_5005.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___118_5005.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___118_5005.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___118_5005.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____5006}))
end)))
in (

let uu___119_5010 = se
in (

let uu____5011 = (

let uu____5012 = (

let uu____5020 = (

let uu____5024 = (FStar_List.map update lbs)
in ((b), (uu____5024)))
in ((uu____5020), (ids), (qs), (attrs)))
in FStar_Syntax_Syntax.Sig_let (uu____5012))
in {FStar_Syntax_Syntax.sigel = uu____5011; FStar_Syntax_Syntax.sigdoc = uu___119_5010.FStar_Syntax_Syntax.sigdoc; FStar_Syntax_Syntax.sigrng = uu___119_5010.FStar_Syntax_Syntax.sigrng}))))
end
| uu____5033 -> begin
se
end))
in (

let normalized_module = (

let uu___120_5035 = m1
in (

let uu____5036 = (FStar_List.map normalize_toplevel_lets m1.FStar_Syntax_Syntax.declarations)
in {FStar_Syntax_Syntax.name = uu___120_5035.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu____5036; FStar_Syntax_Syntax.exports = uu___120_5035.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___120_5035.FStar_Syntax_Syntax.is_interface}))
in (

let uu____5037 = (FStar_Syntax_Print.modul_to_string normalized_module)
in (FStar_Util.print1 "%s\n" uu____5037))))
end
| uu____5038 -> begin
()
end));
((m1), (env2));
)
end)));
))




