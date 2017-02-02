
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

let uu___95_12 = env
in {FStar_TypeChecker_Env.solver = uu___95_12.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___95_12.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___95_12.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___95_12.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___95_12.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___95_12.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___95_12.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___95_12.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___95_12.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___95_12.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___95_12.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___95_12.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___95_12.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___95_12.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___95_12.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___95_12.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___95_12.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___95_12.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___95_12.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___95_12.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___95_12.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___95_12.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___95_12.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), ((Prims.parse_int "0"))))}))
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

let uu___96_24 = env
in {FStar_TypeChecker_Env.solver = uu___96_24.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___96_24.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___96_24.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___96_24.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___96_24.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___96_24.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___96_24.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___96_24.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___96_24.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___96_24.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___96_24.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___96_24.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___96_24.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___96_24.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___96_24.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___96_24.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___96_24.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___96_24.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___96_24.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___96_24.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___96_24.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___96_24.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___96_24.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), ((Prims.parse_int "0"))))})))
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


let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let uu____122 = (FStar_TypeChecker_TcTerm.tc_binders env tps)
in (match (uu____122) with
| (tps, env, g, us) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
((tps), (env), (us));
)
end)))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun env m s -> (

let fail = (fun uu____155 -> (

let uu____156 = (

let uu____157 = (

let uu____160 = (FStar_TypeChecker_Err.unexpected_signature_for_monad env m s)
in ((uu____160), ((FStar_Ident.range_of_lid m))))
in FStar_Errors.Error (uu____157))
in (Prims.raise uu____156)))
in (

let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, uu____188))::((wp, uu____190))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____199 -> begin
(fail ())
end))
end
| uu____200 -> begin
(fail ())
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let uu____230 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (uu____230) with
| (uvs, c) -> begin
((uvs), ([]), (c))
end))
end
| uu____246 -> begin
(

let t' = (FStar_Syntax_Util.arrow binders c)
in (

let uu____253 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (uu____253) with
| (uvs, t') -> begin
(

let uu____264 = (

let uu____265 = (FStar_Syntax_Subst.compress t')
in uu____265.FStar_Syntax_Syntax.n)
in (match (uu____264) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
((uvs), (binders), (c))
end
| uu____291 -> begin
(failwith "Impossible")
end))
end)))
end))


let rec tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (

let uu____360 = (FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____360) with
| (effect_params_un, signature_un, opening) -> begin
(

let uu____367 = (tc_tparams env0 effect_params_un)
in (match (uu____367) with
| (effect_params, env, uu____373) -> begin
(

let uu____374 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (uu____374) with
| (signature, uu____378) -> begin
(

let ed = (

let uu___97_380 = ed
in {FStar_Syntax_Syntax.qualifiers = uu___97_380.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___97_380.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___97_380.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___97_380.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = uu___97_380.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = uu___97_380.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = uu___97_380.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = uu___97_380.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = uu___97_380.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = uu___97_380.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = uu___97_380.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = uu___97_380.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = uu___97_380.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = uu___97_380.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = uu___97_380.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = uu___97_380.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = uu___97_380.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = uu___97_380.FStar_Syntax_Syntax.actions})
in (

let ed = (match (effect_params) with
| [] -> begin
ed
end
| uu____384 -> begin
(

let op = (fun ts -> (

let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in (([]), (t1))))
in (

let uu___98_402 = ed
in (

let uu____403 = (op ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____404 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____405 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____406 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____407 = (op ed.FStar_Syntax_Syntax.stronger)
in (

let uu____408 = (op ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____409 = (op ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____410 = (op ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____411 = (op ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____412 = (op ed.FStar_Syntax_Syntax.trivial)
in (

let uu____413 = (

let uu____414 = (op (([]), (ed.FStar_Syntax_Syntax.repr)))
in (Prims.snd uu____414))
in (

let uu____420 = (op ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____421 = (op ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____422 = (FStar_List.map (fun a -> (

let uu___99_425 = a
in (

let uu____426 = (

let uu____427 = (op (([]), (a.FStar_Syntax_Syntax.action_defn)))
in (Prims.snd uu____427))
in (

let uu____433 = (

let uu____434 = (op (([]), (a.FStar_Syntax_Syntax.action_typ)))
in (Prims.snd uu____434))
in {FStar_Syntax_Syntax.action_name = uu___99_425.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___99_425.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___99_425.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = uu____426; FStar_Syntax_Syntax.action_typ = uu____433})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.qualifiers = uu___98_402.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___98_402.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___98_402.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___98_402.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu___98_402.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = uu___98_402.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = uu____403; FStar_Syntax_Syntax.bind_wp = uu____404; FStar_Syntax_Syntax.if_then_else = uu____405; FStar_Syntax_Syntax.ite_wp = uu____406; FStar_Syntax_Syntax.stronger = uu____407; FStar_Syntax_Syntax.close_wp = uu____408; FStar_Syntax_Syntax.assert_p = uu____409; FStar_Syntax_Syntax.assume_p = uu____410; FStar_Syntax_Syntax.null_wp = uu____411; FStar_Syntax_Syntax.trivial = uu____412; FStar_Syntax_Syntax.repr = uu____413; FStar_Syntax_Syntax.return_repr = uu____420; FStar_Syntax_Syntax.bind_repr = uu____421; FStar_Syntax_Syntax.actions = uu____422}))))))))))))))))
end)
in (

let wp_with_fresh_result_type = (fun env mname signature -> (

let fail = (fun t -> (

let uu____462 = (

let uu____463 = (

let uu____466 = (FStar_TypeChecker_Err.unexpected_signature_for_monad env mname t)
in ((uu____466), ((FStar_Ident.range_of_lid mname))))
in FStar_Errors.Error (uu____463))
in (Prims.raise uu____462)))
in (

let uu____471 = (

let uu____472 = (FStar_Syntax_Subst.compress signature)
in uu____472.FStar_Syntax_Syntax.n)
in (match (uu____471) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, uu____497))::((wp, uu____499))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____508 -> begin
(fail signature)
end))
end
| uu____509 -> begin
(fail signature)
end))))
in (

let uu____510 = (wp_with_fresh_result_type env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (uu____510) with
| (a, wp_a) -> begin
(

let fresh_effect_signature = (fun uu____528 -> (

let uu____529 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (uu____529) with
| (signature, uu____537) -> begin
(wp_with_fresh_result_type env ed.FStar_Syntax_Syntax.mname signature)
end)))
in (

let env = (

let uu____539 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env uu____539))
in ((

let uu____541 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED")))
in (match (uu____541) with
| true -> begin
(

let uu____542 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____543 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (

let uu____544 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (

let uu____545 = (

let uu____546 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Print.term_to_string uu____546))
in (

let uu____547 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.sort)
in (FStar_Util.print5 "Checking effect signature: %s %s : %s\n(a is %s:%s)\n" uu____542 uu____543 uu____544 uu____545 uu____547))))))
end
| uu____548 -> begin
()
end));
(

let check_and_gen' = (fun env uu____560 k -> (match (uu____560) with
| (uu____565, t) -> begin
(check_and_gen env t k)
end))
in (

let return_wp = (

let expected_k = (

let uu____573 = (

let uu____577 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____578 = (

let uu____580 = (

let uu____581 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____581))
in (uu____580)::[])
in (uu____577)::uu____578))
in (

let uu____582 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow uu____573 uu____582)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret_wp expected_k))
in (

let bind_wp = (

let uu____586 = (fresh_effect_signature ())
in (match (uu____586) with
| (b, wp_b) -> begin
(

let a_wp_b = (

let uu____600 = (

let uu____604 = (

let uu____605 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____605))
in (uu____604)::[])
in (

let uu____606 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____600 uu____606)))
in (

let expected_k = (

let uu____612 = (

let uu____616 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (

let uu____617 = (

let uu____619 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____620 = (

let uu____622 = (FStar_Syntax_Syntax.mk_binder b)
in (

let uu____623 = (

let uu____625 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____626 = (

let uu____628 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (uu____628)::[])
in (uu____625)::uu____626))
in (uu____622)::uu____623))
in (uu____619)::uu____620))
in (uu____616)::uu____617))
in (

let uu____629 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____612 uu____629)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else = (

let p = (

let uu____634 = (

let uu____635 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____635 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) uu____634))
in (

let expected_k = (

let uu____643 = (

let uu____647 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____648 = (

let uu____650 = (FStar_Syntax_Syntax.mk_binder p)
in (

let uu____651 = (

let uu____653 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____654 = (

let uu____656 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____656)::[])
in (uu____653)::uu____654))
in (uu____650)::uu____651))
in (uu____647)::uu____648))
in (

let uu____657 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____643 uu____657)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (

let uu____664 = (

let uu____668 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____669 = (

let uu____671 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____671)::[])
in (uu____668)::uu____669))
in (

let uu____672 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____664 uu____672)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let uu____676 = (FStar_Syntax_Util.type_u ())
in (match (uu____676) with
| (t, uu____680) -> begin
(

let expected_k = (

let uu____684 = (

let uu____688 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____689 = (

let uu____691 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____692 = (

let uu____694 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____694)::[])
in (uu____691)::uu____692))
in (uu____688)::uu____689))
in (

let uu____695 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow uu____684 uu____695)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (

let uu____700 = (

let uu____701 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____701 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) uu____700))
in (

let b_wp_a = (

let uu____709 = (

let uu____713 = (

let uu____714 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder uu____714))
in (uu____713)::[])
in (

let uu____715 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____709 uu____715)))
in (

let expected_k = (

let uu____721 = (

let uu____725 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____726 = (

let uu____728 = (FStar_Syntax_Syntax.mk_binder b)
in (

let uu____729 = (

let uu____731 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (uu____731)::[])
in (uu____728)::uu____729))
in (uu____725)::uu____726))
in (

let uu____732 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____721 uu____732)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (

let uu____739 = (

let uu____743 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____744 = (

let uu____746 = (

let uu____747 = (

let uu____748 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____748 Prims.fst))
in (FStar_Syntax_Syntax.null_binder uu____747))
in (

let uu____753 = (

let uu____755 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____755)::[])
in (uu____746)::uu____753))
in (uu____743)::uu____744))
in (

let uu____756 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____739 uu____756)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (

let uu____763 = (

let uu____767 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____768 = (

let uu____770 = (

let uu____771 = (

let uu____772 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____772 Prims.fst))
in (FStar_Syntax_Syntax.null_binder uu____771))
in (

let uu____777 = (

let uu____779 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____779)::[])
in (uu____770)::uu____777))
in (uu____767)::uu____768))
in (

let uu____780 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____763 uu____780)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (

let uu____787 = (

let uu____791 = (FStar_Syntax_Syntax.mk_binder a)
in (uu____791)::[])
in (

let uu____792 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____787 uu____792)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let uu____796 = (FStar_Syntax_Util.type_u ())
in (match (uu____796) with
| (t, uu____800) -> begin
(

let expected_k = (

let uu____804 = (

let uu____808 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____809 = (

let uu____811 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____811)::[])
in (uu____808)::uu____809))
in (

let uu____812 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow uu____804 uu____812)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let uu____815 = (

let uu____821 = (

let uu____822 = (FStar_Syntax_Subst.compress ed.FStar_Syntax_Syntax.repr)
in uu____822.FStar_Syntax_Syntax.n)
in (match (uu____821) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((ed.FStar_Syntax_Syntax.repr), (ed.FStar_Syntax_Syntax.bind_repr), (ed.FStar_Syntax_Syntax.return_repr), (ed.FStar_Syntax_Syntax.actions))
end
| uu____831 -> begin
(

let repr = (

let uu____833 = (FStar_Syntax_Util.type_u ())
in (match (uu____833) with
| (t, uu____837) -> begin
(

let expected_k = (

let uu____841 = (

let uu____845 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____846 = (

let uu____848 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____848)::[])
in (uu____845)::uu____846))
in (

let uu____849 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow uu____841 uu____849)))
in (tc_check_trivial_guard env ed.FStar_Syntax_Syntax.repr expected_k))
end))
in (

let mk_repr' = (fun t wp -> (

let repr = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env repr)
in (

let uu____862 = (

let uu____865 = (

let uu____866 = (

let uu____876 = (

let uu____878 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____879 = (

let uu____881 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____881)::[])
in (uu____878)::uu____879))
in ((repr), (uu____876)))
in FStar_Syntax_Syntax.Tm_app (uu____866))
in (FStar_Syntax_Syntax.mk uu____865))
in (uu____862 None FStar_Range.dummyRange))))
in (

let mk_repr = (fun a wp -> (

let uu____900 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_repr' uu____900 wp)))
in (

let destruct_repr = (fun t -> (

let uu____911 = (

let uu____912 = (FStar_Syntax_Subst.compress t)
in uu____912.FStar_Syntax_Syntax.n)
in (match (uu____911) with
| FStar_Syntax_Syntax.Tm_app (uu____921, ((t, uu____923))::((wp, uu____925))::[]) -> begin
((t), (wp))
end
| uu____959 -> begin
(failwith "Unexpected repr type")
end)))
in (

let bind_repr = (

let r = (

let uu____968 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_0 FStar_Syntax_Syntax.Delta_constant None)
in (FStar_All.pipe_right uu____968 FStar_Syntax_Syntax.fv_to_tm))
in (

let uu____969 = (fresh_effect_signature ())
in (match (uu____969) with
| (b, wp_b) -> begin
(

let a_wp_b = (

let uu____983 = (

let uu____987 = (

let uu____988 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____988))
in (uu____987)::[])
in (

let uu____989 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____983 uu____989)))
in (

let wp_f = (FStar_Syntax_Syntax.gen_bv "wp_f" None wp_a)
in (

let wp_g = (FStar_Syntax_Syntax.gen_bv "wp_g" None a_wp_b)
in (

let x_a = (

let uu____995 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None uu____995))
in (

let wp_g_x = (

let uu____999 = (

let uu____1000 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (

let uu____1001 = (

let uu____1002 = (

let uu____1003 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____1003))
in (uu____1002)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____1000 uu____1001)))
in (uu____999 None FStar_Range.dummyRange))
in (

let res = (

let wp = (

let uu____1014 = (

let uu____1015 = (

let uu____1016 = (FStar_TypeChecker_Env.inst_tscheme bind_wp)
in (FStar_All.pipe_right uu____1016 Prims.snd))
in (

let uu____1021 = (

let uu____1022 = (

let uu____1024 = (

let uu____1026 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____1027 = (

let uu____1029 = (FStar_Syntax_Syntax.bv_to_name b)
in (

let uu____1030 = (

let uu____1032 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (

let uu____1033 = (

let uu____1035 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (uu____1035)::[])
in (uu____1032)::uu____1033))
in (uu____1029)::uu____1030))
in (uu____1026)::uu____1027))
in (r)::uu____1024)
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1022))
in (FStar_Syntax_Syntax.mk_Tm_app uu____1015 uu____1021)))
in (uu____1014 None FStar_Range.dummyRange))
in (mk_repr b wp))
in (

let expected_k = (

let uu____1043 = (

let uu____1047 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1048 = (

let uu____1050 = (FStar_Syntax_Syntax.mk_binder b)
in (

let uu____1051 = (

let uu____1053 = (FStar_Syntax_Syntax.mk_binder wp_f)
in (

let uu____1054 = (

let uu____1056 = (

let uu____1057 = (

let uu____1058 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (mk_repr a uu____1058))
in (FStar_Syntax_Syntax.null_binder uu____1057))
in (

let uu____1059 = (

let uu____1061 = (FStar_Syntax_Syntax.mk_binder wp_g)
in (

let uu____1062 = (

let uu____1064 = (

let uu____1065 = (

let uu____1066 = (

let uu____1070 = (FStar_Syntax_Syntax.mk_binder x_a)
in (uu____1070)::[])
in (

let uu____1071 = (

let uu____1074 = (mk_repr b wp_g_x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____1074))
in (FStar_Syntax_Util.arrow uu____1066 uu____1071)))
in (FStar_Syntax_Syntax.null_binder uu____1065))
in (uu____1064)::[])
in (uu____1061)::uu____1062))
in (uu____1056)::uu____1059))
in (uu____1053)::uu____1054))
in (uu____1050)::uu____1051))
in (uu____1047)::uu____1048))
in (

let uu____1075 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow uu____1043 uu____1075)))
in (

let uu____1078 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (uu____1078) with
| (expected_k, uu____1083, uu____1084) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos)
in (

let env = (

let uu___100_1088 = env
in {FStar_TypeChecker_Env.solver = uu___100_1088.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___100_1088.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___100_1088.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___100_1088.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___100_1088.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___100_1088.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___100_1088.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___100_1088.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___100_1088.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___100_1088.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___100_1088.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___100_1088.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___100_1088.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___100_1088.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___100_1088.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___100_1088.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___100_1088.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___100_1088.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___100_1088.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___100_1088.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___100_1088.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___100_1088.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___100_1088.FStar_TypeChecker_Env.qname_and_index})
in (

let br = (check_and_gen' env ed.FStar_Syntax_Syntax.bind_repr expected_k)
in br)))
end)))))))))
end)))
in (

let return_repr = (

let x_a = (

let uu____1095 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None uu____1095))
in (

let res = (

let wp = (

let uu____1102 = (

let uu____1103 = (

let uu____1104 = (FStar_TypeChecker_Env.inst_tscheme return_wp)
in (FStar_All.pipe_right uu____1104 Prims.snd))
in (

let uu____1109 = (

let uu____1110 = (

let uu____1112 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____1113 = (

let uu____1115 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (uu____1115)::[])
in (uu____1112)::uu____1113))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1110))
in (FStar_Syntax_Syntax.mk_Tm_app uu____1103 uu____1109)))
in (uu____1102 None FStar_Range.dummyRange))
in (mk_repr a wp))
in (

let expected_k = (

let uu____1123 = (

let uu____1127 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1128 = (

let uu____1130 = (FStar_Syntax_Syntax.mk_binder x_a)
in (uu____1130)::[])
in (uu____1127)::uu____1128))
in (

let uu____1131 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow uu____1123 uu____1131)))
in (

let uu____1134 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (uu____1134) with
| (expected_k, uu____1142, uu____1143) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos)
in (

let uu____1146 = (check_and_gen' env ed.FStar_Syntax_Syntax.return_repr expected_k)
in (match (uu____1146) with
| (univs, repr) -> begin
(match (univs) with
| [] -> begin
(([]), (repr))
end
| uu____1158 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected universe-polymorphic return for effect"), (repr.FStar_Syntax_Syntax.pos)))))
end)
end)))
end)))))
in (

let actions = (

let check_action = (fun act -> (

let uu____1169 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env act.FStar_Syntax_Syntax.action_typ)
in (match (uu____1169) with
| (act_typ, uu____1174, g_t) -> begin
(

let env' = (FStar_TypeChecker_Env.set_expected_typ env act_typ)
in ((

let uu____1178 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____1178) with
| true -> begin
(

let uu____1179 = (FStar_Syntax_Print.term_to_string act.FStar_Syntax_Syntax.action_defn)
in (

let uu____1180 = (FStar_Syntax_Print.term_to_string act_typ)
in (FStar_Util.print3 "Checking action %s:\n[definition]: %s\n[cps\'d type]: %s\n" (FStar_Ident.text_of_lid act.FStar_Syntax_Syntax.action_name) uu____1179 uu____1180)))
end
| uu____1181 -> begin
()
end));
(

let uu____1182 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' act.FStar_Syntax_Syntax.action_defn)
in (match (uu____1182) with
| (act_defn, uu____1187, g_a) -> begin
(

let act_defn = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env act_defn)
in (

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
in (

let uu____1191 = (

let act_typ = (FStar_Syntax_Subst.compress act_typ)
in (match (act_typ.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____1209 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____1209) with
| (bs, uu____1215) -> begin
(

let res = (mk_repr' FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun)
in (

let k = (

let uu____1222 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs uu____1222))
in (

let uu____1225 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env k)
in (match (uu____1225) with
| (k, uu____1232, g) -> begin
((k), (g))
end))))
end))
end
| uu____1234 -> begin
(

let uu____1235 = (

let uu____1236 = (

let uu____1239 = (

let uu____1240 = (FStar_Syntax_Print.term_to_string act_typ)
in (

let uu____1241 = (FStar_Syntax_Print.tag_of_term act_typ)
in (FStar_Util.format2 "Actions must have function types (not: %s, a.k.a. %s)" uu____1240 uu____1241)))
in ((uu____1239), (act_defn.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____1236))
in (Prims.raise uu____1235))
end))
in (match (uu____1191) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env act_typ expected_k)
in ((

let uu____1248 = (

let uu____1249 = (

let uu____1250 = (FStar_TypeChecker_Rel.conj_guard g_t g)
in (FStar_TypeChecker_Rel.conj_guard g_k uu____1250))
in (FStar_TypeChecker_Rel.conj_guard g_a uu____1249))
in (FStar_TypeChecker_Rel.force_trivial_guard env uu____1248));
(

let act_typ = (

let uu____1254 = (

let uu____1255 = (FStar_Syntax_Subst.compress expected_k)
in uu____1255.FStar_Syntax_Syntax.n)
in (match (uu____1254) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____1272 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____1272) with
| (bs, c) -> begin
(

let uu____1279 = (destruct_repr (FStar_Syntax_Util.comp_result c))
in (match (uu____1279) with
| (a, wp) -> begin
(

let c = (

let uu____1299 = (

let uu____1300 = (env.FStar_TypeChecker_Env.universe_of env a)
in (uu____1300)::[])
in (

let uu____1301 = (

let uu____1307 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____1307)::[])
in {FStar_Syntax_Syntax.comp_univs = uu____1299; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a; FStar_Syntax_Syntax.effect_args = uu____1301; FStar_Syntax_Syntax.flags = []}))
in (

let uu____1308 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Util.arrow bs uu____1308)))
end))
end))
end
| uu____1311 -> begin
(failwith "")
end))
in (

let uu____1314 = (FStar_TypeChecker_Util.generalize_universes env act_defn)
in (match (uu____1314) with
| (univs, act_defn) -> begin
(

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
in (

let uu___101_1320 = act
in {FStar_Syntax_Syntax.action_name = uu___101_1320.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___101_1320.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = act_defn; FStar_Syntax_Syntax.action_typ = act_typ}))
end)));
))
end))))
end));
))
end)))
in (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.map check_action)))
in ((repr), (bind_repr), (return_repr), (actions)))))))))
end))
in (match (uu____815) with
| (repr, bind_repr, return_repr, actions) -> begin
(

let t = (

let uu____1336 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders uu____1336))
in (

let uu____1339 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (uu____1339) with
| (univs, t) -> begin
(

let signature = (

let uu____1345 = (

let uu____1348 = (

let uu____1349 = (FStar_Syntax_Subst.compress t)
in uu____1349.FStar_Syntax_Syntax.n)
in ((effect_params), (uu____1348)))
in (match (uu____1345) with
| ([], uu____1352) -> begin
t
end
| (uu____1358, FStar_Syntax_Syntax.Tm_arrow (uu____1359, c)) -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____1371 -> begin
(failwith "Impossible")
end))
in (

let close = (fun n ts -> (

let ts = (

let uu____1382 = (FStar_Syntax_Subst.close_tscheme effect_params ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs uu____1382))
in (

let m = (FStar_List.length (Prims.fst ts))
in ((

let uu____1387 = (((n >= (Prims.parse_int "0")) && (

let uu____1388 = (FStar_Syntax_Util.is_unknown (Prims.snd ts))
in (not (uu____1388)))) && (m <> n))
in (match (uu____1387) with
| true -> begin
(

let error = (match ((m < n)) with
| true -> begin
"not universe-polymorphic enough"
end
| uu____1396 -> begin
"too universe-polymorphic"
end)
in (

let uu____1397 = (

let uu____1398 = (FStar_Util.string_of_int n)
in (

let uu____1399 = (FStar_Syntax_Print.tscheme_to_string ts)
in (FStar_Util.format3 "The effect combinator is %s (n=%s) (%s)" error uu____1398 uu____1399)))
in (failwith uu____1397)))
end
| uu____1400 -> begin
()
end));
ts;
))))
in (

let close_action = (fun act -> (

let uu____1405 = (close (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_defn)))
in (match (uu____1405) with
| (univs, defn) -> begin
(

let uu____1410 = (close (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_typ)))
in (match (uu____1410) with
| (univs', typ) -> begin
(

let uu___102_1416 = act
in {FStar_Syntax_Syntax.action_name = uu___102_1416.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___102_1416.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = defn; FStar_Syntax_Syntax.action_typ = typ})
end))
end)))
in (

let nunivs = (FStar_List.length univs)
in (

let ed = (

let uu___103_1421 = ed
in (

let uu____1422 = (close (Prims.parse_int "0") return_wp)
in (

let uu____1423 = (close (Prims.parse_int "1") bind_wp)
in (

let uu____1424 = (close (Prims.parse_int "0") if_then_else)
in (

let uu____1425 = (close (Prims.parse_int "0") ite_wp)
in (

let uu____1426 = (close (Prims.parse_int "0") stronger)
in (

let uu____1427 = (close (Prims.parse_int "1") close_wp)
in (

let uu____1428 = (close (Prims.parse_int "0") assert_p)
in (

let uu____1429 = (close (Prims.parse_int "0") assume_p)
in (

let uu____1430 = (close (Prims.parse_int "0") null_wp)
in (

let uu____1431 = (close (Prims.parse_int "0") trivial_wp)
in (

let uu____1432 = (

let uu____1433 = (close (Prims.parse_int "0") (([]), (repr)))
in (Prims.snd uu____1433))
in (

let uu____1439 = (close (Prims.parse_int "0") return_repr)
in (

let uu____1440 = (close (Prims.parse_int "1") bind_repr)
in (

let uu____1441 = (FStar_List.map close_action actions)
in {FStar_Syntax_Syntax.qualifiers = uu___103_1421.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___103_1421.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___103_1421.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = uu____1422; FStar_Syntax_Syntax.bind_wp = uu____1423; FStar_Syntax_Syntax.if_then_else = uu____1424; FStar_Syntax_Syntax.ite_wp = uu____1425; FStar_Syntax_Syntax.stronger = uu____1426; FStar_Syntax_Syntax.close_wp = uu____1427; FStar_Syntax_Syntax.assert_p = uu____1428; FStar_Syntax_Syntax.assume_p = uu____1429; FStar_Syntax_Syntax.null_wp = uu____1430; FStar_Syntax_Syntax.trivial = uu____1431; FStar_Syntax_Syntax.repr = uu____1432; FStar_Syntax_Syntax.return_repr = uu____1439; FStar_Syntax_Syntax.bind_repr = uu____1440; FStar_Syntax_Syntax.actions = uu____1441})))))))))))))))
in ((

let uu____1444 = ((FStar_TypeChecker_Env.debug env FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ED"))))
in (match (uu____1444) with
| true -> begin
(

let uu____1445 = (FStar_Syntax_Print.eff_decl_to_string false ed)
in (FStar_Util.print_string uu____1445))
end
| uu____1446 -> begin
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
and cps_and_elaborate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.sigelt Prims.option) = (fun env ed -> (

let uu____1449 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____1449) with
| (effect_binders_un, signature_un) -> begin
(

let uu____1459 = (tc_tparams env effect_binders_un)
in (match (uu____1459) with
| (effect_binders, env, uu____1470) -> begin
(

let uu____1471 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (uu____1471) with
| (signature, uu____1480) -> begin
(

let effect_binders = (FStar_List.map (fun uu____1489 -> (match (uu____1489) with
| (bv, qual) -> begin
(

let uu____1496 = (

let uu___104_1497 = bv
in (

let uu____1498 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___104_1497.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___104_1497.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1498}))
in ((uu____1496), (qual)))
end)) effect_binders)
in (

let uu____1501 = (

let uu____1506 = (

let uu____1507 = (FStar_Syntax_Subst.compress signature_un)
in uu____1507.FStar_Syntax_Syntax.n)
in (match (uu____1506) with
| FStar_Syntax_Syntax.Tm_arrow (((a, uu____1515))::[], effect_marker) -> begin
((a), (effect_marker))
end
| uu____1530 -> begin
(failwith "bad shape for effect-for-free signature")
end))
in (match (uu____1501) with
| (a, effect_marker) -> begin
(

let a = (

let uu____1547 = (FStar_Syntax_Syntax.is_null_bv a)
in (match (uu____1547) with
| true -> begin
(

let uu____1548 = (

let uu____1550 = (FStar_Syntax_Syntax.range_of_bv a)
in Some (uu____1550))
in (FStar_Syntax_Syntax.gen_bv "a" uu____1548 a.FStar_Syntax_Syntax.sort))
end
| uu____1551 -> begin
a
end))
in (

let open_and_check = (fun t -> (

let subst = (FStar_Syntax_Subst.opening_of_binders effect_binders)
in (

let t = (FStar_Syntax_Subst.subst subst t)
in (

let uu____1560 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (uu____1560) with
| (t, comp, uu____1568) -> begin
((t), (comp))
end)))))
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None signature.FStar_Syntax_Syntax.pos))
in (

let uu____1579 = (open_and_check ed.FStar_Syntax_Syntax.repr)
in (match (uu____1579) with
| (repr, _comp) -> begin
((

let uu____1590 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____1590) with
| true -> begin
(

let uu____1591 = (FStar_Syntax_Print.term_to_string repr)
in (FStar_Util.print1 "Representation is: %s\n" uu____1591))
end
| uu____1592 -> begin
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

let uu____1597 = (

let uu____1598 = (

let uu____1599 = (

let uu____1609 = (

let uu____1613 = (

let uu____1616 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____1617 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____1616), (uu____1617))))
in (uu____1613)::[])
in ((wp_type), (uu____1609)))
in FStar_Syntax_Syntax.Tm_app (uu____1599))
in (mk uu____1598))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env uu____1597))
in (

let effect_signature = (

let binders = (

let uu____1632 = (

let uu____1635 = (FStar_Syntax_Syntax.as_implicit false)
in ((a), (uu____1635)))
in (

let uu____1636 = (

let uu____1640 = (

let uu____1641 = (FStar_Syntax_Syntax.gen_bv "dijkstra_wp" None wp_a)
in (FStar_All.pipe_right uu____1641 FStar_Syntax_Syntax.mk_binder))
in (uu____1640)::[])
in (uu____1632)::uu____1636))
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

let uu____1674 = item
in (match (uu____1674) with
| (u_item, item) -> begin
(

let uu____1686 = (open_and_check item)
in (match (uu____1686) with
| (item, item_comp) -> begin
((

let uu____1696 = (

let uu____1697 = (FStar_Syntax_Util.is_total_lcomp item_comp)
in (not (uu____1697)))
in (match (uu____1696) with
| true -> begin
(

let uu____1698 = (

let uu____1699 = (

let uu____1700 = (FStar_Syntax_Print.term_to_string item)
in (

let uu____1701 = (FStar_Syntax_Print.lcomp_to_string item_comp)
in (FStar_Util.format2 "Computation for [%s] is not total : %s !" uu____1700 uu____1701)))
in FStar_Errors.Err (uu____1699))
in (Prims.raise uu____1698))
end
| uu____1702 -> begin
()
end));
(

let uu____1703 = (FStar_TypeChecker_DMFF.star_expr dmff_env item)
in (match (uu____1703) with
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

let uu____1716 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.bind_repr)
in (match (uu____1716) with
| (dmff_env, uu____1727, bind_wp, bind_elab) -> begin
(

let uu____1730 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.return_repr)
in (match (uu____1730) with
| (dmff_env, uu____1741, return_wp, return_elab) -> begin
(

let lift_from_pure_wp = (

let uu____1745 = (

let uu____1746 = (FStar_Syntax_Subst.compress return_wp)
in uu____1746.FStar_Syntax_Syntax.n)
in (match (uu____1745) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(

let uu____1784 = (

let uu____1792 = (

let uu____1795 = (FStar_Syntax_Util.abs bs body None)
in (FStar_Syntax_Subst.open_term ((b1)::(b2)::[]) uu____1795))
in (match (uu____1792) with
| ((b1)::(b2)::[], body) -> begin
((b1), (b2), (body))
end
| uu____1834 -> begin
(failwith "Impossible : open_term not preserving binders arity")
end))
in (match (uu____1784) with
| (b1, b2, body) -> begin
(

let env0 = (

let uu____1856 = (FStar_TypeChecker_DMFF.get_env dmff_env)
in (FStar_TypeChecker_Env.push_binders uu____1856 ((b1)::(b2)::[])))
in (

let wp_b1 = (

let uu____1864 = (

let uu____1865 = (

let uu____1866 = (

let uu____1876 = (

let uu____1880 = (

let uu____1883 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b1))
in (

let uu____1884 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____1883), (uu____1884))))
in (uu____1880)::[])
in ((wp_type), (uu____1876)))
in FStar_Syntax_Syntax.Tm_app (uu____1866))
in (mk uu____1865))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env0 uu____1864))
in (

let uu____1892 = (

let uu____1902 = (

let uu____1903 = (FStar_Syntax_Util.unascribe wp_b1)
in (FStar_TypeChecker_Normalize.eta_expand_with_type body uu____1903))
in (FStar_All.pipe_left FStar_Syntax_Util.abs_formals uu____1902))
in (match (uu____1892) with
| (bs, body, what') -> begin
(

let t2 = (Prims.fst b2).FStar_Syntax_Syntax.sort
in (

let pure_wp_type = (FStar_TypeChecker_DMFF.double_star t2)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None pure_wp_type)
in (

let body = (

let uu____1936 = (

let uu____1937 = (FStar_Syntax_Syntax.bv_to_name wp)
in (

let uu____1938 = (

let uu____1939 = (

let uu____1943 = (FStar_Syntax_Util.abs ((b2)::[]) body what')
in ((uu____1943), (None)))
in (uu____1939)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____1937 uu____1938)))
in (uu____1936 None FStar_Range.dummyRange))
in (

let uu____1959 = (

let uu____1963 = (

let uu____1967 = (FStar_Syntax_Syntax.mk_binder wp)
in (uu____1967)::[])
in (b1)::uu____1963)
in (

let uu____1970 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs uu____1959 uu____1970 (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_GTot_lid), ([]))))))))))))
end))))
end))
end
| uu____1980 -> begin
(failwith "unexpected shape for return")
end))
in (

let return_wp = (

let uu____1982 = (

let uu____1983 = (FStar_Syntax_Subst.compress return_wp)
in uu____1983.FStar_Syntax_Syntax.n)
in (match (uu____1982) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(

let uu____2021 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs ((b1)::(b2)::[]) uu____2021 (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_GTot_lid), ([])))))))
end
| uu____2037 -> begin
(failwith "unexpected shape for return")
end))
in (

let bind_wp = (

let uu____2039 = (

let uu____2040 = (FStar_Syntax_Subst.compress bind_wp)
in uu____2040.FStar_Syntax_Syntax.n)
in (match (uu____2039) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let r = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (

let uu____2069 = (

let uu____2073 = (

let uu____2075 = (

let uu____2076 = (mk (FStar_Syntax_Syntax.Tm_fvar (r)))
in (FStar_Syntax_Syntax.null_binder uu____2076))
in (uu____2075)::[])
in (FStar_List.append uu____2073 binders))
in (FStar_Syntax_Util.abs uu____2069 body what)))
end
| uu____2077 -> begin
(failwith "unexpected shape for bind")
end))
in (

let apply_close = (fun t -> (match (((FStar_List.length effect_binders) = (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____2094 -> begin
(

let uu____2095 = (

let uu____2096 = (

let uu____2097 = (

let uu____2107 = (

let uu____2108 = (FStar_Syntax_Util.args_of_binders effect_binders)
in (Prims.snd uu____2108))
in ((t), (uu____2107)))
in FStar_Syntax_Syntax.Tm_app (uu____2097))
in (mk uu____2096))
in (FStar_Syntax_Subst.close effect_binders uu____2095))
end))
in (

let register = (fun name item -> (

let uu____2120 = (

let uu____2123 = (mk_lid name)
in (

let uu____2124 = (FStar_Syntax_Util.abs effect_binders item None)
in (FStar_TypeChecker_Util.mk_toplevel_definition env uu____2123 uu____2124)))
in (match (uu____2120) with
| (sigelt, fv) -> begin
((

let uu____2133 = (

let uu____2135 = (FStar_ST.read sigelts)
in (sigelt)::uu____2135)
in (FStar_ST.write sigelts uu____2133));
fv;
)
end)))
in (

let lift_from_pure_wp = (register "lift_from_pure" lift_from_pure_wp)
in (

let return_wp = (register "return_wp" return_wp)
in ((

let uu____2146 = (

let uu____2148 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true")), (FStar_Range.dummyRange))))::uu____2148)
in (FStar_ST.write sigelts uu____2146));
(

let return_elab = (register "return_elab" return_elab)
in ((

let uu____2158 = (

let uu____2160 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false")), (FStar_Range.dummyRange))))::uu____2160)
in (FStar_ST.write sigelts uu____2158));
(

let bind_wp = (register "bind_wp" bind_wp)
in ((

let uu____2170 = (

let uu____2172 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true")), (FStar_Range.dummyRange))))::uu____2172)
in (FStar_ST.write sigelts uu____2170));
(

let bind_elab = (register "bind_elab" bind_elab)
in ((

let uu____2182 = (

let uu____2184 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false")), (FStar_Range.dummyRange))))::uu____2184)
in (FStar_ST.write sigelts uu____2182));
(

let uu____2192 = (FStar_List.fold_left (fun uu____2199 action -> (match (uu____2199) with
| (dmff_env, actions) -> begin
(

let uu____2211 = (elaborate_and_star dmff_env ((action.FStar_Syntax_Syntax.action_univs), (action.FStar_Syntax_Syntax.action_defn)))
in (match (uu____2211) with
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

let uu____2227 = (

let uu____2229 = (

let uu___105_2230 = action
in (

let uu____2231 = (apply_close action_elab)
in (

let uu____2232 = (apply_close action_typ_with_wp)
in {FStar_Syntax_Syntax.action_name = uu___105_2230.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___105_2230.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___105_2230.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = uu____2231; FStar_Syntax_Syntax.action_typ = uu____2232})))
in (uu____2229)::actions)
in ((dmff_env), (uu____2227)))))))
end))
end)) ((dmff_env), ([])) ed.FStar_Syntax_Syntax.actions)
in (match (uu____2192) with
| (dmff_env, actions) -> begin
(

let actions = (FStar_List.rev actions)
in (

let repr = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp_a" None wp_a)
in (

let binders = (

let uu____2250 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____2251 = (

let uu____2253 = (FStar_Syntax_Syntax.mk_binder wp)
in (uu____2253)::[])
in (uu____2250)::uu____2251))
in (

let uu____2254 = (

let uu____2255 = (

let uu____2256 = (

let uu____2257 = (

let uu____2267 = (

let uu____2271 = (

let uu____2274 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____2275 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____2274), (uu____2275))))
in (uu____2271)::[])
in ((repr), (uu____2267)))
in FStar_Syntax_Syntax.Tm_app (uu____2257))
in (mk uu____2256))
in (

let uu____2283 = (FStar_Syntax_Syntax.bv_to_name wp)
in (FStar_TypeChecker_DMFF.trans_F dmff_env uu____2255 uu____2283)))
in (FStar_Syntax_Util.abs binders uu____2254 None))))
in (

let repr = (recheck_debug "FC" env repr)
in (

let repr = (register "repr" repr)
in (

let uu____2291 = (

let uu____2296 = (

let uu____2297 = (

let uu____2300 = (FStar_Syntax_Subst.compress wp_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____2300))
in uu____2297.FStar_Syntax_Syntax.n)
in (match (uu____2296) with
| FStar_Syntax_Syntax.Tm_abs ((type_param)::effect_param, arrow, uu____2308) -> begin
(

let uu____2335 = (

let uu____2344 = (FStar_Syntax_Subst.open_term ((type_param)::effect_param) arrow)
in (match (uu____2344) with
| ((b)::bs, body) -> begin
((b), (bs), (body))
end
| uu____2375 -> begin
(failwith "Impossible : open_term nt preserving binders arity")
end))
in (match (uu____2335) with
| (type_param, effect_param, arrow) -> begin
(

let uu____2403 = (

let uu____2404 = (

let uu____2407 = (FStar_Syntax_Subst.compress arrow)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____2407))
in uu____2404.FStar_Syntax_Syntax.n)
in (match (uu____2403) with
| FStar_Syntax_Syntax.Tm_arrow (wp_binders, c) -> begin
(

let uu____2424 = (FStar_Syntax_Subst.open_comp wp_binders c)
in (match (uu____2424) with
| (wp_binders, c) -> begin
(

let uu____2433 = (FStar_List.partition (fun uu____2444 -> (match (uu____2444) with
| (bv, uu____2448) -> begin
(

let uu____2449 = (

let uu____2450 = (FStar_Syntax_Free.names bv.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____2450 (FStar_Util.set_mem (Prims.fst type_param))))
in (FStar_All.pipe_right uu____2449 Prims.op_Negation))
end)) wp_binders)
in (match (uu____2433) with
| (pre_args, post_args) -> begin
(

let post = (match (post_args) with
| (post)::[] -> begin
post
end
| uu____2483 -> begin
(

let uu____2487 = (

let uu____2488 = (FStar_Syntax_Print.term_to_string arrow)
in (FStar_Util.format1 "Impossible: multiple post candidates %s" uu____2488))
in (failwith uu____2487))
end)
in (

let uu____2491 = (FStar_Syntax_Util.arrow pre_args c)
in (

let uu____2494 = (FStar_Syntax_Util.abs ((type_param)::effect_param) (Prims.fst post).FStar_Syntax_Syntax.sort None)
in ((uu____2491), (uu____2494)))))
end))
end))
end
| uu____2504 -> begin
(

let uu____2505 = (

let uu____2506 = (FStar_Syntax_Print.term_to_string arrow)
in (FStar_Util.format1 "Impossible: pre/post arrow %s" uu____2506))
in (failwith uu____2505))
end))
end))
end
| uu____2511 -> begin
(

let uu____2512 = (

let uu____2513 = (FStar_Syntax_Print.term_to_string wp_type)
in (FStar_Util.format1 "Impossible: pre/post abs %s" uu____2513))
in (failwith uu____2512))
end))
in (match (uu____2291) with
| (pre, post) -> begin
((

let uu____2530 = (register "pre" pre)
in ());
(

let uu____2532 = (register "post" post)
in ());
(

let uu____2534 = (register "wp" wp_type)
in ());
(

let ed = (

let uu___106_2536 = ed
in (

let uu____2537 = (FStar_Syntax_Subst.close_binders effect_binders)
in (

let uu____2538 = (FStar_Syntax_Subst.close effect_binders effect_signature)
in (

let uu____2539 = (

let uu____2540 = (apply_close return_wp)
in (([]), (uu____2540)))
in (

let uu____2546 = (

let uu____2547 = (apply_close bind_wp)
in (([]), (uu____2547)))
in (

let uu____2553 = (apply_close repr)
in (

let uu____2554 = (

let uu____2555 = (apply_close return_elab)
in (([]), (uu____2555)))
in (

let uu____2561 = (

let uu____2562 = (apply_close bind_elab)
in (([]), (uu____2562)))
in {FStar_Syntax_Syntax.qualifiers = uu___106_2536.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___106_2536.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___106_2536.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___106_2536.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu____2537; FStar_Syntax_Syntax.signature = uu____2538; FStar_Syntax_Syntax.ret_wp = uu____2539; FStar_Syntax_Syntax.bind_wp = uu____2546; FStar_Syntax_Syntax.if_then_else = uu___106_2536.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = uu___106_2536.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = uu___106_2536.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = uu___106_2536.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = uu___106_2536.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = uu___106_2536.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = uu___106_2536.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = uu___106_2536.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = uu____2553; FStar_Syntax_Syntax.return_repr = uu____2554; FStar_Syntax_Syntax.bind_repr = uu____2561; FStar_Syntax_Syntax.actions = actions}))))))))
in (

let uu____2568 = (FStar_TypeChecker_DMFF.gen_wps_for_free env effect_binders a wp_a ed)
in (match (uu____2568) with
| (sigelts', ed) -> begin
((

let uu____2579 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____2579) with
| true -> begin
(

let uu____2580 = (FStar_Syntax_Print.eff_decl_to_string true ed)
in (FStar_Util.print_string uu____2580))
end
| uu____2581 -> begin
()
end));
(

let lift_from_pure_opt = (match (((FStar_List.length effect_binders) = (Prims.parse_int "0"))) with
| true -> begin
(

let lift_from_pure = (

let uu____2590 = (

let uu____2592 = (

let uu____2598 = (apply_close lift_from_pure_wp)
in (([]), (uu____2598)))
in Some (uu____2592))
in {FStar_Syntax_Syntax.source = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.target = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.lift_wp = uu____2590; FStar_Syntax_Syntax.lift = None})
in Some (FStar_Syntax_Syntax.Sig_sub_effect (((lift_from_pure), (FStar_Range.dummyRange)))))
end
| uu____2609 -> begin
None
end)
in (

let uu____2610 = (

let uu____2612 = (

let uu____2614 = (FStar_ST.read sigelts)
in (FStar_List.rev uu____2614))
in (FStar_List.append uu____2612 sigelts'))
in ((uu____2610), (ed), (lift_from_pure_opt))));
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
| (FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, uu____2637, uu____2638, [], r))::(FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, _0_28, [], uu____2643, r1))::(FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, _0_29, [], uu____2648, r2))::[] when (((_0_28 = (Prims.parse_int "0")) && (_0_29 = (Prims.parse_int "0"))) && (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid))) -> begin
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

let uu____2692 = (

let uu____2695 = (

let uu____2696 = (

let uu____2701 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1) FStar_Syntax_Syntax.Delta_constant None)
in ((uu____2701), ((FStar_Syntax_Syntax.U_name (utop))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____2696))
in (FStar_Syntax_Syntax.mk uu____2695))
in (uu____2692 None r1))
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

let uu____2722 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) uu____2722))
in (

let hd = (

let uu____2728 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) uu____2728))
in (

let tl = (

let uu____2730 = (

let uu____2731 = (

let uu____2734 = (

let uu____2735 = (

let uu____2740 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2) FStar_Syntax_Syntax.Delta_constant None)
in ((uu____2740), ((FStar_Syntax_Syntax.U_name (ucons2))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____2735))
in (FStar_Syntax_Syntax.mk uu____2734))
in (uu____2731 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) uu____2730))
in (

let res = (

let uu____2753 = (

let uu____2756 = (

let uu____2757 = (

let uu____2762 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2) FStar_Syntax_Syntax.Delta_constant None)
in ((uu____2762), ((FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____2757))
in (FStar_Syntax_Syntax.mk uu____2756))
in (uu____2753 None r2))
in (

let uu____2772 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow ((((a), (Some (FStar_Syntax_Syntax.imp_tag))))::(((hd), (None)))::(((tl), (None)))::[]) uu____2772))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon (((lex_cons), ((ucons1)::(ucons2)::[]), (lex_cons_t), (FStar_Syntax_Const.lex_t_lid), ((Prims.parse_int "0")), ([]), ([]), (r2)))
in (

let uu____2795 = (

let uu____2803 = (FStar_TypeChecker_Env.get_range env)
in (((tc)::(dc_lextop)::(dc_lexcons)::[]), ([]), (lids), (uu____2803)))
in FStar_Syntax_Syntax.Sig_bundle (uu____2795)))))))))))))))
end
| uu____2807 -> begin
(

let uu____2809 = (

let uu____2810 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle (((ses), ([]), (lids), (FStar_Range.dummyRange)))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" uu____2810))
in (failwith uu____2809))
end))
and tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let uu____2821 = (FStar_Syntax_Util.type_u ())
in (match (uu____2821) with
| (k, uu____2825) -> begin
(

let phi = (

let uu____2827 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right uu____2827 (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env)))
in ((FStar_TypeChecker_Util.check_uvars r phi);
FStar_Syntax_Syntax.Sig_assume (((lid), (phi), (quals), (r)));
))
end))))
and tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env ses quals lids -> (

let warn_positivity = (fun l r -> (

let uu____2844 = (

let uu____2845 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" uu____2845))
in (FStar_Errors.diag r uu____2844)))
in (

let env0 = env
in (

let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
((warn_positivity tc r);
(

let uu____2882 = (FStar_Syntax_Subst.open_term tps k)
in (match (uu____2882) with
| (tps, k) -> begin
(

let uu____2891 = (FStar_TypeChecker_TcTerm.tc_binders env tps)
in (match (uu____2891) with
| (tps, env_tps, guard_params, us) -> begin
(

let uu____2904 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____2904) with
| (indices, t) -> begin
(

let uu____2928 = (FStar_TypeChecker_TcTerm.tc_binders env_tps indices)
in (match (uu____2928) with
| (indices, env', guard_indices, us') -> begin
(

let uu____2941 = (

let uu____2944 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' t)
in (match (uu____2944) with
| (t, uu____2951, g) -> begin
(

let uu____2953 = (

let uu____2954 = (

let uu____2955 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params uu____2955))
in (FStar_TypeChecker_Rel.discharge_guard env' uu____2954))
in ((t), (uu____2953)))
end))
in (match (uu____2941) with
| (t, guard) -> begin
(

let k = (

let uu____2965 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices uu____2965))
in (

let uu____2968 = (FStar_Syntax_Util.type_u ())
in (match (uu____2968) with
| (t_type, u) -> begin
((

let uu____2978 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' uu____2978));
(

let t_tc = (

let uu____2982 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) uu____2982))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____2990 = (FStar_TypeChecker_Env.push_let_binding env (FStar_Util.Inr (fv_tc)) (([]), (t_tc)))
in ((uu____2990), (FStar_Syntax_Syntax.Sig_inductive_typ (((tc), ([]), (tps), (k), (mutuals), (data), (quals), (r)))), (u), (guard)))))));
)
end)))
end))
end))
end))
end))
end));
)
end
| uu____2998 -> begin
(failwith "impossible")
end))
in (

let positive_if_pure = (fun uu____3008 l -> ())
in (

let tc_data = (fun env tcs uu___83_3024 -> (match (uu___83_3024) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let uu____3043 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun uu____3057 -> (match (uu____3057) with
| (se, u_tc) -> begin
(

let uu____3066 = (

let uu____3067 = (

let uu____3068 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must uu____3068))
in (FStar_Ident.lid_equals tc_lid uu____3067))
in (match (uu____3066) with
| true -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____3078, uu____3079, tps, uu____3081, uu____3082, uu____3083, uu____3084, uu____3085) -> begin
(

let tps = (FStar_All.pipe_right tps (FStar_List.map (fun uu____3106 -> (match (uu____3106) with
| (x, uu____3113) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let tps = (FStar_Syntax_Subst.open_binders tps)
in (

let uu____3116 = (

let uu____3120 = (FStar_TypeChecker_Env.push_binders env tps)
in ((uu____3120), (tps), (u_tc)))
in Some (uu____3116))))
end
| uu____3124 -> begin
(failwith "Impossible")
end)
end
| uu____3129 -> begin
None
end))
end)))
in (match (tps_u_opt) with
| Some (x) -> begin
x
end
| None -> begin
(match ((FStar_Ident.lid_equals tc_lid FStar_Syntax_Const.exn_lid)) with
| true -> begin
((env), ([]), (FStar_Syntax_Syntax.U_zero))
end
| uu____3154 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected data constructor"), (r)))))
end)
end))
in (match (uu____3043) with
| (env, tps, u_tc) -> begin
(

let uu____3163 = (

let uu____3171 = (

let uu____3172 = (FStar_Syntax_Subst.compress t)
in uu____3172.FStar_Syntax_Syntax.n)
in (match (uu____3171) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let uu____3194 = (FStar_Util.first_N ntps bs)
in (match (uu____3194) with
| (uu____3212, bs') -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs'), (res)))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i uu____3244 -> (match (uu____3244) with
| (x, uu____3248) -> begin
FStar_Syntax_Syntax.DB ((((ntps - ((Prims.parse_int "1") + i))), (x)))
end))))
in (

let uu____3249 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals uu____3249))))
end))
end
| uu____3250 -> begin
(([]), (t))
end))
in (match (uu____3163) with
| (arguments, result) -> begin
((

let uu____3271 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____3271) with
| true -> begin
(

let uu____3272 = (FStar_Syntax_Print.lid_to_string c)
in (

let uu____3273 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (

let uu____3274 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" uu____3272 uu____3273 uu____3274))))
end
| uu____3275 -> begin
()
end));
(

let uu____3276 = (tc_tparams env arguments)
in (match (uu____3276) with
| (arguments, env', us) -> begin
(

let uu____3285 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env' result)
in (match (uu____3285) with
| (result, res_lcomp) -> begin
((

let uu____3293 = (

let uu____3294 = (FStar_Syntax_Subst.compress res_lcomp.FStar_Syntax_Syntax.res_typ)
in uu____3294.FStar_Syntax_Syntax.n)
in (match (uu____3293) with
| FStar_Syntax_Syntax.Tm_type (uu____3297) -> begin
()
end
| ty -> begin
(

let uu____3299 = (

let uu____3300 = (

let uu____3303 = (

let uu____3304 = (FStar_Syntax_Print.term_to_string result)
in (

let uu____3305 = (FStar_Syntax_Print.term_to_string res_lcomp.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "The type of %s is %s, but since this is the result type of a constructor its type should be Type" uu____3304 uu____3305)))
in ((uu____3303), (r)))
in FStar_Errors.Error (uu____3300))
in (Prims.raise uu____3299))
end));
(

let uu____3306 = (FStar_Syntax_Util.head_and_args result)
in (match (uu____3306) with
| (head, uu____3319) -> begin
((

let uu____3335 = (

let uu____3336 = (FStar_Syntax_Subst.compress head)
in uu____3336.FStar_Syntax_Syntax.n)
in (match (uu____3335) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| uu____3340 -> begin
(

let uu____3341 = (

let uu____3342 = (

let uu____3345 = (

let uu____3346 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (

let uu____3347 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" uu____3346 uu____3347)))
in ((uu____3345), (r)))
in FStar_Errors.Error (uu____3342))
in (Prims.raise uu____3341))
end));
(

let g = (FStar_List.fold_left2 (fun g uu____3352 u_x -> (match (uu____3352) with
| (x, uu____3357) -> begin
(

let uu____3359 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g uu____3359))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (

let uu____3363 = (

let uu____3367 = (FStar_All.pipe_right tps (FStar_List.map (fun uu____3381 -> (match (uu____3381) with
| (x, uu____3388) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append uu____3367 arguments))
in (

let uu____3393 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow uu____3363 uu____3393)))
in ((FStar_Syntax_Syntax.Sig_datacon (((c), ([]), (t), (tc_lid), (ntps), (quals), ([]), (r)))), (g))));
)
end));
)
end))
end));
)
end))
end))
end
| uu____3401 -> begin
(failwith "impossible")
end))
in (

let generalize_and_inst_within = (fun env g tcs datas -> (

let tc_universe_vars = (FStar_List.map Prims.snd tcs)
in (

let g = (

let uu___107_3434 = g
in {FStar_TypeChecker_Env.guard_f = uu___107_3434.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___107_3434.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = ((tc_universe_vars), ((Prims.snd g.FStar_TypeChecker_Env.univ_ineqs))); FStar_TypeChecker_Env.implicits = uu___107_3434.FStar_TypeChecker_Env.implicits})
in ((

let uu____3440 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____3440) with
| true -> begin
(

let uu____3441 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print1 "@@@@@@Guard before generalization: %s\n" uu____3441))
end
| uu____3442 -> begin
()
end));
(FStar_TypeChecker_Rel.force_trivial_guard env g);
(

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun uu____3452 -> (match (uu____3452) with
| (se, uu____3456) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____3457, uu____3458, tps, k, uu____3461, uu____3462, uu____3463, uu____3464) -> begin
(

let uu____3471 = (

let uu____3472 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) uu____3472))
in (FStar_Syntax_Syntax.null_binder uu____3471))
end
| uu____3479 -> begin
(failwith "Impossible")
end)
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun uu___84_3484 -> (match (uu___84_3484) with
| FStar_Syntax_Syntax.Sig_datacon (uu____3485, uu____3486, t, uu____3488, uu____3489, uu____3490, uu____3491, uu____3492) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| uu____3497 -> begin
(failwith "Impossible")
end))))
in (

let t = (

let uu____3501 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') uu____3501))
in ((

let uu____3505 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____3505) with
| true -> begin
(

let uu____3506 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" uu____3506))
end
| uu____3507 -> begin
()
end));
(

let uu____3508 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (uu____3508) with
| (uvs, t) -> begin
((

let uu____3518 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____3518) with
| true -> begin
(

let uu____3519 = (

let uu____3520 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right uu____3520 (FStar_String.concat ", ")))
in (

let uu____3526 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" uu____3519 uu____3526)))
end
| uu____3527 -> begin
()
end));
(

let uu____3528 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____3528) with
| (uvs, t) -> begin
(

let uu____3537 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____3537) with
| (args, uu____3550) -> begin
(

let uu____3561 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (uu____3561) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun uu____3598 uu____3599 -> (match (((uu____3598), (uu____3599))) with
| ((x, uu____3609), (se, uu____3611)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____3617, tps, uu____3619, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let uu____3631 = (

let uu____3639 = (

let uu____3640 = (FStar_Syntax_Subst.compress ty)
in uu____3640.FStar_Syntax_Syntax.n)
in (match (uu____3639) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____3662 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (uu____3662) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____3705 -> begin
(

let uu____3709 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) uu____3709 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in ((tps), (t)))
end))
end
| uu____3728 -> begin
(([]), (ty))
end))
in (match (uu____3631) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs), (tps), (t), (mutuals), (datas), (quals), (r)))
end)))
end
| uu____3754 -> begin
(failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| uu____3758 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _0_30 -> FStar_Syntax_Syntax.U_name (_0_30))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun uu___85_3775 -> (match (uu___85_3775) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____3780, uu____3781, uu____3782, uu____3783, uu____3784, uu____3785, uu____3786) -> begin
((tc), (uvs_universes))
end
| uu____3794 -> begin
(failwith "Impossible")
end))))
in (FStar_List.map2 (fun uu____3800 d -> (match (uu____3800) with
| (t, uu____3805) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, uu____3807, uu____3808, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (

let uu____3819 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____3819 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon (((l), (uvs), (ty), (tc), (ntps), (quals), (mutuals), (r))))
end
| uu____3822 -> begin
(failwith "Impossible")
end)
end)) data_types datas)))
end)
in ((tcs), (datas))))
end))
end))
end));
)
end));
))));
))))
in (

let uu____3825 = (FStar_All.pipe_right ses (FStar_List.partition (fun uu___86_3835 -> (match (uu___86_3835) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____3836) -> begin
true
end
| uu____3848 -> begin
false
end))))
in (match (uu____3825) with
| (tys, datas) -> begin
((

let uu____3860 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun uu___87_3862 -> (match (uu___87_3862) with
| FStar_Syntax_Syntax.Sig_datacon (uu____3863) -> begin
false
end
| uu____3874 -> begin
true
end))))
in (match (uu____3860) with
| true -> begin
(

let uu____3875 = (

let uu____3876 = (

let uu____3879 = (FStar_TypeChecker_Env.get_range env)
in (("Mutually defined type contains a non-inductive element"), (uu____3879)))
in FStar_Errors.Error (uu____3876))
in (Prims.raise uu____3875))
end
| uu____3880 -> begin
()
end));
(

let env0 = env
in (

let uu____3882 = (FStar_List.fold_right (fun tc uu____3896 -> (match (uu____3896) with
| (env, all_tcs, g) -> begin
(

let uu____3918 = (tc_tycon env tc)
in (match (uu____3918) with
| (env, tc, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in ((

let uu____3935 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____3935) with
| true -> begin
(

let uu____3936 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" uu____3936))
end
| uu____3937 -> begin
()
end));
(

let uu____3938 = (

let uu____3939 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g uu____3939))
in ((env), ((((tc), (tc_u)))::all_tcs), (uu____3938)));
))
end))
end)) tys ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (uu____3882) with
| (env, tcs, g) -> begin
(

let uu____3963 = (FStar_List.fold_right (fun se uu____3971 -> (match (uu____3971) with
| (datas, g) -> begin
(

let uu____3982 = (tc_data env tcs se)
in (match (uu____3982) with
| (data, g') -> begin
(

let uu____3990 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((data)::datas), (uu____3990)))
end))
end)) datas (([]), (g)))
in (match (uu____3963) with
| (datas, g) -> begin
(

let uu____4001 = (generalize_and_inst_within env0 g tcs datas)
in (match (uu____4001) with
| (tcs, datas) -> begin
(

let sig_bndle = (

let uu____4017 = (

let uu____4025 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (uu____4025)))
in FStar_Syntax_Syntax.Sig_bundle (uu____4017))
in (

let datacon_typ = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (uu____4033, uu____4034, t, uu____4036, uu____4037, uu____4038, uu____4039, uu____4040) -> begin
t
end
| uu____4045 -> begin
(failwith "Impossible!")
end))
in (

let data_ops_ses = (

let uu____4048 = (FStar_List.map (FStar_TypeChecker_Util.mk_data_operations quals env tcs) datas)
in (FStar_All.pipe_right uu____4048 FStar_List.flatten))
in (

let check_positivity = (fun env ty -> (

let unfolded_inductives = (FStar_Util.mk_ref [])
in (

let already_unfolded = (fun env ilid args -> (

let uu____4092 = (FStar_ST.read unfolded_inductives)
in (FStar_List.existsML (fun uu____4112 -> (match (uu____4112) with
| (lid, l) -> begin
((FStar_Ident.lid_equals lid ilid) && (

let args = (

let uu____4132 = (FStar_List.splitAt (FStar_List.length l) args)
in (Prims.fst uu____4132))
in (FStar_List.fold_left2 (fun b a a' -> (b && (FStar_TypeChecker_Rel.teq_nosmt env (Prims.fst a) (Prims.fst a')))) true args l)))
end)) uu____4092)))
in (

let uu____4174 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, bs, uu____4184, uu____4185, uu____4186, uu____4187, uu____4188) -> begin
((lid), (us), (bs))
end
| uu____4195 -> begin
(failwith "Impossible!")
end)
in (match (uu____4174) with
| (ty_lid, ty_us, ty_bs) -> begin
(

let debug_log = (fun s -> (

let uu____4206 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Positivity")))
in (match (uu____4206) with
| true -> begin
(FStar_Util.print_string (Prims.strcat "Positivity::" (Prims.strcat s "\n")))
end
| uu____4207 -> begin
()
end)))
in ((debug_log (Prims.strcat "Checking positivity for " ty_lid.FStar_Ident.str));
(

let ty_occurs_in = (fun t -> (

let uu____4213 = (FStar_Syntax_Free.fvars t)
in (FStar_Util.set_mem ty_lid uu____4213)))
in (

let try_get_fv = (fun t -> (

let uu____4223 = (

let uu____4224 = (FStar_Syntax_Subst.compress t)
in uu____4224.FStar_Syntax_Syntax.n)
in (match (uu____4223) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((fv), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((fv), (us))
end
| uu____4240 -> begin
(failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
end)
end
| uu____4243 -> begin
(failwith "Node is not an fvar or a Tm_uinst")
end)))
in (

let uu____4246 = (FStar_Syntax_Subst.univ_var_opening ty_us)
in (match (uu____4246) with
| (ty_usubst, ty_us) -> begin
(

let env = (FStar_TypeChecker_Env.push_univ_vars env ty_us)
in (

let env = (FStar_TypeChecker_Env.push_binders env ty_bs)
in (

let ty_bs = (FStar_Syntax_Subst.subst_binders ty_usubst ty_bs)
in (

let ty_bs = (FStar_Syntax_Subst.open_binders ty_bs)
in (

let rec ty_positive_in_datacon = (fun env dt -> ((

let uu____4305 = (

let uu____4306 = (FStar_Syntax_Print.term_to_string dt)
in (Prims.strcat "Checking data constructor type: " uu____4306))
in (debug_log uu____4305));
(

let dt = (FStar_Syntax_Subst.subst ty_usubst dt)
in (

let uu____4308 = (

let uu____4309 = (FStar_Syntax_Subst.compress dt)
in uu____4309.FStar_Syntax_Syntax.n)
in (match (uu____4308) with
| FStar_Syntax_Syntax.Tm_fvar (uu____4312) -> begin
((debug_log "Data constructor type is simply an fvar, returning true");
true;
)
end
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____4315) -> begin
(

let dbs = (

let uu____4330 = (FStar_List.splitAt (FStar_List.length ty_bs) dbs)
in (Prims.snd uu____4330))
in (

let dbs = (

let uu____4352 = (FStar_Syntax_Subst.opening_of_binders ty_bs)
in (FStar_Syntax_Subst.subst_binders uu____4352 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in ((

let uu____4356 = (

let uu____4357 = (

let uu____4358 = (FStar_Util.string_of_int (FStar_List.length dbs))
in (Prims.strcat uu____4358 " binders"))
in (Prims.strcat "Data constructor type is an arrow type, so checking strict positivity in " uu____4357))
in (debug_log uu____4356));
(

let uu____4364 = (FStar_List.fold_left (fun uu____4371 b -> (match (uu____4371) with
| (r, env) -> begin
(match ((not (r))) with
| true -> begin
((r), (env))
end
| uu____4383 -> begin
(

let uu____4384 = (ty_strictly_positive_in_type (Prims.fst b).FStar_Syntax_Syntax.sort env)
in (

let uu____4385 = (FStar_TypeChecker_Env.push_binders env ((b)::[]))
in ((uu____4384), (uu____4385))))
end)
end)) ((true), (env)) dbs)
in (match (uu____4364) with
| (b, uu____4391) -> begin
b
end));
))))
end
| FStar_Syntax_Syntax.Tm_app (uu____4392, uu____4393) -> begin
((debug_log "Data constructor type is a Tm_app, so returning true");
true;
)
end
| uu____4409 -> begin
(failwith "Unexpected data constructor type when checking positivity")
end)));
))
and ty_strictly_positive_in_type = (fun btype env -> ((

let uu____4413 = (

let uu____4414 = (FStar_Syntax_Print.term_to_string btype)
in (Prims.strcat "Checking strict positivity in type: " uu____4414))
in (debug_log uu____4413));
(

let btype = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env btype)
in ((

let uu____4417 = (

let uu____4418 = (FStar_Syntax_Print.term_to_string btype)
in (Prims.strcat "Checking strict positivity in type, after normalization: " uu____4418))
in (debug_log uu____4417));
((

let uu____4419 = (ty_occurs_in btype)
in (not (uu____4419))) || ((debug_log "ty does occur in this type, pressing ahead");
(

let uu____4421 = (

let uu____4422 = (FStar_Syntax_Subst.compress btype)
in uu____4422.FStar_Syntax_Syntax.n)
in (match (uu____4421) with
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____4441 = (try_get_fv t)
in (match (uu____4441) with
| (fv, us) -> begin
(match ((FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v ty_lid)) with
| true -> begin
((debug_log "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments");
(FStar_List.for_all (fun uu____4453 -> (match (uu____4453) with
| (t, uu____4457) -> begin
(

let uu____4458 = (ty_occurs_in t)
in (not (uu____4458)))
end)) args);
)
end
| uu____4459 -> begin
((debug_log "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity");
(ty_nested_positive_in_inductive fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v us args env);
)
end)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (sbs, c) -> begin
((debug_log "Checking strict positivity in Tm_arrow");
(

let uu____4478 = (

let uu____4479 = (FStar_Syntax_Util.is_pure_or_ghost_comp c)
in (not (uu____4479)))
in (match (uu____4478) with
| true -> begin
((debug_log "Checking strict positivity , the arrow is impure, so return true");
true;
)
end
| uu____4481 -> begin
((debug_log "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type");
((FStar_List.for_all (fun uu____4485 -> (match (uu____4485) with
| (b, uu____4489) -> begin
(

let uu____4490 = (ty_occurs_in b.FStar_Syntax_Syntax.sort)
in (not (uu____4490)))
end)) sbs) && (

let uu____4491 = (FStar_Syntax_Subst.open_term sbs (FStar_Syntax_Util.comp_result c))
in (match (uu____4491) with
| (uu____4494, return_type) -> begin
(

let uu____4496 = (FStar_TypeChecker_Env.push_binders env sbs)
in (ty_strictly_positive_in_type return_type uu____4496))
end)));
)
end));
)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____4497) -> begin
((debug_log "Checking strict positivity in an fvar, return true");
true;
)
end
| FStar_Syntax_Syntax.Tm_type (uu____4499) -> begin
((debug_log "Checking strict positivity in an Tm_type, return true");
true;
)
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____4502) -> begin
((debug_log "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)");
(ty_strictly_positive_in_type t env);
)
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____4509) -> begin
((debug_log "Checking strict positivity in an Tm_refine, recur in the bv sort)");
(ty_strictly_positive_in_type bv.FStar_Syntax_Syntax.sort env);
)
end
| uu____4515 -> begin
((

let uu____4517 = (

let uu____4518 = (FStar_Syntax_Print.term_to_string btype)
in (Prims.strcat "Checking strict positivity, unexpected term: " uu____4518))
in (debug_log uu____4517));
false;
)
end));
));
));
))
and ty_nested_positive_in_inductive = (fun ilid us args env -> ((

let uu____4524 = (

let uu____4525 = (

let uu____4526 = (

let uu____4527 = (FStar_Syntax_Print.args_to_string args)
in (Prims.strcat " applied to arguments: " uu____4527))
in (Prims.strcat ilid.FStar_Ident.str uu____4526))
in (Prims.strcat "Checking nested positivity in the inductive " uu____4525))
in (debug_log uu____4524));
(

let uu____4528 = (FStar_TypeChecker_Env.datacons_of_typ env ilid)
in (match (uu____4528) with
| (b, idatas) -> begin
(match ((not (b))) with
| true -> begin
((debug_log "Checking nested positivity, not an inductive, return false");
false;
)
end
| uu____4537 -> begin
(

let uu____4538 = (already_unfolded env ilid args)
in (match (uu____4538) with
| true -> begin
((debug_log "Checking nested positivity, we have already unfolded this inductive with these args");
true;
)
end
| uu____4540 -> begin
(

let num_ibs = (FStar_TypeChecker_Env.num_inductive_ty_params env ilid)
in ((

let uu____4543 = (

let uu____4544 = (

let uu____4545 = (FStar_Util.string_of_int num_ibs)
in (Prims.strcat uu____4545 ", also adding to the memo table"))
in (Prims.strcat "Checking nested positivity, number of type parameters is " uu____4544))
in (debug_log uu____4543));
(

let uu____4547 = (

let uu____4554 = (FStar_ST.read unfolded_inductives)
in (

let uu____4569 = (

let uu____4576 = (

let uu____4584 = (

let uu____4590 = (FStar_List.splitAt num_ibs args)
in (Prims.fst uu____4590))
in ((ilid), (uu____4584)))
in (uu____4576)::[])
in (FStar_List.append uu____4554 uu____4569)))
in (FStar_ST.write unfolded_inductives uu____4547));
(FStar_List.for_all (fun d -> (ty_nested_positive_in_dlid d ilid us args num_ibs env)) idatas);
))
end))
end)
end));
))
and ty_nested_positive_in_dlid = (fun dlid ilid us args num_ibs env -> ((debug_log (Prims.strcat "Checking nested positivity in data constructor " (Prims.strcat dlid.FStar_Ident.str (Prims.strcat " of the inductive " ilid.FStar_Ident.str))));
(

let uu____4657 = (FStar_TypeChecker_Env.lookup_datacon env dlid)
in (match (uu____4657) with
| (univ_unif_vars, dt) -> begin
((FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| uu____4669 -> begin
(failwith "Impossible")
end)) univ_unif_vars us);
(

let dt = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env dt)
in ((

let uu____4672 = (

let uu____4673 = (FStar_Syntax_Print.term_to_string dt)
in (Prims.strcat "Checking nested positivity in the data constructor type: " uu____4673))
in (debug_log uu____4672));
(

let uu____4674 = (

let uu____4675 = (FStar_Syntax_Subst.compress dt)
in uu____4675.FStar_Syntax_Syntax.n)
in (match (uu____4674) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, c) -> begin
((debug_log "Checked nested positivity in Tm_arrow data constructor type");
(

let uu____4691 = (FStar_List.splitAt num_ibs dbs)
in (match (uu____4691) with
| (ibs, dbs) -> begin
(

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let dbs = (

let uu____4718 = (FStar_Syntax_Subst.opening_of_binders ibs)
in (FStar_Syntax_Subst.subst_binders uu____4718 dbs))
in (

let c = (

let uu____4721 = (FStar_Syntax_Subst.opening_of_binders ibs)
in (FStar_Syntax_Subst.subst_comp uu____4721 c))
in (

let uu____4723 = (FStar_List.splitAt num_ibs args)
in (match (uu____4723) with
| (args, uu____4741) -> begin
(

let subst = (FStar_List.fold_left2 (fun subst ib arg -> (FStar_List.append subst ((FStar_Syntax_Syntax.NT ((((Prims.fst ib)), ((Prims.fst arg)))))::[]))) [] ibs args)
in (

let dbs = (FStar_Syntax_Subst.subst_binders subst dbs)
in (

let c = (

let uu____4787 = (FStar_Syntax_Subst.shift_subst (FStar_List.length dbs) subst)
in (FStar_Syntax_Subst.subst_comp uu____4787 c))
in ((

let uu____4795 = (

let uu____4796 = (

let uu____4797 = (FStar_Syntax_Print.binders_to_string "; " dbs)
in (

let uu____4798 = (

let uu____4799 = (FStar_Syntax_Print.comp_to_string c)
in (Prims.strcat ", and c: " uu____4799))
in (Prims.strcat uu____4797 uu____4798)))
in (Prims.strcat "Checking nested positivity in the unfolded data constructor binders as: " uu____4796))
in (debug_log uu____4795));
(ty_nested_positive_in (FStar_Syntax_Syntax.Tm_arrow (((dbs), (c)))) ilid num_ibs env);
))))
end)))))
end));
)
end
| uu____4800 -> begin
((debug_log "Checking nested positivity in the data constructor type that is not an arrow");
(

let uu____4802 = (

let uu____4803 = (FStar_Syntax_Subst.compress dt)
in uu____4803.FStar_Syntax_Syntax.n)
in (ty_nested_positive_in uu____4802 ilid num_ibs env));
)
end));
));
)
end));
))
and ty_nested_positive_in = (fun t ilid num_ibs env -> (match (t) with
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
((debug_log "Checking nested positivity in an Tm_app node, which is expected to be the ilid itself");
(

let uu____4827 = (try_get_fv t)
in (match (uu____4827) with
| (fv, uu____4831) -> begin
(match ((FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v ilid)) with
| true -> begin
true
end
| uu____4836 -> begin
(failwith "Impossible, expected the type to be ilid")
end)
end));
)
end
| FStar_Syntax_Syntax.Tm_arrow (sbs, c) -> begin
((

let uu____4850 = (

let uu____4851 = (FStar_Syntax_Print.binders_to_string "; " sbs)
in (Prims.strcat "Checking nested positivity in an Tm_arrow node, with binders as: " uu____4851))
in (debug_log uu____4850));
(

let uu____4852 = (FStar_List.fold_left (fun uu____4859 b -> (match (uu____4859) with
| (r, env) -> begin
(match ((not (r))) with
| true -> begin
((r), (env))
end
| uu____4871 -> begin
(

let uu____4872 = (ty_strictly_positive_in_type (Prims.fst b).FStar_Syntax_Syntax.sort env)
in (

let uu____4873 = (FStar_TypeChecker_Env.push_binders env ((b)::[]))
in ((uu____4872), (uu____4873))))
end)
end)) ((true), (env)) sbs)
in (match (uu____4852) with
| (b, uu____4879) -> begin
b
end));
)
end
| uu____4880 -> begin
(failwith "Nested positive check, unhandled case")
end))
in (FStar_List.for_all (fun d -> (

let uu____4882 = (datacon_typ d)
in (ty_positive_in_datacon env uu____4882))) datas))))))
end))));
))
end)))))
in ((

let uu____4884 = ((FStar_Options.no_positivity ()) || (FStar_Options.lax ()))
in (match (uu____4884) with
| true -> begin
()
end
| uu____4885 -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (FStar_List.iter (fun ty -> (

let b = (check_positivity env ty)
in (match ((not (b))) with
| true -> begin
(

let uu____4890 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____4896, uu____4897, uu____4898, uu____4899, uu____4900, uu____4901, r) -> begin
((lid), (r))
end
| uu____4909 -> begin
(failwith "Impossible!")
end)
in (match (uu____4890) with
| (lid, r) -> begin
(FStar_Errors.report r (Prims.strcat "Inductive type " (Prims.strcat lid.FStar_Ident.str " does not satisfy the positivity condition")))
end))
end
| uu____4914 -> begin
()
end))) tcs))
end));
(

let datacon_typ = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (uu____4919, uu____4920, t, uu____4922, uu____4923, uu____4924, uu____4925, uu____4926) -> begin
t
end
| uu____4931 -> begin
(failwith "Impossible!")
end))
in (

let dr = FStar_Range.dummyRange
in (

let optimized_haseq_scheme = (fun uu____4937 -> (

let haseq_ty = (fun usubst us acc ty -> (

let uu____4981 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____4993, bs, t, uu____4996, d_lids, uu____4998, uu____4999) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____5007 -> begin
(failwith "Impossible!")
end)
in (match (uu____4981) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (

let uu____5032 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst uu____5032 t))
in (

let uu____5039 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____5039) with
| (bs, t) -> begin
(

let ibs = (

let uu____5059 = (

let uu____5060 = (FStar_Syntax_Subst.compress t)
in uu____5060.FStar_Syntax_Syntax.n)
in (match (uu____5059) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____5067) -> begin
ibs
end
| uu____5078 -> begin
[]
end))
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (

let uu____5083 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____5084 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____5083 uu____5084)))
in (

let ind = (

let uu____5089 = (

let uu____5090 = (FStar_List.map (fun uu____5095 -> (match (uu____5095) with
| (bv, aq) -> begin
(

let uu____5102 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____5102), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____5090))
in (uu____5089 None dr))
in (

let ind = (

let uu____5110 = (

let uu____5111 = (FStar_List.map (fun uu____5116 -> (match (uu____5116) with
| (bv, aq) -> begin
(

let uu____5123 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____5123), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____5111))
in (uu____5110 None dr))
in (

let haseq_ind = (

let uu____5131 = (

let uu____5132 = (

let uu____5133 = (FStar_Syntax_Syntax.as_arg ind)
in (uu____5133)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____5132))
in (uu____5131 None dr))
in (

let bs' = (FStar_List.filter (fun b -> (

let uu____5147 = acc
in (match (uu____5147) with
| (uu____5155, en, uu____5157, uu____5158) -> begin
(

let opt = (

let uu____5167 = (

let uu____5168 = (FStar_Syntax_Util.type_u ())
in (Prims.fst uu____5168))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort uu____5167 false))
in (match (opt) with
| None -> begin
false
end
| Some (uu____5171) -> begin
true
end))
end))) bs)
in (

let haseq_bs = (FStar_List.fold_left (fun t b -> (

let uu____5175 = (

let uu____5176 = (

let uu____5177 = (

let uu____5178 = (

let uu____5179 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b))
in (FStar_Syntax_Syntax.as_arg uu____5179))
in (uu____5178)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____5177))
in (uu____5176 None dr))
in (FStar_Syntax_Util.mk_conj t uu____5175))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml = (

let uu___108_5188 = fml
in (

let uu____5189 = (

let uu____5190 = (

let uu____5195 = (

let uu____5196 = (

let uu____5203 = (

let uu____5205 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (uu____5205)::[])
in (uu____5203)::[])
in FStar_Syntax_Syntax.Meta_pattern (uu____5196))
in ((fml), (uu____5195)))
in FStar_Syntax_Syntax.Tm_meta (uu____5190))
in {FStar_Syntax_Syntax.n = uu____5189; FStar_Syntax_Syntax.tk = uu___108_5188.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___108_5188.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___108_5188.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (

let uu____5217 = (

let uu____5218 = (

let uu____5219 = (

let uu____5220 = (

let uu____5221 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____5221 None))
in (FStar_Syntax_Syntax.as_arg uu____5220))
in (uu____5219)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____5218))
in (uu____5217 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (

let uu____5243 = (

let uu____5244 = (

let uu____5245 = (

let uu____5246 = (

let uu____5247 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____5247 None))
in (FStar_Syntax_Syntax.as_arg uu____5246))
in (uu____5245)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____5244))
in (uu____5243 None dr))) bs fml)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let uu____5267 = acc
in (match (uu____5267) with
| (l_axioms, env, guard', cond') -> begin
(

let env = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env = (FStar_TypeChecker_Env.push_binders env ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (uu____5301, uu____5302, uu____5303, t_lid, uu____5305, uu____5306, uu____5307, uu____5308) -> begin
(t_lid = lid)
end
| uu____5313 -> begin
(failwith "Impossible")
end)) datas)
in (

let haseq_data = (fun data -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (

let uu____5320 = (

let uu____5321 = (FStar_Syntax_Subst.compress dt)
in uu____5321.FStar_Syntax_Syntax.n)
in (match (uu____5320) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____5325) -> begin
(

let dbs = (

let uu____5340 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd uu____5340))
in (

let dbs = (

let uu____5362 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders uu____5362 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let haseq_b = (

let uu____5371 = (

let uu____5372 = (

let uu____5373 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (uu____5373)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____5372))
in (uu____5371 None dr))
in (

let sort_range = (Prims.fst b).FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos
in (

let haseq_b = (

let uu____5380 = (

let uu____5381 = (FStar_Syntax_Print.term_to_string ind)
in (FStar_Util.format1 "Failed to prove that the type \'%s\' supports decidable equality because of this argument; add the \'noeq\' qualifier" uu____5381))
in (FStar_TypeChecker_Util.label uu____5380 sort_range haseq_b))
in (FStar_Syntax_Util.mk_conj t haseq_b))))) FStar_Syntax_Util.t_true dbs)
in (FStar_List.fold_right (fun b t -> (

let uu____5386 = (

let uu____5387 = (

let uu____5388 = (

let uu____5389 = (

let uu____5390 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____5390 None))
in (FStar_Syntax_Syntax.as_arg uu____5389))
in (uu____5388)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____5387))
in (uu____5386 None dr))) dbs cond)))))
end
| uu____5407 -> begin
FStar_Syntax_Util.t_true
end)))))
in (

let cond = (FStar_List.fold_left (fun acc d -> (

let uu____5411 = (haseq_data d)
in (FStar_Syntax_Util.mk_conj acc uu____5411))) FStar_Syntax_Util.t_true t_datas)
in (

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (

let uu____5413 = (FStar_Syntax_Util.mk_conj guard' guard)
in (

let uu____5416 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml)))::[]))), (env), (uu____5413), (uu____5416))))))))))
end)))))))))))))))
end))))
end)))
in (

let us = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____5434, us, uu____5436, uu____5437, uu____5438, uu____5439, uu____5440, uu____5441) -> begin
us
end
| uu____5448 -> begin
(failwith "Impossible!")
end))
in (

let uu____5449 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____5449) with
| (usubst, us) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq");
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle);
(

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let uu____5465 = (FStar_List.fold_left (haseq_ty usubst us) (([]), (env), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (uu____5465) with
| (axioms, env, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let uu____5497 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env phi)
in (match (uu____5497) with
| (phi, uu____5502) -> begin
((

let uu____5504 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____5504) with
| true -> begin
(

let uu____5505 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi)))
in (FStar_TypeChecker_Rel.force_trivial_guard env uu____5505))
end
| uu____5506 -> begin
()
end));
(

let ses = (FStar_List.fold_left (fun l uu____5513 -> (match (uu____5513) with
| (lid, fml) -> begin
(

let se = (tc_assume env lid fml [] dr)
in (FStar_List.append l ((se)::[])))
end)) [] axioms)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq");
ses;
));
)
end)))
end)));
))
end)))))
in (

let unoptimized_haseq_scheme = (fun uu____5526 -> (

let mutuals = (FStar_List.map (fun ty -> (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____5532, uu____5533, uu____5534, uu____5535, uu____5536, uu____5537, uu____5538) -> begin
lid
end
| uu____5545 -> begin
(failwith "Impossible!")
end)) tcs)
in (

let haseq_ty = (fun usubst us acc ty -> (

let uu____5565 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____5577, bs, t, uu____5580, d_lids, uu____5582, uu____5583) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____5591 -> begin
(failwith "Impossible!")
end)
in (match (uu____5565) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (

let uu____5607 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst uu____5607 t))
in (

let uu____5614 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____5614) with
| (bs, t) -> begin
(

let ibs = (

let uu____5625 = (

let uu____5626 = (FStar_Syntax_Subst.compress t)
in uu____5626.FStar_Syntax_Syntax.n)
in (match (uu____5625) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____5633) -> begin
ibs
end
| uu____5644 -> begin
[]
end))
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (

let uu____5649 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____5650 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____5649 uu____5650)))
in (

let ind = (

let uu____5655 = (

let uu____5656 = (FStar_List.map (fun uu____5661 -> (match (uu____5661) with
| (bv, aq) -> begin
(

let uu____5668 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____5668), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____5656))
in (uu____5655 None dr))
in (

let ind = (

let uu____5676 = (

let uu____5677 = (FStar_List.map (fun uu____5682 -> (match (uu____5682) with
| (bv, aq) -> begin
(

let uu____5689 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____5689), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____5677))
in (uu____5676 None dr))
in (

let haseq_ind = (

let uu____5697 = (

let uu____5698 = (

let uu____5699 = (FStar_Syntax_Syntax.as_arg ind)
in (uu____5699)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____5698))
in (uu____5697 None dr))
in (

let rec is_mutual = (fun t -> (

let uu____5714 = (

let uu____5715 = (FStar_Syntax_Subst.compress t)
in uu____5715.FStar_Syntax_Syntax.n)
in (match (uu____5714) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.existsb (fun lid -> (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) mutuals)
end
| FStar_Syntax_Syntax.Tm_uinst (t', uu____5725) -> begin
(is_mutual t')
end
| FStar_Syntax_Syntax.Tm_refine (bv, t') -> begin
(is_mutual bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_app (t', args) -> begin
(

let uu____5752 = (is_mutual t')
in (match (uu____5752) with
| true -> begin
true
end
| uu____5753 -> begin
(

let uu____5754 = (FStar_List.map Prims.fst args)
in (exists_mutual uu____5754))
end))
end
| FStar_Syntax_Syntax.Tm_meta (t', uu____5767) -> begin
(is_mutual t')
end
| uu____5772 -> begin
false
end)))
and exists_mutual = (fun uu___88_5773 -> (match (uu___88_5773) with
| [] -> begin
false
end
| (hd)::tl -> begin
((is_mutual hd) || (exists_mutual tl))
end))
in (

let haseq_data = (fun acc data -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (

let uu____5799 = (

let uu____5800 = (FStar_Syntax_Subst.compress dt)
in uu____5800.FStar_Syntax_Syntax.n)
in (match (uu____5799) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____5806) -> begin
(

let dbs = (

let uu____5821 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd uu____5821))
in (

let dbs = (

let uu____5843 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders uu____5843 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let sort = (Prims.fst b).FStar_Syntax_Syntax.sort
in (

let haseq_sort = (

let uu____5855 = (

let uu____5856 = (

let uu____5857 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (uu____5857)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____5856))
in (uu____5855 None dr))
in (

let haseq_sort = (

let uu____5863 = (is_mutual sort)
in (match (uu____5863) with
| true -> begin
(FStar_Syntax_Util.mk_imp haseq_ind haseq_sort)
end
| uu____5864 -> begin
haseq_sort
end))
in (FStar_Syntax_Util.mk_conj t haseq_sort))))) FStar_Syntax_Util.t_true dbs)
in (

let cond = (FStar_List.fold_right (fun b t -> (

let uu____5870 = (

let uu____5871 = (

let uu____5872 = (

let uu____5873 = (

let uu____5874 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____5874 None))
in (FStar_Syntax_Syntax.as_arg uu____5873))
in (uu____5872)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____5871))
in (uu____5870 None dr))) dbs cond)
in (FStar_Syntax_Util.mk_conj acc cond))))))
end
| uu____5891 -> begin
acc
end)))))
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (uu____5895, uu____5896, uu____5897, t_lid, uu____5899, uu____5900, uu____5901, uu____5902) -> begin
(t_lid = lid)
end
| uu____5907 -> begin
(failwith "Impossible")
end)) datas)
in (

let data_cond = (FStar_List.fold_left haseq_data FStar_Syntax_Util.t_true t_datas)
in (

let fml = (FStar_Syntax_Util.mk_imp data_cond haseq_ind)
in (

let fml = (

let uu___109_5913 = fml
in (

let uu____5914 = (

let uu____5915 = (

let uu____5920 = (

let uu____5921 = (

let uu____5928 = (

let uu____5930 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (uu____5930)::[])
in (uu____5928)::[])
in FStar_Syntax_Syntax.Meta_pattern (uu____5921))
in ((fml), (uu____5920)))
in FStar_Syntax_Syntax.Tm_meta (uu____5915))
in {FStar_Syntax_Syntax.n = uu____5914; FStar_Syntax_Syntax.tk = uu___109_5913.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___109_5913.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___109_5913.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (

let uu____5942 = (

let uu____5943 = (

let uu____5944 = (

let uu____5945 = (

let uu____5946 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____5946 None))
in (FStar_Syntax_Syntax.as_arg uu____5945))
in (uu____5944)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____5943))
in (uu____5942 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (

let uu____5968 = (

let uu____5969 = (

let uu____5970 = (

let uu____5971 = (

let uu____5972 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____5972 None))
in (FStar_Syntax_Syntax.as_arg uu____5971))
in (uu____5970)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____5969))
in (uu____5968 None dr))) bs fml)
in (FStar_Syntax_Util.mk_conj acc fml)))))))))))))))
end))))
end)))
in (

let uu____5989 = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, uu____5997, uu____5998, uu____5999, uu____6000, uu____6001, uu____6002) -> begin
((lid), (us))
end
| uu____6009 -> begin
(failwith "Impossible!")
end))
in (match (uu____5989) with
| (lid, us) -> begin
(

let uu____6015 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____6015) with
| (usubst, us) -> begin
(

let fml = (FStar_List.fold_left (haseq_ty usubst us) FStar_Syntax_Util.t_true tcs)
in (

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq");
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle);
(

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let se = (

let uu____6033 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (tc_assume env uu____6033 fml [] dr))
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq");
(se)::[];
)));
)))
end))
end)))))
in (

let skip_prims_type = (fun uu____6038 -> (

let lid = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____6042, uu____6043, uu____6044, uu____6045, uu____6046, uu____6047, uu____6048) -> begin
lid
end
| uu____6055 -> begin
(failwith "Impossible")
end))
in (

let types_to_skip = ("c_False")::("c_True")::("equals")::("h_equals")::("c_and")::("c_or")::[]
in (FStar_List.existsb (fun s -> (s = lid.FStar_Ident.ident.FStar_Ident.idText)) types_to_skip))))
in (

let is_noeq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Noeq)) quals)
in (

let uu____6061 = ((((FStar_List.length tcs) = (Prims.parse_int "0")) || ((FStar_Ident.lid_equals env.FStar_TypeChecker_Env.curmodule FStar_Syntax_Const.prims_lid) && (skip_prims_type ()))) || is_noeq)
in (match (uu____6061) with
| true -> begin
(((sig_bndle)::[]), (data_ops_ses))
end
| uu____6070 -> begin
(

let is_unopteq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Unopteq)) quals)
in (

let ses = (match (is_unopteq) with
| true -> begin
(unoptimized_haseq_scheme ())
end
| uu____6076 -> begin
(optimized_haseq_scheme ())
end)
in (

let uu____6077 = (

let uu____6079 = (

let uu____6080 = (

let uu____6088 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (uu____6088)))
in FStar_Syntax_Syntax.Sig_bundle (uu____6080))
in (uu____6079)::ses)
in ((uu____6077), (data_ops_ses)))))
end))))))));
)))))
end))
end))
end)));
)
end)))))))))
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

let uu____6128 = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (uu____6128), ([])))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let uu____6142 = (tc_inductive env ses quals lids)
in (match (uu____6142) with
| (ses, projectors_ses) -> begin
(

let env = (FStar_List.fold_left (fun env' se -> (FStar_TypeChecker_Env.push_sigelt env' se)) env ses)
in ((ses), (env), (projectors_ses)))
end)))
end
| FStar_Syntax_Syntax.Sig_pragma (p, r) -> begin
(

let set_options = (fun t s -> (

let uu____6172 = (FStar_Options.set_options t s)
in (match (uu____6172) with
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
| uu____6180 -> begin
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

let uu____6190 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____6190 Prims.ignore));
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
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____6196) -> begin
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

let uu____6209 = (FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun uu____6220 a -> (match (uu____6220) with
| (env, ses) -> begin
(

let se_let = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a)
in (

let uu____6233 = (FStar_TypeChecker_Env.push_sigelt env se_let)
in ((uu____6233), ((se_let)::ses))))
end)) ((env), ((se)::[]))))
in (match (uu____6209) with
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

let uu____6251 = (

let uu____6256 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source uu____6256))
in (match (uu____6251) with
| (a, wp_a_src) -> begin
(

let uu____6268 = (

let uu____6273 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target uu____6273))
in (match (uu____6268) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (

let uu____6286 = (

let uu____6288 = (

let uu____6289 = (

let uu____6294 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (uu____6294)))
in FStar_Syntax_Syntax.NT (uu____6289))
in (uu____6288)::[])
in (FStar_Syntax_Subst.subst uu____6286 wp_b_tgt))
in (

let expected_k = (

let uu____6298 = (

let uu____6302 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____6303 = (

let uu____6305 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (uu____6305)::[])
in (uu____6302)::uu____6303))
in (

let uu____6306 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow uu____6298 uu____6306)))
in (

let repr_type = (fun eff_name a wp -> (

let no_reify = (fun l -> (

let uu____6327 = (

let uu____6328 = (

let uu____6331 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (

let uu____6332 = (FStar_TypeChecker_Env.get_range env)
in ((uu____6331), (uu____6332))))
in FStar_Errors.Error (uu____6328))
in (Prims.raise uu____6327)))
in (

let uu____6335 = (FStar_TypeChecker_Env.effect_decl_opt env eff_name)
in (match (uu____6335) with
| None -> begin
(no_reify eff_name)
end
| Some (ed) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((FStar_Syntax_Syntax.U_unknown)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let uu____6342 = (

let uu____6343 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (not (uu____6343)))
in (match (uu____6342) with
| true -> begin
(no_reify eff_name)
end
| uu____6347 -> begin
(

let uu____6348 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____6349 = (

let uu____6352 = (

let uu____6353 = (

let uu____6363 = (

let uu____6365 = (FStar_Syntax_Syntax.as_arg a)
in (

let uu____6366 = (

let uu____6368 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____6368)::[])
in (uu____6365)::uu____6366))
in ((repr), (uu____6363)))
in FStar_Syntax_Syntax.Tm_app (uu____6353))
in (FStar_Syntax_Syntax.mk uu____6352))
in (uu____6349 None uu____6348)))
end)))
end))))
in (

let uu____6378 = (match (((sub.FStar_Syntax_Syntax.lift), (sub.FStar_Syntax_Syntax.lift_wp))) with
| (None, None) -> begin
(failwith "Impossible")
end
| (lift, Some (uu____6393, lift_wp)) -> begin
(

let uu____6406 = (check_and_gen env lift_wp expected_k)
in ((lift), (uu____6406)))
end
| (Some (what, lift), None) -> begin
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange))
in (

let uu____6421 = (FStar_TypeChecker_DMFF.star_expr dmff_env lift)
in (match (uu____6421) with
| (uu____6428, lift_wp, lift_elab) -> begin
(

let uu____6431 = (recheck_debug "lift-wp" env lift_wp)
in (

let uu____6432 = (recheck_debug "lift-elab" env lift_elab)
in ((Some ((([]), (lift_elab)))), ((([]), (lift_wp))))))
end)))
end)
in (match (uu____6378) with
| (lift, lift_wp) -> begin
(

let lax = env.FStar_TypeChecker_Env.lax
in (

let env = (

let uu___110_6456 = env
in {FStar_TypeChecker_Env.solver = uu___110_6456.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___110_6456.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___110_6456.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___110_6456.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___110_6456.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___110_6456.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___110_6456.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___110_6456.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___110_6456.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___110_6456.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___110_6456.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___110_6456.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___110_6456.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___110_6456.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___110_6456.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___110_6456.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___110_6456.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___110_6456.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___110_6456.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___110_6456.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___110_6456.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___110_6456.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___110_6456.FStar_TypeChecker_Env.qname_and_index})
in (

let lift = (match (lift) with
| None -> begin
None
end
| Some (uu____6460, lift) -> begin
(

let uu____6467 = (

let uu____6472 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source uu____6472))
in (match (uu____6467) with
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

let uu____6494 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____6495 = (

let uu____6498 = (

let uu____6499 = (

let uu____6509 = (

let uu____6511 = (FStar_Syntax_Syntax.as_arg a_typ)
in (

let uu____6512 = (

let uu____6514 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (uu____6514)::[])
in (uu____6511)::uu____6512))
in ((lift_wp), (uu____6509)))
in FStar_Syntax_Syntax.Tm_app (uu____6499))
in (FStar_Syntax_Syntax.mk uu____6498))
in (uu____6495 None uu____6494)))
in (repr_type sub.FStar_Syntax_Syntax.target a_typ lift_wp_a)))
in (

let expected_k = (

let uu____6527 = (

let uu____6531 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____6532 = (

let uu____6534 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (

let uu____6535 = (

let uu____6537 = (FStar_Syntax_Syntax.null_binder repr_f)
in (uu____6537)::[])
in (uu____6534)::uu____6535))
in (uu____6531)::uu____6532))
in (

let uu____6538 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow uu____6527 uu____6538)))
in (

let uu____6541 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (uu____6541) with
| (expected_k, uu____6547, uu____6548) -> begin
(

let lift = (check_and_gen env lift expected_k)
in Some (lift))
end))))))))
end))
end)
in (

let env = (

let uu___111_6551 = env
in {FStar_TypeChecker_Env.solver = uu___111_6551.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___111_6551.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___111_6551.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___111_6551.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___111_6551.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___111_6551.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___111_6551.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___111_6551.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___111_6551.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___111_6551.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___111_6551.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___111_6551.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___111_6551.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___111_6551.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___111_6551.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___111_6551.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___111_6551.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___111_6551.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = lax; FStar_TypeChecker_Env.lax_universes = uu___111_6551.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___111_6551.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___111_6551.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___111_6551.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___111_6551.FStar_TypeChecker_Env.qname_and_index})
in (

let sub = (

let uu___112_6553 = sub
in {FStar_Syntax_Syntax.source = uu___112_6553.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = uu___112_6553.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = Some (lift_wp); FStar_Syntax_Syntax.lift = lift})
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

let uu____6572 = (FStar_Syntax_Subst.open_comp tps c)
in (match (uu____6572) with
| (tps, c) -> begin
(

let uu____6582 = (tc_tparams env tps)
in (match (uu____6582) with
| (tps, env, us) -> begin
(

let uu____6594 = (FStar_TypeChecker_TcTerm.tc_comp env c)
in (match (uu____6594) with
| (c, u, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
(

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

let uu____6609 = (

let uu____6610 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 uu____6610))
in (match (uu____6609) with
| (uvs, t) -> begin
(

let uu____6624 = (

let uu____6632 = (

let uu____6635 = (

let uu____6636 = (FStar_Syntax_Subst.compress t)
in uu____6636.FStar_Syntax_Syntax.n)
in ((tps), (uu____6635)))
in (match (uu____6632) with
| ([], FStar_Syntax_Syntax.Tm_arrow (uu____6646, c)) -> begin
(([]), (c))
end
| (uu____6670, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
((tps), (c))
end
| uu____6688 -> begin
(failwith "Impossible")
end))
in (match (uu____6624) with
| (tps, c) -> begin
((match ((((FStar_List.length uvs) <> (Prims.parse_int "1")) && (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))))) with
| true -> begin
(

let uu____6718 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____6718) with
| (uu____6721, t) -> begin
(

let uu____6723 = (

let uu____6724 = (

let uu____6727 = (

let uu____6728 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____6729 = (FStar_All.pipe_right (FStar_List.length uvs) FStar_Util.string_of_int)
in (

let uu____6732 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)" uu____6728 uu____6729 uu____6732))))
in ((uu____6727), (r)))
in FStar_Errors.Error (uu____6724))
in (Prims.raise uu____6723))
end))
end
| uu____6733 -> begin
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
| (FStar_Syntax_Syntax.Sig_declare_typ (_, _, _, quals, _)) | (FStar_Syntax_Syntax.Sig_let (_, _, _, quals, _)) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___89_6762 -> (match (uu___89_6762) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____6763 -> begin
false
end)))) -> begin
(([]), (env), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t, quals, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let uu____6774 = (match ((uvs = [])) with
| true -> begin
(

let uu____6775 = (

let uu____6776 = (FStar_Syntax_Util.type_u ())
in (Prims.fst uu____6776))
in (check_and_gen env t uu____6775))
end
| uu____6779 -> begin
(

let uu____6780 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____6780) with
| (uvs, t) -> begin
(

let uu____6785 = (

let uu____6786 = (

let uu____6787 = (

let uu____6788 = (FStar_Syntax_Util.type_u ())
in (Prims.fst uu____6788))
in (tc_check_trivial_guard env t uu____6787))
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) uu____6786))
in ((uvs), (uu____6785)))
end))
end)
in (match (uu____6774) with
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

let uu____6820 = (FStar_TypeChecker_TcTerm.tc_term env e)
in (match (uu____6820) with
| (e, c, g1) -> begin
(

let uu____6832 = (

let uu____6836 = (

let uu____6838 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (uu____6838))
in (

let uu____6839 = (

let uu____6842 = (c.FStar_Syntax_Syntax.comp ())
in ((e), (uu____6842)))
in (FStar_TypeChecker_TcTerm.check_expected_effect env uu____6836 uu____6839)))
in (match (uu____6832) with
| (e, uu____6853, g) -> begin
((

let uu____6856 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env uu____6856));
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

let uu____6898 = (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q'))
in (match (uu____6898) with
| true -> begin
Some (q)
end
| uu____6906 -> begin
(

let uu____6907 = (

let uu____6908 = (

let uu____6911 = (

let uu____6912 = (FStar_Syntax_Print.lid_to_string l)
in (

let uu____6913 = (FStar_Syntax_Print.quals_to_string q)
in (

let uu____6914 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" uu____6912 uu____6913 uu____6914))))
in ((uu____6911), (r)))
in FStar_Errors.Error (uu____6908))
in (Prims.raise uu____6907))
end))
end))
in (

let uu____6917 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun uu____6938 lb -> (match (uu____6938) with
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____6962 = (

let uu____6968 = (FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____6968) with
| None -> begin
(match ((lb.FStar_Syntax_Syntax.lbunivs <> [])) with
| true -> begin
((false), (lb), (quals_opt))
end
| uu____6993 -> begin
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
| uu____7020 -> begin
(FStar_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end);
(match (((lb.FStar_Syntax_Syntax.lbunivs <> []) && ((FStar_List.length lb.FStar_Syntax_Syntax.lbunivs) <> (FStar_List.length uvs)))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Inline universes are incoherent with annotation from val declaration"), (r)))))
end
| uu____7027 -> begin
()
end);
(

let uu____7028 = (FStar_Syntax_Syntax.mk_lb ((FStar_Util.Inr (lbname)), (uvs), (FStar_Syntax_Const.effect_ALL_lid), (tval), (lb.FStar_Syntax_Syntax.lbdef)))
in ((false), (uu____7028), (quals_opt)));
))
end))
in (match (uu____6962) with
| (gen, lb, quals_opt) -> begin
((gen), ((lb)::lbs), (quals_opt))
end)))
end)) ((true), ([]), ((match ((quals = [])) with
| true -> begin
None
end
| uu____7059 -> begin
Some (quals)
end)))))
in (match (uu____6917) with
| (should_generalize, lbs', quals_opt) -> begin
(

let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Visible_default)::[]
end
| Some (q) -> begin
(

let uu____7082 = (FStar_All.pipe_right q (FStar_Util.for_some (fun uu___90_7084 -> (match (uu___90_7084) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Visible_default) | (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> begin
true
end
| uu____7085 -> begin
false
end))))
in (match (uu____7082) with
| true -> begin
q
end
| uu____7087 -> begin
(FStar_Syntax_Syntax.Visible_default)::q
end))
end)
in (

let lbs' = (FStar_List.rev lbs')
in (

let e = (

let uu____7093 = (

let uu____7096 = (

let uu____7097 = (

let uu____7105 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((((Prims.fst lbs)), (lbs'))), (uu____7105)))
in FStar_Syntax_Syntax.Tm_let (uu____7097))
in (FStar_Syntax_Syntax.mk uu____7096))
in (uu____7093 None r))
in (

let uu____7127 = (

let uu____7133 = (FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term (

let uu___113_7137 = env
in {FStar_TypeChecker_Env.solver = uu___113_7137.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___113_7137.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___113_7137.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___113_7137.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___113_7137.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___113_7137.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___113_7137.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___113_7137.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___113_7137.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___113_7137.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___113_7137.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = uu___113_7137.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = uu___113_7137.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___113_7137.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___113_7137.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___113_7137.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___113_7137.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___113_7137.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___113_7137.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___113_7137.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___113_7137.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___113_7137.FStar_TypeChecker_Env.qname_and_index}) e)
in (match (uu____7133) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = uu____7145; FStar_Syntax_Syntax.pos = uu____7146; FStar_Syntax_Syntax.vars = uu____7147}, uu____7148, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (uu____7167, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| uu____7172 -> begin
quals
end)
in ((FStar_Syntax_Syntax.Sig_let (((lbs), (r), (lids), (quals), (attrs)))), (lbs)))
end
| uu____7182 -> begin
(failwith "impossible")
end))
in (match (uu____7127) with
| (se, lbs) -> begin
((

let uu____7205 = (log env)
in (match (uu____7205) with
| true -> begin
(

let uu____7206 = (

let uu____7207 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (

let uu____7214 = (

let uu____7219 = (

let uu____7220 = (

let uu____7225 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____7225.FStar_Syntax_Syntax.fv_name)
in uu____7220.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env uu____7219))
in (match (uu____7214) with
| None -> begin
true
end
| uu____7232 -> begin
false
end))
in (match (should_log) with
| true -> begin
(

let uu____7237 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____7238 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" uu____7237 uu____7238)))
end
| uu____7239 -> begin
""
end)))))
in (FStar_All.pipe_right uu____7207 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" uu____7206))
end
| uu____7241 -> begin
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

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___91_7268 -> (match (uu___91_7268) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| uu____7269 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| uu____7277 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (uu____7282) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, uu____7295, r) -> begin
(

let uu____7303 = (is_abstract quals)
in (match (uu____7303) with
| true -> begin
(FStar_List.fold_right (fun se uu____7313 -> (match (uu____7313) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, uu____7336, uu____7337, quals, r) -> begin
(

let dec = (

let uu____7347 = (

let uu____7354 = (

let uu____7357 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow bs uu____7357))
in ((l), (us), (uu____7354), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____7347))
in (((dec)::out), (hidden)))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, uu____7368, uu____7369, uu____7370, uu____7371, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]), (r)))
in (((dec)::out), ((l)::hidden)))
end
| uu____7381 -> begin
((out), (hidden))
end)
end)) ses (([]), (hidden)))
end
| uu____7386 -> begin
(((se)::[]), (hidden))
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____7389, uu____7390, quals, uu____7392) -> begin
(

let uu____7395 = (is_abstract quals)
in (match (uu____7395) with
| true -> begin
(([]), (hidden))
end
| uu____7402 -> begin
(((se)::[]), (hidden))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, us, t, quals, r) -> begin
(

let uu____7412 = (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc))
in (match (uu____7412) with
| true -> begin
(((FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]), (r))))::[]), ((l)::hidden))
end
| uu____7421 -> begin
(

let uu____7422 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___92_7424 -> (match (uu___92_7424) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| uu____7427 -> begin
false
end))))
in (match (uu____7422) with
| true -> begin
(((se)::[]), (hidden))
end
| uu____7434 -> begin
(([]), (hidden))
end))
end))
end
| FStar_Syntax_Syntax.Sig_main (uu____7437) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____7449, uu____7450, quals, uu____7452) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____7470 = (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
in (match (uu____7470) with
| true -> begin
(([]), (hidden))
end
| uu____7478 -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::[]), ((FStar_Ident.range_of_lid lid))))
in (((dec)::[]), ((lid)::hidden)))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals, uu____7494) -> begin
(

let uu____7501 = (is_abstract quals)
in (match (uu____7501) with
| true -> begin
(

let uu____7506 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let uu____7512 = (

let uu____7519 = (

let uu____7520 = (

let uu____7525 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____7525.FStar_Syntax_Syntax.fv_name)
in uu____7520.FStar_Syntax_Syntax.v)
in ((uu____7519), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____7512)))))
in ((uu____7506), (hidden)))
end
| uu____7535 -> begin
(((se)::[]), (hidden))
end))
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let rec process_one_decl = (fun uu____7572 se -> (match (uu____7572) with
| (ses, exports, env, hidden) -> begin
((

let uu____7603 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____7603) with
| true -> begin
(

let uu____7604 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____7604))
end
| uu____7605 -> begin
()
end));
(

let uu____7606 = (tc_decl env se)
in (match (uu____7606) with
| (ses', env, ses_elaborated) -> begin
((

let uu____7628 = ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes"))))
in (match (uu____7628) with
| true -> begin
(

let uu____7629 = (FStar_List.fold_left (fun s se -> (

let uu____7632 = (

let uu____7633 = (FStar_Syntax_Print.sigelt_to_string se)
in (Prims.strcat uu____7633 "\n"))
in (Prims.strcat s uu____7632))) "" ses')
in (FStar_Util.print1 "Checked: %s\n" uu____7629))
end
| uu____7634 -> begin
()
end));
(FStar_List.iter (fun se -> (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)) ses');
(

let uu____7637 = (FStar_List.fold_left (fun uu____7646 se -> (match (uu____7646) with
| (le, lh) -> begin
(

let tup = (for_export hidden se)
in (((FStar_List.rev_append (Prims.fst tup) le)), ((FStar_List.rev_append (Prims.snd tup) lh))))
end)) (([]), ([])) ses')
in (match (uu____7637) with
| (exported, hidden) -> begin
(FStar_List.fold_left process_one_decl (((FStar_List.rev_append ses' ses)), (((FStar_List.rev_append exported []))::exports), (env), (hidden)) ses_elaborated)
end));
)
end));
)
end))
in (

let uu____7702 = (FStar_List.fold_left (fun acc se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, r) -> begin
(

let uu____7739 = acc
in (match (uu____7739) with
| (uu____7756, uu____7757, env, uu____7759) -> begin
(

let uu____7768 = (cps_and_elaborate env ne)
in (match (uu____7768) with
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
| uu____7801 -> begin
(process_one_decl acc se)
end)) (([]), ([]), (env), ([])) ses)
in (match (uu____7702) with
| (ses, exports, env, uu____7815) -> begin
(

let uu____7824 = (FStar_All.pipe_right (FStar_List.rev_append exports []) FStar_List.flatten)
in (((FStar_List.rev_append ses [])), (uu____7824), (env)))
end))))


let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (

let verify = (FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let action = (match (verify) with
| true -> begin
"Verifying"
end
| uu____7845 -> begin
"Lax-checking"
end)
in (

let label = (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____7847 -> begin
"implementation"
end)
in ((

let uu____7849 = (FStar_Options.debug_any ())
in (match (uu____7849) with
| true -> begin
(FStar_Util.print3 "%s %s of %s\n" action label modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
end
| uu____7850 -> begin
()
end));
(

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____7852 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let msg = (Prims.strcat "Internals for " name)
in (

let env = (

let uu___114_7855 = env
in {FStar_TypeChecker_Env.solver = uu___114_7855.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___114_7855.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___114_7855.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___114_7855.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___114_7855.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___114_7855.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___114_7855.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___114_7855.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___114_7855.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___114_7855.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___114_7855.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___114_7855.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___114_7855.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___114_7855.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___114_7855.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___114_7855.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = (not (verify)); FStar_TypeChecker_Env.lax = uu___114_7855.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___114_7855.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___114_7855.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___114_7855.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___114_7855.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___114_7855.FStar_TypeChecker_Env.qname_and_index})
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg);
(

let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

let uu____7858 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (uu____7858) with
| (ses, exports, env) -> begin
(((

let uu___115_7876 = modul
in {FStar_Syntax_Syntax.name = uu___115_7876.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = uu___115_7876.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___115_7876.FStar_Syntax_Syntax.is_interface})), (exports), (env))
end)));
))));
)))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let uu____7892 = (tc_decls env decls)
in (match (uu____7892) with
| (ses, exports, env) -> begin
(

let modul = (

let uu___116_7910 = modul
in {FStar_Syntax_Syntax.name = uu___116_7910.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = uu___116_7910.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___116_7910.FStar_Syntax_Syntax.is_interface})
in ((modul), (exports), (env)))
end)))


let check_exports : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env modul exports -> (

let env = (

let uu___117_7924 = env
in {FStar_TypeChecker_Env.solver = uu___117_7924.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___117_7924.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___117_7924.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___117_7924.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___117_7924.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___117_7924.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___117_7924.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___117_7924.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___117_7924.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___117_7924.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___117_7924.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___117_7924.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___117_7924.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = uu___117_7924.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___117_7924.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___117_7924.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___117_7924.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = true; FStar_TypeChecker_Env.type_of = uu___117_7924.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___117_7924.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___117_7924.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___117_7924.FStar_TypeChecker_Env.qname_and_index})
in (

let check_term = (fun lid univs t -> (

let uu____7935 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (uu____7935) with
| (univs, t) -> begin
((

let uu____7941 = (

let uu____7942 = (

let uu____7945 = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (FStar_TypeChecker_Env.debug uu____7945))
in (FStar_All.pipe_left uu____7942 (FStar_Options.Other ("Exports"))))
in (match (uu____7941) with
| true -> begin
(

let uu____7946 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____7947 = (

let uu____7948 = (FStar_All.pipe_right univs (FStar_List.map (fun x -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (x))))))
in (FStar_All.pipe_right uu____7948 (FStar_String.concat ", ")))
in (

let uu____7953 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print3 "Checking for export %s <%s> : %s\n" uu____7946 uu____7947 uu____7953))))
end
| uu____7954 -> begin
()
end));
(

let env = (FStar_TypeChecker_Env.push_univ_vars env univs)
in (

let uu____7956 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env t)
in (FStar_All.pipe_right uu____7956 Prims.ignore)));
)
end)))
in (

let check_term = (fun lid univs t -> ((

let uu____7974 = (

let uu____7975 = (FStar_Syntax_Print.lid_to_string modul.FStar_Syntax_Syntax.name)
in (

let uu____7976 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Interface of %s violates its abstraction (add a \'private\' qualifier to \'%s\'?)" uu____7975 uu____7976)))
in (FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____7974));
(check_term lid univs t);
(FStar_Errors.message_prefix.FStar_Errors.clear_prefix ());
))
in (

let rec check_sigelt = (fun uu___93_7981 -> (match (uu___93_7981) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, uu____7984, uu____7985) -> begin
(

let uu____7992 = (

let uu____7993 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____7993)))
in (match (uu____7992) with
| true -> begin
(FStar_All.pipe_right ses (FStar_List.iter check_sigelt))
end
| uu____7996 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (l, univs, binders, typ, uu____8001, uu____8002, uu____8003, r) -> begin
(

let t = (

let uu____8014 = (

let uu____8017 = (

let uu____8018 = (

let uu____8026 = (FStar_Syntax_Syntax.mk_Total typ)
in ((binders), (uu____8026)))
in FStar_Syntax_Syntax.Tm_arrow (uu____8018))
in (FStar_Syntax_Syntax.mk uu____8017))
in (uu____8014 None r))
in (check_term l univs t))
end
| FStar_Syntax_Syntax.Sig_datacon (l, univs, t, uu____8038, uu____8039, uu____8040, uu____8041, uu____8042) -> begin
(check_term l univs t)
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, univs, t, quals, uu____8051) -> begin
(

let uu____8054 = (

let uu____8055 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____8055)))
in (match (uu____8054) with
| true -> begin
(check_term l univs t)
end
| uu____8057 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_let ((uu____8058, lbs), uu____8060, uu____8061, quals, uu____8063) -> begin
(

let uu____8075 = (

let uu____8076 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____8076)))
in (match (uu____8075) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (check_term fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp)))))
end
| uu____8085 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, binders, comp, quals, flags, r) -> begin
(

let uu____8097 = (

let uu____8098 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____8098)))
in (match (uu____8097) with
| true -> begin
(

let arrow = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp))))) None r)
in (check_term l univs arrow))
end
| uu____8111 -> begin
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
| uu____8118 -> begin
(FStar_List.iter check_sigelt exports)
end))))))


let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (

let modul = (

let uu___118_8131 = modul
in {FStar_Syntax_Syntax.name = uu___118_8131.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu___118_8131.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module env modul)
in ((

let uu____8134 = (

let uu____8135 = (FStar_Options.lax ())
in (not (uu____8135)))
in (match (uu____8134) with
| true -> begin
(check_exports env modul exports)
end
| uu____8136 -> begin
()
end));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul);
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
(

let uu____8141 = (

let uu____8142 = (FStar_Options.interactive ())
in (not (uu____8142)))
in (match (uu____8141) with
| true -> begin
(

let uu____8143 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right uu____8143 Prims.ignore))
end
| uu____8144 -> begin
()
end));
((modul), (env));
))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let uu____8153 = (tc_partial_modul env modul)
in (match (uu____8153) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> ((

let uu____8174 = (FStar_Options.debug_any ())
in (match (uu____8174) with
| true -> begin
(

let uu____8175 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (match (m.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"i\'face"
end
| uu____8176 -> begin
"module"
end) uu____8175))
end
| uu____8177 -> begin
()
end));
(

let env = (

let uu___119_8179 = env
in (

let uu____8180 = (

let uu____8181 = (FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (not (uu____8181)))
in {FStar_TypeChecker_Env.solver = uu___119_8179.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___119_8179.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___119_8179.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___119_8179.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___119_8179.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___119_8179.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___119_8179.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___119_8179.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___119_8179.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___119_8179.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___119_8179.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___119_8179.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___119_8179.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___119_8179.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___119_8179.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___119_8179.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___119_8179.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___119_8179.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu____8180; FStar_TypeChecker_Env.lax_universes = uu___119_8179.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___119_8179.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___119_8179.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___119_8179.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___119_8179.FStar_TypeChecker_Env.qname_and_index}))
in (

let uu____8182 = (tc_modul env m)
in (match (uu____8182) with
| (m, env) -> begin
((

let uu____8190 = (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____8190) with
| true -> begin
(

let uu____8191 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" uu____8191))
end
| uu____8192 -> begin
()
end));
(

let uu____8194 = ((FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) && (FStar_Options.debug_at_level m.FStar_Syntax_Syntax.name.FStar_Ident.str (FStar_Options.Other ("Normalize"))))
in (match (uu____8194) with
| true -> begin
(

let normalize_toplevel_lets = (fun uu___94_8198 -> (match (uu___94_8198) with
| FStar_Syntax_Syntax.Sig_let ((b, lbs), r, ids, qs, attrs) -> begin
(

let n = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]))
in (

let update = (fun lb -> (

let uu____8225 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____8225) with
| (univnames, e) -> begin
(

let uu___120_8230 = lb
in (

let uu____8231 = (

let uu____8234 = (FStar_TypeChecker_Env.push_univ_vars env univnames)
in (n uu____8234 e))
in {FStar_Syntax_Syntax.lbname = uu___120_8230.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___120_8230.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___120_8230.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___120_8230.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____8231}))
end)))
in (

let uu____8235 = (

let uu____8244 = (

let uu____8248 = (FStar_List.map update lbs)
in ((b), (uu____8248)))
in ((uu____8244), (r), (ids), (qs), (attrs)))
in FStar_Syntax_Syntax.Sig_let (uu____8235))))
end
| se -> begin
se
end))
in (

let normalized_module = (

let uu___121_8259 = m
in (

let uu____8260 = (FStar_List.map normalize_toplevel_lets m.FStar_Syntax_Syntax.declarations)
in {FStar_Syntax_Syntax.name = uu___121_8259.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu____8260; FStar_Syntax_Syntax.exports = uu___121_8259.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___121_8259.FStar_Syntax_Syntax.is_interface}))
in (

let uu____8261 = (FStar_Syntax_Print.modul_to_string normalized_module)
in (FStar_Util.print1 "%s\n" uu____8261))))
end
| uu____8262 -> begin
()
end));
((m), (env));
)
end)));
))




