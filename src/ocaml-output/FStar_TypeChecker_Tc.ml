
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

let uu___96_12 = env
in {FStar_TypeChecker_Env.solver = uu___96_12.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___96_12.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___96_12.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___96_12.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___96_12.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___96_12.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___96_12.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___96_12.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___96_12.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___96_12.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___96_12.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___96_12.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___96_12.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___96_12.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___96_12.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___96_12.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___96_12.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___96_12.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___96_12.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___96_12.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___96_12.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___96_12.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___96_12.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), ((Prims.parse_int "0"))))}))
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

let uu___97_24 = env
in {FStar_TypeChecker_Env.solver = uu___97_24.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___97_24.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___97_24.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___97_24.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___97_24.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___97_24.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___97_24.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___97_24.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___97_24.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___97_24.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___97_24.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___97_24.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___97_24.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___97_24.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___97_24.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___97_24.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___97_24.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___97_24.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___97_24.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___97_24.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___97_24.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___97_24.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___97_24.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), ((Prims.parse_int "0"))))})))
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

let uu___98_380 = ed
in {FStar_Syntax_Syntax.qualifiers = uu___98_380.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___98_380.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___98_380.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___98_380.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = uu___98_380.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = uu___98_380.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = uu___98_380.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = uu___98_380.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = uu___98_380.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = uu___98_380.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = uu___98_380.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = uu___98_380.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = uu___98_380.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = uu___98_380.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = uu___98_380.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = uu___98_380.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = uu___98_380.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = uu___98_380.FStar_Syntax_Syntax.actions})
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

let uu___99_402 = ed
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

let uu___100_425 = a
in (

let uu____426 = (

let uu____427 = (op (([]), (a.FStar_Syntax_Syntax.action_defn)))
in (Prims.snd uu____427))
in (

let uu____433 = (

let uu____434 = (op (([]), (a.FStar_Syntax_Syntax.action_typ)))
in (Prims.snd uu____434))
in {FStar_Syntax_Syntax.action_name = uu___100_425.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___100_425.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___100_425.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = uu____426; FStar_Syntax_Syntax.action_typ = uu____433})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.qualifiers = uu___99_402.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___99_402.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___99_402.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___99_402.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu___99_402.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = uu___99_402.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = uu____403; FStar_Syntax_Syntax.bind_wp = uu____404; FStar_Syntax_Syntax.if_then_else = uu____405; FStar_Syntax_Syntax.ite_wp = uu____406; FStar_Syntax_Syntax.stronger = uu____407; FStar_Syntax_Syntax.close_wp = uu____408; FStar_Syntax_Syntax.assert_p = uu____409; FStar_Syntax_Syntax.assume_p = uu____410; FStar_Syntax_Syntax.null_wp = uu____411; FStar_Syntax_Syntax.trivial = uu____412; FStar_Syntax_Syntax.repr = uu____413; FStar_Syntax_Syntax.return_repr = uu____420; FStar_Syntax_Syntax.bind_repr = uu____421; FStar_Syntax_Syntax.actions = uu____422}))))))))))))))))
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

let uu___101_1088 = env
in {FStar_TypeChecker_Env.solver = uu___101_1088.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___101_1088.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___101_1088.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___101_1088.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___101_1088.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___101_1088.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___101_1088.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___101_1088.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___101_1088.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___101_1088.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___101_1088.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___101_1088.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___101_1088.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___101_1088.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___101_1088.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___101_1088.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___101_1088.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___101_1088.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___101_1088.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___101_1088.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___101_1088.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___101_1088.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___101_1088.FStar_TypeChecker_Env.qname_and_index})
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

let uu___102_1320 = act
in {FStar_Syntax_Syntax.action_name = uu___102_1320.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___102_1320.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = act_defn; FStar_Syntax_Syntax.action_typ = act_typ}))
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

let uu___103_1416 = act
in {FStar_Syntax_Syntax.action_name = uu___103_1416.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___103_1416.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = defn; FStar_Syntax_Syntax.action_typ = typ})
end))
end)))
in (

let nunivs = (FStar_List.length univs)
in (

let ed = (

let uu___104_1421 = ed
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
in {FStar_Syntax_Syntax.qualifiers = uu___104_1421.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___104_1421.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___104_1421.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = uu____1422; FStar_Syntax_Syntax.bind_wp = uu____1423; FStar_Syntax_Syntax.if_then_else = uu____1424; FStar_Syntax_Syntax.ite_wp = uu____1425; FStar_Syntax_Syntax.stronger = uu____1426; FStar_Syntax_Syntax.close_wp = uu____1427; FStar_Syntax_Syntax.assert_p = uu____1428; FStar_Syntax_Syntax.assume_p = uu____1429; FStar_Syntax_Syntax.null_wp = uu____1430; FStar_Syntax_Syntax.trivial = uu____1431; FStar_Syntax_Syntax.repr = uu____1432; FStar_Syntax_Syntax.return_repr = uu____1439; FStar_Syntax_Syntax.bind_repr = uu____1440; FStar_Syntax_Syntax.actions = uu____1441})))))))))))))))
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

let uu___105_1497 = bv
in (

let uu____1498 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___105_1497.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___105_1497.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1498}))
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

let uu____2111 = (FStar_Syntax_Util.args_of_binders effect_binders)
in (Prims.snd uu____2111))
in ((t), (uu____2107)))
in FStar_Syntax_Syntax.Tm_app (uu____2097))
in (mk uu____2096))
in (FStar_Syntax_Subst.close effect_binders uu____2095))
end))
in (

let register = (fun name item -> (

let uu____2138 = (

let uu____2141 = (mk_lid name)
in (

let uu____2142 = (FStar_Syntax_Util.abs effect_binders item None)
in (FStar_TypeChecker_Util.mk_toplevel_definition env uu____2141 uu____2142)))
in (match (uu____2138) with
| (sigelt, fv) -> begin
((

let uu____2151 = (

let uu____2153 = (FStar_ST.read sigelts)
in (sigelt)::uu____2153)
in (FStar_ST.write sigelts uu____2151));
fv;
)
end)))
in (

let lift_from_pure_wp = (register "lift_from_pure" lift_from_pure_wp)
in (

let return_wp = (register "return_wp" return_wp)
in ((

let uu____2164 = (

let uu____2166 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true")), (FStar_Range.dummyRange))))::uu____2166)
in (FStar_ST.write sigelts uu____2164));
(

let return_elab = (register "return_elab" return_elab)
in ((

let uu____2176 = (

let uu____2178 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false")), (FStar_Range.dummyRange))))::uu____2178)
in (FStar_ST.write sigelts uu____2176));
(

let bind_wp = (register "bind_wp" bind_wp)
in ((

let uu____2188 = (

let uu____2190 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true")), (FStar_Range.dummyRange))))::uu____2190)
in (FStar_ST.write sigelts uu____2188));
(

let bind_elab = (register "bind_elab" bind_elab)
in ((

let uu____2200 = (

let uu____2202 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false")), (FStar_Range.dummyRange))))::uu____2202)
in (FStar_ST.write sigelts uu____2200));
(

let uu____2210 = (FStar_List.fold_left (fun uu____2217 action -> (match (uu____2217) with
| (dmff_env, actions) -> begin
(

let uu____2229 = (elaborate_and_star dmff_env ((action.FStar_Syntax_Syntax.action_univs), (action.FStar_Syntax_Syntax.action_defn)))
in (match (uu____2229) with
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

let uu____2245 = (

let uu____2247 = (

let uu___106_2248 = action
in (

let uu____2249 = (apply_close action_elab)
in (

let uu____2250 = (apply_close action_typ_with_wp)
in {FStar_Syntax_Syntax.action_name = uu___106_2248.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___106_2248.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___106_2248.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = uu____2249; FStar_Syntax_Syntax.action_typ = uu____2250})))
in (uu____2247)::actions)
in ((dmff_env), (uu____2245)))))))
end))
end)) ((dmff_env), ([])) ed.FStar_Syntax_Syntax.actions)
in (match (uu____2210) with
| (dmff_env, actions) -> begin
(

let actions = (FStar_List.rev actions)
in (

let repr = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp_a" None wp_a)
in (

let binders = (

let uu____2268 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____2269 = (

let uu____2271 = (FStar_Syntax_Syntax.mk_binder wp)
in (uu____2271)::[])
in (uu____2268)::uu____2269))
in (

let uu____2272 = (

let uu____2273 = (

let uu____2274 = (

let uu____2275 = (

let uu____2285 = (

let uu____2289 = (

let uu____2292 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____2293 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____2292), (uu____2293))))
in (uu____2289)::[])
in ((repr), (uu____2285)))
in FStar_Syntax_Syntax.Tm_app (uu____2275))
in (mk uu____2274))
in (

let uu____2301 = (FStar_Syntax_Syntax.bv_to_name wp)
in (FStar_TypeChecker_DMFF.trans_F dmff_env uu____2273 uu____2301)))
in (FStar_Syntax_Util.abs binders uu____2272 None))))
in (

let repr = (recheck_debug "FC" env repr)
in (

let repr = (register "repr" repr)
in (

let uu____2309 = (

let uu____2314 = (

let uu____2315 = (

let uu____2318 = (FStar_Syntax_Subst.compress wp_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____2318))
in uu____2315.FStar_Syntax_Syntax.n)
in (match (uu____2314) with
| FStar_Syntax_Syntax.Tm_abs ((type_param)::effect_param, arrow, uu____2326) -> begin
(

let uu____2353 = (

let uu____2362 = (FStar_Syntax_Subst.open_term ((type_param)::effect_param) arrow)
in (match (uu____2362) with
| ((b)::bs, body) -> begin
((b), (bs), (body))
end
| uu____2393 -> begin
(failwith "Impossible : open_term nt preserving binders arity")
end))
in (match (uu____2353) with
| (type_param, effect_param, arrow) -> begin
(

let uu____2421 = (

let uu____2422 = (

let uu____2425 = (FStar_Syntax_Subst.compress arrow)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____2425))
in uu____2422.FStar_Syntax_Syntax.n)
in (match (uu____2421) with
| FStar_Syntax_Syntax.Tm_arrow (wp_binders, c) -> begin
(

let uu____2442 = (FStar_Syntax_Subst.open_comp wp_binders c)
in (match (uu____2442) with
| (wp_binders, c) -> begin
(

let uu____2451 = (FStar_List.partition (fun uu____2462 -> (match (uu____2462) with
| (bv, uu____2466) -> begin
(

let uu____2467 = (

let uu____2468 = (FStar_Syntax_Free.names bv.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____2468 (FStar_Util.set_mem (Prims.fst type_param))))
in (FStar_All.pipe_right uu____2467 Prims.op_Negation))
end)) wp_binders)
in (match (uu____2451) with
| (pre_args, post_args) -> begin
(

let post = (match (post_args) with
| (post)::[] -> begin
post
end
| uu____2501 -> begin
(

let uu____2505 = (

let uu____2506 = (FStar_Syntax_Print.term_to_string arrow)
in (FStar_Util.format1 "Impossible: multiple post candidates %s" uu____2506))
in (failwith uu____2505))
end)
in (

let uu____2509 = (FStar_Syntax_Util.arrow pre_args c)
in (

let uu____2512 = (FStar_Syntax_Util.abs ((type_param)::effect_param) (Prims.fst post).FStar_Syntax_Syntax.sort None)
in ((uu____2509), (uu____2512)))))
end))
end))
end
| uu____2522 -> begin
(

let uu____2523 = (

let uu____2524 = (FStar_Syntax_Print.term_to_string arrow)
in (FStar_Util.format1 "Impossible: pre/post arrow %s" uu____2524))
in (failwith uu____2523))
end))
end))
end
| uu____2529 -> begin
(

let uu____2530 = (

let uu____2531 = (FStar_Syntax_Print.term_to_string wp_type)
in (FStar_Util.format1 "Impossible: pre/post abs %s" uu____2531))
in (failwith uu____2530))
end))
in (match (uu____2309) with
| (pre, post) -> begin
((

let uu____2548 = (register "pre" pre)
in ());
(

let uu____2550 = (register "post" post)
in ());
(

let uu____2552 = (register "wp" wp_type)
in ());
(

let ed = (

let uu___107_2554 = ed
in (

let uu____2555 = (FStar_Syntax_Subst.close_binders effect_binders)
in (

let uu____2556 = (FStar_Syntax_Subst.close effect_binders effect_signature)
in (

let uu____2557 = (

let uu____2558 = (apply_close return_wp)
in (([]), (uu____2558)))
in (

let uu____2564 = (

let uu____2565 = (apply_close bind_wp)
in (([]), (uu____2565)))
in (

let uu____2571 = (apply_close repr)
in (

let uu____2572 = (

let uu____2573 = (apply_close return_elab)
in (([]), (uu____2573)))
in (

let uu____2579 = (

let uu____2580 = (apply_close bind_elab)
in (([]), (uu____2580)))
in {FStar_Syntax_Syntax.qualifiers = uu___107_2554.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___107_2554.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___107_2554.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___107_2554.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu____2555; FStar_Syntax_Syntax.signature = uu____2556; FStar_Syntax_Syntax.ret_wp = uu____2557; FStar_Syntax_Syntax.bind_wp = uu____2564; FStar_Syntax_Syntax.if_then_else = uu___107_2554.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = uu___107_2554.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = uu___107_2554.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = uu___107_2554.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = uu___107_2554.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = uu___107_2554.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = uu___107_2554.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = uu___107_2554.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = uu____2571; FStar_Syntax_Syntax.return_repr = uu____2572; FStar_Syntax_Syntax.bind_repr = uu____2579; FStar_Syntax_Syntax.actions = actions}))))))))
in (

let uu____2586 = (FStar_TypeChecker_DMFF.gen_wps_for_free env effect_binders a wp_a ed)
in (match (uu____2586) with
| (sigelts', ed) -> begin
((

let uu____2597 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____2597) with
| true -> begin
(

let uu____2598 = (FStar_Syntax_Print.eff_decl_to_string true ed)
in (FStar_Util.print_string uu____2598))
end
| uu____2599 -> begin
()
end));
(

let lift_from_pure_opt = (match (((FStar_List.length effect_binders) = (Prims.parse_int "0"))) with
| true -> begin
(

let lift_from_pure = (

let uu____2608 = (

let uu____2610 = (

let uu____2616 = (apply_close lift_from_pure_wp)
in (([]), (uu____2616)))
in Some (uu____2610))
in {FStar_Syntax_Syntax.source = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.target = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.lift_wp = uu____2608; FStar_Syntax_Syntax.lift = None})
in Some (FStar_Syntax_Syntax.Sig_sub_effect (((lift_from_pure), (FStar_Range.dummyRange)))))
end
| uu____2627 -> begin
None
end)
in (

let uu____2628 = (

let uu____2630 = (

let uu____2632 = (FStar_ST.read sigelts)
in (FStar_List.rev uu____2632))
in (FStar_List.append uu____2630 sigelts'))
in ((uu____2628), (ed), (lift_from_pure_opt))));
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
| (FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, uu____2655, uu____2656, [], r))::(FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, _0_28, [], uu____2661, r1))::(FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, _0_29, [], uu____2666, r2))::[] when (((_0_28 = (Prims.parse_int "0")) && (_0_29 = (Prims.parse_int "0"))) && (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid))) -> begin
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

let uu____2710 = (

let uu____2713 = (

let uu____2714 = (

let uu____2719 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1) FStar_Syntax_Syntax.Delta_constant None)
in ((uu____2719), ((FStar_Syntax_Syntax.U_name (utop))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____2714))
in (FStar_Syntax_Syntax.mk uu____2713))
in (uu____2710 None r1))
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

let uu____2740 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) uu____2740))
in (

let hd = (

let uu____2746 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) uu____2746))
in (

let tl = (

let uu____2748 = (

let uu____2749 = (

let uu____2752 = (

let uu____2753 = (

let uu____2758 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2) FStar_Syntax_Syntax.Delta_constant None)
in ((uu____2758), ((FStar_Syntax_Syntax.U_name (ucons2))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____2753))
in (FStar_Syntax_Syntax.mk uu____2752))
in (uu____2749 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) uu____2748))
in (

let res = (

let uu____2771 = (

let uu____2774 = (

let uu____2775 = (

let uu____2780 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2) FStar_Syntax_Syntax.Delta_constant None)
in ((uu____2780), ((FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____2775))
in (FStar_Syntax_Syntax.mk uu____2774))
in (uu____2771 None r2))
in (

let uu____2790 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow ((((a), (Some (FStar_Syntax_Syntax.imp_tag))))::(((hd), (None)))::(((tl), (None)))::[]) uu____2790))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon (((lex_cons), ((ucons1)::(ucons2)::[]), (lex_cons_t), (FStar_Syntax_Const.lex_t_lid), ((Prims.parse_int "0")), ([]), ([]), (r2)))
in (

let uu____2813 = (

let uu____2821 = (FStar_TypeChecker_Env.get_range env)
in (((tc)::(dc_lextop)::(dc_lexcons)::[]), ([]), (lids), (uu____2821)))
in FStar_Syntax_Syntax.Sig_bundle (uu____2813)))))))))))))))
end
| uu____2825 -> begin
(

let uu____2827 = (

let uu____2828 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle (((ses), ([]), (lids), (FStar_Range.dummyRange)))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" uu____2828))
in (failwith uu____2827))
end))
and tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let uu____2839 = (FStar_Syntax_Util.type_u ())
in (match (uu____2839) with
| (k, uu____2843) -> begin
(

let phi = (

let uu____2845 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right uu____2845 (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env)))
in ((FStar_TypeChecker_Util.check_uvars r phi);
FStar_Syntax_Syntax.Sig_assume (((lid), (phi), (quals), (r)));
))
end))))
and tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env ses quals lids -> (

let warn_positivity = (fun l r -> (

let uu____2862 = (

let uu____2863 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" uu____2863))
in (FStar_Errors.diag r uu____2862)))
in (

let env0 = env
in (

let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
((warn_positivity tc r);
(

let uu____2900 = (FStar_Syntax_Subst.open_term tps k)
in (match (uu____2900) with
| (tps, k) -> begin
(

let uu____2909 = (FStar_TypeChecker_TcTerm.tc_binders env tps)
in (match (uu____2909) with
| (tps, env_tps, guard_params, us) -> begin
(

let uu____2922 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____2922) with
| (indices, t) -> begin
(

let uu____2946 = (FStar_TypeChecker_TcTerm.tc_binders env_tps indices)
in (match (uu____2946) with
| (indices, env', guard_indices, us') -> begin
(

let uu____2959 = (

let uu____2962 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' t)
in (match (uu____2962) with
| (t, uu____2969, g) -> begin
(

let uu____2971 = (

let uu____2972 = (

let uu____2973 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params uu____2973))
in (FStar_TypeChecker_Rel.discharge_guard env' uu____2972))
in ((t), (uu____2971)))
end))
in (match (uu____2959) with
| (t, guard) -> begin
(

let k = (

let uu____2983 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices uu____2983))
in (

let uu____2986 = (FStar_Syntax_Util.type_u ())
in (match (uu____2986) with
| (t_type, u) -> begin
((

let uu____2996 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' uu____2996));
(

let t_tc = (

let uu____3000 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) uu____3000))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____3008 = (FStar_TypeChecker_Env.push_let_binding env (FStar_Util.Inr (fv_tc)) (([]), (t_tc)))
in ((uu____3008), (FStar_Syntax_Syntax.Sig_inductive_typ (((tc), ([]), (tps), (k), (mutuals), (data), (quals), (r)))), (u), (guard)))))));
)
end)))
end))
end))
end))
end))
end));
)
end
| uu____3016 -> begin
(failwith "impossible")
end))
in (

let positive_if_pure = (fun uu____3026 l -> ())
in (

let tc_data = (fun env tcs uu___83_3042 -> (match (uu___83_3042) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let uu____3061 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun uu____3075 -> (match (uu____3075) with
| (se, u_tc) -> begin
(

let uu____3084 = (

let uu____3085 = (FStar_Util.must (FStar_Syntax_Util.lid_of_sigelt se))
in (FStar_Ident.lid_equals tc_lid uu____3085))
in (match (uu____3084) with
| true -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____3094, uu____3095, tps, uu____3097, uu____3098, uu____3099, uu____3100, uu____3101) -> begin
(

let tps = (FStar_All.pipe_right tps (FStar_List.map (fun uu____3122 -> (match (uu____3122) with
| (x, uu____3129) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let tps = (FStar_Syntax_Subst.open_binders tps)
in (

let uu____3132 = (

let uu____3136 = (FStar_TypeChecker_Env.push_binders env tps)
in ((uu____3136), (tps), (u_tc)))
in Some (uu____3132))))
end
| uu____3140 -> begin
(failwith "Impossible")
end)
end
| uu____3145 -> begin
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
| uu____3170 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected data constructor"), (r)))))
end)
end))
in (match (uu____3061) with
| (env, tps, u_tc) -> begin
(

let uu____3179 = (

let uu____3187 = (

let uu____3188 = (FStar_Syntax_Subst.compress t)
in uu____3188.FStar_Syntax_Syntax.n)
in (match (uu____3187) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let uu____3210 = (FStar_Util.first_N ntps bs)
in (match (uu____3210) with
| (uu____3228, bs') -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs'), (res)))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i uu____3260 -> (match (uu____3260) with
| (x, uu____3264) -> begin
FStar_Syntax_Syntax.DB ((((ntps - ((Prims.parse_int "1") + i))), (x)))
end))))
in (

let uu____3265 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals uu____3265))))
end))
end
| uu____3266 -> begin
(([]), (t))
end))
in (match (uu____3179) with
| (arguments, result) -> begin
((

let uu____3287 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____3287) with
| true -> begin
(

let uu____3288 = (FStar_Syntax_Print.lid_to_string c)
in (

let uu____3289 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (

let uu____3290 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" uu____3288 uu____3289 uu____3290))))
end
| uu____3291 -> begin
()
end));
(

let uu____3292 = (tc_tparams env arguments)
in (match (uu____3292) with
| (arguments, env', us) -> begin
(

let uu____3301 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env' result)
in (match (uu____3301) with
| (result, res_lcomp) -> begin
((

let uu____3309 = (

let uu____3310 = (FStar_Syntax_Subst.compress res_lcomp.FStar_Syntax_Syntax.res_typ)
in uu____3310.FStar_Syntax_Syntax.n)
in (match (uu____3309) with
| FStar_Syntax_Syntax.Tm_type (uu____3313) -> begin
()
end
| ty -> begin
(

let uu____3315 = (

let uu____3316 = (

let uu____3319 = (

let uu____3320 = (FStar_Syntax_Print.term_to_string result)
in (

let uu____3321 = (FStar_Syntax_Print.term_to_string res_lcomp.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "The type of %s is %s, but since this is the result type of a constructor its type should be Type" uu____3320 uu____3321)))
in ((uu____3319), (r)))
in FStar_Errors.Error (uu____3316))
in (Prims.raise uu____3315))
end));
(

let uu____3322 = (FStar_Syntax_Util.head_and_args result)
in (match (uu____3322) with
| (head, uu____3335) -> begin
((

let uu____3351 = (

let uu____3352 = (FStar_Syntax_Subst.compress head)
in uu____3352.FStar_Syntax_Syntax.n)
in (match (uu____3351) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| uu____3356 -> begin
(

let uu____3357 = (

let uu____3358 = (

let uu____3361 = (

let uu____3362 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (

let uu____3363 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" uu____3362 uu____3363)))
in ((uu____3361), (r)))
in FStar_Errors.Error (uu____3358))
in (Prims.raise uu____3357))
end));
(

let g = (FStar_List.fold_left2 (fun g uu____3368 u_x -> (match (uu____3368) with
| (x, uu____3373) -> begin
(

let uu____3375 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g uu____3375))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (

let uu____3379 = (

let uu____3383 = (FStar_All.pipe_right tps (FStar_List.map (fun uu____3397 -> (match (uu____3397) with
| (x, uu____3404) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append uu____3383 arguments))
in (

let uu____3409 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow uu____3379 uu____3409)))
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
| uu____3417 -> begin
(failwith "impossible")
end))
in (

let generalize_and_inst_within = (fun env g tcs datas -> ((FStar_TypeChecker_Rel.force_trivial_guard env g);
(

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun uu___84_3446 -> (match (uu___84_3446) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____3447, uu____3448, tps, k, uu____3451, uu____3452, uu____3453, uu____3454) -> begin
(

let uu____3461 = (

let uu____3462 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) uu____3462))
in (FStar_Syntax_Syntax.null_binder uu____3461))
end
| uu____3469 -> begin
(failwith "Impossible")
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun uu___85_3474 -> (match (uu___85_3474) with
| FStar_Syntax_Syntax.Sig_datacon (uu____3475, uu____3476, t, uu____3478, uu____3479, uu____3480, uu____3481, uu____3482) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| uu____3487 -> begin
(failwith "Impossible")
end))))
in (

let t = (

let uu____3491 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') uu____3491))
in ((

let uu____3495 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____3495) with
| true -> begin
(

let uu____3496 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" uu____3496))
end
| uu____3497 -> begin
()
end));
(

let uu____3498 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (uu____3498) with
| (uvs, t) -> begin
((

let uu____3508 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____3508) with
| true -> begin
(

let uu____3509 = (

let uu____3510 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right uu____3510 (FStar_String.concat ", ")))
in (

let uu____3516 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" uu____3509 uu____3516)))
end
| uu____3517 -> begin
()
end));
(

let uu____3518 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____3518) with
| (uvs, t) -> begin
(

let uu____3527 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____3527) with
| (args, uu____3540) -> begin
(

let uu____3551 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (uu____3551) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun uu____3586 se -> (match (uu____3586) with
| (x, uu____3591) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____3593, tps, uu____3595, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let uu____3607 = (

let uu____3615 = (

let uu____3616 = (FStar_Syntax_Subst.compress ty)
in uu____3616.FStar_Syntax_Syntax.n)
in (match (uu____3615) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____3638 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (uu____3638) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____3681 -> begin
(

let uu____3685 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) uu____3685 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in ((tps), (t)))
end))
end
| uu____3704 -> begin
(([]), (ty))
end))
in (match (uu____3607) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs), (tps), (t), (mutuals), (datas), (quals), (r)))
end)))
end
| uu____3730 -> begin
(failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| uu____3734 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _0_30 -> FStar_Syntax_Syntax.U_name (_0_30))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun uu___86_3751 -> (match (uu___86_3751) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____3756, uu____3757, uu____3758, uu____3759, uu____3760, uu____3761, uu____3762) -> begin
((tc), (uvs_universes))
end
| uu____3770 -> begin
(failwith "Impossible")
end))))
in (FStar_List.map2 (fun uu____3776 d -> (match (uu____3776) with
| (t, uu____3781) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, uu____3783, uu____3784, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (

let uu____3795 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____3795 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon (((l), (uvs), (ty), (tc), (ntps), (quals), (mutuals), (r))))
end
| uu____3798 -> begin
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
))
in (

let uu____3801 = (FStar_All.pipe_right ses (FStar_List.partition (fun uu___87_3811 -> (match (uu___87_3811) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____3812) -> begin
true
end
| uu____3824 -> begin
false
end))))
in (match (uu____3801) with
| (tys, datas) -> begin
((

let uu____3836 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun uu___88_3838 -> (match (uu___88_3838) with
| FStar_Syntax_Syntax.Sig_datacon (uu____3839) -> begin
false
end
| uu____3850 -> begin
true
end))))
in (match (uu____3836) with
| true -> begin
(

let uu____3851 = (

let uu____3852 = (

let uu____3855 = (FStar_TypeChecker_Env.get_range env)
in (("Mutually defined type contains a non-inductive element"), (uu____3855)))
in FStar_Errors.Error (uu____3852))
in (Prims.raise uu____3851))
end
| uu____3856 -> begin
()
end));
(

let env0 = env
in (

let uu____3858 = (FStar_List.fold_right (fun tc uu____3872 -> (match (uu____3872) with
| (env, all_tcs, g) -> begin
(

let uu____3894 = (tc_tycon env tc)
in (match (uu____3894) with
| (env, tc, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in ((

let uu____3911 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____3911) with
| true -> begin
(

let uu____3912 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" uu____3912))
end
| uu____3913 -> begin
()
end));
(

let uu____3914 = (

let uu____3915 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g uu____3915))
in ((env), ((((tc), (tc_u)))::all_tcs), (uu____3914)));
))
end))
end)) tys ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (uu____3858) with
| (env, tcs, g) -> begin
(

let uu____3939 = (FStar_List.fold_right (fun se uu____3947 -> (match (uu____3947) with
| (datas, g) -> begin
(

let uu____3958 = (tc_data env tcs se)
in (match (uu____3958) with
| (data, g') -> begin
(

let uu____3966 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((data)::datas), (uu____3966)))
end))
end)) datas (([]), (g)))
in (match (uu____3939) with
| (datas, g) -> begin
(

let uu____3977 = (

let uu____3982 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g uu____3982 datas))
in (match (uu____3977) with
| (tcs, datas) -> begin
(

let sig_bndle = (

let uu____3997 = (

let uu____4005 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (uu____4005)))
in FStar_Syntax_Syntax.Sig_bundle (uu____3997))
in (

let data_ops_ses = (

let uu____4011 = (FStar_List.map (FStar_TypeChecker_Util.mk_data_operations quals env tcs) datas)
in (FStar_All.pipe_right uu____4011 FStar_List.flatten))
in (

let datacon_typ = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (uu____4022, uu____4023, t, uu____4025, uu____4026, uu____4027, uu____4028, uu____4029) -> begin
t
end
| uu____4034 -> begin
(failwith "Impossible!")
end))
in (

let dr = FStar_Range.dummyRange
in (

let optimized_haseq_scheme = (fun uu____4040 -> (

let haseq_ty = (fun usubst us acc ty -> (

let uu____4084 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____4096, bs, t, uu____4099, d_lids, uu____4101, uu____4102) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____4110 -> begin
(failwith "Impossible!")
end)
in (match (uu____4084) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (

let uu____4135 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst uu____4135 t))
in (

let uu____4142 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____4142) with
| (bs, t) -> begin
(

let ibs = (

let uu____4162 = (

let uu____4163 = (FStar_Syntax_Subst.compress t)
in uu____4163.FStar_Syntax_Syntax.n)
in (match (uu____4162) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____4170) -> begin
ibs
end
| uu____4181 -> begin
[]
end))
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (

let uu____4186 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____4187 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____4186 uu____4187)))
in (

let ind = (

let uu____4192 = (

let uu____4193 = (FStar_List.map (fun uu____4198 -> (match (uu____4198) with
| (bv, aq) -> begin
(

let uu____4205 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____4205), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____4193))
in (uu____4192 None dr))
in (

let ind = (

let uu____4213 = (

let uu____4214 = (FStar_List.map (fun uu____4219 -> (match (uu____4219) with
| (bv, aq) -> begin
(

let uu____4226 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____4226), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____4214))
in (uu____4213 None dr))
in (

let haseq_ind = (

let uu____4234 = (

let uu____4235 = (

let uu____4236 = (FStar_Syntax_Syntax.as_arg ind)
in (uu____4236)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____4235))
in (uu____4234 None dr))
in (

let bs' = (FStar_List.filter (fun b -> (

let uu____4250 = acc
in (match (uu____4250) with
| (uu____4258, en, uu____4260, uu____4261) -> begin
(

let opt = (

let uu____4270 = (

let uu____4271 = (FStar_Syntax_Util.type_u ())
in (Prims.fst uu____4271))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort uu____4270 false))
in (match (opt) with
| None -> begin
false
end
| Some (uu____4274) -> begin
true
end))
end))) bs)
in (

let haseq_bs = (FStar_List.fold_left (fun t b -> (

let uu____4278 = (

let uu____4279 = (

let uu____4280 = (

let uu____4281 = (

let uu____4282 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b))
in (FStar_Syntax_Syntax.as_arg uu____4282))
in (uu____4281)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____4280))
in (uu____4279 None dr))
in (FStar_Syntax_Util.mk_conj t uu____4278))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml = (

let uu___108_4291 = fml
in (

let uu____4292 = (

let uu____4293 = (

let uu____4298 = (

let uu____4299 = (

let uu____4306 = (

let uu____4308 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (uu____4308)::[])
in (uu____4306)::[])
in FStar_Syntax_Syntax.Meta_pattern (uu____4299))
in ((fml), (uu____4298)))
in FStar_Syntax_Syntax.Tm_meta (uu____4293))
in {FStar_Syntax_Syntax.n = uu____4292; FStar_Syntax_Syntax.tk = uu___108_4291.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___108_4291.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___108_4291.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (

let uu____4320 = (

let uu____4321 = (

let uu____4322 = (

let uu____4323 = (

let uu____4324 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____4324 None))
in (FStar_Syntax_Syntax.as_arg uu____4323))
in (uu____4322)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____4321))
in (uu____4320 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (

let uu____4346 = (

let uu____4347 = (

let uu____4348 = (

let uu____4349 = (

let uu____4350 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____4350 None))
in (FStar_Syntax_Syntax.as_arg uu____4349))
in (uu____4348)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____4347))
in (uu____4346 None dr))) bs fml)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let uu____4370 = acc
in (match (uu____4370) with
| (l_axioms, env, guard', cond') -> begin
(

let env = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env = (FStar_TypeChecker_Env.push_binders env ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (uu____4404, uu____4405, uu____4406, t_lid, uu____4408, uu____4409, uu____4410, uu____4411) -> begin
(t_lid = lid)
end
| uu____4416 -> begin
(failwith "Impossible")
end)) datas)
in (

let haseq_data = (fun data -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (

let uu____4423 = (

let uu____4424 = (FStar_Syntax_Subst.compress dt)
in uu____4424.FStar_Syntax_Syntax.n)
in (match (uu____4423) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____4428) -> begin
(

let dbs = (

let uu____4443 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd uu____4443))
in (

let dbs = (

let uu____4465 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders uu____4465 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let haseq_b = (

let uu____4474 = (

let uu____4475 = (

let uu____4476 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (uu____4476)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____4475))
in (uu____4474 None dr))
in (

let sort_range = (Prims.fst b).FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos
in (

let haseq_b = (

let uu____4483 = (

let uu____4484 = (FStar_Syntax_Print.term_to_string ind)
in (FStar_Util.format1 "Failed to prove that the type \'%s\' supports decidable equality because of this argument; add the \'noeq\' qualifier" uu____4484))
in (FStar_TypeChecker_Util.label uu____4483 sort_range haseq_b))
in (FStar_Syntax_Util.mk_conj t haseq_b))))) FStar_Syntax_Util.t_true dbs)
in (FStar_List.fold_right (fun b t -> (

let uu____4489 = (

let uu____4490 = (

let uu____4491 = (

let uu____4492 = (

let uu____4493 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____4493 None))
in (FStar_Syntax_Syntax.as_arg uu____4492))
in (uu____4491)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____4490))
in (uu____4489 None dr))) dbs cond)))))
end
| uu____4510 -> begin
FStar_Syntax_Util.t_true
end)))))
in (

let cond = (FStar_List.fold_left (fun acc d -> (

let uu____4514 = (haseq_data d)
in (FStar_Syntax_Util.mk_conj acc uu____4514))) FStar_Syntax_Util.t_true t_datas)
in (

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (

let uu____4516 = (FStar_Syntax_Util.mk_conj guard' guard)
in (

let uu____4519 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml)))::[]))), (env), (uu____4516), (uu____4519))))))))))
end)))))))))))))))
end))))
end)))
in (

let us = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____4537, us, uu____4539, uu____4540, uu____4541, uu____4542, uu____4543, uu____4544) -> begin
us
end
| uu____4551 -> begin
(failwith "Impossible!")
end))
in (

let uu____4552 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____4552) with
| (usubst, us) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq");
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle);
(

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let uu____4568 = (FStar_List.fold_left (haseq_ty usubst us) (([]), (env), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (uu____4568) with
| (axioms, env, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let uu____4600 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env phi)
in (match (uu____4600) with
| (phi, uu____4605) -> begin
((

let uu____4607 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____4607) with
| true -> begin
(

let uu____4608 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi)))
in (FStar_TypeChecker_Rel.force_trivial_guard env uu____4608))
end
| uu____4609 -> begin
()
end));
(

let ses = (FStar_List.fold_left (fun l uu____4616 -> (match (uu____4616) with
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

let unoptimized_haseq_scheme = (fun uu____4629 -> (

let mutuals = (FStar_List.map (fun ty -> (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____4635, uu____4636, uu____4637, uu____4638, uu____4639, uu____4640, uu____4641) -> begin
lid
end
| uu____4648 -> begin
(failwith "Impossible!")
end)) tcs)
in (

let haseq_ty = (fun usubst us acc ty -> (

let uu____4668 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____4680, bs, t, uu____4683, d_lids, uu____4685, uu____4686) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____4694 -> begin
(failwith "Impossible!")
end)
in (match (uu____4668) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (

let uu____4710 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst uu____4710 t))
in (

let uu____4717 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____4717) with
| (bs, t) -> begin
(

let ibs = (

let uu____4728 = (

let uu____4729 = (FStar_Syntax_Subst.compress t)
in uu____4729.FStar_Syntax_Syntax.n)
in (match (uu____4728) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____4736) -> begin
ibs
end
| uu____4747 -> begin
[]
end))
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (

let uu____4752 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____4753 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____4752 uu____4753)))
in (

let ind = (

let uu____4758 = (

let uu____4759 = (FStar_List.map (fun uu____4764 -> (match (uu____4764) with
| (bv, aq) -> begin
(

let uu____4771 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____4771), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____4759))
in (uu____4758 None dr))
in (

let ind = (

let uu____4779 = (

let uu____4780 = (FStar_List.map (fun uu____4785 -> (match (uu____4785) with
| (bv, aq) -> begin
(

let uu____4792 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((uu____4792), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind uu____4780))
in (uu____4779 None dr))
in (

let haseq_ind = (

let uu____4800 = (

let uu____4801 = (

let uu____4802 = (FStar_Syntax_Syntax.as_arg ind)
in (uu____4802)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____4801))
in (uu____4800 None dr))
in (

let rec is_mutual = (fun t -> (

let uu____4817 = (

let uu____4818 = (FStar_Syntax_Subst.compress t)
in uu____4818.FStar_Syntax_Syntax.n)
in (match (uu____4817) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.existsb (fun lid -> (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) mutuals)
end
| FStar_Syntax_Syntax.Tm_uinst (t', uu____4828) -> begin
(is_mutual t')
end
| FStar_Syntax_Syntax.Tm_refine (bv, t') -> begin
(is_mutual bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_app (t', args) -> begin
(

let uu____4855 = (is_mutual t')
in (match (uu____4855) with
| true -> begin
true
end
| uu____4856 -> begin
(

let uu____4857 = (FStar_List.map Prims.fst args)
in (exists_mutual uu____4857))
end))
end
| FStar_Syntax_Syntax.Tm_meta (t', uu____4870) -> begin
(is_mutual t')
end
| uu____4875 -> begin
false
end)))
and exists_mutual = (fun uu___89_4876 -> (match (uu___89_4876) with
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

let uu____4902 = (

let uu____4903 = (FStar_Syntax_Subst.compress dt)
in uu____4903.FStar_Syntax_Syntax.n)
in (match (uu____4902) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____4909) -> begin
(

let dbs = (

let uu____4924 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd uu____4924))
in (

let dbs = (

let uu____4946 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders uu____4946 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let sort = (Prims.fst b).FStar_Syntax_Syntax.sort
in (

let haseq_sort = (

let uu____4958 = (

let uu____4959 = (

let uu____4960 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (uu____4960)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq uu____4959))
in (uu____4958 None dr))
in (

let haseq_sort = (

let uu____4966 = (is_mutual sort)
in (match (uu____4966) with
| true -> begin
(FStar_Syntax_Util.mk_imp haseq_ind haseq_sort)
end
| uu____4967 -> begin
haseq_sort
end))
in (FStar_Syntax_Util.mk_conj t haseq_sort))))) FStar_Syntax_Util.t_true dbs)
in (

let cond = (FStar_List.fold_right (fun b t -> (

let uu____4973 = (

let uu____4974 = (

let uu____4975 = (

let uu____4976 = (

let uu____4977 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____4977 None))
in (FStar_Syntax_Syntax.as_arg uu____4976))
in (uu____4975)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____4974))
in (uu____4973 None dr))) dbs cond)
in (FStar_Syntax_Util.mk_conj acc cond))))))
end
| uu____4994 -> begin
acc
end)))))
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (uu____4998, uu____4999, uu____5000, t_lid, uu____5002, uu____5003, uu____5004, uu____5005) -> begin
(t_lid = lid)
end
| uu____5010 -> begin
(failwith "Impossible")
end)) datas)
in (

let data_cond = (FStar_List.fold_left haseq_data FStar_Syntax_Util.t_true t_datas)
in (

let fml = (FStar_Syntax_Util.mk_imp data_cond haseq_ind)
in (

let fml = (

let uu___109_5016 = fml
in (

let uu____5017 = (

let uu____5018 = (

let uu____5023 = (

let uu____5024 = (

let uu____5031 = (

let uu____5033 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (uu____5033)::[])
in (uu____5031)::[])
in FStar_Syntax_Syntax.Meta_pattern (uu____5024))
in ((fml), (uu____5023)))
in FStar_Syntax_Syntax.Tm_meta (uu____5018))
in {FStar_Syntax_Syntax.n = uu____5017; FStar_Syntax_Syntax.tk = uu___109_5016.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___109_5016.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___109_5016.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (

let uu____5045 = (

let uu____5046 = (

let uu____5047 = (

let uu____5048 = (

let uu____5049 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____5049 None))
in (FStar_Syntax_Syntax.as_arg uu____5048))
in (uu____5047)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____5046))
in (uu____5045 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (

let uu____5071 = (

let uu____5072 = (

let uu____5073 = (

let uu____5074 = (

let uu____5075 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) uu____5075 None))
in (FStar_Syntax_Syntax.as_arg uu____5074))
in (uu____5073)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall uu____5072))
in (uu____5071 None dr))) bs fml)
in (FStar_Syntax_Util.mk_conj acc fml)))))))))))))))
end))))
end)))
in (

let uu____5092 = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, uu____5100, uu____5101, uu____5102, uu____5103, uu____5104, uu____5105) -> begin
((lid), (us))
end
| uu____5112 -> begin
(failwith "Impossible!")
end))
in (match (uu____5092) with
| (lid, us) -> begin
(

let uu____5118 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____5118) with
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

let uu____5136 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (tc_assume env uu____5136 fml [] dr))
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq");
(se)::[];
)));
)))
end))
end)))))
in (

let skip_prims_type = (fun uu____5141 -> (

let lid = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____5145, uu____5146, uu____5147, uu____5148, uu____5149, uu____5150, uu____5151) -> begin
lid
end
| uu____5158 -> begin
(failwith "Impossible")
end))
in (

let types_to_skip = ("c_False")::("c_True")::("equals")::("h_equals")::("c_and")::("c_or")::[]
in (FStar_List.existsb (fun s -> (s = lid.FStar_Ident.ident.FStar_Ident.idText)) types_to_skip))))
in (

let is_noeq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Noeq)) quals)
in (

let uu____5164 = ((((FStar_List.length tcs) = (Prims.parse_int "0")) || ((FStar_Ident.lid_equals env.FStar_TypeChecker_Env.curmodule FStar_Syntax_Const.prims_lid) && (skip_prims_type ()))) || is_noeq)
in (match (uu____5164) with
| true -> begin
(((sig_bndle)::[]), (data_ops_ses))
end
| uu____5173 -> begin
(

let is_unopteq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Unopteq)) quals)
in (

let ses = (match (is_unopteq) with
| true -> begin
(unoptimized_haseq_scheme ())
end
| uu____5179 -> begin
(optimized_haseq_scheme ())
end)
in (

let uu____5180 = (

let uu____5182 = (

let uu____5183 = (

let uu____5191 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (uu____5191)))
in FStar_Syntax_Syntax.Sig_bundle (uu____5183))
in (uu____5182)::ses)
in ((uu____5180), (data_ops_ses)))))
end))))))))))
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

let uu____5231 = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (uu____5231), ([])))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let uu____5245 = (tc_inductive env ses quals lids)
in (match (uu____5245) with
| (ses, projectors_ses) -> begin
(

let env = (FStar_List.fold_left (fun env' se -> (FStar_TypeChecker_Env.push_sigelt env' se)) env ses)
in ((ses), (env), (projectors_ses)))
end)))
end
| FStar_Syntax_Syntax.Sig_pragma (p, r) -> begin
(

let set_options = (fun t s -> (

let uu____5275 = (FStar_Options.set_options t s)
in (match (uu____5275) with
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
| uu____5283 -> begin
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

let uu____5293 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____5293 Prims.ignore));
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
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____5299) -> begin
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

let uu____5312 = (FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun uu____5323 a -> (match (uu____5323) with
| (env, ses) -> begin
(

let se_let = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a)
in (

let uu____5336 = (FStar_TypeChecker_Env.push_sigelt env se_let)
in ((uu____5336), ((se_let)::ses))))
end)) ((env), ((se)::[]))))
in (match (uu____5312) with
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

let uu____5354 = (

let uu____5359 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source uu____5359))
in (match (uu____5354) with
| (a, wp_a_src) -> begin
(

let uu____5371 = (

let uu____5376 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target uu____5376))
in (match (uu____5371) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (

let uu____5389 = (

let uu____5391 = (

let uu____5392 = (

let uu____5397 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (uu____5397)))
in FStar_Syntax_Syntax.NT (uu____5392))
in (uu____5391)::[])
in (FStar_Syntax_Subst.subst uu____5389 wp_b_tgt))
in (

let expected_k = (

let uu____5401 = (

let uu____5405 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____5406 = (

let uu____5408 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (uu____5408)::[])
in (uu____5405)::uu____5406))
in (

let uu____5409 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow uu____5401 uu____5409)))
in (

let repr_type = (fun eff_name a wp -> (

let no_reify = (fun l -> (

let uu____5430 = (

let uu____5431 = (

let uu____5434 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (

let uu____5435 = (FStar_TypeChecker_Env.get_range env)
in ((uu____5434), (uu____5435))))
in FStar_Errors.Error (uu____5431))
in (Prims.raise uu____5430)))
in (

let uu____5438 = (FStar_TypeChecker_Env.effect_decl_opt env eff_name)
in (match (uu____5438) with
| None -> begin
(no_reify eff_name)
end
| Some (ed) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((FStar_Syntax_Syntax.U_unknown)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let uu____5445 = (

let uu____5446 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (not (uu____5446)))
in (match (uu____5445) with
| true -> begin
(no_reify eff_name)
end
| uu____5450 -> begin
(

let uu____5451 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____5452 = (

let uu____5455 = (

let uu____5456 = (

let uu____5466 = (

let uu____5468 = (FStar_Syntax_Syntax.as_arg a)
in (

let uu____5469 = (

let uu____5471 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____5471)::[])
in (uu____5468)::uu____5469))
in ((repr), (uu____5466)))
in FStar_Syntax_Syntax.Tm_app (uu____5456))
in (FStar_Syntax_Syntax.mk uu____5455))
in (uu____5452 None uu____5451)))
end)))
end))))
in (

let uu____5481 = (match (((sub.FStar_Syntax_Syntax.lift), (sub.FStar_Syntax_Syntax.lift_wp))) with
| (None, None) -> begin
(failwith "Impossible")
end
| (lift, Some (uu____5496, lift_wp)) -> begin
(

let uu____5509 = (check_and_gen env lift_wp expected_k)
in ((lift), (uu____5509)))
end
| (Some (what, lift), None) -> begin
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange))
in (

let uu____5524 = (FStar_TypeChecker_DMFF.star_expr dmff_env lift)
in (match (uu____5524) with
| (uu____5531, lift_wp, lift_elab) -> begin
(

let uu____5534 = (recheck_debug "lift-wp" env lift_wp)
in (

let uu____5535 = (recheck_debug "lift-elab" env lift_elab)
in ((Some ((([]), (lift_elab)))), ((([]), (lift_wp))))))
end)))
end)
in (match (uu____5481) with
| (lift, lift_wp) -> begin
(

let lax = env.FStar_TypeChecker_Env.lax
in (

let env = (

let uu___110_5559 = env
in {FStar_TypeChecker_Env.solver = uu___110_5559.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___110_5559.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___110_5559.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___110_5559.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___110_5559.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___110_5559.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___110_5559.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___110_5559.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___110_5559.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___110_5559.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___110_5559.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___110_5559.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___110_5559.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___110_5559.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___110_5559.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___110_5559.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___110_5559.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___110_5559.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___110_5559.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___110_5559.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___110_5559.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___110_5559.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___110_5559.FStar_TypeChecker_Env.qname_and_index})
in (

let lift = (match (lift) with
| None -> begin
None
end
| Some (uu____5563, lift) -> begin
(

let uu____5570 = (

let uu____5575 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source uu____5575))
in (match (uu____5570) with
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

let uu____5597 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____5598 = (

let uu____5601 = (

let uu____5602 = (

let uu____5612 = (

let uu____5614 = (FStar_Syntax_Syntax.as_arg a_typ)
in (

let uu____5615 = (

let uu____5617 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (uu____5617)::[])
in (uu____5614)::uu____5615))
in ((lift_wp), (uu____5612)))
in FStar_Syntax_Syntax.Tm_app (uu____5602))
in (FStar_Syntax_Syntax.mk uu____5601))
in (uu____5598 None uu____5597)))
in (repr_type sub.FStar_Syntax_Syntax.target a_typ lift_wp_a)))
in (

let expected_k = (

let uu____5630 = (

let uu____5634 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____5635 = (

let uu____5637 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (

let uu____5638 = (

let uu____5640 = (FStar_Syntax_Syntax.null_binder repr_f)
in (uu____5640)::[])
in (uu____5637)::uu____5638))
in (uu____5634)::uu____5635))
in (

let uu____5641 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow uu____5630 uu____5641)))
in (

let uu____5644 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (uu____5644) with
| (expected_k, uu____5650, uu____5651) -> begin
(

let lift = (check_and_gen env lift expected_k)
in Some (lift))
end))))))))
end))
end)
in (

let env = (

let uu___111_5654 = env
in {FStar_TypeChecker_Env.solver = uu___111_5654.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___111_5654.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___111_5654.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___111_5654.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___111_5654.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___111_5654.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___111_5654.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___111_5654.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___111_5654.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___111_5654.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___111_5654.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___111_5654.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___111_5654.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___111_5654.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___111_5654.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___111_5654.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___111_5654.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___111_5654.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = lax; FStar_TypeChecker_Env.lax_universes = uu___111_5654.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___111_5654.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___111_5654.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___111_5654.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___111_5654.FStar_TypeChecker_Env.qname_and_index})
in (

let sub = (

let uu___112_5656 = sub
in {FStar_Syntax_Syntax.source = uu___112_5656.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = uu___112_5656.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = Some (lift_wp); FStar_Syntax_Syntax.lift = lift})
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

let uu____5675 = (FStar_Syntax_Subst.open_comp tps c)
in (match (uu____5675) with
| (tps, c) -> begin
(

let uu____5685 = (tc_tparams env tps)
in (match (uu____5685) with
| (tps, env, us) -> begin
(

let uu____5697 = (FStar_TypeChecker_TcTerm.tc_comp env c)
in (match (uu____5697) with
| (c, u, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
(

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

let uu____5712 = (

let uu____5713 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 uu____5713))
in (match (uu____5712) with
| (uvs, t) -> begin
(

let uu____5727 = (

let uu____5735 = (

let uu____5738 = (

let uu____5739 = (FStar_Syntax_Subst.compress t)
in uu____5739.FStar_Syntax_Syntax.n)
in ((tps), (uu____5738)))
in (match (uu____5735) with
| ([], FStar_Syntax_Syntax.Tm_arrow (uu____5749, c)) -> begin
(([]), (c))
end
| (uu____5773, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
((tps), (c))
end
| uu____5791 -> begin
(failwith "Impossible")
end))
in (match (uu____5727) with
| (tps, c) -> begin
((match ((((FStar_List.length uvs) <> (Prims.parse_int "1")) && (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))))) with
| true -> begin
(

let uu____5821 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____5821) with
| (uu____5824, t) -> begin
(

let uu____5826 = (

let uu____5827 = (

let uu____5830 = (

let uu____5831 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____5832 = (FStar_All.pipe_right (FStar_List.length uvs) FStar_Util.string_of_int)
in (

let uu____5835 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)" uu____5831 uu____5832 uu____5835))))
in ((uu____5830), (r)))
in FStar_Errors.Error (uu____5827))
in (Prims.raise uu____5826))
end))
end
| uu____5836 -> begin
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
| (FStar_Syntax_Syntax.Sig_declare_typ (_, _, _, quals, _)) | (FStar_Syntax_Syntax.Sig_let (_, _, _, quals, _)) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___90_5865 -> (match (uu___90_5865) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____5866 -> begin
false
end)))) -> begin
(([]), (env), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t, quals, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let uu____5877 = (match ((uvs = [])) with
| true -> begin
(

let uu____5878 = (

let uu____5879 = (FStar_Syntax_Util.type_u ())
in (Prims.fst uu____5879))
in (check_and_gen env t uu____5878))
end
| uu____5882 -> begin
(

let uu____5883 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____5883) with
| (uvs, t) -> begin
(

let uu____5888 = (

let uu____5889 = (

let uu____5890 = (

let uu____5891 = (FStar_Syntax_Util.type_u ())
in (Prims.fst uu____5891))
in (tc_check_trivial_guard env t uu____5890))
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) uu____5889))
in ((uvs), (uu____5888)))
end))
end)
in (match (uu____5877) with
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

let uu____5923 = (FStar_TypeChecker_TcTerm.tc_term env e)
in (match (uu____5923) with
| (e, c, g1) -> begin
(

let uu____5935 = (

let uu____5939 = (

let uu____5941 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (uu____5941))
in (

let uu____5942 = (

let uu____5945 = (c.FStar_Syntax_Syntax.comp ())
in ((e), (uu____5945)))
in (FStar_TypeChecker_TcTerm.check_expected_effect env uu____5939 uu____5942)))
in (match (uu____5935) with
| (e, uu____5956, g) -> begin
((

let uu____5959 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env uu____5959));
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

let uu____6001 = (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q'))
in (match (uu____6001) with
| true -> begin
Some (q)
end
| uu____6009 -> begin
(

let uu____6010 = (

let uu____6011 = (

let uu____6014 = (

let uu____6015 = (FStar_Syntax_Print.lid_to_string l)
in (

let uu____6016 = (FStar_Syntax_Print.quals_to_string q)
in (

let uu____6017 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" uu____6015 uu____6016 uu____6017))))
in ((uu____6014), (r)))
in FStar_Errors.Error (uu____6011))
in (Prims.raise uu____6010))
end))
end))
in (

let uu____6020 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun uu____6041 lb -> (match (uu____6041) with
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____6065 = (

let uu____6071 = (FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____6071) with
| None -> begin
(match ((lb.FStar_Syntax_Syntax.lbunivs <> [])) with
| true -> begin
((false), (lb), (quals_opt))
end
| uu____6096 -> begin
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
| uu____6123 -> begin
(FStar_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end);
(match (((lb.FStar_Syntax_Syntax.lbunivs <> []) && ((FStar_List.length lb.FStar_Syntax_Syntax.lbunivs) <> (FStar_List.length uvs)))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Inline universes are incoherent with annotation from val declaration"), (r)))))
end
| uu____6130 -> begin
()
end);
(

let uu____6131 = (FStar_Syntax_Syntax.mk_lb ((FStar_Util.Inr (lbname)), (uvs), (FStar_Syntax_Const.effect_ALL_lid), (tval), (lb.FStar_Syntax_Syntax.lbdef)))
in ((false), (uu____6131), (quals_opt)));
))
end))
in (match (uu____6065) with
| (gen, lb, quals_opt) -> begin
((gen), ((lb)::lbs), (quals_opt))
end)))
end)) ((true), ([]), ((match ((quals = [])) with
| true -> begin
None
end
| uu____6162 -> begin
Some (quals)
end)))))
in (match (uu____6020) with
| (should_generalize, lbs', quals_opt) -> begin
(

let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Visible_default)::[]
end
| Some (q) -> begin
(

let uu____6185 = (FStar_All.pipe_right q (FStar_Util.for_some (fun uu___91_6187 -> (match (uu___91_6187) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Visible_default) | (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> begin
true
end
| uu____6188 -> begin
false
end))))
in (match (uu____6185) with
| true -> begin
q
end
| uu____6190 -> begin
(FStar_Syntax_Syntax.Visible_default)::q
end))
end)
in (

let lbs' = (FStar_List.rev lbs')
in (

let e = (

let uu____6196 = (

let uu____6199 = (

let uu____6200 = (

let uu____6208 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((((Prims.fst lbs)), (lbs'))), (uu____6208)))
in FStar_Syntax_Syntax.Tm_let (uu____6200))
in (FStar_Syntax_Syntax.mk uu____6199))
in (uu____6196 None r))
in (

let uu____6230 = (

let uu____6236 = (FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term (

let uu___113_6240 = env
in {FStar_TypeChecker_Env.solver = uu___113_6240.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___113_6240.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___113_6240.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___113_6240.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___113_6240.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___113_6240.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___113_6240.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___113_6240.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___113_6240.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___113_6240.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___113_6240.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = uu___113_6240.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = uu___113_6240.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___113_6240.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___113_6240.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___113_6240.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___113_6240.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___113_6240.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___113_6240.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___113_6240.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___113_6240.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___113_6240.FStar_TypeChecker_Env.qname_and_index}) e)
in (match (uu____6236) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = uu____6248; FStar_Syntax_Syntax.pos = uu____6249; FStar_Syntax_Syntax.vars = uu____6250}, uu____6251, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (uu____6270, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| uu____6275 -> begin
quals
end)
in ((FStar_Syntax_Syntax.Sig_let (((lbs), (r), (lids), (quals), (attrs)))), (lbs)))
end
| uu____6285 -> begin
(failwith "impossible")
end))
in (match (uu____6230) with
| (se, lbs) -> begin
((

let uu____6308 = (log env)
in (match (uu____6308) with
| true -> begin
(

let uu____6309 = (

let uu____6310 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (

let uu____6317 = (

let uu____6322 = (

let uu____6323 = (

let uu____6328 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____6328.FStar_Syntax_Syntax.fv_name)
in uu____6323.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env uu____6322))
in (match (uu____6317) with
| None -> begin
true
end
| uu____6335 -> begin
false
end))
in (match (should_log) with
| true -> begin
(

let uu____6340 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____6341 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" uu____6340 uu____6341)))
end
| uu____6342 -> begin
""
end)))))
in (FStar_All.pipe_right uu____6310 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" uu____6309))
end
| uu____6344 -> begin
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

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___92_6371 -> (match (uu___92_6371) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| uu____6372 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| uu____6380 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (uu____6385) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, uu____6398, r) -> begin
(

let uu____6406 = (is_abstract quals)
in (match (uu____6406) with
| true -> begin
(FStar_List.fold_right (fun se uu____6416 -> (match (uu____6416) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, uu____6439, uu____6440, quals, r) -> begin
(

let dec = (

let uu____6450 = (

let uu____6457 = (

let uu____6460 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow bs uu____6460))
in ((l), (us), (uu____6457), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____6450))
in (((dec)::out), (hidden)))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, uu____6471, uu____6472, uu____6473, uu____6474, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]), (r)))
in (((dec)::out), ((l)::hidden)))
end
| uu____6484 -> begin
((out), (hidden))
end)
end)) ses (([]), (hidden)))
end
| uu____6489 -> begin
(((se)::[]), (hidden))
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____6492, uu____6493, quals, uu____6495) -> begin
(

let uu____6498 = (is_abstract quals)
in (match (uu____6498) with
| true -> begin
(([]), (hidden))
end
| uu____6505 -> begin
(((se)::[]), (hidden))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, us, t, quals, r) -> begin
(

let uu____6515 = (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc))
in (match (uu____6515) with
| true -> begin
(((FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]), (r))))::[]), ((l)::hidden))
end
| uu____6524 -> begin
(

let uu____6525 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___93_6527 -> (match (uu___93_6527) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| uu____6530 -> begin
false
end))))
in (match (uu____6525) with
| true -> begin
(((se)::[]), (hidden))
end
| uu____6537 -> begin
(([]), (hidden))
end))
end))
end
| FStar_Syntax_Syntax.Sig_main (uu____6540) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____6552, uu____6553, quals, uu____6555) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____6573 = (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
in (match (uu____6573) with
| true -> begin
(([]), (hidden))
end
| uu____6581 -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::[]), ((FStar_Ident.range_of_lid lid))))
in (((dec)::[]), ((lid)::hidden)))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals, uu____6597) -> begin
(

let uu____6604 = (is_abstract quals)
in (match (uu____6604) with
| true -> begin
(

let uu____6609 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let uu____6615 = (

let uu____6622 = (

let uu____6623 = (

let uu____6628 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____6628.FStar_Syntax_Syntax.fv_name)
in uu____6623.FStar_Syntax_Syntax.v)
in ((uu____6622), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____6615)))))
in ((uu____6609), (hidden)))
end
| uu____6638 -> begin
(((se)::[]), (hidden))
end))
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let rec process_one_decl = (fun uu____6675 se -> (match (uu____6675) with
| (ses, exports, env, hidden) -> begin
((

let uu____6706 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____6706) with
| true -> begin
(

let uu____6707 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____6707))
end
| uu____6708 -> begin
()
end));
(

let uu____6709 = (tc_decl env se)
in (match (uu____6709) with
| (ses', env, ses_elaborated) -> begin
((

let uu____6731 = ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes"))))
in (match (uu____6731) with
| true -> begin
(

let uu____6732 = (FStar_List.fold_left (fun s se -> (

let uu____6735 = (

let uu____6736 = (FStar_Syntax_Print.sigelt_to_string se)
in (Prims.strcat uu____6736 "\n"))
in (Prims.strcat s uu____6735))) "" ses')
in (FStar_Util.print1 "Checked: %s\n" uu____6732))
end
| uu____6737 -> begin
()
end));
(FStar_List.iter (fun se -> (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)) ses');
(

let uu____6740 = (FStar_List.fold_left (fun uu____6749 se -> (match (uu____6749) with
| (le, lh) -> begin
(

let tup = (for_export hidden se)
in (((FStar_List.rev_append (Prims.fst tup) le)), ((FStar_List.rev_append (Prims.snd tup) lh))))
end)) (([]), ([])) ses')
in (match (uu____6740) with
| (exported, hidden) -> begin
(FStar_List.fold_left process_one_decl (((FStar_List.rev_append ses' ses)), (((FStar_List.rev_append exported []))::exports), (env), (hidden)) ses_elaborated)
end));
)
end));
)
end))
in (

let uu____6805 = (FStar_List.fold_left (fun acc se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, r) -> begin
(

let uu____6842 = acc
in (match (uu____6842) with
| (uu____6859, uu____6860, env, uu____6862) -> begin
(

let uu____6871 = (cps_and_elaborate env ne)
in (match (uu____6871) with
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
| uu____6904 -> begin
(process_one_decl acc se)
end)) (([]), ([]), (env), ([])) ses)
in (match (uu____6805) with
| (ses, exports, env, uu____6918) -> begin
(

let uu____6927 = (FStar_All.pipe_right (FStar_List.rev_append exports []) FStar_List.flatten)
in (((FStar_List.rev_append ses [])), (uu____6927), (env)))
end))))


let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (

let verify = (FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let action = (match (verify) with
| true -> begin
"Verifying"
end
| uu____6948 -> begin
"Lax-checking"
end)
in (

let label = (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____6950 -> begin
"implementation"
end)
in ((

let uu____6952 = (FStar_Options.debug_any ())
in (match (uu____6952) with
| true -> begin
(FStar_Util.print3 "%s %s of %s\n" action label modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
end
| uu____6953 -> begin
()
end));
(

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____6955 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let msg = (Prims.strcat "Internals for " name)
in (

let env = (

let uu___114_6958 = env
in {FStar_TypeChecker_Env.solver = uu___114_6958.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___114_6958.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___114_6958.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___114_6958.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___114_6958.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___114_6958.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___114_6958.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___114_6958.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___114_6958.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___114_6958.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___114_6958.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___114_6958.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___114_6958.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___114_6958.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___114_6958.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___114_6958.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = (not (verify)); FStar_TypeChecker_Env.lax = uu___114_6958.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___114_6958.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___114_6958.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___114_6958.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___114_6958.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___114_6958.FStar_TypeChecker_Env.qname_and_index})
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg);
(

let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

let uu____6961 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (uu____6961) with
| (ses, exports, env) -> begin
(((

let uu___115_6979 = modul
in {FStar_Syntax_Syntax.name = uu___115_6979.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = uu___115_6979.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___115_6979.FStar_Syntax_Syntax.is_interface})), (exports), (env))
end)));
))));
)))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let uu____6995 = (tc_decls env decls)
in (match (uu____6995) with
| (ses, exports, env) -> begin
(

let modul = (

let uu___116_7013 = modul
in {FStar_Syntax_Syntax.name = uu___116_7013.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = uu___116_7013.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___116_7013.FStar_Syntax_Syntax.is_interface})
in ((modul), (exports), (env)))
end)))


let check_exports : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env modul exports -> (

let env = (

let uu___117_7027 = env
in {FStar_TypeChecker_Env.solver = uu___117_7027.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___117_7027.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___117_7027.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___117_7027.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___117_7027.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___117_7027.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___117_7027.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___117_7027.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___117_7027.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___117_7027.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___117_7027.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___117_7027.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___117_7027.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = uu___117_7027.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___117_7027.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___117_7027.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___117_7027.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = true; FStar_TypeChecker_Env.type_of = uu___117_7027.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___117_7027.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___117_7027.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___117_7027.FStar_TypeChecker_Env.qname_and_index})
in (

let check_term = (fun lid univs t -> (

let uu____7038 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (uu____7038) with
| (univs, t) -> begin
((

let uu____7044 = (

let uu____7045 = (

let uu____7048 = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (FStar_TypeChecker_Env.debug uu____7048))
in (FStar_All.pipe_left uu____7045 (FStar_Options.Other ("Exports"))))
in (match (uu____7044) with
| true -> begin
(

let uu____7049 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____7050 = (

let uu____7051 = (FStar_All.pipe_right univs (FStar_List.map (fun x -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (x))))))
in (FStar_All.pipe_right uu____7051 (FStar_String.concat ", ")))
in (

let uu____7056 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print3 "Checking for export %s <%s> : %s\n" uu____7049 uu____7050 uu____7056))))
end
| uu____7057 -> begin
()
end));
(

let env = (FStar_TypeChecker_Env.push_univ_vars env univs)
in (

let uu____7059 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env t)
in (FStar_All.pipe_right uu____7059 Prims.ignore)));
)
end)))
in (

let check_term = (fun lid univs t -> ((

let uu____7077 = (

let uu____7078 = (FStar_Syntax_Print.lid_to_string modul.FStar_Syntax_Syntax.name)
in (

let uu____7079 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Interface of %s violates its abstraction (add a \'private\' qualifier to \'%s\'?)" uu____7078 uu____7079)))
in (FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____7077));
(check_term lid univs t);
(FStar_Errors.message_prefix.FStar_Errors.clear_prefix ());
))
in (

let rec check_sigelt = (fun uu___94_7084 -> (match (uu___94_7084) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, uu____7087, uu____7088) -> begin
(

let uu____7095 = (

let uu____7096 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____7096)))
in (match (uu____7095) with
| true -> begin
(FStar_All.pipe_right ses (FStar_List.iter check_sigelt))
end
| uu____7099 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (l, univs, binders, typ, uu____7104, uu____7105, uu____7106, r) -> begin
(

let t = (

let uu____7117 = (

let uu____7120 = (

let uu____7121 = (

let uu____7129 = (FStar_Syntax_Syntax.mk_Total typ)
in ((binders), (uu____7129)))
in FStar_Syntax_Syntax.Tm_arrow (uu____7121))
in (FStar_Syntax_Syntax.mk uu____7120))
in (uu____7117 None r))
in (check_term l univs t))
end
| FStar_Syntax_Syntax.Sig_datacon (l, univs, t, uu____7141, uu____7142, uu____7143, uu____7144, uu____7145) -> begin
(check_term l univs t)
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, univs, t, quals, uu____7154) -> begin
(

let uu____7157 = (

let uu____7158 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____7158)))
in (match (uu____7157) with
| true -> begin
(check_term l univs t)
end
| uu____7160 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_let ((uu____7161, lbs), uu____7163, uu____7164, quals, uu____7166) -> begin
(

let uu____7178 = (

let uu____7179 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____7179)))
in (match (uu____7178) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (check_term fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp)))))
end
| uu____7188 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, binders, comp, quals, flags, r) -> begin
(

let uu____7200 = (

let uu____7201 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____7201)))
in (match (uu____7200) with
| true -> begin
(

let arrow = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp))))) None r)
in (check_term l univs arrow))
end
| uu____7214 -> begin
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
| uu____7221 -> begin
(FStar_List.iter check_sigelt exports)
end))))))


let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (

let modul = (

let uu___118_7234 = modul
in {FStar_Syntax_Syntax.name = uu___118_7234.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu___118_7234.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module env modul)
in ((

let uu____7237 = (

let uu____7238 = (FStar_Options.lax ())
in (not (uu____7238)))
in (match (uu____7237) with
| true -> begin
(check_exports env modul exports)
end
| uu____7239 -> begin
()
end));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul);
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
(

let uu____7244 = (

let uu____7245 = (FStar_Options.interactive ())
in (not (uu____7245)))
in (match (uu____7244) with
| true -> begin
(

let uu____7246 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right uu____7246 Prims.ignore))
end
| uu____7247 -> begin
()
end));
((modul), (env));
))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let uu____7256 = (tc_partial_modul env modul)
in (match (uu____7256) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> ((

let uu____7277 = (FStar_Options.debug_any ())
in (match (uu____7277) with
| true -> begin
(

let uu____7278 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (match (m.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"i\'face"
end
| uu____7279 -> begin
"module"
end) uu____7278))
end
| uu____7280 -> begin
()
end));
(

let env = (

let uu___119_7282 = env
in (

let uu____7283 = (

let uu____7284 = (FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (not (uu____7284)))
in {FStar_TypeChecker_Env.solver = uu___119_7282.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___119_7282.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___119_7282.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___119_7282.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___119_7282.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___119_7282.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___119_7282.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___119_7282.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___119_7282.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___119_7282.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___119_7282.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___119_7282.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___119_7282.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___119_7282.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___119_7282.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___119_7282.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___119_7282.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___119_7282.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu____7283; FStar_TypeChecker_Env.lax_universes = uu___119_7282.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___119_7282.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___119_7282.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___119_7282.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___119_7282.FStar_TypeChecker_Env.qname_and_index}))
in (

let uu____7285 = (tc_modul env m)
in (match (uu____7285) with
| (m, env) -> begin
((

let uu____7293 = (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____7293) with
| true -> begin
(

let uu____7294 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" uu____7294))
end
| uu____7295 -> begin
()
end));
(

let uu____7297 = ((FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) && (FStar_Options.debug_at_level m.FStar_Syntax_Syntax.name.FStar_Ident.str (FStar_Options.Other ("Normalize"))))
in (match (uu____7297) with
| true -> begin
(

let normalize_toplevel_lets = (fun uu___95_7301 -> (match (uu___95_7301) with
| FStar_Syntax_Syntax.Sig_let ((b, lbs), r, ids, qs, attrs) -> begin
(

let n = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]))
in (

let update = (fun lb -> (

let uu____7328 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____7328) with
| (univnames, e) -> begin
(

let uu___120_7333 = lb
in (

let uu____7334 = (

let uu____7337 = (FStar_TypeChecker_Env.push_univ_vars env univnames)
in (n uu____7337 e))
in {FStar_Syntax_Syntax.lbname = uu___120_7333.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___120_7333.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___120_7333.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___120_7333.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____7334}))
end)))
in (

let uu____7338 = (

let uu____7347 = (

let uu____7351 = (FStar_List.map update lbs)
in ((b), (uu____7351)))
in ((uu____7347), (r), (ids), (qs), (attrs)))
in FStar_Syntax_Syntax.Sig_let (uu____7338))))
end
| se -> begin
se
end))
in (

let normalized_module = (

let uu___121_7362 = m
in (

let uu____7363 = (FStar_List.map normalize_toplevel_lets m.FStar_Syntax_Syntax.declarations)
in {FStar_Syntax_Syntax.name = uu___121_7362.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu____7363; FStar_Syntax_Syntax.exports = uu___121_7362.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___121_7362.FStar_Syntax_Syntax.is_interface}))
in (

let uu____7364 = (FStar_Syntax_Print.modul_to_string normalized_module)
in (FStar_Util.print1 "%s\n" uu____7364))))
end
| uu____7365 -> begin
()
end));
((m), (env));
)
end)));
))




