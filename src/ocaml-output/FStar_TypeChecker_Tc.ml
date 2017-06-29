
open Prims
open FStar_Pervasives

let set_hint_correlator : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env = (fun env se -> (

let uu____9 = (FStar_Options.reuse_hint_for ())
in (match (uu____9) with
| FStar_Pervasives_Native.Some (l) -> begin
(

let lid = (

let uu____13 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_add_suffix uu____13 l))
in (

let uu___91_14 = env
in {FStar_TypeChecker_Env.solver = uu___91_14.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___91_14.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___91_14.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___91_14.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___91_14.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___91_14.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___91_14.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___91_14.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___91_14.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___91_14.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___91_14.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___91_14.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___91_14.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___91_14.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___91_14.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___91_14.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___91_14.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___91_14.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___91_14.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___91_14.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___91_14.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___91_14.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___91_14.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = FStar_Pervasives_Native.Some (((lid), ((Prims.parse_int "0")))); FStar_TypeChecker_Env.proof_ns = uu___91_14.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___91_14.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___91_14.FStar_TypeChecker_Env.is_native_tactic}))
end
| FStar_Pervasives_Native.None -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (

let lid = (match (lids) with
| [] -> begin
(

let uu____20 = (FStar_TypeChecker_Env.current_module env)
in (

let uu____21 = (

let uu____22 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_right uu____22 FStar_Util.string_of_int))
in (FStar_Ident.lid_add_suffix uu____20 uu____21)))
end
| (l)::uu____24 -> begin
l
end)
in (

let uu___92_26 = env
in {FStar_TypeChecker_Env.solver = uu___92_26.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___92_26.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___92_26.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___92_26.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___92_26.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___92_26.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___92_26.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___92_26.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___92_26.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___92_26.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___92_26.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___92_26.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___92_26.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___92_26.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___92_26.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___92_26.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___92_26.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___92_26.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___92_26.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___92_26.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___92_26.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___92_26.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___92_26.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = FStar_Pervasives_Native.Some (((lid), ((Prims.parse_int "0")))); FStar_TypeChecker_Env.proof_ns = uu___92_26.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___92_26.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___92_26.FStar_TypeChecker_Env.is_native_tactic})))
end)))


let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_Options.log_types ()) && (

let uu____34 = (

let uu____35 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____35))
in (not (uu____34)))))


let is_native_tactic : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env tac_lid h -> (match (h.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h', uu____49) -> begin
(

let uu____54 = (

let uu____55 = (FStar_Syntax_Subst.compress h')
in uu____55.FStar_Syntax_Syntax.n)
in (match (uu____54) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.tactic_lid) -> begin
(env.FStar_TypeChecker_Env.is_native_tactic tac_lid)
end
| uu____59 -> begin
false
end))
end
| uu____60 -> begin
false
end))


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let uu____73 = (FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k)
in (match (uu____73) with
| (t1, c, g) -> begin
((FStar_ST.write t1.FStar_Syntax_Syntax.tk (FStar_Pervasives_Native.Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)));
(FStar_TypeChecker_Rel.force_trivial_guard env g);
t1;
)
end)))


let recheck_debug : Prims.string  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s env t -> ((

let uu____98 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____98) with
| true -> begin
(

let uu____99 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Term has been %s-transformed to:\n%s\n----------\n" s uu____99))
end
| uu____100 -> begin
()
end));
(

let uu____101 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (uu____101) with
| (t', uu____106, uu____107) -> begin
((

let uu____109 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____109) with
| true -> begin
(

let uu____110 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print1 "Re-checked; got:\n%s\n----------\n" uu____110))
end
| uu____111 -> begin
()
end));
t;
)
end));
))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (

let uu____124 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env uu____124)))


let check_nogen = (fun env t k -> (

let t1 = (tc_check_trivial_guard env t k)
in (

let uu____150 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t1)
in (([]), (uu____150)))))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun env m s -> (

let fail = (fun uu____175 -> (

let uu____176 = (

let uu____177 = (

let uu____180 = (FStar_TypeChecker_Err.unexpected_signature_for_monad env m s)
in ((uu____180), ((FStar_Ident.range_of_lid m))))
in FStar_Errors.Error (uu____177))
in (FStar_Pervasives.raise uu____176)))
in (

let s1 = (FStar_Syntax_Subst.compress s)
in (match (s1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs1 = (FStar_Syntax_Subst.open_binders bs)
in (match (bs1) with
| ((a, uu____208))::((wp, uu____210))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____219 -> begin
(fail ())
end))
end
| uu____220 -> begin
(fail ())
end))))


let tc_eff_decl : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (

let uu____231 = (FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____231) with
| (effect_params_un, signature_un, opening) -> begin
(

let uu____238 = (FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un)
in (match (uu____238) with
| (effect_params, env, uu____244) -> begin
(

let uu____245 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (uu____245) with
| (signature, uu____249) -> begin
(

let ed1 = (

let uu___93_251 = ed
in {FStar_Syntax_Syntax.cattributes = uu___93_251.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___93_251.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___93_251.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = uu___93_251.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = uu___93_251.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = uu___93_251.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = uu___93_251.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = uu___93_251.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = uu___93_251.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = uu___93_251.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = uu___93_251.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = uu___93_251.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = uu___93_251.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = uu___93_251.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = uu___93_251.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = uu___93_251.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = uu___93_251.FStar_Syntax_Syntax.actions})
in (

let ed2 = (match (effect_params) with
| [] -> begin
ed1
end
| uu____255 -> begin
(

let op = (fun ts -> (

let t1 = (FStar_Syntax_Subst.subst opening (FStar_Pervasives_Native.snd ts))
in (([]), (t1))))
in (

let uu___94_274 = ed1
in (

let uu____275 = (op ed1.FStar_Syntax_Syntax.ret_wp)
in (

let uu____276 = (op ed1.FStar_Syntax_Syntax.bind_wp)
in (

let uu____277 = (op ed1.FStar_Syntax_Syntax.if_then_else)
in (

let uu____278 = (op ed1.FStar_Syntax_Syntax.ite_wp)
in (

let uu____279 = (op ed1.FStar_Syntax_Syntax.stronger)
in (

let uu____280 = (op ed1.FStar_Syntax_Syntax.close_wp)
in (

let uu____281 = (op ed1.FStar_Syntax_Syntax.assert_p)
in (

let uu____282 = (op ed1.FStar_Syntax_Syntax.assume_p)
in (

let uu____283 = (op ed1.FStar_Syntax_Syntax.null_wp)
in (

let uu____284 = (op ed1.FStar_Syntax_Syntax.trivial)
in (

let uu____285 = (

let uu____286 = (op (([]), (ed1.FStar_Syntax_Syntax.repr)))
in (FStar_Pervasives_Native.snd uu____286))
in (

let uu____292 = (op ed1.FStar_Syntax_Syntax.return_repr)
in (

let uu____293 = (op ed1.FStar_Syntax_Syntax.bind_repr)
in (

let uu____294 = (FStar_List.map (fun a -> (

let uu___95_301 = a
in (

let uu____302 = (

let uu____303 = (op (([]), (a.FStar_Syntax_Syntax.action_defn)))
in (FStar_Pervasives_Native.snd uu____303))
in (

let uu____309 = (

let uu____310 = (op (([]), (a.FStar_Syntax_Syntax.action_typ)))
in (FStar_Pervasives_Native.snd uu____310))
in {FStar_Syntax_Syntax.action_name = uu___95_301.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___95_301.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___95_301.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = uu___95_301.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = uu____302; FStar_Syntax_Syntax.action_typ = uu____309})))) ed1.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.cattributes = uu___94_274.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___94_274.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___94_274.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu___94_274.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = uu___94_274.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = uu____275; FStar_Syntax_Syntax.bind_wp = uu____276; FStar_Syntax_Syntax.if_then_else = uu____277; FStar_Syntax_Syntax.ite_wp = uu____278; FStar_Syntax_Syntax.stronger = uu____279; FStar_Syntax_Syntax.close_wp = uu____280; FStar_Syntax_Syntax.assert_p = uu____281; FStar_Syntax_Syntax.assume_p = uu____282; FStar_Syntax_Syntax.null_wp = uu____283; FStar_Syntax_Syntax.trivial = uu____284; FStar_Syntax_Syntax.repr = uu____285; FStar_Syntax_Syntax.return_repr = uu____292; FStar_Syntax_Syntax.bind_repr = uu____293; FStar_Syntax_Syntax.actions = uu____294}))))))))))))))))
end)
in (

let wp_with_fresh_result_type = (fun env1 mname signature1 -> (

let fail = (fun t -> (

let uu____338 = (

let uu____339 = (

let uu____342 = (FStar_TypeChecker_Err.unexpected_signature_for_monad env1 mname t)
in ((uu____342), ((FStar_Ident.range_of_lid mname))))
in FStar_Errors.Error (uu____339))
in (FStar_Pervasives.raise uu____338)))
in (

let uu____347 = (

let uu____348 = (FStar_Syntax_Subst.compress signature1)
in uu____348.FStar_Syntax_Syntax.n)
in (match (uu____347) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs1 = (FStar_Syntax_Subst.open_binders bs)
in (match (bs1) with
| ((a, uu____373))::((wp, uu____375))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____384 -> begin
(fail signature1)
end))
end
| uu____385 -> begin
(fail signature1)
end))))
in (

let uu____386 = (wp_with_fresh_result_type env ed2.FStar_Syntax_Syntax.mname ed2.FStar_Syntax_Syntax.signature)
in (match (uu____386) with
| (a, wp_a) -> begin
(

let fresh_effect_signature = (fun uu____404 -> (

let uu____405 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (uu____405) with
| (signature1, uu____413) -> begin
(wp_with_fresh_result_type env ed2.FStar_Syntax_Syntax.mname signature1)
end)))
in (

let env1 = (

let uu____415 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None ed2.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env uu____415))
in ((

let uu____417 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED")))
in (match (uu____417) with
| true -> begin
(

let uu____418 = (FStar_Syntax_Print.lid_to_string ed2.FStar_Syntax_Syntax.mname)
in (

let uu____419 = (FStar_Syntax_Print.binders_to_string " " ed2.FStar_Syntax_Syntax.binders)
in (

let uu____420 = (FStar_Syntax_Print.term_to_string ed2.FStar_Syntax_Syntax.signature)
in (

let uu____421 = (

let uu____422 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Print.term_to_string uu____422))
in (

let uu____423 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.sort)
in (FStar_Util.print5 "Checking effect signature: %s %s : %s\n(a is %s:%s)\n" uu____418 uu____419 uu____420 uu____421 uu____423))))))
end
| uu____424 -> begin
()
end));
(

let check_and_gen' = (fun env2 uu____436 k -> (match (uu____436) with
| (uu____441, t) -> begin
(check_and_gen env2 t k)
end))
in (

let return_wp = (

let expected_k = (

let uu____449 = (

let uu____453 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____454 = (

let uu____456 = (

let uu____457 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____457))
in (uu____456)::[])
in (uu____453)::uu____454))
in (

let uu____458 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow uu____449 uu____458)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.ret_wp expected_k))
in (

let bind_wp = (

let uu____462 = (fresh_effect_signature ())
in (match (uu____462) with
| (b, wp_b) -> begin
(

let a_wp_b = (

let uu____476 = (

let uu____480 = (

let uu____481 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____481))
in (uu____480)::[])
in (

let uu____482 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____476 uu____482)))
in (

let expected_k = (

let uu____488 = (

let uu____492 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (

let uu____493 = (

let uu____495 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____496 = (

let uu____498 = (FStar_Syntax_Syntax.mk_binder b)
in (

let uu____499 = (

let uu____501 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____502 = (

let uu____504 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (uu____504)::[])
in (uu____501)::uu____502))
in (uu____498)::uu____499))
in (uu____495)::uu____496))
in (uu____492)::uu____493))
in (

let uu____505 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____488 uu____505)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else1 = (

let p = (

let uu____510 = (

let uu____511 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____511 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some ((FStar_Ident.range_of_lid ed2.FStar_Syntax_Syntax.mname))) uu____510))
in (

let expected_k = (

let uu____519 = (

let uu____523 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____524 = (

let uu____526 = (FStar_Syntax_Syntax.mk_binder p)
in (

let uu____527 = (

let uu____529 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____530 = (

let uu____532 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____532)::[])
in (uu____529)::uu____530))
in (uu____526)::uu____527))
in (uu____523)::uu____524))
in (

let uu____533 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____519 uu____533)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (

let uu____540 = (

let uu____544 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____545 = (

let uu____547 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____547)::[])
in (uu____544)::uu____545))
in (

let uu____548 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____540 uu____548)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let uu____552 = (FStar_Syntax_Util.type_u ())
in (match (uu____552) with
| (t, uu____556) -> begin
(

let expected_k = (

let uu____560 = (

let uu____564 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____565 = (

let uu____567 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____568 = (

let uu____570 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____570)::[])
in (uu____567)::uu____568))
in (uu____564)::uu____565))
in (

let uu____571 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow uu____560 uu____571)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (

let uu____576 = (

let uu____577 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____577 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some ((FStar_Ident.range_of_lid ed2.FStar_Syntax_Syntax.mname))) uu____576))
in (

let b_wp_a = (

let uu____585 = (

let uu____589 = (

let uu____590 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder uu____590))
in (uu____589)::[])
in (

let uu____591 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____585 uu____591)))
in (

let expected_k = (

let uu____597 = (

let uu____601 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____602 = (

let uu____604 = (FStar_Syntax_Syntax.mk_binder b)
in (

let uu____605 = (

let uu____607 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (uu____607)::[])
in (uu____604)::uu____605))
in (uu____601)::uu____602))
in (

let uu____608 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____597 uu____608)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (

let uu____615 = (

let uu____619 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____620 = (

let uu____622 = (

let uu____623 = (

let uu____624 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____624 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.null_binder uu____623))
in (

let uu____629 = (

let uu____631 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____631)::[])
in (uu____622)::uu____629))
in (uu____619)::uu____620))
in (

let uu____632 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____615 uu____632)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (

let uu____639 = (

let uu____643 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____644 = (

let uu____646 = (

let uu____647 = (

let uu____648 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____648 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.null_binder uu____647))
in (

let uu____653 = (

let uu____655 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____655)::[])
in (uu____646)::uu____653))
in (uu____643)::uu____644))
in (

let uu____656 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____639 uu____656)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (

let uu____663 = (

let uu____667 = (FStar_Syntax_Syntax.mk_binder a)
in (uu____667)::[])
in (

let uu____668 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____663 uu____668)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let uu____672 = (FStar_Syntax_Util.type_u ())
in (match (uu____672) with
| (t, uu____676) -> begin
(

let expected_k = (

let uu____680 = (

let uu____684 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____685 = (

let uu____687 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____687)::[])
in (uu____684)::uu____685))
in (

let uu____688 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow uu____680 uu____688)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let uu____691 = (

let uu____697 = (

let uu____698 = (FStar_Syntax_Subst.compress ed2.FStar_Syntax_Syntax.repr)
in uu____698.FStar_Syntax_Syntax.n)
in (match (uu____697) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((ed2.FStar_Syntax_Syntax.repr), (ed2.FStar_Syntax_Syntax.bind_repr), (ed2.FStar_Syntax_Syntax.return_repr), (ed2.FStar_Syntax_Syntax.actions))
end
| uu____707 -> begin
(

let repr = (

let uu____709 = (FStar_Syntax_Util.type_u ())
in (match (uu____709) with
| (t, uu____713) -> begin
(

let expected_k = (

let uu____717 = (

let uu____721 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____722 = (

let uu____724 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____724)::[])
in (uu____721)::uu____722))
in (

let uu____725 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow uu____717 uu____725)))
in (tc_check_trivial_guard env1 ed2.FStar_Syntax_Syntax.repr expected_k))
end))
in (

let mk_repr' = (fun t wp -> (

let repr1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env1 repr)
in (

let uu____738 = (

let uu____741 = (

let uu____742 = (

let uu____752 = (

let uu____754 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____755 = (

let uu____757 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____757)::[])
in (uu____754)::uu____755))
in ((repr1), (uu____752)))
in FStar_Syntax_Syntax.Tm_app (uu____742))
in (FStar_Syntax_Syntax.mk uu____741))
in (uu____738 FStar_Pervasives_Native.None FStar_Range.dummyRange))))
in (

let mk_repr = (fun a1 wp -> (

let uu____776 = (FStar_Syntax_Syntax.bv_to_name a1)
in (mk_repr' uu____776 wp)))
in (

let destruct_repr = (fun t -> (

let uu____787 = (

let uu____788 = (FStar_Syntax_Subst.compress t)
in uu____788.FStar_Syntax_Syntax.n)
in (match (uu____787) with
| FStar_Syntax_Syntax.Tm_app (uu____797, ((t1, uu____799))::((wp, uu____801))::[]) -> begin
((t1), (wp))
end
| uu____835 -> begin
(failwith "Unexpected repr type")
end)))
in (

let bind_repr = (

let r = (

let uu____844 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.range_0 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_All.pipe_right uu____844 FStar_Syntax_Syntax.fv_to_tm))
in (

let uu____845 = (fresh_effect_signature ())
in (match (uu____845) with
| (b, wp_b) -> begin
(

let a_wp_b = (

let uu____859 = (

let uu____863 = (

let uu____864 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____864))
in (uu____863)::[])
in (

let uu____865 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____859 uu____865)))
in (

let wp_f = (FStar_Syntax_Syntax.gen_bv "wp_f" FStar_Pervasives_Native.None wp_a)
in (

let wp_g = (FStar_Syntax_Syntax.gen_bv "wp_g" FStar_Pervasives_Native.None a_wp_b)
in (

let x_a = (

let uu____871 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" FStar_Pervasives_Native.None uu____871))
in (

let wp_g_x = (

let uu____875 = (

let uu____876 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (

let uu____877 = (

let uu____878 = (

let uu____879 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____879))
in (uu____878)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____876 uu____877)))
in (uu____875 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let res = (

let wp = (

let uu____890 = (

let uu____891 = (

let uu____892 = (FStar_TypeChecker_Env.inst_tscheme bind_wp)
in (FStar_All.pipe_right uu____892 FStar_Pervasives_Native.snd))
in (

let uu____897 = (

let uu____898 = (

let uu____900 = (

let uu____902 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____903 = (

let uu____905 = (FStar_Syntax_Syntax.bv_to_name b)
in (

let uu____906 = (

let uu____908 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (

let uu____909 = (

let uu____911 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (uu____911)::[])
in (uu____908)::uu____909))
in (uu____905)::uu____906))
in (uu____902)::uu____903))
in (r)::uu____900)
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____898))
in (FStar_Syntax_Syntax.mk_Tm_app uu____891 uu____897)))
in (uu____890 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (mk_repr b wp))
in (

let expected_k = (

let uu____919 = (

let uu____923 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____924 = (

let uu____926 = (FStar_Syntax_Syntax.mk_binder b)
in (

let uu____927 = (

let uu____929 = (FStar_Syntax_Syntax.mk_binder wp_f)
in (

let uu____930 = (

let uu____932 = (

let uu____933 = (

let uu____934 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (mk_repr a uu____934))
in (FStar_Syntax_Syntax.null_binder uu____933))
in (

let uu____935 = (

let uu____937 = (FStar_Syntax_Syntax.mk_binder wp_g)
in (

let uu____938 = (

let uu____940 = (

let uu____941 = (

let uu____942 = (

let uu____946 = (FStar_Syntax_Syntax.mk_binder x_a)
in (uu____946)::[])
in (

let uu____947 = (

let uu____950 = (mk_repr b wp_g_x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____950))
in (FStar_Syntax_Util.arrow uu____942 uu____947)))
in (FStar_Syntax_Syntax.null_binder uu____941))
in (uu____940)::[])
in (uu____937)::uu____938))
in (uu____932)::uu____935))
in (uu____929)::uu____930))
in (uu____926)::uu____927))
in (uu____923)::uu____924))
in (

let uu____951 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow uu____919 uu____951)))
in (

let uu____954 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1 expected_k)
in (match (uu____954) with
| (expected_k1, uu____959, uu____960) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_range env1 (FStar_Pervasives_Native.snd ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos)
in (

let env3 = (

let uu___96_964 = env2
in {FStar_TypeChecker_Env.solver = uu___96_964.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___96_964.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___96_964.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___96_964.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___96_964.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___96_964.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___96_964.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___96_964.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___96_964.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___96_964.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___96_964.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___96_964.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___96_964.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___96_964.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___96_964.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___96_964.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___96_964.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___96_964.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___96_964.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___96_964.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___96_964.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___96_964.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___96_964.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___96_964.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___96_964.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___96_964.FStar_TypeChecker_Env.is_native_tactic})
in (

let br = (check_and_gen' env3 ed2.FStar_Syntax_Syntax.bind_repr expected_k1)
in br)))
end)))))))))
end)))
in (

let return_repr = (

let x_a = (

let uu____971 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" FStar_Pervasives_Native.None uu____971))
in (

let res = (

let wp = (

let uu____978 = (

let uu____979 = (

let uu____980 = (FStar_TypeChecker_Env.inst_tscheme return_wp)
in (FStar_All.pipe_right uu____980 FStar_Pervasives_Native.snd))
in (

let uu____985 = (

let uu____986 = (

let uu____988 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____989 = (

let uu____991 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (uu____991)::[])
in (uu____988)::uu____989))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____986))
in (FStar_Syntax_Syntax.mk_Tm_app uu____979 uu____985)))
in (uu____978 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (mk_repr a wp))
in (

let expected_k = (

let uu____999 = (

let uu____1003 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1004 = (

let uu____1006 = (FStar_Syntax_Syntax.mk_binder x_a)
in (uu____1006)::[])
in (uu____1003)::uu____1004))
in (

let uu____1007 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow uu____999 uu____1007)))
in (

let uu____1010 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1 expected_k)
in (match (uu____1010) with
| (expected_k1, uu____1018, uu____1019) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_range env1 (FStar_Pervasives_Native.snd ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos)
in (

let uu____1022 = (check_and_gen' env2 ed2.FStar_Syntax_Syntax.return_repr expected_k1)
in (match (uu____1022) with
| (univs1, repr1) -> begin
(match (univs1) with
| [] -> begin
(([]), (repr1))
end
| uu____1034 -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Unexpected universe-polymorphic return for effect"), (repr1.FStar_Syntax_Syntax.pos)))))
end)
end)))
end)))))
in (

let actions = (

let check_action = (fun act -> (

let uu____1054 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1 act.FStar_Syntax_Syntax.action_typ)
in (match (uu____1054) with
| (act_typ, uu____1059, g_t) -> begin
(

let env' = (

let uu___97_1062 = (FStar_TypeChecker_Env.set_expected_typ env1 act_typ)
in {FStar_TypeChecker_Env.solver = uu___97_1062.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___97_1062.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___97_1062.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___97_1062.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___97_1062.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___97_1062.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___97_1062.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___97_1062.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___97_1062.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = uu___97_1062.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___97_1062.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___97_1062.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___97_1062.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___97_1062.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___97_1062.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___97_1062.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___97_1062.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___97_1062.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___97_1062.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___97_1062.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___97_1062.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___97_1062.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___97_1062.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___97_1062.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___97_1062.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___97_1062.FStar_TypeChecker_Env.is_native_tactic})
in ((

let uu____1064 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____1064) with
| true -> begin
(

let uu____1065 = (FStar_Syntax_Print.term_to_string act.FStar_Syntax_Syntax.action_defn)
in (

let uu____1066 = (FStar_Syntax_Print.term_to_string act_typ)
in (FStar_Util.print3 "Checking action %s:\n[definition]: %s\n[cps\'d type]: %s\n" (FStar_Ident.text_of_lid act.FStar_Syntax_Syntax.action_name) uu____1065 uu____1066)))
end
| uu____1067 -> begin
()
end));
(

let uu____1068 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' act.FStar_Syntax_Syntax.action_defn)
in (match (uu____1068) with
| (act_defn, uu____1073, g_a) -> begin
(

let act_defn1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env1 act_defn)
in (

let act_typ1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::[]) env1 act_typ)
in (

let uu____1077 = (

let act_typ2 = (FStar_Syntax_Subst.compress act_typ1)
in (match (act_typ2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____1095 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____1095) with
| (bs1, uu____1101) -> begin
(

let res = (mk_repr' FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun)
in (

let k = (

let uu____1108 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs1 uu____1108))
in (

let uu____1111 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1 k)
in (match (uu____1111) with
| (k1, uu____1118, g) -> begin
((k1), (g))
end))))
end))
end
| uu____1120 -> begin
(

let uu____1121 = (

let uu____1122 = (

let uu____1125 = (

let uu____1126 = (FStar_Syntax_Print.term_to_string act_typ2)
in (

let uu____1127 = (FStar_Syntax_Print.tag_of_term act_typ2)
in (FStar_Util.format2 "Actions must have function types (not: %s, a.k.a. %s)" uu____1126 uu____1127)))
in ((uu____1125), (act_defn1.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____1122))
in (FStar_Pervasives.raise uu____1121))
end))
in (match (uu____1077) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env1 act_typ1 expected_k)
in ((

let uu____1134 = (

let uu____1135 = (

let uu____1136 = (FStar_TypeChecker_Rel.conj_guard g_t g)
in (FStar_TypeChecker_Rel.conj_guard g_k uu____1136))
in (FStar_TypeChecker_Rel.conj_guard g_a uu____1135))
in (FStar_TypeChecker_Rel.force_trivial_guard env1 uu____1134));
(

let act_typ2 = (

let uu____1140 = (

let uu____1141 = (FStar_Syntax_Subst.compress expected_k)
in uu____1141.FStar_Syntax_Syntax.n)
in (match (uu____1140) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____1158 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____1158) with
| (bs1, c1) -> begin
(

let uu____1165 = (destruct_repr (FStar_Syntax_Util.comp_result c1))
in (match (uu____1165) with
| (a1, wp) -> begin
(

let c2 = (

let uu____1185 = (

let uu____1186 = (env1.FStar_TypeChecker_Env.universe_of env1 a1)
in (uu____1186)::[])
in (

let uu____1187 = (

let uu____1193 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____1193)::[])
in {FStar_Syntax_Syntax.comp_univs = uu____1185; FStar_Syntax_Syntax.effect_name = ed2.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a1; FStar_Syntax_Syntax.effect_args = uu____1187; FStar_Syntax_Syntax.flags = []}))
in (

let uu____1194 = (FStar_Syntax_Syntax.mk_Comp c2)
in (FStar_Syntax_Util.arrow bs1 uu____1194)))
end))
end))
end
| uu____1197 -> begin
(failwith "")
end))
in (

let uu____1200 = (FStar_TypeChecker_Util.generalize_universes env1 act_defn1)
in (match (uu____1200) with
| (univs1, act_defn2) -> begin
(

let act_typ3 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env1 act_typ2)
in (

let act_typ4 = (FStar_Syntax_Subst.close_univ_vars univs1 act_typ3)
in (

let uu___98_1207 = act
in {FStar_Syntax_Syntax.action_name = uu___98_1207.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___98_1207.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs1; FStar_Syntax_Syntax.action_params = uu___98_1207.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = act_defn2; FStar_Syntax_Syntax.action_typ = act_typ4})))
end)));
))
end))))
end));
))
end)))
in (FStar_All.pipe_right ed2.FStar_Syntax_Syntax.actions (FStar_List.map check_action)))
in ((repr), (bind_repr), (return_repr), (actions)))))))))
end))
in (match (uu____691) with
| (repr, bind_repr, return_repr, actions) -> begin
(

let t = (

let uu____1223 = (FStar_Syntax_Syntax.mk_Total ed2.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed2.FStar_Syntax_Syntax.binders uu____1223))
in (

let uu____1226 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (uu____1226) with
| (univs1, t1) -> begin
(

let signature1 = (

let uu____1232 = (

let uu____1235 = (

let uu____1236 = (FStar_Syntax_Subst.compress t1)
in uu____1236.FStar_Syntax_Syntax.n)
in ((effect_params), (uu____1235)))
in (match (uu____1232) with
| ([], uu____1239) -> begin
t1
end
| (uu____1245, FStar_Syntax_Syntax.Tm_arrow (uu____1246, c)) -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____1258 -> begin
(failwith "Impossible")
end))
in (

let close1 = (fun n1 ts -> (

let ts1 = (

let uu____1269 = (FStar_Syntax_Subst.close_tscheme effect_params ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs1 uu____1269))
in (

let m = (FStar_List.length (FStar_Pervasives_Native.fst ts1))
in ((

let uu____1275 = (((n1 >= (Prims.parse_int "0")) && (

let uu____1277 = (FStar_Syntax_Util.is_unknown (FStar_Pervasives_Native.snd ts1))
in (not (uu____1277)))) && (m <> n1))
in (match (uu____1275) with
| true -> begin
(

let error = (match ((m < n1)) with
| true -> begin
"not universe-polymorphic enough"
end
| uu____1290 -> begin
"too universe-polymorphic"
end)
in (

let uu____1291 = (

let uu____1292 = (FStar_Util.string_of_int n1)
in (

let uu____1293 = (FStar_Syntax_Print.tscheme_to_string ts1)
in (FStar_Util.format3 "The effect combinator is %s (n=%s) (%s)" error uu____1292 uu____1293)))
in (failwith uu____1291)))
end
| uu____1294 -> begin
()
end));
ts1;
))))
in (

let close_action = (fun act -> (

let uu____1299 = (close1 (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_defn)))
in (match (uu____1299) with
| (univs2, defn) -> begin
(

let uu____1304 = (close1 (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_typ)))
in (match (uu____1304) with
| (univs', typ) -> begin
(

let uu___99_1311 = act
in {FStar_Syntax_Syntax.action_name = uu___99_1311.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___99_1311.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs2; FStar_Syntax_Syntax.action_params = uu___99_1311.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = defn; FStar_Syntax_Syntax.action_typ = typ})
end))
end)))
in (

let ed3 = (

let uu___100_1315 = ed2
in (

let uu____1316 = (close1 (Prims.parse_int "0") return_wp)
in (

let uu____1317 = (close1 (Prims.parse_int "1") bind_wp)
in (

let uu____1318 = (close1 (Prims.parse_int "0") if_then_else1)
in (

let uu____1319 = (close1 (Prims.parse_int "0") ite_wp)
in (

let uu____1320 = (close1 (Prims.parse_int "0") stronger)
in (

let uu____1321 = (close1 (Prims.parse_int "1") close_wp)
in (

let uu____1322 = (close1 (Prims.parse_int "0") assert_p)
in (

let uu____1323 = (close1 (Prims.parse_int "0") assume_p)
in (

let uu____1324 = (close1 (Prims.parse_int "0") null_wp)
in (

let uu____1325 = (close1 (Prims.parse_int "0") trivial_wp)
in (

let uu____1326 = (

let uu____1327 = (close1 (Prims.parse_int "0") (([]), (repr)))
in (FStar_Pervasives_Native.snd uu____1327))
in (

let uu____1333 = (close1 (Prims.parse_int "0") return_repr)
in (

let uu____1334 = (close1 (Prims.parse_int "1") bind_repr)
in (

let uu____1335 = (FStar_List.map close_action actions)
in {FStar_Syntax_Syntax.cattributes = uu___100_1315.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___100_1315.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs1; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature1; FStar_Syntax_Syntax.ret_wp = uu____1316; FStar_Syntax_Syntax.bind_wp = uu____1317; FStar_Syntax_Syntax.if_then_else = uu____1318; FStar_Syntax_Syntax.ite_wp = uu____1319; FStar_Syntax_Syntax.stronger = uu____1320; FStar_Syntax_Syntax.close_wp = uu____1321; FStar_Syntax_Syntax.assert_p = uu____1322; FStar_Syntax_Syntax.assume_p = uu____1323; FStar_Syntax_Syntax.null_wp = uu____1324; FStar_Syntax_Syntax.trivial = uu____1325; FStar_Syntax_Syntax.repr = uu____1326; FStar_Syntax_Syntax.return_repr = uu____1333; FStar_Syntax_Syntax.bind_repr = uu____1334; FStar_Syntax_Syntax.actions = uu____1335})))))))))))))))
in ((

let uu____1338 = ((FStar_TypeChecker_Env.debug env1 FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("ED"))))
in (match (uu____1338) with
| true -> begin
(

let uu____1339 = (FStar_Syntax_Print.eff_decl_to_string false ed3)
in (FStar_Util.print_string uu____1339))
end
| uu____1340 -> begin
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
end)))


let cps_and_elaborate : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option) = (fun env ed -> (

let uu____1354 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____1354) with
| (effect_binders_un, signature_un) -> begin
(

let uu____1364 = (FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un)
in (match (uu____1364) with
| (effect_binders, env1, uu____1375) -> begin
(

let uu____1376 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un)
in (match (uu____1376) with
| (signature, uu____1385) -> begin
(

let effect_binders1 = (FStar_List.map (fun uu____1398 -> (match (uu____1398) with
| (bv, qual) -> begin
(

let uu____1405 = (

let uu___101_1406 = bv
in (

let uu____1407 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env1 bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___101_1406.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___101_1406.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1407}))
in ((uu____1405), (qual)))
end)) effect_binders)
in (

let uu____1410 = (

let uu____1415 = (

let uu____1416 = (FStar_Syntax_Subst.compress signature_un)
in uu____1416.FStar_Syntax_Syntax.n)
in (match (uu____1415) with
| FStar_Syntax_Syntax.Tm_arrow (((a, uu____1424))::[], effect_marker) -> begin
((a), (effect_marker))
end
| uu____1439 -> begin
(failwith "bad shape for effect-for-free signature")
end))
in (match (uu____1410) with
| (a, effect_marker) -> begin
(

let a1 = (

let uu____1456 = (FStar_Syntax_Syntax.is_null_bv a)
in (match (uu____1456) with
| true -> begin
(

let uu____1457 = (

let uu____1459 = (FStar_Syntax_Syntax.range_of_bv a)
in FStar_Pervasives_Native.Some (uu____1459))
in (FStar_Syntax_Syntax.gen_bv "a" uu____1457 a.FStar_Syntax_Syntax.sort))
end
| uu____1460 -> begin
a
end))
in (

let open_and_check = (fun env2 other_binders t -> (

let subst1 = (FStar_Syntax_Subst.opening_of_binders (FStar_List.append effect_binders1 other_binders))
in (

let t1 = (FStar_Syntax_Subst.subst subst1 t)
in (

let uu____1483 = (FStar_TypeChecker_TcTerm.tc_term env2 t1)
in (match (uu____1483) with
| (t2, comp, uu____1491) -> begin
((t2), (comp))
end)))))
in (

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None signature.FStar_Syntax_Syntax.pos))
in (

let uu____1502 = (open_and_check env1 [] ed.FStar_Syntax_Syntax.repr)
in (match (uu____1502) with
| (repr, _comp) -> begin
((

let uu____1515 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____1515) with
| true -> begin
(

let uu____1516 = (FStar_Syntax_Print.term_to_string repr)
in (FStar_Util.print1 "Representation is: %s\n" uu____1516))
end
| uu____1517 -> begin
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

let uu____1522 = (

let uu____1523 = (

let uu____1524 = (

let uu____1534 = (

let uu____1538 = (

let uu____1541 = (FStar_Syntax_Syntax.bv_to_name a1)
in (

let uu____1542 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____1541), (uu____1542))))
in (uu____1538)::[])
in ((wp_type1), (uu____1534)))
in FStar_Syntax_Syntax.Tm_app (uu____1524))
in (mk1 uu____1523))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env1 uu____1522))
in (

let effect_signature = (

let binders = (

let uu____1557 = (

let uu____1560 = (FStar_Syntax_Syntax.as_implicit false)
in ((a1), (uu____1560)))
in (

let uu____1561 = (

let uu____1565 = (

let uu____1566 = (FStar_Syntax_Syntax.gen_bv "dijkstra_wp" FStar_Pervasives_Native.None wp_a)
in (FStar_All.pipe_right uu____1566 FStar_Syntax_Syntax.mk_binder))
in (uu____1565)::[])
in (uu____1557)::uu____1561))
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

let uu____1609 = item
in (match (uu____1609) with
| (u_item, item1) -> begin
(

let uu____1621 = (open_and_check env2 other_binders item1)
in (match (uu____1621) with
| (item2, item_comp) -> begin
((

let uu____1631 = (

let uu____1632 = (FStar_Syntax_Util.is_total_lcomp item_comp)
in (not (uu____1632)))
in (match (uu____1631) with
| true -> begin
(

let uu____1633 = (

let uu____1634 = (

let uu____1635 = (FStar_Syntax_Print.term_to_string item2)
in (

let uu____1636 = (FStar_Syntax_Print.lcomp_to_string item_comp)
in (FStar_Util.format2 "Computation for [%s] is not total : %s !" uu____1635 uu____1636)))
in FStar_Errors.Err (uu____1634))
in (FStar_Pervasives.raise uu____1633))
end
| uu____1637 -> begin
()
end));
(

let uu____1638 = (FStar_TypeChecker_DMFF.star_expr dmff_env1 item2)
in (match (uu____1638) with
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

let uu____1651 = (elaborate_and_star dmff_env [] ed.FStar_Syntax_Syntax.bind_repr)
in (match (uu____1651) with
| (dmff_env1, uu____1664, bind_wp, bind_elab) -> begin
(

let uu____1667 = (elaborate_and_star dmff_env1 [] ed.FStar_Syntax_Syntax.return_repr)
in (match (uu____1667) with
| (dmff_env2, uu____1680, return_wp, return_elab) -> begin
(

let rc_gtot = {FStar_Syntax_Syntax.residual_effect = FStar_Parser_Const.effect_GTot_lid; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.None; FStar_Syntax_Syntax.residual_flags = []}
in (

let lift_from_pure_wp = (

let uu____1687 = (

let uu____1688 = (FStar_Syntax_Subst.compress return_wp)
in uu____1688.FStar_Syntax_Syntax.n)
in (match (uu____1687) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(

let uu____1716 = (

let uu____1724 = (

let uu____1727 = (FStar_Syntax_Util.abs bs body FStar_Pervasives_Native.None)
in (FStar_Syntax_Subst.open_term ((b1)::(b2)::[]) uu____1727))
in (match (uu____1724) with
| ((b11)::(b21)::[], body1) -> begin
((b11), (b21), (body1))
end
| uu____1761 -> begin
(failwith "Impossible : open_term not preserving binders arity")
end))
in (match (uu____1716) with
| (b11, b21, body1) -> begin
(

let env0 = (

let uu____1783 = (FStar_TypeChecker_DMFF.get_env dmff_env2)
in (FStar_TypeChecker_Env.push_binders uu____1783 ((b11)::(b21)::[])))
in (

let wp_b1 = (

let raw_wp_b1 = (

let uu____1794 = (

let uu____1795 = (

let uu____1805 = (

let uu____1809 = (

let uu____1812 = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst b11))
in (

let uu____1813 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____1812), (uu____1813))))
in (uu____1809)::[])
in ((wp_type1), (uu____1805)))
in FStar_Syntax_Syntax.Tm_app (uu____1795))
in (mk1 uu____1794))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env0 raw_wp_b1))
in (

let uu____1821 = (

let uu____1826 = (

let uu____1827 = (FStar_Syntax_Util.unascribe wp_b1)
in (FStar_TypeChecker_Normalize.eta_expand_with_type env0 body1 uu____1827))
in (FStar_All.pipe_left FStar_Syntax_Util.abs_formals uu____1826))
in (match (uu____1821) with
| (bs1, body2, what') -> begin
(

let fail = (fun uu____1840 -> (

let error_msg = (

let uu____1842 = (FStar_Syntax_Print.term_to_string body2)
in (FStar_Util.format2 "The body of return_wp (%s) should be of type Type0 but is of type %s" uu____1842 (match (what') with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (rc) -> begin
(FStar_Ident.text_of_lid rc.FStar_Syntax_Syntax.residual_effect)
end)))
in (failwith error_msg)))
in ((match (what') with
| FStar_Pervasives_Native.None -> begin
(fail ())
end
| FStar_Pervasives_Native.Some (rc) -> begin
((match ((not ((FStar_Syntax_Util.is_pure_effect rc.FStar_Syntax_Syntax.residual_effect)))) with
| true -> begin
(fail ())
end
| uu____1847 -> begin
()
end);
(

let uu____1848 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun rt -> (

let g_opt = (FStar_TypeChecker_Rel.try_teq true env1 rt FStar_Syntax_Util.ktype0)
in (match (g_opt) with
| FStar_Pervasives_Native.Some (g') -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env1 g')
end
| FStar_Pervasives_Native.None -> begin
(fail ())
end))))
in (FStar_All.pipe_right uu____1848 FStar_Pervasives.ignore));
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

let uu____1871 = (

let uu____1872 = (FStar_Syntax_Syntax.bv_to_name wp)
in (

let uu____1873 = (

let uu____1874 = (

let uu____1878 = (FStar_Syntax_Util.abs ((b21)::[]) body2 what')
in ((uu____1878), (FStar_Pervasives_Native.None)))
in (uu____1874)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____1872 uu____1873)))
in (uu____1871 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let uu____1894 = (

let uu____1895 = (

let uu____1899 = (FStar_Syntax_Syntax.mk_binder wp)
in (uu____1899)::[])
in (b11)::uu____1895)
in (

let uu____1902 = (FStar_Syntax_Util.abs bs1 body3 what)
in (FStar_Syntax_Util.abs uu____1894 uu____1902 (FStar_Pervasives_Native.Some (rc_gtot)))))));
))
end))))
end))
end
| uu____1903 -> begin
(failwith "unexpected shape for return")
end))
in (

let return_wp1 = (

let uu____1905 = (

let uu____1906 = (FStar_Syntax_Subst.compress return_wp)
in uu____1906.FStar_Syntax_Syntax.n)
in (match (uu____1905) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(

let uu____1934 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs ((b1)::(b2)::[]) uu____1934 (FStar_Pervasives_Native.Some (rc_gtot))))
end
| uu____1941 -> begin
(failwith "unexpected shape for return")
end))
in (

let bind_wp1 = (

let uu____1943 = (

let uu____1944 = (FStar_Syntax_Subst.compress bind_wp)
in uu____1944.FStar_Syntax_Syntax.n)
in (match (uu____1943) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let r = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.range_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let uu____1963 = (

let uu____1964 = (

let uu____1966 = (

let uu____1967 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (r)))
in (FStar_Syntax_Syntax.null_binder uu____1967))
in (uu____1966)::[])
in (FStar_List.append uu____1964 binders))
in (FStar_Syntax_Util.abs uu____1963 body what)))
end
| uu____1968 -> begin
(failwith "unexpected shape for bind")
end))
in (

let apply_close = (fun t -> (match (((FStar_List.length effect_binders1) = (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____1987 -> begin
(

let uu____1988 = (

let uu____1989 = (

let uu____1990 = (

let uu____2000 = (

let uu____2001 = (FStar_Syntax_Util.args_of_binders effect_binders1)
in (FStar_Pervasives_Native.snd uu____2001))
in ((t), (uu____2000)))
in FStar_Syntax_Syntax.Tm_app (uu____1990))
in (mk1 uu____1989))
in (FStar_Syntax_Subst.close effect_binders1 uu____1988))
end))
in (

let rec apply_last1 = (fun f l -> (match (l) with
| [] -> begin
(failwith "empty path..")
end
| (a2)::[] -> begin
(

let uu____2024 = (f a2)
in (uu____2024)::[])
end
| (x)::xs -> begin
(

let uu____2028 = (apply_last1 f xs)
in (x)::uu____2028)
end))
in (

let register = (fun name item -> (

let p = (FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname)
in (

let p' = (apply_last1 (fun s -> (Prims.strcat "__" (Prims.strcat s (Prims.strcat "_eff_override_" name)))) p)
in (

let l' = (FStar_Ident.lid_of_path p' FStar_Range.dummyRange)
in (

let uu____2045 = (FStar_TypeChecker_Env.try_lookup_lid env1 l')
in (match (uu____2045) with
| FStar_Pervasives_Native.Some (_us, _t) -> begin
((

let uu____2062 = (FStar_Options.debug_any ())
in (match (uu____2062) with
| true -> begin
(

let uu____2063 = (FStar_Ident.string_of_lid l')
in (FStar_Util.print1 "DM4F: Applying override %s\n" uu____2063))
end
| uu____2064 -> begin
()
end));
(

let uu____2065 = (FStar_Syntax_Syntax.lid_as_fv l' FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____2065));
)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2070 = (

let uu____2073 = (mk_lid name)
in (

let uu____2074 = (FStar_Syntax_Util.abs effect_binders1 item FStar_Pervasives_Native.None)
in (FStar_TypeChecker_Util.mk_toplevel_definition env1 uu____2073 uu____2074)))
in (match (uu____2070) with
| (sigelt, fv) -> begin
((

let uu____2078 = (

let uu____2080 = (FStar_ST.read sigelts)
in (sigelt)::uu____2080)
in (FStar_ST.write sigelts uu____2078));
fv;
)
end))
end))))))
in (

let lift_from_pure_wp1 = (register "lift_from_pure" lift_from_pure_wp)
in (

let return_wp2 = (register "return_wp" return_wp1)
in ((

let uu____2091 = (

let uu____2093 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true"))))
in (

let uu____2094 = (FStar_ST.read sigelts)
in (uu____2093)::uu____2094))
in (FStar_ST.write sigelts uu____2091));
(

let return_elab1 = (register "return_elab" return_elab)
in ((

let uu____2104 = (

let uu____2106 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false"))))
in (

let uu____2107 = (FStar_ST.read sigelts)
in (uu____2106)::uu____2107))
in (FStar_ST.write sigelts uu____2104));
(

let bind_wp2 = (register "bind_wp" bind_wp1)
in ((

let uu____2117 = (

let uu____2119 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true"))))
in (

let uu____2120 = (FStar_ST.read sigelts)
in (uu____2119)::uu____2120))
in (FStar_ST.write sigelts uu____2117));
(

let bind_elab1 = (register "bind_elab" bind_elab)
in ((

let uu____2130 = (

let uu____2132 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false"))))
in (

let uu____2133 = (FStar_ST.read sigelts)
in (uu____2132)::uu____2133))
in (FStar_ST.write sigelts uu____2130));
(

let uu____2141 = (FStar_List.fold_left (fun uu____2175 action -> (match (uu____2175) with
| (dmff_env3, actions) -> begin
(

let params_un = (FStar_Syntax_Subst.open_binders action.FStar_Syntax_Syntax.action_params)
in (

let uu____2188 = (

let uu____2192 = (FStar_TypeChecker_DMFF.get_env dmff_env3)
in (FStar_TypeChecker_TcTerm.tc_tparams uu____2192 params_un))
in (match (uu____2188) with
| (action_params, env', uu____2198) -> begin
(

let action_params1 = (FStar_List.map (fun uu____2211 -> (match (uu____2211) with
| (bv, qual) -> begin
(

let uu____2218 = (

let uu___102_2219 = bv
in (

let uu____2220 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env' bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___102_2219.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___102_2219.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____2220}))
in ((uu____2218), (qual)))
end)) action_params)
in (

let dmff_env' = (FStar_TypeChecker_DMFF.set_env dmff_env3 env')
in (

let uu____2224 = (elaborate_and_star dmff_env' action_params1 ((action.FStar_Syntax_Syntax.action_univs), (action.FStar_Syntax_Syntax.action_defn)))
in (match (uu____2224) with
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
| uu____2245 -> begin
(

let uu____2246 = (FStar_Syntax_Syntax.mk_Total action_typ_with_wp1)
in (FStar_Syntax_Util.flat_arrow action_params2 uu____2246))
end)
in ((

let uu____2250 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("ED")))
in (match (uu____2250) with
| true -> begin
(

let uu____2251 = (FStar_Syntax_Print.binders_to_string "," params_un)
in (

let uu____2252 = (FStar_Syntax_Print.binders_to_string "," action_params2)
in (

let uu____2253 = (FStar_Syntax_Print.term_to_string action_typ_with_wp2)
in (

let uu____2254 = (FStar_Syntax_Print.term_to_string action_elab2)
in (FStar_Util.print4 "original action_params %s, end action_params %s, type %s, term %s\n" uu____2251 uu____2252 uu____2253 uu____2254)))))
end
| uu____2255 -> begin
()
end));
(

let action_elab3 = (register (Prims.strcat name "_elab") action_elab2)
in (

let action_typ_with_wp3 = (register (Prims.strcat name "_complete_type") action_typ_with_wp2)
in (

let uu____2258 = (

let uu____2260 = (

let uu___103_2261 = action
in (

let uu____2262 = (apply_close action_elab3)
in (

let uu____2263 = (apply_close action_typ_with_wp3)
in {FStar_Syntax_Syntax.action_name = uu___103_2261.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___103_2261.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___103_2261.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = []; FStar_Syntax_Syntax.action_defn = uu____2262; FStar_Syntax_Syntax.action_typ = uu____2263})))
in (uu____2260)::actions)
in ((dmff_env4), (uu____2258)))));
))))))))
end))))
end)))
end)) ((dmff_env2), ([])) ed.FStar_Syntax_Syntax.actions)
in (match (uu____2141) with
| (dmff_env3, actions) -> begin
(

let actions1 = (FStar_List.rev actions)
in (

let repr1 = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp_a" FStar_Pervasives_Native.None wp_a)
in (

let binders = (

let uu____2283 = (FStar_Syntax_Syntax.mk_binder a1)
in (

let uu____2284 = (

let uu____2286 = (FStar_Syntax_Syntax.mk_binder wp)
in (uu____2286)::[])
in (uu____2283)::uu____2284))
in (

let uu____2287 = (

let uu____2288 = (

let uu____2289 = (

let uu____2290 = (

let uu____2300 = (

let uu____2304 = (

let uu____2307 = (FStar_Syntax_Syntax.bv_to_name a1)
in (

let uu____2308 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____2307), (uu____2308))))
in (uu____2304)::[])
in ((repr), (uu____2300)))
in FStar_Syntax_Syntax.Tm_app (uu____2290))
in (mk1 uu____2289))
in (

let uu____2316 = (FStar_Syntax_Syntax.bv_to_name wp)
in (FStar_TypeChecker_DMFF.trans_F dmff_env3 uu____2288 uu____2316)))
in (FStar_Syntax_Util.abs binders uu____2287 FStar_Pervasives_Native.None))))
in (

let repr2 = (recheck_debug "FC" env1 repr1)
in (

let repr3 = (register "repr" repr2)
in (

let uu____2319 = (

let uu____2324 = (

let uu____2325 = (

let uu____2328 = (FStar_Syntax_Subst.compress wp_type1)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____2328))
in uu____2325.FStar_Syntax_Syntax.n)
in (match (uu____2324) with
| FStar_Syntax_Syntax.Tm_abs ((type_param)::effect_param, arrow1, uu____2336) -> begin
(

let uu____2353 = (

let uu____2362 = (FStar_Syntax_Subst.open_term ((type_param)::effect_param) arrow1)
in (match (uu____2362) with
| ((b)::bs, body) -> begin
((b), (bs), (body))
end
| uu____2393 -> begin
(failwith "Impossible : open_term nt preserving binders arity")
end))
in (match (uu____2353) with
| (type_param1, effect_param1, arrow2) -> begin
(

let uu____2421 = (

let uu____2422 = (

let uu____2425 = (FStar_Syntax_Subst.compress arrow2)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____2425))
in uu____2422.FStar_Syntax_Syntax.n)
in (match (uu____2421) with
| FStar_Syntax_Syntax.Tm_arrow (wp_binders, c) -> begin
(

let uu____2442 = (FStar_Syntax_Subst.open_comp wp_binders c)
in (match (uu____2442) with
| (wp_binders1, c1) -> begin
(

let uu____2451 = (FStar_List.partition (fun uu____2466 -> (match (uu____2466) with
| (bv, uu____2470) -> begin
(

let uu____2471 = (

let uu____2472 = (FStar_Syntax_Free.names bv.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____2472 (FStar_Util.set_mem (FStar_Pervasives_Native.fst type_param1))))
in (FStar_All.pipe_right uu____2471 Prims.op_Negation))
end)) wp_binders1)
in (match (uu____2451) with
| (pre_args, post_args) -> begin
(

let post = (match (post_args) with
| (post)::[] -> begin
post
end
| uu____2505 -> begin
(

let uu____2509 = (

let uu____2510 = (FStar_Syntax_Print.term_to_string arrow2)
in (FStar_Util.format1 "Impossible: multiple post candidates %s" uu____2510))
in (failwith uu____2509))
end)
in (

let uu____2513 = (FStar_Syntax_Util.arrow pre_args c1)
in (

let uu____2516 = (FStar_Syntax_Util.abs ((type_param1)::effect_param1) (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort FStar_Pervasives_Native.None)
in ((uu____2513), (uu____2516)))))
end))
end))
end
| uu____2521 -> begin
(

let uu____2522 = (

let uu____2523 = (FStar_Syntax_Print.term_to_string arrow2)
in (FStar_Util.format1 "Impossible: pre/post arrow %s" uu____2523))
in (failwith uu____2522))
end))
end))
end
| uu____2528 -> begin
(

let uu____2529 = (

let uu____2530 = (FStar_Syntax_Print.term_to_string wp_type1)
in (FStar_Util.format1 "Impossible: pre/post abs %s" uu____2530))
in (failwith uu____2529))
end))
in (match (uu____2319) with
| (pre, post) -> begin
((

let uu____2547 = (register "pre" pre)
in ());
(

let uu____2549 = (register "post" post)
in ());
(

let uu____2551 = (register "wp" wp_type1)
in ());
(

let ed1 = (

let uu___104_2553 = ed
in (

let uu____2554 = (FStar_Syntax_Subst.close_binders effect_binders1)
in (

let uu____2555 = (FStar_Syntax_Subst.close effect_binders1 effect_signature1)
in (

let uu____2556 = (

let uu____2557 = (apply_close return_wp2)
in (([]), (uu____2557)))
in (

let uu____2563 = (

let uu____2564 = (apply_close bind_wp2)
in (([]), (uu____2564)))
in (

let uu____2570 = (apply_close repr3)
in (

let uu____2571 = (

let uu____2572 = (apply_close return_elab1)
in (([]), (uu____2572)))
in (

let uu____2578 = (

let uu____2579 = (apply_close bind_elab1)
in (([]), (uu____2579)))
in {FStar_Syntax_Syntax.cattributes = uu___104_2553.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___104_2553.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___104_2553.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu____2554; FStar_Syntax_Syntax.signature = uu____2555; FStar_Syntax_Syntax.ret_wp = uu____2556; FStar_Syntax_Syntax.bind_wp = uu____2563; FStar_Syntax_Syntax.if_then_else = uu___104_2553.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = uu___104_2553.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = uu___104_2553.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = uu___104_2553.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = uu___104_2553.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = uu___104_2553.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = uu___104_2553.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = uu___104_2553.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = uu____2570; FStar_Syntax_Syntax.return_repr = uu____2571; FStar_Syntax_Syntax.bind_repr = uu____2578; FStar_Syntax_Syntax.actions = actions1}))))))))
in (

let uu____2585 = (FStar_TypeChecker_DMFF.gen_wps_for_free env1 effect_binders1 a1 wp_a ed1)
in (match (uu____2585) with
| (sigelts', ed2) -> begin
((

let uu____2596 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____2596) with
| true -> begin
(

let uu____2597 = (FStar_Syntax_Print.eff_decl_to_string true ed2)
in (FStar_Util.print_string uu____2597))
end
| uu____2598 -> begin
()
end));
(

let lift_from_pure_opt = (match (((FStar_List.length effect_binders1) = (Prims.parse_int "0"))) with
| true -> begin
(

let lift_from_pure = (

let uu____2609 = (

let uu____2611 = (

let uu____2617 = (apply_close lift_from_pure_wp1)
in (([]), (uu____2617)))
in FStar_Pervasives_Native.Some (uu____2611))
in {FStar_Syntax_Syntax.source = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.target = ed2.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.lift_wp = uu____2609; FStar_Syntax_Syntax.lift = FStar_Pervasives_Native.None})
in (

let uu____2628 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_sub_effect (lift_from_pure)))
in FStar_Pervasives_Native.Some (uu____2628)))
end
| uu____2629 -> begin
FStar_Pervasives_Native.None
end)
in (

let uu____2630 = (

let uu____2632 = (

let uu____2634 = (FStar_ST.read sigelts)
in (FStar_List.rev uu____2634))
in (FStar_List.append uu____2632 sigelts'))
in ((uu____2630), (ed2), (lift_from_pure_opt))));
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
end)))
end))
end))
end)))


let tc_lex_t = (fun env ses quals lids -> (match (ses) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (lex_t1, [], [], t, uu____2685, uu____2686); FStar_Syntax_Syntax.sigrng = r; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = uu____2688; FStar_Syntax_Syntax.sigattrs = uu____2689})::({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (lex_top1, [], _t_top, _lex_t_top, _0_39, uu____2693); FStar_Syntax_Syntax.sigrng = r1; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = uu____2695; FStar_Syntax_Syntax.sigattrs = uu____2696})::({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, _0_40, uu____2700); FStar_Syntax_Syntax.sigrng = r2; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = uu____2702; FStar_Syntax_Syntax.sigattrs = uu____2703})::[] when (((_0_39 = (Prims.parse_int "0")) && (_0_40 = (Prims.parse_int "0"))) && (((FStar_Ident.lid_equals lex_t1 FStar_Parser_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top1 FStar_Parser_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Parser_Const.lexcons_lid))) -> begin
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

let uu____2745 = (

let uu____2748 = (

let uu____2749 = (

let uu____2754 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid r1) FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in ((uu____2754), ((FStar_Syntax_Syntax.U_name (utop))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____2749))
in (FStar_Syntax_Syntax.mk uu____2748))
in (uu____2745 FStar_Pervasives_Native.None r1))
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

let uu____2774 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) FStar_Pervasives_Native.None r2)
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (r2)) uu____2774))
in (

let hd1 = (

let uu____2780 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (r2)) uu____2780))
in (

let tl1 = (

let uu____2782 = (

let uu____2783 = (

let uu____2786 = (

let uu____2787 = (

let uu____2792 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid r2) FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in ((uu____2792), ((FStar_Syntax_Syntax.U_name (ucons2))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____2787))
in (FStar_Syntax_Syntax.mk uu____2786))
in (uu____2783 FStar_Pervasives_Native.None r2))
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (r2)) uu____2782))
in (

let res = (

let uu____2805 = (

let uu____2808 = (

let uu____2809 = (

let uu____2814 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid r2) FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in ((uu____2814), ((FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____2809))
in (FStar_Syntax_Syntax.mk uu____2808))
in (uu____2805 FStar_Pervasives_Native.None r2))
in (

let uu____2824 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow ((((a), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::(((hd1), (FStar_Pervasives_Native.None)))::(((tl1), (FStar_Pervasives_Native.None)))::[]) uu____2824))))))
in (

let lex_cons_t1 = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((lex_cons), ((ucons1)::(ucons2)::[]), (lex_cons_t1), (FStar_Parser_Const.lex_t_lid), ((Prims.parse_int "0")), ([]))); FStar_Syntax_Syntax.sigrng = r2; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (

let uu____2846 = (FStar_TypeChecker_Env.get_range env)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle ((((tc)::(dc_lextop)::(dc_lexcons)::[]), (lids))); FStar_Syntax_Syntax.sigrng = uu____2846; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))))))))))))))
end
| uu____2849 -> begin
(

let uu____2851 = (

let uu____2852 = (

let uu____2853 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_bundle (((ses), (lids)))))
in (FStar_Syntax_Print.sigelt_to_string uu____2853))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" uu____2852))
in (failwith uu____2851))
end))


let tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env1 = (FStar_TypeChecker_Env.set_range env r)
in (

let uu____2879 = (FStar_Syntax_Util.type_u ())
in (match (uu____2879) with
| (k, uu____2883) -> begin
(

let phi1 = (

let uu____2885 = (tc_check_trivial_guard env1 phi k)
in (FStar_All.pipe_right uu____2885 (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env1)))
in ((FStar_TypeChecker_Util.check_uvars r phi1);
(

let uu____2887 = (FStar_TypeChecker_Util.generalize_universes env1 phi1)
in (match (uu____2887) with
| (us, phi2) -> begin
{FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_assume (((lid), (us), (phi2))); FStar_Syntax_Syntax.sigrng = r; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
end));
))
end))))


let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env ses quals lids -> (

let env1 = (FStar_TypeChecker_Env.push env "tc_inductive")
in (

let uu____2920 = (FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1 ses quals lids)
in (match (uu____2920) with
| (sig_bndle, tcs, datas) -> begin
(

let data_ops_ses = (

let uu____2939 = (FStar_List.map (FStar_TypeChecker_Util.mk_data_operations quals env1 tcs) datas)
in (FStar_All.pipe_right uu____2939 FStar_List.flatten))
in ((

let uu____2947 = ((FStar_Options.no_positivity ()) || (FStar_Options.lax ()))
in (match (uu____2947) with
| true -> begin
()
end
| uu____2948 -> begin
(

let env2 = (FStar_TypeChecker_Env.push_sigelt env1 sig_bndle)
in (FStar_List.iter (fun ty -> (

let b = (FStar_TypeChecker_TcInductive.check_positivity ty env2)
in (match ((not (b))) with
| true -> begin
(

let uu____2958 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____2964, uu____2965, uu____2966, uu____2967, uu____2968) -> begin
((lid), (ty.FStar_Syntax_Syntax.sigrng))
end
| uu____2973 -> begin
(failwith "Impossible!")
end)
in (match (uu____2958) with
| (lid, r) -> begin
(FStar_Errors.err r (Prims.strcat "Inductive type " (Prims.strcat lid.FStar_Ident.str " does not satisfy the positivity condition")))
end))
end
| uu____2978 -> begin
()
end))) tcs))
end));
(

let skip_prims_type = (fun uu____2982 -> (

let lid = (

let ty = (FStar_List.hd tcs)
in (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____2986, uu____2987, uu____2988, uu____2989, uu____2990) -> begin
lid
end
| uu____2995 -> begin
(failwith "Impossible")
end))
in (

let types_to_skip = ("c_False")::("c_True")::("equals")::("h_equals")::("c_and")::("c_or")::[]
in (FStar_List.existsb (fun s -> (s = lid.FStar_Ident.ident.FStar_Ident.idText)) types_to_skip))))
in (

let is_noeq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Noeq)) quals)
in (

let res = (

let uu____3008 = ((((FStar_List.length tcs) = (Prims.parse_int "0")) || ((FStar_Ident.lid_equals env1.FStar_TypeChecker_Env.curmodule FStar_Parser_Const.prims_lid) && (skip_prims_type ()))) || is_noeq)
in (match (uu____3008) with
| true -> begin
(((sig_bndle)::[]), (data_ops_ses))
end
| uu____3019 -> begin
(

let is_unopteq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Unopteq)) quals)
in (

let ses1 = (match (is_unopteq) with
| true -> begin
(FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme sig_bndle tcs datas env1 tc_assume)
end
| uu____3026 -> begin
(FStar_TypeChecker_TcInductive.optimized_haseq_scheme sig_bndle tcs datas env1 tc_assume)
end)
in (

let uu____3027 = (

let uu____3029 = (

let uu____3030 = (FStar_TypeChecker_Env.get_range env1)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle ((((FStar_List.append tcs datas)), (lids))); FStar_Syntax_Syntax.sigrng = uu____3030; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (uu____3029)::ses1)
in ((uu____3027), (data_ops_ses)))))
end))
in ((

let uu____3036 = (FStar_TypeChecker_Env.pop env1 "tc_inductive")
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
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____3060) -> begin
(failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____3073) -> begin
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

let uu____3103 = (tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids)
in (match (uu____3103) with
| (ses1, projectors_ses) -> begin
((ses1), (projectors_ses))
end)))
end
| FStar_Syntax_Syntax.Sig_pragma (p) -> begin
(

let set_options1 = (fun t s -> (

let uu____3128 = (FStar_Options.set_options t s)
in (match (uu____3128) with
| FStar_Getopt.Success -> begin
()
end
| FStar_Getopt.Help -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Failed to process pragma: use \'fstar --help\' to see which options are available"), (r)))))
end
| FStar_Getopt.Error (s1) -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((((Prims.strcat "Failed to process pragma: " s1)), (r)))))
end)))
in (match (p) with
| FStar_Syntax_Syntax.LightOff -> begin
((match ((p = FStar_Syntax_Syntax.LightOff)) with
| true -> begin
(FStar_Options.set_ml_ish ())
end
| uu____3135 -> begin
()
end);
(((se)::[]), ([]));
)
end
| FStar_Syntax_Syntax.SetOptions (o) -> begin
((set_options1 FStar_Options.Set o);
(((se)::[]), ([]));
)
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
((

let uu____3145 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____3145 FStar_Pervasives.ignore));
(match (sopt) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (s) -> begin
(set_options1 FStar_Options.Reset s)
end);
(((se)::[]), ([]));
)
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne) -> begin
(

let uu____3151 = (cps_and_elaborate env1 ne)
in (match (uu____3151) with
| (ses, ne1, lift_from_pure_opt) -> begin
(

let effect_and_lift_ses = (match (lift_from_pure_opt) with
| FStar_Pervasives_Native.Some (lift) -> begin
((

let uu___105_3173 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne1); FStar_Syntax_Syntax.sigrng = uu___105_3173.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___105_3173.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___105_3173.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___105_3173.FStar_Syntax_Syntax.sigattrs}))::(lift)::[]
end
| FStar_Pervasives_Native.None -> begin
((

let uu___106_3175 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne1); FStar_Syntax_Syntax.sigrng = uu___106_3175.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___106_3175.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___106_3175.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___106_3175.FStar_Syntax_Syntax.sigattrs}))::[]
end)
in (([]), ((FStar_List.append ses effect_and_lift_ses))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let ne1 = (tc_eff_decl env1 ne)
in (

let se1 = (

let uu___107_3181 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne1); FStar_Syntax_Syntax.sigrng = uu___107_3181.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___107_3181.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___107_3181.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___107_3181.FStar_Syntax_Syntax.sigattrs})
in (((se1)::[]), ([]))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub1) -> begin
(

let ed_src = (FStar_TypeChecker_Env.get_effect_decl env1 sub1.FStar_Syntax_Syntax.source)
in (

let ed_tgt = (FStar_TypeChecker_Env.get_effect_decl env1 sub1.FStar_Syntax_Syntax.target)
in (

let uu____3187 = (

let uu____3192 = (FStar_TypeChecker_Env.lookup_effect_lid env1 sub1.FStar_Syntax_Syntax.source)
in (monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____3192))
in (match (uu____3187) with
| (a, wp_a_src) -> begin
(

let uu____3203 = (

let uu____3208 = (FStar_TypeChecker_Env.lookup_effect_lid env1 sub1.FStar_Syntax_Syntax.target)
in (monad_signature env1 sub1.FStar_Syntax_Syntax.target uu____3208))
in (match (uu____3203) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (

let uu____3220 = (

let uu____3222 = (

let uu____3223 = (

let uu____3228 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (uu____3228)))
in FStar_Syntax_Syntax.NT (uu____3223))
in (uu____3222)::[])
in (FStar_Syntax_Subst.subst uu____3220 wp_b_tgt))
in (

let expected_k = (

let uu____3232 = (

let uu____3236 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____3237 = (

let uu____3239 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (uu____3239)::[])
in (uu____3236)::uu____3237))
in (

let uu____3240 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow uu____3232 uu____3240)))
in (

let repr_type = (fun eff_name a1 wp -> (

let no_reify = (fun l -> (

let uu____3261 = (

let uu____3262 = (

let uu____3265 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (

let uu____3266 = (FStar_TypeChecker_Env.get_range env1)
in ((uu____3265), (uu____3266))))
in FStar_Errors.Error (uu____3262))
in (FStar_Pervasives.raise uu____3261)))
in (

let uu____3269 = (FStar_TypeChecker_Env.effect_decl_opt env1 eff_name)
in (match (uu____3269) with
| FStar_Pervasives_Native.None -> begin
(no_reify eff_name)
end
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((FStar_Syntax_Syntax.U_unknown)::[]) env1 ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let uu____3288 = (

let uu____3289 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (not (uu____3289)))
in (match (uu____3288) with
| true -> begin
(no_reify eff_name)
end
| uu____3293 -> begin
(

let uu____3294 = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____3295 = (

let uu____3298 = (

let uu____3299 = (

let uu____3309 = (

let uu____3311 = (FStar_Syntax_Syntax.as_arg a1)
in (

let uu____3312 = (

let uu____3314 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____3314)::[])
in (uu____3311)::uu____3312))
in ((repr), (uu____3309)))
in FStar_Syntax_Syntax.Tm_app (uu____3299))
in (FStar_Syntax_Syntax.mk uu____3298))
in (uu____3295 FStar_Pervasives_Native.None uu____3294)))
end)))
end))))
in (

let uu____3324 = (match (((sub1.FStar_Syntax_Syntax.lift), (sub1.FStar_Syntax_Syntax.lift_wp))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(failwith "Impossible")
end
| (lift, FStar_Pervasives_Native.Some (uu____3339, lift_wp)) -> begin
(

let uu____3352 = (check_and_gen env1 lift_wp expected_k)
in ((lift), (uu____3352)))
end
| (FStar_Pervasives_Native.Some (what, lift), FStar_Pervasives_Native.None) -> begin
((

let uu____3367 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____3367) with
| true -> begin
(

let uu____3368 = (FStar_Syntax_Print.term_to_string lift)
in (FStar_Util.print1 "Lift for free : %s\n" uu____3368))
end
| uu____3369 -> begin
()
end));
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env1 (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange))
in (

let uu____3371 = (FStar_TypeChecker_TcTerm.tc_term env1 lift)
in (match (uu____3371) with
| (lift1, comp, uu____3380) -> begin
(

let uu____3381 = (FStar_TypeChecker_DMFF.star_expr dmff_env lift1)
in (match (uu____3381) with
| (uu____3388, lift_wp, lift_elab) -> begin
(

let uu____3391 = (recheck_debug "lift-wp" env1 lift_wp)
in (

let uu____3392 = (recheck_debug "lift-elab" env1 lift_elab)
in ((FStar_Pervasives_Native.Some ((([]), (lift_elab)))), ((([]), (lift_wp))))))
end))
end)));
)
end)
in (match (uu____3324) with
| (lift, lift_wp) -> begin
(

let lax1 = env1.FStar_TypeChecker_Env.lax
in (

let env2 = (

let uu___108_3415 = env1
in {FStar_TypeChecker_Env.solver = uu___108_3415.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___108_3415.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___108_3415.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___108_3415.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___108_3415.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___108_3415.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___108_3415.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___108_3415.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___108_3415.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___108_3415.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___108_3415.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___108_3415.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___108_3415.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___108_3415.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___108_3415.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___108_3415.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___108_3415.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___108_3415.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___108_3415.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___108_3415.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___108_3415.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___108_3415.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___108_3415.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___108_3415.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___108_3415.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___108_3415.FStar_TypeChecker_Env.is_native_tactic})
in (

let lift1 = (match (lift) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (uu____3419, lift1) -> begin
(

let uu____3426 = (

let uu____3431 = (FStar_TypeChecker_Env.lookup_effect_lid env2 sub1.FStar_Syntax_Syntax.source)
in (monad_signature env2 sub1.FStar_Syntax_Syntax.source uu____3431))
in (match (uu____3426) with
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

let uu____3453 = (FStar_TypeChecker_Env.get_range env2)
in (

let uu____3454 = (

let uu____3457 = (

let uu____3458 = (

let uu____3468 = (

let uu____3470 = (FStar_Syntax_Syntax.as_arg a_typ)
in (

let uu____3471 = (

let uu____3473 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (uu____3473)::[])
in (uu____3470)::uu____3471))
in ((lift_wp1), (uu____3468)))
in FStar_Syntax_Syntax.Tm_app (uu____3458))
in (FStar_Syntax_Syntax.mk uu____3457))
in (uu____3454 FStar_Pervasives_Native.None uu____3453)))
in (repr_type sub1.FStar_Syntax_Syntax.target a_typ lift_wp_a)))
in (

let expected_k1 = (

let uu____3486 = (

let uu____3490 = (FStar_Syntax_Syntax.mk_binder a1)
in (

let uu____3491 = (

let uu____3493 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (

let uu____3494 = (

let uu____3496 = (FStar_Syntax_Syntax.null_binder repr_f)
in (uu____3496)::[])
in (uu____3493)::uu____3494))
in (uu____3490)::uu____3491))
in (

let uu____3497 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow uu____3486 uu____3497)))
in (

let uu____3500 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env2 expected_k1)
in (match (uu____3500) with
| (expected_k2, uu____3506, uu____3507) -> begin
(

let lift2 = (check_and_gen env2 lift1 expected_k2)
in FStar_Pervasives_Native.Some (lift2))
end))))))))
end))
end)
in (

let sub2 = (

let uu___109_3510 = sub1
in {FStar_Syntax_Syntax.source = uu___109_3510.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = uu___109_3510.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = FStar_Pervasives_Native.Some (lift_wp); FStar_Syntax_Syntax.lift = lift1})
in (

let se1 = (

let uu___110_3512 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_sub_effect (sub2); FStar_Syntax_Syntax.sigrng = uu___110_3512.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___110_3512.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___110_3512.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___110_3512.FStar_Syntax_Syntax.sigattrs})
in (((se1)::[]), ([])))))))
end)))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, flags) -> begin
(

let env0 = env1
in (

let env2 = (FStar_TypeChecker_Env.set_range env1 r)
in (

let uu____3526 = (FStar_Syntax_Subst.open_comp tps c)
in (match (uu____3526) with
| (tps1, c1) -> begin
(

let uu____3535 = (FStar_TypeChecker_TcTerm.tc_tparams env2 tps1)
in (match (uu____3535) with
| (tps2, env3, us) -> begin
(

let uu____3546 = (FStar_TypeChecker_TcTerm.tc_comp env3 c1)
in (match (uu____3546) with
| (c2, u, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env3 g);
(

let tps3 = (FStar_Syntax_Subst.close_binders tps2)
in (

let c3 = (FStar_Syntax_Subst.close_comp tps3 c2)
in (

let uu____3560 = (

let uu____3561 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps3), (c3)))) FStar_Pervasives_Native.None r)
in (FStar_TypeChecker_Util.generalize_universes env0 uu____3561))
in (match (uu____3560) with
| (uvs1, t) -> begin
(

let uu____3574 = (

let uu____3582 = (

let uu____3585 = (

let uu____3586 = (FStar_Syntax_Subst.compress t)
in uu____3586.FStar_Syntax_Syntax.n)
in ((tps3), (uu____3585)))
in (match (uu____3582) with
| ([], FStar_Syntax_Syntax.Tm_arrow (uu____3596, c4)) -> begin
(([]), (c4))
end
| (uu____3620, FStar_Syntax_Syntax.Tm_arrow (tps4, c4)) -> begin
((tps4), (c4))
end
| uu____3638 -> begin
(failwith "Impossible")
end))
in (match (uu____3574) with
| (tps4, c4) -> begin
((match (((FStar_List.length uvs1) <> (Prims.parse_int "1"))) with
| true -> begin
(

let uu____3669 = (FStar_Syntax_Subst.open_univ_vars uvs1 t)
in (match (uu____3669) with
| (uu____3672, t1) -> begin
(

let uu____3674 = (

let uu____3675 = (

let uu____3678 = (

let uu____3679 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____3680 = (FStar_All.pipe_right (FStar_List.length uvs1) FStar_Util.string_of_int)
in (

let uu____3685 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)" uu____3679 uu____3680 uu____3685))))
in ((uu____3678), (r)))
in FStar_Errors.Error (uu____3675))
in (FStar_Pervasives.raise uu____3674))
end))
end
| uu____3686 -> begin
()
end);
(

let se1 = (

let uu___111_3688 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (((lid), (uvs1), (tps4), (c4), (flags))); FStar_Syntax_Syntax.sigrng = uu___111_3688.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___111_3688.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___111_3688.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___111_3688.FStar_Syntax_Syntax.sigattrs})
in (((se1)::[]), ([])));
)
end))
end))));
)
end))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____3698, uu____3699, uu____3700) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___85_3703 -> (match (uu___85_3703) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____3704 -> begin
false
end)))) -> begin
(([]), ([]))
end
| FStar_Syntax_Syntax.Sig_let (uu____3707, uu____3708) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___85_3713 -> (match (uu___85_3713) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____3714 -> begin
false
end)))) -> begin
(([]), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_range env1 r)
in (

let uu____3721 = (match ((uvs = [])) with
| true -> begin
(

let uu____3722 = (

let uu____3723 = (FStar_Syntax_Util.type_u ())
in (FStar_Pervasives_Native.fst uu____3723))
in (check_and_gen env2 t uu____3722))
end
| uu____3726 -> begin
(

let uu____3727 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____3727) with
| (uvs1, t1) -> begin
(

let t2 = (

let uu____3733 = (

let uu____3734 = (FStar_Syntax_Util.type_u ())
in (FStar_Pervasives_Native.fst uu____3734))
in (tc_check_trivial_guard env2 t1 uu____3733))
in (

let t3 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Beta)::[]) env2 t2)
in (

let uu____3738 = (FStar_Syntax_Subst.close_univ_vars uvs1 t3)
in ((uvs1), (uu____3738)))))
end))
end)
in (match (uu____3721) with
| (uvs1, t1) -> begin
(

let se1 = (

let uu___112_3748 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (uvs1), (t1))); FStar_Syntax_Syntax.sigrng = uu___112_3748.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___112_3748.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___112_3748.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___112_3748.FStar_Syntax_Syntax.sigattrs})
in (((se1)::[]), ([])))
end)))
end
| FStar_Syntax_Syntax.Sig_assume (lid, us, phi) -> begin
(

let uu____3755 = (FStar_Syntax_Subst.open_univ_vars us phi)
in (match (uu____3755) with
| (uu____3762, phi1) -> begin
(

let se1 = (tc_assume env1 lid phi1 se.FStar_Syntax_Syntax.sigquals r)
in (((se1)::[]), ([])))
end))
end
| FStar_Syntax_Syntax.Sig_main (e) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_range env1 r)
in (

let env3 = (FStar_TypeChecker_Env.set_expected_typ env2 FStar_TypeChecker_Common.t_unit)
in (

let uu____3770 = (FStar_TypeChecker_TcTerm.tc_term env3 e)
in (match (uu____3770) with
| (e1, c, g1) -> begin
(

let uu____3781 = (

let uu____3785 = (

let uu____3787 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in FStar_Pervasives_Native.Some (uu____3787))
in (

let uu____3788 = (

let uu____3791 = (c.FStar_Syntax_Syntax.comp ())
in ((e1), (uu____3791)))
in (FStar_TypeChecker_TcTerm.check_expected_effect env3 uu____3785 uu____3788)))
in (match (uu____3781) with
| (e2, uu____3801, g) -> begin
((

let uu____3804 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env3 uu____3804));
(

let se1 = (

let uu___113_3806 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_main (e2); FStar_Syntax_Syntax.sigrng = uu___113_3806.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___113_3806.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___113_3806.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___113_3806.FStar_Syntax_Syntax.sigattrs})
in (((se1)::[]), ([])));
)
end))
end))))
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

let uu____3839 = (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q'))
in (match (uu____3839) with
| true -> begin
FStar_Pervasives_Native.Some (q)
end
| uu____3851 -> begin
(

let uu____3852 = (

let uu____3853 = (

let uu____3856 = (

let uu____3857 = (FStar_Syntax_Print.lid_to_string l)
in (

let uu____3858 = (FStar_Syntax_Print.quals_to_string q)
in (

let uu____3859 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" uu____3857 uu____3858 uu____3859))))
in ((uu____3856), (r)))
in FStar_Errors.Error (uu____3853))
in (FStar_Pervasives.raise uu____3852))
end))
end))
in (

let uu____3862 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.fold_left (fun uu____3893 lb -> (match (uu____3893) with
| (gen1, lbs1, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____3917 = (

let uu____3923 = (FStar_TypeChecker_Env.try_lookup_val_decl env2 lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____3923) with
| FStar_Pervasives_Native.None -> begin
(match ((lb.FStar_Syntax_Syntax.lbunivs <> [])) with
| true -> begin
((false), (lb), (quals_opt))
end
| uu____3944 -> begin
((gen1), (lb), (quals_opt))
end)
end
| FStar_Pervasives_Native.Some ((uvs, tval), quals) -> begin
(

let quals_opt1 = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in ((match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| uu____3967 -> begin
(FStar_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end);
(match (((lb.FStar_Syntax_Syntax.lbunivs <> []) && ((FStar_List.length lb.FStar_Syntax_Syntax.lbunivs) <> (FStar_List.length uvs)))) with
| true -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Inline universes are incoherent with annotation from val declaration"), (r)))))
end
| uu____3978 -> begin
()
end);
(

let uu____3979 = (FStar_Syntax_Syntax.mk_lb ((FStar_Util.Inr (lbname)), (uvs), (FStar_Parser_Const.effect_ALL_lid), (tval), (lb.FStar_Syntax_Syntax.lbdef)))
in ((false), (uu____3979), (quals_opt1)));
))
end))
in (match (uu____3917) with
| (gen2, lb1, quals_opt1) -> begin
((gen2), ((lb1)::lbs1), (quals_opt1))
end)))
end)) ((true), ([]), ((match ((se.FStar_Syntax_Syntax.sigquals = [])) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____4010 -> begin
FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
end)))))
in (match (uu____3862) with
| (should_generalize, lbs', quals_opt) -> begin
(

let quals = (match (quals_opt) with
| FStar_Pervasives_Native.None -> begin
(FStar_Syntax_Syntax.Visible_default)::[]
end
| FStar_Pervasives_Native.Some (q) -> begin
(

let uu____4032 = (FStar_All.pipe_right q (FStar_Util.for_some (fun uu___86_4035 -> (match (uu___86_4035) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| FStar_Syntax_Syntax.Visible_default -> begin
true
end
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____4036 -> begin
false
end))))
in (match (uu____4032) with
| true -> begin
q
end
| uu____4038 -> begin
(FStar_Syntax_Syntax.Visible_default)::q
end))
end)
in (

let lbs'1 = (FStar_List.rev lbs')
in (

let e = (

let uu____4044 = (

let uu____4047 = (

let uu____4048 = (

let uu____4056 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) FStar_Pervasives_Native.None r)
in (((((FStar_Pervasives_Native.fst lbs)), (lbs'1))), (uu____4056)))
in FStar_Syntax_Syntax.Tm_let (uu____4048))
in (FStar_Syntax_Syntax.mk uu____4047))
in (uu____4044 FStar_Pervasives_Native.None r))
in (

let uu____4078 = (

let uu____4084 = (FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term (

let uu___114_4090 = env2
in {FStar_TypeChecker_Env.solver = uu___114_4090.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___114_4090.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___114_4090.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___114_4090.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___114_4090.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___114_4090.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___114_4090.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___114_4090.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___114_4090.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___114_4090.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___114_4090.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = uu___114_4090.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = uu___114_4090.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___114_4090.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___114_4090.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___114_4090.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___114_4090.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___114_4090.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___114_4090.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___114_4090.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___114_4090.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___114_4090.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___114_4090.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___114_4090.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___114_4090.FStar_TypeChecker_Env.is_native_tactic}) e)
in (match (uu____4084) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs1, e1); FStar_Syntax_Syntax.tk = uu____4098; FStar_Syntax_Syntax.pos = uu____4099; FStar_Syntax_Syntax.vars = uu____4100}, uu____4101, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals1 = (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (uu____4120, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| uu____4125 -> begin
quals
end)
in (

let quals2 = (FStar_List.choose (fun uu___87_4130 -> (match (uu___87_4130) with
| FStar_Syntax_Syntax.Inline_for_extraction -> begin
(

let uu____4132 = (

let uu____4133 = (FStar_List.for_all (fun lb -> (

let ok = (FStar_Syntax_Util.is_pure_or_ghost_function lb.FStar_Syntax_Syntax.lbtyp)
in ((match ((not (ok))) with
| true -> begin
(

let uu____4140 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (FStar_Util.print1_warning "Dropping inline_for_extraction from %s because it is not a pure function\n" uu____4140))
end
| uu____4141 -> begin
()
end);
ok;
))) (FStar_Pervasives_Native.snd lbs1))
in (not (uu____4133)))
in (match (uu____4132) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____4144 -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Inline_for_extraction)
end))
end
| q -> begin
FStar_Pervasives_Native.Some (q)
end)) quals1)
in (((

let uu___115_4150 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((lbs1), (lids))); FStar_Syntax_Syntax.sigrng = uu___115_4150.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = uu___115_4150.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___115_4150.FStar_Syntax_Syntax.sigattrs})), (lbs1))))
end
| uu____4155 -> begin
(failwith "impossible")
end))
in (match (uu____4078) with
| (se1, lbs1) -> begin
((FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1) (FStar_List.iter (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (FStar_TypeChecker_Common.insert_fv fv lb.FStar_Syntax_Syntax.lbtyp)))));
(

let uu____4184 = (log env2)
in (match (uu____4184) with
| true -> begin
(

let uu____4185 = (

let uu____4186 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1) (FStar_List.map (fun lb -> (

let should_log = (

let uu____4197 = (

let uu____4202 = (

let uu____4203 = (

let uu____4205 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____4205.FStar_Syntax_Syntax.fv_name)
in uu____4203.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env2 uu____4202))
in (match (uu____4197) with
| FStar_Pervasives_Native.None -> begin
true
end
| uu____4209 -> begin
false
end))
in (match (should_log) with
| true -> begin
(

let uu____4214 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____4215 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" uu____4214 uu____4215)))
end
| uu____4216 -> begin
""
end)))))
in (FStar_All.pipe_right uu____4186 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" uu____4185))
end
| uu____4218 -> begin
()
end));
(

let reified_tactic_type = (fun l t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____4239 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____4239) with
| (bs1, c1) -> begin
(

let uu____4244 = (FStar_Syntax_Util.is_total_comp c1)
in (match (uu____4244) with
| true -> begin
(

let c' = (match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t', u) -> begin
(

let uu____4254 = (

let uu____4255 = (FStar_Syntax_Subst.compress t')
in uu____4255.FStar_Syntax_Syntax.n)
in (match (uu____4254) with
| FStar_Syntax_Syntax.Tm_app (h, args) -> begin
(

let uu____4274 = (

let uu____4275 = (FStar_Syntax_Subst.compress h)
in uu____4275.FStar_Syntax_Syntax.n)
in (match (uu____4274) with
| FStar_Syntax_Syntax.Tm_uinst (h', u') -> begin
(

let h'' = (

let uu____4285 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.u_tac_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm uu____4285))
in (

let uu____4286 = (

let uu____4287 = (

let uu____4288 = (FStar_Syntax_Syntax.mk_Tm_uinst h'' u')
in (FStar_Syntax_Syntax.mk_Tm_app uu____4288 args))
in (uu____4287 FStar_Pervasives_Native.None t'.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Syntax.mk_Total' uu____4286 u)))
end
| uu____4293 -> begin
c1
end))
end
| uu____4294 -> begin
c1
end))
end
| uu____4295 -> begin
c1
end)
in (

let uu___116_4296 = t1
in (

let uu____4297 = (

let uu____4298 = (

let uu____4306 = (FStar_Syntax_Subst.close_comp bs1 c')
in ((bs1), (uu____4306)))
in FStar_Syntax_Syntax.Tm_arrow (uu____4298))
in {FStar_Syntax_Syntax.n = uu____4297; FStar_Syntax_Syntax.tk = uu___116_4296.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___116_4296.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___116_4296.FStar_Syntax_Syntax.vars})))
end
| uu____4311 -> begin
t1
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (h, args) -> begin
(

let uu____4328 = (

let uu____4329 = (FStar_Syntax_Subst.compress h)
in uu____4329.FStar_Syntax_Syntax.n)
in (match (uu____4328) with
| FStar_Syntax_Syntax.Tm_uinst (h', u') -> begin
(

let h'' = (

let uu____4339 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.u_tac_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm uu____4339))
in (

let uu____4340 = (

let uu____4341 = (FStar_Syntax_Syntax.mk_Tm_uinst h'' u')
in (FStar_Syntax_Syntax.mk_Tm_app uu____4341 args))
in (uu____4340 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)))
end
| uu____4346 -> begin
t1
end))
end
| uu____4347 -> begin
t1
end)))
in (

let reified_tactic_decl = (fun assm_lid lb -> (

let t = (reified_tactic_type assm_lid lb.FStar_Syntax_Syntax.lbtyp)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((assm_lid), (lb.FStar_Syntax_Syntax.lbunivs), (t))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid assm_lid); FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::[]; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))
in (

let reflected_tactic_decl = (fun b lb bs assm_lid comp -> (

let reified_tac = (

let uu____4374 = (FStar_Syntax_Syntax.lid_as_fv assm_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm uu____4374))
in (

let tac_args = (FStar_List.map (fun x -> (

let uu____4385 = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst x))
in ((uu____4385), ((FStar_Pervasives_Native.snd x))))) bs)
in (

let reflect_head = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (FStar_Parser_Const.tac_effect_lid))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let refl_arg = (FStar_Syntax_Syntax.mk_Tm_app reified_tac tac_args FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let app = (FStar_Syntax_Syntax.mk_Tm_app reflect_head ((((refl_arg), (FStar_Pervasives_Native.None)))::[]) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let unit_binder = (

let uu____4417 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____4417))
in (

let body = (FStar_All.pipe_left (FStar_Syntax_Util.abs ((unit_binder)::[]) app) (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp comp))))
in (

let func = (FStar_All.pipe_left (FStar_Syntax_Util.abs bs body) (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp comp))))
in (

let uu___117_4422 = se1
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((b), (((

let uu___118_4429 = lb
in {FStar_Syntax_Syntax.lbname = uu___118_4429.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___118_4429.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___118_4429.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___118_4429.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = func}))::[]))), (lids))); FStar_Syntax_Syntax.sigrng = uu___117_4422.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___117_4422.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___117_4422.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___117_4422.FStar_Syntax_Syntax.sigattrs}))))))))))
in (

let tactic_decls = (match ((FStar_Pervasives_Native.snd lbs1)) with
| (hd1)::[] -> begin
(

let uu____4439 = (FStar_Syntax_Util.arrow_formals_comp hd1.FStar_Syntax_Syntax.lbtyp)
in (match (uu____4439) with
| (bs, comp) -> begin
(

let t = (FStar_Syntax_Util.comp_result comp)
in (

let uu____4459 = (

let uu____4460 = (FStar_Syntax_Subst.compress t)
in uu____4460.FStar_Syntax_Syntax.n)
in (match (uu____4459) with
| FStar_Syntax_Syntax.Tm_app (h, args) -> begin
(

let h1 = (FStar_Syntax_Subst.compress h)
in (

let tac_lid = (

let uu____4484 = (

let uu____4486 = (FStar_Util.right hd1.FStar_Syntax_Syntax.lbname)
in uu____4486.FStar_Syntax_Syntax.fv_name)
in uu____4484.FStar_Syntax_Syntax.v)
in (

let assm_lid = (

let uu____4488 = (FStar_All.pipe_left FStar_Ident.id_of_text (Prims.strcat "__" tac_lid.FStar_Ident.ident.FStar_Ident.idText))
in (FStar_Ident.lid_of_ns_and_id tac_lid.FStar_Ident.ns uu____4488))
in (

let uu____4489 = ((is_native_tactic env2 assm_lid h1) && (

let uu____4491 = (

let uu____4492 = (FStar_TypeChecker_Env.try_lookup_val_decl env2 tac_lid)
in (FStar_All.pipe_left FStar_Util.is_some uu____4492))
in (not (uu____4491))))
in (match (uu____4489) with
| true -> begin
(

let se_assm = (reified_tactic_decl assm_lid hd1)
in (

let se_refl = (reflected_tactic_decl (FStar_Pervasives_Native.fst lbs1) hd1 bs assm_lid comp)
in FStar_Pervasives_Native.Some (((se_assm), (se_refl)))))
end
| uu____4512 -> begin
FStar_Pervasives_Native.None
end)))))
end
| uu____4515 -> begin
FStar_Pervasives_Native.None
end)))
end))
end
| uu____4518 -> begin
FStar_Pervasives_Native.None
end)
in (match (tactic_decls) with
| FStar_Pervasives_Native.Some (se_assm, se_refl) -> begin
((

let uu____4531 = (FStar_TypeChecker_Env.debug env2 (FStar_Options.Other ("NativeTactics")))
in (match (uu____4531) with
| true -> begin
(

let uu____4532 = (FStar_Syntax_Print.sigelt_to_string se_assm)
in (

let uu____4533 = (FStar_Syntax_Print.sigelt_to_string se_refl)
in (FStar_Util.print2 "Native tactic declarations: \n%s\n%s\n" uu____4532 uu____4533)))
end
| uu____4534 -> begin
()
end));
(((se_assm)::(se_refl)::[]), ([]));
)
end
| FStar_Pervasives_Native.None -> begin
(((se1)::[]), ([]))
end)))));
)
end)))))
end))))
end));
)))


let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___88_4567 -> (match (uu___88_4567) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| uu____4568 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| FStar_Syntax_Syntax.Projector (l, uu____4574) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| FStar_Syntax_Syntax.Discriminator (l) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| uu____4578 -> begin
false
end))
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_pragma (uu____4583) -> begin
(([]), (hidden))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____4586) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____4599) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____4612) -> begin
(

let uu____4617 = (is_abstract se.FStar_Syntax_Syntax.sigquals)
in (match (uu____4617) with
| true -> begin
(

let for_export_bundle = (fun se1 uu____4636 -> (match (uu____4636) with
| (out, hidden1) -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, uu____4659, uu____4660) -> begin
(

let dec = (

let uu___119_4666 = se1
in (

let uu____4667 = (

let uu____4668 = (

let uu____4672 = (

let uu____4675 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow bs uu____4675))
in ((l), (us), (uu____4672)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____4668))
in {FStar_Syntax_Syntax.sigel = uu____4667; FStar_Syntax_Syntax.sigrng = uu___119_4666.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::se1.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___119_4666.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___119_4666.FStar_Syntax_Syntax.sigattrs}))
in (((dec)::out), (hidden1)))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, uu____4685, uu____4686, uu____4687) -> begin
(

let dec = (

let uu___120_4691 = se1
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t))); FStar_Syntax_Syntax.sigrng = uu___120_4691.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::[]; FStar_Syntax_Syntax.sigmeta = uu___120_4691.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___120_4691.FStar_Syntax_Syntax.sigattrs})
in (((dec)::out), ((l)::hidden1)))
end
| uu____4694 -> begin
((out), (hidden1))
end)
end))
in (FStar_List.fold_right for_export_bundle ses (([]), (hidden))))
end
| uu____4703 -> begin
(((se)::[]), (hidden))
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____4706, uu____4707, uu____4708) -> begin
(

let uu____4709 = (is_abstract se.FStar_Syntax_Syntax.sigquals)
in (match (uu____4709) with
| true -> begin
(([]), (hidden))
end
| uu____4716 -> begin
(((se)::[]), (hidden))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, us, t) -> begin
(

let uu____4722 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some is_hidden_proj_or_disc))
in (match (uu____4722) with
| true -> begin
((((

let uu___121_4731 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t))); FStar_Syntax_Syntax.sigrng = uu___121_4731.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::[]; FStar_Syntax_Syntax.sigmeta = uu___121_4731.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___121_4731.FStar_Syntax_Syntax.sigattrs}))::[]), ((l)::hidden))
end
| uu____4732 -> begin
(

let uu____4733 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___89_4736 -> (match (uu___89_4736) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____4737) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____4740) -> begin
true
end
| uu____4741 -> begin
false
end))))
in (match (uu____4733) with
| true -> begin
(((se)::[]), (hidden))
end
| uu____4748 -> begin
(([]), (hidden))
end))
end))
end
| FStar_Syntax_Syntax.Sig_main (uu____4751) -> begin
(([]), (hidden))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____4754) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____4757) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____4760) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____4763) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____4773) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____4783 = (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
in (match (uu____4783) with
| true -> begin
(([]), (hidden))
end
| uu____4791 -> begin
(

let dec = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::[]; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (((dec)::[]), ((lid)::hidden)))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, l) -> begin
(

let uu____4802 = (is_abstract se.FStar_Syntax_Syntax.sigquals)
in (match (uu____4802) with
| true -> begin
(

let uu____4807 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let uu___122_4816 = se
in (

let uu____4817 = (

let uu____4818 = (

let uu____4822 = (

let uu____4823 = (

let uu____4825 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____4825.FStar_Syntax_Syntax.fv_name)
in uu____4823.FStar_Syntax_Syntax.v)
in ((uu____4822), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____4818))
in {FStar_Syntax_Syntax.sigel = uu____4817; FStar_Syntax_Syntax.sigrng = uu___122_4816.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___122_4816.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___122_4816.FStar_Syntax_Syntax.sigattrs})))))
in ((uu____4807), (hidden)))
end
| uu____4831 -> begin
(((se)::[]), (hidden))
end))
end))))


let add_sigelt_to_env : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____4842) -> begin
(failwith "add_sigelt_to_env: Impossible, bare data constructor")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____4851) -> begin
(failwith "add_sigelt_to_env: Impossible, bare data constructor")
end
| FStar_Syntax_Syntax.Sig_pragma (p) -> begin
(match (p) with
| FStar_Syntax_Syntax.ResetOptions (uu____4860) -> begin
((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
(

let uu____4863 = (FStar_Options.using_facts_from ())
in (match (uu____4863) with
| FStar_Pervasives_Native.Some (ns) -> begin
(

let proof_ns = (

let uu____4875 = (

let uu____4880 = (FStar_List.map (fun s -> (((FStar_Ident.path_of_text s)), (true))) ns)
in (FStar_List.append uu____4880 (((([]), (false)))::[])))
in (uu____4875)::[])
in (

let uu___123_4909 = env
in {FStar_TypeChecker_Env.solver = uu___123_4909.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___123_4909.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___123_4909.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___123_4909.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___123_4909.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___123_4909.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___123_4909.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___123_4909.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___123_4909.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___123_4909.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___123_4909.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___123_4909.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___123_4909.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___123_4909.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___123_4909.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___123_4909.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___123_4909.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___123_4909.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___123_4909.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___123_4909.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___123_4909.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___123_4909.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___123_4909.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___123_4909.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = proof_ns; FStar_TypeChecker_Env.synth = uu___123_4909.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___123_4909.FStar_TypeChecker_Env.is_native_tactic}))
end
| FStar_Pervasives_Native.None -> begin
env
end));
)
end
| uu____4911 -> begin
env
end)
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____4912) -> begin
env
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_sigelt env se)
in (FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun env2 a -> (

let uu____4921 = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a)
in (FStar_TypeChecker_Env.push_sigelt env2 uu____4921))) env1)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____4922, uu____4923, uu____4924) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___90_4927 -> (match (uu___90_4927) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____4928 -> begin
false
end)))) -> begin
env
end
| FStar_Syntax_Syntax.Sig_let (uu____4929, uu____4930) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___90_4935 -> (match (uu___90_4935) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____4936 -> begin
false
end)))) -> begin
env
end
| uu____4937 -> begin
(FStar_TypeChecker_Env.push_sigelt env se)
end))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let rec process_one_decl = (fun uu____4975 se -> (match (uu____4975) with
| (ses1, exports, env1, hidden) -> begin
((

let uu____5005 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____5005) with
| true -> begin
(

let uu____5006 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____5006))
end
| uu____5007 -> begin
()
end));
(

let uu____5008 = (tc_decl env1 se)
in (match (uu____5008) with
| (ses', ses_elaborated) -> begin
(

let ses'1 = (FStar_All.pipe_right ses' (FStar_List.map (fun se1 -> ((

let uu____5037 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("UF")))
in (match (uu____5037) with
| true -> begin
(

let uu____5038 = (FStar_Syntax_Print.sigelt_to_string se1)
in (FStar_Util.print1 "About to elim vars from %s" uu____5038))
end
| uu____5039 -> begin
()
end));
(FStar_TypeChecker_Normalize.elim_uvars env1 se1);
))))
in (

let ses_elaborated1 = (FStar_All.pipe_right ses_elaborated (FStar_List.map (fun se1 -> (FStar_TypeChecker_Normalize.elim_uvars env1 se1))))
in (

let env2 = (FStar_All.pipe_right ses'1 (FStar_List.fold_left (fun env2 se1 -> (add_sigelt_to_env env2 se1)) env1))
in ((FStar_Syntax_Unionfind.reset ());
(

let uu____5054 = ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("LogTypes"))))
in (match (uu____5054) with
| true -> begin
(

let uu____5055 = (FStar_List.fold_left (fun s se1 -> (

let uu____5061 = (

let uu____5062 = (FStar_Syntax_Print.sigelt_to_string se1)
in (Prims.strcat uu____5062 "\n"))
in (Prims.strcat s uu____5061))) "" ses'1)
in (FStar_Util.print1 "Checked: %s\n" uu____5055))
end
| uu____5063 -> begin
()
end));
(FStar_List.iter (fun se1 -> (env2.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env2 se1)) ses'1);
(

let uu____5067 = (

let accum_exports_hidden = (fun uu____5085 se1 -> (match (uu____5085) with
| (exports1, hidden1) -> begin
(

let uu____5101 = (for_export hidden1 se1)
in (match (uu____5101) with
| (se_exported, hidden2) -> begin
(((FStar_List.rev_append se_exported exports1)), (hidden2))
end))
end))
in (FStar_List.fold_left accum_exports_hidden ((exports), (hidden)) ses'1))
in (match (uu____5067) with
| (exports1, hidden1) -> begin
(

let ses'2 = (FStar_List.map (fun s -> (

let uu___124_5145 = s
in {FStar_Syntax_Syntax.sigel = uu___124_5145.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___124_5145.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___124_5145.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___124_5145.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = se.FStar_Syntax_Syntax.sigattrs})) ses'1)
in (((((FStar_List.rev_append ses'2 ses1)), (exports1), (env2), (hidden1))), (ses_elaborated1)))
end));
))))
end));
)
end))
in (

let process_one_decl_timed = (fun acc se -> (

let uu____5188 = acc
in (match (uu____5188) with
| (uu____5206, uu____5207, env1, uu____5209) -> begin
(

let uu____5216 = (FStar_Util.record_time (fun uu____5240 -> (process_one_decl acc se)))
in (match (uu____5216) with
| (r, ms_elapsed) -> begin
((

let uu____5274 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("TCDeclTime")))
in (match (uu____5274) with
| true -> begin
(

let uu____5275 = (FStar_Syntax_Print.sigelt_to_string_short se)
in (

let uu____5276 = (FStar_Util.string_of_int ms_elapsed)
in (FStar_Util.print2 "Checked %s in %s milliseconds\n" uu____5275 uu____5276)))
end
| uu____5277 -> begin
()
end));
r;
)
end))
end)))
in (

let uu____5278 = (FStar_Util.fold_flatten process_one_decl_timed (([]), ([]), (env), ([])) ses)
in (match (uu____5278) with
| (ses1, exports, env1, uu____5304) -> begin
(((FStar_List.rev_append ses1 [])), ((FStar_List.rev_append exports [])), (env1))
end)))))


let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (

let verify = (FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let action = (match (verify) with
| true -> begin
"Verifying"
end
| uu____5327 -> begin
"Lax-checking"
end)
in (

let label1 = (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____5329 -> begin
"implementation"
end)
in ((

let uu____5331 = (FStar_Options.debug_any ())
in (match (uu____5331) with
| true -> begin
(FStar_Util.print3 "%s %s of %s\n" action label1 modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
end
| uu____5332 -> begin
()
end));
(

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____5334 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let msg = (Prims.strcat "Internals for " name)
in (

let env1 = (

let uu___125_5337 = env
in {FStar_TypeChecker_Env.solver = uu___125_5337.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___125_5337.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___125_5337.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___125_5337.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___125_5337.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___125_5337.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___125_5337.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___125_5337.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___125_5337.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___125_5337.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___125_5337.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___125_5337.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___125_5337.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___125_5337.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___125_5337.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___125_5337.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = (not (verify)); FStar_TypeChecker_Env.lax = uu___125_5337.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___125_5337.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___125_5337.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___125_5337.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___125_5337.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___125_5337.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___125_5337.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___125_5337.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___125_5337.FStar_TypeChecker_Env.is_native_tactic})
in ((env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg);
(

let env2 = (FStar_TypeChecker_Env.set_current_module env1 modul.FStar_Syntax_Syntax.name)
in (

let uu____5340 = (tc_decls env2 modul.FStar_Syntax_Syntax.declarations)
in (match (uu____5340) with
| (ses, exports, env3) -> begin
(((

let uu___126_5359 = modul
in {FStar_Syntax_Syntax.name = uu___126_5359.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = uu___126_5359.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___126_5359.FStar_Syntax_Syntax.is_interface})), (exports), (env3))
end)));
))));
)))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let uu____5378 = (tc_decls env decls)
in (match (uu____5378) with
| (ses, exports, env1) -> begin
(

let modul1 = (

let uu___127_5396 = modul
in {FStar_Syntax_Syntax.name = uu___127_5396.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = uu___127_5396.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___127_5396.FStar_Syntax_Syntax.is_interface})
in ((modul1), (exports), (env1)))
end)))


let check_exports : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env modul exports -> (

let env1 = (

let uu___128_5413 = env
in {FStar_TypeChecker_Env.solver = uu___128_5413.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___128_5413.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___128_5413.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___128_5413.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___128_5413.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___128_5413.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___128_5413.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___128_5413.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___128_5413.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___128_5413.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___128_5413.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___128_5413.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___128_5413.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = uu___128_5413.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___128_5413.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___128_5413.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___128_5413.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = true; FStar_TypeChecker_Env.type_of = uu___128_5413.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___128_5413.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___128_5413.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___128_5413.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___128_5413.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___128_5413.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___128_5413.FStar_TypeChecker_Env.is_native_tactic})
in (

let check_term = (fun lid univs1 t -> (

let uu____5424 = (FStar_Syntax_Subst.open_univ_vars univs1 t)
in (match (uu____5424) with
| (univs2, t1) -> begin
((

let uu____5430 = (

let uu____5431 = (

let uu____5434 = (FStar_TypeChecker_Env.set_current_module env1 modul.FStar_Syntax_Syntax.name)
in (FStar_TypeChecker_Env.debug uu____5434))
in (FStar_All.pipe_left uu____5431 (FStar_Options.Other ("Exports"))))
in (match (uu____5430) with
| true -> begin
(

let uu____5435 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____5436 = (

let uu____5437 = (FStar_All.pipe_right univs2 (FStar_List.map (fun x -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (x))))))
in (FStar_All.pipe_right uu____5437 (FStar_String.concat ", ")))
in (

let uu____5443 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Checking for export %s <%s> : %s\n" uu____5435 uu____5436 uu____5443))))
end
| uu____5444 -> begin
()
end));
(

let env2 = (FStar_TypeChecker_Env.push_univ_vars env1 univs2)
in (

let uu____5446 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1)
in (FStar_All.pipe_right uu____5446 FStar_Pervasives.ignore)));
)
end)))
in (

let check_term1 = (fun lid univs1 t -> ((

let uu____5464 = (

let uu____5465 = (FStar_Syntax_Print.lid_to_string modul.FStar_Syntax_Syntax.name)
in (

let uu____5466 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Interface of %s violates its abstraction (add a \'private\' qualifier to \'%s\'?)" uu____5465 uu____5466)))
in (FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____5464));
(check_term lid univs1 t);
(FStar_Errors.message_prefix.FStar_Errors.clear_prefix ());
))
in (

let rec check_sigelt = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____5473) -> begin
(

let uu____5478 = (

let uu____5479 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____5479)))
in (match (uu____5478) with
| true -> begin
(FStar_All.pipe_right ses (FStar_List.iter check_sigelt))
end
| uu____5482 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (l, univs1, binders, typ, uu____5487, uu____5488) -> begin
(

let t = (

let uu____5496 = (

let uu____5499 = (

let uu____5500 = (

let uu____5508 = (FStar_Syntax_Syntax.mk_Total typ)
in ((binders), (uu____5508)))
in FStar_Syntax_Syntax.Tm_arrow (uu____5500))
in (FStar_Syntax_Syntax.mk uu____5499))
in (uu____5496 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng))
in (check_term1 l univs1 t))
end
| FStar_Syntax_Syntax.Sig_datacon (l, univs1, t, uu____5520, uu____5521, uu____5522) -> begin
(check_term1 l univs1 t)
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, univs1, t) -> begin
(

let uu____5528 = (

let uu____5529 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____5529)))
in (match (uu____5528) with
| true -> begin
(check_term1 l univs1 t)
end
| uu____5531 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_let ((uu____5532, lbs), uu____5534) -> begin
(

let uu____5542 = (

let uu____5543 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____5543)))
in (match (uu____5542) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (check_term1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp)))))
end
| uu____5550 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs1, binders, comp, flags) -> begin
(

let uu____5558 = (

let uu____5559 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____5559)))
in (match (uu____5558) with
| true -> begin
(

let arrow1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))) FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng)
in (check_term1 l univs1 arrow1))
end
| uu____5568 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_main (uu____5569) -> begin
()
end
| FStar_Syntax_Syntax.Sig_assume (uu____5570) -> begin
()
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____5574) -> begin
()
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____5575) -> begin
()
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____5576) -> begin
()
end
| FStar_Syntax_Syntax.Sig_pragma (uu____5577) -> begin
()
end))
in (match ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Parser_Const.prims_lid)) with
| true -> begin
()
end
| uu____5578 -> begin
(FStar_List.iter check_sigelt exports)
end))))))


let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (

let modul1 = (

let uu___129_5594 = modul
in {FStar_Syntax_Syntax.name = uu___129_5594.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu___129_5594.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env1 = (FStar_TypeChecker_Env.finish_module env modul1)
in ((

let uu____5597 = (

let uu____5598 = (FStar_Options.lax ())
in (not (uu____5598)))
in (match (uu____5597) with
| true -> begin
(check_exports env1 modul1 exports)
end
| uu____5599 -> begin
()
end));
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul1.FStar_Syntax_Syntax.name.FStar_Ident.str));
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env1 modul1);
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
(

let uu____5604 = (

let uu____5605 = (FStar_Options.interactive ())
in (not (uu____5605)))
in (match (uu____5604) with
| true -> begin
(

let uu____5606 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right uu____5606 FStar_Pervasives.ignore))
end
| uu____5607 -> begin
()
end));
((modul1), (env1));
))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let uu____5618 = (tc_partial_modul env modul)
in (match (uu____5618) with
| (modul1, non_private_decls, env1) -> begin
(finish_partial_modul env1 modul1 non_private_decls)
end)))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> ((

let uu____5641 = (FStar_Options.debug_any ())
in (match (uu____5641) with
| true -> begin
(

let uu____5642 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (match (m.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"i\'face"
end
| uu____5643 -> begin
"module"
end) uu____5642))
end
| uu____5644 -> begin
()
end));
(

let env1 = (

let uu___130_5646 = env
in (

let uu____5647 = (

let uu____5648 = (FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (not (uu____5648)))
in {FStar_TypeChecker_Env.solver = uu___130_5646.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___130_5646.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___130_5646.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___130_5646.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___130_5646.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___130_5646.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___130_5646.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___130_5646.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___130_5646.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___130_5646.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___130_5646.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___130_5646.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___130_5646.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___130_5646.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___130_5646.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___130_5646.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___130_5646.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___130_5646.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu____5647; FStar_TypeChecker_Env.lax_universes = uu___130_5646.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___130_5646.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___130_5646.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___130_5646.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___130_5646.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___130_5646.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___130_5646.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___130_5646.FStar_TypeChecker_Env.is_native_tactic}))
in (

let uu____5649 = (tc_modul env1 m)
in (match (uu____5649) with
| (m1, env2) -> begin
((

let uu____5657 = (FStar_Options.dump_module m1.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____5657) with
| true -> begin
(

let uu____5658 = (FStar_Syntax_Print.modul_to_string m1)
in (FStar_Util.print1 "%s\n" uu____5658))
end
| uu____5659 -> begin
()
end));
(

let uu____5661 = ((FStar_Options.dump_module m1.FStar_Syntax_Syntax.name.FStar_Ident.str) && (FStar_Options.debug_at_level m1.FStar_Syntax_Syntax.name.FStar_Ident.str (FStar_Options.Other ("Normalize"))))
in (match (uu____5661) with
| true -> begin
(

let normalize_toplevel_lets = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((b, lbs), ids) -> begin
(

let n1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]))
in (

let update = (fun lb -> (

let uu____5685 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____5685) with
| (univnames1, e) -> begin
(

let uu___131_5690 = lb
in (

let uu____5691 = (

let uu____5694 = (FStar_TypeChecker_Env.push_univ_vars env2 univnames1)
in (n1 uu____5694 e))
in {FStar_Syntax_Syntax.lbname = uu___131_5690.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___131_5690.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___131_5690.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___131_5690.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____5691}))
end)))
in (

let uu___132_5695 = se
in (

let uu____5696 = (

let uu____5697 = (

let uu____5701 = (

let uu____5705 = (FStar_List.map update lbs)
in ((b), (uu____5705)))
in ((uu____5701), (ids)))
in FStar_Syntax_Syntax.Sig_let (uu____5697))
in {FStar_Syntax_Syntax.sigel = uu____5696; FStar_Syntax_Syntax.sigrng = uu___132_5695.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___132_5695.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___132_5695.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___132_5695.FStar_Syntax_Syntax.sigattrs}))))
end
| uu____5712 -> begin
se
end))
in (

let normalized_module = (

let uu___133_5714 = m1
in (

let uu____5715 = (FStar_List.map normalize_toplevel_lets m1.FStar_Syntax_Syntax.declarations)
in {FStar_Syntax_Syntax.name = uu___133_5714.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu____5715; FStar_Syntax_Syntax.exports = uu___133_5714.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___133_5714.FStar_Syntax_Syntax.is_interface}))
in (

let uu____5716 = (FStar_Syntax_Print.modul_to_string normalized_module)
in (FStar_Util.print1 "%s\n" uu____5716))))
end
| uu____5717 -> begin
()
end));
((m1), (env2));
)
end)));
))




