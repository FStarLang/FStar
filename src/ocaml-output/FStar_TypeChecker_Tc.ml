
open Prims
open FStar_Pervasives

let set_hint_correlator : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env = (fun env se -> (

let uu____9 = (FStar_Options.reuse_hint_for ())
in (match (uu____9) with
| FStar_Pervasives_Native.Some (l) -> begin
(

let lid = (

let uu____14 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_add_suffix uu____14 l))
in (

let uu___113_15 = env
in {FStar_TypeChecker_Env.solver = uu___113_15.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___113_15.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___113_15.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___113_15.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___113_15.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___113_15.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___113_15.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___113_15.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___113_15.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___113_15.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___113_15.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___113_15.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___113_15.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___113_15.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___113_15.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___113_15.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___113_15.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___113_15.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___113_15.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___113_15.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___113_15.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___113_15.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___113_15.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___113_15.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___113_15.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___113_15.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = FStar_Pervasives_Native.Some (((lid), ((Prims.parse_int "0")))); FStar_TypeChecker_Env.proof_ns = uu___113_15.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___113_15.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___113_15.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___113_15.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___113_15.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___113_15.FStar_TypeChecker_Env.dsenv}))
end
| FStar_Pervasives_Native.None -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (

let lid = (match (lids) with
| [] -> begin
(

let uu____24 = (FStar_TypeChecker_Env.current_module env)
in (

let uu____25 = (

let uu____26 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_right uu____26 FStar_Util.string_of_int))
in (FStar_Ident.lid_add_suffix uu____24 uu____25)))
end
| (l)::uu____28 -> begin
l
end)
in (

let uu___114_31 = env
in {FStar_TypeChecker_Env.solver = uu___114_31.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___114_31.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___114_31.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___114_31.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___114_31.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___114_31.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___114_31.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___114_31.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___114_31.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___114_31.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___114_31.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___114_31.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___114_31.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___114_31.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___114_31.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___114_31.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___114_31.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___114_31.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___114_31.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___114_31.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___114_31.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___114_31.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___114_31.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___114_31.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___114_31.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___114_31.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = FStar_Pervasives_Native.Some (((lid), ((Prims.parse_int "0")))); FStar_TypeChecker_Env.proof_ns = uu___114_31.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___114_31.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___114_31.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___114_31.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___114_31.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___114_31.FStar_TypeChecker_Env.dsenv})))
end)))


let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_Options.log_types ()) && (

let uu____41 = (

let uu____42 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____42))
in (not (uu____41)))))


let get_tactic_fv : 'Auu____51 . 'Auu____51  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv FStar_Pervasives_Native.option = (fun env tac_lid h -> (match (h.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h', uu____67) -> begin
(

let uu____72 = (

let uu____73 = (FStar_Syntax_Subst.compress h')
in uu____73.FStar_Syntax_Syntax.n)
in (match (uu____72) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.tactic_lid) -> begin
FStar_Pervasives_Native.Some (fv)
end
| uu____79 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____80 -> begin
FStar_Pervasives_Native.None
end))


let is_builtin_tactic : FStar_Ident.lident  ->  Prims.bool = (fun md -> (

let path = (FStar_Ident.path_of_lid md)
in (match (((FStar_List.length path) > (Prims.parse_int "2"))) with
| true -> begin
(

let uu____88 = (

let uu____91 = (FStar_List.splitAt (Prims.parse_int "2") path)
in (FStar_Pervasives_Native.fst uu____91))
in (match (uu____88) with
| ("FStar")::("Tactics")::[] -> begin
true
end
| ("FStar")::("Reflection")::[] -> begin
true
end
| uu____104 -> begin
false
end))
end
| uu____107 -> begin
false
end)))


let user_tactics_modules : Prims.string Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let uu____144 = (FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k)
in (match (uu____144) with
| (t1, c, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
t1;
)
end)))


let recheck_debug : Prims.string  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s env t -> ((

let uu____168 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____168) with
| true -> begin
(

let uu____169 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Term has been %s-transformed to:\n%s\n----------\n" s uu____169))
end
| uu____170 -> begin
()
end));
(

let uu____171 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (uu____171) with
| (t', uu____179, uu____180) -> begin
((

let uu____182 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____182) with
| true -> begin
(

let uu____183 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print1 "Re-checked; got:\n%s\n----------\n" uu____183))
end
| uu____184 -> begin
()
end));
t;
)
end));
))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (

let uu____197 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env uu____197)))


let check_nogen : 'Auu____206 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  ('Auu____206 Prims.list * FStar_Syntax_Syntax.term) = (fun env t k -> (

let t1 = (tc_check_trivial_guard env t k)
in (

let uu____226 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t1)
in (([]), (uu____226)))))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun env m s -> (

let fail = (fun uu____256 -> (

let uu____257 = (

let uu____258 = (

let uu____263 = (FStar_TypeChecker_Err.unexpected_signature_for_monad env m s)
in ((uu____263), ((FStar_Ident.range_of_lid m))))
in FStar_Errors.Error (uu____258))
in (FStar_Exn.raise uu____257)))
in (

let s1 = (FStar_Syntax_Subst.compress s)
in (match (s1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs1 = (FStar_Syntax_Subst.open_binders bs)
in (match (bs1) with
| ((a, uu____303))::((wp, uu____305))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____320 -> begin
(fail ())
end))
end
| uu____321 -> begin
(fail ())
end))))


let tc_eff_decl : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (

let uu____333 = (FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____333) with
| (effect_params_un, signature_un, opening) -> begin
(

let uu____343 = (FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un)
in (match (uu____343) with
| (effect_params, env, uu____352) -> begin
(

let uu____353 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (uu____353) with
| (signature, uu____359) -> begin
(

let ed1 = (

let uu___115_361 = ed
in {FStar_Syntax_Syntax.cattributes = uu___115_361.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___115_361.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___115_361.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = uu___115_361.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = uu___115_361.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = uu___115_361.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = uu___115_361.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = uu___115_361.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = uu___115_361.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = uu___115_361.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = uu___115_361.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = uu___115_361.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = uu___115_361.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = uu___115_361.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = uu___115_361.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = uu___115_361.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = uu___115_361.FStar_Syntax_Syntax.actions})
in (

let ed2 = (match (effect_params) with
| [] -> begin
ed1
end
| uu____367 -> begin
(

let op = (fun ts -> (

let t1 = (FStar_Syntax_Subst.subst opening (FStar_Pervasives_Native.snd ts))
in (([]), (t1))))
in (

let uu___116_398 = ed1
in (

let uu____399 = (op ed1.FStar_Syntax_Syntax.ret_wp)
in (

let uu____400 = (op ed1.FStar_Syntax_Syntax.bind_wp)
in (

let uu____401 = (op ed1.FStar_Syntax_Syntax.if_then_else)
in (

let uu____402 = (op ed1.FStar_Syntax_Syntax.ite_wp)
in (

let uu____403 = (op ed1.FStar_Syntax_Syntax.stronger)
in (

let uu____404 = (op ed1.FStar_Syntax_Syntax.close_wp)
in (

let uu____405 = (op ed1.FStar_Syntax_Syntax.assert_p)
in (

let uu____406 = (op ed1.FStar_Syntax_Syntax.assume_p)
in (

let uu____407 = (op ed1.FStar_Syntax_Syntax.null_wp)
in (

let uu____408 = (op ed1.FStar_Syntax_Syntax.trivial)
in (

let uu____409 = (

let uu____410 = (op (([]), (ed1.FStar_Syntax_Syntax.repr)))
in (FStar_Pervasives_Native.snd uu____410))
in (

let uu____421 = (op ed1.FStar_Syntax_Syntax.return_repr)
in (

let uu____422 = (op ed1.FStar_Syntax_Syntax.bind_repr)
in (

let uu____423 = (FStar_List.map (fun a -> (

let uu___117_431 = a
in (

let uu____432 = (

let uu____433 = (op (([]), (a.FStar_Syntax_Syntax.action_defn)))
in (FStar_Pervasives_Native.snd uu____433))
in (

let uu____444 = (

let uu____445 = (op (([]), (a.FStar_Syntax_Syntax.action_typ)))
in (FStar_Pervasives_Native.snd uu____445))
in {FStar_Syntax_Syntax.action_name = uu___117_431.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___117_431.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___117_431.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = uu___117_431.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = uu____432; FStar_Syntax_Syntax.action_typ = uu____444})))) ed1.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.cattributes = uu___116_398.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___116_398.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___116_398.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu___116_398.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = uu___116_398.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = uu____399; FStar_Syntax_Syntax.bind_wp = uu____400; FStar_Syntax_Syntax.if_then_else = uu____401; FStar_Syntax_Syntax.ite_wp = uu____402; FStar_Syntax_Syntax.stronger = uu____403; FStar_Syntax_Syntax.close_wp = uu____404; FStar_Syntax_Syntax.assert_p = uu____405; FStar_Syntax_Syntax.assume_p = uu____406; FStar_Syntax_Syntax.null_wp = uu____407; FStar_Syntax_Syntax.trivial = uu____408; FStar_Syntax_Syntax.repr = uu____409; FStar_Syntax_Syntax.return_repr = uu____421; FStar_Syntax_Syntax.bind_repr = uu____422; FStar_Syntax_Syntax.actions = uu____423}))))))))))))))))
end)
in (

let wp_with_fresh_result_type = (fun env1 mname signature1 -> (

let fail = (fun t -> (

let uu____482 = (

let uu____483 = (

let uu____488 = (FStar_TypeChecker_Err.unexpected_signature_for_monad env1 mname t)
in ((uu____488), ((FStar_Ident.range_of_lid mname))))
in FStar_Errors.Error (uu____483))
in (FStar_Exn.raise uu____482)))
in (

let uu____495 = (

let uu____496 = (FStar_Syntax_Subst.compress signature1)
in uu____496.FStar_Syntax_Syntax.n)
in (match (uu____495) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs1 = (FStar_Syntax_Subst.open_binders bs)
in (match (bs1) with
| ((a, uu____531))::((wp, uu____533))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____548 -> begin
(fail signature1)
end))
end
| uu____549 -> begin
(fail signature1)
end))))
in (

let uu____550 = (wp_with_fresh_result_type env ed2.FStar_Syntax_Syntax.mname ed2.FStar_Syntax_Syntax.signature)
in (match (uu____550) with
| (a, wp_a) -> begin
(

let fresh_effect_signature = (fun uu____572 -> (

let uu____573 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (uu____573) with
| (signature1, uu____585) -> begin
(wp_with_fresh_result_type env ed2.FStar_Syntax_Syntax.mname signature1)
end)))
in (

let env1 = (

let uu____587 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None ed2.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env uu____587))
in ((

let uu____589 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED")))
in (match (uu____589) with
| true -> begin
(

let uu____590 = (FStar_Syntax_Print.lid_to_string ed2.FStar_Syntax_Syntax.mname)
in (

let uu____591 = (FStar_Syntax_Print.binders_to_string " " ed2.FStar_Syntax_Syntax.binders)
in (

let uu____592 = (FStar_Syntax_Print.term_to_string ed2.FStar_Syntax_Syntax.signature)
in (

let uu____593 = (

let uu____594 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Print.term_to_string uu____594))
in (

let uu____595 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.sort)
in (FStar_Util.print5 "Checking effect signature: %s %s : %s\n(a is %s:%s)\n" uu____590 uu____591 uu____592 uu____593 uu____595))))))
end
| uu____596 -> begin
()
end));
(

let check_and_gen' = (fun env2 uu____611 k -> (match (uu____611) with
| (uu____619, t) -> begin
(check_and_gen env2 t k)
end))
in (

let return_wp = (

let expected_k = (

let uu____629 = (

let uu____636 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____637 = (

let uu____640 = (

let uu____641 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____641))
in (uu____640)::[])
in (uu____636)::uu____637))
in (

let uu____642 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow uu____629 uu____642)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.ret_wp expected_k))
in (

let bind_wp = (

let uu____646 = (fresh_effect_signature ())
in (match (uu____646) with
| (b, wp_b) -> begin
(

let a_wp_b = (

let uu____662 = (

let uu____669 = (

let uu____670 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____670))
in (uu____669)::[])
in (

let uu____671 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____662 uu____671)))
in (

let expected_k = (

let uu____677 = (

let uu____684 = (FStar_Syntax_Syntax.null_binder FStar_Syntax_Syntax.t_range)
in (

let uu____685 = (

let uu____688 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____689 = (

let uu____692 = (FStar_Syntax_Syntax.mk_binder b)
in (

let uu____693 = (

let uu____696 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____697 = (

let uu____700 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (uu____700)::[])
in (uu____696)::uu____697))
in (uu____692)::uu____693))
in (uu____688)::uu____689))
in (uu____684)::uu____685))
in (

let uu____701 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____677 uu____701)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else1 = (

let p = (

let uu____706 = (

let uu____707 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____707 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some ((FStar_Ident.range_of_lid ed2.FStar_Syntax_Syntax.mname))) uu____706))
in (

let expected_k = (

let uu____719 = (

let uu____726 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____727 = (

let uu____730 = (FStar_Syntax_Syntax.mk_binder p)
in (

let uu____731 = (

let uu____734 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____735 = (

let uu____738 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____738)::[])
in (uu____734)::uu____735))
in (uu____730)::uu____731))
in (uu____726)::uu____727))
in (

let uu____739 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____719 uu____739)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (

let uu____746 = (

let uu____753 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____754 = (

let uu____757 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____757)::[])
in (uu____753)::uu____754))
in (

let uu____758 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____746 uu____758)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let uu____762 = (FStar_Syntax_Util.type_u ())
in (match (uu____762) with
| (t, uu____768) -> begin
(

let expected_k = (

let uu____772 = (

let uu____779 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____780 = (

let uu____783 = (FStar_Syntax_Syntax.null_binder wp_a)
in (

let uu____784 = (

let uu____787 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____787)::[])
in (uu____783)::uu____784))
in (uu____779)::uu____780))
in (

let uu____788 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow uu____772 uu____788)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (

let uu____793 = (

let uu____794 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____794 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some ((FStar_Ident.range_of_lid ed2.FStar_Syntax_Syntax.mname))) uu____793))
in (

let b_wp_a = (

let uu____806 = (

let uu____813 = (

let uu____814 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder uu____814))
in (uu____813)::[])
in (

let uu____815 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____806 uu____815)))
in (

let expected_k = (

let uu____821 = (

let uu____828 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____829 = (

let uu____832 = (FStar_Syntax_Syntax.mk_binder b)
in (

let uu____833 = (

let uu____836 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (uu____836)::[])
in (uu____832)::uu____833))
in (uu____828)::uu____829))
in (

let uu____837 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____821 uu____837)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (

let uu____844 = (

let uu____851 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____852 = (

let uu____855 = (

let uu____856 = (

let uu____857 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____857 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.null_binder uu____856))
in (

let uu____866 = (

let uu____869 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____869)::[])
in (uu____855)::uu____866))
in (uu____851)::uu____852))
in (

let uu____870 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____844 uu____870)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (

let uu____877 = (

let uu____884 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____885 = (

let uu____888 = (

let uu____889 = (

let uu____890 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right uu____890 FStar_Pervasives_Native.fst))
in (FStar_Syntax_Syntax.null_binder uu____889))
in (

let uu____899 = (

let uu____902 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____902)::[])
in (uu____888)::uu____899))
in (uu____884)::uu____885))
in (

let uu____903 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____877 uu____903)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (

let uu____910 = (

let uu____917 = (FStar_Syntax_Syntax.mk_binder a)
in (uu____917)::[])
in (

let uu____918 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow uu____910 uu____918)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let uu____922 = (FStar_Syntax_Util.type_u ())
in (match (uu____922) with
| (t, uu____928) -> begin
(

let expected_k = (

let uu____932 = (

let uu____939 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____940 = (

let uu____943 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____943)::[])
in (uu____939)::uu____940))
in (

let uu____944 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow uu____932 uu____944)))
in (check_and_gen' env1 ed2.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let uu____947 = (

let uu____958 = (

let uu____959 = (FStar_Syntax_Subst.compress ed2.FStar_Syntax_Syntax.repr)
in uu____959.FStar_Syntax_Syntax.n)
in (match (uu____958) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((ed2.FStar_Syntax_Syntax.repr), (ed2.FStar_Syntax_Syntax.bind_repr), (ed2.FStar_Syntax_Syntax.return_repr), (ed2.FStar_Syntax_Syntax.actions))
end
| uu____974 -> begin
(

let repr = (

let uu____976 = (FStar_Syntax_Util.type_u ())
in (match (uu____976) with
| (t, uu____982) -> begin
(

let expected_k = (

let uu____986 = (

let uu____993 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____994 = (

let uu____997 = (FStar_Syntax_Syntax.null_binder wp_a)
in (uu____997)::[])
in (uu____993)::uu____994))
in (

let uu____998 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow uu____986 uu____998)))
in (tc_check_trivial_guard env1 ed2.FStar_Syntax_Syntax.repr expected_k))
end))
in (

let mk_repr' = (fun t wp -> (

let repr1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env1 repr)
in (

let uu____1011 = (

let uu____1014 = (

let uu____1015 = (

let uu____1030 = (

let uu____1033 = (FStar_Syntax_Syntax.as_arg t)
in (

let uu____1034 = (

let uu____1037 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____1037)::[])
in (uu____1033)::uu____1034))
in ((repr1), (uu____1030)))
in FStar_Syntax_Syntax.Tm_app (uu____1015))
in (FStar_Syntax_Syntax.mk uu____1014))
in (uu____1011 FStar_Pervasives_Native.None FStar_Range.dummyRange))))
in (

let mk_repr = (fun a1 wp -> (

let uu____1052 = (FStar_Syntax_Syntax.bv_to_name a1)
in (mk_repr' uu____1052 wp)))
in (

let destruct_repr = (fun t -> (

let uu____1065 = (

let uu____1066 = (FStar_Syntax_Subst.compress t)
in uu____1066.FStar_Syntax_Syntax.n)
in (match (uu____1065) with
| FStar_Syntax_Syntax.Tm_app (uu____1077, ((t1, uu____1079))::((wp, uu____1081))::[]) -> begin
((t1), (wp))
end
| uu____1124 -> begin
(failwith "Unexpected repr type")
end)))
in (

let bind_repr = (

let r = (

let uu____1135 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.range_0 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_All.pipe_right uu____1135 FStar_Syntax_Syntax.fv_to_tm))
in (

let uu____1136 = (fresh_effect_signature ())
in (match (uu____1136) with
| (b, wp_b) -> begin
(

let a_wp_b = (

let uu____1152 = (

let uu____1159 = (

let uu____1160 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder uu____1160))
in (uu____1159)::[])
in (

let uu____1161 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow uu____1152 uu____1161)))
in (

let wp_f = (FStar_Syntax_Syntax.gen_bv "wp_f" FStar_Pervasives_Native.None wp_a)
in (

let wp_g = (FStar_Syntax_Syntax.gen_bv "wp_g" FStar_Pervasives_Native.None a_wp_b)
in (

let x_a = (

let uu____1167 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" FStar_Pervasives_Native.None uu____1167))
in (

let wp_g_x = (

let uu____1171 = (

let uu____1172 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (

let uu____1173 = (

let uu____1174 = (

let uu____1175 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____1175))
in (uu____1174)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____1172 uu____1173)))
in (uu____1171 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let res = (

let wp = (

let uu____1184 = (

let uu____1185 = (

let uu____1186 = (FStar_TypeChecker_Env.inst_tscheme bind_wp)
in (FStar_All.pipe_right uu____1186 FStar_Pervasives_Native.snd))
in (

let uu____1195 = (

let uu____1196 = (

let uu____1199 = (

let uu____1202 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____1203 = (

let uu____1206 = (FStar_Syntax_Syntax.bv_to_name b)
in (

let uu____1207 = (

let uu____1210 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (

let uu____1211 = (

let uu____1214 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (uu____1214)::[])
in (uu____1210)::uu____1211))
in (uu____1206)::uu____1207))
in (uu____1202)::uu____1203))
in (r)::uu____1199)
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1196))
in (FStar_Syntax_Syntax.mk_Tm_app uu____1185 uu____1195)))
in (uu____1184 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (mk_repr b wp))
in (

let expected_k = (

let uu____1220 = (

let uu____1227 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1228 = (

let uu____1231 = (FStar_Syntax_Syntax.mk_binder b)
in (

let uu____1232 = (

let uu____1235 = (FStar_Syntax_Syntax.mk_binder wp_f)
in (

let uu____1236 = (

let uu____1239 = (

let uu____1240 = (

let uu____1241 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (mk_repr a uu____1241))
in (FStar_Syntax_Syntax.null_binder uu____1240))
in (

let uu____1242 = (

let uu____1245 = (FStar_Syntax_Syntax.mk_binder wp_g)
in (

let uu____1246 = (

let uu____1249 = (

let uu____1250 = (

let uu____1251 = (

let uu____1258 = (FStar_Syntax_Syntax.mk_binder x_a)
in (uu____1258)::[])
in (

let uu____1259 = (

let uu____1262 = (mk_repr b wp_g_x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____1262))
in (FStar_Syntax_Util.arrow uu____1251 uu____1259)))
in (FStar_Syntax_Syntax.null_binder uu____1250))
in (uu____1249)::[])
in (uu____1245)::uu____1246))
in (uu____1239)::uu____1242))
in (uu____1235)::uu____1236))
in (uu____1231)::uu____1232))
in (uu____1227)::uu____1228))
in (

let uu____1263 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow uu____1220 uu____1263)))
in (

let uu____1266 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1 expected_k)
in (match (uu____1266) with
| (expected_k1, uu____1274, uu____1275) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_range env1 (FStar_Pervasives_Native.snd ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos)
in (

let env3 = (

let uu___118_1280 = env2
in {FStar_TypeChecker_Env.solver = uu___118_1280.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___118_1280.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___118_1280.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___118_1280.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___118_1280.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___118_1280.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___118_1280.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___118_1280.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___118_1280.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___118_1280.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___118_1280.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___118_1280.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___118_1280.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___118_1280.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___118_1280.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___118_1280.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___118_1280.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___118_1280.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___118_1280.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___118_1280.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___118_1280.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___118_1280.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___118_1280.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___118_1280.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___118_1280.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___118_1280.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___118_1280.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___118_1280.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___118_1280.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___118_1280.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___118_1280.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___118_1280.FStar_TypeChecker_Env.dsenv})
in (

let br = (check_and_gen' env3 ed2.FStar_Syntax_Syntax.bind_repr expected_k1)
in br)))
end)))))))))
end)))
in (

let return_repr = (

let x_a = (

let uu____1290 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" FStar_Pervasives_Native.None uu____1290))
in (

let res = (

let wp = (

let uu____1297 = (

let uu____1298 = (

let uu____1299 = (FStar_TypeChecker_Env.inst_tscheme return_wp)
in (FStar_All.pipe_right uu____1299 FStar_Pervasives_Native.snd))
in (

let uu____1308 = (

let uu____1309 = (

let uu____1312 = (FStar_Syntax_Syntax.bv_to_name a)
in (

let uu____1313 = (

let uu____1316 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (uu____1316)::[])
in (uu____1312)::uu____1313))
in (FStar_List.map FStar_Syntax_Syntax.as_arg uu____1309))
in (FStar_Syntax_Syntax.mk_Tm_app uu____1298 uu____1308)))
in (uu____1297 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (mk_repr a wp))
in (

let expected_k = (

let uu____1322 = (

let uu____1329 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____1330 = (

let uu____1333 = (FStar_Syntax_Syntax.mk_binder x_a)
in (uu____1333)::[])
in (uu____1329)::uu____1330))
in (

let uu____1334 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow uu____1322 uu____1334)))
in (

let uu____1337 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1 expected_k)
in (match (uu____1337) with
| (expected_k1, uu____1351, uu____1352) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_range env1 (FStar_Pervasives_Native.snd ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos)
in (

let uu____1356 = (check_and_gen' env2 ed2.FStar_Syntax_Syntax.return_repr expected_k1)
in (match (uu____1356) with
| (univs1, repr1) -> begin
(match (univs1) with
| [] -> begin
(([]), (repr1))
end
| uu____1377 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unexpected universe-polymorphic return for effect"), (repr1.FStar_Syntax_Syntax.pos)))))
end)
end)))
end)))))
in (

let actions = (

let check_action = (fun act -> (

let uu____1402 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1 act.FStar_Syntax_Syntax.action_typ)
in (match (uu____1402) with
| (act_typ, uu____1410, g_t) -> begin
(

let env' = (

let uu___119_1413 = (FStar_TypeChecker_Env.set_expected_typ env1 act_typ)
in {FStar_TypeChecker_Env.solver = uu___119_1413.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___119_1413.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___119_1413.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___119_1413.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___119_1413.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___119_1413.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___119_1413.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___119_1413.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___119_1413.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = uu___119_1413.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___119_1413.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___119_1413.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___119_1413.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___119_1413.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___119_1413.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___119_1413.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___119_1413.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___119_1413.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___119_1413.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___119_1413.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___119_1413.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___119_1413.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___119_1413.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___119_1413.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___119_1413.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___119_1413.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___119_1413.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___119_1413.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___119_1413.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___119_1413.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___119_1413.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___119_1413.FStar_TypeChecker_Env.dsenv})
in ((

let uu____1415 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____1415) with
| true -> begin
(

let uu____1416 = (FStar_Syntax_Print.term_to_string act.FStar_Syntax_Syntax.action_defn)
in (

let uu____1417 = (FStar_Syntax_Print.term_to_string act_typ)
in (FStar_Util.print3 "Checking action %s:\n[definition]: %s\n[cps\'d type]: %s\n" (FStar_Ident.text_of_lid act.FStar_Syntax_Syntax.action_name) uu____1416 uu____1417)))
end
| uu____1418 -> begin
()
end));
(

let uu____1419 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' act.FStar_Syntax_Syntax.action_defn)
in (match (uu____1419) with
| (act_defn, uu____1427, g_a) -> begin
(

let act_defn1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env1 act_defn)
in (

let act_typ1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::[]) env1 act_typ)
in (

let uu____1431 = (

let act_typ2 = (FStar_Syntax_Subst.compress act_typ1)
in (match (act_typ2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____1459 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____1459) with
| (bs1, uu____1469) -> begin
(

let res = (mk_repr' FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun)
in (

let k = (

let uu____1476 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs1 uu____1476))
in (

let uu____1479 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1 k)
in (match (uu____1479) with
| (k1, uu____1491, g) -> begin
((k1), (g))
end))))
end))
end
| uu____1493 -> begin
(

let uu____1494 = (

let uu____1495 = (

let uu____1500 = (

let uu____1501 = (FStar_Syntax_Print.term_to_string act_typ2)
in (

let uu____1502 = (FStar_Syntax_Print.tag_of_term act_typ2)
in (FStar_Util.format2 "Actions must have function types (not: %s, a.k.a. %s)" uu____1501 uu____1502)))
in ((uu____1500), (act_defn1.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____1495))
in (FStar_Exn.raise uu____1494))
end))
in (match (uu____1431) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env1 act_typ1 expected_k)
in ((

let uu____1511 = (

let uu____1512 = (

let uu____1513 = (FStar_TypeChecker_Rel.conj_guard g_t g)
in (FStar_TypeChecker_Rel.conj_guard g_k uu____1513))
in (FStar_TypeChecker_Rel.conj_guard g_a uu____1512))
in (FStar_TypeChecker_Rel.force_trivial_guard env1 uu____1511));
(

let act_typ2 = (

let uu____1517 = (

let uu____1518 = (FStar_Syntax_Subst.compress expected_k)
in uu____1518.FStar_Syntax_Syntax.n)
in (match (uu____1517) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____1541 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____1541) with
| (bs1, c1) -> begin
(

let uu____1550 = (destruct_repr (FStar_Syntax_Util.comp_result c1))
in (match (uu____1550) with
| (a1, wp) -> begin
(

let c2 = (

let uu____1572 = (

let uu____1573 = (env1.FStar_TypeChecker_Env.universe_of env1 a1)
in (uu____1573)::[])
in (

let uu____1574 = (

let uu____1583 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____1583)::[])
in {FStar_Syntax_Syntax.comp_univs = uu____1572; FStar_Syntax_Syntax.effect_name = ed2.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a1; FStar_Syntax_Syntax.effect_args = uu____1574; FStar_Syntax_Syntax.flags = []}))
in (

let uu____1584 = (FStar_Syntax_Syntax.mk_Comp c2)
in (FStar_Syntax_Util.arrow bs1 uu____1584)))
end))
end))
end
| uu____1587 -> begin
(failwith "Impossible (expected_k is an arrow)")
end))
in (

let uu____1590 = (FStar_TypeChecker_Util.generalize_universes env1 act_defn1)
in (match (uu____1590) with
| (univs1, act_defn2) -> begin
(

let act_typ3 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env1 act_typ2)
in (

let act_typ4 = (FStar_Syntax_Subst.close_univ_vars univs1 act_typ3)
in (

let uu___120_1599 = act
in {FStar_Syntax_Syntax.action_name = uu___120_1599.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___120_1599.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs1; FStar_Syntax_Syntax.action_params = uu___120_1599.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = act_defn2; FStar_Syntax_Syntax.action_typ = act_typ4})))
end)));
))
end))))
end));
))
end)))
in (FStar_All.pipe_right ed2.FStar_Syntax_Syntax.actions (FStar_List.map check_action)))
in ((repr), (bind_repr), (return_repr), (actions)))))))))
end))
in (match (uu____947) with
| (repr, bind_repr, return_repr, actions) -> begin
(

let t = (

let uu____1623 = (FStar_Syntax_Syntax.mk_Total ed2.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed2.FStar_Syntax_Syntax.binders uu____1623))
in (

let uu____1626 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (uu____1626) with
| (univs1, t1) -> begin
(

let signature1 = (

let uu____1634 = (

let uu____1639 = (

let uu____1640 = (FStar_Syntax_Subst.compress t1)
in uu____1640.FStar_Syntax_Syntax.n)
in ((effect_params), (uu____1639)))
in (match (uu____1634) with
| ([], uu____1643) -> begin
t1
end
| (uu____1654, FStar_Syntax_Syntax.Tm_arrow (uu____1655, c)) -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____1673 -> begin
(failwith "Impossible : t is an arrow")
end))
in (

let close1 = (fun n1 ts -> (

let ts1 = (

let uu____1686 = (FStar_Syntax_Subst.close_tscheme effect_params ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs1 uu____1686))
in (

let m = (FStar_List.length (FStar_Pervasives_Native.fst ts1))
in ((

let uu____1691 = (((n1 >= (Prims.parse_int "0")) && (

let uu____1693 = (FStar_Syntax_Util.is_unknown (FStar_Pervasives_Native.snd ts1))
in (not (uu____1693)))) && (Prims.op_disEquality m n1))
in (match (uu____1691) with
| true -> begin
(

let error1 = (match ((m < n1)) with
| true -> begin
"not universe-polymorphic enough"
end
| uu____1707 -> begin
"too universe-polymorphic"
end)
in (

let err_msg = (

let uu____1709 = (FStar_Util.string_of_int n1)
in (

let uu____1710 = (FStar_Syntax_Print.tscheme_to_string ts1)
in (FStar_Util.format3 "The effect combinator is %s (n=%s) (%s)" error1 uu____1709 uu____1710)))
in (FStar_Exn.raise (FStar_Errors.Error (((err_msg), ((FStar_Pervasives_Native.snd ts1).FStar_Syntax_Syntax.pos)))))))
end
| uu____1713 -> begin
()
end));
ts1;
))))
in (

let close_action = (fun act -> (

let uu____1718 = (close1 (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_defn)))
in (match (uu____1718) with
| (univs2, defn) -> begin
(

let uu____1725 = (close1 (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_typ)))
in (match (uu____1725) with
| (univs', typ) -> begin
(

let uu___121_1735 = act
in {FStar_Syntax_Syntax.action_name = uu___121_1735.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___121_1735.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs2; FStar_Syntax_Syntax.action_params = uu___121_1735.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = defn; FStar_Syntax_Syntax.action_typ = typ})
end))
end)))
in (

let ed3 = (

let uu___122_1740 = ed2
in (

let uu____1741 = (close1 (Prims.parse_int "0") return_wp)
in (

let uu____1742 = (close1 (Prims.parse_int "1") bind_wp)
in (

let uu____1743 = (close1 (Prims.parse_int "0") if_then_else1)
in (

let uu____1744 = (close1 (Prims.parse_int "0") ite_wp)
in (

let uu____1745 = (close1 (Prims.parse_int "0") stronger)
in (

let uu____1746 = (close1 (Prims.parse_int "1") close_wp)
in (

let uu____1747 = (close1 (Prims.parse_int "0") assert_p)
in (

let uu____1748 = (close1 (Prims.parse_int "0") assume_p)
in (

let uu____1749 = (close1 (Prims.parse_int "0") null_wp)
in (

let uu____1750 = (close1 (Prims.parse_int "0") trivial_wp)
in (

let uu____1751 = (

let uu____1752 = (close1 (Prims.parse_int "0") (([]), (repr)))
in (FStar_Pervasives_Native.snd uu____1752))
in (

let uu____1763 = (close1 (Prims.parse_int "0") return_repr)
in (

let uu____1764 = (close1 (Prims.parse_int "1") bind_repr)
in (

let uu____1765 = (FStar_List.map close_action actions)
in {FStar_Syntax_Syntax.cattributes = uu___122_1740.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___122_1740.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs1; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature1; FStar_Syntax_Syntax.ret_wp = uu____1741; FStar_Syntax_Syntax.bind_wp = uu____1742; FStar_Syntax_Syntax.if_then_else = uu____1743; FStar_Syntax_Syntax.ite_wp = uu____1744; FStar_Syntax_Syntax.stronger = uu____1745; FStar_Syntax_Syntax.close_wp = uu____1746; FStar_Syntax_Syntax.assert_p = uu____1747; FStar_Syntax_Syntax.assume_p = uu____1748; FStar_Syntax_Syntax.null_wp = uu____1749; FStar_Syntax_Syntax.trivial = uu____1750; FStar_Syntax_Syntax.repr = uu____1751; FStar_Syntax_Syntax.return_repr = uu____1763; FStar_Syntax_Syntax.bind_repr = uu____1764; FStar_Syntax_Syntax.actions = uu____1765})))))))))))))))
in ((

let uu____1769 = ((FStar_TypeChecker_Env.debug env1 FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("ED"))))
in (match (uu____1769) with
| true -> begin
(

let uu____1770 = (FStar_Syntax_Print.eff_decl_to_string false ed3)
in (FStar_Util.print_string uu____1770))
end
| uu____1771 -> begin
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

let uu____1790 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____1790) with
| (effect_binders_un, signature_un) -> begin
(

let uu____1807 = (FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un)
in (match (uu____1807) with
| (effect_binders, env1, uu____1826) -> begin
(

let uu____1827 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un)
in (match (uu____1827) with
| (signature, uu____1843) -> begin
(

let raise_error = (fun err_msg -> (FStar_Exn.raise (FStar_Errors.Error (((err_msg), (signature.FStar_Syntax_Syntax.pos))))))
in (

let effect_binders1 = (FStar_List.map (fun uu____1871 -> (match (uu____1871) with
| (bv, qual) -> begin
(

let uu____1882 = (

let uu___123_1883 = bv
in (

let uu____1884 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env1 bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___123_1883.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___123_1883.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____1884}))
in ((uu____1882), (qual)))
end)) effect_binders)
in (

let uu____1887 = (

let uu____1894 = (

let uu____1895 = (FStar_Syntax_Subst.compress signature_un)
in uu____1895.FStar_Syntax_Syntax.n)
in (match (uu____1894) with
| FStar_Syntax_Syntax.Tm_arrow (((a, uu____1905))::[], effect_marker) -> begin
((a), (effect_marker))
end
| uu____1927 -> begin
(raise_error "bad shape for effect-for-free signature")
end))
in (match (uu____1887) with
| (a, effect_marker) -> begin
(

let a1 = (

let uu____1951 = (FStar_Syntax_Syntax.is_null_bv a)
in (match (uu____1951) with
| true -> begin
(

let uu____1952 = (

let uu____1955 = (FStar_Syntax_Syntax.range_of_bv a)
in FStar_Pervasives_Native.Some (uu____1955))
in (FStar_Syntax_Syntax.gen_bv "a" uu____1952 a.FStar_Syntax_Syntax.sort))
end
| uu____1956 -> begin
a
end))
in (

let open_and_check = (fun env2 other_binders t -> (

let subst1 = (FStar_Syntax_Subst.opening_of_binders (FStar_List.append effect_binders1 other_binders))
in (

let t1 = (FStar_Syntax_Subst.subst subst1 t)
in (

let uu____1989 = (FStar_TypeChecker_TcTerm.tc_term env2 t1)
in (match (uu____1989) with
| (t2, comp, uu____2002) -> begin
((t2), (comp))
end)))))
in (

let mk1 = (fun x -> (FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None signature.FStar_Syntax_Syntax.pos))
in (

let uu____2009 = (open_and_check env1 [] ed.FStar_Syntax_Syntax.repr)
in (match (uu____2009) with
| (repr, _comp) -> begin
((

let uu____2031 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____2031) with
| true -> begin
(

let uu____2032 = (FStar_Syntax_Print.term_to_string repr)
in (FStar_Util.print1 "Representation is: %s\n" uu____2032))
end
| uu____2033 -> begin
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

let uu____2038 = (

let uu____2039 = (

let uu____2040 = (

let uu____2055 = (

let uu____2062 = (

let uu____2067 = (FStar_Syntax_Syntax.bv_to_name a1)
in (

let uu____2068 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____2067), (uu____2068))))
in (uu____2062)::[])
in ((wp_type1), (uu____2055)))
in FStar_Syntax_Syntax.Tm_app (uu____2040))
in (mk1 uu____2039))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env1 uu____2038))
in (

let effect_signature = (

let binders = (

let uu____2093 = (

let uu____2098 = (FStar_Syntax_Syntax.as_implicit false)
in ((a1), (uu____2098)))
in (

let uu____2099 = (

let uu____2106 = (

let uu____2107 = (FStar_Syntax_Syntax.gen_bv "dijkstra_wp" FStar_Pervasives_Native.None wp_a)
in (FStar_All.pipe_right uu____2107 FStar_Syntax_Syntax.mk_binder))
in (uu____2106)::[])
in (uu____2093)::uu____2099))
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

let uu____2170 = item
in (match (uu____2170) with
| (u_item, item1) -> begin
(

let uu____2191 = (open_and_check env2 other_binders item1)
in (match (uu____2191) with
| (item2, item_comp) -> begin
((

let uu____2207 = (

let uu____2208 = (FStar_Syntax_Util.is_total_lcomp item_comp)
in (not (uu____2208)))
in (match (uu____2207) with
| true -> begin
(

let uu____2209 = (

let uu____2210 = (

let uu____2211 = (FStar_Syntax_Print.term_to_string item2)
in (

let uu____2212 = (FStar_Syntax_Print.lcomp_to_string item_comp)
in (FStar_Util.format2 "Computation for [%s] is not total : %s !" uu____2211 uu____2212)))
in FStar_Errors.Err (uu____2210))
in (FStar_Exn.raise uu____2209))
end
| uu____2213 -> begin
()
end));
(

let uu____2214 = (FStar_TypeChecker_DMFF.star_expr dmff_env1 item2)
in (match (uu____2214) with
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

let uu____2234 = (elaborate_and_star dmff_env [] ed.FStar_Syntax_Syntax.bind_repr)
in (match (uu____2234) with
| (dmff_env1, uu____2258, bind_wp, bind_elab) -> begin
(

let uu____2261 = (elaborate_and_star dmff_env1 [] ed.FStar_Syntax_Syntax.return_repr)
in (match (uu____2261) with
| (dmff_env2, uu____2285, return_wp, return_elab) -> begin
(

let rc_gtot = {FStar_Syntax_Syntax.residual_effect = FStar_Parser_Const.effect_GTot_lid; FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.None; FStar_Syntax_Syntax.residual_flags = []}
in (

let lift_from_pure_wp = (

let uu____2292 = (

let uu____2293 = (FStar_Syntax_Subst.compress return_wp)
in uu____2293.FStar_Syntax_Syntax.n)
in (match (uu____2292) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(

let uu____2337 = (

let uu____2352 = (

let uu____2357 = (FStar_Syntax_Util.abs bs body FStar_Pervasives_Native.None)
in (FStar_Syntax_Subst.open_term ((b1)::(b2)::[]) uu____2357))
in (match (uu____2352) with
| ((b11)::(b21)::[], body1) -> begin
((b11), (b21), (body1))
end
| uu____2421 -> begin
(failwith "Impossible : open_term not preserving binders arity")
end))
in (match (uu____2337) with
| (b11, b21, body1) -> begin
(

let env0 = (

let uu____2460 = (FStar_TypeChecker_DMFF.get_env dmff_env2)
in (FStar_TypeChecker_Env.push_binders uu____2460 ((b11)::(b21)::[])))
in (

let wp_b1 = (

let raw_wp_b1 = (

let uu____2477 = (

let uu____2478 = (

let uu____2493 = (

let uu____2500 = (

let uu____2505 = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst b11))
in (

let uu____2506 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____2505), (uu____2506))))
in (uu____2500)::[])
in ((wp_type1), (uu____2493)))
in FStar_Syntax_Syntax.Tm_app (uu____2478))
in (mk1 uu____2477))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env0 raw_wp_b1))
in (

let uu____2521 = (

let uu____2530 = (

let uu____2531 = (FStar_Syntax_Util.unascribe wp_b1)
in (FStar_TypeChecker_Normalize.eta_expand_with_type env0 body1 uu____2531))
in (FStar_All.pipe_left FStar_Syntax_Util.abs_formals uu____2530))
in (match (uu____2521) with
| (bs1, body2, what') -> begin
(

let fail = (fun uu____2550 -> (

let error_msg = (

let uu____2552 = (FStar_Syntax_Print.term_to_string body2)
in (FStar_Util.format2 "The body of return_wp (%s) should be of type Type0 but is of type %s" uu____2552 (match (what') with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (rc) -> begin
(FStar_Ident.text_of_lid rc.FStar_Syntax_Syntax.residual_effect)
end)))
in (raise_error error_msg)))
in ((match (what') with
| FStar_Pervasives_Native.None -> begin
(fail ())
end
| FStar_Pervasives_Native.Some (rc) -> begin
((match ((not ((FStar_Syntax_Util.is_pure_effect rc.FStar_Syntax_Syntax.residual_effect)))) with
| true -> begin
(fail ())
end
| uu____2557 -> begin
()
end);
(

let uu____2558 = (FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (fun rt -> (

let g_opt = (FStar_TypeChecker_Rel.try_teq true env1 rt FStar_Syntax_Util.ktype0)
in (match (g_opt) with
| FStar_Pervasives_Native.Some (g') -> begin
(FStar_TypeChecker_Rel.force_trivial_guard env1 g')
end
| FStar_Pervasives_Native.None -> begin
(fail ())
end))))
in (FStar_All.pipe_right uu____2558 FStar_Pervasives.ignore));
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

let uu____2585 = (

let uu____2586 = (FStar_Syntax_Syntax.bv_to_name wp)
in (

let uu____2587 = (

let uu____2588 = (

let uu____2595 = (FStar_Syntax_Util.abs ((b21)::[]) body2 what')
in ((uu____2595), (FStar_Pervasives_Native.None)))
in (uu____2588)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____2586 uu____2587)))
in (uu____2585 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let uu____2620 = (

let uu____2621 = (

let uu____2628 = (FStar_Syntax_Syntax.mk_binder wp)
in (uu____2628)::[])
in (b11)::uu____2621)
in (

let uu____2633 = (FStar_Syntax_Util.abs bs1 body3 what)
in (FStar_Syntax_Util.abs uu____2620 uu____2633 (FStar_Pervasives_Native.Some (rc_gtot)))))));
))
end))))
end))
end
| uu____2634 -> begin
(raise_error "unexpected shape for return")
end))
in (

let return_wp1 = (

let uu____2636 = (

let uu____2637 = (FStar_Syntax_Subst.compress return_wp)
in uu____2637.FStar_Syntax_Syntax.n)
in (match (uu____2636) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(

let uu____2681 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs ((b1)::(b2)::[]) uu____2681 (FStar_Pervasives_Native.Some (rc_gtot))))
end
| uu____2694 -> begin
(raise_error "unexpected shape for return")
end))
in (

let bind_wp1 = (

let uu____2696 = (

let uu____2697 = (FStar_Syntax_Subst.compress bind_wp)
in uu____2697.FStar_Syntax_Syntax.n)
in (match (uu____2696) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let r = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.range_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let uu____2724 = (

let uu____2725 = (

let uu____2728 = (

let uu____2729 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (r)))
in (FStar_Syntax_Syntax.null_binder uu____2729))
in (uu____2728)::[])
in (FStar_List.append uu____2725 binders))
in (FStar_Syntax_Util.abs uu____2724 body what)))
end
| uu____2730 -> begin
(raise_error "unexpected shape for bind")
end))
in (

let apply_close = (fun t -> (match ((Prims.op_Equality (FStar_List.length effect_binders1) (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____2747 -> begin
(

let uu____2748 = (

let uu____2749 = (

let uu____2750 = (

let uu____2765 = (

let uu____2766 = (FStar_Syntax_Util.args_of_binders effect_binders1)
in (FStar_Pervasives_Native.snd uu____2766))
in ((t), (uu____2765)))
in FStar_Syntax_Syntax.Tm_app (uu____2750))
in (mk1 uu____2749))
in (FStar_Syntax_Subst.close effect_binders1 uu____2748))
end))
in (

let rec apply_last1 = (fun f l -> (match (l) with
| [] -> begin
(failwith "empty path..")
end
| (a2)::[] -> begin
(

let uu____2796 = (f a2)
in (uu____2796)::[])
end
| (x)::xs -> begin
(

let uu____2801 = (apply_last1 f xs)
in (x)::uu____2801)
end))
in (

let register = (fun name item -> (

let p = (FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname)
in (

let p' = (apply_last1 (fun s -> (Prims.strcat "__" (Prims.strcat s (Prims.strcat "_eff_override_" name)))) p)
in (

let l' = (FStar_Ident.lid_of_path p' FStar_Range.dummyRange)
in (

let uu____2821 = (FStar_TypeChecker_Env.try_lookup_lid env1 l')
in (match (uu____2821) with
| FStar_Pervasives_Native.Some (_us, _t) -> begin
((

let uu____2851 = (FStar_Options.debug_any ())
in (match (uu____2851) with
| true -> begin
(

let uu____2852 = (FStar_Ident.string_of_lid l')
in (FStar_Util.print1 "DM4F: Applying override %s\n" uu____2852))
end
| uu____2853 -> begin
()
end));
(

let uu____2854 = (FStar_Syntax_Syntax.lid_as_fv l' FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____2854));
)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2863 = (

let uu____2868 = (mk_lid name)
in (

let uu____2869 = (FStar_Syntax_Util.abs effect_binders1 item FStar_Pervasives_Native.None)
in (FStar_TypeChecker_Util.mk_toplevel_definition env1 uu____2868 uu____2869)))
in (match (uu____2863) with
| (sigelt, fv) -> begin
((

let uu____2873 = (

let uu____2876 = (FStar_ST.op_Bang sigelts)
in (sigelt)::uu____2876)
in (FStar_ST.op_Colon_Equals sigelts uu____2873));
fv;
)
end))
end))))))
in (

let lift_from_pure_wp1 = (register "lift_from_pure" lift_from_pure_wp)
in (

let return_wp2 = (register "return_wp" return_wp1)
in ((

let uu____3010 = (

let uu____3013 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true"))))
in (

let uu____3014 = (FStar_ST.op_Bang sigelts)
in (uu____3013)::uu____3014))
in (FStar_ST.op_Colon_Equals sigelts uu____3010));
(

let return_elab1 = (register "return_elab" return_elab)
in ((

let uu____3147 = (

let uu____3150 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false"))))
in (

let uu____3151 = (FStar_ST.op_Bang sigelts)
in (uu____3150)::uu____3151))
in (FStar_ST.op_Colon_Equals sigelts uu____3147));
(

let bind_wp2 = (register "bind_wp" bind_wp1)
in ((

let uu____3284 = (

let uu____3287 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true"))))
in (

let uu____3288 = (FStar_ST.op_Bang sigelts)
in (uu____3287)::uu____3288))
in (FStar_ST.op_Colon_Equals sigelts uu____3284));
(

let bind_elab1 = (register "bind_elab" bind_elab)
in ((

let uu____3421 = (

let uu____3424 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false"))))
in (

let uu____3425 = (FStar_ST.op_Bang sigelts)
in (uu____3424)::uu____3425))
in (FStar_ST.op_Colon_Equals sigelts uu____3421));
(

let uu____3556 = (FStar_List.fold_left (fun uu____3596 action -> (match (uu____3596) with
| (dmff_env3, actions) -> begin
(

let params_un = (FStar_Syntax_Subst.open_binders action.FStar_Syntax_Syntax.action_params)
in (

let uu____3617 = (

let uu____3624 = (FStar_TypeChecker_DMFF.get_env dmff_env3)
in (FStar_TypeChecker_TcTerm.tc_tparams uu____3624 params_un))
in (match (uu____3617) with
| (action_params, env', uu____3633) -> begin
(

let action_params1 = (FStar_List.map (fun uu____3653 -> (match (uu____3653) with
| (bv, qual) -> begin
(

let uu____3664 = (

let uu___124_3665 = bv
in (

let uu____3666 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env' bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___124_3665.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___124_3665.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____3666}))
in ((uu____3664), (qual)))
end)) action_params)
in (

let dmff_env' = (FStar_TypeChecker_DMFF.set_env dmff_env3 env')
in (

let uu____3670 = (elaborate_and_star dmff_env' action_params1 ((action.FStar_Syntax_Syntax.action_univs), (action.FStar_Syntax_Syntax.action_defn)))
in (match (uu____3670) with
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
| uu____3700 -> begin
(

let uu____3701 = (FStar_Syntax_Syntax.mk_Total action_typ_with_wp1)
in (FStar_Syntax_Util.flat_arrow action_params2 uu____3701))
end)
in ((

let uu____3705 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1) (FStar_Options.Other ("ED")))
in (match (uu____3705) with
| true -> begin
(

let uu____3706 = (FStar_Syntax_Print.binders_to_string "," params_un)
in (

let uu____3707 = (FStar_Syntax_Print.binders_to_string "," action_params2)
in (

let uu____3708 = (FStar_Syntax_Print.term_to_string action_typ_with_wp2)
in (

let uu____3709 = (FStar_Syntax_Print.term_to_string action_elab2)
in (FStar_Util.print4 "original action_params %s, end action_params %s, type %s, term %s\n" uu____3706 uu____3707 uu____3708 uu____3709)))))
end
| uu____3710 -> begin
()
end));
(

let action_elab3 = (register (Prims.strcat name "_elab") action_elab2)
in (

let action_typ_with_wp3 = (register (Prims.strcat name "_complete_type") action_typ_with_wp2)
in (

let uu____3713 = (

let uu____3716 = (

let uu___125_3717 = action
in (

let uu____3718 = (apply_close action_elab3)
in (

let uu____3719 = (apply_close action_typ_with_wp3)
in {FStar_Syntax_Syntax.action_name = uu___125_3717.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___125_3717.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___125_3717.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = []; FStar_Syntax_Syntax.action_defn = uu____3718; FStar_Syntax_Syntax.action_typ = uu____3719})))
in (uu____3716)::actions)
in ((dmff_env4), (uu____3713)))));
))))))))
end))))
end)))
end)) ((dmff_env2), ([])) ed.FStar_Syntax_Syntax.actions)
in (match (uu____3556) with
| (dmff_env3, actions) -> begin
(

let actions1 = (FStar_List.rev actions)
in (

let repr1 = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp_a" FStar_Pervasives_Native.None wp_a)
in (

let binders = (

let uu____3752 = (FStar_Syntax_Syntax.mk_binder a1)
in (

let uu____3753 = (

let uu____3756 = (FStar_Syntax_Syntax.mk_binder wp)
in (uu____3756)::[])
in (uu____3752)::uu____3753))
in (

let uu____3757 = (

let uu____3758 = (

let uu____3759 = (

let uu____3760 = (

let uu____3775 = (

let uu____3782 = (

let uu____3787 = (FStar_Syntax_Syntax.bv_to_name a1)
in (

let uu____3788 = (FStar_Syntax_Syntax.as_implicit false)
in ((uu____3787), (uu____3788))))
in (uu____3782)::[])
in ((repr), (uu____3775)))
in FStar_Syntax_Syntax.Tm_app (uu____3760))
in (mk1 uu____3759))
in (

let uu____3803 = (FStar_Syntax_Syntax.bv_to_name wp)
in (FStar_TypeChecker_DMFF.trans_F dmff_env3 uu____3758 uu____3803)))
in (FStar_Syntax_Util.abs binders uu____3757 FStar_Pervasives_Native.None))))
in (

let repr2 = (recheck_debug "FC" env1 repr1)
in (

let repr3 = (register "repr" repr2)
in (

let uu____3806 = (

let uu____3813 = (

let uu____3814 = (

let uu____3817 = (FStar_Syntax_Subst.compress wp_type1)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____3817))
in uu____3814.FStar_Syntax_Syntax.n)
in (match (uu____3813) with
| FStar_Syntax_Syntax.Tm_abs ((type_param)::effect_param, arrow1, uu____3827) -> begin
(

let uu____3856 = (

let uu____3873 = (FStar_Syntax_Subst.open_term ((type_param)::effect_param) arrow1)
in (match (uu____3873) with
| ((b)::bs, body) -> begin
((b), (bs), (body))
end
| uu____3931 -> begin
(failwith "Impossible : open_term nt preserving binders arity")
end))
in (match (uu____3856) with
| (type_param1, effect_param1, arrow2) -> begin
(

let uu____3981 = (

let uu____3982 = (

let uu____3985 = (FStar_Syntax_Subst.compress arrow2)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____3985))
in uu____3982.FStar_Syntax_Syntax.n)
in (match (uu____3981) with
| FStar_Syntax_Syntax.Tm_arrow (wp_binders, c) -> begin
(

let uu____4010 = (FStar_Syntax_Subst.open_comp wp_binders c)
in (match (uu____4010) with
| (wp_binders1, c1) -> begin
(

let uu____4023 = (FStar_List.partition (fun uu____4048 -> (match (uu____4048) with
| (bv, uu____4054) -> begin
(

let uu____4055 = (

let uu____4056 = (FStar_Syntax_Free.names bv.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right uu____4056 (FStar_Util.set_mem (FStar_Pervasives_Native.fst type_param1))))
in (FStar_All.pipe_right uu____4055 Prims.op_Negation))
end)) wp_binders1)
in (match (uu____4023) with
| (pre_args, post_args) -> begin
(

let post = (match (post_args) with
| (post)::[] -> begin
post
end
| [] -> begin
(

let err_msg = (

let uu____4120 = (FStar_Syntax_Print.term_to_string arrow2)
in (FStar_Util.format1 "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)" uu____4120))
in (FStar_Exn.raise (FStar_Errors.Err (err_msg))))
end
| uu____4125 -> begin
(

let err_msg = (

let uu____4133 = (FStar_Syntax_Print.term_to_string arrow2)
in (FStar_Util.format1 "Impossible to generate DM effect: multiple post candidates %s" uu____4133))
in (FStar_Exn.raise (FStar_Errors.Err (err_msg))))
end)
in (

let uu____4138 = (FStar_Syntax_Util.arrow pre_args c1)
in (

let uu____4141 = (FStar_Syntax_Util.abs ((type_param1)::effect_param1) (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort FStar_Pervasives_Native.None)
in ((uu____4138), (uu____4141)))))
end))
end))
end
| uu____4148 -> begin
(

let uu____4149 = (

let uu____4150 = (FStar_Syntax_Print.term_to_string arrow2)
in (FStar_Util.format1 "Impossible: pre/post arrow %s" uu____4150))
in (raise_error uu____4149))
end))
end))
end
| uu____4157 -> begin
(

let uu____4158 = (

let uu____4159 = (FStar_Syntax_Print.term_to_string wp_type1)
in (FStar_Util.format1 "Impossible: pre/post abs %s" uu____4159))
in (raise_error uu____4158))
end))
in (match (uu____3806) with
| (pre, post) -> begin
((

let uu____4183 = (register "pre" pre)
in ());
(

let uu____4185 = (register "post" post)
in ());
(

let uu____4187 = (register "wp" wp_type1)
in ());
(

let ed1 = (

let uu___126_4189 = ed
in (

let uu____4190 = (FStar_Syntax_Subst.close_binders effect_binders1)
in (

let uu____4191 = (FStar_Syntax_Subst.close effect_binders1 effect_signature1)
in (

let uu____4192 = (

let uu____4193 = (apply_close return_wp2)
in (([]), (uu____4193)))
in (

let uu____4200 = (

let uu____4201 = (apply_close bind_wp2)
in (([]), (uu____4201)))
in (

let uu____4208 = (apply_close repr3)
in (

let uu____4209 = (

let uu____4210 = (apply_close return_elab1)
in (([]), (uu____4210)))
in (

let uu____4217 = (

let uu____4218 = (apply_close bind_elab1)
in (([]), (uu____4218)))
in {FStar_Syntax_Syntax.cattributes = uu___126_4189.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___126_4189.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___126_4189.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu____4190; FStar_Syntax_Syntax.signature = uu____4191; FStar_Syntax_Syntax.ret_wp = uu____4192; FStar_Syntax_Syntax.bind_wp = uu____4200; FStar_Syntax_Syntax.if_then_else = uu___126_4189.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = uu___126_4189.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = uu___126_4189.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = uu___126_4189.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = uu___126_4189.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = uu___126_4189.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = uu___126_4189.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = uu___126_4189.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = uu____4208; FStar_Syntax_Syntax.return_repr = uu____4209; FStar_Syntax_Syntax.bind_repr = uu____4217; FStar_Syntax_Syntax.actions = actions1}))))))))
in (

let uu____4225 = (FStar_TypeChecker_DMFF.gen_wps_for_free env1 effect_binders1 a1 wp_a ed1)
in (match (uu____4225) with
| (sigelts', ed2) -> begin
((

let uu____4243 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____4243) with
| true -> begin
(

let uu____4244 = (FStar_Syntax_Print.eff_decl_to_string true ed2)
in (FStar_Util.print_string uu____4244))
end
| uu____4245 -> begin
()
end));
(

let lift_from_pure_opt = (match ((Prims.op_Equality (FStar_List.length effect_binders1) (Prims.parse_int "0"))) with
| true -> begin
(

let lift_from_pure = (

let uu____4256 = (

let uu____4259 = (

let uu____4268 = (apply_close lift_from_pure_wp1)
in (([]), (uu____4268)))
in FStar_Pervasives_Native.Some (uu____4259))
in {FStar_Syntax_Syntax.source = FStar_Parser_Const.effect_PURE_lid; FStar_Syntax_Syntax.target = ed2.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.lift_wp = uu____4256; FStar_Syntax_Syntax.lift = FStar_Pervasives_Native.None})
in (

let uu____4283 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_sub_effect (lift_from_pure)))
in FStar_Pervasives_Native.Some (uu____4283)))
end
| uu____4284 -> begin
FStar_Pervasives_Native.None
end)
in (

let uu____4285 = (

let uu____4288 = (

let uu____4291 = (FStar_ST.op_Bang sigelts)
in (FStar_List.rev uu____4291))
in (FStar_List.append uu____4288 sigelts'))
in ((uu____4285), (ed2), (lift_from_pure_opt))));
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


let tc_lex_t : 'Auu____4372 . FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  'Auu____4372 Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (

let err_range = (

let uu____4405 = (FStar_List.hd ses)
in uu____4405.FStar_Syntax_Syntax.sigrng)
in ((match (lids) with
| (lex_t1)::(lex_top1)::(lex_cons)::[] when (((FStar_Ident.lid_equals lex_t1 FStar_Parser_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top1 FStar_Parser_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Parser_Const.lexcons_lid)) -> begin
()
end
| uu____4410 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Invalid (partial) redefinition of lex_t"), (err_range)))))
end);
(match (ses) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (lex_t1, [], [], t, uu____4415, uu____4416); FStar_Syntax_Syntax.sigrng = r; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = uu____4418; FStar_Syntax_Syntax.sigattrs = uu____4419})::({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (lex_top1, [], _t_top, _lex_t_top, _0_41, uu____4423); FStar_Syntax_Syntax.sigrng = r1; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = uu____4425; FStar_Syntax_Syntax.sigattrs = uu____4426})::({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, _0_42, uu____4430); FStar_Syntax_Syntax.sigrng = r2; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = uu____4432; FStar_Syntax_Syntax.sigattrs = uu____4433})::[] when (((_0_41 = (Prims.parse_int "0")) && (_0_42 = (Prims.parse_int "0"))) && (((FStar_Ident.lid_equals lex_t1 FStar_Parser_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top1 FStar_Parser_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Parser_Const.lexcons_lid))) -> begin
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

let uu____4498 = (

let uu____4501 = (

let uu____4502 = (

let uu____4509 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid r1) FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in ((uu____4509), ((FStar_Syntax_Syntax.U_name (utop))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____4502))
in (FStar_Syntax_Syntax.mk uu____4501))
in (uu____4498 FStar_Pervasives_Native.None r1))
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

let uu____4527 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) FStar_Pervasives_Native.None r2)
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (r2)) uu____4527))
in (

let hd1 = (

let uu____4529 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (r2)) uu____4529))
in (

let tl1 = (

let uu____4531 = (

let uu____4532 = (

let uu____4535 = (

let uu____4536 = (

let uu____4543 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid r2) FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in ((uu____4543), ((FStar_Syntax_Syntax.U_name (ucons2))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____4536))
in (FStar_Syntax_Syntax.mk uu____4535))
in (uu____4532 FStar_Pervasives_Native.None r2))
in (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (r2)) uu____4531))
in (

let res = (

let uu____4552 = (

let uu____4555 = (

let uu____4556 = (

let uu____4563 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.lex_t_lid r2) FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in ((uu____4563), ((FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[])))
in FStar_Syntax_Syntax.Tm_uinst (uu____4556))
in (FStar_Syntax_Syntax.mk uu____4555))
in (uu____4552 FStar_Pervasives_Native.None r2))
in (

let uu____4569 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow ((((a), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::(((hd1), (FStar_Pervasives_Native.None)))::(((tl1), (FStar_Pervasives_Native.None)))::[]) uu____4569))))))
in (

let lex_cons_t1 = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((lex_cons), ((ucons1)::(ucons2)::[]), (lex_cons_t1), (FStar_Parser_Const.lex_t_lid), ((Prims.parse_int "0")), ([]))); FStar_Syntax_Syntax.sigrng = r2; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (

let uu____4608 = (FStar_TypeChecker_Env.get_range env)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle ((((tc)::(dc_lextop)::(dc_lexcons)::[]), (lids))); FStar_Syntax_Syntax.sigrng = uu____4608; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))))))))))))))
end
| uu____4613 -> begin
(

let err_msg = (

let uu____4617 = (

let uu____4618 = (FStar_Syntax_Syntax.mk_sigelt (FStar_Syntax_Syntax.Sig_bundle (((ses), (lids)))))
in (FStar_Syntax_Print.sigelt_to_string uu____4618))
in (FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n" uu____4617))
in (FStar_Exn.raise (FStar_Errors.Error (((err_msg), (err_range))))))
end);
)))


let tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env1 = (FStar_TypeChecker_Env.set_range env r)
in (

let uu____4648 = (FStar_Syntax_Util.type_u ())
in (match (uu____4648) with
| (k, uu____4654) -> begin
(

let phi1 = (

let uu____4656 = (tc_check_trivial_guard env1 phi k)
in (FStar_All.pipe_right uu____4656 (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env1)))
in ((FStar_TypeChecker_Util.check_uvars r phi1);
(

let uu____4658 = (FStar_TypeChecker_Util.generalize_universes env1 phi1)
in (match (uu____4658) with
| (us, phi2) -> begin
{FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_assume (((lid), (us), (phi2))); FStar_Syntax_Syntax.sigrng = r; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
end));
))
end))))


let tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env ses quals lids -> (

let env1 = (FStar_TypeChecker_Env.push env "tc_inductive")
in (

let uu____4704 = (FStar_TypeChecker_TcInductive.check_inductive_well_typedness env1 ses quals lids)
in (match (uu____4704) with
| (sig_bndle, tcs, datas) -> begin
(

let data_ops_ses = (

let uu____4737 = (FStar_List.map (FStar_TypeChecker_Util.mk_data_operations quals env1 tcs) datas)
in (FStar_All.pipe_right uu____4737 FStar_List.flatten))
in ((

let uu____4751 = ((FStar_Options.no_positivity ()) || (FStar_Options.lax ()))
in (match (uu____4751) with
| true -> begin
()
end
| uu____4752 -> begin
(

let env2 = (FStar_TypeChecker_Env.push_sigelt env1 sig_bndle)
in (FStar_List.iter (fun ty -> (

let b = (FStar_TypeChecker_TcInductive.check_positivity ty env2)
in (match ((not (b))) with
| true -> begin
(

let uu____4762 = (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____4772, uu____4773, uu____4774, uu____4775, uu____4776) -> begin
((lid), (ty.FStar_Syntax_Syntax.sigrng))
end
| uu____4785 -> begin
(failwith "Impossible!")
end)
in (match (uu____4762) with
| (lid, r) -> begin
(FStar_Errors.err r (Prims.strcat "Inductive type " (Prims.strcat lid.FStar_Ident.str " does not satisfy the positivity condition")))
end))
end
| uu____4792 -> begin
()
end))) tcs))
end));
(

let skip_prims_type = (fun uu____4796 -> (

let lid = (

let ty = (FStar_List.hd tcs)
in (match (ty.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____4800, uu____4801, uu____4802, uu____4803, uu____4804) -> begin
lid
end
| uu____4813 -> begin
(failwith "Impossible")
end))
in (

let types_to_skip = ("c_False")::("c_True")::("equals")::("h_equals")::("c_and")::("c_or")::[]
in (FStar_List.existsb (fun s -> (Prims.op_Equality s lid.FStar_Ident.ident.FStar_Ident.idText)) types_to_skip))))
in (

let is_noeq = (FStar_List.existsb (fun q -> (Prims.op_Equality q FStar_Syntax_Syntax.Noeq)) quals)
in (

let res = (

let uu____4831 = (((Prims.op_Equality (FStar_List.length tcs) (Prims.parse_int "0")) || ((FStar_Ident.lid_equals env1.FStar_TypeChecker_Env.curmodule FStar_Parser_Const.prims_lid) && (skip_prims_type ()))) || is_noeq)
in (match (uu____4831) with
| true -> begin
(((sig_bndle)::[]), (data_ops_ses))
end
| uu____4844 -> begin
(

let is_unopteq = (FStar_List.existsb (fun q -> (Prims.op_Equality q FStar_Syntax_Syntax.Unopteq)) quals)
in (

let ses1 = (match (is_unopteq) with
| true -> begin
(FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme sig_bndle tcs datas env1 tc_assume)
end
| uu____4853 -> begin
(FStar_TypeChecker_TcInductive.optimized_haseq_scheme sig_bndle tcs datas env1 tc_assume)
end)
in (

let uu____4854 = (

let uu____4857 = (

let uu____4858 = (FStar_TypeChecker_Env.get_range env1)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle ((((FStar_List.append tcs datas)), (lids))); FStar_Syntax_Syntax.sigrng = uu____4858; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (uu____4857)::ses1)
in ((uu____4854), (data_ops_ses)))))
end))
in ((

let uu____4868 = (FStar_TypeChecker_Env.pop env1 "tc_inductive")
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
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____4904) -> begin
(failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____4929) -> begin
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

let uu____4981 = (tc_inductive env2 ses se.FStar_Syntax_Syntax.sigquals lids)
in (match (uu____4981) with
| (ses1, projectors_ses) -> begin
((ses1), (projectors_ses))
end)))
end
| FStar_Syntax_Syntax.Sig_pragma (p) -> begin
(

let set_options1 = (fun t s -> (

let uu____5020 = (FStar_Options.set_options t s)
in (match (uu____5020) with
| FStar_Getopt.Success -> begin
()
end
| FStar_Getopt.Help -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Failed to process pragma: use \'fstar --help\' to see which options are available"), (r)))))
end
| FStar_Getopt.Error (s1) -> begin
(FStar_Exn.raise (FStar_Errors.Error ((((Prims.strcat "Failed to process pragma: " s1)), (r)))))
end)))
in (match (p) with
| FStar_Syntax_Syntax.LightOff -> begin
((match ((Prims.op_Equality p FStar_Syntax_Syntax.LightOff)) with
| true -> begin
(FStar_Options.set_ml_ish ())
end
| uu____5031 -> begin
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

let uu____5046 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right uu____5046 FStar_Pervasives.ignore));
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

let uu____5054 = (cps_and_elaborate env1 ne)
in (match (uu____5054) with
| (ses, ne1, lift_from_pure_opt) -> begin
(

let effect_and_lift_ses = (match (lift_from_pure_opt) with
| FStar_Pervasives_Native.Some (lift) -> begin
((

let uu___127_5091 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne1); FStar_Syntax_Syntax.sigrng = uu___127_5091.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___127_5091.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___127_5091.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___127_5091.FStar_Syntax_Syntax.sigattrs}))::(lift)::[]
end
| FStar_Pervasives_Native.None -> begin
((

let uu___128_5093 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne1); FStar_Syntax_Syntax.sigrng = uu___128_5093.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___128_5093.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___128_5093.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___128_5093.FStar_Syntax_Syntax.sigattrs}))::[]
end)
in (([]), ((FStar_List.append ses effect_and_lift_ses))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let ne1 = (tc_eff_decl env1 ne)
in (

let se1 = (

let uu___129_5101 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ne1); FStar_Syntax_Syntax.sigrng = uu___129_5101.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___129_5101.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___129_5101.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___129_5101.FStar_Syntax_Syntax.sigattrs})
in (((se1)::[]), ([]))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub1) -> begin
(

let ed_src = (FStar_TypeChecker_Env.get_effect_decl env1 sub1.FStar_Syntax_Syntax.source)
in (

let ed_tgt = (FStar_TypeChecker_Env.get_effect_decl env1 sub1.FStar_Syntax_Syntax.target)
in (

let uu____5109 = (

let uu____5116 = (FStar_TypeChecker_Env.lookup_effect_lid env1 sub1.FStar_Syntax_Syntax.source)
in (monad_signature env1 sub1.FStar_Syntax_Syntax.source uu____5116))
in (match (uu____5109) with
| (a, wp_a_src) -> begin
(

let uu____5131 = (

let uu____5138 = (FStar_TypeChecker_Env.lookup_effect_lid env1 sub1.FStar_Syntax_Syntax.target)
in (monad_signature env1 sub1.FStar_Syntax_Syntax.target uu____5138))
in (match (uu____5131) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (

let uu____5154 = (

let uu____5157 = (

let uu____5158 = (

let uu____5165 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (uu____5165)))
in FStar_Syntax_Syntax.NT (uu____5158))
in (uu____5157)::[])
in (FStar_Syntax_Subst.subst uu____5154 wp_b_tgt))
in (

let expected_k = (

let uu____5169 = (

let uu____5176 = (FStar_Syntax_Syntax.mk_binder a)
in (

let uu____5177 = (

let uu____5180 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (uu____5180)::[])
in (uu____5176)::uu____5177))
in (

let uu____5181 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow uu____5169 uu____5181)))
in (

let repr_type = (fun eff_name a1 wp -> (

let no_reify = (fun l -> (

let uu____5202 = (

let uu____5203 = (

let uu____5208 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (

let uu____5209 = (FStar_TypeChecker_Env.get_range env1)
in ((uu____5208), (uu____5209))))
in FStar_Errors.Error (uu____5203))
in (FStar_Exn.raise uu____5202)))
in (

let uu____5212 = (FStar_TypeChecker_Env.effect_decl_opt env1 eff_name)
in (match (uu____5212) with
| FStar_Pervasives_Native.None -> begin
(no_reify eff_name)
end
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((FStar_Syntax_Syntax.U_unknown)::[]) env1 ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let uu____5244 = (

let uu____5245 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (not (uu____5245)))
in (match (uu____5244) with
| true -> begin
(no_reify eff_name)
end
| uu____5250 -> begin
(

let uu____5251 = (FStar_TypeChecker_Env.get_range env1)
in (

let uu____5252 = (

let uu____5255 = (

let uu____5256 = (

let uu____5271 = (

let uu____5274 = (FStar_Syntax_Syntax.as_arg a1)
in (

let uu____5275 = (

let uu____5278 = (FStar_Syntax_Syntax.as_arg wp)
in (uu____5278)::[])
in (uu____5274)::uu____5275))
in ((repr), (uu____5271)))
in FStar_Syntax_Syntax.Tm_app (uu____5256))
in (FStar_Syntax_Syntax.mk uu____5255))
in (uu____5252 FStar_Pervasives_Native.None uu____5251)))
end)))
end))))
in (

let uu____5284 = (match (((sub1.FStar_Syntax_Syntax.lift), (sub1.FStar_Syntax_Syntax.lift_wp))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(failwith "Impossible (parser)")
end
| (lift, FStar_Pervasives_Native.Some (uu____5312, lift_wp)) -> begin
(

let uu____5336 = (check_and_gen env1 lift_wp expected_k)
in ((lift), (uu____5336)))
end
| (FStar_Pervasives_Native.Some (what, lift), FStar_Pervasives_Native.None) -> begin
((

let uu____5362 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("ED")))
in (match (uu____5362) with
| true -> begin
(

let uu____5363 = (FStar_Syntax_Print.term_to_string lift)
in (FStar_Util.print1 "Lift for free : %s\n" uu____5363))
end
| uu____5364 -> begin
()
end));
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env1 (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange))
in (

let uu____5366 = (FStar_TypeChecker_TcTerm.tc_term env1 lift)
in (match (uu____5366) with
| (lift1, comp, uu____5381) -> begin
(

let uu____5382 = (FStar_TypeChecker_DMFF.star_expr dmff_env lift1)
in (match (uu____5382) with
| (uu____5395, lift_wp, lift_elab) -> begin
(

let uu____5398 = (recheck_debug "lift-wp" env1 lift_wp)
in (

let uu____5399 = (recheck_debug "lift-elab" env1 lift_elab)
in ((FStar_Pervasives_Native.Some ((([]), (lift_elab)))), ((([]), (lift_wp))))))
end))
end)));
)
end)
in (match (uu____5284) with
| (lift, lift_wp) -> begin
(

let lax1 = env1.FStar_TypeChecker_Env.lax
in (

let env2 = (

let uu___130_5440 = env1
in {FStar_TypeChecker_Env.solver = uu___130_5440.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___130_5440.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___130_5440.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___130_5440.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___130_5440.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___130_5440.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___130_5440.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___130_5440.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___130_5440.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___130_5440.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___130_5440.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___130_5440.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___130_5440.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___130_5440.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___130_5440.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___130_5440.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___130_5440.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___130_5440.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___130_5440.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___130_5440.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___130_5440.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___130_5440.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___130_5440.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___130_5440.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___130_5440.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___130_5440.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___130_5440.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___130_5440.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___130_5440.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___130_5440.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___130_5440.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___130_5440.FStar_TypeChecker_Env.dsenv})
in (

let lift1 = (match (lift) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (uu____5446, lift1) -> begin
(

let uu____5458 = (

let uu____5465 = (FStar_TypeChecker_Env.lookup_effect_lid env2 sub1.FStar_Syntax_Syntax.source)
in (monad_signature env2 sub1.FStar_Syntax_Syntax.source uu____5465))
in (match (uu____5458) with
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

let uu____5489 = (FStar_TypeChecker_Env.get_range env2)
in (

let uu____5490 = (

let uu____5493 = (

let uu____5494 = (

let uu____5509 = (

let uu____5512 = (FStar_Syntax_Syntax.as_arg a_typ)
in (

let uu____5513 = (

let uu____5516 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (uu____5516)::[])
in (uu____5512)::uu____5513))
in ((lift_wp1), (uu____5509)))
in FStar_Syntax_Syntax.Tm_app (uu____5494))
in (FStar_Syntax_Syntax.mk uu____5493))
in (uu____5490 FStar_Pervasives_Native.None uu____5489)))
in (repr_type sub1.FStar_Syntax_Syntax.target a_typ lift_wp_a)))
in (

let expected_k1 = (

let uu____5525 = (

let uu____5532 = (FStar_Syntax_Syntax.mk_binder a1)
in (

let uu____5533 = (

let uu____5536 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (

let uu____5537 = (

let uu____5540 = (FStar_Syntax_Syntax.null_binder repr_f)
in (uu____5540)::[])
in (uu____5536)::uu____5537))
in (uu____5532)::uu____5533))
in (

let uu____5541 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow uu____5525 uu____5541)))
in (

let uu____5544 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env2 expected_k1)
in (match (uu____5544) with
| (expected_k2, uu____5554, uu____5555) -> begin
(

let lift2 = (check_and_gen env2 lift1 expected_k2)
in FStar_Pervasives_Native.Some (lift2))
end))))))))
end))
end)
in (

let sub2 = (

let uu___131_5558 = sub1
in {FStar_Syntax_Syntax.source = uu___131_5558.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = uu___131_5558.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = FStar_Pervasives_Native.Some (lift_wp); FStar_Syntax_Syntax.lift = lift1})
in (

let se1 = (

let uu___132_5560 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_sub_effect (sub2); FStar_Syntax_Syntax.sigrng = uu___132_5560.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___132_5560.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___132_5560.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___132_5560.FStar_Syntax_Syntax.sigattrs})
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

let uu____5579 = (FStar_Syntax_Subst.open_comp tps c)
in (match (uu____5579) with
| (tps1, c1) -> begin
(

let uu____5594 = (FStar_TypeChecker_TcTerm.tc_tparams env2 tps1)
in (match (uu____5594) with
| (tps2, env3, us) -> begin
(

let uu____5612 = (FStar_TypeChecker_TcTerm.tc_comp env3 c1)
in (match (uu____5612) with
| (c2, u, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env3 g);
(

let tps3 = (FStar_Syntax_Subst.close_binders tps2)
in (

let c3 = (FStar_Syntax_Subst.close_comp tps3 c2)
in (

let uu____5633 = (

let uu____5634 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps3), (c3)))) FStar_Pervasives_Native.None r)
in (FStar_TypeChecker_Util.generalize_universes env0 uu____5634))
in (match (uu____5633) with
| (uvs1, t) -> begin
(

let uu____5649 = (

let uu____5662 = (

let uu____5667 = (

let uu____5668 = (FStar_Syntax_Subst.compress t)
in uu____5668.FStar_Syntax_Syntax.n)
in ((tps3), (uu____5667)))
in (match (uu____5662) with
| ([], FStar_Syntax_Syntax.Tm_arrow (uu____5683, c4)) -> begin
(([]), (c4))
end
| (uu____5723, FStar_Syntax_Syntax.Tm_arrow (tps4, c4)) -> begin
((tps4), (c4))
end
| uu____5750 -> begin
(failwith "Impossible (t is an arrow)")
end))
in (match (uu____5649) with
| (tps4, c4) -> begin
((match ((Prims.op_disEquality (FStar_List.length uvs1) (Prims.parse_int "1"))) with
| true -> begin
(

let uu____5794 = (FStar_Syntax_Subst.open_univ_vars uvs1 t)
in (match (uu____5794) with
| (uu____5799, t1) -> begin
(

let uu____5801 = (

let uu____5802 = (

let uu____5807 = (

let uu____5808 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____5809 = (FStar_All.pipe_right (FStar_List.length uvs1) FStar_Util.string_of_int)
in (

let uu____5810 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)" uu____5808 uu____5809 uu____5810))))
in ((uu____5807), (r)))
in FStar_Errors.Error (uu____5802))
in (FStar_Exn.raise uu____5801))
end))
end
| uu____5811 -> begin
()
end);
(

let se1 = (

let uu___133_5813 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (((lid), (uvs1), (tps4), (c4), (flags))); FStar_Syntax_Syntax.sigrng = uu___133_5813.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___133_5813.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___133_5813.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___133_5813.FStar_Syntax_Syntax.sigattrs})
in (((se1)::[]), ([])));
)
end))
end))));
)
end))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____5830, uu____5831, uu____5832) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___108_5836 -> (match (uu___108_5836) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____5837 -> begin
false
end)))) -> begin
(([]), ([]))
end
| FStar_Syntax_Syntax.Sig_let (uu____5842, uu____5843) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___108_5851 -> (match (uu___108_5851) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____5852 -> begin
false
end)))) -> begin
(([]), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) -> begin
(

let env2 = (FStar_TypeChecker_Env.set_range env1 r)
in ((

let uu____5862 = (FStar_TypeChecker_Env.lid_exists env2 lid)
in (match (uu____5862) with
| true -> begin
(

let uu____5863 = (

let uu____5864 = (

let uu____5869 = (FStar_Util.format1 "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module" (FStar_Ident.text_of_lid lid))
in ((uu____5869), (r)))
in FStar_Errors.Error (uu____5864))
in (FStar_Exn.raise uu____5863))
end
| uu____5870 -> begin
()
end));
(

let uu____5871 = (match ((Prims.op_Equality uvs [])) with
| true -> begin
(

let uu____5872 = (

let uu____5873 = (FStar_Syntax_Util.type_u ())
in (FStar_Pervasives_Native.fst uu____5873))
in (check_and_gen env2 t uu____5872))
end
| uu____5878 -> begin
(

let uu____5879 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____5879) with
| (uvs1, t1) -> begin
(

let t2 = (

let uu____5887 = (

let uu____5888 = (FStar_Syntax_Util.type_u ())
in (FStar_Pervasives_Native.fst uu____5888))
in (tc_check_trivial_guard env2 t1 uu____5887))
in (

let t3 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Beta)::[]) env2 t2)
in (

let uu____5894 = (FStar_Syntax_Subst.close_univ_vars uvs1 t3)
in ((uvs1), (uu____5894)))))
end))
end)
in (match (uu____5871) with
| (uvs1, t1) -> begin
(

let se1 = (

let uu___134_5910 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (uvs1), (t1))); FStar_Syntax_Syntax.sigrng = uu___134_5910.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___134_5910.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___134_5910.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___134_5910.FStar_Syntax_Syntax.sigattrs})
in (((se1)::[]), ([])))
end));
))
end
| FStar_Syntax_Syntax.Sig_assume (lid, us, phi) -> begin
(

let uu____5920 = (FStar_Syntax_Subst.open_univ_vars us phi)
in (match (uu____5920) with
| (uu____5933, phi1) -> begin
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

let uu____5943 = (FStar_TypeChecker_TcTerm.tc_term env3 e)
in (match (uu____5943) with
| (e1, c, g1) -> begin
(

let uu____5961 = (

let uu____5968 = (

let uu____5971 = (FStar_Syntax_Util.ml_comp FStar_Syntax_Syntax.t_unit r)
in FStar_Pervasives_Native.Some (uu____5971))
in (

let uu____5972 = (

let uu____5977 = (c.FStar_Syntax_Syntax.comp ())
in ((e1), (uu____5977)))
in (FStar_TypeChecker_TcTerm.check_expected_effect env3 uu____5968 uu____5972)))
in (match (uu____5961) with
| (e2, uu____5991, g) -> begin
((

let uu____5994 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env3 uu____5994));
(

let se1 = (

let uu___135_5996 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_main (e2); FStar_Syntax_Syntax.sigrng = uu___135_5996.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___135_5996.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___135_5996.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___135_5996.FStar_Syntax_Syntax.sigattrs})
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

let uu____6047 = ((Prims.op_Equality (FStar_List.length q) (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q'))
in (match (uu____6047) with
| true -> begin
FStar_Pervasives_Native.Some (q)
end
| uu____6054 -> begin
(

let uu____6055 = (

let uu____6056 = (

let uu____6061 = (

let uu____6062 = (FStar_Syntax_Print.lid_to_string l)
in (

let uu____6063 = (FStar_Syntax_Print.quals_to_string q)
in (

let uu____6064 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" uu____6062 uu____6063 uu____6064))))
in ((uu____6061), (r)))
in FStar_Errors.Error (uu____6056))
in (FStar_Exn.raise uu____6055))
end))
end))
in (

let rename_parameters = (fun lb -> (

let rename_in_typ = (fun def typ -> (

let typ1 = (FStar_Syntax_Subst.compress typ)
in (

let def_bs = (

let uu____6090 = (

let uu____6091 = (FStar_Syntax_Subst.compress def)
in uu____6091.FStar_Syntax_Syntax.n)
in (match (uu____6090) with
| FStar_Syntax_Syntax.Tm_abs (binders, uu____6101, uu____6102) -> begin
binders
end
| uu____6123 -> begin
[]
end))
in (match (typ1) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow (val_bs, c); FStar_Syntax_Syntax.pos = r1; FStar_Syntax_Syntax.vars = uu____6133} -> begin
(

let has_auto_name = (fun bv -> (FStar_Util.starts_with bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Ident.reserved_prefix))
in (

let rec rename_binders1 = (fun def_bs1 val_bs1 -> (match (((def_bs1), (val_bs1))) with
| ([], uu____6211) -> begin
val_bs1
end
| (uu____6234, []) -> begin
val_bs1
end
| (((body_bv, uu____6258))::bt, ((val_bv, aqual))::vt) -> begin
(

let uu____6295 = (rename_binders1 bt vt)
in ((match ((((has_auto_name body_bv)), ((has_auto_name val_bv)))) with
| (true, uu____6311) -> begin
((val_bv), (aqual))
end
| (false, true) -> begin
(((

let uu___136_6313 = val_bv
in {FStar_Syntax_Syntax.ppname = (

let uu___137_6316 = val_bv.FStar_Syntax_Syntax.ppname
in {FStar_Ident.idText = body_bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText; FStar_Ident.idRange = uu___137_6316.FStar_Ident.idRange}); FStar_Syntax_Syntax.index = uu___136_6313.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___136_6313.FStar_Syntax_Syntax.sort})), (aqual))
end
| (false, false) -> begin
((val_bv), (aqual))
end))::uu____6295)
end))
in (

let uu____6317 = (

let uu____6320 = (

let uu____6321 = (

let uu____6334 = (rename_binders1 def_bs val_bs)
in ((uu____6334), (c)))
in FStar_Syntax_Syntax.Tm_arrow (uu____6321))
in (FStar_Syntax_Syntax.mk uu____6320))
in (uu____6317 FStar_Pervasives_Native.None r1))))
end
| uu____6352 -> begin
typ1
end))))
in (

let uu___138_6353 = lb
in (

let uu____6354 = (rename_in_typ lb.FStar_Syntax_Syntax.lbdef lb.FStar_Syntax_Syntax.lbtyp)
in {FStar_Syntax_Syntax.lbname = uu___138_6353.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___138_6353.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu____6354; FStar_Syntax_Syntax.lbeff = uu___138_6353.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___138_6353.FStar_Syntax_Syntax.lbdef}))))
in (

let uu____6357 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.fold_left (fun uu____6408 lb -> (match (uu____6408) with
| (gen1, lbs1, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____6450 = (

let uu____6461 = (FStar_TypeChecker_Env.try_lookup_val_decl env2 lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____6461) with
| FStar_Pervasives_Native.None -> begin
(match ((Prims.op_disEquality lb.FStar_Syntax_Syntax.lbunivs [])) with
| true -> begin
((false), (lb), (quals_opt))
end
| uu____6502 -> begin
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
| uu____6546 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((lb.FStar_Syntax_Syntax.lbdef), (((FStar_Util.Inl (lb.FStar_Syntax_Syntax.lbtyp)), (FStar_Pervasives_Native.None))), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.pos)
end)
in ((match (((Prims.op_disEquality lb.FStar_Syntax_Syntax.lbunivs []) && (Prims.op_disEquality (FStar_List.length lb.FStar_Syntax_Syntax.lbunivs) (FStar_List.length uvs)))) with
| true -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Inline universes are incoherent with annotation from val declaration"), (r)))))
end
| uu____6588 -> begin
()
end);
(

let uu____6589 = (FStar_Syntax_Syntax.mk_lb ((FStar_Util.Inr (lbname)), (uvs), (FStar_Parser_Const.effect_ALL_lid), (tval), (def)))
in ((false), (uu____6589), (quals_opt1)));
)))
end))
in (match (uu____6450) with
| (gen2, lb1, quals_opt1) -> begin
((gen2), ((lb1)::lbs1), (quals_opt1))
end)))
end)) ((true), ([]), ((match ((Prims.op_Equality se.FStar_Syntax_Syntax.sigquals [])) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____6645 -> begin
FStar_Pervasives_Native.Some (se.FStar_Syntax_Syntax.sigquals)
end)))))
in (match (uu____6357) with
| (should_generalize, lbs', quals_opt) -> begin
(

let quals = (match (quals_opt) with
| FStar_Pervasives_Native.None -> begin
(FStar_Syntax_Syntax.Visible_default)::[]
end
| FStar_Pervasives_Native.Some (q) -> begin
(

let uu____6683 = (FStar_All.pipe_right q (FStar_Util.for_some (fun uu___109_6687 -> (match (uu___109_6687) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| FStar_Syntax_Syntax.Visible_default -> begin
true
end
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____6688 -> begin
false
end))))
in (match (uu____6683) with
| true -> begin
q
end
| uu____6691 -> begin
(FStar_Syntax_Syntax.Visible_default)::q
end))
end)
in (

let lbs'1 = (FStar_List.rev lbs')
in (

let e = (

let uu____6698 = (

let uu____6701 = (

let uu____6702 = (

let uu____6715 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) FStar_Pervasives_Native.None r)
in (((((FStar_Pervasives_Native.fst lbs)), (lbs'1))), (uu____6715)))
in FStar_Syntax_Syntax.Tm_let (uu____6702))
in (FStar_Syntax_Syntax.mk uu____6701))
in (uu____6698 FStar_Pervasives_Native.None r))
in (

let uu____6733 = (

let uu____6744 = (FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term (

let uu___139_6753 = env2
in {FStar_TypeChecker_Env.solver = uu___139_6753.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___139_6753.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___139_6753.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___139_6753.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___139_6753.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___139_6753.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___139_6753.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___139_6753.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___139_6753.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___139_6753.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___139_6753.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = uu___139_6753.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = uu___139_6753.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___139_6753.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___139_6753.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___139_6753.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___139_6753.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___139_6753.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___139_6753.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___139_6753.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___139_6753.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___139_6753.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___139_6753.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___139_6753.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___139_6753.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___139_6753.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___139_6753.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___139_6753.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___139_6753.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___139_6753.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___139_6753.FStar_TypeChecker_Env.dsenv}) e)
in (match (uu____6744) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs1, e1); FStar_Syntax_Syntax.pos = uu____6766; FStar_Syntax_Syntax.vars = uu____6767}, uu____6768, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let lbs2 = (

let uu____6797 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1) (FStar_List.map rename_parameters))
in (((FStar_Pervasives_Native.fst lbs1)), (uu____6797)))
in (

let quals1 = (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (uu____6815, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| uu____6820 -> begin
quals
end)
in (((

let uu___140_6828 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((lbs2), (lids))); FStar_Syntax_Syntax.sigrng = uu___140_6828.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = uu___140_6828.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___140_6828.FStar_Syntax_Syntax.sigattrs})), (lbs2))))
end
| uu____6837 -> begin
(failwith "impossible (typechecking should preserve Tm_let)")
end))
in (match (uu____6733) with
| (se1, lbs1) -> begin
((FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1) (FStar_List.iter (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (FStar_TypeChecker_Env.insert_fv_info env2 fv lb.FStar_Syntax_Syntax.lbtyp)))));
(

let uu____6886 = (log env2)
in (match (uu____6886) with
| true -> begin
(

let uu____6887 = (

let uu____6888 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1) (FStar_List.map (fun lb -> (

let should_log = (

let uu____6903 = (

let uu____6912 = (

let uu____6913 = (

let uu____6916 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____6916.FStar_Syntax_Syntax.fv_name)
in uu____6913.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env2 uu____6912))
in (match (uu____6903) with
| FStar_Pervasives_Native.None -> begin
true
end
| uu____6923 -> begin
false
end))
in (match (should_log) with
| true -> begin
(

let uu____6932 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____6933 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" uu____6932 uu____6933)))
end
| uu____6934 -> begin
""
end)))))
in (FStar_All.pipe_right uu____6888 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" uu____6887))
end
| uu____6937 -> begin
()
end));
(

let reified_tactic_type = (fun l t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____6964 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____6964) with
| (bs1, c1) -> begin
(

let uu____6971 = (FStar_Syntax_Util.is_total_comp c1)
in (match (uu____6971) with
| true -> begin
(

let c' = (match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t', u) -> begin
(

let uu____6983 = (

let uu____6984 = (FStar_Syntax_Subst.compress t')
in uu____6984.FStar_Syntax_Syntax.n)
in (match (uu____6983) with
| FStar_Syntax_Syntax.Tm_app (h, args) -> begin
(

let uu____7009 = (

let uu____7010 = (FStar_Syntax_Subst.compress h)
in uu____7010.FStar_Syntax_Syntax.n)
in (match (uu____7009) with
| FStar_Syntax_Syntax.Tm_uinst (h', u') -> begin
(

let h'' = (

let uu____7020 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.u_tac_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm uu____7020))
in (

let uu____7021 = (

let uu____7022 = (

let uu____7023 = (FStar_Syntax_Syntax.mk_Tm_uinst h'' u')
in (FStar_Syntax_Syntax.mk_Tm_app uu____7023 args))
in (uu____7022 FStar_Pervasives_Native.None t'.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Syntax.mk_Total' uu____7021 u)))
end
| uu____7026 -> begin
c1
end))
end
| uu____7027 -> begin
c1
end))
end
| uu____7028 -> begin
c1
end)
in (

let uu___141_7029 = t1
in (

let uu____7030 = (

let uu____7031 = (

let uu____7044 = (FStar_Syntax_Subst.close_comp bs1 c')
in ((bs1), (uu____7044)))
in FStar_Syntax_Syntax.Tm_arrow (uu____7031))
in {FStar_Syntax_Syntax.n = uu____7030; FStar_Syntax_Syntax.pos = uu___141_7029.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___141_7029.FStar_Syntax_Syntax.vars})))
end
| uu____7045 -> begin
t1
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (h, args) -> begin
(

let uu____7068 = (

let uu____7069 = (FStar_Syntax_Subst.compress h)
in uu____7069.FStar_Syntax_Syntax.n)
in (match (uu____7068) with
| FStar_Syntax_Syntax.Tm_uinst (h', u') -> begin
(

let h'' = (

let uu____7079 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.u_tac_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm uu____7079))
in (

let uu____7080 = (

let uu____7081 = (FStar_Syntax_Syntax.mk_Tm_uinst h'' u')
in (FStar_Syntax_Syntax.mk_Tm_app uu____7081 args))
in (uu____7080 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos)))
end
| uu____7084 -> begin
t1
end))
end
| uu____7085 -> begin
t1
end)))
in (

let reified_tactic_decl = (fun assm_lid lb -> (

let t = (reified_tactic_type assm_lid lb.FStar_Syntax_Syntax.lbtyp)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((assm_lid), (lb.FStar_Syntax_Syntax.lbunivs), (t))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid assm_lid); FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::[]; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))
in (

let reflected_tactic_decl = (fun b lb bs assm_lid comp -> (

let reified_tac = (

let uu____7113 = (FStar_Syntax_Syntax.lid_as_fv assm_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_All.pipe_left FStar_Syntax_Syntax.fv_to_tm uu____7113))
in (

let tac_args = (FStar_List.map (fun x -> (

let uu____7130 = (FStar_Syntax_Syntax.bv_to_name (FStar_Pervasives_Native.fst x))
in ((uu____7130), ((FStar_Pervasives_Native.snd x))))) bs)
in (

let reflect_head = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (FStar_Parser_Const.tac_effect_lid))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let refl_arg = (FStar_Syntax_Syntax.mk_Tm_app reified_tac tac_args FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let app = (FStar_Syntax_Syntax.mk_Tm_app reflect_head ((((refl_arg), (FStar_Pervasives_Native.None)))::[]) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let unit_binder = (

let uu____7161 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____7161))
in (

let body = (FStar_All.pipe_left (FStar_Syntax_Util.abs ((unit_binder)::[]) app) (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp comp))))
in (

let func = (FStar_All.pipe_left (FStar_Syntax_Util.abs bs body) (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.residual_comp_of_comp comp))))
in (

let uu___142_7168 = se1
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((b), (((

let uu___143_7180 = lb
in {FStar_Syntax_Syntax.lbname = uu___143_7180.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___143_7180.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___143_7180.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___143_7180.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = func}))::[]))), (lids))); FStar_Syntax_Syntax.sigrng = uu___142_7168.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___142_7168.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___142_7168.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___142_7168.FStar_Syntax_Syntax.sigattrs}))))))))))
in (

let tactic_decls = (match ((FStar_Pervasives_Native.snd lbs1)) with
| (hd1)::[] -> begin
(

let uu____7197 = (FStar_Syntax_Util.arrow_formals_comp hd1.FStar_Syntax_Syntax.lbtyp)
in (match (uu____7197) with
| (bs, comp) -> begin
(

let t = (FStar_Syntax_Util.comp_result comp)
in (

let uu____7231 = (

let uu____7232 = (FStar_Syntax_Subst.compress t)
in uu____7232.FStar_Syntax_Syntax.n)
in (match (uu____7231) with
| FStar_Syntax_Syntax.Tm_app (h, args) -> begin
(

let h1 = (FStar_Syntax_Subst.compress h)
in (

let tac_lid = (

let uu____7265 = (

let uu____7268 = (FStar_Util.right hd1.FStar_Syntax_Syntax.lbname)
in uu____7268.FStar_Syntax_Syntax.fv_name)
in uu____7265.FStar_Syntax_Syntax.v)
in (

let assm_lid = (

let uu____7270 = (FStar_All.pipe_left FStar_Ident.id_of_text (Prims.strcat "__" tac_lid.FStar_Ident.ident.FStar_Ident.idText))
in (FStar_Ident.lid_of_ns_and_id tac_lid.FStar_Ident.ns uu____7270))
in (

let uu____7271 = (get_tactic_fv env2 assm_lid h1)
in (match (uu____7271) with
| FStar_Pervasives_Native.Some (fv) -> begin
(

let uu____7281 = (

let uu____7282 = (

let uu____7283 = (FStar_TypeChecker_Env.try_lookup_val_decl env2 tac_lid)
in (FStar_All.pipe_left FStar_Util.is_some uu____7283))
in (not (uu____7282)))
in (match (uu____7281) with
| true -> begin
((

let uu____7313 = (

let uu____7314 = (is_builtin_tactic env2.FStar_TypeChecker_Env.curmodule)
in (not (uu____7314)))
in (match (uu____7313) with
| true -> begin
(

let added_modules = (FStar_ST.op_Bang user_tactics_modules)
in (

let module_name = (FStar_Ident.ml_path_of_lid env2.FStar_TypeChecker_Env.curmodule)
in (match ((not ((FStar_List.contains module_name added_modules)))) with
| true -> begin
(FStar_ST.op_Colon_Equals user_tactics_modules (FStar_List.append added_modules ((module_name)::[])))
end
| uu____7419 -> begin
()
end)))
end
| uu____7420 -> begin
()
end));
(

let uu____7421 = (env2.FStar_TypeChecker_Env.is_native_tactic assm_lid)
in (match (uu____7421) with
| true -> begin
(

let se_assm = (reified_tactic_decl assm_lid hd1)
in (

let se_refl = (reflected_tactic_decl (FStar_Pervasives_Native.fst lbs1) hd1 bs assm_lid comp)
in FStar_Pervasives_Native.Some (((se_assm), (se_refl)))))
end
| uu____7436 -> begin
FStar_Pervasives_Native.None
end));
)
end
| uu____7441 -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))))
end
| uu____7450 -> begin
FStar_Pervasives_Native.None
end)))
end))
end
| uu____7455 -> begin
FStar_Pervasives_Native.None
end)
in (match (tactic_decls) with
| FStar_Pervasives_Native.Some (se_assm, se_refl) -> begin
((

let uu____7477 = (FStar_TypeChecker_Env.debug env2 (FStar_Options.Other ("NativeTactics")))
in (match (uu____7477) with
| true -> begin
(

let uu____7478 = (FStar_Syntax_Print.sigelt_to_string se_assm)
in (

let uu____7479 = (FStar_Syntax_Print.sigelt_to_string se_refl)
in (FStar_Util.print2 "Native tactic declarations: \n%s\n%s\n" uu____7478 uu____7479)))
end
| uu____7480 -> begin
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
end)))))
end));
)))


let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___110_7532 -> (match (uu___110_7532) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| uu____7533 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| FStar_Syntax_Syntax.Projector (l, uu____7539) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| FStar_Syntax_Syntax.Discriminator (l) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| uu____7545 -> begin
false
end))
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_pragma (uu____7554) -> begin
(([]), (hidden))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____7559) -> begin
(failwith "Impossible (Already handled)")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____7584) -> begin
(failwith "Impossible (Already handled)")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____7608) -> begin
(

let uu____7617 = (is_abstract se.FStar_Syntax_Syntax.sigquals)
in (match (uu____7617) with
| true -> begin
(

let for_export_bundle = (fun se1 uu____7648 -> (match (uu____7648) with
| (out, hidden1) -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, uu____7687, uu____7688) -> begin
(

let dec = (

let uu___144_7698 = se1
in (

let uu____7699 = (

let uu____7700 = (

let uu____7707 = (

let uu____7710 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow bs uu____7710))
in ((l), (us), (uu____7707)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____7700))
in {FStar_Syntax_Syntax.sigel = uu____7699; FStar_Syntax_Syntax.sigrng = uu___144_7698.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::se1.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___144_7698.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___144_7698.FStar_Syntax_Syntax.sigattrs}))
in (((dec)::out), (hidden1)))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, uu____7722, uu____7723, uu____7724) -> begin
(

let dec = (

let uu___145_7730 = se1
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t))); FStar_Syntax_Syntax.sigrng = uu___145_7730.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::[]; FStar_Syntax_Syntax.sigmeta = uu___145_7730.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___145_7730.FStar_Syntax_Syntax.sigattrs})
in (((dec)::out), ((l)::hidden1)))
end
| uu____7735 -> begin
((out), (hidden1))
end)
end))
in (FStar_List.fold_right for_export_bundle ses (([]), (hidden))))
end
| uu____7752 -> begin
(((se)::[]), (hidden))
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____7757, uu____7758, uu____7759) -> begin
(

let uu____7760 = (is_abstract se.FStar_Syntax_Syntax.sigquals)
in (match (uu____7760) with
| true -> begin
(([]), (hidden))
end
| uu____7773 -> begin
(((se)::[]), (hidden))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, us, t) -> begin
(

let uu____7781 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some is_hidden_proj_or_disc))
in (match (uu____7781) with
| true -> begin
((((

let uu___146_7797 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t))); FStar_Syntax_Syntax.sigrng = uu___146_7797.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::[]; FStar_Syntax_Syntax.sigmeta = uu___146_7797.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___146_7797.FStar_Syntax_Syntax.sigattrs}))::[]), ((l)::hidden))
end
| uu____7798 -> begin
(

let uu____7799 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___111_7803 -> (match (uu___111_7803) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____7804) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____7809) -> begin
true
end
| uu____7810 -> begin
false
end))))
in (match (uu____7799) with
| true -> begin
(((se)::[]), (hidden))
end
| uu____7823 -> begin
(([]), (hidden))
end))
end))
end
| FStar_Syntax_Syntax.Sig_main (uu____7828) -> begin
(([]), (hidden))
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____7833) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____7838) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____7843) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____7848) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____7866) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____7883 = (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
in (match (uu____7883) with
| true -> begin
(([]), (hidden))
end
| uu____7898 -> begin
(

let dec = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::[]; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (((dec)::[]), ((lid)::hidden)))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, l) -> begin
(

let uu____7914 = (is_abstract se.FStar_Syntax_Syntax.sigquals)
in (match (uu____7914) with
| true -> begin
(

let uu____7923 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let uu___147_7936 = se
in (

let uu____7937 = (

let uu____7938 = (

let uu____7945 = (

let uu____7946 = (

let uu____7949 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____7949.FStar_Syntax_Syntax.fv_name)
in uu____7946.FStar_Syntax_Syntax.v)
in ((uu____7945), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____7938))
in {FStar_Syntax_Syntax.sigel = uu____7937; FStar_Syntax_Syntax.sigrng = uu___147_7936.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___147_7936.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___147_7936.FStar_Syntax_Syntax.sigattrs})))))
in ((uu____7923), (hidden)))
end
| uu____7958 -> begin
(((se)::[]), (hidden))
end))
end))))


let add_sigelt_to_env : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____7971) -> begin
(failwith "add_sigelt_to_env: Impossible, bare data constructor")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____7988) -> begin
(failwith "add_sigelt_to_env: Impossible, bare data constructor")
end
| FStar_Syntax_Syntax.Sig_pragma (p) -> begin
(match (p) with
| FStar_Syntax_Syntax.SetOptions (uu____8004) -> begin
(

let uu____8005 = (FStar_Options.using_facts_from ())
in (match (uu____8005) with
| FStar_Pervasives_Native.Some (ns) -> begin
(

let proof_ns = (

let uu____8026 = (

let uu____8035 = (FStar_List.map (fun s -> (((FStar_Ident.path_of_text s)), (true))) ns)
in (FStar_List.append uu____8035 (((([]), (false)))::[])))
in (uu____8026)::[])
in (

let uu___148_8090 = env
in {FStar_TypeChecker_Env.solver = uu___148_8090.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___148_8090.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___148_8090.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___148_8090.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___148_8090.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___148_8090.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___148_8090.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___148_8090.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___148_8090.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___148_8090.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___148_8090.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___148_8090.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___148_8090.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___148_8090.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___148_8090.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___148_8090.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___148_8090.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___148_8090.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___148_8090.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___148_8090.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___148_8090.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___148_8090.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___148_8090.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___148_8090.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___148_8090.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___148_8090.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___148_8090.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = proof_ns; FStar_TypeChecker_Env.synth = uu___148_8090.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___148_8090.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___148_8090.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___148_8090.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___148_8090.FStar_TypeChecker_Env.dsenv}))
end
| FStar_Pervasives_Native.None -> begin
(

let uu___149_8093 = env
in {FStar_TypeChecker_Env.solver = uu___149_8093.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___149_8093.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___149_8093.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___149_8093.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___149_8093.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___149_8093.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___149_8093.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___149_8093.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___149_8093.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___149_8093.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___149_8093.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___149_8093.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___149_8093.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___149_8093.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___149_8093.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___149_8093.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___149_8093.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___149_8093.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___149_8093.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___149_8093.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___149_8093.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___149_8093.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___149_8093.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___149_8093.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___149_8093.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___149_8093.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___149_8093.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = ([])::[]; FStar_TypeChecker_Env.synth = uu___149_8093.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___149_8093.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___149_8093.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___149_8093.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___149_8093.FStar_TypeChecker_Env.dsenv})
end))
end
| FStar_Syntax_Syntax.ResetOptions (uu____8110) -> begin
(

let uu____8113 = (FStar_Options.using_facts_from ())
in (match (uu____8113) with
| FStar_Pervasives_Native.Some (ns) -> begin
(

let proof_ns = (

let uu____8134 = (

let uu____8143 = (FStar_List.map (fun s -> (((FStar_Ident.path_of_text s)), (true))) ns)
in (FStar_List.append uu____8143 (((([]), (false)))::[])))
in (uu____8134)::[])
in (

let uu___148_8198 = env
in {FStar_TypeChecker_Env.solver = uu___148_8198.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___148_8198.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___148_8198.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___148_8198.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___148_8198.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___148_8198.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___148_8198.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___148_8198.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___148_8198.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___148_8198.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___148_8198.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___148_8198.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___148_8198.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___148_8198.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___148_8198.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___148_8198.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___148_8198.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___148_8198.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___148_8198.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___148_8198.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___148_8198.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___148_8198.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___148_8198.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___148_8198.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___148_8198.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___148_8198.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___148_8198.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = proof_ns; FStar_TypeChecker_Env.synth = uu___148_8198.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___148_8198.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___148_8198.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___148_8198.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___148_8198.FStar_TypeChecker_Env.dsenv}))
end
| FStar_Pervasives_Native.None -> begin
(

let uu___149_8201 = env
in {FStar_TypeChecker_Env.solver = uu___149_8201.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___149_8201.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___149_8201.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___149_8201.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___149_8201.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___149_8201.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___149_8201.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___149_8201.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___149_8201.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___149_8201.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___149_8201.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___149_8201.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___149_8201.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___149_8201.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___149_8201.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___149_8201.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___149_8201.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___149_8201.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___149_8201.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___149_8201.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___149_8201.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___149_8201.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___149_8201.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___149_8201.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___149_8201.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___149_8201.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___149_8201.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = ([])::[]; FStar_TypeChecker_Env.synth = uu___149_8201.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___149_8201.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___149_8201.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___149_8201.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___149_8201.FStar_TypeChecker_Env.dsenv})
end))
end
| uu____8218 -> begin
env
end)
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____8219) -> begin
env
end
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_sigelt env se)
in (FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun env2 a -> (

let uu____8229 = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a)
in (FStar_TypeChecker_Env.push_sigelt env2 uu____8229))) env1)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____8230, uu____8231, uu____8232) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___112_8236 -> (match (uu___112_8236) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____8237 -> begin
false
end)))) -> begin
env
end
| FStar_Syntax_Syntax.Sig_let (uu____8238, uu____8239) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___112_8247 -> (match (uu___112_8247) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____8248 -> begin
false
end)))) -> begin
env
end
| uu____8249 -> begin
(FStar_TypeChecker_Env.push_sigelt env se)
end))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let rec process_one_decl = (fun uu____8311 se -> (match (uu____8311) with
| (ses1, exports, env1, hidden) -> begin
((

let uu____8364 = (FStar_TypeChecker_Env.debug env1 FStar_Options.Low)
in (match (uu____8364) with
| true -> begin
(

let uu____8365 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____8365))
end
| uu____8366 -> begin
()
end));
(

let uu____8367 = (tc_decl env1 se)
in (match (uu____8367) with
| (ses', ses_elaborated) -> begin
(

let ses'1 = (FStar_All.pipe_right ses' (FStar_List.map (fun se1 -> ((

let uu____8417 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("UF")))
in (match (uu____8417) with
| true -> begin
(

let uu____8418 = (FStar_Syntax_Print.sigelt_to_string se1)
in (FStar_Util.print1 "About to elim vars from %s" uu____8418))
end
| uu____8419 -> begin
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

let uu____8441 = ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2) (FStar_Options.Other ("LogTypes"))))
in (match (uu____8441) with
| true -> begin
(

let uu____8442 = (FStar_List.fold_left (fun s se1 -> (

let uu____8448 = (

let uu____8449 = (FStar_Syntax_Print.sigelt_to_string se1)
in (Prims.strcat uu____8449 "\n"))
in (Prims.strcat s uu____8448))) "" ses'1)
in (FStar_Util.print1 "Checked: %s\n" uu____8442))
end
| uu____8450 -> begin
()
end));
(FStar_List.iter (fun se1 -> (env2.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env2 se1)) ses'1);
(

let uu____8454 = (

let accum_exports_hidden = (fun uu____8484 se1 -> (match (uu____8484) with
| (exports1, hidden1) -> begin
(

let uu____8512 = (for_export hidden1 se1)
in (match (uu____8512) with
| (se_exported, hidden2) -> begin
(((FStar_List.rev_append se_exported exports1)), (hidden2))
end))
end))
in (FStar_List.fold_left accum_exports_hidden ((exports), (hidden)) ses'1))
in (match (uu____8454) with
| (exports1, hidden1) -> begin
(

let ses'2 = (FStar_List.map (fun s -> (

let uu___150_8591 = s
in {FStar_Syntax_Syntax.sigel = uu___150_8591.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___150_8591.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___150_8591.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___150_8591.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = se.FStar_Syntax_Syntax.sigattrs})) ses'1)
in (((((FStar_List.rev_append ses'2 ses1)), (exports1), (env2), (hidden1))), (ses_elaborated1)))
end));
));
)))
end));
)
end))
in (

let process_one_decl_timed = (fun acc se -> (

let uu____8669 = acc
in (match (uu____8669) with
| (uu____8704, uu____8705, env1, uu____8707) -> begin
(

let uu____8720 = (FStar_Util.record_time (fun uu____8766 -> (process_one_decl acc se)))
in (match (uu____8720) with
| (r, ms_elapsed) -> begin
((

let uu____8830 = (FStar_TypeChecker_Env.debug env1 (FStar_Options.Other ("TCDeclTime")))
in (match (uu____8830) with
| true -> begin
(

let uu____8831 = (FStar_Syntax_Print.sigelt_to_string_short se)
in (

let uu____8832 = (FStar_Util.string_of_int ms_elapsed)
in (FStar_Util.print2 "Checked %s in %s milliseconds\n" uu____8831 uu____8832)))
end
| uu____8833 -> begin
()
end));
r;
)
end))
end)))
in (

let uu____8834 = (FStar_Util.fold_flatten process_one_decl_timed (([]), ([]), (env), ([])) ses)
in (match (uu____8834) with
| (ses1, exports, env1, uu____8882) -> begin
(((FStar_List.rev_append ses1 [])), ((FStar_List.rev_append exports [])), (env1))
end)))))


let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.bool  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul push_before_typechecking -> (

let verify = (FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let action = (match (verify) with
| true -> begin
"Verifying"
end
| uu____8921 -> begin
"Lax-checking"
end)
in (

let label1 = (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____8923 -> begin
"implementation"
end)
in ((

let uu____8925 = (FStar_Options.debug_any ())
in (match (uu____8925) with
| true -> begin
(FStar_Util.print3 "%s %s of %s\n" action label1 modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
end
| uu____8926 -> begin
()
end));
(

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____8928 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let msg = (Prims.strcat "Internals for " name)
in (

let env1 = (

let uu___151_8931 = env
in {FStar_TypeChecker_Env.solver = uu___151_8931.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___151_8931.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___151_8931.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___151_8931.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___151_8931.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___151_8931.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___151_8931.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___151_8931.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___151_8931.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___151_8931.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___151_8931.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___151_8931.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___151_8931.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___151_8931.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___151_8931.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___151_8931.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = (not (verify)); FStar_TypeChecker_Env.lax = uu___151_8931.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___151_8931.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___151_8931.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___151_8931.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___151_8931.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___151_8931.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___151_8931.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___151_8931.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___151_8931.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___151_8931.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___151_8931.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___151_8931.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___151_8931.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___151_8931.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___151_8931.FStar_TypeChecker_Env.dsenv})
in ((match (push_before_typechecking) with
| true -> begin
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
end
| uu____8933 -> begin
()
end);
(

let env2 = (FStar_TypeChecker_Env.set_current_module env1 modul.FStar_Syntax_Syntax.name)
in (

let uu____8935 = (tc_decls env2 modul.FStar_Syntax_Syntax.declarations)
in (match (uu____8935) with
| (ses, exports, env3) -> begin
(((

let uu___152_8968 = modul
in {FStar_Syntax_Syntax.name = uu___152_8968.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = uu___152_8968.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___152_8968.FStar_Syntax_Syntax.is_interface})), (exports), (env3))
end)));
))));
)))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let uu____8993 = (tc_decls env decls)
in (match (uu____8993) with
| (ses, exports, env1) -> begin
(

let modul1 = (

let uu___153_9024 = modul
in {FStar_Syntax_Syntax.name = uu___153_9024.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = uu___153_9024.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___153_9024.FStar_Syntax_Syntax.is_interface})
in ((modul1), (exports), (env1)))
end)))


let check_exports : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env modul exports -> (

let env1 = (

let uu___154_9044 = env
in {FStar_TypeChecker_Env.solver = uu___154_9044.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___154_9044.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___154_9044.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___154_9044.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___154_9044.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___154_9044.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___154_9044.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___154_9044.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___154_9044.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___154_9044.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___154_9044.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___154_9044.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___154_9044.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = uu___154_9044.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___154_9044.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___154_9044.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___154_9044.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = true; FStar_TypeChecker_Env.failhard = uu___154_9044.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___154_9044.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___154_9044.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___154_9044.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___154_9044.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___154_9044.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___154_9044.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___154_9044.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___154_9044.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___154_9044.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___154_9044.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___154_9044.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___154_9044.FStar_TypeChecker_Env.dsenv})
in (

let check_term = (fun lid univs1 t -> (

let uu____9055 = (FStar_Syntax_Subst.open_univ_vars univs1 t)
in (match (uu____9055) with
| (univs2, t1) -> begin
((

let uu____9063 = (

let uu____9064 = (

let uu____9067 = (FStar_TypeChecker_Env.set_current_module env1 modul.FStar_Syntax_Syntax.name)
in (FStar_TypeChecker_Env.debug uu____9067))
in (FStar_All.pipe_left uu____9064 (FStar_Options.Other ("Exports"))))
in (match (uu____9063) with
| true -> begin
(

let uu____9068 = (FStar_Syntax_Print.lid_to_string lid)
in (

let uu____9069 = (

let uu____9070 = (FStar_All.pipe_right univs2 (FStar_List.map (fun x -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (x))))))
in (FStar_All.pipe_right uu____9070 (FStar_String.concat ", ")))
in (

let uu____9079 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Checking for export %s <%s> : %s\n" uu____9068 uu____9069 uu____9079))))
end
| uu____9080 -> begin
()
end));
(

let env2 = (FStar_TypeChecker_Env.push_univ_vars env1 univs2)
in (

let uu____9082 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1)
in (FStar_All.pipe_right uu____9082 FStar_Pervasives.ignore)));
)
end)))
in (

let check_term1 = (fun lid univs1 t -> ((

let uu____9106 = (

let uu____9107 = (FStar_Syntax_Print.lid_to_string modul.FStar_Syntax_Syntax.name)
in (

let uu____9108 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Interface of %s violates its abstraction (add a \'private\' qualifier to \'%s\'?)" uu____9107 uu____9108)))
in (FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____9106));
(check_term lid univs1 t);
(FStar_Errors.message_prefix.FStar_Errors.clear_prefix ());
))
in (

let rec check_sigelt = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____9115) -> begin
(

let uu____9124 = (

let uu____9125 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____9125)))
in (match (uu____9124) with
| true -> begin
(FStar_All.pipe_right ses (FStar_List.iter check_sigelt))
end
| uu____9130 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (l, univs1, binders, typ, uu____9135, uu____9136) -> begin
(

let t = (

let uu____9148 = (

let uu____9151 = (

let uu____9152 = (

let uu____9165 = (FStar_Syntax_Syntax.mk_Total typ)
in ((binders), (uu____9165)))
in FStar_Syntax_Syntax.Tm_arrow (uu____9152))
in (FStar_Syntax_Syntax.mk uu____9151))
in (uu____9148 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng))
in (check_term1 l univs1 t))
end
| FStar_Syntax_Syntax.Sig_datacon (l, univs1, t, uu____9172, uu____9173, uu____9174) -> begin
(check_term1 l univs1 t)
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, univs1, t) -> begin
(

let uu____9182 = (

let uu____9183 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____9183)))
in (match (uu____9182) with
| true -> begin
(check_term1 l univs1 t)
end
| uu____9186 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_let ((uu____9187, lbs), uu____9189) -> begin
(

let uu____9204 = (

let uu____9205 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____9205)))
in (match (uu____9204) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (check_term1 fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp)))))
end
| uu____9214 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs1, binders, comp, flags) -> begin
(

let uu____9224 = (

let uu____9225 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Private))
in (not (uu____9225)))
in (match (uu____9224) with
| true -> begin
(

let arrow1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))) FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng)
in (check_term1 l univs1 arrow1))
end
| uu____9231 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_main (uu____9232) -> begin
()
end
| FStar_Syntax_Syntax.Sig_assume (uu____9233) -> begin
()
end
| FStar_Syntax_Syntax.Sig_new_effect (uu____9240) -> begin
()
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____9241) -> begin
()
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____9242) -> begin
()
end
| FStar_Syntax_Syntax.Sig_pragma (uu____9243) -> begin
()
end))
in (match ((FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Parser_Const.prims_lid)) with
| true -> begin
()
end
| uu____9244 -> begin
(FStar_List.iter check_sigelt exports)
end))))))


let load_checked_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_TypeChecker_Env.env = (fun env modul -> (

let env1 = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

let env2 = (FStar_List.fold_left FStar_TypeChecker_Env.push_sigelt env1 modul.FStar_Syntax_Syntax.exports)
in (

let env3 = (FStar_TypeChecker_Env.finish_module env2 modul)
in ((env3.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env3 modul);
(env3.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
(

let uu____9259 = (

let uu____9260 = (FStar_Options.interactive ())
in (not (uu____9260)))
in (match (uu____9259) with
| true -> begin
(

let uu____9261 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right uu____9261 FStar_Pervasives.ignore))
end
| uu____9262 -> begin
()
end));
env3;
)))))


let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (

let modul1 = (

let uu___155_9280 = modul
in {FStar_Syntax_Syntax.name = uu___155_9280.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu___155_9280.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env1 = (FStar_TypeChecker_Env.finish_module env modul1)
in ((

let uu____9283 = (

let uu____9284 = (FStar_Options.lax ())
in (not (uu____9284)))
in (match (uu____9283) with
| true -> begin
(check_exports env1 modul1 exports)
end
| uu____9285 -> begin
()
end));
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul1.FStar_Syntax_Syntax.name.FStar_Ident.str));
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env1 modul1);
(env1.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
(

let uu____9290 = (

let uu____9291 = (FStar_Options.interactive ())
in (not (uu____9291)))
in (match (uu____9290) with
| true -> begin
(

let uu____9292 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right uu____9292 FStar_Pervasives.ignore))
end
| uu____9293 -> begin
()
end));
((modul1), (env1));
))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let uu____9306 = (tc_partial_modul env modul true)
in (match (uu____9306) with
| (modul1, non_private_decls, env1) -> begin
(finish_partial_modul env1 modul1 non_private_decls)
end)))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> ((

let uu____9339 = (FStar_Options.debug_any ())
in (match (uu____9339) with
| true -> begin
(

let uu____9340 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (match (m.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"i\'face"
end
| uu____9341 -> begin
"module"
end) uu____9340))
end
| uu____9342 -> begin
()
end));
(

let env1 = (

let uu___156_9344 = env
in (

let uu____9345 = (

let uu____9346 = (FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (not (uu____9346)))
in {FStar_TypeChecker_Env.solver = uu___156_9344.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___156_9344.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___156_9344.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___156_9344.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___156_9344.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___156_9344.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___156_9344.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___156_9344.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___156_9344.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___156_9344.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___156_9344.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___156_9344.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___156_9344.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___156_9344.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___156_9344.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___156_9344.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___156_9344.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___156_9344.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu____9345; FStar_TypeChecker_Env.lax_universes = uu___156_9344.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___156_9344.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___156_9344.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___156_9344.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___156_9344.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___156_9344.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___156_9344.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___156_9344.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___156_9344.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___156_9344.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___156_9344.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___156_9344.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___156_9344.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___156_9344.FStar_TypeChecker_Env.dsenv}))
in (

let uu____9347 = (tc_modul env1 m)
in (match (uu____9347) with
| (m1, env2) -> begin
((

let uu____9359 = (FStar_Options.dump_module m1.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____9359) with
| true -> begin
(

let uu____9360 = (FStar_Syntax_Print.modul_to_string m1)
in (FStar_Util.print1 "%s\n" uu____9360))
end
| uu____9361 -> begin
()
end));
(

let uu____9363 = ((FStar_Options.dump_module m1.FStar_Syntax_Syntax.name.FStar_Ident.str) && (FStar_Options.debug_at_level m1.FStar_Syntax_Syntax.name.FStar_Ident.str (FStar_Options.Other ("Normalize"))))
in (match (uu____9363) with
| true -> begin
(

let normalize_toplevel_lets = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((b, lbs), ids) -> begin
(

let n1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]))
in (

let update = (fun lb -> (

let uu____9394 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____9394) with
| (univnames1, e) -> begin
(

let uu___157_9401 = lb
in (

let uu____9402 = (

let uu____9405 = (FStar_TypeChecker_Env.push_univ_vars env2 univnames1)
in (n1 uu____9405 e))
in {FStar_Syntax_Syntax.lbname = uu___157_9401.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___157_9401.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___157_9401.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___157_9401.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____9402}))
end)))
in (

let uu___158_9406 = se
in (

let uu____9407 = (

let uu____9408 = (

let uu____9415 = (

let uu____9422 = (FStar_List.map update lbs)
in ((b), (uu____9422)))
in ((uu____9415), (ids)))
in FStar_Syntax_Syntax.Sig_let (uu____9408))
in {FStar_Syntax_Syntax.sigel = uu____9407; FStar_Syntax_Syntax.sigrng = uu___158_9406.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___158_9406.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___158_9406.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___158_9406.FStar_Syntax_Syntax.sigattrs}))))
end
| uu____9435 -> begin
se
end))
in (

let normalized_module = (

let uu___159_9437 = m1
in (

let uu____9438 = (FStar_List.map normalize_toplevel_lets m1.FStar_Syntax_Syntax.declarations)
in {FStar_Syntax_Syntax.name = uu___159_9437.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu____9438; FStar_Syntax_Syntax.exports = uu___159_9437.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___159_9437.FStar_Syntax_Syntax.is_interface}))
in (

let uu____9439 = (FStar_Syntax_Print.modul_to_string normalized_module)
in (FStar_Util.print1 "%s\n" uu____9439))))
end
| uu____9440 -> begin
()
end));
((m1), (env2));
)
end)));
))




