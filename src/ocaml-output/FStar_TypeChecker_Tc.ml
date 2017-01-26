
open Prims

let set_hint_correlator : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env = (fun env se -> (

let uu____7 = (FStar_Options.reuse_hint_for ())
in (match (uu____7) with
| Some (l) -> begin
(

let lid = (let _0_226 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_add_suffix _0_226 l))
in (

let uu___96_11 = env
in {FStar_TypeChecker_Env.solver = uu___96_11.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___96_11.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___96_11.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___96_11.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___96_11.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___96_11.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___96_11.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___96_11.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___96_11.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___96_11.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___96_11.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___96_11.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___96_11.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___96_11.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___96_11.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___96_11.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___96_11.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___96_11.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___96_11.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___96_11.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___96_11.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___96_11.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___96_11.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), ((Prims.parse_int "0"))))}))
end
| None -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (

let lid = (match (lids) with
| [] -> begin
(let _0_229 = (FStar_TypeChecker_Env.current_module env)
in (let _0_228 = (let _0_227 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_right _0_227 FStar_Util.string_of_int))
in (FStar_Ident.lid_add_suffix _0_229 _0_228)))
end
| (l)::uu____18 -> begin
l
end)
in (

let uu___97_20 = env
in {FStar_TypeChecker_Env.solver = uu___97_20.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___97_20.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___97_20.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___97_20.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___97_20.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___97_20.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___97_20.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___97_20.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___97_20.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___97_20.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___97_20.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___97_20.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___97_20.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___97_20.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___97_20.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___97_20.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___97_20.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___97_20.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___97_20.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___97_20.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___97_20.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___97_20.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___97_20.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), ((Prims.parse_int "0"))))})))
end)))


let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_Options.log_types ()) && (not ((let _0_230 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _0_230))))))


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let uu____35 = (FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k)
in (match (uu____35) with
| (t, c, g) -> begin
((FStar_ST.write t.FStar_Syntax_Syntax.tk (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)));
(FStar_TypeChecker_Rel.force_trivial_guard env g);
t;
)
end)))


let recheck_debug : Prims.string  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s env t -> ((

let uu____57 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____57) with
| true -> begin
(let _0_231 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Term has been %s-transformed to:\n%s\n----------\n" s _0_231))
end
| uu____58 -> begin
()
end));
(

let uu____59 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (uu____59) with
| (t', uu____64, uu____65) -> begin
((

let uu____67 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____67) with
| true -> begin
(let _0_232 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print1 "Re-checked; got:\n%s\n----------\n" _0_232))
end
| uu____68 -> begin
()
end));
t;
)
end));
))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _0_233 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _0_233)))


let check_nogen = (fun env t k -> (

let t = (tc_check_trivial_guard env t k)
in (let _0_234 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (([]), (_0_234)))))


let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let uu____112 = (FStar_TypeChecker_TcTerm.tc_binders env tps)
in (match (uu____112) with
| (tps, env, g, us) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
((tps), (env), (us));
)
end)))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun env m s -> (

let fail = (fun uu____145 -> (Prims.raise (FStar_Errors.Error ((let _0_235 = (FStar_TypeChecker_Err.unexpected_signature_for_monad env m s)
in ((_0_235), ((FStar_Ident.range_of_lid m))))))))
in (

let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, uu____173))::((wp, uu____175))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____184 -> begin
(fail ())
end))
end
| uu____185 -> begin
(fail ())
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let uu____215 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (uu____215) with
| (uvs, c) -> begin
((uvs), ([]), (c))
end))
end
| uu____231 -> begin
(

let t' = (FStar_Syntax_Util.arrow binders c)
in (

let uu____238 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (uu____238) with
| (uvs, t') -> begin
(

let uu____249 = (FStar_Syntax_Subst.compress t').FStar_Syntax_Syntax.n
in (match (uu____249) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
((uvs), (binders), (c))
end
| uu____273 -> begin
(failwith "Impossible")
end))
end)))
end))


let rec tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (

let uu____342 = (FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____342) with
| (effect_params_un, signature_un, opening) -> begin
(

let uu____349 = (tc_tparams env0 effect_params_un)
in (match (uu____349) with
| (effect_params, env, uu____355) -> begin
(

let uu____356 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (uu____356) with
| (signature, uu____360) -> begin
(

let ed = (

let uu___98_362 = ed
in {FStar_Syntax_Syntax.qualifiers = uu___98_362.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___98_362.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___98_362.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___98_362.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = uu___98_362.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = uu___98_362.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = uu___98_362.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = uu___98_362.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = uu___98_362.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = uu___98_362.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = uu___98_362.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = uu___98_362.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = uu___98_362.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = uu___98_362.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = uu___98_362.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = uu___98_362.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = uu___98_362.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = uu___98_362.FStar_Syntax_Syntax.actions})
in (

let ed = (match (effect_params) with
| [] -> begin
ed
end
| uu____366 -> begin
(

let op = (fun ts -> (

let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in (([]), (t1))))
in (

let uu___99_384 = ed
in (let _0_251 = (op ed.FStar_Syntax_Syntax.ret_wp)
in (let _0_250 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _0_249 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _0_248 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _0_247 = (op ed.FStar_Syntax_Syntax.stronger)
in (let _0_246 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _0_245 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _0_244 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _0_243 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _0_242 = (op ed.FStar_Syntax_Syntax.trivial)
in (let _0_241 = (Prims.snd (op (([]), (ed.FStar_Syntax_Syntax.repr))))
in (let _0_240 = (op ed.FStar_Syntax_Syntax.return_repr)
in (let _0_239 = (op ed.FStar_Syntax_Syntax.bind_repr)
in (let _0_238 = (FStar_List.map (fun a -> (

let uu___100_388 = a
in (let _0_237 = (Prims.snd (op (([]), (a.FStar_Syntax_Syntax.action_defn))))
in (let _0_236 = (Prims.snd (op (([]), (a.FStar_Syntax_Syntax.action_typ))))
in {FStar_Syntax_Syntax.action_name = uu___100_388.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___100_388.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___100_388.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _0_237; FStar_Syntax_Syntax.action_typ = _0_236})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.qualifiers = uu___99_384.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___99_384.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___99_384.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___99_384.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu___99_384.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = uu___99_384.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _0_251; FStar_Syntax_Syntax.bind_wp = _0_250; FStar_Syntax_Syntax.if_then_else = _0_249; FStar_Syntax_Syntax.ite_wp = _0_248; FStar_Syntax_Syntax.stronger = _0_247; FStar_Syntax_Syntax.close_wp = _0_246; FStar_Syntax_Syntax.assert_p = _0_245; FStar_Syntax_Syntax.assume_p = _0_244; FStar_Syntax_Syntax.null_wp = _0_243; FStar_Syntax_Syntax.trivial = _0_242; FStar_Syntax_Syntax.repr = _0_241; FStar_Syntax_Syntax.return_repr = _0_240; FStar_Syntax_Syntax.bind_repr = _0_239; FStar_Syntax_Syntax.actions = _0_238}))))))))))))))))
end)
in (

let wp_with_fresh_result_type = (fun env mname signature -> (

let fail = (fun t -> (Prims.raise (FStar_Errors.Error ((let _0_252 = (FStar_TypeChecker_Err.unexpected_signature_for_monad env mname t)
in ((_0_252), ((FStar_Ident.range_of_lid mname))))))))
in (

let uu____419 = (FStar_Syntax_Subst.compress signature).FStar_Syntax_Syntax.n
in (match (uu____419) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, uu____442))::((wp, uu____444))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____453 -> begin
(fail signature)
end))
end
| uu____454 -> begin
(fail signature)
end))))
in (

let uu____455 = (wp_with_fresh_result_type env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (uu____455) with
| (a, wp_a) -> begin
(

let fresh_effect_signature = (fun uu____473 -> (

let uu____474 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (uu____474) with
| (signature, uu____482) -> begin
(wp_with_fresh_result_type env ed.FStar_Syntax_Syntax.mname signature)
end)))
in (

let env = (let _0_253 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _0_253))
in ((

let uu____485 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED")))
in (match (uu____485) with
| true -> begin
(let _0_258 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _0_257 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _0_256 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _0_255 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Syntax.bv_to_name a))
in (let _0_254 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.sort)
in (FStar_Util.print5 "Checking effect signature: %s %s : %s\n(a is %s:%s)\n" _0_258 _0_257 _0_256 _0_255 _0_254))))))
end
| uu____486 -> begin
()
end));
(

let check_and_gen' = (fun env uu____498 k -> (match (uu____498) with
| (uu____503, t) -> begin
(check_and_gen env t k)
end))
in (

let return_wp = (

let expected_k = (let _0_263 = (let _0_261 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_260 = (let _0_259 = (FStar_Syntax_Syntax.null_binder (FStar_Syntax_Syntax.bv_to_name a))
in (_0_259)::[])
in (_0_261)::_0_260))
in (let _0_262 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _0_263 _0_262)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret_wp expected_k))
in (

let bind_wp = (

let uu____512 = (fresh_effect_signature ())
in (match (uu____512) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _0_266 = (let _0_264 = (FStar_Syntax_Syntax.null_binder (FStar_Syntax_Syntax.bv_to_name a))
in (_0_264)::[])
in (let _0_265 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _0_266 _0_265)))
in (

let expected_k = (let _0_277 = (let _0_275 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _0_274 = (let _0_273 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_272 = (let _0_271 = (FStar_Syntax_Syntax.mk_binder b)
in (let _0_270 = (let _0_269 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _0_268 = (let _0_267 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (_0_267)::[])
in (_0_269)::_0_268))
in (_0_271)::_0_270))
in (_0_273)::_0_272))
in (_0_275)::_0_274))
in (let _0_276 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _0_277 _0_276)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else = (

let p = (let _0_279 = (let _0_278 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _0_278 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _0_279))
in (

let expected_k = (let _0_288 = (let _0_286 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_285 = (let _0_284 = (FStar_Syntax_Syntax.mk_binder p)
in (let _0_283 = (let _0_282 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _0_281 = (let _0_280 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_0_280)::[])
in (_0_282)::_0_281))
in (_0_284)::_0_283))
in (_0_286)::_0_285))
in (let _0_287 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _0_288 _0_287)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (let _0_293 = (let _0_291 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_290 = (let _0_289 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_0_289)::[])
in (_0_291)::_0_290))
in (let _0_292 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _0_293 _0_292)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let uu____541 = (FStar_Syntax_Util.type_u ())
in (match (uu____541) with
| (t, uu____545) -> begin
(

let expected_k = (let _0_300 = (let _0_298 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_297 = (let _0_296 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _0_295 = (let _0_294 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_0_294)::[])
in (_0_296)::_0_295))
in (_0_298)::_0_297))
in (let _0_299 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _0_300 _0_299)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (let _0_302 = (let _0_301 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _0_301 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _0_302))
in (

let b_wp_a = (let _0_305 = (let _0_303 = (FStar_Syntax_Syntax.null_binder (FStar_Syntax_Syntax.bv_to_name b))
in (_0_303)::[])
in (let _0_304 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _0_305 _0_304)))
in (

let expected_k = (let _0_312 = (let _0_310 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_309 = (let _0_308 = (FStar_Syntax_Syntax.mk_binder b)
in (let _0_307 = (let _0_306 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_0_306)::[])
in (_0_308)::_0_307))
in (_0_310)::_0_309))
in (let _0_311 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _0_312 _0_311)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (let _0_320 = (let _0_318 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_317 = (let _0_316 = (FStar_Syntax_Syntax.null_binder (let _0_313 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _0_313 Prims.fst)))
in (let _0_315 = (let _0_314 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_0_314)::[])
in (_0_316)::_0_315))
in (_0_318)::_0_317))
in (let _0_319 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _0_320 _0_319)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (let _0_328 = (let _0_326 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_325 = (let _0_324 = (FStar_Syntax_Syntax.null_binder (let _0_321 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _0_321 Prims.fst)))
in (let _0_323 = (let _0_322 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_0_322)::[])
in (_0_324)::_0_323))
in (_0_326)::_0_325))
in (let _0_327 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _0_328 _0_327)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (let _0_331 = (let _0_329 = (FStar_Syntax_Syntax.mk_binder a)
in (_0_329)::[])
in (let _0_330 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _0_331 _0_330)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let uu____576 = (FStar_Syntax_Util.type_u ())
in (match (uu____576) with
| (t, uu____580) -> begin
(

let expected_k = (let _0_336 = (let _0_334 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_333 = (let _0_332 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_0_332)::[])
in (_0_334)::_0_333))
in (let _0_335 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _0_336 _0_335)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let uu____584 = (

let uu____590 = (FStar_Syntax_Subst.compress ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n
in (match (uu____590) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((ed.FStar_Syntax_Syntax.repr), (ed.FStar_Syntax_Syntax.bind_repr), (ed.FStar_Syntax_Syntax.return_repr), (ed.FStar_Syntax_Syntax.actions))
end
| uu____597 -> begin
(

let repr = (

let uu____599 = (FStar_Syntax_Util.type_u ())
in (match (uu____599) with
| (t, uu____603) -> begin
(

let expected_k = (let _0_341 = (let _0_339 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_338 = (let _0_337 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_0_337)::[])
in (_0_339)::_0_338))
in (let _0_340 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _0_341 _0_340)))
in (tc_check_trivial_guard env ed.FStar_Syntax_Syntax.repr expected_k))
end))
in (

let mk_repr' = (fun t wp -> (

let repr = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env repr)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_345 = (let _0_344 = (FStar_Syntax_Syntax.as_arg t)
in (let _0_343 = (let _0_342 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_342)::[])
in (_0_344)::_0_343))
in ((repr), (_0_345)))))) None FStar_Range.dummyRange)))
in (

let mk_repr = (fun a wp -> (let _0_346 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_repr' _0_346 wp)))
in (

let destruct_repr = (fun t -> (

let uu____645 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____645) with
| FStar_Syntax_Syntax.Tm_app (uu____652, ((t, uu____654))::((wp, uu____656))::[]) -> begin
((t), (wp))
end
| uu____690 -> begin
(failwith "Unexpected repr type")
end)))
in (

let bind_repr = (

let r = (let _0_347 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_0 FStar_Syntax_Syntax.Delta_constant None)
in (FStar_All.pipe_right _0_347 FStar_Syntax_Syntax.fv_to_tm))
in (

let uu____699 = (fresh_effect_signature ())
in (match (uu____699) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _0_350 = (let _0_348 = (FStar_Syntax_Syntax.null_binder (FStar_Syntax_Syntax.bv_to_name a))
in (_0_348)::[])
in (let _0_349 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _0_350 _0_349)))
in (

let wp_f = (FStar_Syntax_Syntax.gen_bv "wp_f" None wp_a)
in (

let wp_g = (FStar_Syntax_Syntax.gen_bv "wp_g" None a_wp_b)
in (

let x_a = (let _0_351 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _0_351))
in (

let wp_g_x = ((let _0_355 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (let _0_354 = (let _0_353 = (let _0_352 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_352))
in (_0_353)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _0_355 _0_354))) None FStar_Range.dummyRange)
in (

let res = (

let wp = ((let _0_367 = (let _0_356 = (FStar_TypeChecker_Env.inst_tscheme bind_wp)
in (FStar_All.pipe_right _0_356 Prims.snd))
in (let _0_366 = (let _0_365 = (let _0_364 = (let _0_363 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _0_362 = (let _0_361 = (FStar_Syntax_Syntax.bv_to_name b)
in (let _0_360 = (let _0_359 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (let _0_358 = (let _0_357 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (_0_357)::[])
in (_0_359)::_0_358))
in (_0_361)::_0_360))
in (_0_363)::_0_362))
in (r)::_0_364)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _0_365))
in (FStar_Syntax_Syntax.mk_Tm_app _0_367 _0_366))) None FStar_Range.dummyRange)
in (mk_repr b wp))
in (

let expected_k = (let _0_385 = (let _0_383 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_382 = (let _0_381 = (FStar_Syntax_Syntax.mk_binder b)
in (let _0_380 = (let _0_379 = (FStar_Syntax_Syntax.mk_binder wp_f)
in (let _0_378 = (let _0_377 = (FStar_Syntax_Syntax.null_binder (let _0_368 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (mk_repr a _0_368)))
in (let _0_376 = (let _0_375 = (FStar_Syntax_Syntax.mk_binder wp_g)
in (let _0_374 = (let _0_373 = (FStar_Syntax_Syntax.null_binder (let _0_372 = (let _0_369 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_0_369)::[])
in (let _0_371 = (let _0_370 = (mk_repr b wp_g_x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _0_370))
in (FStar_Syntax_Util.arrow _0_372 _0_371))))
in (_0_373)::[])
in (_0_375)::_0_374))
in (_0_377)::_0_376))
in (_0_379)::_0_378))
in (_0_381)::_0_380))
in (_0_383)::_0_382))
in (let _0_384 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _0_385 _0_384)))
in (

let uu____738 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (uu____738) with
| (expected_k, uu____743, uu____744) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos)
in (

let env = (

let uu___101_748 = env
in {FStar_TypeChecker_Env.solver = uu___101_748.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___101_748.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___101_748.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___101_748.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___101_748.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___101_748.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___101_748.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___101_748.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___101_748.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___101_748.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___101_748.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___101_748.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___101_748.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___101_748.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___101_748.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___101_748.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___101_748.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___101_748.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___101_748.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___101_748.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___101_748.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___101_748.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___101_748.FStar_TypeChecker_Env.qname_and_index})
in (

let br = (check_and_gen' env ed.FStar_Syntax_Syntax.bind_repr expected_k)
in br)))
end)))))))))
end)))
in (

let return_repr = (

let x_a = (let _0_386 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _0_386))
in (

let res = (

let wp = ((let _0_393 = (let _0_387 = (FStar_TypeChecker_Env.inst_tscheme return_wp)
in (FStar_All.pipe_right _0_387 Prims.snd))
in (let _0_392 = (let _0_391 = (let _0_390 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _0_389 = (let _0_388 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (_0_388)::[])
in (_0_390)::_0_389))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _0_391))
in (FStar_Syntax_Syntax.mk_Tm_app _0_393 _0_392))) None FStar_Range.dummyRange)
in (mk_repr a wp))
in (

let expected_k = (let _0_398 = (let _0_396 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_395 = (let _0_394 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_0_394)::[])
in (_0_396)::_0_395))
in (let _0_397 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _0_398 _0_397)))
in (

let uu____770 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (uu____770) with
| (expected_k, uu____778, uu____779) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos)
in (

let uu____782 = (check_and_gen' env ed.FStar_Syntax_Syntax.return_repr expected_k)
in (match (uu____782) with
| (univs, repr) -> begin
(match (univs) with
| [] -> begin
(([]), (repr))
end
| uu____794 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected universe-polymorphic return for effect"), (repr.FStar_Syntax_Syntax.pos)))))
end)
end)))
end)))))
in (

let actions = (

let check_action = (fun act -> (

let uu____805 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env act.FStar_Syntax_Syntax.action_typ)
in (match (uu____805) with
| (act_typ, uu____810, g_t) -> begin
(

let env' = (FStar_TypeChecker_Env.set_expected_typ env act_typ)
in ((

let uu____814 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____814) with
| true -> begin
(let _0_400 = (FStar_Syntax_Print.term_to_string act.FStar_Syntax_Syntax.action_defn)
in (let _0_399 = (FStar_Syntax_Print.term_to_string act_typ)
in (FStar_Util.print3 "Checking action %s:\n[definition]: %s\n[cps\'d type]: %s\n" (FStar_Ident.text_of_lid act.FStar_Syntax_Syntax.action_name) _0_400 _0_399)))
end
| uu____815 -> begin
()
end));
(

let uu____816 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' act.FStar_Syntax_Syntax.action_defn)
in (match (uu____816) with
| (act_defn, uu____821, g_a) -> begin
(

let act_defn = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env act_defn)
in (

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
in (

let uu____825 = (

let act_typ = (FStar_Syntax_Subst.compress act_typ)
in (match (act_typ.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____843 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____843) with
| (bs, uu____849) -> begin
(

let res = (mk_repr' FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun)
in (

let k = (let _0_401 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs _0_401))
in (

let uu____856 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env k)
in (match (uu____856) with
| (k, uu____863, g) -> begin
((k), (g))
end))))
end))
end
| uu____865 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_404 = (let _0_403 = (FStar_Syntax_Print.term_to_string act_typ)
in (let _0_402 = (FStar_Syntax_Print.tag_of_term act_typ)
in (FStar_Util.format2 "Actions must have function types (not: %s, a.k.a. %s)" _0_403 _0_402)))
in ((_0_404), (act_defn.FStar_Syntax_Syntax.pos))))))
end))
in (match (uu____825) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env act_typ expected_k)
in ((let _0_407 = (let _0_406 = (let _0_405 = (FStar_TypeChecker_Rel.conj_guard g_t g)
in (FStar_TypeChecker_Rel.conj_guard g_k _0_405))
in (FStar_TypeChecker_Rel.conj_guard g_a _0_406))
in (FStar_TypeChecker_Rel.force_trivial_guard env _0_407));
(

let act_typ = (

let uu____875 = (FStar_Syntax_Subst.compress expected_k).FStar_Syntax_Syntax.n
in (match (uu____875) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____890 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____890) with
| (bs, c) -> begin
(

let uu____897 = (destruct_repr (FStar_Syntax_Util.comp_result c))
in (match (uu____897) with
| (a, wp) -> begin
(

let c = (let _0_411 = (let _0_408 = (env.FStar_TypeChecker_Env.universe_of env a)
in (_0_408)::[])
in (let _0_410 = (let _0_409 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_409)::[])
in {FStar_Syntax_Syntax.comp_univs = _0_411; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a; FStar_Syntax_Syntax.effect_args = _0_410; FStar_Syntax_Syntax.flags = []}))
in (let _0_412 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Util.arrow bs _0_412)))
end))
end))
end
| uu____917 -> begin
(failwith "")
end))
in (

let uu____920 = (FStar_TypeChecker_Util.generalize_universes env act_defn)
in (match (uu____920) with
| (univs, act_defn) -> begin
(

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
in (

let uu___102_926 = act
in {FStar_Syntax_Syntax.action_name = uu___102_926.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___102_926.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = act_defn; FStar_Syntax_Syntax.action_typ = act_typ}))
end)));
))
end))))
end));
))
end)))
in (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.map check_action)))
in ((repr), (bind_repr), (return_repr), (actions)))))))))
end))
in (match (uu____584) with
| (repr, bind_repr, return_repr, actions) -> begin
(

let t = (let _0_413 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _0_413))
in (

let uu____942 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (uu____942) with
| (univs, t) -> begin
(

let signature = (

let uu____948 = (let _0_414 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in ((effect_params), (_0_414)))
in (match (uu____948) with
| ([], uu____951) -> begin
t
end
| (uu____957, FStar_Syntax_Syntax.Tm_arrow (uu____958, c)) -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____970 -> begin
(failwith "Impossible")
end))
in (

let close = (fun n ts -> (

let ts = (let _0_415 = (FStar_Syntax_Subst.close_tscheme effect_params ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _0_415))
in (

let m = (FStar_List.length (Prims.fst ts))
in ((

let uu____985 = (((n >= (Prims.parse_int "0")) && (not ((FStar_Syntax_Util.is_unknown (Prims.snd ts))))) && (m <> n))
in (match (uu____985) with
| true -> begin
(

let error = (match ((m < n)) with
| true -> begin
"not universe-polymorphic enough"
end
| uu____993 -> begin
"too universe-polymorphic"
end)
in (failwith (let _0_417 = (FStar_Util.string_of_int n)
in (let _0_416 = (FStar_Syntax_Print.tscheme_to_string ts)
in (FStar_Util.format3 "The effect combinator is %s (n=%s) (%s)" error _0_417 _0_416)))))
end
| uu____994 -> begin
()
end));
ts;
))))
in (

let close_action = (fun act -> (

let uu____999 = (close (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_defn)))
in (match (uu____999) with
| (univs, defn) -> begin
(

let uu____1004 = (close (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_typ)))
in (match (uu____1004) with
| (univs', typ) -> begin
(

let uu___103_1010 = act
in {FStar_Syntax_Syntax.action_name = uu___103_1010.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___103_1010.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = defn; FStar_Syntax_Syntax.action_typ = typ})
end))
end)))
in (

let nunivs = (FStar_List.length univs)
in (

let ed = (

let uu___104_1015 = ed
in (let _0_431 = (close (Prims.parse_int "0") return_wp)
in (let _0_430 = (close (Prims.parse_int "1") bind_wp)
in (let _0_429 = (close (Prims.parse_int "0") if_then_else)
in (let _0_428 = (close (Prims.parse_int "0") ite_wp)
in (let _0_427 = (close (Prims.parse_int "0") stronger)
in (let _0_426 = (close (Prims.parse_int "1") close_wp)
in (let _0_425 = (close (Prims.parse_int "0") assert_p)
in (let _0_424 = (close (Prims.parse_int "0") assume_p)
in (let _0_423 = (close (Prims.parse_int "0") null_wp)
in (let _0_422 = (close (Prims.parse_int "0") trivial_wp)
in (let _0_421 = (Prims.snd (close (Prims.parse_int "0") (([]), (repr))))
in (let _0_420 = (close (Prims.parse_int "0") return_repr)
in (let _0_419 = (close (Prims.parse_int "1") bind_repr)
in (let _0_418 = (FStar_List.map close_action actions)
in {FStar_Syntax_Syntax.qualifiers = uu___104_1015.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___104_1015.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___104_1015.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _0_431; FStar_Syntax_Syntax.bind_wp = _0_430; FStar_Syntax_Syntax.if_then_else = _0_429; FStar_Syntax_Syntax.ite_wp = _0_428; FStar_Syntax_Syntax.stronger = _0_427; FStar_Syntax_Syntax.close_wp = _0_426; FStar_Syntax_Syntax.assert_p = _0_425; FStar_Syntax_Syntax.assume_p = _0_424; FStar_Syntax_Syntax.null_wp = _0_423; FStar_Syntax_Syntax.trivial = _0_422; FStar_Syntax_Syntax.repr = _0_421; FStar_Syntax_Syntax.return_repr = _0_420; FStar_Syntax_Syntax.bind_repr = _0_419; FStar_Syntax_Syntax.actions = _0_418})))))))))))))))
in ((

let uu____1019 = ((FStar_TypeChecker_Env.debug env FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ED"))))
in (match (uu____1019) with
| true -> begin
(FStar_Util.print_string (FStar_Syntax_Print.eff_decl_to_string false ed))
end
| uu____1020 -> begin
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

let uu____1023 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____1023) with
| (effect_binders_un, signature_un) -> begin
(

let uu____1033 = (tc_tparams env effect_binders_un)
in (match (uu____1033) with
| (effect_binders, env, uu____1044) -> begin
(

let uu____1045 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (uu____1045) with
| (signature, uu____1054) -> begin
(

let effect_binders = (FStar_List.map (fun uu____1063 -> (match (uu____1063) with
| (bv, qual) -> begin
(let _0_433 = (

let uu___105_1070 = bv
in (let _0_432 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___105_1070.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___105_1070.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_432}))
in ((_0_433), (qual)))
end)) effect_binders)
in (

let uu____1071 = (

let uu____1076 = (FStar_Syntax_Subst.compress signature_un).FStar_Syntax_Syntax.n
in (match (uu____1076) with
| FStar_Syntax_Syntax.Tm_arrow (((a, uu____1082))::[], effect_marker) -> begin
((a), (effect_marker))
end
| uu____1097 -> begin
(failwith "bad shape for effect-for-free signature")
end))
in (match (uu____1071) with
| (a, effect_marker) -> begin
(

let a = (

let uu____1114 = (FStar_Syntax_Syntax.is_null_bv a)
in (match (uu____1114) with
| true -> begin
(let _0_434 = Some ((FStar_Syntax_Syntax.range_of_bv a))
in (FStar_Syntax_Syntax.gen_bv "a" _0_434 a.FStar_Syntax_Syntax.sort))
end
| uu____1115 -> begin
a
end))
in (

let open_and_check = (fun t -> (

let subst = (FStar_Syntax_Subst.opening_of_binders effect_binders)
in (

let t = (FStar_Syntax_Subst.subst subst t)
in (

let uu____1124 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (uu____1124) with
| (t, comp, uu____1132) -> begin
((t), (comp))
end)))))
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None signature.FStar_Syntax_Syntax.pos))
in (

let uu____1143 = (open_and_check ed.FStar_Syntax_Syntax.repr)
in (match (uu____1143) with
| (repr, _comp) -> begin
((

let uu____1154 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____1154) with
| true -> begin
(let _0_435 = (FStar_Syntax_Print.term_to_string repr)
in (FStar_Util.print1 "Representation is: %s\n" _0_435))
end
| uu____1155 -> begin
()
end));
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange))
in (

let wp_type = (FStar_TypeChecker_DMFF.star_type dmff_env repr)
in (

let wp_type = (recheck_debug "*" env wp_type)
in (

let wp_a = (let _0_440 = (mk (FStar_Syntax_Syntax.Tm_app ((let _0_439 = (let _0_438 = (let _0_437 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _0_436 = (FStar_Syntax_Syntax.as_implicit false)
in ((_0_437), (_0_436))))
in (_0_438)::[])
in ((wp_type), (_0_439))))))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _0_440))
in (

let effect_signature = (

let binders = (let _0_445 = (let _0_441 = (FStar_Syntax_Syntax.as_implicit false)
in ((a), (_0_441)))
in (let _0_444 = (let _0_443 = (let _0_442 = (FStar_Syntax_Syntax.gen_bv "dijkstra_wp" None wp_a)
in (FStar_All.pipe_right _0_442 FStar_Syntax_Syntax.mk_binder))
in (_0_443)::[])
in (_0_445)::_0_444))
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

let uu____1206 = item
in (match (uu____1206) with
| (u_item, item) -> begin
(

let uu____1218 = (open_and_check item)
in (match (uu____1218) with
| (item, item_comp) -> begin
((

let uu____1228 = (not ((FStar_Syntax_Util.is_total_lcomp item_comp)))
in (match (uu____1228) with
| true -> begin
(Prims.raise (FStar_Errors.Err ((let _0_447 = (FStar_Syntax_Print.term_to_string item)
in (let _0_446 = (FStar_Syntax_Print.lcomp_to_string item_comp)
in (FStar_Util.format2 "Computation for [%s] is not total : %s !" _0_447 _0_446))))))
end
| uu____1229 -> begin
()
end));
(

let uu____1230 = (FStar_TypeChecker_DMFF.star_expr dmff_env item)
in (match (uu____1230) with
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

let uu____1243 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.bind_repr)
in (match (uu____1243) with
| (dmff_env, uu____1254, bind_wp, bind_elab) -> begin
(

let uu____1257 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.return_repr)
in (match (uu____1257) with
| (dmff_env, uu____1268, return_wp, return_elab) -> begin
(

let lift_from_pure_wp = (

let uu____1272 = (FStar_Syntax_Subst.compress return_wp).FStar_Syntax_Syntax.n
in (match (uu____1272) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(

let uu____1308 = (

let uu____1316 = (let _0_448 = (FStar_Syntax_Util.abs bs body None)
in (FStar_Syntax_Subst.open_term ((b1)::(b2)::[]) _0_448))
in (match (uu____1316) with
| ((b1)::(b2)::[], body) -> begin
((b1), (b2), (body))
end
| uu____1357 -> begin
(failwith "Impossible : open_term not preserving binders arity")
end))
in (match (uu____1308) with
| (b1, b2, body) -> begin
(

let env0 = (let _0_449 = (FStar_TypeChecker_DMFF.get_env dmff_env)
in (FStar_TypeChecker_Env.push_binders _0_449 ((b1)::(b2)::[])))
in (

let wp_b1 = (let _0_454 = (mk (FStar_Syntax_Syntax.Tm_app ((let _0_453 = (let _0_452 = (let _0_451 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b1))
in (let _0_450 = (FStar_Syntax_Syntax.as_implicit false)
in ((_0_451), (_0_450))))
in (_0_452)::[])
in ((wp_type), (_0_453))))))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env0 _0_454))
in (

let uu____1393 = (let _0_456 = (let _0_455 = (FStar_Syntax_Util.unascribe wp_b1)
in (FStar_TypeChecker_Normalize.eta_expand_with_type body _0_455))
in (FStar_All.pipe_left FStar_Syntax_Util.abs_formals _0_456))
in (match (uu____1393) with
| (bs, body, what') -> begin
(

let t2 = (Prims.fst b2).FStar_Syntax_Syntax.sort
in (

let pure_wp_type = (FStar_TypeChecker_DMFF.double_star t2)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None pure_wp_type)
in (

let body = ((let _0_460 = (FStar_Syntax_Syntax.bv_to_name wp)
in (let _0_459 = (let _0_458 = (let _0_457 = (FStar_Syntax_Util.abs ((b2)::[]) body what')
in ((_0_457), (None)))
in (_0_458)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _0_460 _0_459))) None FStar_Range.dummyRange)
in (let _0_464 = (let _0_462 = (let _0_461 = (FStar_Syntax_Syntax.mk_binder wp)
in (_0_461)::[])
in (b1)::_0_462)
in (let _0_463 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs _0_464 _0_463 (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_GTot_lid), ([]))))))))))))
end))))
end))
end
| uu____1461 -> begin
(failwith "unexpected shape for return")
end))
in (

let return_wp = (

let uu____1463 = (FStar_Syntax_Subst.compress return_wp).FStar_Syntax_Syntax.n
in (match (uu____1463) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(let _0_465 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs ((b1)::(b2)::[]) _0_465 (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_GTot_lid), ([])))))))
end
| uu____1514 -> begin
(failwith "unexpected shape for return")
end))
in (

let bind_wp = (

let uu____1516 = (FStar_Syntax_Subst.compress bind_wp).FStar_Syntax_Syntax.n
in (match (uu____1516) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let r = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (let _0_468 = (let _0_467 = (let _0_466 = (FStar_Syntax_Syntax.null_binder (mk (FStar_Syntax_Syntax.Tm_fvar (r))))
in (_0_466)::[])
in (FStar_List.append _0_467 binders))
in (FStar_Syntax_Util.abs _0_468 body what)))
end
| uu____1543 -> begin
(failwith "unexpected shape for bind")
end))
in (

let apply_close = (fun t -> (match (((FStar_List.length effect_binders) = (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____1560 -> begin
(let _0_470 = (mk (FStar_Syntax_Syntax.Tm_app ((let _0_469 = (Prims.snd (FStar_Syntax_Util.args_of_binders effect_binders))
in ((t), (_0_469))))))
in (FStar_Syntax_Subst.close effect_binders _0_470))
end))
in (

let register = (fun name item -> (

let uu____1579 = (let _0_472 = (mk_lid name)
in (let _0_471 = (FStar_Syntax_Util.abs effect_binders item None)
in (FStar_TypeChecker_Util.mk_toplevel_definition env _0_472 _0_471)))
in (match (uu____1579) with
| (sigelt, fv) -> begin
((let _0_474 = (let _0_473 = (FStar_ST.read sigelts)
in (sigelt)::_0_473)
in (FStar_ST.write sigelts _0_474));
fv;
)
end)))
in (

let lift_from_pure_wp = (register "lift_from_pure" lift_from_pure_wp)
in (

let return_wp = (register "return_wp" return_wp)
in ((let _0_476 = (let _0_475 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true")), (FStar_Range.dummyRange))))::_0_475)
in (FStar_ST.write sigelts _0_476));
(

let return_elab = (register "return_elab" return_elab)
in ((let _0_478 = (let _0_477 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false")), (FStar_Range.dummyRange))))::_0_477)
in (FStar_ST.write sigelts _0_478));
(

let bind_wp = (register "bind_wp" bind_wp)
in ((let _0_480 = (let _0_479 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true")), (FStar_Range.dummyRange))))::_0_479)
in (FStar_ST.write sigelts _0_480));
(

let bind_elab = (register "bind_elab" bind_elab)
in ((let _0_482 = (let _0_481 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false")), (FStar_Range.dummyRange))))::_0_481)
in (FStar_ST.write sigelts _0_482));
(

let uu____1629 = (FStar_List.fold_left (fun uu____1636 action -> (match (uu____1636) with
| (dmff_env, actions) -> begin
(

let uu____1648 = (elaborate_and_star dmff_env ((action.FStar_Syntax_Syntax.action_univs), (action.FStar_Syntax_Syntax.action_defn)))
in (match (uu____1648) with
| (dmff_env, action_t, action_wp, action_elab) -> begin
(

let name = action.FStar_Syntax_Syntax.action_name.FStar_Ident.ident.FStar_Ident.idText
in (

let action_typ_with_wp = (FStar_TypeChecker_DMFF.trans_F dmff_env action_t action_wp)
in (

let action_elab = (register (Prims.strcat name "_elab") action_elab)
in (

let action_typ_with_wp = (register (Prims.strcat name "_complete_type") action_typ_with_wp)
in (let _0_486 = (let _0_485 = (

let uu___106_1665 = action
in (let _0_484 = (apply_close action_elab)
in (let _0_483 = (apply_close action_typ_with_wp)
in {FStar_Syntax_Syntax.action_name = uu___106_1665.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___106_1665.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___106_1665.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _0_484; FStar_Syntax_Syntax.action_typ = _0_483})))
in (_0_485)::actions)
in ((dmff_env), (_0_486)))))))
end))
end)) ((dmff_env), ([])) ed.FStar_Syntax_Syntax.actions)
in (match (uu____1629) with
| (dmff_env, actions) -> begin
(

let actions = (FStar_List.rev actions)
in (

let repr = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp_a" None wp_a)
in (

let binders = (let _0_489 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_488 = (let _0_487 = (FStar_Syntax_Syntax.mk_binder wp)
in (_0_487)::[])
in (_0_489)::_0_488))
in (let _0_496 = (let _0_495 = (mk (FStar_Syntax_Syntax.Tm_app ((let _0_493 = (let _0_492 = (let _0_491 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _0_490 = (FStar_Syntax_Syntax.as_implicit false)
in ((_0_491), (_0_490))))
in (_0_492)::[])
in ((repr), (_0_493))))))
in (let _0_494 = (FStar_Syntax_Syntax.bv_to_name wp)
in (FStar_TypeChecker_DMFF.trans_F dmff_env _0_495 _0_494)))
in (FStar_Syntax_Util.abs binders _0_496 None))))
in (

let repr = (recheck_debug "FC" env repr)
in (

let repr = (register "repr" repr)
in (

let uu____1696 = (

let uu____1701 = (let _0_497 = (FStar_Syntax_Subst.compress wp_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe _0_497)).FStar_Syntax_Syntax.n
in (match (uu____1701) with
| FStar_Syntax_Syntax.Tm_abs ((type_param)::effect_param, arrow, uu____1709) -> begin
(

let uu____1736 = (

let uu____1745 = (FStar_Syntax_Subst.open_term ((type_param)::effect_param) arrow)
in (match (uu____1745) with
| ((b)::bs, body) -> begin
((b), (bs), (body))
end
| uu____1776 -> begin
(failwith "Impossible : open_term nt preserving binders arity")
end))
in (match (uu____1736) with
| (type_param, effect_param, arrow) -> begin
(

let uu____1804 = (let _0_498 = (FStar_Syntax_Subst.compress arrow)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe _0_498)).FStar_Syntax_Syntax.n
in (match (uu____1804) with
| FStar_Syntax_Syntax.Tm_arrow (wp_binders, c) -> begin
(

let uu____1821 = (FStar_Syntax_Subst.open_comp wp_binders c)
in (match (uu____1821) with
| (wp_binders, c) -> begin
(

let uu____1830 = (FStar_List.partition (fun uu____1841 -> (match (uu____1841) with
| (bv, uu____1845) -> begin
(let _0_500 = (let _0_499 = (FStar_Syntax_Free.names bv.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _0_499 (FStar_Util.set_mem (Prims.fst type_param))))
in (FStar_All.pipe_right _0_500 Prims.op_Negation))
end)) wp_binders)
in (match (uu____1830) with
| (pre_args, post_args) -> begin
(

let post = (match (post_args) with
| (post)::[] -> begin
post
end
| uu____1877 -> begin
(failwith (let _0_501 = (FStar_Syntax_Print.term_to_string arrow)
in (FStar_Util.format1 "Impossible: multiple post candidates %s" _0_501)))
end)
in (let _0_503 = (FStar_Syntax_Util.arrow pre_args c)
in (let _0_502 = (FStar_Syntax_Util.abs ((type_param)::effect_param) (Prims.fst post).FStar_Syntax_Syntax.sort None)
in ((_0_503), (_0_502)))))
end))
end))
end
| uu____1892 -> begin
(failwith (let _0_504 = (FStar_Syntax_Print.term_to_string arrow)
in (FStar_Util.format1 "Impossible: pre/post arrow %s" _0_504)))
end))
end))
end
| uu____1897 -> begin
(failwith (let _0_505 = (FStar_Syntax_Print.term_to_string wp_type)
in (FStar_Util.format1 "Impossible: pre/post abs %s" _0_505)))
end))
in (match (uu____1696) with
| (pre, post) -> begin
((Prims.ignore (register "pre" pre));
(Prims.ignore (register "post" post));
(Prims.ignore (register "wp" wp_type));
(

let ed = (

let uu___107_1917 = ed
in (let _0_516 = (FStar_Syntax_Subst.close_binders effect_binders)
in (let _0_515 = (FStar_Syntax_Subst.close effect_binders effect_signature)
in (let _0_514 = (let _0_506 = (apply_close return_wp)
in (([]), (_0_506)))
in (let _0_513 = (let _0_507 = (apply_close bind_wp)
in (([]), (_0_507)))
in (let _0_512 = (apply_close repr)
in (let _0_511 = (let _0_508 = (apply_close return_elab)
in (([]), (_0_508)))
in (let _0_510 = (let _0_509 = (apply_close bind_elab)
in (([]), (_0_509)))
in {FStar_Syntax_Syntax.qualifiers = uu___107_1917.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___107_1917.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___107_1917.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___107_1917.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _0_516; FStar_Syntax_Syntax.signature = _0_515; FStar_Syntax_Syntax.ret_wp = _0_514; FStar_Syntax_Syntax.bind_wp = _0_513; FStar_Syntax_Syntax.if_then_else = uu___107_1917.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = uu___107_1917.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = uu___107_1917.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = uu___107_1917.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = uu___107_1917.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = uu___107_1917.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = uu___107_1917.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = uu___107_1917.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _0_512; FStar_Syntax_Syntax.return_repr = _0_511; FStar_Syntax_Syntax.bind_repr = _0_510; FStar_Syntax_Syntax.actions = actions}))))))))
in (

let uu____1930 = (FStar_TypeChecker_DMFF.gen_wps_for_free env effect_binders a wp_a ed)
in (match (uu____1930) with
| (sigelts', ed) -> begin
((

let uu____1941 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____1941) with
| true -> begin
(FStar_Util.print_string (FStar_Syntax_Print.eff_decl_to_string true ed))
end
| uu____1942 -> begin
()
end));
(

let lift_from_pure_opt = (match (((FStar_List.length effect_binders) = (Prims.parse_int "0"))) with
| true -> begin
(

let lift_from_pure = (let _0_518 = Some ((let _0_517 = (apply_close lift_from_pure_wp)
in (([]), (_0_517))))
in {FStar_Syntax_Syntax.source = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.target = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.lift_wp = _0_518; FStar_Syntax_Syntax.lift = None})
in Some (FStar_Syntax_Syntax.Sig_sub_effect (((lift_from_pure), (FStar_Range.dummyRange)))))
end
| uu____1959 -> begin
None
end)
in (let _0_520 = (let _0_519 = (FStar_List.rev (FStar_ST.read sigelts))
in (FStar_List.append _0_519 sigelts'))
in ((_0_520), (ed), (lift_from_pure_opt))));
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
| (FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, uu____1981, uu____1982, [], r))::(FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, _0_521, [], uu____1987, r1))::(FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, _0_522, [], uu____1992, r2))::[] when (((_0_521 = (Prims.parse_int "0")) && (_0_522 = (Prims.parse_int "0"))) && (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid))) -> begin
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

let lex_top_t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst ((let _0_523 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1) FStar_Syntax_Syntax.Delta_constant None)
in ((_0_523), ((FStar_Syntax_Syntax.U_name (utop))::[])))))) None r1)
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

let a = (let _0_524 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _0_524))
in (

let hd = (let _0_525 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _0_525))
in (

let tl = (let _0_527 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst ((let _0_526 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2) FStar_Syntax_Syntax.Delta_constant None)
in ((_0_526), ((FStar_Syntax_Syntax.U_name (ucons2))::[])))))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _0_527))
in (

let res = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst ((let _0_528 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2) FStar_Syntax_Syntax.Delta_constant None)
in ((_0_528), ((FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[])))))) None r2)
in (let _0_529 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow ((((a), (Some (FStar_Syntax_Syntax.imp_tag))))::(((hd), (None)))::(((tl), (None)))::[]) _0_529))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon (((lex_cons), ((ucons1)::(ucons2)::[]), (lex_cons_t), (FStar_Syntax_Const.lex_t_lid), ((Prims.parse_int "0")), ([]), ([]), (r2)))
in FStar_Syntax_Syntax.Sig_bundle ((let _0_530 = (FStar_TypeChecker_Env.get_range env)
in (((tc)::(dc_lextop)::(dc_lexcons)::[]), ([]), (lids), (_0_530)))))))))))))))))
end
| uu____2114 -> begin
(failwith (let _0_531 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle (((ses), ([]), (lids), (FStar_Range.dummyRange)))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _0_531)))
end))
and tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let uu____2126 = (FStar_Syntax_Util.type_u ())
in (match (uu____2126) with
| (k, uu____2130) -> begin
(

let phi = (let _0_532 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _0_532 (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env)))
in ((FStar_TypeChecker_Util.check_uvars r phi);
FStar_Syntax_Syntax.Sig_assume (((lid), (phi), (quals), (r)));
))
end))))
and tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env ses quals lids -> (

let warn_positivity = (fun l r -> (let _0_534 = (let _0_533 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _0_533))
in (FStar_Errors.diag r _0_534)))
in (

let env0 = env
in (

let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
((warn_positivity tc r);
(

let uu____2184 = (FStar_Syntax_Subst.open_term tps k)
in (match (uu____2184) with
| (tps, k) -> begin
(

let uu____2193 = (FStar_TypeChecker_TcTerm.tc_binders env tps)
in (match (uu____2193) with
| (tps, env_tps, guard_params, us) -> begin
(

let uu____2206 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____2206) with
| (indices, t) -> begin
(

let uu____2230 = (FStar_TypeChecker_TcTerm.tc_binders env_tps indices)
in (match (uu____2230) with
| (indices, env', guard_indices, us') -> begin
(

let uu____2243 = (

let uu____2246 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' t)
in (match (uu____2246) with
| (t, uu____2253, g) -> begin
(let _0_537 = (let _0_536 = (let _0_535 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params _0_535))
in (FStar_TypeChecker_Rel.discharge_guard env' _0_536))
in ((t), (_0_537)))
end))
in (match (uu____2243) with
| (t, guard) -> begin
(

let k = (let _0_538 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _0_538))
in (

let uu____2264 = (FStar_Syntax_Util.type_u ())
in (match (uu____2264) with
| (t_type, u) -> begin
((let _0_539 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _0_539));
(

let t_tc = (let _0_540 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _0_540))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _0_541 = (FStar_TypeChecker_Env.push_let_binding env (FStar_Util.Inr (fv_tc)) (([]), (t_tc)))
in ((_0_541), (FStar_Syntax_Syntax.Sig_inductive_typ (((tc), ([]), (tps), (k), (mutuals), (data), (quals), (r)))), (u), (guard)))))));
)
end)))
end))
end))
end))
end))
end));
)
end
| uu____2289 -> begin
(failwith "impossible")
end))
in (

let positive_if_pure = (fun uu____2299 l -> ())
in (

let tc_data = (fun env tcs uu___83_2315 -> (match (uu___83_2315) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let uu____2334 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun uu____2348 -> (match (uu____2348) with
| (se, u_tc) -> begin
(

let uu____2357 = (let _0_542 = (FStar_Util.must (FStar_Syntax_Util.lid_of_sigelt se))
in (FStar_Ident.lid_equals tc_lid _0_542))
in (match (uu____2357) with
| true -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____2366, uu____2367, tps, uu____2369, uu____2370, uu____2371, uu____2372, uu____2373) -> begin
(

let tps = (FStar_All.pipe_right tps (FStar_List.map (fun uu____2394 -> (match (uu____2394) with
| (x, uu____2401) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let tps = (FStar_Syntax_Subst.open_binders tps)
in Some ((let _0_543 = (FStar_TypeChecker_Env.push_binders env tps)
in ((_0_543), (tps), (u_tc))))))
end
| uu____2407 -> begin
(failwith "Impossible")
end)
end
| uu____2412 -> begin
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
| uu____2437 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected data constructor"), (r)))))
end)
end))
in (match (uu____2334) with
| (env, tps, u_tc) -> begin
(

let uu____2446 = (

let uu____2454 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____2454) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let uu____2474 = (FStar_Util.first_N ntps bs)
in (match (uu____2474) with
| (uu____2492, bs') -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs'), (res)))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i uu____2524 -> (match (uu____2524) with
| (x, uu____2528) -> begin
FStar_Syntax_Syntax.DB ((((ntps - ((Prims.parse_int "1") + i))), (x)))
end))))
in (FStar_Syntax_Util.arrow_formals (FStar_Syntax_Subst.subst subst t))))
end))
end
| uu____2529 -> begin
(([]), (t))
end))
in (match (uu____2446) with
| (arguments, result) -> begin
((

let uu____2550 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____2550) with
| true -> begin
(let _0_546 = (FStar_Syntax_Print.lid_to_string c)
in (let _0_545 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _0_544 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _0_546 _0_545 _0_544))))
end
| uu____2551 -> begin
()
end));
(

let uu____2552 = (tc_tparams env arguments)
in (match (uu____2552) with
| (arguments, env', us) -> begin
(

let uu____2561 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env' result)
in (match (uu____2561) with
| (result, res_lcomp) -> begin
((

let uu____2569 = (FStar_Syntax_Subst.compress res_lcomp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n
in (match (uu____2569) with
| FStar_Syntax_Syntax.Tm_type (uu____2570) -> begin
()
end
| ty -> begin
(Prims.raise (FStar_Errors.Error ((let _0_549 = (let _0_548 = (FStar_Syntax_Print.term_to_string result)
in (let _0_547 = (FStar_Syntax_Print.term_to_string res_lcomp.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "The type of %s is %s, but since this is the result type of a constructor its type should be Type" _0_548 _0_547)))
in ((_0_549), (r))))))
end));
(

let uu____2572 = (FStar_Syntax_Util.head_and_args result)
in (match (uu____2572) with
| (head, uu____2585) -> begin
((

let uu____2601 = (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
in (match (uu____2601) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| uu____2603 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_552 = (let _0_551 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (let _0_550 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" _0_551 _0_550)))
in ((_0_552), (r))))))
end));
(

let g = (FStar_List.fold_left2 (fun g uu____2608 u_x -> (match (uu____2608) with
| (x, uu____2613) -> begin
(

let _0_553 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _0_553))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _0_556 = (let _0_554 = (FStar_All.pipe_right tps (FStar_List.map (fun uu____2630 -> (match (uu____2630) with
| (x, uu____2637) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append _0_554 arguments))
in (let _0_555 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _0_556 _0_555)))
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
| uu____2644 -> begin
(failwith "impossible")
end))
in (

let generalize_and_inst_within = (fun env g tcs datas -> ((FStar_TypeChecker_Rel.force_trivial_guard env g);
(

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun uu___84_2673 -> (match (uu___84_2673) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____2674, uu____2675, tps, k, uu____2678, uu____2679, uu____2680, uu____2681) -> begin
(FStar_Syntax_Syntax.null_binder (let _0_557 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _0_557)))
end
| uu____2692 -> begin
(failwith "Impossible")
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun uu___85_2697 -> (match (uu___85_2697) with
| FStar_Syntax_Syntax.Sig_datacon (uu____2698, uu____2699, t, uu____2701, uu____2702, uu____2703, uu____2704, uu____2705) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| uu____2710 -> begin
(failwith "Impossible")
end))))
in (

let t = (let _0_558 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _0_558))
in ((

let uu____2715 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____2715) with
| true -> begin
(let _0_559 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _0_559))
end
| uu____2716 -> begin
()
end));
(

let uu____2717 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (uu____2717) with
| (uvs, t) -> begin
((

let uu____2727 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____2727) with
| true -> begin
(let _0_562 = (let _0_560 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _0_560 (FStar_String.concat ", ")))
in (let _0_561 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _0_562 _0_561)))
end
| uu____2732 -> begin
()
end));
(

let uu____2733 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____2733) with
| (uvs, t) -> begin
(

let uu____2742 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____2742) with
| (args, uu____2755) -> begin
(

let uu____2766 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (uu____2766) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun uu____2801 se -> (match (uu____2801) with
| (x, uu____2806) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____2808, tps, uu____2810, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let uu____2822 = (

let uu____2830 = (FStar_Syntax_Subst.compress ty).FStar_Syntax_Syntax.n
in (match (uu____2830) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____2850 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (uu____2850) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____2893 -> begin
(let _0_563 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) _0_563 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in ((tps), (t)))
end))
end
| uu____2914 -> begin
(([]), (ty))
end))
in (match (uu____2822) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs), (tps), (t), (mutuals), (datas), (quals), (r)))
end)))
end
| uu____2940 -> begin
(failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| uu____2944 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _0_564 -> FStar_Syntax_Syntax.U_name (_0_564))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun uu___86_2961 -> (match (uu___86_2961) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____2966, uu____2967, uu____2968, uu____2969, uu____2970, uu____2971, uu____2972) -> begin
((tc), (uvs_universes))
end
| uu____2980 -> begin
(failwith "Impossible")
end))))
in (FStar_List.map2 (fun uu____2986 d -> (match (uu____2986) with
| (t, uu____2991) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, uu____2993, uu____2994, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (let _0_565 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _0_565 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon (((l), (uvs), (ty), (tc), (ntps), (quals), (mutuals), (r))))
end
| uu____3007 -> begin
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

let uu____3010 = (FStar_All.pipe_right ses (FStar_List.partition (fun uu___87_3020 -> (match (uu___87_3020) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____3021) -> begin
true
end
| uu____3033 -> begin
false
end))))
in (match (uu____3010) with
| (tys, datas) -> begin
((

let uu____3045 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun uu___88_3047 -> (match (uu___88_3047) with
| FStar_Syntax_Syntax.Sig_datacon (uu____3048) -> begin
false
end
| uu____3059 -> begin
true
end))))
in (match (uu____3045) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((let _0_566 = (FStar_TypeChecker_Env.get_range env)
in (("Mutually defined type contains a non-inductive element"), (_0_566))))))
end
| uu____3060 -> begin
()
end));
(

let env0 = env
in (

let uu____3062 = (FStar_List.fold_right (fun tc uu____3076 -> (match (uu____3076) with
| (env, all_tcs, g) -> begin
(

let uu____3098 = (tc_tycon env tc)
in (match (uu____3098) with
| (env, tc, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in ((

let uu____3115 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____3115) with
| true -> begin
(let _0_567 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _0_567))
end
| uu____3116 -> begin
()
end));
(let _0_569 = (let _0_568 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g _0_568))
in ((env), ((((tc), (tc_u)))::all_tcs), (_0_569)));
))
end))
end)) tys ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (uu____3062) with
| (env, tcs, g) -> begin
(

let uu____3140 = (FStar_List.fold_right (fun se uu____3148 -> (match (uu____3148) with
| (datas, g) -> begin
(

let uu____3159 = (tc_data env tcs se)
in (match (uu____3159) with
| (data, g') -> begin
(let _0_570 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((data)::datas), (_0_570)))
end))
end)) datas (([]), (g)))
in (match (uu____3140) with
| (datas, g) -> begin
(

let uu____3177 = (let _0_571 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _0_571 datas))
in (match (uu____3177) with
| (tcs, datas) -> begin
(

let sig_bndle = FStar_Syntax_Syntax.Sig_bundle ((let _0_572 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_0_572))))
in (

let data_ops_ses = (let _0_573 = (FStar_List.map (FStar_TypeChecker_Util.mk_data_operations quals env tcs) datas)
in (FStar_All.pipe_right _0_573 FStar_List.flatten))
in (

let datacon_typ = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (uu____3208, uu____3209, t, uu____3211, uu____3212, uu____3213, uu____3214, uu____3215) -> begin
t
end
| uu____3220 -> begin
(failwith "Impossible!")
end))
in (

let dr = FStar_Range.dummyRange
in (

let optimized_haseq_scheme = (fun uu____3226 -> (

let haseq_ty = (fun usubst us acc ty -> (

let uu____3270 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____3282, bs, t, uu____3285, d_lids, uu____3287, uu____3288) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____3296 -> begin
(failwith "Impossible!")
end)
in (match (uu____3270) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _0_574 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _0_574 t))
in (

let uu____3326 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____3326) with
| (bs, t) -> begin
(

let ibs = (

let uu____3346 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____3346) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____3351) -> begin
ibs
end
| uu____3362 -> begin
[]
end))
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _0_576 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _0_575 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _0_576 _0_575)))
in (

let ind = ((let _0_578 = (FStar_List.map (fun uu____3379 -> (match (uu____3379) with
| (bv, aq) -> begin
(let _0_577 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_0_577), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _0_578)) None dr)
in (

let ind = ((let _0_580 = (FStar_List.map (fun uu____3397 -> (match (uu____3397) with
| (bv, aq) -> begin
(let _0_579 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_0_579), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _0_580)) None dr)
in (

let haseq_ind = ((let _0_582 = (let _0_581 = (FStar_Syntax_Syntax.as_arg ind)
in (_0_581)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _0_582)) None dr)
in (

let bs' = (FStar_List.filter (fun b -> (

let uu____3420 = acc
in (match (uu____3420) with
| (uu____3428, en, uu____3430, uu____3431) -> begin
(

let opt = (let _0_583 = (Prims.fst (FStar_Syntax_Util.type_u ()))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort _0_583 false))
in (match (opt) with
| None -> begin
false
end
| Some (uu____3440) -> begin
true
end))
end))) bs)
in (

let haseq_bs = (FStar_List.fold_left (fun t b -> (let _0_586 = ((let _0_585 = (let _0_584 = (FStar_Syntax_Syntax.as_arg (FStar_Syntax_Syntax.bv_to_name (Prims.fst b)))
in (_0_584)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _0_585)) None dr)
in (FStar_Syntax_Util.mk_conj t _0_586))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml = (

let uu___108_3454 = fml
in (let _0_590 = FStar_Syntax_Syntax.Tm_meta ((let _0_589 = FStar_Syntax_Syntax.Meta_pattern ((let _0_588 = (let _0_587 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_0_587)::[])
in (_0_588)::[]))
in ((fml), (_0_589))))
in {FStar_Syntax_Syntax.n = _0_590; FStar_Syntax_Syntax.tk = uu___108_3454.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___108_3454.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___108_3454.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> ((let _0_593 = (let _0_592 = (FStar_Syntax_Syntax.as_arg (let _0_591 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _0_591 None)))
in (_0_592)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _0_593)) None dr)) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> ((let _0_596 = (let _0_595 = (FStar_Syntax_Syntax.as_arg (let _0_594 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _0_594 None)))
in (_0_595)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _0_596)) None dr)) bs fml)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let uu____3506 = acc
in (match (uu____3506) with
| (l_axioms, env, guard', cond') -> begin
(

let env = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env = (FStar_TypeChecker_Env.push_binders env ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (uu____3540, uu____3541, uu____3542, t_lid, uu____3544, uu____3545, uu____3546, uu____3547) -> begin
(t_lid = lid)
end
| uu____3552 -> begin
(failwith "Impossible")
end)) datas)
in (

let haseq_data = (fun data -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (

let uu____3559 = (FStar_Syntax_Subst.compress dt).FStar_Syntax_Syntax.n
in (match (uu____3559) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____3561) -> begin
(

let dbs = (Prims.snd (FStar_List.splitAt (FStar_List.length bs) dbs))
in (

let dbs = (let _0_597 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _0_597 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let haseq_b = ((let _0_599 = (let _0_598 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_0_598)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _0_599)) None dr)
in (

let sort_range = (Prims.fst b).FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos
in (

let haseq_b = (let _0_601 = (let _0_600 = (FStar_Syntax_Print.term_to_string ind)
in (FStar_Util.format1 "Failed to prove that the type \'%s\' supports decidable equality because of this argument; add the \'noeq\' qualifier" _0_600))
in (FStar_TypeChecker_Util.label _0_601 sort_range haseq_b))
in (FStar_Syntax_Util.mk_conj t haseq_b))))) FStar_Syntax_Util.t_true dbs)
in (FStar_List.fold_right (fun b t -> ((let _0_604 = (let _0_603 = (FStar_Syntax_Syntax.as_arg (let _0_602 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _0_602 None)))
in (_0_603)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _0_604)) None dr)) dbs cond)))))
end
| uu____3622 -> begin
FStar_Syntax_Util.t_true
end)))))
in (

let cond = (FStar_List.fold_left (fun acc d -> (let _0_605 = (haseq_data d)
in (FStar_Syntax_Util.mk_conj acc _0_605))) FStar_Syntax_Util.t_true t_datas)
in (

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (let _0_607 = (FStar_Syntax_Util.mk_conj guard' guard)
in (let _0_606 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml)))::[]))), (env), (_0_607), (_0_606))))))))))
end)))))))))))))))
end))))
end)))
in (

let us = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____3642, us, uu____3644, uu____3645, uu____3646, uu____3647, uu____3648, uu____3649) -> begin
us
end
| uu____3656 -> begin
(failwith "Impossible!")
end))
in (

let uu____3657 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____3657) with
| (usubst, us) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq");
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle);
(

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let uu____3673 = (FStar_List.fold_left (haseq_ty usubst us) (([]), (env), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (uu____3673) with
| (axioms, env, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let uu____3705 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env phi)
in (match (uu____3705) with
| (phi, uu____3710) -> begin
((

let uu____3712 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____3712) with
| true -> begin
(let _0_608 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi)))
in (FStar_TypeChecker_Rel.force_trivial_guard env _0_608))
end
| uu____3713 -> begin
()
end));
(

let ses = (FStar_List.fold_left (fun l uu____3720 -> (match (uu____3720) with
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

let unoptimized_haseq_scheme = (fun uu____3733 -> (

let mutuals = (FStar_List.map (fun ty -> (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____3739, uu____3740, uu____3741, uu____3742, uu____3743, uu____3744, uu____3745) -> begin
lid
end
| uu____3752 -> begin
(failwith "Impossible!")
end)) tcs)
in (

let haseq_ty = (fun usubst us acc ty -> (

let uu____3772 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____3784, bs, t, uu____3787, d_lids, uu____3789, uu____3790) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____3798 -> begin
(failwith "Impossible!")
end)
in (match (uu____3772) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _0_609 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _0_609 t))
in (

let uu____3819 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____3819) with
| (bs, t) -> begin
(

let ibs = (

let uu____3830 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____3830) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____3835) -> begin
ibs
end
| uu____3846 -> begin
[]
end))
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _0_611 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _0_610 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _0_611 _0_610)))
in (

let ind = ((let _0_613 = (FStar_List.map (fun uu____3863 -> (match (uu____3863) with
| (bv, aq) -> begin
(let _0_612 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_0_612), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _0_613)) None dr)
in (

let ind = ((let _0_615 = (FStar_List.map (fun uu____3881 -> (match (uu____3881) with
| (bv, aq) -> begin
(let _0_614 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_0_614), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _0_615)) None dr)
in (

let haseq_ind = ((let _0_617 = (let _0_616 = (FStar_Syntax_Syntax.as_arg ind)
in (_0_616)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _0_617)) None dr)
in (

let rec is_mutual = (fun t -> (

let uu____3905 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____3905) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.existsb (fun lid -> (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) mutuals)
end
| FStar_Syntax_Syntax.Tm_uinst (t', uu____3913) -> begin
(is_mutual t')
end
| FStar_Syntax_Syntax.Tm_refine (bv, t') -> begin
(is_mutual bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_app (t', args) -> begin
(

let uu____3940 = (is_mutual t')
in (match (uu____3940) with
| true -> begin
true
end
| uu____3941 -> begin
(exists_mutual (FStar_List.map Prims.fst args))
end))
end
| FStar_Syntax_Syntax.Tm_meta (t', uu____3951) -> begin
(is_mutual t')
end
| uu____3956 -> begin
false
end)))
and exists_mutual = (fun uu___89_3957 -> (match (uu___89_3957) with
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

let uu____3983 = (FStar_Syntax_Subst.compress dt).FStar_Syntax_Syntax.n
in (match (uu____3983) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____3987) -> begin
(

let dbs = (Prims.snd (FStar_List.splitAt (FStar_List.length bs) dbs))
in (

let dbs = (let _0_618 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _0_618 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let sort = (Prims.fst b).FStar_Syntax_Syntax.sort
in (

let haseq_sort = ((let _0_620 = (let _0_619 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_0_619)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _0_620)) None dr)
in (

let haseq_sort = (

let uu____4030 = (is_mutual sort)
in (match (uu____4030) with
| true -> begin
(FStar_Syntax_Util.mk_imp haseq_ind haseq_sort)
end
| uu____4031 -> begin
haseq_sort
end))
in (FStar_Syntax_Util.mk_conj t haseq_sort))))) FStar_Syntax_Util.t_true dbs)
in (

let cond = (FStar_List.fold_right (fun b t -> ((let _0_623 = (let _0_622 = (FStar_Syntax_Syntax.as_arg (let _0_621 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _0_621 None)))
in (_0_622)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _0_623)) None dr)) dbs cond)
in (FStar_Syntax_Util.mk_conj acc cond))))))
end
| uu____4053 -> begin
acc
end)))))
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (uu____4057, uu____4058, uu____4059, t_lid, uu____4061, uu____4062, uu____4063, uu____4064) -> begin
(t_lid = lid)
end
| uu____4069 -> begin
(failwith "Impossible")
end)) datas)
in (

let data_cond = (FStar_List.fold_left haseq_data FStar_Syntax_Util.t_true t_datas)
in (

let fml = (FStar_Syntax_Util.mk_imp data_cond haseq_ind)
in (

let fml = (

let uu___109_4075 = fml
in (let _0_627 = FStar_Syntax_Syntax.Tm_meta ((let _0_626 = FStar_Syntax_Syntax.Meta_pattern ((let _0_625 = (let _0_624 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_0_624)::[])
in (_0_625)::[]))
in ((fml), (_0_626))))
in {FStar_Syntax_Syntax.n = _0_627; FStar_Syntax_Syntax.tk = uu___109_4075.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___109_4075.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___109_4075.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> ((let _0_630 = (let _0_629 = (FStar_Syntax_Syntax.as_arg (let _0_628 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _0_628 None)))
in (_0_629)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _0_630)) None dr)) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> ((let _0_633 = (let _0_632 = (FStar_Syntax_Syntax.as_arg (let _0_631 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _0_631 None)))
in (_0_632)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _0_633)) None dr)) bs fml)
in (FStar_Syntax_Util.mk_conj acc fml)))))))))))))))
end))))
end)))
in (

let uu____4124 = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, uu____4132, uu____4133, uu____4134, uu____4135, uu____4136, uu____4137) -> begin
((lid), (us))
end
| uu____4144 -> begin
(failwith "Impossible!")
end))
in (match (uu____4124) with
| (lid, us) -> begin
(

let uu____4150 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____4150) with
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

let se = (let _0_634 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (tc_assume env _0_634 fml [] dr))
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq");
(se)::[];
)));
)))
end))
end)))))
in (

let skip_prims_type = (fun uu____4172 -> (

let lid = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____4176, uu____4177, uu____4178, uu____4179, uu____4180, uu____4181, uu____4182) -> begin
lid
end
| uu____4189 -> begin
(failwith "Impossible")
end))
in (

let types_to_skip = ("c_False")::("c_True")::("equals")::("h_equals")::("c_and")::("c_or")::[]
in (FStar_List.existsb (fun s -> (s = lid.FStar_Ident.ident.FStar_Ident.idText)) types_to_skip))))
in (

let is_noeq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Noeq)) quals)
in (

let uu____4195 = ((((FStar_List.length tcs) = (Prims.parse_int "0")) || ((FStar_Ident.lid_equals env.FStar_TypeChecker_Env.curmodule FStar_Syntax_Const.prims_lid) && (skip_prims_type ()))) || is_noeq)
in (match (uu____4195) with
| true -> begin
(((sig_bndle)::[]), (data_ops_ses))
end
| uu____4204 -> begin
(

let is_unopteq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Unopteq)) quals)
in (

let ses = (match (is_unopteq) with
| true -> begin
(unoptimized_haseq_scheme ())
end
| uu____4210 -> begin
(optimized_haseq_scheme ())
end)
in (let _0_637 = (let _0_636 = FStar_Syntax_Syntax.Sig_bundle ((let _0_635 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_0_635))))
in (_0_636)::ses)
in ((_0_637), (data_ops_ses)))))
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
in (let _0_638 = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (_0_638), ([])))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let uu____4263 = (tc_inductive env ses quals lids)
in (match (uu____4263) with
| (ses, projectors_ses) -> begin
(

let env = (FStar_List.fold_left (fun env' se -> (FStar_TypeChecker_Env.push_sigelt env' se)) env ses)
in ((ses), (env), (projectors_ses)))
end)))
end
| FStar_Syntax_Syntax.Sig_pragma (p, r) -> begin
(

let set_options = (fun t s -> (

let uu____4293 = (FStar_Options.set_options t s)
in (match (uu____4293) with
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
| FStar_Syntax_Syntax.SetOptions (o) -> begin
((set_options FStar_Options.Set o);
(((se)::[]), (env), ([]));
)
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
((let _0_639 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _0_639 Prims.ignore));
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
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____4312) -> begin
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

let uu____4325 = (FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun uu____4336 a -> (match (uu____4336) with
| (env, ses) -> begin
(

let se_let = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a)
in (let _0_640 = (FStar_TypeChecker_Env.push_sigelt env se_let)
in ((_0_640), ((se_let)::ses))))
end)) ((env), ((se)::[]))))
in (match (uu____4325) with
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

let uu____4366 = (let _0_641 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _0_641))
in (match (uu____4366) with
| (a, wp_a_src) -> begin
(

let uu____4382 = (let _0_642 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _0_642))
in (match (uu____4382) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (let _0_645 = (let _0_644 = FStar_Syntax_Syntax.NT ((let _0_643 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (_0_643))))
in (_0_644)::[])
in (FStar_Syntax_Subst.subst _0_645 wp_b_tgt))
in (

let expected_k = (let _0_650 = (let _0_648 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_647 = (let _0_646 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_0_646)::[])
in (_0_648)::_0_647))
in (let _0_649 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _0_650 _0_649)))
in (

let repr_type = (fun eff_name a wp -> (

let no_reify = (fun l -> (Prims.raise (FStar_Errors.Error ((let _0_652 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _0_651 = (FStar_TypeChecker_Env.get_range env)
in ((_0_652), (_0_651))))))))
in (

let uu____4422 = (FStar_TypeChecker_Env.effect_decl_opt env eff_name)
in (match (uu____4422) with
| None -> begin
(no_reify eff_name)
end
| Some (ed) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((FStar_Syntax_Syntax.U_unknown)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let uu____4429 = (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))))
in (match (uu____4429) with
| true -> begin
(no_reify eff_name)
end
| uu____4433 -> begin
(let _0_657 = (FStar_TypeChecker_Env.get_range env)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_656 = (let _0_655 = (FStar_Syntax_Syntax.as_arg a)
in (let _0_654 = (let _0_653 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_653)::[])
in (_0_655)::_0_654))
in ((repr), (_0_656)))))) None _0_657))
end)))
end))))
in (

let uu____4443 = (match (((sub.FStar_Syntax_Syntax.lift), (sub.FStar_Syntax_Syntax.lift_wp))) with
| (None, None) -> begin
(failwith "Impossible")
end
| (lift, Some (uu____4458, lift_wp)) -> begin
(let _0_658 = (check_and_gen env lift_wp expected_k)
in ((lift), (_0_658)))
end
| (Some (what, lift), None) -> begin
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange))
in (

let uu____4485 = (FStar_TypeChecker_DMFF.star_expr dmff_env lift)
in (match (uu____4485) with
| (uu____4492, lift_wp, lift_elab) -> begin
(

let uu____4495 = (recheck_debug "lift-wp" env lift_wp)
in (

let uu____4496 = (recheck_debug "lift-elab" env lift_elab)
in ((Some ((([]), (lift_elab)))), ((([]), (lift_wp))))))
end)))
end)
in (match (uu____4443) with
| (lift, lift_wp) -> begin
(

let lax = env.FStar_TypeChecker_Env.lax
in (

let env = (

let uu___110_4520 = env
in {FStar_TypeChecker_Env.solver = uu___110_4520.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___110_4520.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___110_4520.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___110_4520.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___110_4520.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___110_4520.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___110_4520.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___110_4520.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___110_4520.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___110_4520.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___110_4520.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___110_4520.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___110_4520.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___110_4520.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___110_4520.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___110_4520.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___110_4520.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___110_4520.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___110_4520.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___110_4520.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___110_4520.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___110_4520.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___110_4520.FStar_TypeChecker_Env.qname_and_index})
in (

let lift = (match (lift) with
| None -> begin
None
end
| Some (uu____4524, lift) -> begin
(

let uu____4531 = (let _0_659 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _0_659))
in (match (uu____4531) with
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

let lift_wp_a = (let _0_664 = (FStar_TypeChecker_Env.get_range env)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_663 = (let _0_662 = (FStar_Syntax_Syntax.as_arg a_typ)
in (let _0_661 = (let _0_660 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (_0_660)::[])
in (_0_662)::_0_661))
in ((lift_wp), (_0_663)))))) None _0_664))
in (repr_type sub.FStar_Syntax_Syntax.target a_typ lift_wp_a)))
in (

let expected_k = (let _0_671 = (let _0_669 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_668 = (let _0_667 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (let _0_666 = (let _0_665 = (FStar_Syntax_Syntax.null_binder repr_f)
in (_0_665)::[])
in (_0_667)::_0_666))
in (_0_669)::_0_668))
in (let _0_670 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow _0_671 _0_670)))
in (

let uu____4569 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (uu____4569) with
| (expected_k, uu____4575, uu____4576) -> begin
(

let lift = (check_and_gen env lift expected_k)
in Some (lift))
end))))))))
end))
end)
in (

let env = (

let uu___111_4579 = env
in {FStar_TypeChecker_Env.solver = uu___111_4579.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___111_4579.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___111_4579.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___111_4579.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___111_4579.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___111_4579.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___111_4579.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___111_4579.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___111_4579.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___111_4579.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___111_4579.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___111_4579.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___111_4579.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___111_4579.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___111_4579.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___111_4579.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___111_4579.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___111_4579.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = lax; FStar_TypeChecker_Env.lax_universes = uu___111_4579.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___111_4579.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___111_4579.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___111_4579.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___111_4579.FStar_TypeChecker_Env.qname_and_index})
in (

let sub = (

let uu___112_4581 = sub
in {FStar_Syntax_Syntax.source = uu___112_4581.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = uu___112_4581.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = Some (lift_wp); FStar_Syntax_Syntax.lift = lift})
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

let uu____4600 = (FStar_Syntax_Subst.open_comp tps c)
in (match (uu____4600) with
| (tps, c) -> begin
(

let uu____4610 = (tc_tparams env tps)
in (match (uu____4610) with
| (tps, env, us) -> begin
(

let uu____4622 = (FStar_TypeChecker_TcTerm.tc_comp env c)
in (match (uu____4622) with
| (c, u, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
(

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

let uu____4637 = (let _0_672 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _0_672))
in (match (uu____4637) with
| (uvs, t) -> begin
(

let uu____4655 = (

let uu____4663 = (let _0_673 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in ((tps), (_0_673)))
in (match (uu____4663) with
| ([], FStar_Syntax_Syntax.Tm_arrow (uu____4673, c)) -> begin
(([]), (c))
end
| (uu____4697, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
((tps), (c))
end
| uu____4715 -> begin
(failwith "Impossible")
end))
in (match (uu____4655) with
| (tps, c) -> begin
((match ((((FStar_List.length uvs) <> (Prims.parse_int "1")) && (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))))) with
| true -> begin
(

let uu____4745 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____4745) with
| (uu____4748, t) -> begin
(Prims.raise (FStar_Errors.Error ((let _0_677 = (let _0_676 = (FStar_Syntax_Print.lid_to_string lid)
in (let _0_675 = (FStar_All.pipe_right (FStar_List.length uvs) FStar_Util.string_of_int)
in (let _0_674 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)" _0_676 _0_675 _0_674))))
in ((_0_677), (r))))))
end))
end
| uu____4752 -> begin
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
| (FStar_Syntax_Syntax.Sig_declare_typ (_, _, _, quals, _)) | (FStar_Syntax_Syntax.Sig_let (_, _, _, quals, _)) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___90_4781 -> (match (uu___90_4781) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____4782 -> begin
false
end)))) -> begin
(([]), (env), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t, quals, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let uu____4793 = (match ((uvs = [])) with
| true -> begin
(let _0_678 = (Prims.fst (FStar_Syntax_Util.type_u ()))
in (check_and_gen env t _0_678))
end
| uu____4794 -> begin
(

let uu____4795 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____4795) with
| (uvs, t) -> begin
(let _0_681 = (let _0_680 = (let _0_679 = (Prims.fst (FStar_Syntax_Util.type_u ()))
in (tc_check_trivial_guard env t _0_679))
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) _0_680))
in ((uvs), (_0_681)))
end))
end)
in (match (uu____4793) with
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

let uu____4829 = (FStar_TypeChecker_TcTerm.tc_term env e)
in (match (uu____4829) with
| (e, c, g1) -> begin
(

let uu____4841 = (let _0_684 = Some ((FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r))
in (let _0_683 = (let _0_682 = (c.FStar_Syntax_Syntax.comp ())
in ((e), (_0_682)))
in (FStar_TypeChecker_TcTerm.check_expected_effect env _0_684 _0_683)))
in (match (uu____4841) with
| (e, uu____4853, g) -> begin
((let _0_685 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _0_685));
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

let uu____4897 = (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q'))
in (match (uu____4897) with
| true -> begin
Some (q)
end
| uu____4905 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_689 = (let _0_688 = (FStar_Syntax_Print.lid_to_string l)
in (let _0_687 = (FStar_Syntax_Print.quals_to_string q)
in (let _0_686 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _0_688 _0_687 _0_686))))
in ((_0_689), (r))))))
end))
end))
in (

let uu____4908 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun uu____4929 lb -> (match (uu____4929) with
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____4953 = (

let uu____4959 = (FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____4959) with
| None -> begin
(match ((lb.FStar_Syntax_Syntax.lbunivs <> [])) with
| true -> begin
((false), (lb), (quals_opt))
end
| uu____4984 -> begin
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
| uu____5011 -> begin
(FStar_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end);
(match (((lb.FStar_Syntax_Syntax.lbunivs <> []) && ((FStar_List.length lb.FStar_Syntax_Syntax.lbunivs) <> (FStar_List.length uvs)))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Inline universes are incoherent with annotation from val declaration"), (r)))))
end
| uu____5018 -> begin
()
end);
(let _0_690 = (FStar_Syntax_Syntax.mk_lb ((FStar_Util.Inr (lbname)), (uvs), (FStar_Syntax_Const.effect_ALL_lid), (tval), (lb.FStar_Syntax_Syntax.lbdef)))
in ((false), (_0_690), (quals_opt)));
))
end))
in (match (uu____4953) with
| (gen, lb, quals_opt) -> begin
((gen), ((lb)::lbs), (quals_opt))
end)))
end)) ((true), ([]), ((match ((quals = [])) with
| true -> begin
None
end
| uu____5049 -> begin
Some (quals)
end)))))
in (match (uu____4908) with
| (should_generalize, lbs', quals_opt) -> begin
(

let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Visible_default)::[]
end
| Some (q) -> begin
(

let uu____5072 = (FStar_All.pipe_right q (FStar_Util.for_some (fun uu___91_5074 -> (match (uu___91_5074) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Visible_default) | (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> begin
true
end
| uu____5075 -> begin
false
end))))
in (match (uu____5072) with
| true -> begin
q
end
| uu____5077 -> begin
(FStar_Syntax_Syntax.Visible_default)::q
end))
end)
in (

let lbs' = (FStar_List.rev lbs')
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let ((let _0_691 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((((Prims.fst lbs)), (lbs'))), (_0_691)))))) None r)
in (

let uu____5106 = (

let uu____5112 = (FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term (

let uu___113_5116 = env
in {FStar_TypeChecker_Env.solver = uu___113_5116.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___113_5116.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___113_5116.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___113_5116.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___113_5116.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___113_5116.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___113_5116.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___113_5116.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___113_5116.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___113_5116.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___113_5116.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = uu___113_5116.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = uu___113_5116.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___113_5116.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___113_5116.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___113_5116.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___113_5116.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___113_5116.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___113_5116.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___113_5116.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___113_5116.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___113_5116.FStar_TypeChecker_Env.qname_and_index}) e)
in (match (uu____5112) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = uu____5124; FStar_Syntax_Syntax.pos = uu____5125; FStar_Syntax_Syntax.vars = uu____5126}, uu____5127, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (uu____5146, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| uu____5151 -> begin
quals
end)
in ((FStar_Syntax_Syntax.Sig_let (((lbs), (r), (lids), (quals), (attrs)))), (lbs)))
end
| uu____5161 -> begin
(failwith "impossible")
end))
in (match (uu____5106) with
| (se, lbs) -> begin
((

let uu____5184 = (log env)
in (match (uu____5184) with
| true -> begin
(let _0_696 = (let _0_695 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (

let uu____5191 = (let _0_692 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname).FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (FStar_TypeChecker_Env.try_lookup_val_decl env _0_692))
in (match (uu____5191) with
| None -> begin
true
end
| uu____5203 -> begin
false
end))
in (match (should_log) with
| true -> begin
(let _0_694 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _0_693 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _0_694 _0_693)))
end
| uu____5208 -> begin
""
end)))))
in (FStar_All.pipe_right _0_695 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _0_696))
end
| uu____5209 -> begin
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

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___92_5236 -> (match (uu___92_5236) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| uu____5237 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| uu____5245 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (uu____5250) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, uu____5263, r) -> begin
(

let uu____5271 = (is_abstract quals)
in (match (uu____5271) with
| true -> begin
(FStar_List.fold_right (fun se uu____5281 -> (match (uu____5281) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, uu____5304, uu____5305, quals, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ ((let _0_698 = (let _0_697 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow bs _0_697))
in ((l), (us), (_0_698), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals), (r))))
in (((dec)::out), (hidden)))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, uu____5323, uu____5324, uu____5325, uu____5326, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]), (r)))
in (((dec)::out), ((l)::hidden)))
end
| uu____5336 -> begin
((out), (hidden))
end)
end)) ses (([]), (hidden)))
end
| uu____5341 -> begin
(((se)::[]), (hidden))
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____5344, uu____5345, quals, uu____5347) -> begin
(

let uu____5350 = (is_abstract quals)
in (match (uu____5350) with
| true -> begin
(([]), (hidden))
end
| uu____5357 -> begin
(((se)::[]), (hidden))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, us, t, quals, r) -> begin
(

let uu____5367 = (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc))
in (match (uu____5367) with
| true -> begin
(((FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]), (r))))::[]), ((l)::hidden))
end
| uu____5376 -> begin
(

let uu____5377 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___93_5379 -> (match (uu___93_5379) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| uu____5382 -> begin
false
end))))
in (match (uu____5377) with
| true -> begin
(((se)::[]), (hidden))
end
| uu____5389 -> begin
(([]), (hidden))
end))
end))
end
| FStar_Syntax_Syntax.Sig_main (uu____5392) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____5404, uu____5405, quals, uu____5407) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____5425 = (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
in (match (uu____5425) with
| true -> begin
(([]), (hidden))
end
| uu____5433 -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::[]), ((FStar_Ident.range_of_lid lid))))
in (((dec)::[]), ((lid)::hidden)))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals, uu____5449) -> begin
(

let uu____5456 = (is_abstract quals)
in (match (uu____5456) with
| true -> begin
(let _0_700 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> FStar_Syntax_Syntax.Sig_declare_typ ((let _0_699 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname).FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in ((_0_699), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))))))
in ((_0_700), (hidden)))
end
| uu____5475 -> begin
(((se)::[]), (hidden))
end))
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let rec process_one_decl = (fun uu____5512 se -> (match (uu____5512) with
| (ses, exports, env, hidden) -> begin
((

let uu____5543 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____5543) with
| true -> begin
(let _0_701 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _0_701))
end
| uu____5544 -> begin
()
end));
(

let uu____5545 = (tc_decl env se)
in (match (uu____5545) with
| (ses', env, ses_elaborated) -> begin
((

let uu____5567 = ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes"))))
in (match (uu____5567) with
| true -> begin
(let _0_704 = (FStar_List.fold_left (fun s se -> (let _0_703 = (let _0_702 = (FStar_Syntax_Print.sigelt_to_string se)
in (Prims.strcat _0_702 "\n"))
in (Prims.strcat s _0_703))) "" ses')
in (FStar_Util.print1 "Checked: %s\n" _0_704))
end
| uu____5570 -> begin
()
end));
(FStar_List.iter (fun se -> (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)) ses');
(

let uu____5573 = (FStar_List.fold_left (fun uu____5582 se -> (match (uu____5582) with
| (le, lh) -> begin
(

let tup = (for_export hidden se)
in (((FStar_List.rev_append (Prims.fst tup) le)), ((FStar_List.rev_append (Prims.snd tup) lh))))
end)) (([]), ([])) ses')
in (match (uu____5573) with
| (exported, hidden) -> begin
(FStar_List.fold_left process_one_decl (((FStar_List.rev_append ses' ses)), (((FStar_List.rev_append exported []))::exports), (env), (hidden)) ses_elaborated)
end));
)
end));
)
end))
in (

let uu____5638 = (FStar_List.fold_left (fun acc se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, r) -> begin
(

let uu____5675 = acc
in (match (uu____5675) with
| (uu____5692, uu____5693, env, uu____5695) -> begin
(

let uu____5704 = (cps_and_elaborate env ne)
in (match (uu____5704) with
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
| uu____5737 -> begin
(process_one_decl acc se)
end)) (([]), ([]), (env), ([])) ses)
in (match (uu____5638) with
| (ses, exports, env, uu____5751) -> begin
(let _0_705 = (FStar_All.pipe_right (FStar_List.rev_append exports []) FStar_List.flatten)
in (((FStar_List.rev_append ses [])), (_0_705), (env)))
end))))


let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (

let verify = (FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let action = (match (verify) with
| true -> begin
"Verifying"
end
| uu____5779 -> begin
"Lax-checking"
end)
in (

let label = (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____5781 -> begin
"implementation"
end)
in ((

let uu____5783 = (FStar_Options.debug_any ())
in (match (uu____5783) with
| true -> begin
(FStar_Util.print3 "%s %s of %s\n" action label modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
end
| uu____5784 -> begin
()
end));
(

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____5786 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let msg = (Prims.strcat "Internals for " name)
in (

let env = (

let uu___114_5789 = env
in {FStar_TypeChecker_Env.solver = uu___114_5789.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___114_5789.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___114_5789.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___114_5789.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___114_5789.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___114_5789.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___114_5789.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___114_5789.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___114_5789.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___114_5789.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___114_5789.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___114_5789.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___114_5789.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___114_5789.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___114_5789.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___114_5789.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = (not (verify)); FStar_TypeChecker_Env.lax = uu___114_5789.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___114_5789.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___114_5789.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___114_5789.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___114_5789.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___114_5789.FStar_TypeChecker_Env.qname_and_index})
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg);
(

let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

let uu____5792 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (uu____5792) with
| (ses, exports, env) -> begin
(((

let uu___115_5810 = modul
in {FStar_Syntax_Syntax.name = uu___115_5810.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = uu___115_5810.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___115_5810.FStar_Syntax_Syntax.is_interface})), (exports), (env))
end)));
))));
)))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let uu____5826 = (tc_decls env decls)
in (match (uu____5826) with
| (ses, exports, env) -> begin
(

let modul = (

let uu___116_5844 = modul
in {FStar_Syntax_Syntax.name = uu___116_5844.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = uu___116_5844.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___116_5844.FStar_Syntax_Syntax.is_interface})
in ((modul), (exports), (env)))
end)))


let check_exports : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env modul exports -> (

let env = (

let uu___117_5858 = env
in {FStar_TypeChecker_Env.solver = uu___117_5858.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___117_5858.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___117_5858.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___117_5858.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___117_5858.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___117_5858.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___117_5858.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___117_5858.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___117_5858.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___117_5858.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___117_5858.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___117_5858.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___117_5858.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = uu___117_5858.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___117_5858.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___117_5858.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___117_5858.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = true; FStar_TypeChecker_Env.type_of = uu___117_5858.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___117_5858.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___117_5858.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___117_5858.FStar_TypeChecker_Env.qname_and_index})
in (

let check_term = (fun lid univs t -> (

let uu____5869 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (uu____5869) with
| (univs, t) -> begin
((

let uu____5875 = (let _0_706 = (FStar_TypeChecker_Env.debug (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name))
in (FStar_All.pipe_left _0_706 (FStar_Options.Other ("Exports"))))
in (match (uu____5875) with
| true -> begin
(let _0_710 = (FStar_Syntax_Print.lid_to_string lid)
in (let _0_709 = (let _0_707 = (FStar_All.pipe_right univs (FStar_List.map (fun x -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (x))))))
in (FStar_All.pipe_right _0_707 (FStar_String.concat ", ")))
in (let _0_708 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print3 "Checking for export %s <%s> : %s\n" _0_710 _0_709 _0_708))))
end
| uu____5879 -> begin
()
end));
(

let env = (FStar_TypeChecker_Env.push_univ_vars env univs)
in (let _0_711 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env t)
in (FStar_All.pipe_right _0_711 Prims.ignore)));
)
end)))
in (

let check_term = (fun lid univs t -> ((FStar_Errors.message_prefix.FStar_Errors.set_prefix (let _0_713 = (FStar_Syntax_Print.lid_to_string modul.FStar_Syntax_Syntax.name)
in (let _0_712 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Interface of %s violates its abstraction (add a \'private\' qualifier to \'%s\'?)" _0_713 _0_712))));
(check_term lid univs t);
(FStar_Errors.message_prefix.FStar_Errors.clear_prefix ());
))
in (

let rec check_sigelt = (fun uu___94_5900 -> (match (uu___94_5900) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, uu____5903, uu____5904) -> begin
(

let uu____5911 = (not ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private))))
in (match (uu____5911) with
| true -> begin
(FStar_All.pipe_right ses (FStar_List.iter check_sigelt))
end
| uu____5914 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (l, univs, binders, typ, uu____5919, uu____5920, uu____5921, r) -> begin
(

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((let _0_714 = (FStar_Syntax_Syntax.mk_Total typ)
in ((binders), (_0_714)))))) None r)
in (check_term l univs t))
end
| FStar_Syntax_Syntax.Sig_datacon (l, univs, t, uu____5943, uu____5944, uu____5945, uu____5946, uu____5947) -> begin
(check_term l univs t)
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, univs, t, quals, uu____5956) -> begin
(

let uu____5959 = (not ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private))))
in (match (uu____5959) with
| true -> begin
(check_term l univs t)
end
| uu____5961 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_let ((uu____5962, lbs), uu____5964, uu____5965, quals, uu____5967) -> begin
(

let uu____5979 = (not ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private))))
in (match (uu____5979) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (check_term fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp)))))
end
| uu____5988 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, binders, comp, quals, flags, r) -> begin
(

let uu____6000 = (not ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private))))
in (match (uu____6000) with
| true -> begin
(

let arrow = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp))))) None r)
in (check_term l univs arrow))
end
| uu____6013 -> begin
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
| uu____6020 -> begin
(FStar_List.iter check_sigelt exports)
end))))))


let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (

let modul = (

let uu___118_6033 = modul
in {FStar_Syntax_Syntax.name = uu___118_6033.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu___118_6033.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module env modul)
in ((

let uu____6036 = (not ((FStar_Options.lax ())))
in (match (uu____6036) with
| true -> begin
(check_exports env modul exports)
end
| uu____6037 -> begin
()
end));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul);
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
(

let uu____6042 = (not ((FStar_Options.interactive ())))
in (match (uu____6042) with
| true -> begin
(let _0_715 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _0_715 Prims.ignore))
end
| uu____6043 -> begin
()
end));
((modul), (env));
))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let uu____6052 = (tc_partial_modul env modul)
in (match (uu____6052) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> ((

let uu____6073 = (FStar_Options.debug_any ())
in (match (uu____6073) with
| true -> begin
(let _0_716 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (match (m.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"i\'face"
end
| uu____6074 -> begin
"module"
end) _0_716))
end
| uu____6075 -> begin
()
end));
(

let env = (

let uu___119_6077 = env
in (let _0_717 = (not ((FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = uu___119_6077.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___119_6077.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___119_6077.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___119_6077.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___119_6077.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___119_6077.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___119_6077.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___119_6077.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___119_6077.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___119_6077.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___119_6077.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___119_6077.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___119_6077.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___119_6077.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___119_6077.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___119_6077.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___119_6077.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___119_6077.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _0_717; FStar_TypeChecker_Env.lax_universes = uu___119_6077.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___119_6077.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___119_6077.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___119_6077.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___119_6077.FStar_TypeChecker_Env.qname_and_index}))
in (

let uu____6078 = (tc_modul env m)
in (match (uu____6078) with
| (m, env) -> begin
((

let uu____6086 = (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____6086) with
| true -> begin
(let _0_718 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _0_718))
end
| uu____6087 -> begin
()
end));
(

let uu____6089 = ((FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) && (FStar_Options.debug_at_level m.FStar_Syntax_Syntax.name.FStar_Ident.str (FStar_Options.Other ("Normalize"))))
in (match (uu____6089) with
| true -> begin
(

let normalize_toplevel_lets = (fun uu___95_6093 -> (match (uu___95_6093) with
| FStar_Syntax_Syntax.Sig_let ((b, lbs), r, ids, qs, attrs) -> begin
(

let n = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]))
in (

let update = (fun lb -> (

let uu____6120 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____6120) with
| (univnames, e) -> begin
(

let uu___120_6125 = lb
in (let _0_720 = (let _0_719 = (FStar_TypeChecker_Env.push_univ_vars env univnames)
in (n _0_719 e))
in {FStar_Syntax_Syntax.lbname = uu___120_6125.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___120_6125.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___120_6125.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___120_6125.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _0_720}))
end)))
in FStar_Syntax_Syntax.Sig_let ((let _0_722 = (let _0_721 = (FStar_List.map update lbs)
in ((b), (_0_721)))
in ((_0_722), (r), (ids), (qs), (attrs))))))
end
| se -> begin
se
end))
in (

let normalized_module = (

let uu___121_6135 = m
in (let _0_723 = (FStar_List.map normalize_toplevel_lets m.FStar_Syntax_Syntax.declarations)
in {FStar_Syntax_Syntax.name = uu___121_6135.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _0_723; FStar_Syntax_Syntax.exports = uu___121_6135.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___121_6135.FStar_Syntax_Syntax.is_interface}))
in (let _0_724 = (FStar_Syntax_Print.modul_to_string normalized_module)
in (FStar_Util.print1 "%s\n" _0_724))))
end
| uu____6136 -> begin
()
end));
((m), (env));
)
end)));
))




