
open Prims

let set_hint_correlator : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env = (fun env se -> (

let uu____7 = (FStar_Options.reuse_hint_for ())
in (match (uu____7) with
| Some (l) -> begin
(

let lid = (let _0_237 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_add_suffix _0_237 l))
in (

let uu___95_11 = env
in {FStar_TypeChecker_Env.solver = uu___95_11.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___95_11.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___95_11.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___95_11.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___95_11.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___95_11.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___95_11.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___95_11.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___95_11.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___95_11.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___95_11.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___95_11.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___95_11.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___95_11.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___95_11.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___95_11.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___95_11.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___95_11.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___95_11.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___95_11.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___95_11.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___95_11.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___95_11.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), ((Prims.parse_int "0"))))}))
end
| None -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (

let lid = (match (lids) with
| [] -> begin
(let _0_240 = (FStar_TypeChecker_Env.current_module env)
in (let _0_239 = (let _0_238 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_right _0_238 FStar_Util.string_of_int))
in (FStar_Ident.lid_add_suffix _0_240 _0_239)))
end
| (l)::uu____18 -> begin
l
end)
in (

let uu___96_20 = env
in {FStar_TypeChecker_Env.solver = uu___96_20.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___96_20.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___96_20.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___96_20.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___96_20.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___96_20.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___96_20.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___96_20.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___96_20.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___96_20.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___96_20.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___96_20.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___96_20.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___96_20.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___96_20.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___96_20.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___96_20.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___96_20.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___96_20.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___96_20.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___96_20.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___96_20.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___96_20.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), ((Prims.parse_int "0"))))})))
end)))


let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_Options.log_types ()) && (not ((let _0_241 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _0_241))))))


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
(let _0_242 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Term has been %s-transformed to:\n%s\n----------\n" s _0_242))
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
(let _0_243 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print1 "Re-checked; got:\n%s\n----------\n" _0_243))
end
| uu____68 -> begin
()
end));
t;
)
end));
))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _0_244 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _0_244)))


let check_nogen = (fun env t k -> (

let t = (tc_check_trivial_guard env t k)
in (let _0_245 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (([]), (_0_245)))))


let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let uu____112 = (FStar_TypeChecker_TcTerm.tc_binders env tps)
in (match (uu____112) with
| (tps, env, g, us) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
((tps), (env), (us));
)
end)))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun env m s -> (

let fail = (fun uu____145 -> (Prims.raise (FStar_Errors.Error ((let _0_246 = (FStar_TypeChecker_Err.unexpected_signature_for_monad env m s)
in ((_0_246), ((FStar_Ident.range_of_lid m))))))))
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

let uu___97_362 = ed
in {FStar_Syntax_Syntax.qualifiers = uu___97_362.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___97_362.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___97_362.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___97_362.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = uu___97_362.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = uu___97_362.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = uu___97_362.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = uu___97_362.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = uu___97_362.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = uu___97_362.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = uu___97_362.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = uu___97_362.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = uu___97_362.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = uu___97_362.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = uu___97_362.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = uu___97_362.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = uu___97_362.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = uu___97_362.FStar_Syntax_Syntax.actions})
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

let uu___98_384 = ed
in (let _0_262 = (op ed.FStar_Syntax_Syntax.ret_wp)
in (let _0_261 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _0_260 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _0_259 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _0_258 = (op ed.FStar_Syntax_Syntax.stronger)
in (let _0_257 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _0_256 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _0_255 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _0_254 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _0_253 = (op ed.FStar_Syntax_Syntax.trivial)
in (let _0_252 = (Prims.snd (op (([]), (ed.FStar_Syntax_Syntax.repr))))
in (let _0_251 = (op ed.FStar_Syntax_Syntax.return_repr)
in (let _0_250 = (op ed.FStar_Syntax_Syntax.bind_repr)
in (let _0_249 = (FStar_List.map (fun a -> (

let uu___99_388 = a
in (let _0_248 = (Prims.snd (op (([]), (a.FStar_Syntax_Syntax.action_defn))))
in (let _0_247 = (Prims.snd (op (([]), (a.FStar_Syntax_Syntax.action_typ))))
in {FStar_Syntax_Syntax.action_name = uu___99_388.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___99_388.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___99_388.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _0_248; FStar_Syntax_Syntax.action_typ = _0_247})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.qualifiers = uu___98_384.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___98_384.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___98_384.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___98_384.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu___98_384.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = uu___98_384.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _0_262; FStar_Syntax_Syntax.bind_wp = _0_261; FStar_Syntax_Syntax.if_then_else = _0_260; FStar_Syntax_Syntax.ite_wp = _0_259; FStar_Syntax_Syntax.stronger = _0_258; FStar_Syntax_Syntax.close_wp = _0_257; FStar_Syntax_Syntax.assert_p = _0_256; FStar_Syntax_Syntax.assume_p = _0_255; FStar_Syntax_Syntax.null_wp = _0_254; FStar_Syntax_Syntax.trivial = _0_253; FStar_Syntax_Syntax.repr = _0_252; FStar_Syntax_Syntax.return_repr = _0_251; FStar_Syntax_Syntax.bind_repr = _0_250; FStar_Syntax_Syntax.actions = _0_249}))))))))))))))))
end)
in (

let wp_with_fresh_result_type = (fun env mname signature -> (

let fail = (fun t -> (Prims.raise (FStar_Errors.Error ((let _0_263 = (FStar_TypeChecker_Err.unexpected_signature_for_monad env mname t)
in ((_0_263), ((FStar_Ident.range_of_lid mname))))))))
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

let env = (let _0_264 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _0_264))
in ((

let uu____485 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED")))
in (match (uu____485) with
| true -> begin
(let _0_269 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _0_268 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _0_267 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _0_266 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Syntax.bv_to_name a))
in (let _0_265 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.sort)
in (FStar_Util.print5 "Checking effect signature: %s %s : %s\n(a is %s:%s)\n" _0_269 _0_268 _0_267 _0_266 _0_265))))))
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

let expected_k = (let _0_274 = (let _0_272 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_271 = (let _0_270 = (FStar_Syntax_Syntax.null_binder (FStar_Syntax_Syntax.bv_to_name a))
in (_0_270)::[])
in (_0_272)::_0_271))
in (let _0_273 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _0_274 _0_273)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret_wp expected_k))
in (

let bind_wp = (

let uu____512 = (fresh_effect_signature ())
in (match (uu____512) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _0_277 = (let _0_275 = (FStar_Syntax_Syntax.null_binder (FStar_Syntax_Syntax.bv_to_name a))
in (_0_275)::[])
in (let _0_276 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _0_277 _0_276)))
in (

let expected_k = (let _0_288 = (let _0_286 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _0_285 = (let _0_284 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_283 = (let _0_282 = (FStar_Syntax_Syntax.mk_binder b)
in (let _0_281 = (let _0_280 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _0_279 = (let _0_278 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (_0_278)::[])
in (_0_280)::_0_279))
in (_0_282)::_0_281))
in (_0_284)::_0_283))
in (_0_286)::_0_285))
in (let _0_287 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _0_288 _0_287)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else = (

let p = (let _0_290 = (let _0_289 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _0_289 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _0_290))
in (

let expected_k = (let _0_299 = (let _0_297 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_296 = (let _0_295 = (FStar_Syntax_Syntax.mk_binder p)
in (let _0_294 = (let _0_293 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _0_292 = (let _0_291 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_0_291)::[])
in (_0_293)::_0_292))
in (_0_295)::_0_294))
in (_0_297)::_0_296))
in (let _0_298 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _0_299 _0_298)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (let _0_304 = (let _0_302 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_301 = (let _0_300 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_0_300)::[])
in (_0_302)::_0_301))
in (let _0_303 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _0_304 _0_303)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let uu____541 = (FStar_Syntax_Util.type_u ())
in (match (uu____541) with
| (t, uu____545) -> begin
(

let expected_k = (let _0_311 = (let _0_309 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_308 = (let _0_307 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _0_306 = (let _0_305 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_0_305)::[])
in (_0_307)::_0_306))
in (_0_309)::_0_308))
in (let _0_310 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _0_311 _0_310)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (let _0_313 = (let _0_312 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _0_312 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _0_313))
in (

let b_wp_a = (let _0_316 = (let _0_314 = (FStar_Syntax_Syntax.null_binder (FStar_Syntax_Syntax.bv_to_name b))
in (_0_314)::[])
in (let _0_315 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _0_316 _0_315)))
in (

let expected_k = (let _0_323 = (let _0_321 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_320 = (let _0_319 = (FStar_Syntax_Syntax.mk_binder b)
in (let _0_318 = (let _0_317 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_0_317)::[])
in (_0_319)::_0_318))
in (_0_321)::_0_320))
in (let _0_322 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _0_323 _0_322)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (let _0_331 = (let _0_329 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_328 = (let _0_327 = (FStar_Syntax_Syntax.null_binder (let _0_324 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _0_324 Prims.fst)))
in (let _0_326 = (let _0_325 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_0_325)::[])
in (_0_327)::_0_326))
in (_0_329)::_0_328))
in (let _0_330 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _0_331 _0_330)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (let _0_339 = (let _0_337 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_336 = (let _0_335 = (FStar_Syntax_Syntax.null_binder (let _0_332 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _0_332 Prims.fst)))
in (let _0_334 = (let _0_333 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_0_333)::[])
in (_0_335)::_0_334))
in (_0_337)::_0_336))
in (let _0_338 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _0_339 _0_338)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (let _0_342 = (let _0_340 = (FStar_Syntax_Syntax.mk_binder a)
in (_0_340)::[])
in (let _0_341 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _0_342 _0_341)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let uu____576 = (FStar_Syntax_Util.type_u ())
in (match (uu____576) with
| (t, uu____580) -> begin
(

let expected_k = (let _0_347 = (let _0_345 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_344 = (let _0_343 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_0_343)::[])
in (_0_345)::_0_344))
in (let _0_346 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _0_347 _0_346)))
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

let expected_k = (let _0_352 = (let _0_350 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_349 = (let _0_348 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_0_348)::[])
in (_0_350)::_0_349))
in (let _0_351 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _0_352 _0_351)))
in (tc_check_trivial_guard env ed.FStar_Syntax_Syntax.repr expected_k))
end))
in (

let mk_repr' = (fun t wp -> (

let repr = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env repr)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_356 = (let _0_355 = (FStar_Syntax_Syntax.as_arg t)
in (let _0_354 = (let _0_353 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_353)::[])
in (_0_355)::_0_354))
in ((repr), (_0_356)))))) None FStar_Range.dummyRange)))
in (

let mk_repr = (fun a wp -> (let _0_357 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_repr' _0_357 wp)))
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

let r = (let _0_358 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_0 FStar_Syntax_Syntax.Delta_constant None)
in (FStar_All.pipe_right _0_358 FStar_Syntax_Syntax.fv_to_tm))
in (

let uu____699 = (fresh_effect_signature ())
in (match (uu____699) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _0_361 = (let _0_359 = (FStar_Syntax_Syntax.null_binder (FStar_Syntax_Syntax.bv_to_name a))
in (_0_359)::[])
in (let _0_360 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _0_361 _0_360)))
in (

let wp_f = (FStar_Syntax_Syntax.gen_bv "wp_f" None wp_a)
in (

let wp_g = (FStar_Syntax_Syntax.gen_bv "wp_g" None a_wp_b)
in (

let x_a = (let _0_362 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _0_362))
in (

let wp_g_x = ((let _0_366 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (let _0_365 = (let _0_364 = (let _0_363 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _0_363))
in (_0_364)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _0_366 _0_365))) None FStar_Range.dummyRange)
in (

let res = (

let wp = ((let _0_378 = (let _0_367 = (FStar_TypeChecker_Env.inst_tscheme bind_wp)
in (FStar_All.pipe_right _0_367 Prims.snd))
in (let _0_377 = (let _0_376 = (let _0_375 = (let _0_374 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _0_373 = (let _0_372 = (FStar_Syntax_Syntax.bv_to_name b)
in (let _0_371 = (let _0_370 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (let _0_369 = (let _0_368 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (_0_368)::[])
in (_0_370)::_0_369))
in (_0_372)::_0_371))
in (_0_374)::_0_373))
in (r)::_0_375)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _0_376))
in (FStar_Syntax_Syntax.mk_Tm_app _0_378 _0_377))) None FStar_Range.dummyRange)
in (mk_repr b wp))
in (

let expected_k = (let _0_396 = (let _0_394 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_393 = (let _0_392 = (FStar_Syntax_Syntax.mk_binder b)
in (let _0_391 = (let _0_390 = (FStar_Syntax_Syntax.mk_binder wp_f)
in (let _0_389 = (let _0_388 = (FStar_Syntax_Syntax.null_binder (let _0_379 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (mk_repr a _0_379)))
in (let _0_387 = (let _0_386 = (FStar_Syntax_Syntax.mk_binder wp_g)
in (let _0_385 = (let _0_384 = (FStar_Syntax_Syntax.null_binder (let _0_383 = (let _0_380 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_0_380)::[])
in (let _0_382 = (let _0_381 = (mk_repr b wp_g_x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _0_381))
in (FStar_Syntax_Util.arrow _0_383 _0_382))))
in (_0_384)::[])
in (_0_386)::_0_385))
in (_0_388)::_0_387))
in (_0_390)::_0_389))
in (_0_392)::_0_391))
in (_0_394)::_0_393))
in (let _0_395 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _0_396 _0_395)))
in (

let uu____738 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (uu____738) with
| (expected_k, uu____743, uu____744) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos)
in (

let env = (

let uu___100_748 = env
in {FStar_TypeChecker_Env.solver = uu___100_748.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___100_748.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___100_748.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___100_748.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___100_748.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___100_748.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___100_748.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___100_748.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___100_748.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___100_748.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___100_748.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___100_748.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___100_748.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___100_748.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___100_748.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___100_748.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___100_748.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___100_748.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___100_748.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___100_748.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___100_748.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___100_748.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___100_748.FStar_TypeChecker_Env.qname_and_index})
in (

let br = (check_and_gen' env ed.FStar_Syntax_Syntax.bind_repr expected_k)
in br)))
end)))))))))
end)))
in (

let return_repr = (

let x_a = (let _0_397 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _0_397))
in (

let res = (

let wp = ((let _0_404 = (let _0_398 = (FStar_TypeChecker_Env.inst_tscheme return_wp)
in (FStar_All.pipe_right _0_398 Prims.snd))
in (let _0_403 = (let _0_402 = (let _0_401 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _0_400 = (let _0_399 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (_0_399)::[])
in (_0_401)::_0_400))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _0_402))
in (FStar_Syntax_Syntax.mk_Tm_app _0_404 _0_403))) None FStar_Range.dummyRange)
in (mk_repr a wp))
in (

let expected_k = (let _0_409 = (let _0_407 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_406 = (let _0_405 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_0_405)::[])
in (_0_407)::_0_406))
in (let _0_408 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _0_409 _0_408)))
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
(let _0_411 = (FStar_Syntax_Print.term_to_string act.FStar_Syntax_Syntax.action_defn)
in (let _0_410 = (FStar_Syntax_Print.term_to_string act_typ)
in (FStar_Util.print3 "Checking action %s:\n[definition]: %s\n[cps\'d type]: %s\n" (FStar_Ident.text_of_lid act.FStar_Syntax_Syntax.action_name) _0_411 _0_410)))
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

let k = (let _0_412 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs _0_412))
in (

let uu____856 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env k)
in (match (uu____856) with
| (k, uu____863, g) -> begin
((k), (g))
end))))
end))
end
| uu____865 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_415 = (let _0_414 = (FStar_Syntax_Print.term_to_string act_typ)
in (let _0_413 = (FStar_Syntax_Print.tag_of_term act_typ)
in (FStar_Util.format2 "Actions must have function types (not: %s, a.k.a. %s)" _0_414 _0_413)))
in ((_0_415), (act_defn.FStar_Syntax_Syntax.pos))))))
end))
in (match (uu____825) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env act_typ expected_k)
in ((let _0_418 = (let _0_417 = (let _0_416 = (FStar_TypeChecker_Rel.conj_guard g_t g)
in (FStar_TypeChecker_Rel.conj_guard g_k _0_416))
in (FStar_TypeChecker_Rel.conj_guard g_a _0_417))
in (FStar_TypeChecker_Rel.force_trivial_guard env _0_418));
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

let c = (let _0_422 = (let _0_419 = (env.FStar_TypeChecker_Env.universe_of env a)
in (_0_419)::[])
in (let _0_421 = (let _0_420 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_420)::[])
in {FStar_Syntax_Syntax.comp_univs = _0_422; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a; FStar_Syntax_Syntax.effect_args = _0_421; FStar_Syntax_Syntax.flags = []}))
in (let _0_423 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Util.arrow bs _0_423)))
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

let uu___101_926 = act
in {FStar_Syntax_Syntax.action_name = uu___101_926.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___101_926.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = act_defn; FStar_Syntax_Syntax.action_typ = act_typ}))
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

let t = (let _0_424 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _0_424))
in (

let uu____942 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (uu____942) with
| (univs, t) -> begin
(

let signature = (

let uu____948 = (let _0_425 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in ((effect_params), (_0_425)))
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

let ts = (let _0_426 = (FStar_Syntax_Subst.close_tscheme effect_params ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _0_426))
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
in (failwith (let _0_428 = (FStar_Util.string_of_int n)
in (let _0_427 = (FStar_Syntax_Print.tscheme_to_string ts)
in (FStar_Util.format3 "The effect combinator is %s (n=%s) (%s)" error _0_428 _0_427)))))
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

let uu___102_1010 = act
in {FStar_Syntax_Syntax.action_name = uu___102_1010.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___102_1010.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = defn; FStar_Syntax_Syntax.action_typ = typ})
end))
end)))
in (

let nunivs = (FStar_List.length univs)
in (

let ed = (

let uu___103_1015 = ed
in (let _0_442 = (close (Prims.parse_int "0") return_wp)
in (let _0_441 = (close (Prims.parse_int "1") bind_wp)
in (let _0_440 = (close (Prims.parse_int "0") if_then_else)
in (let _0_439 = (close (Prims.parse_int "0") ite_wp)
in (let _0_438 = (close (Prims.parse_int "0") stronger)
in (let _0_437 = (close (Prims.parse_int "1") close_wp)
in (let _0_436 = (close (Prims.parse_int "0") assert_p)
in (let _0_435 = (close (Prims.parse_int "0") assume_p)
in (let _0_434 = (close (Prims.parse_int "0") null_wp)
in (let _0_433 = (close (Prims.parse_int "0") trivial_wp)
in (let _0_432 = (Prims.snd (close (Prims.parse_int "0") (([]), (repr))))
in (let _0_431 = (close (Prims.parse_int "0") return_repr)
in (let _0_430 = (close (Prims.parse_int "1") bind_repr)
in (let _0_429 = (FStar_List.map close_action actions)
in {FStar_Syntax_Syntax.qualifiers = uu___103_1015.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___103_1015.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___103_1015.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _0_442; FStar_Syntax_Syntax.bind_wp = _0_441; FStar_Syntax_Syntax.if_then_else = _0_440; FStar_Syntax_Syntax.ite_wp = _0_439; FStar_Syntax_Syntax.stronger = _0_438; FStar_Syntax_Syntax.close_wp = _0_437; FStar_Syntax_Syntax.assert_p = _0_436; FStar_Syntax_Syntax.assume_p = _0_435; FStar_Syntax_Syntax.null_wp = _0_434; FStar_Syntax_Syntax.trivial = _0_433; FStar_Syntax_Syntax.repr = _0_432; FStar_Syntax_Syntax.return_repr = _0_431; FStar_Syntax_Syntax.bind_repr = _0_430; FStar_Syntax_Syntax.actions = _0_429})))))))))))))))
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
(let _0_444 = (

let uu___104_1070 = bv
in (let _0_443 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___104_1070.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___104_1070.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_443}))
in ((_0_444), (qual)))
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
(let _0_445 = Some ((FStar_Syntax_Syntax.range_of_bv a))
in (FStar_Syntax_Syntax.gen_bv "a" _0_445 a.FStar_Syntax_Syntax.sort))
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
(let _0_446 = (FStar_Syntax_Print.term_to_string repr)
in (FStar_Util.print1 "Representation is: %s\n" _0_446))
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

let wp_a = (let _0_451 = (mk (FStar_Syntax_Syntax.Tm_app ((let _0_450 = (let _0_449 = (let _0_448 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _0_447 = (FStar_Syntax_Syntax.as_implicit false)
in ((_0_448), (_0_447))))
in (_0_449)::[])
in ((wp_type), (_0_450))))))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _0_451))
in (

let effect_signature = (

let binders = (let _0_456 = (let _0_452 = (FStar_Syntax_Syntax.as_implicit false)
in ((a), (_0_452)))
in (let _0_455 = (let _0_454 = (let _0_453 = (FStar_Syntax_Syntax.gen_bv "dijkstra_wp" None wp_a)
in (FStar_All.pipe_right _0_453 FStar_Syntax_Syntax.mk_binder))
in (_0_454)::[])
in (_0_456)::_0_455))
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
(Prims.raise (FStar_Errors.Err ((let _0_458 = (FStar_Syntax_Print.term_to_string item)
in (let _0_457 = (FStar_Syntax_Print.lcomp_to_string item_comp)
in (FStar_Util.format2 "Computation for [%s] is not total : %s !" _0_458 _0_457))))))
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

let uu____1316 = (let _0_459 = (FStar_Syntax_Util.abs bs body None)
in (FStar_Syntax_Subst.open_term ((b1)::(b2)::[]) _0_459))
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

let env0 = (let _0_460 = (FStar_TypeChecker_DMFF.get_env dmff_env)
in (FStar_TypeChecker_Env.push_binders _0_460 ((b1)::(b2)::[])))
in (

let wp_b1 = (let _0_465 = (mk (FStar_Syntax_Syntax.Tm_app ((let _0_464 = (let _0_463 = (let _0_462 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b1))
in (let _0_461 = (FStar_Syntax_Syntax.as_implicit false)
in ((_0_462), (_0_461))))
in (_0_463)::[])
in ((wp_type), (_0_464))))))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env0 _0_465))
in (

let uu____1393 = (let _0_467 = (let _0_466 = (FStar_Syntax_Util.unascribe wp_b1)
in (FStar_TypeChecker_Normalize.eta_expand_with_type body _0_466))
in (FStar_All.pipe_left FStar_Syntax_Util.abs_formals _0_467))
in (match (uu____1393) with
| (bs, body, what') -> begin
(

let t2 = (Prims.fst b2).FStar_Syntax_Syntax.sort
in (

let pure_wp_type = (FStar_TypeChecker_DMFF.double_star t2)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None pure_wp_type)
in (

let body = ((let _0_471 = (FStar_Syntax_Syntax.bv_to_name wp)
in (let _0_470 = (let _0_469 = (let _0_468 = (FStar_Syntax_Util.abs ((b2)::[]) body what')
in ((_0_468), (None)))
in (_0_469)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _0_471 _0_470))) None FStar_Range.dummyRange)
in (let _0_475 = (let _0_473 = (let _0_472 = (FStar_Syntax_Syntax.mk_binder wp)
in (_0_472)::[])
in (b1)::_0_473)
in (let _0_474 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs _0_475 _0_474 (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_GTot_lid), ([]))))))))))))
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
(let _0_476 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs ((b1)::(b2)::[]) _0_476 (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_GTot_lid), ([])))))))
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
in (let _0_479 = (let _0_478 = (let _0_477 = (FStar_Syntax_Syntax.null_binder (mk (FStar_Syntax_Syntax.Tm_fvar (r))))
in (_0_477)::[])
in (FStar_List.append _0_478 binders))
in (FStar_Syntax_Util.abs _0_479 body what)))
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
(let _0_481 = (mk (FStar_Syntax_Syntax.Tm_app ((let _0_480 = (Prims.snd (FStar_Syntax_Util.args_of_binders effect_binders))
in ((t), (_0_480))))))
in (FStar_Syntax_Subst.close effect_binders _0_481))
end))
in (

let register = (fun name item -> (

let uu____1570 = (let _0_483 = (mk_lid name)
in (let _0_482 = (FStar_Syntax_Util.abs effect_binders item None)
in (FStar_TypeChecker_Util.mk_toplevel_definition env _0_483 _0_482)))
in (match (uu____1570) with
| (sigelt, fv) -> begin
((let _0_485 = (let _0_484 = (FStar_ST.read sigelts)
in (sigelt)::_0_484)
in (FStar_ST.write sigelts _0_485));
fv;
)
end)))
in (

let lift_from_pure_wp = (register "lift_from_pure" lift_from_pure_wp)
in (

let return_wp = (register "return_wp" return_wp)
in ((let _0_487 = (let _0_486 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true")), (FStar_Range.dummyRange))))::_0_486)
in (FStar_ST.write sigelts _0_487));
(

let return_elab = (register "return_elab" return_elab)
in ((let _0_489 = (let _0_488 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false")), (FStar_Range.dummyRange))))::_0_488)
in (FStar_ST.write sigelts _0_489));
(

let bind_wp = (register "bind_wp" bind_wp)
in ((let _0_491 = (let _0_490 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true")), (FStar_Range.dummyRange))))::_0_490)
in (FStar_ST.write sigelts _0_491));
(

let bind_elab = (register "bind_elab" bind_elab)
in ((let _0_493 = (let _0_492 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false")), (FStar_Range.dummyRange))))::_0_492)
in (FStar_ST.write sigelts _0_493));
(

let uu____1620 = (FStar_List.fold_left (fun uu____1627 action -> (match (uu____1627) with
| (dmff_env, actions) -> begin
(

let uu____1639 = (elaborate_and_star dmff_env ((action.FStar_Syntax_Syntax.action_univs), (action.FStar_Syntax_Syntax.action_defn)))
in (match (uu____1639) with
| (dmff_env, action_t, action_wp, action_elab) -> begin
(

let name = action.FStar_Syntax_Syntax.action_name.FStar_Ident.ident.FStar_Ident.idText
in (

let action_typ_with_wp = (FStar_TypeChecker_DMFF.trans_F dmff_env action_t action_wp)
in (

let action_elab = (register (Prims.strcat name "_elab") action_elab)
in (

let action_typ_with_wp = (register (Prims.strcat name "_complete_type") action_typ_with_wp)
in (let _0_497 = (let _0_496 = (

let uu___105_1656 = action
in (let _0_495 = (apply_close action_elab)
in (let _0_494 = (apply_close action_typ_with_wp)
in {FStar_Syntax_Syntax.action_name = uu___105_1656.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___105_1656.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = uu___105_1656.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _0_495; FStar_Syntax_Syntax.action_typ = _0_494})))
in (_0_496)::actions)
in ((dmff_env), (_0_497)))))))
end))
end)) ((dmff_env), ([])) ed.FStar_Syntax_Syntax.actions)
in (match (uu____1620) with
| (dmff_env, actions) -> begin
(

let actions = (FStar_List.rev actions)
in (

let repr = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp_a" None wp_a)
in (

let binders = (let _0_500 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_499 = (let _0_498 = (FStar_Syntax_Syntax.mk_binder wp)
in (_0_498)::[])
in (_0_500)::_0_499))
in (let _0_507 = (let _0_506 = (mk (FStar_Syntax_Syntax.Tm_app ((let _0_504 = (let _0_503 = (let _0_502 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _0_501 = (FStar_Syntax_Syntax.as_implicit false)
in ((_0_502), (_0_501))))
in (_0_503)::[])
in ((repr), (_0_504))))))
in (let _0_505 = (FStar_Syntax_Syntax.bv_to_name wp)
in (FStar_TypeChecker_DMFF.trans_F dmff_env _0_506 _0_505)))
in (FStar_Syntax_Util.abs binders _0_507 None))))
in (

let repr = (recheck_debug "FC" env repr)
in (

let repr = (register "repr" repr)
in (

let uu____1687 = (

let uu____1692 = (let _0_508 = (FStar_Syntax_Subst.compress wp_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe _0_508)).FStar_Syntax_Syntax.n
in (match (uu____1692) with
| FStar_Syntax_Syntax.Tm_abs ((type_param)::effect_param, arrow, uu____1700) -> begin
(

let uu____1727 = (

let uu____1736 = (FStar_Syntax_Subst.open_term ((type_param)::effect_param) arrow)
in (match (uu____1736) with
| ((b)::bs, body) -> begin
((b), (bs), (body))
end
| uu____1767 -> begin
(failwith "Impossible : open_term nt preserving binders arity")
end))
in (match (uu____1727) with
| (type_param, effect_param, arrow) -> begin
(

let uu____1795 = (let _0_509 = (FStar_Syntax_Subst.compress arrow)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe _0_509)).FStar_Syntax_Syntax.n
in (match (uu____1795) with
| FStar_Syntax_Syntax.Tm_arrow (wp_binders, c) -> begin
(

let uu____1812 = (FStar_Syntax_Subst.open_comp wp_binders c)
in (match (uu____1812) with
| (wp_binders, c) -> begin
(

let uu____1821 = (FStar_List.partition (fun uu____1832 -> (match (uu____1832) with
| (bv, uu____1836) -> begin
(let _0_511 = (let _0_510 = (FStar_Syntax_Free.names bv.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _0_510 (FStar_Util.set_mem (Prims.fst type_param))))
in (FStar_All.pipe_right _0_511 Prims.op_Negation))
end)) wp_binders)
in (match (uu____1821) with
| (pre_args, post_args) -> begin
(

let post = (match (post_args) with
| (post)::[] -> begin
post
end
| uu____1868 -> begin
(failwith (let _0_512 = (FStar_Syntax_Print.term_to_string arrow)
in (FStar_Util.format1 "Impossible: multiple post candidates %s" _0_512)))
end)
in (let _0_514 = (FStar_Syntax_Util.arrow pre_args c)
in (let _0_513 = (FStar_Syntax_Util.abs ((type_param)::effect_param) (Prims.fst post).FStar_Syntax_Syntax.sort None)
in ((_0_514), (_0_513)))))
end))
end))
end
| uu____1883 -> begin
(failwith (let _0_515 = (FStar_Syntax_Print.term_to_string arrow)
in (FStar_Util.format1 "Impossible: pre/post arrow %s" _0_515)))
end))
end))
end
| uu____1888 -> begin
(failwith (let _0_516 = (FStar_Syntax_Print.term_to_string wp_type)
in (FStar_Util.format1 "Impossible: pre/post abs %s" _0_516)))
end))
in (match (uu____1687) with
| (pre, post) -> begin
((Prims.ignore (register "pre" pre));
(Prims.ignore (register "post" post));
(Prims.ignore (register "wp" wp_type));
(

let ed = (

let uu___106_1908 = ed
in (let _0_527 = (FStar_Syntax_Subst.close_binders effect_binders)
in (let _0_526 = (FStar_Syntax_Subst.close effect_binders effect_signature)
in (let _0_525 = (let _0_517 = (apply_close return_wp)
in (([]), (_0_517)))
in (let _0_524 = (let _0_518 = (apply_close bind_wp)
in (([]), (_0_518)))
in (let _0_523 = (apply_close repr)
in (let _0_522 = (let _0_519 = (apply_close return_elab)
in (([]), (_0_519)))
in (let _0_521 = (let _0_520 = (apply_close bind_elab)
in (([]), (_0_520)))
in {FStar_Syntax_Syntax.qualifiers = uu___106_1908.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___106_1908.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___106_1908.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___106_1908.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _0_527; FStar_Syntax_Syntax.signature = _0_526; FStar_Syntax_Syntax.ret_wp = _0_525; FStar_Syntax_Syntax.bind_wp = _0_524; FStar_Syntax_Syntax.if_then_else = uu___106_1908.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = uu___106_1908.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = uu___106_1908.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = uu___106_1908.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = uu___106_1908.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = uu___106_1908.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = uu___106_1908.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = uu___106_1908.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _0_523; FStar_Syntax_Syntax.return_repr = _0_522; FStar_Syntax_Syntax.bind_repr = _0_521; FStar_Syntax_Syntax.actions = actions}))))))))
in (

let uu____1921 = (FStar_TypeChecker_DMFF.gen_wps_for_free env effect_binders a wp_a ed)
in (match (uu____1921) with
| (sigelts', ed) -> begin
((

let uu____1932 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____1932) with
| true -> begin
(FStar_Util.print_string (FStar_Syntax_Print.eff_decl_to_string true ed))
end
| uu____1933 -> begin
()
end));
(

let lift_from_pure_opt = (match (((FStar_List.length effect_binders) = (Prims.parse_int "0"))) with
| true -> begin
(

let lift_from_pure = (let _0_529 = Some ((let _0_528 = (apply_close lift_from_pure_wp)
in (([]), (_0_528))))
in {FStar_Syntax_Syntax.source = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.target = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.lift_wp = _0_529; FStar_Syntax_Syntax.lift = None})
in Some (FStar_Syntax_Syntax.Sig_sub_effect (((lift_from_pure), (FStar_Range.dummyRange)))))
end
| uu____1950 -> begin
None
end)
in (let _0_531 = (let _0_530 = (FStar_List.rev (FStar_ST.read sigelts))
in (FStar_List.append _0_530 sigelts'))
in ((_0_531), (ed), (lift_from_pure_opt))));
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
| (FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, uu____1972, uu____1973, [], r))::(FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, _0_532, [], uu____1978, r1))::(FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, _0_533, [], uu____1983, r2))::[] when (((_0_532 = (Prims.parse_int "0")) && (_0_533 = (Prims.parse_int "0"))) && (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid))) -> begin
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

let lex_top_t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst ((let _0_534 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1) FStar_Syntax_Syntax.Delta_constant None)
in ((_0_534), ((FStar_Syntax_Syntax.U_name (utop))::[])))))) None r1)
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

let a = (let _0_535 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _0_535))
in (

let hd = (let _0_536 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _0_536))
in (

let tl = (let _0_538 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst ((let _0_537 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2) FStar_Syntax_Syntax.Delta_constant None)
in ((_0_537), ((FStar_Syntax_Syntax.U_name (ucons2))::[])))))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _0_538))
in (

let res = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst ((let _0_539 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2) FStar_Syntax_Syntax.Delta_constant None)
in ((_0_539), ((FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[])))))) None r2)
in (let _0_540 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow ((((a), (Some (FStar_Syntax_Syntax.imp_tag))))::(((hd), (None)))::(((tl), (None)))::[]) _0_540))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon (((lex_cons), ((ucons1)::(ucons2)::[]), (lex_cons_t), (FStar_Syntax_Const.lex_t_lid), ((Prims.parse_int "0")), ([]), ([]), (r2)))
in FStar_Syntax_Syntax.Sig_bundle ((let _0_541 = (FStar_TypeChecker_Env.get_range env)
in (((tc)::(dc_lextop)::(dc_lexcons)::[]), ([]), (lids), (_0_541)))))))))))))))))
end
| uu____2105 -> begin
(failwith (let _0_542 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle (((ses), ([]), (lids), (FStar_Range.dummyRange)))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _0_542)))
end))
and tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let uu____2117 = (FStar_Syntax_Util.type_u ())
in (match (uu____2117) with
| (k, uu____2121) -> begin
(

let phi = (let _0_543 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _0_543 (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env)))
in ((FStar_TypeChecker_Util.check_uvars r phi);
FStar_Syntax_Syntax.Sig_assume (((lid), (phi), (quals), (r)));
))
end))))
and tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env ses quals lids -> (

let warn_positivity = (fun l r -> (let _0_545 = (let _0_544 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _0_544))
in (FStar_Errors.diag r _0_545)))
in (

let env0 = env
in (

let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
((warn_positivity tc r);
(

let uu____2175 = (FStar_Syntax_Subst.open_term tps k)
in (match (uu____2175) with
| (tps, k) -> begin
(

let uu____2184 = (FStar_TypeChecker_TcTerm.tc_binders env tps)
in (match (uu____2184) with
| (tps, env_tps, guard_params, us) -> begin
(

let uu____2197 = (FStar_Syntax_Util.arrow_formals k)
in (match (uu____2197) with
| (indices, t) -> begin
(

let uu____2221 = (FStar_TypeChecker_TcTerm.tc_binders env_tps indices)
in (match (uu____2221) with
| (indices, env', guard_indices, us') -> begin
(

let uu____2234 = (

let uu____2237 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' t)
in (match (uu____2237) with
| (t, uu____2244, g) -> begin
(let _0_548 = (let _0_547 = (let _0_546 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params _0_546))
in (FStar_TypeChecker_Rel.discharge_guard env' _0_547))
in ((t), (_0_548)))
end))
in (match (uu____2234) with
| (t, guard) -> begin
(

let k = (let _0_549 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _0_549))
in (

let uu____2255 = (FStar_Syntax_Util.type_u ())
in (match (uu____2255) with
| (t_type, u) -> begin
((let _0_550 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _0_550));
(

let t_tc = (let _0_551 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _0_551))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _0_552 = (FStar_TypeChecker_Env.push_let_binding env (FStar_Util.Inr (fv_tc)) (([]), (t_tc)))
in ((_0_552), (FStar_Syntax_Syntax.Sig_inductive_typ (((tc), ([]), (tps), (k), (mutuals), (data), (quals), (r)))), (u), (guard)))))));
)
end)))
end))
end))
end))
end))
end));
)
end
| uu____2280 -> begin
(failwith "impossible")
end))
in (

let positive_if_pure = (fun uu____2290 l -> ())
in (

let tc_data = (fun env tcs uu___83_2306 -> (match (uu___83_2306) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let uu____2325 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun uu____2339 -> (match (uu____2339) with
| (se, u_tc) -> begin
(

let uu____2348 = (let _0_553 = (FStar_Util.must (FStar_Syntax_Util.lid_of_sigelt se))
in (FStar_Ident.lid_equals tc_lid _0_553))
in (match (uu____2348) with
| true -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____2357, uu____2358, tps, uu____2360, uu____2361, uu____2362, uu____2363, uu____2364) -> begin
(

let tps = (FStar_All.pipe_right tps (FStar_List.map (fun uu____2385 -> (match (uu____2385) with
| (x, uu____2392) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let tps = (FStar_Syntax_Subst.open_binders tps)
in Some ((let _0_554 = (FStar_TypeChecker_Env.push_binders env tps)
in ((_0_554), (tps), (u_tc))))))
end
| uu____2398 -> begin
(failwith "Impossible")
end)
end
| uu____2403 -> begin
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
| uu____2428 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected data constructor"), (r)))))
end)
end))
in (match (uu____2325) with
| (env, tps, u_tc) -> begin
(

let uu____2437 = (

let uu____2445 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____2445) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let uu____2465 = (FStar_Util.first_N ntps bs)
in (match (uu____2465) with
| (uu____2483, bs') -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs'), (res)))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i uu____2515 -> (match (uu____2515) with
| (x, uu____2519) -> begin
FStar_Syntax_Syntax.DB ((((ntps - ((Prims.parse_int "1") + i))), (x)))
end))))
in (FStar_Syntax_Util.arrow_formals (FStar_Syntax_Subst.subst subst t))))
end))
end
| uu____2520 -> begin
(([]), (t))
end))
in (match (uu____2437) with
| (arguments, result) -> begin
((

let uu____2541 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____2541) with
| true -> begin
(let _0_557 = (FStar_Syntax_Print.lid_to_string c)
in (let _0_556 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _0_555 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _0_557 _0_556 _0_555))))
end
| uu____2542 -> begin
()
end));
(

let uu____2543 = (tc_tparams env arguments)
in (match (uu____2543) with
| (arguments, env', us) -> begin
(

let uu____2552 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env' result)
in (match (uu____2552) with
| (result, res_lcomp) -> begin
((

let uu____2560 = (FStar_Syntax_Subst.compress res_lcomp.FStar_Syntax_Syntax.res_typ).FStar_Syntax_Syntax.n
in (match (uu____2560) with
| FStar_Syntax_Syntax.Tm_type (uu____2561) -> begin
()
end
| ty -> begin
(Prims.raise (FStar_Errors.Error ((let _0_560 = (let _0_559 = (FStar_Syntax_Print.term_to_string result)
in (let _0_558 = (FStar_Syntax_Print.term_to_string res_lcomp.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "The type of %s is %s, but since this is the result type of a constructor its type should be Type" _0_559 _0_558)))
in ((_0_560), (r))))))
end));
(

let uu____2563 = (FStar_Syntax_Util.head_and_args result)
in (match (uu____2563) with
| (head, uu____2576) -> begin
((

let uu____2592 = (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
in (match (uu____2592) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| uu____2594 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_563 = (let _0_562 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (let _0_561 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" _0_562 _0_561)))
in ((_0_563), (r))))))
end));
(

let g = (FStar_List.fold_left2 (fun g uu____2599 u_x -> (match (uu____2599) with
| (x, uu____2604) -> begin
(

let _0_564 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _0_564))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _0_567 = (let _0_565 = (FStar_All.pipe_right tps (FStar_List.map (fun uu____2621 -> (match (uu____2621) with
| (x, uu____2628) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append _0_565 arguments))
in (let _0_566 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _0_567 _0_566)))
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
| uu____2635 -> begin
(failwith "impossible")
end))
in (

let generalize_and_inst_within = (fun env g tcs datas -> (

let tc_universe_vars = (FStar_List.map Prims.snd tcs)
in (

let g = (

let uu___107_2668 = g
in {FStar_TypeChecker_Env.guard_f = uu___107_2668.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = uu___107_2668.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = ((tc_universe_vars), ((Prims.snd g.FStar_TypeChecker_Env.univ_ineqs))); FStar_TypeChecker_Env.implicits = uu___107_2668.FStar_TypeChecker_Env.implicits})
in ((

let uu____2674 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____2674) with
| true -> begin
(let _0_568 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print1 "@@@@@@Guard before generalization: %s\n" _0_568))
end
| uu____2675 -> begin
()
end));
(FStar_TypeChecker_Rel.force_trivial_guard env g);
(

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun uu____2685 -> (match (uu____2685) with
| (se, uu____2689) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____2690, uu____2691, tps, k, uu____2694, uu____2695, uu____2696, uu____2697) -> begin
(FStar_Syntax_Syntax.null_binder (let _0_569 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _0_569)))
end
| uu____2708 -> begin
(failwith "Impossible")
end)
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun uu___84_2713 -> (match (uu___84_2713) with
| FStar_Syntax_Syntax.Sig_datacon (uu____2714, uu____2715, t, uu____2717, uu____2718, uu____2719, uu____2720, uu____2721) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| uu____2726 -> begin
(failwith "Impossible")
end))))
in (

let t = (let _0_570 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _0_570))
in ((

let uu____2731 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____2731) with
| true -> begin
(let _0_571 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _0_571))
end
| uu____2732 -> begin
()
end));
(

let uu____2733 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (uu____2733) with
| (uvs, t) -> begin
((

let uu____2743 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("GenUniverses")))
in (match (uu____2743) with
| true -> begin
(let _0_574 = (let _0_572 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _0_572 (FStar_String.concat ", ")))
in (let _0_573 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _0_574 _0_573)))
end
| uu____2748 -> begin
()
end));
(

let uu____2749 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____2749) with
| (uvs, t) -> begin
(

let uu____2758 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____2758) with
| (args, uu____2771) -> begin
(

let uu____2782 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (uu____2782) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun uu____2819 uu____2820 -> (match (((uu____2819), (uu____2820))) with
| ((x, uu____2830), (se, uu____2832)) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____2838, tps, uu____2840, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let uu____2852 = (

let uu____2860 = (FStar_Syntax_Subst.compress ty).FStar_Syntax_Syntax.n
in (match (uu____2860) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____2880 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (uu____2880) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| uu____2923 -> begin
(let _0_575 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) _0_575 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in ((tps), (t)))
end))
end
| uu____2944 -> begin
(([]), (ty))
end))
in (match (uu____2852) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs), (tps), (t), (mutuals), (datas), (quals), (r)))
end)))
end
| uu____2970 -> begin
(failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| uu____2974 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _0_576 -> FStar_Syntax_Syntax.U_name (_0_576))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun uu___85_2991 -> (match (uu___85_2991) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uu____2996, uu____2997, uu____2998, uu____2999, uu____3000, uu____3001, uu____3002) -> begin
((tc), (uvs_universes))
end
| uu____3010 -> begin
(failwith "Impossible")
end))))
in (FStar_List.map2 (fun uu____3016 d -> (match (uu____3016) with
| (t, uu____3021) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, uu____3023, uu____3024, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (let _0_577 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _0_577 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon (((l), (uvs), (ty), (tc), (ntps), (quals), (mutuals), (r))))
end
| uu____3037 -> begin
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

let uu____3040 = (FStar_All.pipe_right ses (FStar_List.partition (fun uu___86_3050 -> (match (uu___86_3050) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____3051) -> begin
true
end
| uu____3063 -> begin
false
end))))
in (match (uu____3040) with
| (tys, datas) -> begin
((

let uu____3075 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun uu___87_3077 -> (match (uu___87_3077) with
| FStar_Syntax_Syntax.Sig_datacon (uu____3078) -> begin
false
end
| uu____3089 -> begin
true
end))))
in (match (uu____3075) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((let _0_578 = (FStar_TypeChecker_Env.get_range env)
in (("Mutually defined type contains a non-inductive element"), (_0_578))))))
end
| uu____3090 -> begin
()
end));
(

let env0 = env
in (

let uu____3092 = (FStar_List.fold_right (fun tc uu____3106 -> (match (uu____3106) with
| (env, all_tcs, g) -> begin
(

let uu____3128 = (tc_tycon env tc)
in (match (uu____3128) with
| (env, tc, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in ((

let uu____3145 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____3145) with
| true -> begin
(let _0_579 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _0_579))
end
| uu____3146 -> begin
()
end));
(let _0_581 = (let _0_580 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g _0_580))
in ((env), ((((tc), (tc_u)))::all_tcs), (_0_581)));
))
end))
end)) tys ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (uu____3092) with
| (env, tcs, g) -> begin
(

let uu____3170 = (FStar_List.fold_right (fun se uu____3178 -> (match (uu____3178) with
| (datas, g) -> begin
(

let uu____3189 = (tc_data env tcs se)
in (match (uu____3189) with
| (data, g') -> begin
(let _0_582 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((data)::datas), (_0_582)))
end))
end)) datas (([]), (g)))
in (match (uu____3170) with
| (datas, g) -> begin
(

let uu____3207 = (generalize_and_inst_within env0 g tcs datas)
in (match (uu____3207) with
| (tcs, datas) -> begin
(

let sig_bndle = FStar_Syntax_Syntax.Sig_bundle ((let _0_583 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_0_583))))
in (

let datacon_typ = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (uu____3230, uu____3231, t, uu____3233, uu____3234, uu____3235, uu____3236, uu____3237) -> begin
t
end
| uu____3242 -> begin
(failwith "Impossible!")
end))
in (

let data_ops_ses = (let _0_584 = (FStar_List.map (FStar_TypeChecker_Util.mk_data_operations quals env tcs) datas)
in (FStar_All.pipe_right _0_584 FStar_List.flatten))
in (

let check_positivity = (fun env ty -> (

let unfolded_inductives = (FStar_Util.mk_ref [])
in (

let already_unfolded = (fun env ilid args -> (let _0_585 = (FStar_ST.read unfolded_inductives)
in (FStar_List.existsML (fun uu____3291 -> (match (uu____3291) with
| (lid, l) -> begin
((FStar_Ident.lid_equals lid ilid) && (

let args = (Prims.fst (FStar_List.splitAt (FStar_List.length l) args))
in (FStar_List.fold_left2 (fun b a a' -> (b && (FStar_TypeChecker_Rel.teq_nosmt env (Prims.fst a) (Prims.fst a')))) true args l)))
end)) _0_585)))
in (

let uu____3348 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, bs, uu____3358, uu____3359, uu____3360, uu____3361, uu____3362) -> begin
((lid), (us), (bs))
end
| uu____3369 -> begin
(failwith "Impossible!")
end)
in (match (uu____3348) with
| (ty_lid, ty_us, ty_bs) -> begin
(

let debug_log = (fun s -> (

let uu____3380 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Positivity")))
in (match (uu____3380) with
| true -> begin
(FStar_Util.print_string (Prims.strcat "Positivity::" (Prims.strcat s "\n")))
end
| uu____3381 -> begin
()
end)))
in ((debug_log (Prims.strcat "Checking positivity for " ty_lid.FStar_Ident.str));
(

let ty_occurs_in = (fun t -> (let _0_586 = (FStar_Syntax_Free.fvars t)
in (FStar_Util.set_mem ty_lid _0_586)))
in (

let try_get_fv = (fun t -> (

let uu____3395 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____3395) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((fv), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((fv), (us))
end
| uu____3409 -> begin
(failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
end)
end
| uu____3412 -> begin
(failwith "Node is not an fvar or a Tm_uinst")
end)))
in (

let uu____3415 = (FStar_Syntax_Subst.univ_var_opening ty_us)
in (match (uu____3415) with
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

let rec ty_positive_in_datacon = (fun env dt -> ((debug_log (let _0_587 = (FStar_Syntax_Print.term_to_string dt)
in (Prims.strcat "Checking data constructor type: " _0_587)));
(

let dt = (FStar_Syntax_Subst.subst ty_usubst dt)
in (

let uu____3475 = (FStar_Syntax_Subst.compress dt).FStar_Syntax_Syntax.n
in (match (uu____3475) with
| FStar_Syntax_Syntax.Tm_fvar (uu____3476) -> begin
((debug_log "Data constructor type is simply an fvar, returning true");
true;
)
end
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____3479) -> begin
(

let dbs = (Prims.snd (FStar_List.splitAt (FStar_List.length ty_bs) dbs))
in (

let dbs = (let _0_588 = (FStar_Syntax_Subst.opening_of_binders ty_bs)
in (FStar_Syntax_Subst.subst_binders _0_588 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in ((debug_log (let _0_590 = (let _0_589 = (FStar_Util.string_of_int (FStar_List.length dbs))
in (Prims.strcat _0_589 " binders"))
in (Prims.strcat "Data constructor type is an arrow type, so checking strict positivity in " _0_590)));
(

let uu____3514 = (FStar_List.fold_left (fun uu____3521 b -> (match (uu____3521) with
| (r, env) -> begin
(match ((not (r))) with
| true -> begin
((r), (env))
end
| uu____3533 -> begin
(let _0_592 = (ty_strictly_positive_in_type (Prims.fst b).FStar_Syntax_Syntax.sort env)
in (let _0_591 = (FStar_TypeChecker_Env.push_binders env ((b)::[]))
in ((_0_592), (_0_591))))
end)
end)) ((true), (env)) dbs)
in (match (uu____3514) with
| (b, uu____3539) -> begin
b
end));
))))
end
| FStar_Syntax_Syntax.Tm_app (uu____3540, uu____3541) -> begin
((debug_log "Data constructor type is a Tm_app, so returning true");
true;
)
end
| uu____3557 -> begin
(failwith "Unexpected data constructor type when checking positivity")
end)));
))
and ty_strictly_positive_in_type = (fun btype env -> ((debug_log (let _0_593 = (FStar_Syntax_Print.term_to_string btype)
in (Prims.strcat "Checking strict positivity in type: " _0_593)));
(

let btype = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env btype)
in ((debug_log (let _0_594 = (FStar_Syntax_Print.term_to_string btype)
in (Prims.strcat "Checking strict positivity in type, after normalization: " _0_594)));
((not ((ty_occurs_in btype))) || ((debug_log "ty does occur in this type, pressing ahead");
(

let uu____3564 = (FStar_Syntax_Subst.compress btype).FStar_Syntax_Syntax.n
in (match (uu____3564) with
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____3581 = (try_get_fv t)
in (match (uu____3581) with
| (fv, us) -> begin
(match ((FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v ty_lid)) with
| true -> begin
((debug_log "Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments");
(FStar_List.for_all (fun uu____3593 -> (match (uu____3593) with
| (t, uu____3597) -> begin
(not ((ty_occurs_in t)))
end)) args);
)
end
| uu____3598 -> begin
((debug_log "Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity");
(ty_nested_positive_in_inductive fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v us args env);
)
end)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (sbs, c) -> begin
((debug_log "Checking strict positivity in Tm_arrow");
(

let uu____3617 = (not ((FStar_Syntax_Util.is_pure_or_ghost_comp c)))
in (match (uu____3617) with
| true -> begin
((debug_log "Checking strict positivity , the arrow is impure, so return true");
true;
)
end
| uu____3619 -> begin
((debug_log "Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type");
((FStar_List.for_all (fun uu____3623 -> (match (uu____3623) with
| (b, uu____3627) -> begin
(not ((ty_occurs_in b.FStar_Syntax_Syntax.sort)))
end)) sbs) && (

let uu____3628 = (FStar_Syntax_Subst.open_term sbs (FStar_Syntax_Util.comp_result c))
in (match (uu____3628) with
| (uu____3631, return_type) -> begin
(let _0_595 = (FStar_TypeChecker_Env.push_binders env sbs)
in (ty_strictly_positive_in_type return_type _0_595))
end)));
)
end));
)
end
| FStar_Syntax_Syntax.Tm_fvar (uu____3633) -> begin
((debug_log "Checking strict positivity in an fvar, return true");
true;
)
end
| FStar_Syntax_Syntax.Tm_type (uu____3635) -> begin
((debug_log "Checking strict positivity in an Tm_type, return true");
true;
)
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____3638) -> begin
((debug_log "Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)");
(ty_strictly_positive_in_type t env);
)
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____3645) -> begin
((debug_log "Checking strict positivity in an Tm_refine, recur in the bv sort)");
(ty_strictly_positive_in_type bv.FStar_Syntax_Syntax.sort env);
)
end
| uu____3651 -> begin
((debug_log (let _0_596 = (FStar_Syntax_Print.term_to_string btype)
in (Prims.strcat "Checking strict positivity, unexpected term: " _0_596)));
false;
)
end));
));
));
))
and ty_nested_positive_in_inductive = (fun ilid us args env -> ((debug_log (let _0_599 = (let _0_598 = (let _0_597 = (FStar_Syntax_Print.args_to_string args)
in (Prims.strcat " applied to arguments: " _0_597))
in (Prims.strcat ilid.FStar_Ident.str _0_598))
in (Prims.strcat "Checking nested positivity in the inductive " _0_599)));
(

let uu____3658 = (FStar_TypeChecker_Env.datacons_of_typ env ilid)
in (match (uu____3658) with
| (b, idatas) -> begin
(match ((not (b))) with
| true -> begin
((debug_log "Checking nested positivity, not an inductive, return false");
false;
)
end
| uu____3667 -> begin
(

let uu____3668 = (already_unfolded env ilid args)
in (match (uu____3668) with
| true -> begin
((debug_log "Checking nested positivity, we have already unfolded this inductive with these args");
true;
)
end
| uu____3670 -> begin
(

let num_ibs = (FStar_TypeChecker_Env.num_inductive_ty_params env ilid)
in ((debug_log (let _0_601 = (let _0_600 = (FStar_Util.string_of_int num_ibs)
in (Prims.strcat _0_600 ", also adding to the memo table"))
in (Prims.strcat "Checking nested positivity, number of type parameters is " _0_601)));
(let _0_606 = (let _0_605 = (FStar_ST.read unfolded_inductives)
in (let _0_604 = (let _0_603 = (let _0_602 = (Prims.fst (FStar_List.splitAt num_ibs args))
in ((ilid), (_0_602)))
in (_0_603)::[])
in (FStar_List.append _0_605 _0_604)))
in (FStar_ST.write unfolded_inductives _0_606));
(FStar_List.for_all (fun d -> (ty_nested_positive_in_dlid d ilid us args num_ibs env)) idatas);
))
end))
end)
end));
))
and ty_nested_positive_in_dlid = (fun dlid ilid us args num_ibs env -> ((debug_log (Prims.strcat "Checking nested positivity in data constructor " (Prims.strcat dlid.FStar_Ident.str (Prims.strcat " of the inductive " ilid.FStar_Ident.str))));
(

let uu____3736 = (FStar_TypeChecker_Env.lookup_datacon env dlid)
in (match (uu____3736) with
| (univ_unif_vars, dt) -> begin
((FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| uu____3748 -> begin
(failwith "Impossible")
end)) univ_unif_vars us);
(

let dt = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env dt)
in ((debug_log (let _0_607 = (FStar_Syntax_Print.term_to_string dt)
in (Prims.strcat "Checking nested positivity in the data constructor type: " _0_607)));
(

let uu____3751 = (FStar_Syntax_Subst.compress dt).FStar_Syntax_Syntax.n
in (match (uu____3751) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, c) -> begin
((debug_log "Checked nested positivity in Tm_arrow data constructor type");
(

let uu____3765 = (FStar_List.splitAt num_ibs dbs)
in (match (uu____3765) with
| (ibs, dbs) -> begin
(

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let dbs = (let _0_608 = (FStar_Syntax_Subst.opening_of_binders ibs)
in (FStar_Syntax_Subst.subst_binders _0_608 dbs))
in (

let c = (let _0_609 = (FStar_Syntax_Subst.opening_of_binders ibs)
in (FStar_Syntax_Subst.subst_comp _0_609 c))
in (

let uu____3793 = (FStar_List.splitAt num_ibs args)
in (match (uu____3793) with
| (args, uu____3811) -> begin
(

let subst = (FStar_List.fold_left2 (fun subst ib arg -> (FStar_List.append subst ((FStar_Syntax_Syntax.NT ((((Prims.fst ib)), ((Prims.fst arg)))))::[]))) [] ibs args)
in (

let dbs = (FStar_Syntax_Subst.subst_binders subst dbs)
in (

let c = (let _0_610 = (FStar_Syntax_Subst.shift_subst (FStar_List.length dbs) subst)
in (FStar_Syntax_Subst.subst_comp _0_610 c))
in ((debug_log (let _0_614 = (let _0_613 = (FStar_Syntax_Print.binders_to_string "; " dbs)
in (let _0_612 = (let _0_611 = (FStar_Syntax_Print.comp_to_string c)
in (Prims.strcat ", and c: " _0_611))
in (Prims.strcat _0_613 _0_612)))
in (Prims.strcat "Checking nested positivity in the unfolded data constructor binders as: " _0_614)));
(ty_nested_positive_in (FStar_Syntax_Syntax.Tm_arrow (((dbs), (c)))) ilid num_ibs env);
))))
end)))))
end));
)
end
| uu____3863 -> begin
((debug_log "Checking nested positivity in the data constructor type that is not an arrow");
(let _0_615 = (FStar_Syntax_Subst.compress dt).FStar_Syntax_Syntax.n
in (ty_nested_positive_in _0_615 ilid num_ibs env));
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

let uu____3886 = (try_get_fv t)
in (match (uu____3886) with
| (fv, uu____3890) -> begin
(match ((FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v ilid)) with
| true -> begin
true
end
| uu____3895 -> begin
(failwith "Impossible, expected the type to be ilid")
end)
end));
)
end
| FStar_Syntax_Syntax.Tm_arrow (sbs, c) -> begin
((debug_log (let _0_616 = (FStar_Syntax_Print.binders_to_string "; " sbs)
in (Prims.strcat "Checking nested positivity in an Tm_arrow node, with binders as: " _0_616)));
(

let uu____3909 = (FStar_List.fold_left (fun uu____3916 b -> (match (uu____3916) with
| (r, env) -> begin
(match ((not (r))) with
| true -> begin
((r), (env))
end
| uu____3928 -> begin
(let _0_618 = (ty_strictly_positive_in_type (Prims.fst b).FStar_Syntax_Syntax.sort env)
in (let _0_617 = (FStar_TypeChecker_Env.push_binders env ((b)::[]))
in ((_0_618), (_0_617))))
end)
end)) ((true), (env)) sbs)
in (match (uu____3909) with
| (b, uu____3934) -> begin
b
end));
)
end
| uu____3935 -> begin
(failwith "Nested positive check, unhandled case")
end))
in (FStar_List.for_all (fun d -> (let _0_619 = (datacon_typ d)
in (ty_positive_in_datacon env _0_619))) datas))))))
end))));
))
end)))))
in ((

let uu____3938 = ((FStar_Options.no_positivity ()) || (FStar_Options.lax ()))
in (match (uu____3938) with
| true -> begin
()
end
| uu____3939 -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (FStar_List.iter (fun ty -> (

let b = (check_positivity env ty)
in (match ((not (b))) with
| true -> begin
(

let uu____3944 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____3950, uu____3951, uu____3952, uu____3953, uu____3954, uu____3955, r) -> begin
((lid), (r))
end
| uu____3963 -> begin
(failwith "Impossible!")
end)
in (match (uu____3944) with
| (lid, r) -> begin
(FStar_Errors.report r (Prims.strcat "Inductive type " (Prims.strcat lid.FStar_Ident.str " does not satisfy the positivity condition")))
end))
end
| uu____3968 -> begin
()
end))) tcs))
end));
(

let datacon_typ = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (uu____3973, uu____3974, t, uu____3976, uu____3977, uu____3978, uu____3979, uu____3980) -> begin
t
end
| uu____3985 -> begin
(failwith "Impossible!")
end))
in (

let dr = FStar_Range.dummyRange
in (

let optimized_haseq_scheme = (fun uu____3991 -> (

let haseq_ty = (fun usubst us acc ty -> (

let uu____4035 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____4047, bs, t, uu____4050, d_lids, uu____4052, uu____4053) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____4061 -> begin
(failwith "Impossible!")
end)
in (match (uu____4035) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _0_620 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _0_620 t))
in (

let uu____4091 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____4091) with
| (bs, t) -> begin
(

let ibs = (

let uu____4111 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____4111) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____4116) -> begin
ibs
end
| uu____4127 -> begin
[]
end))
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _0_622 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _0_621 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _0_622 _0_621)))
in (

let ind = ((let _0_624 = (FStar_List.map (fun uu____4144 -> (match (uu____4144) with
| (bv, aq) -> begin
(let _0_623 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_0_623), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _0_624)) None dr)
in (

let ind = ((let _0_626 = (FStar_List.map (fun uu____4162 -> (match (uu____4162) with
| (bv, aq) -> begin
(let _0_625 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_0_625), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _0_626)) None dr)
in (

let haseq_ind = ((let _0_628 = (let _0_627 = (FStar_Syntax_Syntax.as_arg ind)
in (_0_627)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _0_628)) None dr)
in (

let bs' = (FStar_List.filter (fun b -> (

let uu____4185 = acc
in (match (uu____4185) with
| (uu____4193, en, uu____4195, uu____4196) -> begin
(

let opt = (let _0_629 = (Prims.fst (FStar_Syntax_Util.type_u ()))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort _0_629 false))
in (match (opt) with
| None -> begin
false
end
| Some (uu____4205) -> begin
true
end))
end))) bs)
in (

let haseq_bs = (FStar_List.fold_left (fun t b -> (let _0_632 = ((let _0_631 = (let _0_630 = (FStar_Syntax_Syntax.as_arg (FStar_Syntax_Syntax.bv_to_name (Prims.fst b)))
in (_0_630)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _0_631)) None dr)
in (FStar_Syntax_Util.mk_conj t _0_632))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml = (

let uu___108_4219 = fml
in (let _0_636 = FStar_Syntax_Syntax.Tm_meta ((let _0_635 = FStar_Syntax_Syntax.Meta_pattern ((let _0_634 = (let _0_633 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_0_633)::[])
in (_0_634)::[]))
in ((fml), (_0_635))))
in {FStar_Syntax_Syntax.n = _0_636; FStar_Syntax_Syntax.tk = uu___108_4219.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___108_4219.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___108_4219.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> ((let _0_639 = (let _0_638 = (FStar_Syntax_Syntax.as_arg (let _0_637 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _0_637 None)))
in (_0_638)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _0_639)) None dr)) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> ((let _0_642 = (let _0_641 = (FStar_Syntax_Syntax.as_arg (let _0_640 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _0_640 None)))
in (_0_641)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _0_642)) None dr)) bs fml)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let uu____4271 = acc
in (match (uu____4271) with
| (l_axioms, env, guard', cond') -> begin
(

let env = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env = (FStar_TypeChecker_Env.push_binders env ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (uu____4305, uu____4306, uu____4307, t_lid, uu____4309, uu____4310, uu____4311, uu____4312) -> begin
(t_lid = lid)
end
| uu____4317 -> begin
(failwith "Impossible")
end)) datas)
in (

let haseq_data = (fun data -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (

let uu____4324 = (FStar_Syntax_Subst.compress dt).FStar_Syntax_Syntax.n
in (match (uu____4324) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____4326) -> begin
(

let dbs = (Prims.snd (FStar_List.splitAt (FStar_List.length bs) dbs))
in (

let dbs = (let _0_643 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _0_643 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let haseq_b = ((let _0_645 = (let _0_644 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_0_644)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _0_645)) None dr)
in (

let sort_range = (Prims.fst b).FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos
in (

let haseq_b = (let _0_647 = (let _0_646 = (FStar_Syntax_Print.term_to_string ind)
in (FStar_Util.format1 "Failed to prove that the type \'%s\' supports decidable equality because of this argument; add the \'noeq\' qualifier" _0_646))
in (FStar_TypeChecker_Util.label _0_647 sort_range haseq_b))
in (FStar_Syntax_Util.mk_conj t haseq_b))))) FStar_Syntax_Util.t_true dbs)
in (FStar_List.fold_right (fun b t -> ((let _0_650 = (let _0_649 = (FStar_Syntax_Syntax.as_arg (let _0_648 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _0_648 None)))
in (_0_649)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _0_650)) None dr)) dbs cond)))))
end
| uu____4387 -> begin
FStar_Syntax_Util.t_true
end)))))
in (

let cond = (FStar_List.fold_left (fun acc d -> (let _0_651 = (haseq_data d)
in (FStar_Syntax_Util.mk_conj acc _0_651))) FStar_Syntax_Util.t_true t_datas)
in (

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (let _0_653 = (FStar_Syntax_Util.mk_conj guard' guard)
in (let _0_652 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml)))::[]))), (env), (_0_653), (_0_652))))))))))
end)))))))))))))))
end))))
end)))
in (

let us = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____4407, us, uu____4409, uu____4410, uu____4411, uu____4412, uu____4413, uu____4414) -> begin
us
end
| uu____4421 -> begin
(failwith "Impossible!")
end))
in (

let uu____4422 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____4422) with
| (usubst, us) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq");
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle);
(

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let uu____4438 = (FStar_List.fold_left (haseq_ty usubst us) (([]), (env), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (uu____4438) with
| (axioms, env, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let uu____4470 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env phi)
in (match (uu____4470) with
| (phi, uu____4475) -> begin
((

let uu____4477 = (FStar_TypeChecker_Env.should_verify env)
in (match (uu____4477) with
| true -> begin
(let _0_654 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi)))
in (FStar_TypeChecker_Rel.force_trivial_guard env _0_654))
end
| uu____4478 -> begin
()
end));
(

let ses = (FStar_List.fold_left (fun l uu____4485 -> (match (uu____4485) with
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

let unoptimized_haseq_scheme = (fun uu____4498 -> (

let mutuals = (FStar_List.map (fun ty -> (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____4504, uu____4505, uu____4506, uu____4507, uu____4508, uu____4509, uu____4510) -> begin
lid
end
| uu____4517 -> begin
(failwith "Impossible!")
end)) tcs)
in (

let haseq_ty = (fun usubst us acc ty -> (

let uu____4537 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____4549, bs, t, uu____4552, d_lids, uu____4554, uu____4555) -> begin
((lid), (bs), (t), (d_lids))
end
| uu____4563 -> begin
(failwith "Impossible!")
end)
in (match (uu____4537) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _0_655 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _0_655 t))
in (

let uu____4584 = (FStar_Syntax_Subst.open_term bs t)
in (match (uu____4584) with
| (bs, t) -> begin
(

let ibs = (

let uu____4595 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____4595) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, uu____4600) -> begin
ibs
end
| uu____4611 -> begin
[]
end))
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _0_657 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _0_656 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _0_657 _0_656)))
in (

let ind = ((let _0_659 = (FStar_List.map (fun uu____4628 -> (match (uu____4628) with
| (bv, aq) -> begin
(let _0_658 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_0_658), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _0_659)) None dr)
in (

let ind = ((let _0_661 = (FStar_List.map (fun uu____4646 -> (match (uu____4646) with
| (bv, aq) -> begin
(let _0_660 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_0_660), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _0_661)) None dr)
in (

let haseq_ind = ((let _0_663 = (let _0_662 = (FStar_Syntax_Syntax.as_arg ind)
in (_0_662)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _0_663)) None dr)
in (

let rec is_mutual = (fun t -> (

let uu____4670 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____4670) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.existsb (fun lid -> (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) mutuals)
end
| FStar_Syntax_Syntax.Tm_uinst (t', uu____4678) -> begin
(is_mutual t')
end
| FStar_Syntax_Syntax.Tm_refine (bv, t') -> begin
(is_mutual bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_app (t', args) -> begin
(

let uu____4705 = (is_mutual t')
in (match (uu____4705) with
| true -> begin
true
end
| uu____4706 -> begin
(exists_mutual (FStar_List.map Prims.fst args))
end))
end
| FStar_Syntax_Syntax.Tm_meta (t', uu____4716) -> begin
(is_mutual t')
end
| uu____4721 -> begin
false
end)))
and exists_mutual = (fun uu___88_4722 -> (match (uu___88_4722) with
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

let uu____4748 = (FStar_Syntax_Subst.compress dt).FStar_Syntax_Syntax.n
in (match (uu____4748) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, uu____4752) -> begin
(

let dbs = (Prims.snd (FStar_List.splitAt (FStar_List.length bs) dbs))
in (

let dbs = (let _0_664 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _0_664 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let sort = (Prims.fst b).FStar_Syntax_Syntax.sort
in (

let haseq_sort = ((let _0_666 = (let _0_665 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_0_665)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _0_666)) None dr)
in (

let haseq_sort = (

let uu____4795 = (is_mutual sort)
in (match (uu____4795) with
| true -> begin
(FStar_Syntax_Util.mk_imp haseq_ind haseq_sort)
end
| uu____4796 -> begin
haseq_sort
end))
in (FStar_Syntax_Util.mk_conj t haseq_sort))))) FStar_Syntax_Util.t_true dbs)
in (

let cond = (FStar_List.fold_right (fun b t -> ((let _0_669 = (let _0_668 = (FStar_Syntax_Syntax.as_arg (let _0_667 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _0_667 None)))
in (_0_668)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _0_669)) None dr)) dbs cond)
in (FStar_Syntax_Util.mk_conj acc cond))))))
end
| uu____4818 -> begin
acc
end)))))
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (uu____4822, uu____4823, uu____4824, t_lid, uu____4826, uu____4827, uu____4828, uu____4829) -> begin
(t_lid = lid)
end
| uu____4834 -> begin
(failwith "Impossible")
end)) datas)
in (

let data_cond = (FStar_List.fold_left haseq_data FStar_Syntax_Util.t_true t_datas)
in (

let fml = (FStar_Syntax_Util.mk_imp data_cond haseq_ind)
in (

let fml = (

let uu___109_4840 = fml
in (let _0_673 = FStar_Syntax_Syntax.Tm_meta ((let _0_672 = FStar_Syntax_Syntax.Meta_pattern ((let _0_671 = (let _0_670 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_0_670)::[])
in (_0_671)::[]))
in ((fml), (_0_672))))
in {FStar_Syntax_Syntax.n = _0_673; FStar_Syntax_Syntax.tk = uu___109_4840.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___109_4840.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___109_4840.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> ((let _0_676 = (let _0_675 = (FStar_Syntax_Syntax.as_arg (let _0_674 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _0_674 None)))
in (_0_675)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _0_676)) None dr)) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> ((let _0_679 = (let _0_678 = (FStar_Syntax_Syntax.as_arg (let _0_677 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _0_677 None)))
in (_0_678)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _0_679)) None dr)) bs fml)
in (FStar_Syntax_Util.mk_conj acc fml)))))))))))))))
end))))
end)))
in (

let uu____4889 = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, uu____4897, uu____4898, uu____4899, uu____4900, uu____4901, uu____4902) -> begin
((lid), (us))
end
| uu____4909 -> begin
(failwith "Impossible!")
end))
in (match (uu____4889) with
| (lid, us) -> begin
(

let uu____4915 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____4915) with
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

let se = (let _0_680 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (tc_assume env _0_680 fml [] dr))
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq");
(se)::[];
)));
)))
end))
end)))))
in (

let skip_prims_type = (fun uu____4937 -> (

let lid = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____4941, uu____4942, uu____4943, uu____4944, uu____4945, uu____4946, uu____4947) -> begin
lid
end
| uu____4954 -> begin
(failwith "Impossible")
end))
in (

let types_to_skip = ("c_False")::("c_True")::("equals")::("h_equals")::("c_and")::("c_or")::[]
in (FStar_List.existsb (fun s -> (s = lid.FStar_Ident.ident.FStar_Ident.idText)) types_to_skip))))
in (

let is_noeq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Noeq)) quals)
in (

let uu____4960 = ((((FStar_List.length tcs) = (Prims.parse_int "0")) || ((FStar_Ident.lid_equals env.FStar_TypeChecker_Env.curmodule FStar_Syntax_Const.prims_lid) && (skip_prims_type ()))) || is_noeq)
in (match (uu____4960) with
| true -> begin
(((sig_bndle)::[]), (data_ops_ses))
end
| uu____4969 -> begin
(

let is_unopteq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Unopteq)) quals)
in (

let ses = (match (is_unopteq) with
| true -> begin
(unoptimized_haseq_scheme ())
end
| uu____4975 -> begin
(optimized_haseq_scheme ())
end)
in (let _0_683 = (let _0_682 = FStar_Syntax_Syntax.Sig_bundle ((let _0_681 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_0_681))))
in (_0_682)::ses)
in ((_0_683), (data_ops_ses)))))
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
in (let _0_684 = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (_0_684), ([])))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let uu____5028 = (tc_inductive env ses quals lids)
in (match (uu____5028) with
| (ses, projectors_ses) -> begin
(

let env = (FStar_List.fold_left (fun env' se -> (FStar_TypeChecker_Env.push_sigelt env' se)) env ses)
in ((ses), (env), (projectors_ses)))
end)))
end
| FStar_Syntax_Syntax.Sig_pragma (p, r) -> begin
(

let set_options = (fun t s -> (

let uu____5058 = (FStar_Options.set_options t s)
in (match (uu____5058) with
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
| uu____5066 -> begin
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
((let _0_685 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _0_685 Prims.ignore));
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
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____5081) -> begin
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

let uu____5094 = (FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun uu____5105 a -> (match (uu____5105) with
| (env, ses) -> begin
(

let se_let = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a)
in (let _0_686 = (FStar_TypeChecker_Env.push_sigelt env se_let)
in ((_0_686), ((se_let)::ses))))
end)) ((env), ((se)::[]))))
in (match (uu____5094) with
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

let uu____5135 = (let _0_687 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _0_687))
in (match (uu____5135) with
| (a, wp_a_src) -> begin
(

let uu____5151 = (let _0_688 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _0_688))
in (match (uu____5151) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (let _0_691 = (let _0_690 = FStar_Syntax_Syntax.NT ((let _0_689 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (_0_689))))
in (_0_690)::[])
in (FStar_Syntax_Subst.subst _0_691 wp_b_tgt))
in (

let expected_k = (let _0_696 = (let _0_694 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_693 = (let _0_692 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_0_692)::[])
in (_0_694)::_0_693))
in (let _0_695 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _0_696 _0_695)))
in (

let repr_type = (fun eff_name a wp -> (

let no_reify = (fun l -> (Prims.raise (FStar_Errors.Error ((let _0_698 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _0_697 = (FStar_TypeChecker_Env.get_range env)
in ((_0_698), (_0_697))))))))
in (

let uu____5191 = (FStar_TypeChecker_Env.effect_decl_opt env eff_name)
in (match (uu____5191) with
| None -> begin
(no_reify eff_name)
end
| Some (ed) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((FStar_Syntax_Syntax.U_unknown)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let uu____5198 = (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))))
in (match (uu____5198) with
| true -> begin
(no_reify eff_name)
end
| uu____5202 -> begin
(let _0_703 = (FStar_TypeChecker_Env.get_range env)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_702 = (let _0_701 = (FStar_Syntax_Syntax.as_arg a)
in (let _0_700 = (let _0_699 = (FStar_Syntax_Syntax.as_arg wp)
in (_0_699)::[])
in (_0_701)::_0_700))
in ((repr), (_0_702)))))) None _0_703))
end)))
end))))
in (

let uu____5212 = (match (((sub.FStar_Syntax_Syntax.lift), (sub.FStar_Syntax_Syntax.lift_wp))) with
| (None, None) -> begin
(failwith "Impossible")
end
| (lift, Some (uu____5227, lift_wp)) -> begin
(let _0_704 = (check_and_gen env lift_wp expected_k)
in ((lift), (_0_704)))
end
| (Some (what, lift), None) -> begin
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange))
in (

let uu____5254 = (FStar_TypeChecker_DMFF.star_expr dmff_env lift)
in (match (uu____5254) with
| (uu____5261, lift_wp, lift_elab) -> begin
(

let uu____5264 = (recheck_debug "lift-wp" env lift_wp)
in (

let uu____5265 = (recheck_debug "lift-elab" env lift_elab)
in ((Some ((([]), (lift_elab)))), ((([]), (lift_wp))))))
end)))
end)
in (match (uu____5212) with
| (lift, lift_wp) -> begin
(

let lax = env.FStar_TypeChecker_Env.lax
in (

let env = (

let uu___110_5289 = env
in {FStar_TypeChecker_Env.solver = uu___110_5289.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___110_5289.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___110_5289.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___110_5289.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___110_5289.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___110_5289.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___110_5289.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___110_5289.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___110_5289.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___110_5289.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___110_5289.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___110_5289.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___110_5289.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___110_5289.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___110_5289.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___110_5289.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___110_5289.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___110_5289.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___110_5289.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___110_5289.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___110_5289.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___110_5289.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___110_5289.FStar_TypeChecker_Env.qname_and_index})
in (

let lift = (match (lift) with
| None -> begin
None
end
| Some (uu____5293, lift) -> begin
(

let uu____5300 = (let _0_705 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _0_705))
in (match (uu____5300) with
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

let lift_wp_a = (let _0_710 = (FStar_TypeChecker_Env.get_range env)
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_709 = (let _0_708 = (FStar_Syntax_Syntax.as_arg a_typ)
in (let _0_707 = (let _0_706 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (_0_706)::[])
in (_0_708)::_0_707))
in ((lift_wp), (_0_709)))))) None _0_710))
in (repr_type sub.FStar_Syntax_Syntax.target a_typ lift_wp_a)))
in (

let expected_k = (let _0_717 = (let _0_715 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_714 = (let _0_713 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (let _0_712 = (let _0_711 = (FStar_Syntax_Syntax.null_binder repr_f)
in (_0_711)::[])
in (_0_713)::_0_712))
in (_0_715)::_0_714))
in (let _0_716 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow _0_717 _0_716)))
in (

let uu____5338 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (uu____5338) with
| (expected_k, uu____5344, uu____5345) -> begin
(

let lift = (check_and_gen env lift expected_k)
in Some (lift))
end))))))))
end))
end)
in (

let env = (

let uu___111_5348 = env
in {FStar_TypeChecker_Env.solver = uu___111_5348.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___111_5348.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___111_5348.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___111_5348.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___111_5348.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___111_5348.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___111_5348.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___111_5348.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___111_5348.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___111_5348.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___111_5348.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___111_5348.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___111_5348.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___111_5348.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___111_5348.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___111_5348.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___111_5348.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___111_5348.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = lax; FStar_TypeChecker_Env.lax_universes = uu___111_5348.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___111_5348.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___111_5348.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___111_5348.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___111_5348.FStar_TypeChecker_Env.qname_and_index})
in (

let sub = (

let uu___112_5350 = sub
in {FStar_Syntax_Syntax.source = uu___112_5350.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = uu___112_5350.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = Some (lift_wp); FStar_Syntax_Syntax.lift = lift})
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

let uu____5369 = (FStar_Syntax_Subst.open_comp tps c)
in (match (uu____5369) with
| (tps, c) -> begin
(

let uu____5379 = (tc_tparams env tps)
in (match (uu____5379) with
| (tps, env, us) -> begin
(

let uu____5391 = (FStar_TypeChecker_TcTerm.tc_comp env c)
in (match (uu____5391) with
| (c, u, g) -> begin
((FStar_TypeChecker_Rel.force_trivial_guard env g);
(

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

let uu____5406 = (let _0_718 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _0_718))
in (match (uu____5406) with
| (uvs, t) -> begin
(

let uu____5424 = (

let uu____5432 = (let _0_719 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in ((tps), (_0_719)))
in (match (uu____5432) with
| ([], FStar_Syntax_Syntax.Tm_arrow (uu____5442, c)) -> begin
(([]), (c))
end
| (uu____5466, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
((tps), (c))
end
| uu____5484 -> begin
(failwith "Impossible")
end))
in (match (uu____5424) with
| (tps, c) -> begin
((match ((((FStar_List.length uvs) <> (Prims.parse_int "1")) && (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid))))) with
| true -> begin
(

let uu____5514 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____5514) with
| (uu____5517, t) -> begin
(Prims.raise (FStar_Errors.Error ((let _0_723 = (let _0_722 = (FStar_Syntax_Print.lid_to_string lid)
in (let _0_721 = (FStar_All.pipe_right (FStar_List.length uvs) FStar_Util.string_of_int)
in (let _0_720 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)" _0_722 _0_721 _0_720))))
in ((_0_723), (r))))))
end))
end
| uu____5521 -> begin
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
| (FStar_Syntax_Syntax.Sig_declare_typ (_, _, _, quals, _)) | (FStar_Syntax_Syntax.Sig_let (_, _, _, quals, _)) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___89_5550 -> (match (uu___89_5550) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| uu____5551 -> begin
false
end)))) -> begin
(([]), (env), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t, quals, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let uu____5562 = (match ((uvs = [])) with
| true -> begin
(let _0_724 = (Prims.fst (FStar_Syntax_Util.type_u ()))
in (check_and_gen env t _0_724))
end
| uu____5563 -> begin
(

let uu____5564 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____5564) with
| (uvs, t) -> begin
(let _0_727 = (let _0_726 = (let _0_725 = (Prims.fst (FStar_Syntax_Util.type_u ()))
in (tc_check_trivial_guard env t _0_725))
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) _0_726))
in ((uvs), (_0_727)))
end))
end)
in (match (uu____5562) with
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

let uu____5598 = (FStar_TypeChecker_TcTerm.tc_term env e)
in (match (uu____5598) with
| (e, c, g1) -> begin
(

let uu____5610 = (let _0_730 = Some ((FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r))
in (let _0_729 = (let _0_728 = (c.FStar_Syntax_Syntax.comp ())
in ((e), (_0_728)))
in (FStar_TypeChecker_TcTerm.check_expected_effect env _0_730 _0_729)))
in (match (uu____5610) with
| (e, uu____5622, g) -> begin
((let _0_731 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _0_731));
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

let uu____5666 = (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q'))
in (match (uu____5666) with
| true -> begin
Some (q)
end
| uu____5674 -> begin
(Prims.raise (FStar_Errors.Error ((let _0_735 = (let _0_734 = (FStar_Syntax_Print.lid_to_string l)
in (let _0_733 = (FStar_Syntax_Print.quals_to_string q)
in (let _0_732 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _0_734 _0_733 _0_732))))
in ((_0_735), (r))))))
end))
end))
in (

let uu____5677 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun uu____5698 lb -> (match (uu____5698) with
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____5722 = (

let uu____5728 = (FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____5728) with
| None -> begin
(match ((lb.FStar_Syntax_Syntax.lbunivs <> [])) with
| true -> begin
((false), (lb), (quals_opt))
end
| uu____5753 -> begin
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
| uu____5780 -> begin
(FStar_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end);
(match (((lb.FStar_Syntax_Syntax.lbunivs <> []) && ((FStar_List.length lb.FStar_Syntax_Syntax.lbunivs) <> (FStar_List.length uvs)))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Inline universes are incoherent with annotation from val declaration"), (r)))))
end
| uu____5787 -> begin
()
end);
(let _0_736 = (FStar_Syntax_Syntax.mk_lb ((FStar_Util.Inr (lbname)), (uvs), (FStar_Syntax_Const.effect_ALL_lid), (tval), (lb.FStar_Syntax_Syntax.lbdef)))
in ((false), (_0_736), (quals_opt)));
))
end))
in (match (uu____5722) with
| (gen, lb, quals_opt) -> begin
((gen), ((lb)::lbs), (quals_opt))
end)))
end)) ((true), ([]), ((match ((quals = [])) with
| true -> begin
None
end
| uu____5818 -> begin
Some (quals)
end)))))
in (match (uu____5677) with
| (should_generalize, lbs', quals_opt) -> begin
(

let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Visible_default)::[]
end
| Some (q) -> begin
(

let uu____5841 = (FStar_All.pipe_right q (FStar_Util.for_some (fun uu___90_5843 -> (match (uu___90_5843) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Visible_default) | (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> begin
true
end
| uu____5844 -> begin
false
end))))
in (match (uu____5841) with
| true -> begin
q
end
| uu____5846 -> begin
(FStar_Syntax_Syntax.Visible_default)::q
end))
end)
in (

let lbs' = (FStar_List.rev lbs')
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let ((let _0_737 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((((Prims.fst lbs)), (lbs'))), (_0_737)))))) None r)
in (

let uu____5875 = (

let uu____5881 = (FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term (

let uu___113_5885 = env
in {FStar_TypeChecker_Env.solver = uu___113_5885.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___113_5885.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___113_5885.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___113_5885.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___113_5885.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___113_5885.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___113_5885.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___113_5885.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___113_5885.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___113_5885.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___113_5885.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = uu___113_5885.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = uu___113_5885.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___113_5885.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___113_5885.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___113_5885.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = uu___113_5885.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___113_5885.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___113_5885.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___113_5885.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___113_5885.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___113_5885.FStar_TypeChecker_Env.qname_and_index}) e)
in (match (uu____5881) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = uu____5893; FStar_Syntax_Syntax.pos = uu____5894; FStar_Syntax_Syntax.vars = uu____5895}, uu____5896, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (uu____5915, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| uu____5920 -> begin
quals
end)
in ((FStar_Syntax_Syntax.Sig_let (((lbs), (r), (lids), (quals), (attrs)))), (lbs)))
end
| uu____5930 -> begin
(failwith "impossible")
end))
in (match (uu____5875) with
| (se, lbs) -> begin
((

let uu____5953 = (log env)
in (match (uu____5953) with
| true -> begin
(let _0_742 = (let _0_741 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (

let uu____5960 = (let _0_738 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname).FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (FStar_TypeChecker_Env.try_lookup_val_decl env _0_738))
in (match (uu____5960) with
| None -> begin
true
end
| uu____5972 -> begin
false
end))
in (match (should_log) with
| true -> begin
(let _0_740 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _0_739 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _0_740 _0_739)))
end
| uu____5977 -> begin
""
end)))))
in (FStar_All.pipe_right _0_741 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _0_742))
end
| uu____5978 -> begin
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

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___91_6005 -> (match (uu___91_6005) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| uu____6006 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| uu____6014 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (uu____6019) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, uu____6032, r) -> begin
(

let uu____6040 = (is_abstract quals)
in (match (uu____6040) with
| true -> begin
(FStar_List.fold_right (fun se uu____6050 -> (match (uu____6050) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, uu____6073, uu____6074, quals, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ ((let _0_744 = (let _0_743 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow bs _0_743))
in ((l), (us), (_0_744), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals), (r))))
in (((dec)::out), (hidden)))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, uu____6092, uu____6093, uu____6094, uu____6095, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]), (r)))
in (((dec)::out), ((l)::hidden)))
end
| uu____6105 -> begin
((out), (hidden))
end)
end)) ses (([]), (hidden)))
end
| uu____6110 -> begin
(((se)::[]), (hidden))
end))
end
| FStar_Syntax_Syntax.Sig_assume (uu____6113, uu____6114, quals, uu____6116) -> begin
(

let uu____6119 = (is_abstract quals)
in (match (uu____6119) with
| true -> begin
(([]), (hidden))
end
| uu____6126 -> begin
(((se)::[]), (hidden))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, us, t, quals, r) -> begin
(

let uu____6136 = (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc))
in (match (uu____6136) with
| true -> begin
(((FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]), (r))))::[]), ((l)::hidden))
end
| uu____6145 -> begin
(

let uu____6146 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___92_6148 -> (match (uu___92_6148) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| uu____6151 -> begin
false
end))))
in (match (uu____6146) with
| true -> begin
(((se)::[]), (hidden))
end
| uu____6158 -> begin
(([]), (hidden))
end))
end))
end
| FStar_Syntax_Syntax.Sig_main (uu____6161) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____6173, uu____6174, quals, uu____6176) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____6194 = (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
in (match (uu____6194) with
| true -> begin
(([]), (hidden))
end
| uu____6202 -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::[]), ((FStar_Ident.range_of_lid lid))))
in (((dec)::[]), ((lid)::hidden)))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals, uu____6218) -> begin
(

let uu____6225 = (is_abstract quals)
in (match (uu____6225) with
| true -> begin
(let _0_746 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> FStar_Syntax_Syntax.Sig_declare_typ ((let _0_745 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname).FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in ((_0_745), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))))))
in ((_0_746), (hidden)))
end
| uu____6244 -> begin
(((se)::[]), (hidden))
end))
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let rec process_one_decl = (fun uu____6281 se -> (match (uu____6281) with
| (ses, exports, env, hidden) -> begin
((

let uu____6312 = (FStar_TypeChecker_Env.debug env FStar_Options.Low)
in (match (uu____6312) with
| true -> begin
(let _0_747 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _0_747))
end
| uu____6313 -> begin
()
end));
(

let uu____6314 = (tc_decl env se)
in (match (uu____6314) with
| (ses', env, ses_elaborated) -> begin
((

let uu____6336 = ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes"))))
in (match (uu____6336) with
| true -> begin
(let _0_750 = (FStar_List.fold_left (fun s se -> (let _0_749 = (let _0_748 = (FStar_Syntax_Print.sigelt_to_string se)
in (Prims.strcat _0_748 "\n"))
in (Prims.strcat s _0_749))) "" ses')
in (FStar_Util.print1 "Checked: %s\n" _0_750))
end
| uu____6339 -> begin
()
end));
(FStar_List.iter (fun se -> (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)) ses');
(

let uu____6342 = (FStar_List.fold_left (fun uu____6351 se -> (match (uu____6351) with
| (le, lh) -> begin
(

let tup = (for_export hidden se)
in (((FStar_List.rev_append (Prims.fst tup) le)), ((FStar_List.rev_append (Prims.snd tup) lh))))
end)) (([]), ([])) ses')
in (match (uu____6342) with
| (exported, hidden) -> begin
(FStar_List.fold_left process_one_decl (((FStar_List.rev_append ses' ses)), (((FStar_List.rev_append exported []))::exports), (env), (hidden)) ses_elaborated)
end));
)
end));
)
end))
in (

let uu____6407 = (FStar_List.fold_left (fun acc se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, r) -> begin
(

let uu____6444 = acc
in (match (uu____6444) with
| (uu____6461, uu____6462, env, uu____6464) -> begin
(

let uu____6473 = (cps_and_elaborate env ne)
in (match (uu____6473) with
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
| uu____6506 -> begin
(process_one_decl acc se)
end)) (([]), ([]), (env), ([])) ses)
in (match (uu____6407) with
| (ses, exports, env, uu____6520) -> begin
(let _0_751 = (FStar_All.pipe_right (FStar_List.rev_append exports []) FStar_List.flatten)
in (((FStar_List.rev_append ses [])), (_0_751), (env)))
end))))


let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (

let verify = (FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let action = (match (verify) with
| true -> begin
"Verifying"
end
| uu____6548 -> begin
"Lax-checking"
end)
in (

let label = (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____6550 -> begin
"implementation"
end)
in ((

let uu____6552 = (FStar_Options.debug_any ())
in (match (uu____6552) with
| true -> begin
(FStar_Util.print3 "%s %s of %s\n" action label modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
end
| uu____6553 -> begin
()
end));
(

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____6555 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let msg = (Prims.strcat "Internals for " name)
in (

let env = (

let uu___114_6558 = env
in {FStar_TypeChecker_Env.solver = uu___114_6558.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___114_6558.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___114_6558.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___114_6558.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___114_6558.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___114_6558.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___114_6558.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___114_6558.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___114_6558.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___114_6558.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___114_6558.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___114_6558.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___114_6558.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___114_6558.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___114_6558.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___114_6558.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = (not (verify)); FStar_TypeChecker_Env.lax = uu___114_6558.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = uu___114_6558.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___114_6558.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___114_6558.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___114_6558.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___114_6558.FStar_TypeChecker_Env.qname_and_index})
in ((env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg);
(

let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

let uu____6561 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (uu____6561) with
| (ses, exports, env) -> begin
(((

let uu___115_6579 = modul
in {FStar_Syntax_Syntax.name = uu___115_6579.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = uu___115_6579.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___115_6579.FStar_Syntax_Syntax.is_interface})), (exports), (env))
end)));
))));
)))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let uu____6595 = (tc_decls env decls)
in (match (uu____6595) with
| (ses, exports, env) -> begin
(

let modul = (

let uu___116_6613 = modul
in {FStar_Syntax_Syntax.name = uu___116_6613.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = uu___116_6613.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___116_6613.FStar_Syntax_Syntax.is_interface})
in ((modul), (exports), (env)))
end)))


let check_exports : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env modul exports -> (

let env = (

let uu___117_6627 = env
in {FStar_TypeChecker_Env.solver = uu___117_6627.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___117_6627.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___117_6627.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___117_6627.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___117_6627.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___117_6627.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___117_6627.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___117_6627.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___117_6627.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___117_6627.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___117_6627.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___117_6627.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___117_6627.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = uu___117_6627.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___117_6627.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___117_6627.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___117_6627.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = true; FStar_TypeChecker_Env.type_of = uu___117_6627.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___117_6627.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___117_6627.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___117_6627.FStar_TypeChecker_Env.qname_and_index})
in (

let check_term = (fun lid univs t -> (

let uu____6638 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (uu____6638) with
| (univs, t) -> begin
((

let uu____6644 = (let _0_752 = (FStar_TypeChecker_Env.debug (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name))
in (FStar_All.pipe_left _0_752 (FStar_Options.Other ("Exports"))))
in (match (uu____6644) with
| true -> begin
(let _0_756 = (FStar_Syntax_Print.lid_to_string lid)
in (let _0_755 = (let _0_753 = (FStar_All.pipe_right univs (FStar_List.map (fun x -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (x))))))
in (FStar_All.pipe_right _0_753 (FStar_String.concat ", ")))
in (let _0_754 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print3 "Checking for export %s <%s> : %s\n" _0_756 _0_755 _0_754))))
end
| uu____6648 -> begin
()
end));
(

let env = (FStar_TypeChecker_Env.push_univ_vars env univs)
in (let _0_757 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env t)
in (FStar_All.pipe_right _0_757 Prims.ignore)));
)
end)))
in (

let check_term = (fun lid univs t -> ((FStar_Errors.message_prefix.FStar_Errors.set_prefix (let _0_759 = (FStar_Syntax_Print.lid_to_string modul.FStar_Syntax_Syntax.name)
in (let _0_758 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Interface of %s violates its abstraction (add a \'private\' qualifier to \'%s\'?)" _0_759 _0_758))));
(check_term lid univs t);
(FStar_Errors.message_prefix.FStar_Errors.clear_prefix ());
))
in (

let rec check_sigelt = (fun uu___93_6669 -> (match (uu___93_6669) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, uu____6672, uu____6673) -> begin
(

let uu____6680 = (not ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private))))
in (match (uu____6680) with
| true -> begin
(FStar_All.pipe_right ses (FStar_List.iter check_sigelt))
end
| uu____6683 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (l, univs, binders, typ, uu____6688, uu____6689, uu____6690, r) -> begin
(

let t = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((let _0_760 = (FStar_Syntax_Syntax.mk_Total typ)
in ((binders), (_0_760)))))) None r)
in (check_term l univs t))
end
| FStar_Syntax_Syntax.Sig_datacon (l, univs, t, uu____6712, uu____6713, uu____6714, uu____6715, uu____6716) -> begin
(check_term l univs t)
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, univs, t, quals, uu____6725) -> begin
(

let uu____6728 = (not ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private))))
in (match (uu____6728) with
| true -> begin
(check_term l univs t)
end
| uu____6730 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_let ((uu____6731, lbs), uu____6733, uu____6734, quals, uu____6736) -> begin
(

let uu____6748 = (not ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private))))
in (match (uu____6748) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (check_term fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp)))))
end
| uu____6757 -> begin
()
end))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, binders, comp, quals, flags, r) -> begin
(

let uu____6769 = (not ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private))))
in (match (uu____6769) with
| true -> begin
(

let arrow = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp))))) None r)
in (check_term l univs arrow))
end
| uu____6782 -> begin
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
| uu____6789 -> begin
(FStar_List.iter check_sigelt exports)
end))))))


let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (

let modul = (

let uu___118_6802 = modul
in {FStar_Syntax_Syntax.name = uu___118_6802.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = uu___118_6802.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module env modul)
in ((

let uu____6805 = (not ((FStar_Options.lax ())))
in (match (uu____6805) with
| true -> begin
(check_exports env modul exports)
end
| uu____6806 -> begin
()
end));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str));
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul);
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ());
(

let uu____6811 = (not ((FStar_Options.interactive ())))
in (match (uu____6811) with
| true -> begin
(let _0_761 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _0_761 Prims.ignore))
end
| uu____6812 -> begin
()
end));
((modul), (env));
))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let uu____6821 = (tc_partial_modul env modul)
in (match (uu____6821) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> ((

let uu____6842 = (FStar_Options.debug_any ())
in (match (uu____6842) with
| true -> begin
(let _0_762 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (match (m.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"i\'face"
end
| uu____6843 -> begin
"module"
end) _0_762))
end
| uu____6844 -> begin
()
end));
(

let env = (

let uu___119_6846 = env
in (let _0_763 = (not ((FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = uu___119_6846.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___119_6846.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___119_6846.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___119_6846.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___119_6846.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___119_6846.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___119_6846.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___119_6846.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___119_6846.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___119_6846.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___119_6846.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___119_6846.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___119_6846.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___119_6846.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___119_6846.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___119_6846.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___119_6846.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___119_6846.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _0_763; FStar_TypeChecker_Env.lax_universes = uu___119_6846.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___119_6846.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___119_6846.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___119_6846.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___119_6846.FStar_TypeChecker_Env.qname_and_index}))
in (

let uu____6847 = (tc_modul env m)
in (match (uu____6847) with
| (m, env) -> begin
((

let uu____6855 = (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____6855) with
| true -> begin
(let _0_764 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _0_764))
end
| uu____6856 -> begin
()
end));
(

let uu____6858 = ((FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) && (FStar_Options.debug_at_level m.FStar_Syntax_Syntax.name.FStar_Ident.str (FStar_Options.Other ("Normalize"))))
in (match (uu____6858) with
| true -> begin
(

let normalize_toplevel_lets = (fun uu___94_6862 -> (match (uu___94_6862) with
| FStar_Syntax_Syntax.Sig_let ((b, lbs), r, ids, qs, attrs) -> begin
(

let n = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]))
in (

let update = (fun lb -> (

let uu____6889 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____6889) with
| (univnames, e) -> begin
(

let uu___120_6894 = lb
in (let _0_766 = (let _0_765 = (FStar_TypeChecker_Env.push_univ_vars env univnames)
in (n _0_765 e))
in {FStar_Syntax_Syntax.lbname = uu___120_6894.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___120_6894.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___120_6894.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___120_6894.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _0_766}))
end)))
in FStar_Syntax_Syntax.Sig_let ((let _0_768 = (let _0_767 = (FStar_List.map update lbs)
in ((b), (_0_767)))
in ((_0_768), (r), (ids), (qs), (attrs))))))
end
| se -> begin
se
end))
in (

let normalized_module = (

let uu___121_6904 = m
in (let _0_769 = (FStar_List.map normalize_toplevel_lets m.FStar_Syntax_Syntax.declarations)
in {FStar_Syntax_Syntax.name = uu___121_6904.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _0_769; FStar_Syntax_Syntax.exports = uu___121_6904.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = uu___121_6904.FStar_Syntax_Syntax.is_interface}))
in (let _0_770 = (FStar_Syntax_Print.modul_to_string normalized_module)
in (FStar_Util.print1 "%s\n" _0_770))))
end
| uu____6905 -> begin
()
end));
((m), (env));
)
end)));
))




