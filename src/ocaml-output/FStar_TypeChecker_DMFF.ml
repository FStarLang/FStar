
open Prims
type env =
{env : FStar_TypeChecker_Env.env; subst : FStar_Syntax_Syntax.subst_elt Prims.list; tc_const : FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ}


let empty : FStar_TypeChecker_Env.env  ->  (FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ)  ->  env = (fun env tc_const -> {env = env; subst = []; tc_const = tc_const})


let gen_wps_for_free : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.sigelts * FStar_Syntax_Syntax.eff_decl) = (fun env binders a wp_a ed -> (

let wp_a = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env wp_a)
in (

let a = (

let uu___93_64 = a
in (let _0_159 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env a.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___93_64.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___93_64.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_159}))
in (

let d = (fun s -> (FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s))
in ((

let uu____70 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____70) with
| true -> begin
((d "Elaborating extra WP combinators");
(let _0_160 = (FStar_Syntax_Print.term_to_string wp_a)
in (FStar_Util.print1 "wp_a is: %s\n" _0_160));
)
end
| uu____72 -> begin
()
end));
(

let rec collect_binders = (fun t -> (

let uu____80 = (let _0_161 = (FStar_Syntax_Subst.compress t)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe _0_161)).FStar_Syntax_Syntax.n
in (match (uu____80) with
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let rest = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____102) -> begin
t
end
| uu____109 -> begin
(failwith "wp_a contains non-Tot arrow")
end)
in (let _0_162 = (collect_binders rest)
in (FStar_List.append bs _0_162)))
end
| FStar_Syntax_Syntax.Tm_type (uu____114) -> begin
[]
end
| uu____117 -> begin
(failwith "wp_a doesn\'t end in Type0")
end)))
in (

let mk_lid = (fun name -> (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" name))) FStar_Range.dummyRange))
in (

let gamma = (let _0_163 = (collect_binders wp_a)
in (FStar_All.pipe_right _0_163 FStar_Syntax_Util.name_binders))
in ((

let uu____136 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____136) with
| true -> begin
(d (let _0_164 = (FStar_Syntax_Print.binders_to_string ", " gamma)
in (FStar_Util.format1 "Gamma is %s\n" _0_164)))
end
| uu____137 -> begin
()
end));
(

let unknown = FStar_Syntax_Syntax.tun
in (

let mk = (fun x -> ((FStar_Syntax_Syntax.mk x) None FStar_Range.dummyRange))
in (

let sigelts = (FStar_Util.mk_ref [])
in (

let register = (fun env lident def -> (

let uu____168 = (FStar_TypeChecker_Util.mk_toplevel_definition env lident def)
in (match (uu____168) with
| (sigelt, fv) -> begin
((let _0_166 = (let _0_165 = (FStar_ST.read sigelts)
in (sigelt)::_0_165)
in (FStar_ST.write sigelts _0_166));
fv;
)
end)))
in (

let binders_of_list = (FStar_List.map (fun uu____193 -> (match (uu____193) with
| (t, b) -> begin
(let _0_167 = (FStar_Syntax_Syntax.as_implicit b)
in ((t), (_0_167)))
end)))
in (

let mk_all_implicit = (FStar_List.map (fun t -> (let _0_168 = (FStar_Syntax_Syntax.as_implicit true)
in (((Prims.fst t)), (_0_168)))))
in (

let args_of_binders = (FStar_List.map (fun bv -> (FStar_Syntax_Syntax.as_arg (FStar_Syntax_Syntax.bv_to_name (Prims.fst bv)))))
in (

let uu____228 = (

let uu____240 = (

let mk = (fun f -> (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let body = (let _0_169 = (f (FStar_Syntax_Syntax.bv_to_name t))
in (FStar_Syntax_Util.arrow gamma _0_169))
in (let _0_174 = (let _0_173 = (let _0_172 = (FStar_Syntax_Syntax.mk_binder a)
in (let _0_171 = (let _0_170 = (FStar_Syntax_Syntax.mk_binder t)
in (_0_170)::[])
in (_0_172)::_0_171))
in (FStar_List.append binders _0_173))
in (FStar_Syntax_Util.abs _0_174 body None)))))
in (let _0_176 = (mk FStar_Syntax_Syntax.mk_Total)
in (let _0_175 = (mk FStar_Syntax_Syntax.mk_GTotal)
in ((_0_176), (_0_175)))))
in (match (uu____240) with
| (ctx_def, gctx_def) -> begin
(

let ctx_lid = (mk_lid "ctx")
in (

let ctx_fv = (register env ctx_lid ctx_def)
in (

let gctx_lid = (mk_lid "gctx")
in (

let gctx_fv = (register env gctx_lid gctx_def)
in (

let mk_app = (fun fv t -> (mk (FStar_Syntax_Syntax.Tm_app ((let _0_187 = (let _0_186 = (FStar_List.map (fun uu____308 -> (match (uu____308) with
| (bv, uu____314) -> begin
(let _0_178 = (FStar_Syntax_Syntax.bv_to_name bv)
in (let _0_177 = (FStar_Syntax_Syntax.as_implicit false)
in ((_0_178), (_0_177))))
end)) binders)
in (let _0_185 = (let _0_184 = (let _0_180 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _0_179 = (FStar_Syntax_Syntax.as_implicit false)
in ((_0_180), (_0_179))))
in (let _0_183 = (let _0_182 = (let _0_181 = (FStar_Syntax_Syntax.as_implicit false)
in ((t), (_0_181)))
in (_0_182)::[])
in (_0_184)::_0_183))
in (FStar_List.append _0_186 _0_185)))
in ((fv), (_0_187)))))))
in ((env), ((mk_app ctx_fv)), ((mk_app gctx_fv))))))))
end))
in (match (uu____228) with
| (env, mk_ctx, mk_gctx) -> begin
(

let c_pure = (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let x = (let _0_188 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" None _0_188))
in (

let ret = Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp (FStar_Syntax_Syntax.mk_Total (mk_ctx (FStar_Syntax_Syntax.bv_to_name t))))))
in (

let body = (let _0_189 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs gamma _0_189 ret))
in (let _0_192 = (let _0_191 = (mk_all_implicit binders)
in (let _0_190 = (binders_of_list ((((a), (true)))::(((t), (true)))::(((x), (false)))::[]))
in (FStar_List.append _0_191 _0_190)))
in (FStar_Syntax_Util.abs _0_192 body ret))))))
in (

let c_pure = (let _0_193 = (mk_lid "pure")
in (register env _0_193 c_pure))
in (

let c_app = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let l = (let _0_198 = (mk_gctx (let _0_197 = (let _0_195 = (FStar_Syntax_Syntax.mk_binder (let _0_194 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv None _0_194)))
in (_0_195)::[])
in (let _0_196 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Syntax.bv_to_name t2))
in (FStar_Syntax_Util.arrow _0_197 _0_196))))
in (FStar_Syntax_Syntax.gen_bv "l" None _0_198))
in (

let r = (let _0_199 = (mk_gctx (FStar_Syntax_Syntax.bv_to_name t1))
in (FStar_Syntax_Syntax.gen_bv "r" None _0_199))
in (

let ret = Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp (FStar_Syntax_Syntax.mk_Total (mk_gctx (FStar_Syntax_Syntax.bv_to_name t2))))))
in (

let outer_body = (

let gamma_as_args = (args_of_binders gamma)
in (

let inner_body = (let _0_204 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _0_203 = (let _0_202 = (let _0_201 = (FStar_Syntax_Syntax.as_arg (let _0_200 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app _0_200 gamma_as_args)))
in (_0_201)::[])
in (FStar_List.append gamma_as_args _0_202))
in (FStar_Syntax_Util.mk_app _0_204 _0_203)))
in (FStar_Syntax_Util.abs gamma inner_body ret)))
in (let _0_207 = (let _0_206 = (mk_all_implicit binders)
in (let _0_205 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((l), (false)))::(((r), (false)))::[]))
in (FStar_List.append _0_206 _0_205)))
in (FStar_Syntax_Util.abs _0_207 outer_body ret))))))))
in (

let c_app = (let _0_208 = (mk_lid "app")
in (register env _0_208 c_app))
in (

let c_lift1 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _0_211 = (let _0_209 = (FStar_Syntax_Syntax.null_binder (FStar_Syntax_Syntax.bv_to_name t1))
in (_0_209)::[])
in (let _0_210 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Syntax.bv_to_name t2))
in (FStar_Syntax_Util.arrow _0_211 _0_210)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _0_212 = (mk_gctx (FStar_Syntax_Syntax.bv_to_name t1))
in (FStar_Syntax_Syntax.gen_bv "a1" None _0_212))
in (

let ret = Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp (FStar_Syntax_Syntax.mk_Total (mk_gctx (FStar_Syntax_Syntax.bv_to_name t2))))))
in (let _0_224 = (let _0_214 = (mk_all_implicit binders)
in (let _0_213 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::(((a1), (false)))::[]))
in (FStar_List.append _0_214 _0_213)))
in (let _0_223 = (let _0_222 = (let _0_221 = (let _0_220 = (let _0_217 = (let _0_216 = (let _0_215 = (FStar_Syntax_Syntax.bv_to_name f)
in (_0_215)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _0_216))
in (FStar_Syntax_Util.mk_app c_pure _0_217))
in (let _0_219 = (let _0_218 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_0_218)::[])
in (_0_220)::_0_219))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _0_221))
in (FStar_Syntax_Util.mk_app c_app _0_222))
in (FStar_Syntax_Util.abs _0_224 _0_223 ret)))))))))
in (

let c_lift1 = (let _0_225 = (mk_lid "lift1")
in (register env _0_225 c_lift1))
in (

let c_lift2 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t3 = (FStar_Syntax_Syntax.gen_bv "t3" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _0_230 = (let _0_228 = (FStar_Syntax_Syntax.null_binder (FStar_Syntax_Syntax.bv_to_name t1))
in (let _0_227 = (let _0_226 = (FStar_Syntax_Syntax.null_binder (FStar_Syntax_Syntax.bv_to_name t2))
in (_0_226)::[])
in (_0_228)::_0_227))
in (let _0_229 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Syntax.bv_to_name t3))
in (FStar_Syntax_Util.arrow _0_230 _0_229)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _0_231 = (mk_gctx (FStar_Syntax_Syntax.bv_to_name t1))
in (FStar_Syntax_Syntax.gen_bv "a1" None _0_231))
in (

let a2 = (let _0_232 = (mk_gctx (FStar_Syntax_Syntax.bv_to_name t2))
in (FStar_Syntax_Syntax.gen_bv "a2" None _0_232))
in (

let ret = Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp (FStar_Syntax_Syntax.mk_Total (mk_gctx (FStar_Syntax_Syntax.bv_to_name t3))))))
in (let _0_249 = (let _0_234 = (mk_all_implicit binders)
in (let _0_233 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((t3), (true)))::(((f), (false)))::(((a1), (false)))::(((a2), (false)))::[]))
in (FStar_List.append _0_234 _0_233)))
in (let _0_248 = (let _0_247 = (let _0_246 = (let _0_245 = (let _0_242 = (let _0_241 = (let _0_240 = (let _0_237 = (let _0_236 = (let _0_235 = (FStar_Syntax_Syntax.bv_to_name f)
in (_0_235)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _0_236))
in (FStar_Syntax_Util.mk_app c_pure _0_237))
in (let _0_239 = (let _0_238 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_0_238)::[])
in (_0_240)::_0_239))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _0_241))
in (FStar_Syntax_Util.mk_app c_app _0_242))
in (let _0_244 = (let _0_243 = (FStar_Syntax_Syntax.bv_to_name a2)
in (_0_243)::[])
in (_0_245)::_0_244))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _0_246))
in (FStar_Syntax_Util.mk_app c_app _0_247))
in (FStar_Syntax_Util.abs _0_249 _0_248 ret)))))))))))
in (

let c_lift2 = (let _0_250 = (mk_lid "lift2")
in (register env _0_250 c_lift2))
in (

let c_push = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _0_253 = (let _0_251 = (FStar_Syntax_Syntax.null_binder (FStar_Syntax_Syntax.bv_to_name t1))
in (_0_251)::[])
in (let _0_252 = (FStar_Syntax_Syntax.mk_Total (mk_gctx (FStar_Syntax_Syntax.bv_to_name t2)))
in (FStar_Syntax_Util.arrow _0_253 _0_252)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let ret = Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp (FStar_Syntax_Syntax.mk_Total (mk_ctx (let _0_256 = (let _0_254 = (FStar_Syntax_Syntax.null_binder (FStar_Syntax_Syntax.bv_to_name t1))
in (_0_254)::[])
in (let _0_255 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Syntax.bv_to_name t2))
in (FStar_Syntax_Util.arrow _0_256 _0_255))))))))
in (

let e1 = (let _0_257 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" None _0_257))
in (

let body = (let _0_265 = (let _0_259 = (let _0_258 = (FStar_Syntax_Syntax.mk_binder e1)
in (_0_258)::[])
in (FStar_List.append gamma _0_259))
in (let _0_264 = (let _0_263 = (FStar_Syntax_Syntax.bv_to_name f)
in (let _0_262 = (let _0_261 = (FStar_Syntax_Syntax.as_arg (FStar_Syntax_Syntax.bv_to_name e1))
in (let _0_260 = (args_of_binders gamma)
in (_0_261)::_0_260))
in (FStar_Syntax_Util.mk_app _0_263 _0_262)))
in (FStar_Syntax_Util.abs _0_265 _0_264 ret)))
in (let _0_268 = (let _0_267 = (mk_all_implicit binders)
in (let _0_266 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::[]))
in (FStar_List.append _0_267 _0_266)))
in (FStar_Syntax_Util.abs _0_268 body ret)))))))))
in (

let c_push = (let _0_269 = (mk_lid "push")
in (register env _0_269 c_push))
in (

let ret_tot_wp_a = Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp (FStar_Syntax_Syntax.mk_Total wp_a))))
in (

let mk_generic_app = (fun c -> (match (((FStar_List.length binders) > (Prims.parse_int "0"))) with
| true -> begin
(mk (FStar_Syntax_Syntax.Tm_app ((let _0_270 = (args_of_binders binders)
in ((c), (_0_270))))))
end
| uu____583 -> begin
c
end))
in (

let wp_if_then_else = (

let result_comp = (FStar_Syntax_Syntax.mk_Total (let _0_275 = (let _0_273 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _0_272 = (let _0_271 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_0_271)::[])
in (_0_273)::_0_272))
in (let _0_274 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _0_275 _0_274))))
in (

let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (let _0_284 = (let _0_276 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (FStar_List.append binders _0_276))
in (let _0_283 = (

let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "2"))) None)
in (let _0_282 = (let _0_281 = (let _0_280 = (let _0_279 = (let _0_278 = (let _0_277 = (FStar_Syntax_Syntax.as_arg (FStar_Syntax_Syntax.bv_to_name c))
in (_0_277)::[])
in (FStar_Syntax_Util.mk_app l_ite _0_278))
in (_0_279)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _0_280))
in (FStar_Syntax_Util.mk_app c_lift2 _0_281))
in (FStar_Syntax_Util.ascribe _0_282 (FStar_Util.Inr (result_comp)))))
in (FStar_Syntax_Util.abs _0_284 _0_283 (Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp result_comp)))))))))
in (

let wp_if_then_else = (let _0_285 = (mk_lid "wp_if_then_else")
in (register env _0_285 wp_if_then_else))
in (

let wp_if_then_else = (mk_generic_app wp_if_then_else)
in (

let wp_assert = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_and = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.and_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (

let body = (let _0_295 = (let _0_294 = (let _0_293 = (let _0_290 = (let _0_289 = (let _0_288 = (let _0_287 = (let _0_286 = (FStar_Syntax_Syntax.as_arg (FStar_Syntax_Syntax.bv_to_name q))
in (_0_286)::[])
in (FStar_Syntax_Util.mk_app l_and _0_287))
in (_0_288)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _0_289))
in (FStar_Syntax_Util.mk_app c_pure _0_290))
in (let _0_292 = (let _0_291 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_0_291)::[])
in (_0_293)::_0_292))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _0_294))
in (FStar_Syntax_Util.mk_app c_app _0_295))
in (let _0_297 = (let _0_296 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders _0_296))
in (FStar_Syntax_Util.abs _0_297 body ret_tot_wp_a))))))
in (

let wp_assert = (let _0_298 = (mk_lid "wp_assert")
in (register env _0_298 wp_assert))
in (

let wp_assert = (mk_generic_app wp_assert)
in (

let wp_assume = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_imp = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.imp_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (

let body = (let _0_308 = (let _0_307 = (let _0_306 = (let _0_303 = (let _0_302 = (let _0_301 = (let _0_300 = (let _0_299 = (FStar_Syntax_Syntax.as_arg (FStar_Syntax_Syntax.bv_to_name q))
in (_0_299)::[])
in (FStar_Syntax_Util.mk_app l_imp _0_300))
in (_0_301)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _0_302))
in (FStar_Syntax_Util.mk_app c_pure _0_303))
in (let _0_305 = (let _0_304 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_0_304)::[])
in (_0_306)::_0_305))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _0_307))
in (FStar_Syntax_Util.mk_app c_app _0_308))
in (let _0_310 = (let _0_309 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders _0_309))
in (FStar_Syntax_Util.abs _0_310 body ret_tot_wp_a))))))
in (

let wp_assume = (let _0_311 = (mk_lid "wp_assume")
in (register env _0_311 wp_assume))
in (

let wp_assume = (mk_generic_app wp_assume)
in (

let wp_close = (

let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _0_314 = (let _0_312 = (FStar_Syntax_Syntax.null_binder (FStar_Syntax_Syntax.bv_to_name b))
in (_0_312)::[])
in (let _0_313 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _0_314 _0_313)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let body = (let _0_323 = (let _0_322 = (let _0_321 = (let _0_315 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((FStar_Syntax_Util.tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure _0_315))
in (let _0_320 = (let _0_319 = (let _0_318 = (let _0_317 = (let _0_316 = (FStar_Syntax_Syntax.bv_to_name f)
in (_0_316)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _0_317))
in (FStar_Syntax_Util.mk_app c_push _0_318))
in (_0_319)::[])
in (_0_321)::_0_320))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _0_322))
in (FStar_Syntax_Util.mk_app c_app _0_323))
in (let _0_325 = (let _0_324 = (FStar_Syntax_Syntax.binders_of_list ((a)::(b)::(f)::[]))
in (FStar_List.append binders _0_324))
in (FStar_Syntax_Util.abs _0_325 body ret_tot_wp_a))))))
in (

let wp_close = (let _0_326 = (mk_lid "wp_close")
in (register env _0_326 wp_close))
in (

let wp_close = (mk_generic_app wp_close)
in (

let ret_tot_type = Some (FStar_Util.Inl ((let _0_327 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _0_327))))
in (

let ret_gtot_type = Some (FStar_Util.Inl ((let _0_328 = (FStar_Syntax_Syntax.mk_GTotal FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _0_328))))
in (

let mk_forall = (fun x body -> ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_332 = (let _0_331 = (FStar_Syntax_Syntax.as_arg (let _0_330 = (let _0_329 = (FStar_Syntax_Syntax.mk_binder x)
in (_0_329)::[])
in (FStar_Syntax_Util.abs _0_330 body ret_tot_type)))
in (_0_331)::[])
in ((FStar_Syntax_Util.tforall), (_0_332)))))) None FStar_Range.dummyRange))
in (

let rec is_discrete = (fun t -> (

let uu____723 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____723) with
| FStar_Syntax_Syntax.Tm_type (uu____724) -> begin
false
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((FStar_List.for_all (fun uu____739 -> (match (uu____739) with
| (b, uu____743) -> begin
(is_discrete b.FStar_Syntax_Syntax.sort)
end)) bs) && (is_discrete (FStar_Syntax_Util.comp_result c)))
end
| uu____744 -> begin
true
end)))
in (

let rec is_monotonic = (fun t -> (

let uu____749 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____749) with
| FStar_Syntax_Syntax.Tm_type (uu____750) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((FStar_List.for_all (fun uu____765 -> (match (uu____765) with
| (b, uu____769) -> begin
(is_discrete b.FStar_Syntax_Syntax.sort)
end)) bs) && (is_monotonic (FStar_Syntax_Util.comp_result c)))
end
| uu____770 -> begin
(is_discrete t)
end)))
in (

let rec mk_rel = (fun rel t x y -> (

let mk_rel = (mk_rel rel)
in (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (

let uu____822 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____822) with
| FStar_Syntax_Syntax.Tm_type (uu____823) -> begin
(rel x y)
end
| (FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(

let a = (Prims.fst binder).FStar_Syntax_Syntax.sort
in (

let uu____869 = ((is_monotonic a) || (is_monotonic b))
in (match (uu____869) with
| true -> begin
(

let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (

let body = (let _0_338 = (let _0_334 = (let _0_333 = (FStar_Syntax_Syntax.as_arg (FStar_Syntax_Syntax.bv_to_name a1))
in (_0_333)::[])
in (FStar_Syntax_Util.mk_app x _0_334))
in (let _0_337 = (let _0_336 = (let _0_335 = (FStar_Syntax_Syntax.as_arg (FStar_Syntax_Syntax.bv_to_name a1))
in (_0_335)::[])
in (FStar_Syntax_Util.mk_app y _0_336))
in (mk_rel b _0_338 _0_337)))
in (mk_forall a1 body)))
end
| uu____872 -> begin
(

let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (

let a2 = (FStar_Syntax_Syntax.gen_bv "a2" None a)
in (

let body = (let _0_348 = (let _0_340 = (FStar_Syntax_Syntax.bv_to_name a1)
in (let _0_339 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_rel a _0_340 _0_339)))
in (let _0_347 = (let _0_346 = (let _0_342 = (let _0_341 = (FStar_Syntax_Syntax.as_arg (FStar_Syntax_Syntax.bv_to_name a1))
in (_0_341)::[])
in (FStar_Syntax_Util.mk_app x _0_342))
in (let _0_345 = (let _0_344 = (let _0_343 = (FStar_Syntax_Syntax.as_arg (FStar_Syntax_Syntax.bv_to_name a2))
in (_0_343)::[])
in (FStar_Syntax_Util.mk_app y _0_344))
in (mk_rel b _0_346 _0_345)))
in (FStar_Syntax_Util.mk_imp _0_348 _0_347)))
in (let _0_349 = (mk_forall a2 body)
in (mk_forall a1 _0_349)))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::binders, comp) -> begin
(

let t = (

let uu___94_896 = t
in (let _0_351 = FStar_Syntax_Syntax.Tm_arrow ((let _0_350 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.arrow binders comp))
in (((binder)::[]), (_0_350))))
in {FStar_Syntax_Syntax.n = _0_351; FStar_Syntax_Syntax.tk = uu___94_896.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___94_896.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___94_896.FStar_Syntax_Syntax.vars}))
in (mk_rel t x y))
end
| FStar_Syntax_Syntax.Tm_arrow (uu____908) -> begin
(failwith "unhandled arrow")
end
| uu____916 -> begin
(FStar_Syntax_Util.mk_eq t t x y)
end)))))
in (

let stronger = (

let wp1 = (FStar_Syntax_Syntax.gen_bv "wp1" None wp_a)
in (

let wp2 = (FStar_Syntax_Syntax.gen_bv "wp2" None wp_a)
in (

let rec mk_stronger = (fun t x y -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (

let uu____931 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____931) with
| FStar_Syntax_Syntax.Tm_type (uu____932) -> begin
(FStar_Syntax_Util.mk_imp x y)
end
| FStar_Syntax_Syntax.Tm_app (head, args) when (FStar_Syntax_Util.is_tuple_constructor (FStar_Syntax_Subst.compress head)) -> begin
(

let project = (fun i tuple -> (

let projector = (let _0_353 = (let _0_352 = (FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) FStar_Range.dummyRange)
in (FStar_TypeChecker_Env.lookup_projector env _0_352 i))
in (FStar_Syntax_Syntax.fvar _0_353 (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None))
in (FStar_Syntax_Util.mk_app projector ((((tuple), (None)))::[]))))
in (

let uu____983 = (

let uu____987 = (FStar_List.mapi (fun i uu____992 -> (match (uu____992) with
| (t, q) -> begin
(let _0_355 = (project i x)
in (let _0_354 = (project i y)
in (mk_stronger t _0_355 _0_354)))
end)) args)
in (match (uu____987) with
| [] -> begin
(failwith "Impossible : Empty application when creating stronger relation in DM4F")
end
| (rel0)::rels -> begin
((rel0), (rels))
end))
in (match (uu____983) with
| (rel0, rels) -> begin
(FStar_List.fold_left FStar_Syntax_Util.mk_conj rel0 rels)
end)))
end
| (FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(

let bvs = (FStar_List.mapi (fun i uu____1052 -> (match (uu____1052) with
| (bv, q) -> begin
(let _0_357 = (let _0_356 = (FStar_Util.string_of_int i)
in (Prims.strcat "a" _0_356))
in (FStar_Syntax_Syntax.gen_bv _0_357 None bv.FStar_Syntax_Syntax.sort))
end)) binders)
in (

let args = (FStar_List.map (fun ai -> (FStar_Syntax_Syntax.as_arg (FStar_Syntax_Syntax.bv_to_name ai))) bvs)
in (

let body = (let _0_359 = (FStar_Syntax_Util.mk_app x args)
in (let _0_358 = (FStar_Syntax_Util.mk_app y args)
in (mk_stronger b _0_359 _0_358)))
in (FStar_List.fold_right (fun bv body -> (mk_forall bv body)) bvs body))))
end
| uu____1063 -> begin
(failwith "Not a DM elaborated type")
end))))
in (

let body = (let _0_362 = (FStar_Syntax_Util.unascribe wp_a)
in (let _0_361 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (let _0_360 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_stronger _0_362 _0_361 _0_360))))
in (let _0_364 = (let _0_363 = (binders_of_list ((((a), (false)))::(((wp1), (false)))::(((wp2), (false)))::[]))
in (FStar_List.append binders _0_363))
in (FStar_Syntax_Util.abs _0_364 body ret_tot_type))))))
in (

let stronger = (let _0_365 = (mk_lid "stronger")
in (register env _0_365 stronger))
in (

let stronger = (mk_generic_app stronger)
in (

let wp_ite = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let uu____1081 = (FStar_Util.prefix gamma)
in (match (uu____1081) with
| (wp_args, post) -> begin
(

let k = (FStar_Syntax_Syntax.gen_bv "k" None (Prims.fst post).FStar_Syntax_Syntax.sort)
in (

let equiv = (

let k_tm = (FStar_Syntax_Syntax.bv_to_name k)
in (

let eq = (let _0_366 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst post))
in (mk_rel FStar_Syntax_Util.mk_iff k.FStar_Syntax_Syntax.sort k_tm _0_366))
in (

let uu____1107 = (FStar_Syntax_Util.destruct_typ_as_formula eq)
in (match (uu____1107) with
| Some (FStar_Syntax_Util.QAll (binders, [], body)) -> begin
(

let k_app = (let _0_367 = (args_of_binders binders)
in (FStar_Syntax_Util.mk_app k_tm _0_367))
in (

let guard_free = (FStar_Syntax_Syntax.fv_to_tm (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.guard_free FStar_Syntax_Syntax.Delta_constant None))
in (

let pat = (let _0_369 = (let _0_368 = (FStar_Syntax_Syntax.as_arg k_app)
in (_0_368)::[])
in (FStar_Syntax_Util.mk_app guard_free _0_369))
in (

let pattern_guarded_body = (mk (FStar_Syntax_Syntax.Tm_meta ((let _0_372 = FStar_Syntax_Syntax.Meta_pattern ((let _0_371 = (let _0_370 = (FStar_Syntax_Syntax.as_arg pat)
in (_0_370)::[])
in (_0_371)::[]))
in ((body), (_0_372))))))
in (FStar_Syntax_Util.close_forall binders pattern_guarded_body)))))
end
| uu____1124 -> begin
(failwith "Impossible: Expected the equivalence to be a quantified formula")
end))))
in (

let body = (let _0_380 = (let _0_379 = (let _0_378 = (let _0_377 = (FStar_Syntax_Syntax.bv_to_name wp)
in (let _0_376 = (let _0_375 = (args_of_binders wp_args)
in (let _0_374 = (let _0_373 = (FStar_Syntax_Syntax.as_arg (FStar_Syntax_Syntax.bv_to_name k))
in (_0_373)::[])
in (FStar_List.append _0_375 _0_374)))
in (FStar_Syntax_Util.mk_app _0_377 _0_376)))
in (FStar_Syntax_Util.mk_imp equiv _0_378))
in (FStar_Syntax_Util.mk_forall k _0_379))
in (FStar_Syntax_Util.abs gamma _0_380 ret_gtot_type))
in (let _0_382 = (let _0_381 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders _0_381))
in (FStar_Syntax_Util.abs _0_382 body ret_gtot_type)))))
end)))
in (

let wp_ite = (let _0_383 = (mk_lid "wp_ite")
in (register env _0_383 wp_ite))
in (

let wp_ite = (mk_generic_app wp_ite)
in (

let null_wp = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let uu____1135 = (FStar_Util.prefix gamma)
in (match (uu____1135) with
| (wp_args, post) -> begin
(

let x = (FStar_Syntax_Syntax.gen_bv "x" None FStar_Syntax_Syntax.tun)
in (

let body = (let _0_387 = (let _0_386 = (FStar_All.pipe_left FStar_Syntax_Syntax.bv_to_name (Prims.fst post))
in (let _0_385 = (let _0_384 = (FStar_Syntax_Syntax.as_arg (FStar_Syntax_Syntax.bv_to_name x))
in (_0_384)::[])
in (FStar_Syntax_Util.mk_app _0_386 _0_385)))
in (FStar_Syntax_Util.mk_forall x _0_387))
in (let _0_390 = (let _0_389 = (let _0_388 = (FStar_Syntax_Syntax.binders_of_list ((a)::[]))
in (FStar_List.append _0_388 gamma))
in (FStar_List.append binders _0_389))
in (FStar_Syntax_Util.abs _0_390 body ret_gtot_type))))
end)))
in (

let null_wp = (let _0_391 = (mk_lid "null_wp")
in (register env _0_391 null_wp))
in (

let null_wp = (mk_generic_app null_wp)
in (

let wp_trivial = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let body = (let _0_400 = (let _0_399 = (let _0_398 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _0_397 = (let _0_396 = (let _0_393 = (let _0_392 = (FStar_Syntax_Syntax.as_arg (FStar_Syntax_Syntax.bv_to_name a))
in (_0_392)::[])
in (FStar_Syntax_Util.mk_app null_wp _0_393))
in (let _0_395 = (let _0_394 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_0_394)::[])
in (_0_396)::_0_395))
in (_0_398)::_0_397))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _0_399))
in (FStar_Syntax_Util.mk_app stronger _0_400))
in (let _0_402 = (let _0_401 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders _0_401))
in (FStar_Syntax_Util.abs _0_402 body ret_tot_type))))
in (

let wp_trivial = (let _0_403 = (mk_lid "wp_trivial")
in (register env _0_403 wp_trivial))
in (

let wp_trivial = (mk_generic_app wp_trivial)
in ((

let uu____1183 = (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED")))
in (match (uu____1183) with
| true -> begin
(d "End Dijkstra monads for free")
end
| uu____1184 -> begin
()
end));
(

let c = (FStar_Syntax_Subst.close binders)
in (let _0_421 = (FStar_List.rev (FStar_ST.read sigelts))
in (let _0_420 = (

let uu___95_1192 = ed
in (let _0_419 = (let _0_404 = (c wp_if_then_else)
in (([]), (_0_404)))
in (let _0_418 = (let _0_405 = (c wp_ite)
in (([]), (_0_405)))
in (let _0_417 = (let _0_406 = (c stronger)
in (([]), (_0_406)))
in (let _0_416 = (let _0_407 = (c wp_close)
in (([]), (_0_407)))
in (let _0_415 = (let _0_408 = (c wp_assert)
in (([]), (_0_408)))
in (let _0_414 = (let _0_409 = (c wp_assume)
in (([]), (_0_409)))
in (let _0_413 = (let _0_410 = (c null_wp)
in (([]), (_0_410)))
in (let _0_412 = (let _0_411 = (c wp_trivial)
in (([]), (_0_411)))
in {FStar_Syntax_Syntax.qualifiers = uu___95_1192.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = uu___95_1192.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___95_1192.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = uu___95_1192.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = uu___95_1192.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = uu___95_1192.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = uu___95_1192.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = uu___95_1192.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _0_419; FStar_Syntax_Syntax.ite_wp = _0_418; FStar_Syntax_Syntax.stronger = _0_417; FStar_Syntax_Syntax.close_wp = _0_416; FStar_Syntax_Syntax.assert_p = _0_415; FStar_Syntax_Syntax.assume_p = _0_414; FStar_Syntax_Syntax.null_wp = _0_413; FStar_Syntax_Syntax.trivial = _0_412; FStar_Syntax_Syntax.repr = uu___95_1192.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = uu___95_1192.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = uu___95_1192.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = uu___95_1192.FStar_Syntax_Syntax.actions})))))))))
in ((_0_421), (_0_420)))));
)))))))))))))))))))))))))))))))))))))))))))
end)))))))));
))));
)))))


type env_ =
env


let get_env : env  ->  FStar_TypeChecker_Env.env = (fun env -> env.env)

type nm =
| N of FStar_Syntax_Syntax.typ
| M of FStar_Syntax_Syntax.typ


let uu___is_N : nm  ->  Prims.bool = (fun projectee -> (match (projectee) with
| N (_0) -> begin
true
end
| uu____1214 -> begin
false
end))


let __proj__N__item___0 : nm  ->  FStar_Syntax_Syntax.typ = (fun projectee -> (match (projectee) with
| N (_0) -> begin
_0
end))


let uu___is_M : nm  ->  Prims.bool = (fun projectee -> (match (projectee) with
| M (_0) -> begin
true
end
| uu____1226 -> begin
false
end))


let __proj__M__item___0 : nm  ->  FStar_Syntax_Syntax.typ = (fun projectee -> (match (projectee) with
| M (_0) -> begin
_0
end))


type nm_ =
nm


let nm_of_comp : FStar_Syntax_Syntax.comp'  ->  nm = (fun uu___82_1236 -> (match (uu___82_1236) with
| FStar_Syntax_Syntax.Total (t, uu____1238) -> begin
N (t)
end
| FStar_Syntax_Syntax.Comp (c) when (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___81_1247 -> (match (uu___81_1247) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| uu____1248 -> begin
false
end)))) -> begin
M (c.FStar_Syntax_Syntax.result_typ)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(failwith (let _0_423 = (let _0_422 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _0_422))
in (FStar_Util.format1 "[nm_of_comp]: impossible (%s)" _0_423)))
end
| FStar_Syntax_Syntax.GTotal (uu____1250) -> begin
(failwith "[nm_of_comp]: impossible (GTot)")
end))


let string_of_nm : nm  ->  Prims.string = (fun uu___83_1258 -> (match (uu___83_1258) with
| N (t) -> begin
(let _0_424 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "N[%s]" _0_424))
end
| M (t) -> begin
(let _0_425 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "M[%s]" _0_425))
end))


let is_monadic_arrow : FStar_Syntax_Syntax.term'  ->  nm = (fun n -> (match (n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1264, {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = uu____1266; FStar_Syntax_Syntax.pos = uu____1267; FStar_Syntax_Syntax.vars = uu____1268}) -> begin
(nm_of_comp n)
end
| uu____1279 -> begin
(failwith "unexpected_argument: [is_monadic_arrow]")
end))


let is_monadic_comp = (fun c -> (

let uu____1291 = (nm_of_comp c.FStar_Syntax_Syntax.n)
in (match (uu____1291) with
| M (uu____1292) -> begin
true
end
| N (uu____1293) -> begin
false
end)))

exception Not_found


let uu___is_Not_found : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not_found -> begin
true
end
| uu____1297 -> begin
false
end))


let double_star : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun typ -> (

let star_once = (fun typ -> (let _0_429 = (let _0_427 = (let _0_426 = (FStar_Syntax_Syntax.new_bv None typ)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _0_426))
in (_0_427)::[])
in (let _0_428 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _0_429 _0_428))))
in (let _0_430 = (FStar_All.pipe_right typ star_once)
in (FStar_All.pipe_left star_once _0_430))))


let rec mk_star_to_type : (FStar_Syntax_Syntax.term'  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun mk env a -> (mk (FStar_Syntax_Syntax.Tm_arrow ((let _0_435 = (let _0_433 = (let _0_432 = (FStar_Syntax_Syntax.null_bv (star_type' env a))
in (let _0_431 = (FStar_Syntax_Syntax.as_implicit false)
in ((_0_432), (_0_431))))
in (_0_433)::[])
in (let _0_434 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_0_435), (_0_434))))))))
and star_type' : env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let mk = (fun x -> ((FStar_Syntax_Syntax.mk x) None t.FStar_Syntax_Syntax.pos))
in (

let mk_star_to_type = (mk_star_to_type mk)
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____1377) -> begin
(

let binders = (FStar_List.map (fun uu____1396 -> (match (uu____1396) with
| (bv, aqual) -> begin
(let _0_437 = (

let uu___96_1403 = bv
in (let _0_436 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___96_1403.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___96_1403.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_436}))
in ((_0_437), (aqual)))
end)) binders)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1404, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (hn, uu____1406); FStar_Syntax_Syntax.tk = uu____1407; FStar_Syntax_Syntax.pos = uu____1408; FStar_Syntax_Syntax.vars = uu____1409}) -> begin
(mk (FStar_Syntax_Syntax.Tm_arrow ((let _0_438 = (FStar_Syntax_Syntax.mk_GTotal (star_type' env hn))
in ((binders), (_0_438))))))
end
| uu____1429 -> begin
(

let uu____1430 = (is_monadic_arrow t.FStar_Syntax_Syntax.n)
in (match (uu____1430) with
| N (hn) -> begin
(mk (FStar_Syntax_Syntax.Tm_arrow ((let _0_439 = (FStar_Syntax_Syntax.mk_Total (star_type' env hn))
in ((binders), (_0_439))))))
end
| M (a) -> begin
(mk (FStar_Syntax_Syntax.Tm_arrow ((let _0_445 = (let _0_443 = (let _0_442 = (let _0_441 = (FStar_Syntax_Syntax.null_bv (mk_star_to_type env a))
in (let _0_440 = (FStar_Syntax_Syntax.as_implicit false)
in ((_0_441), (_0_440))))
in (_0_442)::[])
in (FStar_List.append binders _0_443))
in (let _0_444 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_0_445), (_0_444)))))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let debug = (fun t s -> (

let string_of_set = (fun f s -> (

let elts = (FStar_Util.set_elements s)
in (match (elts) with
| [] -> begin
"{}"
end
| (x)::xs -> begin
(

let strb = (FStar_Util.new_string_builder ())
in ((FStar_Util.string_builder_append strb "{");
(let _0_446 = (f x)
in (FStar_Util.string_builder_append strb _0_446));
(FStar_List.iter (fun x -> ((FStar_Util.string_builder_append strb ", ");
(let _0_447 = (f x)
in (FStar_Util.string_builder_append strb _0_447));
)) xs);
(FStar_Util.string_builder_append strb "}");
(FStar_Util.string_of_string_builder strb);
))
end)))
in (let _0_449 = (FStar_Syntax_Print.term_to_string t)
in (let _0_448 = (string_of_set FStar_Syntax_Print.bv_to_string s)
in (FStar_Util.print2_warning "Dependency found in term %s : %s" _0_449 _0_448)))))
in (

let rec is_non_dependent_arrow = (fun ty n -> (

let uu____1503 = (FStar_Syntax_Subst.compress ty).FStar_Syntax_Syntax.n
in (match (uu____1503) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____1516 = (not ((FStar_Syntax_Util.is_tot_or_gtot_comp c)))
in (match (uu____1516) with
| true -> begin
false
end
| uu____1517 -> begin
try
(match (()) with
| () -> begin
(

let non_dependent_or_raise = (fun s ty -> (

let sinter = (let _0_450 = (FStar_Syntax_Free.names ty)
in (FStar_Util.set_intersect _0_450 s))
in (

let uu____1530 = (not ((FStar_Util.set_is_empty sinter)))
in (match (uu____1530) with
| true -> begin
((debug ty sinter);
(Prims.raise Not_found);
)
end
| uu____1532 -> begin
()
end))))
in (

let uu____1533 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____1533) with
| (binders, c) -> begin
(

let s = (FStar_List.fold_left (fun s uu____1544 -> (match (uu____1544) with
| (bv, uu____1550) -> begin
((non_dependent_or_raise s bv.FStar_Syntax_Syntax.sort);
(FStar_Util.set_add bv s);
)
end)) FStar_Syntax_Syntax.no_names binders)
in (

let ct = (FStar_Syntax_Util.comp_result c)
in ((non_dependent_or_raise s ct);
(

let k = (n - (FStar_List.length binders))
in (match ((k > (Prims.parse_int "0"))) with
| true -> begin
(is_non_dependent_arrow ct k)
end
| uu____1561 -> begin
true
end));
)))
end)))
end)
with
| Not_found -> begin
false
end
end))
end
| uu____1563 -> begin
((let _0_451 = (FStar_Syntax_Print.term_to_string ty)
in (FStar_Util.print1_warning "Not a dependent arrow : %s" _0_451));
false;
)
end)))
in (

let rec is_valid_application = (fun head -> (

let uu____1569 = (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
in (match (uu____1569) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.option_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.either_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.eq2_lid)) || (FStar_Syntax_Util.is_tuple_constructor (FStar_Syntax_Subst.compress head))) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (is_non_dependent_arrow fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty (FStar_List.length args)) -> begin
(

let res = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.env t)
in (match (res.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (uu____1583) -> begin
true
end
| uu____1593 -> begin
((let _0_452 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.print1_warning "Got a term which might be a non-dependent user-defined data-type %s\n" _0_452));
false;
)
end))
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____1598) -> begin
(is_valid_application t)
end
| uu____1603 -> begin
false
end)))
in (

let uu____1604 = (is_valid_application head)
in (match (uu____1604) with
| true -> begin
(mk (FStar_Syntax_Syntax.Tm_app ((let _0_454 = (FStar_List.map (fun uu____1616 -> (match (uu____1616) with
| (t, qual) -> begin
(let _0_453 = (star_type' env t)
in ((_0_453), (qual)))
end)) args)
in ((head), (_0_454))))))
end
| uu____1629 -> begin
(Prims.raise (FStar_Errors.Err ((let _0_455 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)" _0_455)))))
end)))))
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_abs (binders, repr, something) -> begin
(

let uu____1659 = (FStar_Syntax_Subst.open_term binders repr)
in (match (uu____1659) with
| (binders, repr) -> begin
(

let env = (

let uu___99_1665 = env
in (let _0_456 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _0_456; subst = uu___99_1665.subst; tc_const = uu___99_1665.tc_const}))
in (

let repr = (star_type' env repr)
in (FStar_Syntax_Util.abs binders repr something)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, t) when false -> begin
(

let x = (FStar_Syntax_Syntax.freshen_bv x)
in (

let sort = (star_type' env x.FStar_Syntax_Syntax.sort)
in (

let subst = (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x))))::[]
in (

let t = (FStar_Syntax_Subst.subst subst t)
in (

let t = (star_type' env t)
in (

let subst = (FStar_Syntax_Syntax.NM (((x), ((Prims.parse_int "0")))))::[]
in (

let t = (FStar_Syntax_Subst.subst subst t)
in (mk (FStar_Syntax_Syntax.Tm_refine ((((

let uu___100_1682 = x
in {FStar_Syntax_Syntax.ppname = uu___100_1682.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___100_1682.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (t))))))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(mk (FStar_Syntax_Syntax.Tm_meta ((let _0_457 = (star_type' env t)
in ((_0_457), (m))))))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), something) -> begin
(mk (FStar_Syntax_Syntax.Tm_ascribed ((let _0_459 = (star_type' env e)
in (let _0_458 = FStar_Util.Inl ((star_type' env t))
in ((_0_459), (_0_458), (something)))))))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____1717) -> begin
(Prims.raise (FStar_Errors.Err ((let _0_460 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_ascribed is outside of the definition language: %s" _0_460)))))
end
| FStar_Syntax_Syntax.Tm_refine (uu____1730) -> begin
(Prims.raise (FStar_Errors.Err ((let _0_461 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_refine is outside of the definition language: %s" _0_461)))))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____1735) -> begin
(Prims.raise (FStar_Errors.Err ((let _0_462 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_uinst is outside of the definition language: %s" _0_462)))))
end
| FStar_Syntax_Syntax.Tm_constant (uu____1740) -> begin
(Prims.raise (FStar_Errors.Err ((let _0_463 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_constant is outside of the definition language: %s" _0_463)))))
end
| FStar_Syntax_Syntax.Tm_match (uu____1741) -> begin
(Prims.raise (FStar_Errors.Err ((let _0_464 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_match is outside of the definition language: %s" _0_464)))))
end
| FStar_Syntax_Syntax.Tm_let (uu____1757) -> begin
(Prims.raise (FStar_Errors.Err ((let _0_465 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_let is outside of the definition language: %s" _0_465)))))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1765) -> begin
(Prims.raise (FStar_Errors.Err ((let _0_466 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_uvar is outside of the definition language: %s" _0_466)))))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(Prims.raise (FStar_Errors.Err ((let _0_467 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_unknown is outside of the definition language: %s" _0_467)))))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____1774) -> begin
(failwith "impossible")
end)))))


let is_monadic = (fun uu___85_1807 -> (match (uu___85_1807) with
| None -> begin
(failwith "un-annotated lambda?!")
end
| (Some (FStar_Util.Inl ({FStar_Syntax_Syntax.eff_name = _; FStar_Syntax_Syntax.res_typ = _; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = _}))) | (Some (FStar_Util.Inr (_, flags))) -> begin
(FStar_All.pipe_right flags (FStar_Util.for_some (fun uu___84_1844 -> (match (uu___84_1844) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| uu____1845 -> begin
false
end))))
end))


let rec is_C : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (

let uu____1849 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____1849) with
| FStar_Syntax_Syntax.Tm_app (head, args) when (FStar_Syntax_Util.is_tuple_constructor head) -> begin
(

let r = (is_C (Prims.fst (FStar_List.hd args)))
in (match (r) with
| true -> begin
((

let uu____1874 = (not ((FStar_List.for_all (fun uu____1877 -> (match (uu____1877) with
| (h, uu____1881) -> begin
(is_C h)
end)) args)))
in (match (uu____1874) with
| true -> begin
(failwith "not a C (A * C)")
end
| uu____1882 -> begin
()
end));
true;
)
end
| uu____1883 -> begin
((

let uu____1885 = (not ((FStar_List.for_all (fun uu____1888 -> (match (uu____1888) with
| (h, uu____1892) -> begin
(not ((is_C h)))
end)) args)))
in (match (uu____1885) with
| true -> begin
(failwith "not a C (C * A)")
end
| uu____1893 -> begin
()
end));
false;
)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let uu____1906 = (nm_of_comp comp.FStar_Syntax_Syntax.n)
in (match (uu____1906) with
| M (t) -> begin
((

let uu____1909 = (is_C t)
in (match (uu____1909) with
| true -> begin
(failwith "not a C (C -> C)")
end
| uu____1910 -> begin
()
end));
true;
)
end
| N (t) -> begin
(is_C t)
end))
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_uinst (t, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t, _, _)) -> begin
(is_C t)
end
| uu____1936 -> begin
false
end)))


let mk_return : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t e -> (

let mk = (fun x -> ((FStar_Syntax_Syntax.mk x) None e.FStar_Syntax_Syntax.pos))
in (

let p_type = (mk_star_to_type mk env t)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'" None p_type)
in (

let body = (mk (FStar_Syntax_Syntax.Tm_app ((let _0_471 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _0_470 = (let _0_469 = (let _0_468 = (FStar_Syntax_Syntax.as_implicit false)
in ((e), (_0_468)))
in (_0_469)::[])
in ((_0_471), (_0_470)))))))
in (let _0_473 = (let _0_472 = (FStar_Syntax_Syntax.mk_binder p)
in (_0_472)::[])
in (FStar_Syntax_Util.abs _0_473 body None)))))))


let is_unknown : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun uu___86_1981 -> (match (uu___86_1981) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| uu____1982 -> begin
false
end))


let rec check : env  ->  FStar_Syntax_Syntax.term  ->  nm  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e context_nm -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let return_if = (fun uu____2126 -> (match (uu____2126) with
| (rec_nm, s_e, u_e) -> begin
(

let check = (fun t1 t2 -> (

let uu____2147 = ((not ((is_unknown t2.FStar_Syntax_Syntax.n))) && (not ((FStar_TypeChecker_Rel.is_trivial (FStar_TypeChecker_Rel.teq env.env t1 t2)))))
in (match (uu____2147) with
| true -> begin
(Prims.raise (FStar_Errors.Err ((let _0_476 = (FStar_Syntax_Print.term_to_string e)
in (let _0_475 = (FStar_Syntax_Print.term_to_string t1)
in (let _0_474 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check]: the expression [%s] has type [%s] but should have type [%s]" _0_476 _0_475 _0_474)))))))
end
| uu____2148 -> begin
()
end)))
in (match (((rec_nm), (context_nm))) with
| ((N (t1), N (t2))) | ((M (t1), M (t2))) -> begin
((check t1 t2);
((rec_nm), (s_e), (u_e));
)
end
| (N (t1), M (t2)) -> begin
((check t1 t2);
(let _0_477 = (mk_return env t1 s_e)
in ((M (t1)), (_0_477), (u_e)));
)
end
| (M (t1), N (t2)) -> begin
(Prims.raise (FStar_Errors.Err ((let _0_480 = (FStar_Syntax_Print.term_to_string e)
in (let _0_479 = (FStar_Syntax_Print.term_to_string t1)
in (let _0_478 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]" _0_480 _0_479 _0_478)))))))
end))
end))
in (

let ensure_m = (fun env e2 -> (

let strip_m = (fun uu___87_2185 -> (match (uu___87_2185) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| uu____2195 -> begin
(failwith "impossible")
end))
in (match (context_nm) with
| N (t) -> begin
(Prims.raise (FStar_Errors.Error ((let _0_482 = (let _0_481 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren\'t : " _0_481))
in ((_0_482), (e2.FStar_Syntax_Syntax.pos))))))
end
| M (uu____2209) -> begin
(strip_m (check env e2 context_nm))
end)))
in (

let uu____2210 = (FStar_Syntax_Subst.compress e).FStar_Syntax_Syntax.n
in (match (uu____2210) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
(return_if (infer env e))
end
| FStar_Syntax_Syntax.Tm_let ((false, (binding)::[]), e2) -> begin
(mk_let env binding e2 (fun env e2 -> (check env e2 context_nm)) ensure_m)
end
| FStar_Syntax_Syntax.Tm_match (e0, branches) -> begin
(mk_match env e0 branches (fun env body -> (check env body context_nm)))
end
| (FStar_Syntax_Syntax.Tm_meta (e, _)) | (FStar_Syntax_Syntax.Tm_uinst (e, _)) | (FStar_Syntax_Syntax.Tm_ascribed (e, _, _)) -> begin
(check env e context_nm)
end
| FStar_Syntax_Syntax.Tm_let (uu____2286) -> begin
(failwith (let _0_483 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_let %s" _0_483)))
end
| FStar_Syntax_Syntax.Tm_type (uu____2297) -> begin
(failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (uu____2301) -> begin
(failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (uu____2312) -> begin
(failwith (let _0_484 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_refine %s" _0_484)))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____2320) -> begin
(failwith (let _0_485 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_uvar %s" _0_485)))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____2332) -> begin
(failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(failwith (let _0_486 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_unknown %s" _0_486)))
end))))))
and infer : env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.env)
in (

let uu____2377 = (FStar_Syntax_Subst.compress e).FStar_Syntax_Syntax.n
in (match (uu____2377) with
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(failwith "I failed to open a binder... boo")
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
((N (bv.FStar_Syntax_Syntax.sort)), (e), (e))
end
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let binders = (FStar_Syntax_Subst.open_binders binders)
in (

let subst = (FStar_Syntax_Subst.opening_of_binders binders)
in (

let body = (FStar_Syntax_Subst.subst subst body)
in (

let env = (

let uu___101_2415 = env
in (let _0_487 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _0_487; subst = uu___101_2415.subst; tc_const = uu___101_2415.tc_const}))
in (

let s_binders = (FStar_List.map (fun uu____2424 -> (match (uu____2424) with
| (bv, qual) -> begin
(

let sort = (star_type' env bv.FStar_Syntax_Syntax.sort)
in (((

let uu___102_2432 = bv
in {FStar_Syntax_Syntax.ppname = uu___102_2432.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___102_2432.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (qual)))
end)) binders)
in (

let uu____2433 = (FStar_List.fold_left (fun uu____2442 uu____2443 -> (match (((uu____2442), (uu____2443))) with
| ((env, acc), (bv, qual)) -> begin
(

let c = bv.FStar_Syntax_Syntax.sort
in (

let uu____2471 = (is_C c)
in (match (uu____2471) with
| true -> begin
(

let xw = (let _0_488 = (star_type' env c)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "^w") None _0_488))
in (

let x = (

let uu___103_2477 = bv
in (let _0_490 = (let _0_489 = (FStar_Syntax_Syntax.bv_to_name xw)
in (trans_F_ env c _0_489))
in {FStar_Syntax_Syntax.ppname = uu___103_2477.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___103_2477.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_490}))
in (

let env = (

let uu___104_2479 = env
in (let _0_493 = (let _0_492 = FStar_Syntax_Syntax.NT ((let _0_491 = (FStar_Syntax_Syntax.bv_to_name xw)
in ((bv), (_0_491))))
in (_0_492)::env.subst)
in {env = uu___104_2479.env; subst = _0_493; tc_const = uu___104_2479.tc_const}))
in (let _0_497 = (let _0_496 = (FStar_Syntax_Syntax.mk_binder x)
in (let _0_495 = (let _0_494 = (FStar_Syntax_Syntax.mk_binder xw)
in (_0_494)::acc)
in (_0_496)::_0_495))
in ((env), (_0_497))))))
end
| uu____2481 -> begin
(

let x = (

let uu___105_2483 = bv
in (let _0_498 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___105_2483.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___105_2483.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_498}))
in (let _0_500 = (let _0_499 = (FStar_Syntax_Syntax.mk_binder x)
in (_0_499)::acc)
in ((env), (_0_500))))
end)))
end)) ((env), ([])) binders)
in (match (uu____2433) with
| (env, u_binders) -> begin
(

let u_binders = (FStar_List.rev u_binders)
in (

let uu____2495 = (

let check_what = (

let uu____2507 = (is_monadic what)
in (match (uu____2507) with
| true -> begin
check_m
end
| uu____2515 -> begin
check_n
end))
in (

let uu____2516 = (check_what env body)
in (match (uu____2516) with
| (t, s_body, u_body) -> begin
(let _0_501 = (comp_of_nm (

let uu____2526 = (is_monadic what)
in (match (uu____2526) with
| true -> begin
M (t)
end
| uu____2527 -> begin
N (t)
end)))
in ((_0_501), (s_body), (u_body)))
end)))
in (match (uu____2495) with
| (comp, s_body, u_body) -> begin
(

let t = (FStar_Syntax_Util.arrow binders comp)
in (

let s_what = (match (what) with
| None -> begin
None
end
| Some (FStar_Util.Inl (lc)) -> begin
(

let uu____2569 = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___88_2571 -> (match (uu___88_2571) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| uu____2572 -> begin
false
end))))
in (match (uu____2569) with
| true -> begin
(

let double_starred_comp = (FStar_Syntax_Syntax.mk_Total (let _0_502 = (FStar_Syntax_Util.comp_result (lc.FStar_Syntax_Syntax.comp ()))
in (FStar_All.pipe_left double_star _0_502)))
in (

let flags = (FStar_List.filter (fun uu___89_2582 -> (match (uu___89_2582) with
| FStar_Syntax_Syntax.CPS -> begin
false
end
| uu____2583 -> begin
true
end)) lc.FStar_Syntax_Syntax.cflags)
in Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp (FStar_Syntax_Util.comp_set_flags double_starred_comp flags))))))
end
| uu____2592 -> begin
Some (FStar_Util.Inl ((

let uu___106_2601 = lc
in {FStar_Syntax_Syntax.eff_name = uu___106_2601.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = uu___106_2601.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu___106_2601.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____2602 -> (

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let result_typ = (star_type' env (FStar_Syntax_Util.comp_result c))
in (FStar_Syntax_Util.set_result_typ c result_typ))))})))
end))
end
| Some (FStar_Util.Inr (lid, flags)) -> begin
Some (FStar_Util.Inr ((

let uu____2627 = (FStar_All.pipe_right flags (FStar_Util.for_some (fun uu___90_2629 -> (match (uu___90_2629) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| uu____2630 -> begin
false
end))))
in (match (uu____2627) with
| true -> begin
(let _0_503 = (FStar_List.filter (fun uu___91_2635 -> (match (uu___91_2635) with
| FStar_Syntax_Syntax.CPS -> begin
false
end
| uu____2636 -> begin
true
end)) flags)
in ((FStar_Syntax_Const.effect_Tot_lid), (_0_503)))
end
| uu____2637 -> begin
((lid), (flags))
end))))
end)
in (

let uu____2639 = (

let comp = (let _0_505 = (is_monadic what)
in (let _0_504 = (FStar_Syntax_Subst.subst env.subst s_body)
in (trans_G env (FStar_Syntax_Util.comp_result comp) _0_505 _0_504)))
in (let _0_506 = (FStar_Syntax_Util.ascribe u_body (FStar_Util.Inr (comp)))
in ((_0_506), (Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp comp)))))))
in (match (uu____2639) with
| (u_body, u_what) -> begin
(

let s_body = (FStar_Syntax_Subst.close s_binders s_body)
in (

let s_binders = (FStar_Syntax_Subst.close_binders s_binders)
in (

let s_term = (mk (FStar_Syntax_Syntax.Tm_abs (((s_binders), (s_body), (s_what)))))
in (

let u_body = (FStar_Syntax_Subst.close u_binders u_body)
in (

let u_binders = (FStar_Syntax_Subst.close_binders u_binders)
in (

let u_term = (mk (FStar_Syntax_Syntax.Tm_abs (((u_binders), (u_body), (u_what)))))
in ((N (t)), (s_term), (u_term))))))))
end))))
end)))
end)))))))
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = {FStar_Syntax_Syntax.v = lid; FStar_Syntax_Syntax.ty = uu____2717; FStar_Syntax_Syntax.p = uu____2718}; FStar_Syntax_Syntax.fv_delta = uu____2719; FStar_Syntax_Syntax.fv_qual = uu____2720}) -> begin
(

let uu____2726 = (FStar_TypeChecker_Env.lookup_lid env.env lid)
in (match (uu____2726) with
| (uu____2732, t) -> begin
(

let txt = (FStar_Ident.text_of_lid lid)
in (let _0_507 = N ((normalize t))
in ((_0_507), (e), (e))))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let uu____2751 = (check_n env head)
in (match (uu____2751) with
| (t_head, s_head, u_head) -> begin
(

let is_arrow = (fun t -> (

let uu____2765 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____2765) with
| FStar_Syntax_Syntax.Tm_arrow (uu____2766) -> begin
true
end
| uu____2774 -> begin
false
end)))
in (

let rec flatten = (fun t -> (

let uu____2786 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____2786) with
| FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (t, uu____2796); FStar_Syntax_Syntax.tk = uu____2797; FStar_Syntax_Syntax.pos = uu____2798; FStar_Syntax_Syntax.vars = uu____2799}) when (is_arrow t) -> begin
(

let uu____2816 = (flatten t)
in (match (uu____2816) with
| (binders', comp) -> begin
(((FStar_List.append binders binders')), (comp))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
((binders), (comp))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, uu____2868, uu____2869) -> begin
(flatten e)
end
| uu____2888 -> begin
(Prims.raise (FStar_Errors.Err ((let _0_508 = (FStar_Syntax_Print.term_to_string t_head)
in (FStar_Util.format1 "%s: not a function type" _0_508)))))
end)))
in (

let uu____2896 = (flatten t_head)
in (match (uu____2896) with
| (binders, comp) -> begin
(

let n = (FStar_List.length binders)
in (

let n' = (FStar_List.length args)
in ((match (((FStar_List.length binders) < (FStar_List.length args))) with
| true -> begin
(Prims.raise (FStar_Errors.Err ((let _0_511 = (FStar_Util.string_of_int n)
in (let _0_510 = (FStar_Util.string_of_int (n' - n))
in (let _0_509 = (FStar_Util.string_of_int n)
in (FStar_Util.format3 "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments." _0_511 _0_510 _0_509)))))))
end
| uu____2952 -> begin
()
end);
(

let uu____2953 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (uu____2953) with
| (binders, comp) -> begin
(

let rec final_type = (fun subst uu____2980 args -> (match (uu____2980) with
| (binders, comp) -> begin
(match (((binders), (args))) with
| ([], []) -> begin
(nm_of_comp (FStar_Syntax_Subst.subst_comp subst comp).FStar_Syntax_Syntax.n)
end
| (binders, []) -> begin
(

let uu____3039 = (FStar_Syntax_Subst.compress (let _0_512 = (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))))
in (FStar_Syntax_Subst.subst subst _0_512))).FStar_Syntax_Syntax.n
in (match (uu____3039) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
N ((mk (FStar_Syntax_Syntax.Tm_arrow ((let _0_513 = (FStar_Syntax_Subst.close_comp binders comp)
in ((binders), (_0_513)))))))
end
| uu____3058 -> begin
(failwith "wat?")
end))
end
| ([], (uu____3059)::uu____3060) -> begin
(failwith "just checked that?!")
end
| (((bv, uu____3085))::binders, ((arg, uu____3088))::args) -> begin
(final_type ((FStar_Syntax_Syntax.NT (((bv), (arg))))::subst) ((binders), (comp)) args)
end)
end))
in (

let final_type = (final_type [] ((binders), (comp)) args)
in (

let uu____3122 = (FStar_List.splitAt n' binders)
in (match (uu____3122) with
| (binders, uu____3139) -> begin
(

let uu____3152 = (FStar_List.split (FStar_List.map2 (fun uu____3178 uu____3179 -> (match (((uu____3178), (uu____3179))) with
| ((bv, uu____3196), (arg, q)) -> begin
(

let uu____3203 = (FStar_Syntax_Subst.compress bv.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
in (match (uu____3203) with
| FStar_Syntax_Syntax.Tm_type (uu____3211) -> begin
(

let arg = ((arg), (q))
in ((arg), ((arg)::[])))
end
| uu____3224 -> begin
(

let uu____3225 = (check_n env arg)
in (match (uu____3225) with
| (uu____3236, s_arg, u_arg) -> begin
(let _0_516 = (

let uu____3244 = (is_C bv.FStar_Syntax_Syntax.sort)
in (match (uu____3244) with
| true -> begin
(let _0_515 = (let _0_514 = (FStar_Syntax_Subst.subst env.subst s_arg)
in ((_0_514), (q)))
in (_0_515)::(((u_arg), (q)))::[])
end
| uu____3254 -> begin
(((u_arg), (q)))::[]
end))
in ((((s_arg), (q))), (_0_516)))
end))
end))
end)) binders args))
in (match (uu____3152) with
| (s_args, u_args) -> begin
(

let u_args = (FStar_List.flatten u_args)
in (let _0_518 = (mk (FStar_Syntax_Syntax.Tm_app (((s_head), (s_args)))))
in (let _0_517 = (mk (FStar_Syntax_Syntax.Tm_app (((u_head), (u_args)))))
in ((final_type), (_0_518), (_0_517)))))
end))
end))))
end));
)))
end))))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, (binding)::[]), e2) -> begin
(mk_let env binding e2 infer check_m)
end
| FStar_Syntax_Syntax.Tm_match (e0, branches) -> begin
(mk_match env e0 branches infer)
end
| (FStar_Syntax_Syntax.Tm_uinst (e, _)) | (FStar_Syntax_Syntax.Tm_meta (e, _)) | (FStar_Syntax_Syntax.Tm_ascribed (e, _, _)) -> begin
(infer env e)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _0_519 = N ((env.tc_const c))
in ((_0_519), (e), (e)))
end
| FStar_Syntax_Syntax.Tm_let (uu____3357) -> begin
(failwith (let _0_520 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_let %s" _0_520)))
end
| FStar_Syntax_Syntax.Tm_type (uu____3368) -> begin
(failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (uu____3372) -> begin
(failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (uu____3383) -> begin
(failwith (let _0_521 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_refine %s" _0_521)))
end
| FStar_Syntax_Syntax.Tm_uvar (uu____3391) -> begin
(failwith (let _0_522 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_uvar %s" _0_522)))
end
| FStar_Syntax_Syntax.Tm_delayed (uu____3403) -> begin
(failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(failwith (let _0_523 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_unknown %s" _0_523)))
end)))))
and mk_match : env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.option * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) Prims.list  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e0 branches f -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e0.FStar_Syntax_Syntax.pos))
in (

let uu____3464 = (check_n env e0)
in (match (uu____3464) with
| (uu____3471, s_e0, u_e0) -> begin
(

let uu____3474 = (FStar_List.split (FStar_List.map (fun b -> (

let uu____3521 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____3521) with
| (pat, None, body) -> begin
(

let env = (

let uu___107_3553 = env
in (let _0_525 = (let _0_524 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env.env _0_524))
in {env = _0_525; subst = uu___107_3553.subst; tc_const = uu___107_3553.tc_const}))
in (

let uu____3554 = (f env body)
in (match (uu____3554) with
| (nm, s_body, u_body) -> begin
((nm), (((pat), (None), (((s_body), (u_body), (body))))))
end)))
end
| uu____3603 -> begin
(Prims.raise (FStar_Errors.Err ("No when clauses in the definition language")))
end))) branches))
in (match (uu____3474) with
| (nms, branches) -> begin
(

let t1 = (

let uu____3655 = (FStar_List.hd nms)
in (match (uu____3655) with
| (M (t1)) | (N (t1)) -> begin
t1
end))
in (

let has_m = (FStar_List.existsb (fun uu___92_3658 -> (match (uu___92_3658) with
| M (uu____3659) -> begin
true
end
| uu____3660 -> begin
false
end)) nms)
in (

let uu____3661 = (FStar_List.unzip3 (FStar_List.map2 (fun nm uu____3731 -> (match (uu____3731) with
| (pat, guard, (s_body, u_body, original_body)) -> begin
(match (((nm), (has_m))) with
| ((N (t2), false)) | ((M (t2), true)) -> begin
((nm), (((pat), (guard), (s_body))), (((pat), (guard), (u_body))))
end
| (N (t2), true) -> begin
(

let uu____3827 = (check env original_body (M (t2)))
in (match (uu____3827) with
| (uu____3850, s_body, u_body) -> begin
((M (t2)), (((pat), (guard), (s_body))), (((pat), (guard), (u_body))))
end))
end
| (M (uu____3879), false) -> begin
(failwith "impossible")
end)
end)) nms branches))
in (match (uu____3661) with
| (nms, s_branches, u_branches) -> begin
(match (has_m) with
| true -> begin
(

let p_type = (mk_star_to_type mk env t1)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" None p_type)
in (

let s_branches = (FStar_List.map (fun uu____3982 -> (match (uu____3982) with
| (pat, guard, s_body) -> begin
(

let s_body = (mk (FStar_Syntax_Syntax.Tm_app ((let _0_529 = (let _0_528 = (let _0_527 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _0_526 = (FStar_Syntax_Syntax.as_implicit false)
in ((_0_527), (_0_526))))
in (_0_528)::[])
in ((s_body), (_0_529))))))
in ((pat), (guard), (s_body)))
end)) s_branches)
in (

let s_branches = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let s_e = (let _0_532 = (let _0_530 = (FStar_Syntax_Syntax.mk_binder p)
in (_0_530)::[])
in (let _0_531 = (mk (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches)))))
in (FStar_Syntax_Util.abs _0_532 _0_531 None)))
in (

let t1_star = (let _0_536 = (let _0_534 = (let _0_533 = (FStar_Syntax_Syntax.new_bv None p_type)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _0_533))
in (_0_534)::[])
in (let _0_535 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _0_536 _0_535)))
in (let _0_538 = (mk (FStar_Syntax_Syntax.Tm_ascribed (((s_e), (FStar_Util.Inl (t1_star)), (None)))))
in (let _0_537 = (mk (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches)))))
in ((M (t1)), (_0_538), (_0_537)))))))))))
end
| uu____4069 -> begin
(

let s_branches = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let t1_star = t1
in (let _0_541 = (mk (FStar_Syntax_Syntax.Tm_ascribed ((let _0_539 = (mk (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches)))))
in ((_0_539), (FStar_Util.Inl (t1_star)), (None))))))
in (let _0_540 = (mk (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches)))))
in ((N (t1)), (_0_541), (_0_540)))))))
end)
end))))
end))
end))))
and mk_let : env_  ->  FStar_Syntax_Syntax.letbinding  ->  FStar_Syntax_Syntax.term  ->  (env_  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env binding e2 proceed ensure_m -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e2.FStar_Syntax_Syntax.pos))
in (

let e1 = binding.FStar_Syntax_Syntax.lbdef
in (

let x = (FStar_Util.left binding.FStar_Syntax_Syntax.lbname)
in (

let x_binders = (let _0_542 = (FStar_Syntax_Syntax.mk_binder x)
in (_0_542)::[])
in (

let uu____4125 = (FStar_Syntax_Subst.open_term x_binders e2)
in (match (uu____4125) with
| (x_binders, e2) -> begin
(

let uu____4133 = (infer env e1)
in (match (uu____4133) with
| (N (t1), s_e1, u_e1) -> begin
(

let u_binding = (

let uu____4144 = (is_C t1)
in (match (uu____4144) with
| true -> begin
(

let uu___108_4145 = binding
in (let _0_544 = (let _0_543 = (FStar_Syntax_Subst.subst env.subst s_e1)
in (trans_F_ env t1 _0_543))
in {FStar_Syntax_Syntax.lbname = uu___108_4145.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___108_4145.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _0_544; FStar_Syntax_Syntax.lbeff = uu___108_4145.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___108_4145.FStar_Syntax_Syntax.lbdef}))
end
| uu____4146 -> begin
binding
end))
in (

let env = (

let uu___109_4148 = env
in (let _0_545 = (FStar_TypeChecker_Env.push_bv env.env (

let uu___110_4149 = x
in {FStar_Syntax_Syntax.ppname = uu___110_4149.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___110_4149.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _0_545; subst = uu___109_4148.subst; tc_const = uu___109_4148.tc_const}))
in (

let uu____4150 = (proceed env e2)
in (match (uu____4150) with
| (nm_rec, s_e2, u_e2) -> begin
(

let s_binding = (

let uu___111_4161 = binding
in (let _0_546 = (star_type' env binding.FStar_Syntax_Syntax.lbtyp)
in {FStar_Syntax_Syntax.lbname = uu___111_4161.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___111_4161.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _0_546; FStar_Syntax_Syntax.lbeff = uu___111_4161.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___111_4161.FStar_Syntax_Syntax.lbdef}))
in (let _0_550 = (mk (FStar_Syntax_Syntax.Tm_let ((let _0_547 = (FStar_Syntax_Subst.close x_binders s_e2)
in ((((false), (((

let uu___112_4170 = s_binding
in {FStar_Syntax_Syntax.lbname = uu___112_4170.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___112_4170.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___112_4170.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___112_4170.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = s_e1}))::[]))), (_0_547))))))
in (let _0_549 = (mk (FStar_Syntax_Syntax.Tm_let ((let _0_548 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let uu___113_4175 = u_binding
in {FStar_Syntax_Syntax.lbname = uu___113_4175.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___113_4175.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___113_4175.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___113_4175.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_0_548))))))
in ((nm_rec), (_0_550), (_0_549)))))
end))))
end
| (M (t1), s_e1, u_e1) -> begin
(

let u_binding = (

let uu___114_4180 = binding
in {FStar_Syntax_Syntax.lbname = uu___114_4180.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___114_4180.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.lbdef = uu___114_4180.FStar_Syntax_Syntax.lbdef})
in (

let env = (

let uu___115_4182 = env
in (let _0_551 = (FStar_TypeChecker_Env.push_bv env.env (

let uu___116_4183 = x
in {FStar_Syntax_Syntax.ppname = uu___116_4183.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___116_4183.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _0_551; subst = uu___115_4182.subst; tc_const = uu___115_4182.tc_const}))
in (

let uu____4184 = (ensure_m env e2)
in (match (uu____4184) with
| (t2, s_e2, u_e2) -> begin
(

let p_type = (mk_star_to_type mk env t2)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" None p_type)
in (

let s_e2 = (mk (FStar_Syntax_Syntax.Tm_app ((let _0_555 = (let _0_554 = (let _0_553 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _0_552 = (FStar_Syntax_Syntax.as_implicit false)
in ((_0_553), (_0_552))))
in (_0_554)::[])
in ((s_e2), (_0_555))))))
in (

let s_e2 = (FStar_Syntax_Util.abs x_binders s_e2 None)
in (

let body = (mk (FStar_Syntax_Syntax.Tm_app ((let _0_558 = (let _0_557 = (let _0_556 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_e2), (_0_556)))
in (_0_557)::[])
in ((s_e1), (_0_558))))))
in (let _0_563 = (let _0_560 = (let _0_559 = (FStar_Syntax_Syntax.mk_binder p)
in (_0_559)::[])
in (FStar_Syntax_Util.abs _0_560 body None))
in (let _0_562 = (mk (FStar_Syntax_Syntax.Tm_let ((let _0_561 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let uu___117_4235 = u_binding
in {FStar_Syntax_Syntax.lbname = uu___117_4235.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___117_4235.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___117_4235.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___117_4235.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_0_561))))))
in ((M (t2)), (_0_563), (_0_562)))))))))
end))))
end))
end)))))))
and check_n : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = N ((FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos))
in (

let uu____4254 = (check env e mn)
in (match (uu____4254) with
| (N (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| uu____4264 -> begin
(failwith "[check_n]: impossible")
end))))
and check_m : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = M ((FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos))
in (

let uu____4289 = (check env e mn)
in (match (uu____4289) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| uu____4299 -> begin
(failwith "[check_m]: impossible")
end))))
and comp_of_nm : nm_  ->  FStar_Syntax_Syntax.comp = (fun nm -> (match (nm) with
| N (t) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| M (t) -> begin
(mk_M t)
end))
and mk_M : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun t -> (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_unknown)::[]; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.monadic_lid; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.CPS)::(FStar_Syntax_Syntax.TOTAL)::[]}))
and type_of_comp : (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (FStar_Syntax_Util.comp_result t))
and trans_F_ : env_  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> ((

let uu____4321 = (not ((is_C c)))
in (match (uu____4321) with
| true -> begin
(failwith "not a C")
end
| uu____4322 -> begin
()
end));
(

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos))
in (

let uu____4333 = (FStar_Syntax_Subst.compress c).FStar_Syntax_Syntax.n
in (match (uu____4333) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let uu____4350 = (FStar_Syntax_Util.head_and_args wp)
in (match (uu____4350) with
| (wp_head, wp_args) -> begin
((

let uu____4377 = ((not (((FStar_List.length wp_args) = (FStar_List.length args)))) || (not ((let _0_564 = (FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length wp_args) FStar_Range.dummyRange)
in (FStar_Syntax_Util.is_constructor wp_head _0_564)))))
in (match (uu____4377) with
| true -> begin
(failwith "mismatch")
end
| uu____4397 -> begin
()
end));
(mk (FStar_Syntax_Syntax.Tm_app ((let _0_568 = (FStar_List.map2 (fun uu____4409 uu____4410 -> (match (((uu____4409), (uu____4410))) with
| ((arg, q), (wp_arg, q')) -> begin
(

let print_implicit = (fun q -> (

let uu____4433 = (FStar_Syntax_Syntax.is_implicit q)
in (match (uu____4433) with
| true -> begin
"implicit"
end
| uu____4434 -> begin
"explicit"
end)))
in ((match ((q <> q')) with
| true -> begin
(let _0_566 = (print_implicit q)
in (let _0_565 = (print_implicit q')
in (FStar_Util.print2_warning "Incoherent implicit qualifiers %b %b" _0_566 _0_565)))
end
| uu____4436 -> begin
()
end);
(let _0_567 = (trans_F_ env arg wp_arg)
in ((_0_567), (q)));
))
end)) args wp_args)
in ((head), (_0_568))))));
)
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let binders = (FStar_Syntax_Util.name_binders binders)
in (

let uu____4453 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (uu____4453) with
| (binders_orig, comp) -> begin
(

let uu____4458 = (FStar_List.split (FStar_List.map (fun uu____4476 -> (match (uu____4476) with
| (bv, q) -> begin
(

let h = bv.FStar_Syntax_Syntax.sort
in (

let uu____4489 = (is_C h)
in (match (uu____4489) with
| true -> begin
(

let w' = (let _0_569 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-w\'") None _0_569))
in (let _0_574 = (let _0_573 = (let _0_572 = (let _0_571 = (FStar_Syntax_Syntax.null_bv (let _0_570 = (FStar_Syntax_Syntax.bv_to_name w')
in (trans_F_ env h _0_570)))
in ((_0_571), (q)))
in (_0_572)::[])
in (((w'), (q)))::_0_573)
in ((w'), (_0_574))))
end
| uu____4505 -> begin
(

let x = (let _0_575 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-x") None _0_575))
in ((x), ((((x), (q)))::[])))
end)))
end)) binders_orig))
in (match (uu____4458) with
| (bvs, binders) -> begin
(

let binders = (FStar_List.flatten binders)
in (

let comp = (let _0_577 = (let _0_576 = (FStar_Syntax_Syntax.binders_of_list bvs)
in (FStar_Syntax_Util.rename_binders binders_orig _0_576))
in (FStar_Syntax_Subst.subst_comp _0_577 comp))
in (

let app = (mk (FStar_Syntax_Syntax.Tm_app ((let _0_580 = (FStar_List.map (fun bv -> (let _0_579 = (FStar_Syntax_Syntax.bv_to_name bv)
in (let _0_578 = (FStar_Syntax_Syntax.as_implicit false)
in ((_0_579), (_0_578))))) bvs)
in ((wp), (_0_580))))))
in (

let comp = (let _0_582 = (type_of_comp comp)
in (let _0_581 = (is_monadic_comp comp)
in (trans_G env _0_582 _0_581 app)))
in (FStar_Syntax_Util.arrow binders comp)))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, uu____4544, uu____4545) -> begin
(trans_F_ env e wp)
end
| uu____4564 -> begin
(failwith "impossible trans_F_")
end)));
))
and trans_G : env_  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env h is_monadic wp -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None h.FStar_Syntax_Syntax.pos))
in (match (is_monadic) with
| true -> begin
(FStar_Syntax_Syntax.mk_Comp (let _0_586 = (star_type' env h)
in (let _0_585 = (let _0_584 = (let _0_583 = (FStar_Syntax_Syntax.as_implicit false)
in ((wp), (_0_583)))
in (_0_584)::[])
in {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_unknown)::[]; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _0_586; FStar_Syntax_Syntax.effect_args = _0_585; FStar_Syntax_Syntax.flags = []})))
end
| uu____4583 -> begin
(FStar_Syntax_Syntax.mk_Total (trans_F_ env h wp))
end)))


let n : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]))


let star_type : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (let _0_587 = (n env.env t)
in (star_type' env _0_587)))


let star_expr : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env t -> (let _0_588 = (n env.env t)
in (check_n env _0_588)))


let trans_F : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> (let _0_590 = (n env.env c)
in (let _0_589 = (n env.env wp)
in (trans_F_ env _0_590 _0_589))))




