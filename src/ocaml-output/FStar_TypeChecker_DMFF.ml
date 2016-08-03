
open Prims

let gen_wps_for_free = (fun env binders a wp_a tc_decl tc_term ed -> (

let wp_a = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env wp_a)
in (

let a = (

let _57_15 = a
in (let _149_20 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env a.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_15.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_15.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_20}))
in (

let d = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))
in (

let _57_20 = (d "Elaborating extra WP combinators")
in (

let _57_22 = (let _149_23 = (FStar_Syntax_Print.term_to_string wp_a)
in (FStar_Util.print1 "wp_a is: %s\n" _149_23))
in (

let check = (fun env str t -> if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _57_28 = (d str)
in (

let _57_30 = (let _149_30 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Generated term for %s: %s\n" str _149_30))
in (

let _57_43 = (tc_term env t)
in (match (_57_43) with
| (t, {FStar_Syntax_Syntax.eff_name = _57_39; FStar_Syntax_Syntax.res_typ = res_typ; FStar_Syntax_Syntax.cflags = _57_36; FStar_Syntax_Syntax.comp = _57_34}, _57_42) -> begin
(

let res_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env res_typ)
in (let _149_32 = (FStar_Syntax_Print.term_to_string res_typ)
in (FStar_Util.print2 "Inferred type for %s: %s\n" str _149_32)))
end))))
end else begin
()
end)
in (

let rec collect_binders = (fun t -> (match ((let _149_35 = (FStar_Syntax_Subst.compress t)
in _149_35.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let rest = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
t
end
| _57_54 -> begin
(FStar_All.failwith "wp_a contains non-Tot arrow")
end)
in (let _149_36 = (collect_binders rest)
in (FStar_List.append bs _149_36)))
end
| FStar_Syntax_Syntax.Tm_type (_57_57) -> begin
[]
end
| _57_60 -> begin
(FStar_All.failwith "wp_a doesn\'t end in Type0")
end))
in (

let mk_lid = (fun name -> (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" name))) FStar_Range.dummyRange))
in (

let gamma = (collect_binders wp_a)
in (

let _57_64 = (let _149_40 = (let _149_39 = (FStar_Syntax_Print.binders_to_string ", " gamma)
in (FStar_Util.format1 "Gamma is %s\n" _149_39))
in (d _149_40))
in (

let unknown = FStar_Syntax_Syntax.tun
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None FStar_Range.dummyRange))
in (

let register = (fun env lident def -> (FStar_TypeChecker_Util.register_toplevel_definition env tc_decl lident def))
in (

let binders_of_list = (FStar_List.map (fun _57_75 -> (match (_57_75) with
| (t, b) -> begin
(let _149_51 = (FStar_Syntax_Syntax.as_implicit b)
in ((t), (_149_51)))
end)))
in (

let mk_all_implicit = (FStar_List.map (fun t -> (let _149_54 = (FStar_Syntax_Syntax.as_implicit true)
in (((Prims.fst t)), (_149_54)))))
in (

let args_of_binders = (FStar_List.map (fun bv -> (let _149_57 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst bv))
in (FStar_Syntax_Syntax.as_arg _149_57))))
in (

let _57_106 = (

let _57_87 = (

let mk = (fun f -> (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let body = (let _149_70 = (let _149_69 = (FStar_Syntax_Syntax.bv_to_name t)
in (f _149_69))
in (FStar_Syntax_Util.arrow gamma _149_70))
in (let _149_75 = (let _149_74 = (let _149_73 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_72 = (let _149_71 = (FStar_Syntax_Syntax.mk_binder t)
in (_149_71)::[])
in (_149_73)::_149_72))
in (FStar_List.append binders _149_74))
in (FStar_Syntax_Util.abs _149_75 body None)))))
in (let _149_77 = (mk FStar_Syntax_Syntax.mk_Total)
in (let _149_76 = (mk FStar_Syntax_Syntax.mk_GTotal)
in ((_149_77), (_149_76)))))
in (match (_57_87) with
| (ctx_def, gctx_def) -> begin
(

let ctx_lid = (mk_lid "ctx")
in (

let _57_91 = (register env ctx_lid ctx_def)
in (match (_57_91) with
| (env, ctx_fv) -> begin
(

let gctx_lid = (mk_lid "gctx")
in (

let _57_95 = (register env gctx_lid gctx_def)
in (match (_57_95) with
| (env, gctx_fv) -> begin
(

let mk_app = (fun fv t -> (let _149_107 = (let _149_106 = (let _149_105 = (let _149_104 = (FStar_List.map (fun _57_102 -> (match (_57_102) with
| (bv, _57_101) -> begin
(let _149_96 = (FStar_Syntax_Syntax.bv_to_name bv)
in (let _149_95 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_96), (_149_95))))
end)) binders)
in (let _149_103 = (let _149_102 = (let _149_98 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _149_97 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_98), (_149_97))))
in (let _149_101 = (let _149_100 = (let _149_99 = (FStar_Syntax_Syntax.as_implicit false)
in ((t), (_149_99)))
in (_149_100)::[])
in (_149_102)::_149_101))
in (FStar_List.append _149_104 _149_103)))
in ((fv), (_149_105)))
in FStar_Syntax_Syntax.Tm_app (_149_106))
in (mk _149_107)))
in ((env), ((mk_app ctx_fv)), ((mk_app gctx_fv))))
end)))
end)))
end))
in (match (_57_106) with
| (env, mk_ctx, mk_gctx) -> begin
(

let c_pure = (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let x = (let _149_112 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" None _149_112))
in (

let ret = (let _149_117 = (let _149_116 = (let _149_115 = (let _149_114 = (let _149_113 = (FStar_Syntax_Syntax.bv_to_name t)
in (mk_ctx _149_113))
in (FStar_Syntax_Syntax.mk_Total _149_114))
in (FStar_Syntax_Util.lcomp_of_comp _149_115))
in FStar_Util.Inl (_149_116))
in Some (_149_117))
in (

let body = (let _149_118 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs gamma _149_118 ret))
in (let _149_121 = (let _149_120 = (mk_all_implicit binders)
in (let _149_119 = (binders_of_list ((((a), (true)))::(((t), (true)))::(((x), (false)))::[]))
in (FStar_List.append _149_120 _149_119)))
in (FStar_Syntax_Util.abs _149_121 body ret))))))
in (

let _57_114 = (let _149_122 = (mk_lid "pure")
in (register env _149_122 c_pure))
in (match (_57_114) with
| (env, c_pure) -> begin
(

let c_app = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let l = (let _149_130 = (let _149_129 = (let _149_128 = (let _149_125 = (let _149_124 = (let _149_123 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv None _149_123))
in (FStar_Syntax_Syntax.mk_binder _149_124))
in (_149_125)::[])
in (let _149_127 = (let _149_126 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _149_126))
in (FStar_Syntax_Util.arrow _149_128 _149_127)))
in (mk_gctx _149_129))
in (FStar_Syntax_Syntax.gen_bv "l" None _149_130))
in (

let r = (let _149_132 = (let _149_131 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _149_131))
in (FStar_Syntax_Syntax.gen_bv "r" None _149_132))
in (

let ret = (let _149_137 = (let _149_136 = (let _149_135 = (let _149_134 = (let _149_133 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _149_133))
in (FStar_Syntax_Syntax.mk_Total _149_134))
in (FStar_Syntax_Util.lcomp_of_comp _149_135))
in FStar_Util.Inl (_149_136))
in Some (_149_137))
in (

let outer_body = (

let gamma_as_args = (args_of_binders gamma)
in (

let inner_body = (let _149_143 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _149_142 = (let _149_141 = (let _149_140 = (let _149_139 = (let _149_138 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app _149_138 gamma_as_args))
in (FStar_Syntax_Syntax.as_arg _149_139))
in (_149_140)::[])
in (FStar_List.append gamma_as_args _149_141))
in (FStar_Syntax_Util.mk_app _149_143 _149_142)))
in (FStar_Syntax_Util.abs gamma inner_body ret)))
in (let _149_146 = (let _149_145 = (mk_all_implicit binders)
in (let _149_144 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((l), (false)))::(((r), (false)))::[]))
in (FStar_List.append _149_145 _149_144)))
in (FStar_Syntax_Util.abs _149_146 outer_body ret))))))))
in (

let _57_126 = (let _149_147 = (mk_lid "app")
in (register env _149_147 c_app))
in (match (_57_126) with
| (env, c_app) -> begin
(

let c_lift1 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _149_152 = (let _149_149 = (let _149_148 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _149_148))
in (_149_149)::[])
in (let _149_151 = (let _149_150 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _149_150))
in (FStar_Syntax_Util.arrow _149_152 _149_151)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _149_154 = (let _149_153 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _149_153))
in (FStar_Syntax_Syntax.gen_bv "a1" None _149_154))
in (

let ret = (let _149_159 = (let _149_158 = (let _149_157 = (let _149_156 = (let _149_155 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _149_155))
in (FStar_Syntax_Syntax.mk_Total _149_156))
in (FStar_Syntax_Util.lcomp_of_comp _149_157))
in FStar_Util.Inl (_149_158))
in Some (_149_159))
in (let _149_171 = (let _149_161 = (mk_all_implicit binders)
in (let _149_160 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::(((a1), (false)))::[]))
in (FStar_List.append _149_161 _149_160)))
in (let _149_170 = (let _149_169 = (let _149_168 = (let _149_167 = (let _149_164 = (let _149_163 = (let _149_162 = (FStar_Syntax_Syntax.bv_to_name f)
in (_149_162)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_163))
in (FStar_Syntax_Util.mk_app c_pure _149_164))
in (let _149_166 = (let _149_165 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_149_165)::[])
in (_149_167)::_149_166))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_168))
in (FStar_Syntax_Util.mk_app c_app _149_169))
in (FStar_Syntax_Util.abs _149_171 _149_170 ret)))))))))
in (

let _57_136 = (let _149_172 = (mk_lid "lift1")
in (register env _149_172 c_lift1))
in (match (_57_136) with
| (env, c_lift1) -> begin
(

let c_lift2 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t3 = (FStar_Syntax_Syntax.gen_bv "t3" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _149_180 = (let _149_177 = (let _149_173 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _149_173))
in (let _149_176 = (let _149_175 = (let _149_174 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.null_binder _149_174))
in (_149_175)::[])
in (_149_177)::_149_176))
in (let _149_179 = (let _149_178 = (FStar_Syntax_Syntax.bv_to_name t3)
in (FStar_Syntax_Syntax.mk_GTotal _149_178))
in (FStar_Syntax_Util.arrow _149_180 _149_179)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _149_182 = (let _149_181 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _149_181))
in (FStar_Syntax_Syntax.gen_bv "a1" None _149_182))
in (

let a2 = (let _149_184 = (let _149_183 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _149_183))
in (FStar_Syntax_Syntax.gen_bv "a2" None _149_184))
in (

let ret = (let _149_189 = (let _149_188 = (let _149_187 = (let _149_186 = (let _149_185 = (FStar_Syntax_Syntax.bv_to_name t3)
in (mk_gctx _149_185))
in (FStar_Syntax_Syntax.mk_Total _149_186))
in (FStar_Syntax_Util.lcomp_of_comp _149_187))
in FStar_Util.Inl (_149_188))
in Some (_149_189))
in (let _149_205 = (let _149_190 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((t3), (true)))::(((f), (false)))::(((a1), (false)))::(((a2), (false)))::[]))
in (FStar_List.append binders _149_190))
in (let _149_204 = (let _149_203 = (let _149_202 = (let _149_201 = (let _149_198 = (let _149_197 = (let _149_196 = (let _149_193 = (let _149_192 = (let _149_191 = (FStar_Syntax_Syntax.bv_to_name f)
in (_149_191)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_192))
in (FStar_Syntax_Util.mk_app c_pure _149_193))
in (let _149_195 = (let _149_194 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_149_194)::[])
in (_149_196)::_149_195))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_197))
in (FStar_Syntax_Util.mk_app c_app _149_198))
in (let _149_200 = (let _149_199 = (FStar_Syntax_Syntax.bv_to_name a2)
in (_149_199)::[])
in (_149_201)::_149_200))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_202))
in (FStar_Syntax_Util.mk_app c_app _149_203))
in (FStar_Syntax_Util.abs _149_205 _149_204 ret)))))))))))
in (

let _57_148 = (let _149_206 = (mk_lid "lift2")
in (register env _149_206 c_lift2))
in (match (_57_148) with
| (env, c_lift2) -> begin
(

let c_push = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _149_212 = (let _149_208 = (let _149_207 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _149_207))
in (_149_208)::[])
in (let _149_211 = (let _149_210 = (let _149_209 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _149_209))
in (FStar_Syntax_Syntax.mk_Total _149_210))
in (FStar_Syntax_Util.arrow _149_212 _149_211)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let ret = (let _149_222 = (let _149_221 = (let _149_220 = (let _149_219 = (let _149_218 = (let _149_217 = (let _149_214 = (let _149_213 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _149_213))
in (_149_214)::[])
in (let _149_216 = (let _149_215 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _149_215))
in (FStar_Syntax_Util.arrow _149_217 _149_216)))
in (mk_ctx _149_218))
in (FStar_Syntax_Syntax.mk_Total _149_219))
in (FStar_Syntax_Util.lcomp_of_comp _149_220))
in FStar_Util.Inl (_149_221))
in Some (_149_222))
in (

let e1 = (let _149_223 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" None _149_223))
in (

let body = (let _149_232 = (let _149_225 = (let _149_224 = (FStar_Syntax_Syntax.mk_binder e1)
in (_149_224)::[])
in (FStar_List.append gamma _149_225))
in (let _149_231 = (let _149_230 = (FStar_Syntax_Syntax.bv_to_name f)
in (let _149_229 = (let _149_228 = (let _149_226 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg _149_226))
in (let _149_227 = (args_of_binders gamma)
in (_149_228)::_149_227))
in (FStar_Syntax_Util.mk_app _149_230 _149_229)))
in (FStar_Syntax_Util.abs _149_232 _149_231 ret)))
in (let _149_235 = (let _149_234 = (mk_all_implicit binders)
in (let _149_233 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::[]))
in (FStar_List.append _149_234 _149_233)))
in (FStar_Syntax_Util.abs _149_235 body ret)))))))))
in (

let _57_159 = (let _149_236 = (mk_lid "push")
in (register env _149_236 c_push))
in (match (_57_159) with
| (env, c_push) -> begin
(

let ret_tot_wp_a = (let _149_239 = (let _149_238 = (let _149_237 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.lcomp_of_comp _149_237))
in FStar_Util.Inl (_149_238))
in Some (_149_239))
in (

let mk_generic_app = (fun c -> if ((FStar_List.length binders) > 0) then begin
(let _149_244 = (let _149_243 = (let _149_242 = (args_of_binders binders)
in ((c), (_149_242)))
in FStar_Syntax_Syntax.Tm_app (_149_243))
in (mk _149_244))
end else begin
c
end)
in (

let wp_if_then_else = (

let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (let _149_262 = (let _149_245 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (FStar_List.append binders _149_245))
in (let _149_261 = (

let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_unfoldable (2)) None)
in (let _149_260 = (let _149_251 = (let _149_250 = (let _149_249 = (let _149_248 = (let _149_247 = (let _149_246 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg _149_246))
in (_149_247)::[])
in (FStar_Syntax_Util.mk_app l_ite _149_248))
in (_149_249)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_250))
in (FStar_Syntax_Util.mk_app c_lift2 _149_251))
in (let _149_259 = (let _149_258 = (let _149_257 = (let _149_256 = (let _149_254 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _149_253 = (let _149_252 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_149_252)::[])
in (_149_254)::_149_253))
in (let _149_255 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _149_256 _149_255)))
in (FStar_Syntax_Syntax.mk_Total _149_257))
in FStar_Util.Inr (_149_258))
in (FStar_Syntax_Util.ascribe _149_260 _149_259))))
in (FStar_Syntax_Util.abs _149_262 _149_261 ret_tot_wp_a))))
in (

let _57_168 = (let _149_263 = (mk_lid "wp_if_then_else")
in (register env _149_263 wp_if_then_else))
in (match (_57_168) with
| (env, wp_if_then_else) -> begin
(

let wp_if_then_else = (mk_generic_app wp_if_then_else)
in (

let wp_assert = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_and = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.and_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (

let body = (let _149_274 = (let _149_273 = (let _149_272 = (let _149_269 = (let _149_268 = (let _149_267 = (let _149_266 = (let _149_265 = (let _149_264 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _149_264))
in (_149_265)::[])
in (FStar_Syntax_Util.mk_app l_and _149_266))
in (_149_267)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_268))
in (FStar_Syntax_Util.mk_app c_pure _149_269))
in (let _149_271 = (let _149_270 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_149_270)::[])
in (_149_272)::_149_271))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_273))
in (FStar_Syntax_Util.mk_app c_app _149_274))
in (let _149_276 = (let _149_275 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders _149_275))
in (FStar_Syntax_Util.abs _149_276 body ret_tot_wp_a))))))
in (

let _57_177 = (let _149_277 = (mk_lid "wp_assert")
in (register env _149_277 wp_assert))
in (match (_57_177) with
| (env, wp_assert) -> begin
(

let wp_assert = (mk_generic_app wp_assert)
in (

let wp_assume = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_imp = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.imp_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (

let body = (let _149_288 = (let _149_287 = (let _149_286 = (let _149_283 = (let _149_282 = (let _149_281 = (let _149_280 = (let _149_279 = (let _149_278 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _149_278))
in (_149_279)::[])
in (FStar_Syntax_Util.mk_app l_imp _149_280))
in (_149_281)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_282))
in (FStar_Syntax_Util.mk_app c_pure _149_283))
in (let _149_285 = (let _149_284 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_149_284)::[])
in (_149_286)::_149_285))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_287))
in (FStar_Syntax_Util.mk_app c_app _149_288))
in (let _149_290 = (let _149_289 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders _149_289))
in (FStar_Syntax_Util.abs _149_290 body ret_tot_wp_a))))))
in (

let _57_186 = (let _149_291 = (mk_lid "wp_assume")
in (register env _149_291 wp_assume))
in (match (_57_186) with
| (env, wp_assume) -> begin
(

let wp_assume = (mk_generic_app wp_assume)
in (

let wp_close = (

let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _149_295 = (let _149_293 = (let _149_292 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _149_292))
in (_149_293)::[])
in (let _149_294 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _149_295 _149_294)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let body = (let _149_304 = (let _149_303 = (let _149_302 = (let _149_296 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((FStar_Syntax_Util.tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure _149_296))
in (let _149_301 = (let _149_300 = (let _149_299 = (let _149_298 = (let _149_297 = (FStar_Syntax_Syntax.bv_to_name f)
in (_149_297)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_298))
in (FStar_Syntax_Util.mk_app c_push _149_299))
in (_149_300)::[])
in (_149_302)::_149_301))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_303))
in (FStar_Syntax_Util.mk_app c_app _149_304))
in (let _149_306 = (let _149_305 = (FStar_Syntax_Syntax.binders_of_list ((a)::(b)::(f)::[]))
in (FStar_List.append binders _149_305))
in (FStar_Syntax_Util.abs _149_306 body ret_tot_wp_a))))))
in (

let _57_195 = (let _149_307 = (mk_lid "wp_close")
in (register env _149_307 wp_close))
in (match (_57_195) with
| (env, wp_close) -> begin
(

let wp_close = (mk_generic_app wp_close)
in (

let ret_tot_type = (let _149_310 = (let _149_309 = (let _149_308 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _149_308))
in FStar_Util.Inl (_149_309))
in Some (_149_310))
in (

let mk_forall = (fun x body -> (let _149_321 = (let _149_320 = (let _149_319 = (let _149_318 = (let _149_317 = (let _149_316 = (let _149_315 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_315)::[])
in (FStar_Syntax_Util.abs _149_316 body ret_tot_type))
in (FStar_Syntax_Syntax.as_arg _149_317))
in (_149_318)::[])
in ((FStar_Syntax_Util.tforall), (_149_319)))
in FStar_Syntax_Syntax.Tm_app (_149_320))
in (FStar_Syntax_Syntax.mk _149_321 None FStar_Range.dummyRange)))
in (

let rec mk_leq = (fun t x y -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (match ((let _149_328 = (FStar_Syntax_Subst.compress t)
in _149_328.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_207) -> begin
(FStar_Syntax_Util.mk_imp x y)
end
| (FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) when (FStar_Syntax_Syntax.is_null_binder binder) -> begin
(

let a = (Prims.fst binder).FStar_Syntax_Syntax.sort
in (

let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (

let a2 = (FStar_Syntax_Syntax.gen_bv "a2" None a)
in (

let body = (let _149_340 = (let _149_330 = (FStar_Syntax_Syntax.bv_to_name a1)
in (let _149_329 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_leq a _149_330 _149_329)))
in (let _149_339 = (let _149_338 = (let _149_333 = (let _149_332 = (let _149_331 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _149_331))
in (_149_332)::[])
in (FStar_Syntax_Util.mk_app x _149_333))
in (let _149_337 = (let _149_336 = (let _149_335 = (let _149_334 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg _149_334))
in (_149_335)::[])
in (FStar_Syntax_Util.mk_app y _149_336))
in (mk_leq b _149_338 _149_337)))
in (FStar_Syntax_Util.mk_imp _149_340 _149_339)))
in (let _149_341 = (mk_forall a2 body)
in (mk_forall a1 _149_341))))))
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::binders, comp) -> begin
(

let t = (

let _57_243 = t
in (let _149_345 = (let _149_344 = (let _149_343 = (let _149_342 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _149_342))
in (((binder)::[]), (_149_343)))
in FStar_Syntax_Syntax.Tm_arrow (_149_344))
in {FStar_Syntax_Syntax.n = _149_345; FStar_Syntax_Syntax.tk = _57_243.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_243.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_243.FStar_Syntax_Syntax.vars}))
in (mk_leq t x y))
end
| FStar_Syntax_Syntax.Tm_arrow (_57_247) -> begin
(FStar_All.failwith "unhandled arrow")
end
| _57_250 -> begin
(FStar_Syntax_Util.mk_eq t t x y)
end)))
in (

let stronger = (

let wp1 = (FStar_Syntax_Syntax.gen_bv "wp1" None wp_a)
in (

let wp2 = (FStar_Syntax_Syntax.gen_bv "wp2" None wp_a)
in (

let body = (let _149_347 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (let _149_346 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_leq wp_a _149_347 _149_346)))
in (let _149_349 = (let _149_348 = (binders_of_list ((((a), (false)))::(((wp1), (false)))::(((wp2), (false)))::[]))
in (FStar_List.append binders _149_348))
in (FStar_Syntax_Util.abs _149_349 body ret_tot_type)))))
in (

let _57_257 = (let _149_350 = (mk_lid "stronger")
in (register env _149_350 stronger))
in (match (_57_257) with
| (env, stronger) -> begin
(

let stronger = (mk_generic_app stronger)
in (

let null_wp = (Prims.snd ed.FStar_Syntax_Syntax.null_wp)
in (

let wp_trivial = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let body = (let _149_360 = (let _149_359 = (let _149_358 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _149_357 = (let _149_356 = (let _149_353 = (let _149_352 = (let _149_351 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg _149_351))
in (_149_352)::[])
in (FStar_Syntax_Util.mk_app null_wp _149_353))
in (let _149_355 = (let _149_354 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_149_354)::[])
in (_149_356)::_149_355))
in (_149_358)::_149_357))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_359))
in (FStar_Syntax_Util.mk_app stronger _149_360))
in (let _149_362 = (let _149_361 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders _149_361))
in (FStar_Syntax_Util.abs _149_362 body ret_tot_type))))
in (

let _57_265 = (let _149_363 = (mk_lid "wp_trivial")
in (register env _149_363 wp_trivial))
in (match (_57_265) with
| (env, wp_trivial) -> begin
(

let wp_trivial = (mk_generic_app wp_trivial)
in (

let _57_267 = (d "End Dijkstra monads for free")
in ((env), ((

let _57_269 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_269.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_269.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_269.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_269.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_269.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _57_269.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _57_269.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = (([]), (wp_if_then_else)); FStar_Syntax_Syntax.ite_wp = _57_269.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = (([]), (stronger)); FStar_Syntax_Syntax.close_wp = (([]), (wp_close)); FStar_Syntax_Syntax.assert_p = (([]), (wp_assert)); FStar_Syntax_Syntax.assume_p = (([]), (wp_assume)); FStar_Syntax_Syntax.null_wp = _57_269.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = (([]), (wp_trivial)); FStar_Syntax_Syntax.repr = _57_269.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _57_269.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _57_269.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _57_269.FStar_Syntax_Syntax.actions})))))
end)))))
end)))))))
end))))
end))))
end))))
end)))))
end)))
end)))
end)))
end)))
end)))
end)))))))))))))))))))


type env =
{env : FStar_TypeChecker_Env.env; definitions : (FStar_Ident.lid * FStar_Syntax_Syntax.typ) Prims.list; subst : FStar_Syntax_Syntax.subst_elt Prims.list; tc_const : FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))


let empty : FStar_TypeChecker_Env.env  ->  (FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ)  ->  env = (fun env tc_const -> {env = env; definitions = []; subst = []; tc_const = tc_const})


type env_ =
env


type nm =
| N of FStar_Syntax_Syntax.typ
| M of FStar_Syntax_Syntax.typ


let is_N = (fun _discr_ -> (match (_discr_) with
| N (_) -> begin
true
end
| _ -> begin
false
end))


let is_M = (fun _discr_ -> (match (_discr_) with
| M (_) -> begin
true
end
| _ -> begin
false
end))


let ___N____0 = (fun projectee -> (match (projectee) with
| N (_57_280) -> begin
_57_280
end))


let ___M____0 = (fun projectee -> (match (projectee) with
| M (_57_283) -> begin
_57_283
end))


type nm_ =
nm


let nm_of_comp : FStar_Syntax_Syntax.comp'  ->  nm = (fun _57_1 -> (match (_57_1) with
| FStar_Syntax_Syntax.Total (t) -> begin
N (t)
end
| FStar_Syntax_Syntax.Comp (c) when (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.monadic_lid) -> begin
M (c.FStar_Syntax_Syntax.result_typ)
end
| _57_290 -> begin
(FStar_All.failwith "[nm_of_comp]: impossible")
end))


let string_of_nm : nm  ->  Prims.string = (fun _57_2 -> (match (_57_2) with
| N (t) -> begin
(let _149_424 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "N[%s]" _149_424))
end
| M (t) -> begin
(let _149_425 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "M[%s]" _149_425))
end))


let is_monadic_arrow : FStar_Syntax_Syntax.term'  ->  nm = (fun n -> (match (n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_298, {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_304; FStar_Syntax_Syntax.pos = _57_302; FStar_Syntax_Syntax.vars = _57_300}) -> begin
(nm_of_comp n)
end
| _57_310 -> begin
(FStar_All.failwith "unexpected_argument: [is_monadic_arrow]")
end))


let is_monadic_comp = (fun c -> (match ((nm_of_comp c.FStar_Syntax_Syntax.n)) with
| M (_57_313) -> begin
true
end
| N (_57_316) -> begin
false
end))


let rec mk_star_to_type : (FStar_Syntax_Syntax.term'  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun mk env a -> (let _149_449 = (let _149_448 = (let _149_447 = (let _149_445 = (let _149_444 = (let _149_442 = (star_type env a)
in (FStar_Syntax_Syntax.null_bv _149_442))
in (let _149_443 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_444), (_149_443))))
in (_149_445)::[])
in (let _149_446 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_149_447), (_149_446))))
in FStar_Syntax_Syntax.Tm_arrow (_149_448))
in (mk _149_449)))
and star_type : env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None t.FStar_Syntax_Syntax.pos))
in (

let mk_star_to_type = (mk_star_to_type mk)
in (

let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.env)
in (

let t = (normalize t)
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _57_331) -> begin
(

let binders = (FStar_List.map (fun _57_336 -> (match (_57_336) with
| (bv, aqual) -> begin
(let _149_459 = (

let _57_337 = bv
in (let _149_458 = (star_type env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_337.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_337.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_458}))
in ((_149_459), (aqual)))
end)) binders)
in (match ((is_monadic_arrow t.FStar_Syntax_Syntax.n)) with
| N (hn) -> begin
(let _149_463 = (let _149_462 = (let _149_461 = (let _149_460 = (star_type env hn)
in (FStar_Syntax_Syntax.mk_Total _149_460))
in ((binders), (_149_461)))
in FStar_Syntax_Syntax.Tm_arrow (_149_462))
in (mk _149_463))
end
| M (a) -> begin
(let _149_472 = (let _149_471 = (let _149_470 = (let _149_468 = (let _149_467 = (let _149_466 = (let _149_464 = (mk_star_to_type env a)
in (FStar_Syntax_Syntax.null_bv _149_464))
in (let _149_465 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_466), (_149_465))))
in (_149_467)::[])
in (FStar_List.append binders _149_468))
in (let _149_469 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_149_470), (_149_469))))
in FStar_Syntax_Syntax.Tm_arrow (_149_471))
in (mk _149_472))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let is_valid_application = (fun head -> (match ((let _149_475 = (FStar_Syntax_Subst.compress head)
in _149_475.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.option_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.either_lid)) || (let _149_476 = (FStar_Syntax_Subst.compress head)
in (FStar_Syntax_Util.is_tuple_constructor _149_476))) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uinst (_57_353) -> begin
(FStar_All.failwith "impossible")
end
| _57_356 -> begin
false
end))
in if (is_valid_application head) then begin
(let _149_481 = (let _149_480 = (let _149_479 = (FStar_List.map (fun _57_359 -> (match (_57_359) with
| (t, qual) -> begin
(let _149_478 = (star_type env t)
in ((_149_478), (qual)))
end)) args)
in ((head), (_149_479)))
in FStar_Syntax_Syntax.Tm_app (_149_480))
in (mk _149_481))
end else begin
(let _149_484 = (let _149_483 = (let _149_482 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "For now, only [either] and [option] are supported in the definition language (got: %s)" _149_482))
in FStar_Syntax_Syntax.Err (_149_483))
in (Prims.raise _149_484))
end)
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_abs (binders, repr, something) -> begin
(

let subst = (FStar_Syntax_Subst.opening_of_binders binders)
in (

let repr = (FStar_Syntax_Subst.subst subst repr)
in (

let env = (

let _57_379 = env
in (let _149_485 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _149_485; definitions = _57_379.definitions; subst = _57_379.subst; tc_const = _57_379.tc_const}))
in (

let repr = (star_type env repr)
in (

let repr = (FStar_Syntax_Subst.close binders repr)
in (mk (FStar_Syntax_Syntax.Tm_abs (((binders), (repr), (something))))))))))
end
| (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_match (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _149_488 = (let _149_487 = (let _149_486 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "The following term is outside of the definition language: %s" _149_486))
in FStar_Syntax_Syntax.Err (_149_487))
in (Prims.raise _149_488))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_413) -> begin
(FStar_All.failwith "impossible")
end)))))))


let star_definition = (fun env t f -> (match ((let _149_502 = (let _149_501 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.env t)
in (FStar_Syntax_Subst.compress _149_501))
in _149_502.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = lid; FStar_Syntax_Syntax.fv_delta = _57_421; FStar_Syntax_Syntax.fv_qual = _57_419}) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.NoInline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.env t)
in (

let _57_426 = (FStar_Util.print1 "Recording definition of %s\n" (FStar_Ident.text_of_lid lid.FStar_Syntax_Syntax.v))
in (

let _57_430 = (f env t)
in (match (_57_430) with
| (keep, ret) -> begin
(((

let _57_431 = env
in {env = _57_431.env; definitions = (((lid.FStar_Syntax_Syntax.v), (keep)))::env.definitions; subst = _57_431.subst; tc_const = _57_431.tc_const})), (ret))
end))))
end
| _57_434 -> begin
(let _149_505 = (let _149_504 = (let _149_503 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Ill-formed definition: %s" _149_503))
in FStar_Syntax_Syntax.Err (_149_504))
in (Prims.raise _149_505))
end))


let star_type_definition : env  ->  FStar_Syntax_Syntax.term  ->  (env * FStar_Syntax_Syntax.term) = (fun env t -> (star_definition env t (fun env e -> (

let t = (star_type env e)
in ((t), (t))))))


let is_monadic : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  Prims.bool = (fun _57_3 -> (match (_57_3) with
| None -> begin
(FStar_All.failwith "un-annotated lambda?!")
end
| (Some (FStar_Util.Inl ({FStar_Syntax_Syntax.eff_name = lid; FStar_Syntax_Syntax.res_typ = _; FStar_Syntax_Syntax.cflags = _; FStar_Syntax_Syntax.comp = _}))) | (Some (FStar_Util.Inr (lid))) -> begin
(FStar_Ident.lid_equals lid FStar_Syntax_Const.monadic_lid)
end))


let rec is_C : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match ((let _149_516 = (FStar_Syntax_Subst.compress t)
in _149_516.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) when (FStar_Syntax_Util.is_tuple_constructor head) -> begin
(

let r = (let _149_518 = (let _149_517 = (FStar_List.hd args)
in (Prims.fst _149_517))
in (is_C _149_518))
in if r then begin
(

let _57_464 = if (not ((FStar_List.for_all (fun _57_463 -> (match (_57_463) with
| (h, _57_462) -> begin
(is_C h)
end)) args))) then begin
(FStar_All.failwith "not a C (A * C)")
end else begin
()
end
in true)
end else begin
(

let _57_470 = if (not ((FStar_List.for_all (fun _57_469 -> (match (_57_469) with
| (h, _57_468) -> begin
(not ((is_C h)))
end)) args))) then begin
(FStar_All.failwith "not a C (C * A)")
end else begin
()
end
in false)
end)
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(match ((nm_of_comp comp.FStar_Syntax_Syntax.n)) with
| M (t) -> begin
(

let _57_478 = if (is_C t) then begin
(FStar_All.failwith "not a C (C -> C)")
end else begin
()
end
in true)
end
| N (t) -> begin
(is_C t)
end)
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_uinst (t, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t, _, _)) -> begin
(is_C t)
end
| _57_498 -> begin
false
end))


let mk_return : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let p_type = (mk_star_to_type mk env t)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'" None p_type)
in (

let body = (let _149_534 = (let _149_533 = (let _149_532 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _149_531 = (let _149_530 = (let _149_529 = (FStar_Syntax_Syntax.as_implicit false)
in ((e), (_149_529)))
in (_149_530)::[])
in ((_149_532), (_149_531))))
in FStar_Syntax_Syntax.Tm_app (_149_533))
in (mk _149_534))
in (let _149_536 = (let _149_535 = (FStar_Syntax_Syntax.mk_binder p)
in (_149_535)::[])
in (FStar_Syntax_Util.abs _149_536 body None)))))))


let is_unknown : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun _57_4 -> (match (_57_4) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| _57_510 -> begin
false
end))


let rec check : env  ->  FStar_Syntax_Syntax.term  ->  nm  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e context_nm -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let return_if = (fun _57_520 -> (match (_57_520) with
| (rec_nm, s_e, u_e) -> begin
(

let check = (fun t1 t2 -> if ((not ((is_unknown t2.FStar_Syntax_Syntax.n))) && (not ((let _149_590 = (FStar_TypeChecker_Rel.teq env.env t1 t2)
in (FStar_TypeChecker_Rel.is_trivial _149_590))))) then begin
(let _149_595 = (let _149_594 = (let _149_593 = (FStar_Syntax_Print.term_to_string e)
in (let _149_592 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_591 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check]: the expression [%s] has type [%s] but should have type [%s]" _149_593 _149_592 _149_591))))
in FStar_Syntax_Syntax.Err (_149_594))
in (Prims.raise _149_595))
end else begin
()
end)
in (match (((rec_nm), (context_nm))) with
| ((N (t1), N (t2))) | ((M (t1), M (t2))) -> begin
(

let _57_532 = (check t1 t2)
in ((rec_nm), (s_e), (u_e)))
end
| (N (t1), M (t2)) -> begin
(

let _57_539 = (check t1 t2)
in (let _149_596 = (mk_return env t1 s_e)
in ((M (t1)), (_149_596), (u_e))))
end
| (M (t1), N (t2)) -> begin
(let _149_601 = (let _149_600 = (let _149_599 = (FStar_Syntax_Print.term_to_string e)
in (let _149_598 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_597 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]" _149_599 _149_598 _149_597))))
in FStar_Syntax_Syntax.Err (_149_600))
in (Prims.raise _149_601))
end))
end))
in (match ((let _149_602 = (FStar_Syntax_Subst.compress e)
in _149_602.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
(let _149_603 = (infer env e)
in (return_if _149_603))
end
| FStar_Syntax_Syntax.Tm_let ((false, (binding)::[]), e2) -> begin
(mk_let env binding e2 (fun env e2 -> (check env e2 context_nm)) (fun env e2 -> (

let strip_m = (fun _57_5 -> (match (_57_5) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_580 -> begin
(FStar_All.failwith "impossible")
end))
in (match (context_nm) with
| N (t) -> begin
(let _149_610 = (check env e2 (M (t)))
in (strip_m _149_610))
end
| M (_57_585) -> begin
(let _149_611 = (check env e2 context_nm)
in (strip_m _149_611))
end))))
end
| FStar_Syntax_Syntax.Tm_match (e0, branches) -> begin
(mk_match env e0 branches (fun env body -> (check env body context_nm)))
end
| (FStar_Syntax_Syntax.Tm_meta (e, _)) | (FStar_Syntax_Syntax.Tm_uinst (e, _)) | (FStar_Syntax_Syntax.Tm_ascribed (e, _, _)) -> begin
(check env e context_nm)
end
| FStar_Syntax_Syntax.Tm_let (_57_611) -> begin
(let _149_617 = (let _149_616 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_let %s" _149_616))
in (FStar_All.failwith _149_617))
end
| FStar_Syntax_Syntax.Tm_type (_57_614) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_617) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_57_620) -> begin
(let _149_619 = (let _149_618 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_refine %s" _149_618))
in (FStar_All.failwith _149_619))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_623) -> begin
(let _149_621 = (let _149_620 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_uvar %s" _149_620))
in (FStar_All.failwith _149_621))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_626) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _149_626 = (let _149_625 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_unknown %s" _149_625))
in (FStar_All.failwith _149_626))
end))))
and infer : env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.env)
in (match ((let _149_632 = (FStar_Syntax_Subst.compress e)
in _149_632.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(FStar_All.failwith "I failed to open a binder... boo")
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

let _57_646 = env
in (let _149_633 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _149_633; definitions = _57_646.definitions; subst = _57_646.subst; tc_const = _57_646.tc_const}))
in (

let s_binders = (FStar_List.map (fun _57_651 -> (match (_57_651) with
| (bv, qual) -> begin
(

let sort = (star_type env bv.FStar_Syntax_Syntax.sort)
in (((

let _57_653 = bv
in {FStar_Syntax_Syntax.ppname = _57_653.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_653.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (qual)))
end)) binders)
in (

let _57_675 = (FStar_List.fold_left (fun _57_658 _57_661 -> (match (((_57_658), (_57_661))) with
| ((env, acc), (bv, qual)) -> begin
(

let c = (normalize bv.FStar_Syntax_Syntax.sort)
in if (is_C c) then begin
(

let xw = (let _149_637 = (star_type env c)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "^w") None _149_637))
in (

let x = (

let _57_664 = bv
in (let _149_639 = (let _149_638 = (FStar_Syntax_Syntax.bv_to_name xw)
in (trans_F env c _149_638))
in {FStar_Syntax_Syntax.ppname = _57_664.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_664.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_639}))
in (

let env = (

let _57_667 = env
in (let _149_643 = (let _149_642 = (let _149_641 = (let _149_640 = (FStar_Syntax_Syntax.bv_to_name xw)
in ((bv), (_149_640)))
in FStar_Syntax_Syntax.NT (_149_641))
in (_149_642)::env.subst)
in {env = _57_667.env; definitions = _57_667.definitions; subst = _149_643; tc_const = _57_667.tc_const}))
in (let _149_647 = (let _149_646 = (FStar_Syntax_Syntax.mk_binder x)
in (let _149_645 = (let _149_644 = (FStar_Syntax_Syntax.mk_binder xw)
in (_149_644)::acc)
in (_149_646)::_149_645))
in ((env), (_149_647))))))
end else begin
(

let x = (

let _57_670 = bv
in (let _149_648 = (star_type env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_670.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_670.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_648}))
in (let _149_650 = (let _149_649 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_649)::acc)
in ((env), (_149_650))))
end)
end)) ((env), ([])) binders)
in (match (_57_675) with
| (env, u_binders) -> begin
(

let u_binders = (FStar_List.rev u_binders)
in (

let _57_685 = (

let check_what = if (is_monadic what) then begin
check_m
end else begin
check_n
end
in (

let _57_681 = (check_what env body)
in (match (_57_681) with
| (t, s_body, u_body) -> begin
(let _149_656 = (let _149_655 = if (is_monadic what) then begin
M (t)
end else begin
N (t)
end
in (comp_of_nm _149_655))
in ((_149_656), (s_body), (u_body)))
end)))
in (match (_57_685) with
| (comp, s_body, u_body) -> begin
(

let t = (

let binders = (FStar_List.map (fun _57_689 -> (match (_57_689) with
| (bv, _57_688) -> begin
(let _149_659 = (let _149_658 = (normalize bv.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.null_bv _149_658))
in (FStar_Syntax_Syntax.mk_binder _149_659))
end)) binders)
in (

let binders = (FStar_Syntax_Subst.close_binders binders)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))))))
in (

let s_body = (FStar_Syntax_Subst.close s_binders s_body)
in (

let s_binders = (FStar_Syntax_Subst.close_binders s_binders)
in (

let s_term = (mk (FStar_Syntax_Syntax.Tm_abs (((s_binders), (s_body), (what)))))
in (

let u_body = (FStar_Syntax_Subst.close u_binders u_body)
in (

let u_binders = (FStar_Syntax_Subst.close_binders u_binders)
in (

let u_term = (mk (FStar_Syntax_Syntax.Tm_abs (((u_binders), (u_body), (what)))))
in ((N (t)), (s_term), (u_term)))))))))
end)))
end)))))))
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = {FStar_Syntax_Syntax.v = lid; FStar_Syntax_Syntax.ty = _57_706; FStar_Syntax_Syntax.p = _57_704}; FStar_Syntax_Syntax.fv_delta = _57_702; FStar_Syntax_Syntax.fv_qual = _57_700}) -> begin
(match ((FStar_List.find (fun _57_714 -> (match (_57_714) with
| (lid', _57_713) -> begin
(FStar_Ident.lid_equals lid lid')
end)) env.definitions)) with
| Some (_57_716, t) -> begin
((N (t)), (e), (e))
end
| None -> begin
(

let _57_724 = (FStar_TypeChecker_Env.lookup_lid env.env lid)
in (match (_57_724) with
| (_57_722, t) -> begin
(

let txt = (FStar_Ident.text_of_lid lid)
in (

let allowed_prefixes = ("Mktuple")::("Left")::("Right")::("Some")::("None")::[]
in if (FStar_List.existsb (fun s -> (FStar_Util.starts_with txt (Prims.strcat "Prims." s))) allowed_prefixes) then begin
((N (t)), (e), (e))
end else begin
(let _149_663 = (let _149_662 = (FStar_Util.format1 "The %s constructor has not been whitelisted for the definition language" txt)
in FStar_Syntax_Syntax.Err (_149_662))
in (Prims.raise _149_663))
end))
end))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_735 = (check_n env head)
in (match (_57_735) with
| (t_head, s_head, u_head) -> begin
(

let t_head = (normalize t_head)
in (

let is_arrow = (fun t -> (match ((let _149_666 = (FStar_Syntax_Subst.compress t)
in _149_666.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_740) -> begin
true
end
| _57_743 -> begin
false
end))
in (

let rec flatten = (fun t -> (match ((let _149_669 = (FStar_Syntax_Subst.compress t)
in _149_669.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (t); FStar_Syntax_Syntax.tk = _57_752; FStar_Syntax_Syntax.pos = _57_750; FStar_Syntax_Syntax.vars = _57_748}) when (is_arrow t) -> begin
(

let _57_760 = (flatten t)
in (match (_57_760) with
| (binders', comp) -> begin
(((FStar_List.append binders binders')), (comp))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
((binders), (comp))
end
| _57_766 -> begin
(let _149_672 = (let _149_671 = (let _149_670 = (FStar_Syntax_Print.term_to_string t_head)
in (FStar_Util.format1 "%s: not a function type" _149_670))
in FStar_Syntax_Syntax.Err (_149_671))
in (Prims.raise _149_672))
end))
in (

let _57_769 = (flatten t_head)
in (match (_57_769) with
| (binders, comp) -> begin
(

let n = (FStar_List.length binders)
in (

let n' = (FStar_List.length args)
in (

let _57_772 = if ((FStar_List.length binders) < (FStar_List.length args)) then begin
(let _149_677 = (let _149_676 = (let _149_675 = (FStar_Util.string_of_int n)
in (let _149_674 = (FStar_Util.string_of_int (n' - n))
in (let _149_673 = (FStar_Util.string_of_int n)
in (FStar_Util.format3 "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments." _149_675 _149_674 _149_673))))
in FStar_Syntax_Syntax.Err (_149_676))
in (Prims.raise _149_677))
end else begin
()
end
in (

let _57_776 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (_57_776) with
| (binders, comp) -> begin
(

let rec final_type = (fun subst _57_781 args -> (match (_57_781) with
| (binders, comp) -> begin
(match (((binders), (args))) with
| ([], []) -> begin
(let _149_685 = (let _149_684 = (FStar_Syntax_Subst.subst_comp subst comp)
in _149_684.FStar_Syntax_Syntax.n)
in (nm_of_comp _149_685))
end
| (binders, []) -> begin
(match ((let _149_688 = (let _149_687 = (let _149_686 = (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))))
in (FStar_Syntax_Subst.subst subst _149_686))
in (FStar_Syntax_Subst.compress _149_687))
in _149_688.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(let _149_692 = (let _149_691 = (let _149_690 = (let _149_689 = (FStar_Syntax_Subst.close_comp binders comp)
in ((binders), (_149_689)))
in FStar_Syntax_Syntax.Tm_arrow (_149_690))
in (mk _149_691))
in N (_149_692))
end
| _57_794 -> begin
(FStar_All.failwith "wat?")
end)
end
| ([], (_57_799)::_57_797) -> begin
(FStar_All.failwith "just checked that?!")
end
| (((bv, _57_805))::binders, ((arg, _57_811))::args) -> begin
(final_type ((FStar_Syntax_Syntax.NT (((bv), (arg))))::subst) ((binders), (comp)) args)
end)
end))
in (

let final_type = (final_type [] ((binders), (comp)) args)
in (

let _57_836 = (let _149_709 = (FStar_List.map2 (fun _57_819 _57_822 -> (match (((_57_819), (_57_822))) with
| ((bv, _57_818), (arg, q)) -> begin
(match ((let _149_696 = (let _149_695 = (normalize bv.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Subst.compress _149_695))
in _149_696.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_824) -> begin
(

let arg = (let _149_697 = (normalize arg)
in ((_149_697), (q)))
in ((arg), ((arg)::[])))
end
| _57_828 -> begin
(

let _57_833 = (check_n env arg)
in (match (_57_833) with
| (_57_830, s_arg, u_arg) -> begin
(let _149_708 = (let _149_698 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_arg), (_149_698)))
in (let _149_707 = if (is_C bv.FStar_Syntax_Syntax.sort) then begin
(let _149_704 = (let _149_700 = (FStar_Syntax_Subst.subst env.subst s_arg)
in (let _149_699 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_700), (_149_699))))
in (let _149_703 = (let _149_702 = (let _149_701 = (FStar_Syntax_Syntax.as_implicit false)
in ((u_arg), (_149_701)))
in (_149_702)::[])
in (_149_704)::_149_703))
end else begin
(let _149_706 = (let _149_705 = (FStar_Syntax_Syntax.as_implicit false)
in ((u_arg), (_149_705)))
in (_149_706)::[])
end
in ((_149_708), (_149_707))))
end))
end)
end)) binders args)
in (FStar_List.split _149_709))
in (match (_57_836) with
| (s_args, u_args) -> begin
(

let u_args = (FStar_List.flatten u_args)
in (let _149_711 = (mk (FStar_Syntax_Syntax.Tm_app (((s_head), (s_args)))))
in (let _149_710 = (mk (FStar_Syntax_Syntax.Tm_app (((u_head), (u_args)))))
in ((final_type), (_149_711), (_149_710)))))
end))))
end)))))
end)))))
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
(let _149_713 = (let _149_712 = (env.tc_const c)
in N (_149_712))
in ((_149_713), (e), (e)))
end
| FStar_Syntax_Syntax.Tm_let (_57_867) -> begin
(let _149_715 = (let _149_714 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_let %s" _149_714))
in (FStar_All.failwith _149_715))
end
| FStar_Syntax_Syntax.Tm_type (_57_870) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_873) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_57_876) -> begin
(let _149_717 = (let _149_716 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_refine %s" _149_716))
in (FStar_All.failwith _149_717))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_879) -> begin
(let _149_719 = (let _149_718 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_uvar %s" _149_718))
in (FStar_All.failwith _149_719))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_882) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _149_724 = (let _149_723 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_unknown %s" _149_723))
in (FStar_All.failwith _149_724))
end))))
and mk_match : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e0 branches f -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e0.FStar_Syntax_Syntax.pos))
in (

let _57_895 = (check_n env e0)
in (match (_57_895) with
| (_57_892, s_e0, u_e0) -> begin
(

let _57_912 = (let _149_740 = (FStar_List.map (fun b -> (match ((FStar_Syntax_Subst.open_branch b)) with
| (pat, None, body) -> begin
(

let env = (

let _57_901 = env
in (let _149_739 = (let _149_738 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env.env _149_738))
in {env = _149_739; definitions = _57_901.definitions; subst = _57_901.subst; tc_const = _57_901.tc_const}))
in (

let _57_907 = (f env body)
in (match (_57_907) with
| (nm, s_body, u_body) -> begin
((nm), (((pat), (None), (((s_body), (u_body))))))
end)))
end
| _57_909 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("No when clauses in the definition language")))
end)) branches)
in (FStar_List.split _149_740))
in (match (_57_912) with
| (nms, branches) -> begin
(

let t1 = (match ((FStar_List.hd nms)) with
| (M (t1)) | (N (t1)) -> begin
t1
end)
in (

let has_m = (FStar_List.existsb (fun _57_6 -> (match (_57_6) with
| M (_57_919) -> begin
true
end
| _57_922 -> begin
false
end)) nms)
in (

let _57_957 = (let _149_751 = (FStar_List.map2 (fun nm _57_930 -> (match (_57_930) with
| (pat, guard, (s_body, u_body)) -> begin
(

let check = (fun t t' -> if (not ((let _149_748 = (FStar_TypeChecker_Rel.teq env.env t' t)
in (FStar_TypeChecker_Rel.is_trivial _149_748)))) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("[infer]: branches do not have the same type")))
end else begin
()
end)
in (match (((nm), (has_m))) with
| ((N (t2), false)) | ((M (t2), true)) -> begin
(

let _57_941 = (check t2 t1)
in ((nm), (((pat), (guard), (s_body))), (((pat), (guard), (u_body)))))
end
| (N (t2), true) -> begin
(

let _57_947 = (check t2 t1)
in (let _149_750 = (let _149_749 = (mk_return env t2 s_body)
in ((pat), (guard), (_149_749)))
in ((M (t2)), (_149_750), (((pat), (guard), (u_body))))))
end
| (M (_57_950), false) -> begin
(FStar_All.failwith "impossible")
end))
end)) nms branches)
in (FStar_List.unzip3 _149_751))
in (match (_57_957) with
| (nms, s_branches, u_branches) -> begin
(

let s_branches = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (let _149_753 = (mk (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches)))))
in (let _149_752 = (mk (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches)))))
in ((if has_m then begin
M (t1)
end else begin
N (t1)
end), (_149_753), (_149_752))))))
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

let x_binders = (let _149_773 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_773)::[])
in (

let _57_972 = (FStar_Syntax_Subst.open_term x_binders e2)
in (match (_57_972) with
| (x_binders, e2) -> begin
(match ((infer env e1)) with
| (N (t1), s_e1, u_e1) -> begin
(

let env = (

let _57_978 = env
in (let _149_774 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_980 = x
in {FStar_Syntax_Syntax.ppname = _57_980.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_980.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _149_774; definitions = _57_978.definitions; subst = _57_978.subst; tc_const = _57_978.tc_const}))
in (

let _57_986 = (proceed env e2)
in (match (_57_986) with
| (nm_rec, s_e2, u_e2) -> begin
(let _149_782 = (let _149_777 = (let _149_776 = (let _149_775 = (FStar_Syntax_Subst.close x_binders s_e2)
in ((((false), (((

let _57_987 = binding
in {FStar_Syntax_Syntax.lbname = _57_987.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_987.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_987.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_987.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = s_e1}))::[]))), (_149_775)))
in FStar_Syntax_Syntax.Tm_let (_149_776))
in (mk _149_777))
in (let _149_781 = (let _149_780 = (let _149_779 = (let _149_778 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _57_989 = binding
in {FStar_Syntax_Syntax.lbname = _57_989.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_989.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_989.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_989.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_149_778)))
in FStar_Syntax_Syntax.Tm_let (_149_779))
in (mk _149_780))
in ((nm_rec), (_149_782), (_149_781))))
end)))
end
| (M (t1), s_e1, u_e1) -> begin
(

let env = (

let _57_996 = env
in (let _149_783 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_998 = x
in {FStar_Syntax_Syntax.ppname = _57_998.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_998.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _149_783; definitions = _57_996.definitions; subst = _57_996.subst; tc_const = _57_996.tc_const}))
in (

let _57_1004 = (ensure_m env e2)
in (match (_57_1004) with
| (t2, s_e2, u_e2) -> begin
(

let p_type = (mk_star_to_type mk env t2)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" None p_type)
in (

let s_e2 = (let _149_789 = (let _149_788 = (let _149_787 = (let _149_786 = (let _149_785 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _149_784 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_785), (_149_784))))
in (_149_786)::[])
in ((s_e2), (_149_787)))
in FStar_Syntax_Syntax.Tm_app (_149_788))
in (mk _149_789))
in (

let s_e2 = (FStar_Syntax_Util.abs x_binders s_e2 None)
in (

let body = (let _149_794 = (let _149_793 = (let _149_792 = (let _149_791 = (let _149_790 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_e2), (_149_790)))
in (_149_791)::[])
in ((s_e1), (_149_792)))
in FStar_Syntax_Syntax.Tm_app (_149_793))
in (mk _149_794))
in (let _149_801 = (let _149_796 = (let _149_795 = (FStar_Syntax_Syntax.mk_binder p)
in (_149_795)::[])
in (FStar_Syntax_Util.abs _149_796 body None))
in (let _149_800 = (let _149_799 = (let _149_798 = (let _149_797 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _57_1010 = binding
in {FStar_Syntax_Syntax.lbname = _57_1010.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_1010.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1010.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1010.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_149_797)))
in FStar_Syntax_Syntax.Tm_let (_149_798))
in (mk _149_799))
in ((M (t2)), (_149_801), (_149_800)))))))))
end)))
end)
end)))))))
and check_n : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _149_804 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in N (_149_804))
in (match ((check env e mn)) with
| (N (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_1021 -> begin
(FStar_All.failwith "[check_n]: impossible")
end)))
and check_m : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _149_807 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in M (_149_807))
in (match ((check env e mn)) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_1031 -> begin
(FStar_All.failwith "[check_m]: impossible")
end)))
and comp_of_nm : nm_  ->  FStar_Syntax_Syntax.comp = (fun nm -> (match (nm) with
| N (t) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| M (t) -> begin
(mk_M t)
end))
and mk_M : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun t -> (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.monadic_lid; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = []}))
and type_of_comp : (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.typ = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Total (t)) | (FStar_Syntax_Syntax.GTotal (t)) | (FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.effect_name = _; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = _; FStar_Syntax_Syntax.flags = _})) -> begin
t
end))
and trans_F : env_  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> (

let _57_1053 = if (not ((is_C c))) then begin
(FStar_All.failwith "not a C")
end else begin
()
end
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos))
in (match ((let _149_816 = (FStar_Syntax_Subst.compress c)
in _149_816.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_1063 = (FStar_Syntax_Util.head_and_args wp)
in (match (_57_1063) with
| (wp_head, wp_args) -> begin
(

let _57_1064 = if ((not (((FStar_List.length wp_args) = (FStar_List.length args)))) || (not ((let _149_817 = (FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length wp_args) FStar_Range.dummyRange)
in (FStar_Syntax_Util.is_constructor wp_head _149_817))))) then begin
(FStar_All.failwith "mismatch")
end else begin
()
end
in (let _149_824 = (let _149_823 = (let _149_822 = (FStar_List.map2 (fun _57_1069 _57_1073 -> (match (((_57_1069), (_57_1073))) with
| ((arg, _57_1068), (wp_arg, _57_1072)) -> begin
(let _149_821 = (trans_F env arg wp_arg)
in (let _149_820 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_821), (_149_820))))
end)) args wp_args)
in ((head), (_149_822)))
in FStar_Syntax_Syntax.Tm_app (_149_823))
in (mk _149_824)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let binders = (FStar_Syntax_Subst.open_binders binders)
in (

let _57_1081 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (_57_1081) with
| (binders, comp) -> begin
(

let _57_1090 = (let _149_836 = (FStar_List.map (fun _57_1084 -> (match (_57_1084) with
| (bv, q) -> begin
(

let h = bv.FStar_Syntax_Syntax.sort
in if (is_C h) then begin
(

let w' = (let _149_826 = (star_type env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-w\'") None _149_826))
in (let _149_832 = (let _149_831 = (FStar_Syntax_Syntax.mk_binder w')
in (let _149_830 = (let _149_829 = (let _149_828 = (let _149_827 = (FStar_Syntax_Syntax.bv_to_name bv)
in (trans_F env h _149_827))
in (FStar_Syntax_Syntax.null_binder _149_828))
in (_149_829)::[])
in (_149_831)::_149_830))
in ((w'), (_149_832))))
end else begin
(

let x = (let _149_833 = (star_type env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-x") None _149_833))
in (let _149_835 = (let _149_834 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_834)::[])
in ((x), (_149_835))))
end)
end)) binders)
in (FStar_List.split _149_836))
in (match (_57_1090) with
| (bvs, binders) -> begin
(

let binders = (FStar_List.flatten binders)
in (

let app = (let _149_842 = (let _149_841 = (let _149_840 = (FStar_List.map (fun bv -> (let _149_839 = (FStar_Syntax_Syntax.bv_to_name bv)
in (let _149_838 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_839), (_149_838))))) bvs)
in ((wp), (_149_840)))
in FStar_Syntax_Syntax.Tm_app (_149_841))
in (mk _149_842))
in (

let comp = (let _149_844 = (type_of_comp comp)
in (let _149_843 = (is_monadic_comp comp)
in (trans_G env _149_844 _149_843 app)))
in (

let comp = (FStar_Syntax_Subst.close_comp binders comp)
in (

let binders = (FStar_Syntax_Subst.close_binders binders)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp))))))))))
end))
end)))
end
| _57_1098 -> begin
(FStar_All.failwith "impossible trans_F")
end))))
and trans_G : env_  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env h is_monadic wp -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None h.FStar_Syntax_Syntax.pos))
in if is_monadic then begin
(let _149_855 = (let _149_854 = (star_type env h)
in (let _149_853 = (let _149_852 = (let _149_851 = (FStar_Syntax_Syntax.as_implicit false)
in ((wp), (_149_851)))
in (_149_852)::[])
in {FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _149_854; FStar_Syntax_Syntax.effect_args = _149_853; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp _149_855))
end else begin
(let _149_856 = (trans_F env h wp)
in (FStar_Syntax_Syntax.mk_Total _149_856))
end))


let star_expr_definition : env  ->  FStar_Syntax_Syntax.term  ->  (env * (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)) = (fun env t -> (star_definition env t (fun env e -> (

let _57_1112 = (check_n env e)
in (match (_57_1112) with
| (t, s_e, s_u) -> begin
((t), (((s_e), (s_u))))
end)))))


let trans_FC : env_  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> (

let n = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.env)
in (

let c = (n c)
in (

let wp = (n wp)
in (trans_F env c wp)))))




