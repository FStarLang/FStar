
open Prims

let gen_wps_for_free = (fun env binders a wp_a tc_term ed -> (

let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env)
in (

let d = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))
in (

let normalize_and_make_binders_explicit = (fun tm -> (

let tm = (normalize tm)
in (

let rec visit_term = (fun tm -> (

let n = (match ((let _149_24 = (FStar_Syntax_Subst.compress tm)
in _149_24.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let comp = (visit_comp comp)
in (

let binders = (FStar_List.map visit_binder binders)
in FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))))
end
| FStar_Syntax_Syntax.Tm_abs (binders, term, comp) -> begin
(

let comp = (visit_maybe_lcomp comp)
in (

let term = (visit_term term)
in (

let binders = (FStar_List.map visit_binder binders)
in FStar_Syntax_Syntax.Tm_abs (((binders), (term), (comp))))))
end
| _57_40 -> begin
tm.FStar_Syntax_Syntax.n
end)
in (

let _57_42 = tm
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_42.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_42.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_42.FStar_Syntax_Syntax.vars})))
and visit_binder = (fun _57_46 -> (match (_57_46) with
| (bv, a) -> begin
(let _149_28 = (

let _57_47 = bv
in (let _149_26 = (visit_term bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_47.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_47.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_26}))
in (let _149_27 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_28), (_149_27))))
end))
and visit_maybe_lcomp = (fun lcomp -> (match (lcomp) with
| Some (FStar_Util.Inl (lcomp)) -> begin
(let _149_33 = (let _149_32 = (let _149_31 = (let _149_30 = (lcomp.FStar_Syntax_Syntax.comp ())
in (visit_comp _149_30))
in (FStar_Syntax_Util.lcomp_of_comp _149_31))
in FStar_Util.Inl (_149_32))
in Some (_149_33))
end
| comp -> begin
comp
end))
and visit_comp = (fun comp -> (

let n = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tm) -> begin
(let _149_35 = (visit_term tm)
in FStar_Syntax_Syntax.Total (_149_35))
end
| FStar_Syntax_Syntax.GTotal (tm) -> begin
(let _149_36 = (visit_term tm)
in FStar_Syntax_Syntax.GTotal (_149_36))
end
| comp -> begin
comp
end)
in (

let _57_61 = comp
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_61.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_61.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_61.FStar_Syntax_Syntax.vars})))
and visit_args = (fun args -> (FStar_List.map (fun _57_66 -> (match (_57_66) with
| (tm, q) -> begin
(let _149_39 = (visit_term tm)
in ((_149_39), (q)))
end)) args))
in (visit_term tm))))
in (

let check = (fun str t -> if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _57_70 = (let _149_44 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Generated term for %s: %s\n" str _149_44))
in (

let t = (normalize t)
in (

let t = (FStar_Syntax_Subst.compress t)
in (

let _57_85 = (tc_term env t)
in (match (_57_85) with
| (e, {FStar_Syntax_Syntax.eff_name = _57_81; FStar_Syntax_Syntax.res_typ = res_typ; FStar_Syntax_Syntax.cflags = _57_78; FStar_Syntax_Syntax.comp = _57_76}, _57_84) -> begin
(

let _57_86 = (let _149_47 = (let _149_46 = (normalize res_typ)
in (FStar_Syntax_Print.term_to_string _149_46))
in (FStar_Util.print2 "Inferred type for %s: %s\n" str _149_47))
in (let _149_49 = (let _149_48 = (normalize e)
in (FStar_Syntax_Print.term_to_string _149_48))
in (FStar_Util.print2 "Elaborated term for %s: %s\n" str _149_49)))
end)))))
end else begin
()
end)
in (

let rec collect_binders = (fun t -> (match ((let _149_52 = (FStar_Syntax_Subst.compress t)
in _149_52.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let rest = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
t
end
| _57_97 -> begin
(FStar_All.failwith "wp_a contains non-Tot arrow")
end)
in (let _149_53 = (collect_binders rest)
in (FStar_List.append bs _149_53)))
end
| FStar_Syntax_Syntax.Tm_type (_57_100) -> begin
[]
end
| _57_103 -> begin
(FStar_All.failwith "wp_a doesn\'t end in Type0")
end))
in (

let _57_118 = (

let i = (FStar_ST.alloc 0)
in (

let wp_binders = (let _149_60 = (normalize wp_a)
in (collect_binders _149_60))
in (((fun t -> (let _149_66 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow wp_binders _149_66)))), ((fun t -> (let _149_69 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow wp_binders _149_69)))), ((fun _57_108 -> (match (()) with
| () -> begin
(FStar_List.map (fun _57_112 -> (match (_57_112) with
| (bv, _57_111) -> begin
(

let _57_113 = (let _149_73 = ((FStar_ST.read i) + 1)
in (FStar_ST.op_Colon_Equals i _149_73))
in (let _149_76 = (let _149_75 = (let _149_74 = (FStar_ST.read i)
in (FStar_Util.string_of_int _149_74))
in (Prims.strcat "g" _149_75))
in (FStar_Syntax_Syntax.gen_bv _149_76 None bv.FStar_Syntax_Syntax.sort)))
end)) wp_binders)
end))))))
in (match (_57_118) with
| (mk_ctx, mk_gctx, mk_gamma) -> begin
(

let binders_of_list = (FStar_List.map (fun _57_121 -> (match (_57_121) with
| (t, b) -> begin
(let _149_82 = (FStar_Syntax_Syntax.as_implicit b)
in ((t), (_149_82)))
end)))
in (

let implicit_binders_of_list = (FStar_List.map (fun t -> (let _149_85 = (FStar_Syntax_Syntax.as_implicit true)
in ((t), (_149_85)))))
in (

let args_of_bv = (FStar_List.map (fun bv -> (let _149_88 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_Syntax_Syntax.as_arg _149_88))))
in (

let c_pure = (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let x = (let _149_89 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" None _149_89))
in (

let ret = (let _149_94 = (let _149_93 = (let _149_92 = (let _149_91 = (let _149_90 = (FStar_Syntax_Syntax.bv_to_name t)
in (mk_ctx _149_90))
in (FStar_Syntax_Syntax.mk_Total _149_91))
in (FStar_Syntax_Util.lcomp_of_comp _149_92))
in FStar_Util.Inl (_149_93))
in Some (_149_94))
in (

let gamma = (mk_gamma ())
in (

let body = (let _149_96 = (implicit_binders_of_list gamma)
in (let _149_95 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs _149_96 _149_95 ret)))
in (let _149_97 = (binders_of_list ((((t), (true)))::(((x), (false)))::[]))
in (FStar_Syntax_Util.abs _149_97 body ret)))))))
in (

let _57_133 = (let _149_101 = (let _149_100 = (let _149_99 = (let _149_98 = (FStar_Syntax_Syntax.mk_binder a)
in (_149_98)::[])
in (FStar_List.append binders _149_99))
in (FStar_Syntax_Util.abs _149_100 c_pure None))
in (check "pure" _149_101))
in (

let c_app = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let l = (let _149_109 = (let _149_108 = (let _149_107 = (let _149_104 = (let _149_103 = (let _149_102 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv None _149_102))
in (FStar_Syntax_Syntax.mk_binder _149_103))
in (_149_104)::[])
in (let _149_106 = (let _149_105 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _149_105))
in (FStar_Syntax_Util.arrow _149_107 _149_106)))
in (mk_gctx _149_108))
in (FStar_Syntax_Syntax.gen_bv "l" None _149_109))
in (

let r = (let _149_111 = (let _149_110 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _149_110))
in (FStar_Syntax_Syntax.gen_bv "r" None _149_111))
in (

let ret = (let _149_116 = (let _149_115 = (let _149_114 = (let _149_113 = (let _149_112 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _149_112))
in (FStar_Syntax_Syntax.mk_Total _149_113))
in (FStar_Syntax_Util.lcomp_of_comp _149_114))
in FStar_Util.Inl (_149_115))
in Some (_149_116))
in (

let outer_body = (

let gamma = (mk_gamma ())
in (

let gamma_as_args = (args_of_bv gamma)
in (

let inner_body = (let _149_122 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _149_121 = (let _149_120 = (let _149_119 = (let _149_118 = (let _149_117 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app _149_117 gamma_as_args))
in (FStar_Syntax_Syntax.as_arg _149_118))
in (_149_119)::[])
in (FStar_List.append gamma_as_args _149_120))
in (FStar_Syntax_Util.mk_app _149_122 _149_121)))
in (let _149_123 = (implicit_binders_of_list gamma)
in (FStar_Syntax_Util.abs _149_123 inner_body ret)))))
in (let _149_124 = (binders_of_list ((((t1), (true)))::(((t2), (true)))::(((l), (false)))::(((r), (false)))::[]))
in (FStar_Syntax_Util.abs _149_124 outer_body ret))))))))
in (

let _57_145 = (let _149_128 = (let _149_127 = (let _149_126 = (let _149_125 = (FStar_Syntax_Syntax.mk_binder a)
in (_149_125)::[])
in (FStar_List.append binders _149_126))
in (FStar_Syntax_Util.abs _149_127 c_app None))
in (check "app" _149_128))
in (

let unknown = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (

let c_lift1 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _149_133 = (let _149_130 = (let _149_129 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _149_129))
in (_149_130)::[])
in (let _149_132 = (let _149_131 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _149_131))
in (FStar_Syntax_Util.arrow _149_133 _149_132)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _149_135 = (let _149_134 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _149_134))
in (FStar_Syntax_Syntax.gen_bv "a1" None _149_135))
in (

let ret = (let _149_140 = (let _149_139 = (let _149_138 = (let _149_137 = (let _149_136 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _149_136))
in (FStar_Syntax_Syntax.mk_Total _149_137))
in (FStar_Syntax_Util.lcomp_of_comp _149_138))
in FStar_Util.Inl (_149_139))
in Some (_149_140))
in (let _149_153 = (binders_of_list ((((t1), (true)))::(((t2), (true)))::(((f), (false)))::(((a1), (false)))::[]))
in (let _149_152 = (let _149_151 = (let _149_150 = (let _149_149 = (let _149_148 = (let _149_147 = (let _149_144 = (let _149_143 = (let _149_142 = (let _149_141 = (FStar_Syntax_Syntax.bv_to_name f)
in (_149_141)::[])
in (unknown)::_149_142)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_143))
in (FStar_Syntax_Util.mk_app c_pure _149_144))
in (let _149_146 = (let _149_145 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_149_145)::[])
in (_149_147)::_149_146))
in (unknown)::_149_148)
in (unknown)::_149_149)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_150))
in (FStar_Syntax_Util.mk_app c_app _149_151))
in (FStar_Syntax_Util.abs _149_153 _149_152 ret)))))))))
in (

let _57_155 = (let _149_157 = (let _149_156 = (let _149_155 = (let _149_154 = (FStar_Syntax_Syntax.mk_binder a)
in (_149_154)::[])
in (FStar_List.append binders _149_155))
in (FStar_Syntax_Util.abs _149_156 c_lift1 None))
in (check "lift1" _149_157))
in (

let c_lift2 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t3 = (FStar_Syntax_Syntax.gen_bv "t3" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _149_165 = (let _149_162 = (let _149_158 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _149_158))
in (let _149_161 = (let _149_160 = (let _149_159 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.null_binder _149_159))
in (_149_160)::[])
in (_149_162)::_149_161))
in (let _149_164 = (let _149_163 = (FStar_Syntax_Syntax.bv_to_name t3)
in (FStar_Syntax_Syntax.mk_GTotal _149_163))
in (FStar_Syntax_Util.arrow _149_165 _149_164)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _149_167 = (let _149_166 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _149_166))
in (FStar_Syntax_Syntax.gen_bv "a1" None _149_167))
in (

let a2 = (let _149_169 = (let _149_168 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _149_168))
in (FStar_Syntax_Syntax.gen_bv "a2" None _149_169))
in (

let ret = (let _149_174 = (let _149_173 = (let _149_172 = (let _149_171 = (let _149_170 = (FStar_Syntax_Syntax.bv_to_name t3)
in (mk_gctx _149_170))
in (FStar_Syntax_Syntax.mk_Total _149_171))
in (FStar_Syntax_Util.lcomp_of_comp _149_172))
in FStar_Util.Inl (_149_173))
in Some (_149_174))
in (let _149_194 = (binders_of_list ((((t1), (true)))::(((t2), (true)))::(((t3), (true)))::(((f), (false)))::(((a1), (false)))::(((a2), (false)))::[]))
in (let _149_193 = (let _149_192 = (let _149_191 = (let _149_190 = (let _149_189 = (let _149_188 = (let _149_185 = (let _149_184 = (let _149_183 = (let _149_182 = (let _149_181 = (let _149_178 = (let _149_177 = (let _149_176 = (let _149_175 = (FStar_Syntax_Syntax.bv_to_name f)
in (_149_175)::[])
in (unknown)::_149_176)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_177))
in (FStar_Syntax_Util.mk_app c_pure _149_178))
in (let _149_180 = (let _149_179 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_149_179)::[])
in (_149_181)::_149_180))
in (unknown)::_149_182)
in (unknown)::_149_183)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_184))
in (FStar_Syntax_Util.mk_app c_app _149_185))
in (let _149_187 = (let _149_186 = (FStar_Syntax_Syntax.bv_to_name a2)
in (_149_186)::[])
in (_149_188)::_149_187))
in (unknown)::_149_189)
in (unknown)::_149_190)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_191))
in (FStar_Syntax_Util.mk_app c_app _149_192))
in (FStar_Syntax_Util.abs _149_194 _149_193 ret)))))))))))
in (

let _57_166 = (let _149_198 = (let _149_197 = (let _149_196 = (let _149_195 = (FStar_Syntax_Syntax.mk_binder a)
in (_149_195)::[])
in (FStar_List.append binders _149_196))
in (FStar_Syntax_Util.abs _149_197 c_lift2 None))
in (check "lift2" _149_198))
in (

let c_push = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _149_204 = (let _149_200 = (let _149_199 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _149_199))
in (_149_200)::[])
in (let _149_203 = (let _149_202 = (let _149_201 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _149_201))
in (FStar_Syntax_Syntax.mk_Total _149_202))
in (FStar_Syntax_Util.arrow _149_204 _149_203)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let ret = (let _149_214 = (let _149_213 = (let _149_212 = (let _149_211 = (let _149_210 = (let _149_209 = (let _149_206 = (let _149_205 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _149_205))
in (_149_206)::[])
in (let _149_208 = (let _149_207 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _149_207))
in (FStar_Syntax_Util.arrow _149_209 _149_208)))
in (mk_ctx _149_210))
in (FStar_Syntax_Syntax.mk_Total _149_211))
in (FStar_Syntax_Util.lcomp_of_comp _149_212))
in FStar_Util.Inl (_149_213))
in Some (_149_214))
in (

let e1 = (let _149_215 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" None _149_215))
in (

let gamma = (mk_gamma ())
in (

let body = (let _149_225 = (let _149_218 = (FStar_Syntax_Syntax.binders_of_list gamma)
in (let _149_217 = (let _149_216 = (FStar_Syntax_Syntax.mk_binder e1)
in (_149_216)::[])
in (FStar_List.append _149_218 _149_217)))
in (let _149_224 = (let _149_223 = (FStar_Syntax_Syntax.bv_to_name f)
in (let _149_222 = (let _149_221 = (let _149_219 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg _149_219))
in (let _149_220 = (args_of_bv gamma)
in (_149_221)::_149_220))
in (FStar_Syntax_Util.mk_app _149_223 _149_222)))
in (FStar_Syntax_Util.abs _149_225 _149_224 ret)))
in (let _149_226 = (binders_of_list ((((t1), (true)))::(((t2), (true)))::(((f), (false)))::[]))
in (FStar_Syntax_Util.abs _149_226 body ret))))))))))
in (

let _57_177 = (let _149_230 = (let _149_229 = (let _149_228 = (let _149_227 = (FStar_Syntax_Syntax.mk_binder a)
in (_149_227)::[])
in (FStar_List.append binders _149_228))
in (FStar_Syntax_Util.abs _149_229 c_push None))
in (check "push" _149_230))
in (

let ret_tot_wp_a = (let _149_233 = (let _149_232 = (let _149_231 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.lcomp_of_comp _149_231))
in FStar_Util.Inl (_149_232))
in Some (_149_233))
in (

let wp_if_then_else = (

let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (let _149_244 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (let _149_243 = (

let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_unfoldable (2)) None)
in (let _149_242 = (let _149_241 = (let _149_240 = (let _149_239 = (let _149_238 = (let _149_237 = (let _149_236 = (let _149_235 = (let _149_234 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg _149_234))
in (_149_235)::[])
in (FStar_Syntax_Util.mk_app l_ite _149_236))
in (_149_237)::[])
in (unknown)::_149_238)
in (unknown)::_149_239)
in (unknown)::_149_240)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_241))
in (FStar_Syntax_Util.mk_app c_lift2 _149_242)))
in (FStar_Syntax_Util.abs _149_244 _149_243 ret_tot_wp_a))))
in (

let wp_if_then_else = (normalize_and_make_binders_explicit wp_if_then_else)
in (

let _57_184 = (let _149_245 = (FStar_Syntax_Util.abs binders wp_if_then_else None)
in (check "wp_if_then_else" _149_245))
in (

let wp_assert = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype0)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_and = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.and_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (

let body = (let _149_259 = (let _149_258 = (let _149_257 = (let _149_256 = (let _149_255 = (let _149_252 = (let _149_251 = (let _149_250 = (let _149_249 = (let _149_248 = (let _149_247 = (let _149_246 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _149_246))
in (_149_247)::[])
in (FStar_Syntax_Util.mk_app l_and _149_248))
in (_149_249)::[])
in (unknown)::_149_250)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_251))
in (FStar_Syntax_Util.mk_app c_pure _149_252))
in (let _149_254 = (let _149_253 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_149_253)::[])
in (_149_255)::_149_254))
in (unknown)::_149_256)
in (unknown)::_149_257)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_258))
in (FStar_Syntax_Util.mk_app c_app _149_259))
in (let _149_260 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_Syntax_Util.abs _149_260 body ret_tot_wp_a))))))
in (

let wp_assert = (normalize_and_make_binders_explicit wp_assert)
in (

let _57_192 = (let _149_261 = (FStar_Syntax_Util.abs binders wp_assert None)
in (check "wp_assert" _149_261))
in (

let wp_assume = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype0)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_imp = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.imp_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (

let body = (let _149_275 = (let _149_274 = (let _149_273 = (let _149_272 = (let _149_271 = (let _149_268 = (let _149_267 = (let _149_266 = (let _149_265 = (let _149_264 = (let _149_263 = (let _149_262 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _149_262))
in (_149_263)::[])
in (FStar_Syntax_Util.mk_app l_imp _149_264))
in (_149_265)::[])
in (unknown)::_149_266)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_267))
in (FStar_Syntax_Util.mk_app c_pure _149_268))
in (let _149_270 = (let _149_269 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_149_269)::[])
in (_149_271)::_149_270))
in (unknown)::_149_272)
in (unknown)::_149_273)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_274))
in (FStar_Syntax_Util.mk_app c_app _149_275))
in (let _149_276 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_Syntax_Util.abs _149_276 body ret_tot_wp_a))))))
in (

let wp_assume = (normalize_and_make_binders_explicit wp_assume)
in (

let _57_200 = (let _149_277 = (FStar_Syntax_Util.abs binders wp_assume None)
in (check "wp_assume" _149_277))
in (

let tforall = (let _149_280 = (FStar_Syntax_Syntax.mk_Tm_uinst FStar_Syntax_Util.tforall ((FStar_Syntax_Syntax.U_unknown)::[]))
in (let _149_279 = (let _149_278 = (FStar_Syntax_Syntax.as_arg unknown)
in (_149_278)::[])
in (FStar_Syntax_Util.mk_app _149_280 _149_279)))
in (

let wp_close = (

let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _149_284 = (let _149_282 = (let _149_281 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _149_281))
in (_149_282)::[])
in (let _149_283 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _149_284 _149_283)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let body = (let _149_297 = (let _149_296 = (let _149_295 = (let _149_294 = (let _149_293 = (let _149_285 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((unknown)::(tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure _149_285))
in (let _149_292 = (let _149_291 = (let _149_290 = (let _149_289 = (let _149_288 = (let _149_287 = (let _149_286 = (FStar_Syntax_Syntax.bv_to_name f)
in (_149_286)::[])
in (unknown)::_149_287)
in (unknown)::_149_288)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_289))
in (FStar_Syntax_Util.mk_app c_push _149_290))
in (_149_291)::[])
in (_149_293)::_149_292))
in (unknown)::_149_294)
in (unknown)::_149_295)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_296))
in (FStar_Syntax_Util.mk_app c_app _149_297))
in (let _149_298 = (FStar_Syntax_Syntax.binders_of_list ((a)::(b)::(f)::[]))
in (FStar_Syntax_Util.abs _149_298 body ret_tot_wp_a))))))
in (

let wp_close = (normalize_and_make_binders_explicit wp_close)
in (

let _57_209 = (let _149_299 = (FStar_Syntax_Util.abs binders wp_close None)
in (check "wp_close" _149_299))
in (

let ret_tot_type0 = (let _149_302 = (let _149_301 = (let _149_300 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _149_300))
in FStar_Util.Inl (_149_301))
in Some (_149_302))
in (

let mk_forall = (fun x body -> (

let tforall = (let _149_309 = (FStar_Syntax_Syntax.mk_Tm_uinst FStar_Syntax_Util.tforall ((FStar_Syntax_Syntax.U_unknown)::[]))
in (let _149_308 = (let _149_307 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (_149_307)::[])
in (FStar_Syntax_Util.mk_app _149_309 _149_308)))
in (let _149_316 = (let _149_315 = (let _149_314 = (let _149_313 = (let _149_312 = (let _149_311 = (let _149_310 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_310)::[])
in (FStar_Syntax_Util.abs _149_311 body ret_tot_type0))
in (FStar_Syntax_Syntax.as_arg _149_312))
in (_149_313)::[])
in ((tforall), (_149_314)))
in FStar_Syntax_Syntax.Tm_app (_149_315))
in (FStar_Syntax_Syntax.mk _149_316 None FStar_Range.dummyRange))))
in (

let rec mk_leq = (fun t x y -> (match ((let _149_324 = (let _149_323 = (FStar_Syntax_Subst.compress t)
in (normalize _149_323))
in _149_324.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_221) -> begin
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

let body = (let _149_336 = (let _149_326 = (FStar_Syntax_Syntax.bv_to_name a1)
in (let _149_325 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_leq a _149_326 _149_325)))
in (let _149_335 = (let _149_334 = (let _149_329 = (let _149_328 = (let _149_327 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _149_327))
in (_149_328)::[])
in (FStar_Syntax_Util.mk_app x _149_329))
in (let _149_333 = (let _149_332 = (let _149_331 = (let _149_330 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg _149_330))
in (_149_331)::[])
in (FStar_Syntax_Util.mk_app y _149_332))
in (mk_leq b _149_334 _149_333)))
in (FStar_Syntax_Util.mk_imp _149_336 _149_335)))
in (let _149_337 = (mk_forall a2 body)
in (mk_forall a1 _149_337))))))
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::binders, comp) -> begin
(

let t = (

let _57_257 = t
in (let _149_341 = (let _149_340 = (let _149_339 = (let _149_338 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _149_338))
in (((binder)::[]), (_149_339)))
in FStar_Syntax_Syntax.Tm_arrow (_149_340))
in {FStar_Syntax_Syntax.n = _149_341; FStar_Syntax_Syntax.tk = _57_257.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_257.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_257.FStar_Syntax_Syntax.vars}))
in (mk_leq t x y))
end
| FStar_Syntax_Syntax.Tm_arrow (_57_261) -> begin
(FStar_All.failwith "unhandled arrow")
end
| _57_264 -> begin
(FStar_Syntax_Util.mk_eq t t x y)
end))
in (

let stronger = (

let wp1 = (FStar_Syntax_Syntax.gen_bv "wp1" None wp_a)
in (

let wp2 = (FStar_Syntax_Syntax.gen_bv "wp2" None wp_a)
in (

let body = (let _149_343 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (let _149_342 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_leq wp_a _149_343 _149_342)))
in (let _149_344 = (FStar_Syntax_Syntax.binders_of_list ((wp1)::(wp2)::[]))
in (FStar_Syntax_Util.abs _149_344 body ret_tot_type0)))))
in (

let _57_269 = (let _149_348 = (let _149_347 = (let _149_346 = (let _149_345 = (FStar_Syntax_Syntax.mk_binder a)
in (_149_345)::[])
in (FStar_List.append binders _149_346))
in (FStar_Syntax_Util.abs _149_347 stronger None))
in (check "stronger" _149_348))
in (

let null_wp = (Prims.snd ed.FStar_Syntax_Syntax.null_wp)
in (

let wp_trivial = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let body = (let _149_356 = (let _149_355 = (let _149_354 = (let _149_351 = (let _149_350 = (let _149_349 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg _149_349))
in (_149_350)::[])
in (FStar_Syntax_Util.mk_app null_wp _149_351))
in (let _149_353 = (let _149_352 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_149_352)::[])
in (_149_354)::_149_353))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_355))
in (FStar_Syntax_Util.mk_app stronger _149_356))
in (let _149_357 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_Syntax_Util.abs _149_357 body ret_tot_type0))))
in (

let wp_trivial = (normalize_and_make_binders_explicit wp_trivial)
in (

let _57_276 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_276.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_276.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_276.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_276.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_276.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _57_276.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _57_276.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = (([]), (wp_if_then_else)); FStar_Syntax_Syntax.ite_wp = _57_276.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _57_276.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = (([]), (wp_close)); FStar_Syntax_Syntax.assert_p = (([]), (wp_assert)); FStar_Syntax_Syntax.assume_p = (([]), (wp_assume)); FStar_Syntax_Syntax.null_wp = _57_276.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _57_276.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _57_276.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _57_276.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _57_276.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _57_276.FStar_Syntax_Syntax.actions})))))))))))))))))))))))))))))))))))))
end))))))))


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
| N (_57_287) -> begin
_57_287
end))


let ___M____0 = (fun projectee -> (match (projectee) with
| M (_57_290) -> begin
_57_290
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
| _57_297 -> begin
(FStar_All.failwith "[nm_of_comp]: impossible")
end))


let string_of_nm : nm  ->  Prims.string = (fun _57_2 -> (match (_57_2) with
| N (t) -> begin
(let _149_418 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "N[%s]" _149_418))
end
| M (t) -> begin
(let _149_419 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "M[%s]" _149_419))
end))


let is_monadic_arrow : FStar_Syntax_Syntax.term'  ->  nm = (fun n -> (match (n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_305, {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_311; FStar_Syntax_Syntax.pos = _57_309; FStar_Syntax_Syntax.vars = _57_307}) -> begin
(nm_of_comp n)
end
| _57_317 -> begin
(FStar_All.failwith "unexpected_argument: [is_monadic_arrow]")
end))


let is_monadic_comp = (fun c -> (match ((nm_of_comp c.FStar_Syntax_Syntax.n)) with
| M (_57_320) -> begin
true
end
| N (_57_323) -> begin
false
end))


let rec mk_star_to_type : (FStar_Syntax_Syntax.term'  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun mk env a -> (let _149_443 = (let _149_442 = (let _149_441 = (let _149_439 = (let _149_438 = (let _149_436 = (star_type env a)
in (FStar_Syntax_Syntax.null_bv _149_436))
in (let _149_437 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_438), (_149_437))))
in (_149_439)::[])
in (let _149_440 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype)
in ((_149_441), (_149_440))))
in FStar_Syntax_Syntax.Tm_arrow (_149_442))
in (mk _149_443)))
and star_type : env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None t.FStar_Syntax_Syntax.pos))
in (

let mk_star_to_type = (mk_star_to_type mk)
in (

let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.env)
in (

let t = (normalize t)
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _57_338) -> begin
(

let binders = (FStar_List.map (fun _57_343 -> (match (_57_343) with
| (bv, aqual) -> begin
(let _149_453 = (

let _57_344 = bv
in (let _149_452 = (star_type env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_344.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_344.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_452}))
in ((_149_453), (aqual)))
end)) binders)
in (match ((is_monadic_arrow t.FStar_Syntax_Syntax.n)) with
| N (hn) -> begin
(let _149_457 = (let _149_456 = (let _149_455 = (let _149_454 = (star_type env hn)
in (FStar_Syntax_Syntax.mk_Total _149_454))
in ((binders), (_149_455)))
in FStar_Syntax_Syntax.Tm_arrow (_149_456))
in (mk _149_457))
end
| M (a) -> begin
(let _149_466 = (let _149_465 = (let _149_464 = (let _149_462 = (let _149_461 = (let _149_460 = (let _149_458 = (mk_star_to_type env a)
in (FStar_Syntax_Syntax.null_bv _149_458))
in (let _149_459 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_460), (_149_459))))
in (_149_461)::[])
in (FStar_List.append binders _149_462))
in (let _149_463 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype)
in ((_149_464), (_149_463))))
in FStar_Syntax_Syntax.Tm_arrow (_149_465))
in (mk _149_466))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let rec is_valid_application = (fun head -> (match ((let _149_469 = (FStar_Syntax_Subst.compress head)
in _149_469.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.option_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.either_lid)) || (let _149_470 = (FStar_Syntax_Subst.compress head)
in (FStar_Syntax_Util.is_tuple_constructor _149_470))) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uinst (head, _57_361) -> begin
(is_valid_application head)
end
| _57_365 -> begin
false
end))
in if (is_valid_application head) then begin
(let _149_475 = (let _149_474 = (let _149_473 = (FStar_List.map (fun _57_368 -> (match (_57_368) with
| (t, qual) -> begin
(let _149_472 = (star_type env t)
in ((_149_472), (qual)))
end)) args)
in ((head), (_149_473)))
in FStar_Syntax_Syntax.Tm_app (_149_474))
in (mk _149_475))
end else begin
(let _149_478 = (let _149_477 = (let _149_476 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "For now, only [either] and [option] are supported in the definition language (got: %s)" _149_476))
in FStar_Syntax_Syntax.Err (_149_477))
in (Prims.raise _149_478))
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

let _57_388 = env
in (let _149_479 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _149_479; definitions = _57_388.definitions; subst = _57_388.subst; tc_const = _57_388.tc_const}))
in (

let repr = (star_type env repr)
in (

let repr = (FStar_Syntax_Subst.close binders repr)
in (mk (FStar_Syntax_Syntax.Tm_abs (((binders), (repr), (something))))))))))
end
| (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_match (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _149_482 = (let _149_481 = (let _149_480 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "The following term is outside of the definition language: %s" _149_480))
in FStar_Syntax_Syntax.Err (_149_481))
in (Prims.raise _149_482))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_422) -> begin
(FStar_All.failwith "impossible")
end)))))))


let star_definition = (fun env t f -> (match ((let _149_495 = (FStar_Syntax_Subst.compress t)
in _149_495.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = lid; FStar_Syntax_Syntax.fv_delta = _57_430; FStar_Syntax_Syntax.fv_qual = _57_428}) -> begin
(

let _57_434 = (FStar_Util.print1 "Recording definition of %s\n" (FStar_Ident.text_of_lid lid.FStar_Syntax_Syntax.v))
in (

let _57_448 = (match ((let _149_497 = (FStar_TypeChecker_Env.lookup_definition (FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant)) env.env lid.FStar_Syntax_Syntax.v)
in (let _149_496 = (FStar_TypeChecker_Env.lookup_lid env.env lid.FStar_Syntax_Syntax.v)
in ((_149_497), (_149_496))))) with
| (Some ([], e), ([], t)) -> begin
(f env e)
end
| _57_445 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Bad definition in [star_type_definition]")))
end)
in (match (_57_448) with
| (store, ret) -> begin
(((

let _57_449 = env
in {env = _57_449.env; definitions = (((lid.FStar_Syntax_Syntax.v), (store)))::env.definitions; subst = _57_449.subst; tc_const = _57_449.tc_const})), (ret))
end)))
end
| FStar_Syntax_Syntax.Tm_uinst (_57_452) -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Ill-formed definition (hint: use Type0, not Type)")))
end
| _57_455 -> begin
(let _149_500 = (let _149_499 = (let _149_498 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Ill-formed definition: %s" _149_498))
in FStar_Syntax_Syntax.Err (_149_499))
in (Prims.raise _149_500))
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


let rec is_C : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match ((let _149_511 = (FStar_Syntax_Subst.compress t)
in _149_511.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) when (FStar_Syntax_Util.is_tuple_constructor head) -> begin
(

let r = (let _149_513 = (let _149_512 = (FStar_List.hd args)
in (Prims.fst _149_512))
in (is_C _149_513))
in if r then begin
(

let _57_485 = if (not ((FStar_List.for_all (fun _57_484 -> (match (_57_484) with
| (h, _57_483) -> begin
(is_C h)
end)) args))) then begin
(FStar_All.failwith "not a C (A * C)")
end else begin
()
end
in true)
end else begin
(

let _57_491 = if (not ((FStar_List.for_all (fun _57_490 -> (match (_57_490) with
| (h, _57_489) -> begin
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

let _57_499 = if (is_C t) then begin
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
| _57_519 -> begin
false
end))


let mk_return : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let p_type = (mk_star_to_type mk env t)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'" None p_type)
in (

let body = (let _149_529 = (let _149_528 = (let _149_527 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _149_526 = (let _149_525 = (let _149_524 = (FStar_Syntax_Syntax.as_implicit false)
in ((e), (_149_524)))
in (_149_525)::[])
in ((_149_527), (_149_526))))
in FStar_Syntax_Syntax.Tm_app (_149_528))
in (mk _149_529))
in (let _149_531 = (let _149_530 = (FStar_Syntax_Syntax.mk_binder p)
in (_149_530)::[])
in (FStar_Syntax_Util.abs _149_531 body None)))))))


let is_unknown : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun _57_4 -> (match (_57_4) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| _57_531 -> begin
false
end))


let rec check : env  ->  FStar_Syntax_Syntax.term  ->  nm  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e context_nm -> (

let _57_535 = (let _149_577 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "[debug]: check %s\n" _149_577))
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let return_if = (fun _57_543 -> (match (_57_543) with
| (rec_nm, s_e, u_e) -> begin
(

let check = (fun t1 t2 -> if ((not ((is_unknown t2.FStar_Syntax_Syntax.n))) && (not ((let _149_586 = (FStar_TypeChecker_Rel.teq env.env t1 t2)
in (FStar_TypeChecker_Rel.is_trivial _149_586))))) then begin
(let _149_591 = (let _149_590 = (let _149_589 = (FStar_Syntax_Print.term_to_string e)
in (let _149_588 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_587 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check]: the expression [%s] has type [%s] but should have type [%s]" _149_589 _149_588 _149_587))))
in FStar_Syntax_Syntax.Err (_149_590))
in (Prims.raise _149_591))
end else begin
()
end)
in (match (((rec_nm), (context_nm))) with
| ((N (t1), N (t2))) | ((M (t1), M (t2))) -> begin
(

let _57_555 = (check t1 t2)
in ((rec_nm), (s_e), (u_e)))
end
| (N (t1), M (t2)) -> begin
(

let _57_562 = (check t1 t2)
in (let _149_592 = (mk_return env t1 s_e)
in ((M (t1)), (_149_592), (u_e))))
end
| (M (_57_565), N (_57_568)) -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("[check]: got an effectful computation in lieu of a pure computation")))
end))
end))
in (match ((let _149_593 = (FStar_Syntax_Subst.compress e)
in _149_593.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
(let _149_594 = (infer env e)
in (return_if _149_594))
end
| FStar_Syntax_Syntax.Tm_let ((false, (binding)::[]), e2) -> begin
(mk_let env binding e2 (fun env e2 -> (check env e2 context_nm)) (fun env e2 -> (

let strip_m = (fun _57_5 -> (match (_57_5) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_605 -> begin
(FStar_All.failwith "impossible")
end))
in (match (context_nm) with
| N (t) -> begin
(let _149_601 = (check env e2 (M (t)))
in (strip_m _149_601))
end
| M (_57_610) -> begin
(let _149_602 = (check env e2 context_nm)
in (strip_m _149_602))
end))))
end
| FStar_Syntax_Syntax.Tm_match (e0, branches) -> begin
(mk_match env e0 branches (fun env body -> (check env body context_nm)))
end
| (FStar_Syntax_Syntax.Tm_meta (e, _)) | (FStar_Syntax_Syntax.Tm_uinst (e, _)) | (FStar_Syntax_Syntax.Tm_ascribed (e, _, _)) -> begin
(check env e context_nm)
end
| FStar_Syntax_Syntax.Tm_let (_57_636) -> begin
(let _149_608 = (let _149_607 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_let %s" _149_607))
in (FStar_All.failwith _149_608))
end
| FStar_Syntax_Syntax.Tm_type (_57_639) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_642) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_57_645) -> begin
(let _149_610 = (let _149_609 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_refine %s" _149_609))
in (FStar_All.failwith _149_610))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_648) -> begin
(let _149_612 = (let _149_611 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_uvar %s" _149_611))
in (FStar_All.failwith _149_612))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_651) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _149_617 = (let _149_616 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_unknown %s" _149_616))
in (FStar_All.failwith _149_617))
end)))))
and infer : env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let _57_656 = (let _149_620 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "[debug]: infer %s\n" _149_620))
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.env)
in (match ((let _149_624 = (FStar_Syntax_Subst.compress e)
in _149_624.FStar_Syntax_Syntax.n)) with
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

let _57_673 = env
in (let _149_625 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _149_625; definitions = _57_673.definitions; subst = _57_673.subst; tc_const = _57_673.tc_const}))
in (

let s_binders = (FStar_List.map (fun _57_678 -> (match (_57_678) with
| (bv, qual) -> begin
(

let sort = (star_type env bv.FStar_Syntax_Syntax.sort)
in (((

let _57_680 = bv
in {FStar_Syntax_Syntax.ppname = _57_680.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_680.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (qual)))
end)) binders)
in (

let _57_702 = (FStar_List.fold_left (fun _57_685 _57_688 -> (match (((_57_685), (_57_688))) with
| ((env, acc), (bv, qual)) -> begin
(

let c = (normalize bv.FStar_Syntax_Syntax.sort)
in if (is_C c) then begin
(

let xw = (let _149_629 = (star_type env c)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "^w") None _149_629))
in (

let x = (

let _57_691 = bv
in (let _149_631 = (let _149_630 = (FStar_Syntax_Syntax.bv_to_name xw)
in (trans_F env c _149_630))
in {FStar_Syntax_Syntax.ppname = _57_691.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_691.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_631}))
in (

let env = (

let _57_694 = env
in (let _149_635 = (let _149_634 = (let _149_633 = (let _149_632 = (FStar_Syntax_Syntax.bv_to_name xw)
in ((bv), (_149_632)))
in FStar_Syntax_Syntax.NT (_149_633))
in (_149_634)::env.subst)
in {env = _57_694.env; definitions = _57_694.definitions; subst = _149_635; tc_const = _57_694.tc_const}))
in (let _149_639 = (let _149_638 = (FStar_Syntax_Syntax.mk_binder x)
in (let _149_637 = (let _149_636 = (FStar_Syntax_Syntax.mk_binder xw)
in (_149_636)::acc)
in (_149_638)::_149_637))
in ((env), (_149_639))))))
end else begin
(

let x = (

let _57_697 = bv
in (let _149_640 = (star_type env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_697.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_697.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_640}))
in (let _149_642 = (let _149_641 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_641)::acc)
in ((env), (_149_642))))
end)
end)) ((env), ([])) binders)
in (match (_57_702) with
| (env, u_binders) -> begin
(

let u_binders = (FStar_List.rev u_binders)
in (

let _57_712 = (

let check_what = if (is_monadic what) then begin
check_m
end else begin
check_n
end
in (

let _57_708 = (check_what env body)
in (match (_57_708) with
| (t, s_body, u_body) -> begin
(let _149_648 = (let _149_647 = if (is_monadic what) then begin
M (t)
end else begin
N (t)
end
in (comp_of_nm _149_647))
in ((_149_648), (s_body), (u_body)))
end)))
in (match (_57_712) with
| (comp, s_body, u_body) -> begin
(

let t = (

let binders = (FStar_List.map (fun _57_716 -> (match (_57_716) with
| (bv, _57_715) -> begin
(let _149_651 = (let _149_650 = (normalize bv.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.null_bv _149_650))
in (FStar_Syntax_Syntax.mk_binder _149_651))
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
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = {FStar_Syntax_Syntax.v = lid; FStar_Syntax_Syntax.ty = _57_733; FStar_Syntax_Syntax.p = _57_731}; FStar_Syntax_Syntax.fv_delta = _57_729; FStar_Syntax_Syntax.fv_qual = _57_727}) -> begin
(match ((FStar_List.find (fun _57_741 -> (match (_57_741) with
| (lid', _57_740) -> begin
(FStar_Ident.lid_equals lid lid')
end)) env.definitions)) with
| Some (_57_743, t) -> begin
(

let _57_747 = (let _149_653 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "[debug]: lookup %s hit %s\n" (FStar_Ident.text_of_lid lid) _149_653))
in ((N (t)), (e), (e)))
end
| None -> begin
(

let _57_753 = (FStar_TypeChecker_Env.lookup_lid env.env lid)
in (match (_57_753) with
| (_57_751, t) -> begin
(

let txt = (FStar_Ident.text_of_lid lid)
in (

let allowed_prefixes = ("Mktuple")::("Left")::("Right")::("Some")::("None")::[]
in (

let _57_756 = (let _149_654 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "[debug]: lookup %s miss %s\n" txt _149_654))
in if (FStar_List.existsb (fun s -> (FStar_Util.starts_with txt (Prims.strcat "Prims." s))) allowed_prefixes) then begin
((N (t)), (e), (e))
end else begin
(let _149_657 = (let _149_656 = (FStar_Util.format1 "The %s constructor has not been whitelisted for the definition language" txt)
in FStar_Syntax_Syntax.Err (_149_656))
in (Prims.raise _149_657))
end)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_766 = (check_n env head)
in (match (_57_766) with
| (t_head, s_head, u_head) -> begin
(

let t_head = (normalize t_head)
in (

let _57_776 = (match ((let _149_658 = (FStar_Syntax_Subst.compress t_head)
in _149_658.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
((binders), (comp))
end
| _57_773 -> begin
(let _149_661 = (let _149_660 = (let _149_659 = (FStar_Syntax_Print.term_to_string t_head)
in (FStar_Util.format1 "%s: not a function type" _149_659))
in FStar_Syntax_Syntax.Err (_149_660))
in (Prims.raise _149_661))
end)
in (match (_57_776) with
| (binders, comp) -> begin
(

let _57_777 = (let _149_662 = (FStar_Syntax_Print.term_to_string t_head)
in (FStar_Util.print1 "[debug] type of [head] is %s\n" _149_662))
in (

let n = (FStar_List.length binders)
in (

let n' = (FStar_List.length args)
in (

let _57_781 = if ((FStar_List.length binders) < (FStar_List.length args)) then begin
(let _149_667 = (let _149_666 = (let _149_665 = (FStar_Util.string_of_int n)
in (let _149_664 = (FStar_Util.string_of_int (n' - n))
in (let _149_663 = (FStar_Util.string_of_int n)
in (FStar_Util.format3 "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments." _149_665 _149_664 _149_663))))
in FStar_Syntax_Syntax.Err (_149_666))
in (Prims.raise _149_667))
end else begin
()
end
in (

let _57_785 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (_57_785) with
| (binders, comp) -> begin
(

let rec final_type = (fun subst _57_790 args -> (match (_57_790) with
| (binders, comp) -> begin
(match (((binders), (args))) with
| ([], []) -> begin
(let _149_675 = (let _149_674 = (FStar_Syntax_Subst.subst_comp subst comp)
in _149_674.FStar_Syntax_Syntax.n)
in (nm_of_comp _149_675))
end
| (binders, []) -> begin
(match ((let _149_678 = (let _149_677 = (let _149_676 = (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))))
in (FStar_Syntax_Subst.subst subst _149_676))
in (FStar_Syntax_Subst.compress _149_677))
in _149_678.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(let _149_682 = (let _149_681 = (let _149_680 = (let _149_679 = (FStar_Syntax_Subst.close_comp binders comp)
in ((binders), (_149_679)))
in FStar_Syntax_Syntax.Tm_arrow (_149_680))
in (mk _149_681))
in N (_149_682))
end
| _57_803 -> begin
(FStar_All.failwith "wat?")
end)
end
| ([], (_57_808)::_57_806) -> begin
(FStar_All.failwith "just checked that?!")
end
| (((bv, _57_814))::binders, ((arg, _57_820))::args) -> begin
(final_type ((FStar_Syntax_Syntax.NT (((bv), (arg))))::subst) ((binders), (comp)) args)
end)
end))
in (

let final_type = (final_type [] ((binders), (comp)) args)
in (

let _57_825 = (let _149_683 = (string_of_nm final_type)
in (FStar_Util.print1 "[debug]: final type of application is %s\n" _149_683))
in (

let _57_847 = (let _149_700 = (FStar_List.map2 (fun _57_830 _57_833 -> (match (((_57_830), (_57_833))) with
| ((bv, _57_829), (arg, q)) -> begin
(match ((let _149_687 = (let _149_686 = (normalize bv.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Subst.compress _149_686))
in _149_687.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_835) -> begin
(

let arg = (let _149_688 = (normalize arg)
in ((_149_688), (q)))
in ((arg), ((arg)::[])))
end
| _57_839 -> begin
(

let _57_844 = (check_n env arg)
in (match (_57_844) with
| (_57_841, s_arg, u_arg) -> begin
(let _149_699 = (let _149_689 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_arg), (_149_689)))
in (let _149_698 = if (is_C bv.FStar_Syntax_Syntax.sort) then begin
(let _149_695 = (let _149_691 = (FStar_Syntax_Subst.subst env.subst s_arg)
in (let _149_690 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_691), (_149_690))))
in (let _149_694 = (let _149_693 = (let _149_692 = (FStar_Syntax_Syntax.as_implicit false)
in ((u_arg), (_149_692)))
in (_149_693)::[])
in (_149_695)::_149_694))
end else begin
(let _149_697 = (let _149_696 = (FStar_Syntax_Syntax.as_implicit false)
in ((u_arg), (_149_696)))
in (_149_697)::[])
end
in ((_149_699), (_149_698))))
end))
end)
end)) binders args)
in (FStar_List.split _149_700))
in (match (_57_847) with
| (s_args, u_args) -> begin
(

let u_args = (FStar_List.flatten u_args)
in (let _149_702 = (mk (FStar_Syntax_Syntax.Tm_app (((s_head), (s_args)))))
in (let _149_701 = (mk (FStar_Syntax_Syntax.Tm_app (((u_head), (u_args)))))
in ((final_type), (_149_702), (_149_701)))))
end)))))
end))))))
end)))
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
(let _149_704 = (let _149_703 = (env.tc_const c)
in N (_149_703))
in ((_149_704), (e), (e)))
end
| FStar_Syntax_Syntax.Tm_let (_57_878) -> begin
(let _149_706 = (let _149_705 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_let %s" _149_705))
in (FStar_All.failwith _149_706))
end
| FStar_Syntax_Syntax.Tm_type (_57_881) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_884) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_57_887) -> begin
(let _149_708 = (let _149_707 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_refine %s" _149_707))
in (FStar_All.failwith _149_708))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_890) -> begin
(let _149_710 = (let _149_709 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_uvar %s" _149_709))
in (FStar_All.failwith _149_710))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_893) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _149_715 = (let _149_714 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_unknown %s" _149_714))
in (FStar_All.failwith _149_715))
end)))))
and mk_match : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e0 branches f -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e0.FStar_Syntax_Syntax.pos))
in (

let _57_906 = (check_n env e0)
in (match (_57_906) with
| (_57_903, s_e0, u_e0) -> begin
(

let _57_923 = (let _149_731 = (FStar_List.map (fun b -> (match ((FStar_Syntax_Subst.open_branch b)) with
| (pat, None, body) -> begin
(

let env = (

let _57_912 = env
in (let _149_730 = (let _149_729 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env.env _149_729))
in {env = _149_730; definitions = _57_912.definitions; subst = _57_912.subst; tc_const = _57_912.tc_const}))
in (

let _57_918 = (f env body)
in (match (_57_918) with
| (nm, s_body, u_body) -> begin
((nm), (((pat), (None), (((s_body), (u_body))))))
end)))
end
| _57_920 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("No when clauses in the definition language")))
end)) branches)
in (FStar_List.split _149_731))
in (match (_57_923) with
| (nms, branches) -> begin
(

let t1 = (match ((FStar_List.hd nms)) with
| (M (t1)) | (N (t1)) -> begin
t1
end)
in (

let has_m = (FStar_List.existsb (fun _57_6 -> (match (_57_6) with
| M (_57_930) -> begin
true
end
| _57_933 -> begin
false
end)) nms)
in (

let _57_968 = (let _149_742 = (FStar_List.map2 (fun nm _57_941 -> (match (_57_941) with
| (pat, guard, (s_body, u_body)) -> begin
(

let check = (fun t t' -> if (not ((let _149_739 = (FStar_TypeChecker_Rel.teq env.env t' t)
in (FStar_TypeChecker_Rel.is_trivial _149_739)))) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("[infer]: branches do not have the same type")))
end else begin
()
end)
in (match (((nm), (has_m))) with
| ((N (t2), false)) | ((M (t2), true)) -> begin
(

let _57_952 = (check t2 t1)
in ((nm), (((pat), (guard), (s_body))), (((pat), (guard), (u_body)))))
end
| (N (t2), true) -> begin
(

let _57_958 = (check t2 t1)
in (let _149_741 = (let _149_740 = (mk_return env t2 s_body)
in ((pat), (guard), (_149_740)))
in ((M (t2)), (_149_741), (((pat), (guard), (u_body))))))
end
| (M (_57_961), false) -> begin
(FStar_All.failwith "impossible")
end))
end)) nms branches)
in (FStar_List.unzip3 _149_742))
in (match (_57_968) with
| (nms, s_branches, u_branches) -> begin
(

let s_branches = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (let _149_744 = (mk (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches)))))
in (let _149_743 = (mk (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches)))))
in ((if has_m then begin
M (t1)
end else begin
N (t1)
end), (_149_744), (_149_743))))))
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

let x_binders = (let _149_764 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_764)::[])
in (

let _57_983 = (FStar_Syntax_Subst.open_term x_binders e2)
in (match (_57_983) with
| (x_binders, e2) -> begin
(match ((infer env e1)) with
| (N (t1), s_e1, u_e1) -> begin
(

let env = (

let _57_989 = env
in (let _149_765 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_991 = x
in {FStar_Syntax_Syntax.ppname = _57_991.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_991.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _149_765; definitions = _57_989.definitions; subst = _57_989.subst; tc_const = _57_989.tc_const}))
in (

let _57_997 = (proceed env e2)
in (match (_57_997) with
| (nm_rec, s_e2, u_e2) -> begin
(let _149_773 = (let _149_768 = (let _149_767 = (let _149_766 = (FStar_Syntax_Subst.close x_binders s_e2)
in ((((false), (((

let _57_998 = binding
in {FStar_Syntax_Syntax.lbname = _57_998.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_998.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_998.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_998.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = s_e1}))::[]))), (_149_766)))
in FStar_Syntax_Syntax.Tm_let (_149_767))
in (mk _149_768))
in (let _149_772 = (let _149_771 = (let _149_770 = (let _149_769 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _57_1000 = binding
in {FStar_Syntax_Syntax.lbname = _57_1000.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_1000.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1000.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1000.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_149_769)))
in FStar_Syntax_Syntax.Tm_let (_149_770))
in (mk _149_771))
in ((nm_rec), (_149_773), (_149_772))))
end)))
end
| (M (t1), s_e1, u_e1) -> begin
(

let env = (

let _57_1007 = env
in (let _149_774 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_1009 = x
in {FStar_Syntax_Syntax.ppname = _57_1009.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1009.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _149_774; definitions = _57_1007.definitions; subst = _57_1007.subst; tc_const = _57_1007.tc_const}))
in (

let _57_1015 = (ensure_m env e2)
in (match (_57_1015) with
| (t2, s_e2, u_e2) -> begin
(

let p_type = (mk_star_to_type mk env t2)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" None p_type)
in (

let s_e2 = (let _149_780 = (let _149_779 = (let _149_778 = (let _149_777 = (let _149_776 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _149_775 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_776), (_149_775))))
in (_149_777)::[])
in ((s_e2), (_149_778)))
in FStar_Syntax_Syntax.Tm_app (_149_779))
in (mk _149_780))
in (

let s_e2 = (FStar_Syntax_Util.abs x_binders s_e2 None)
in (

let body = (let _149_785 = (let _149_784 = (let _149_783 = (let _149_782 = (let _149_781 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_e2), (_149_781)))
in (_149_782)::[])
in ((s_e1), (_149_783)))
in FStar_Syntax_Syntax.Tm_app (_149_784))
in (mk _149_785))
in (let _149_792 = (let _149_787 = (let _149_786 = (FStar_Syntax_Syntax.mk_binder p)
in (_149_786)::[])
in (FStar_Syntax_Util.abs _149_787 body None))
in (let _149_791 = (let _149_790 = (let _149_789 = (let _149_788 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _57_1021 = binding
in {FStar_Syntax_Syntax.lbname = _57_1021.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_1021.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1021.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1021.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_149_788)))
in FStar_Syntax_Syntax.Tm_let (_149_789))
in (mk _149_790))
in ((M (t2)), (_149_792), (_149_791)))))))))
end)))
end)
end)))))))
and check_n : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _149_795 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in N (_149_795))
in (match ((check env e mn)) with
| (N (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_1032 -> begin
(FStar_All.failwith "[check_n]: impossible")
end)))
and check_m : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _149_798 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in M (_149_798))
in (match ((check env e mn)) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_1042 -> begin
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

let _57_1064 = if (not ((is_C c))) then begin
(FStar_All.failwith "not a C")
end else begin
()
end
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos))
in (match ((let _149_807 = (FStar_Syntax_Subst.compress c)
in _149_807.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_1074 = (FStar_Syntax_Util.head_and_args wp)
in (match (_57_1074) with
| (wp_head, wp_args) -> begin
(

let _57_1075 = if ((not (((FStar_List.length wp_args) = (FStar_List.length args)))) || (not ((let _149_808 = (FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length wp_args) FStar_Range.dummyRange)
in (FStar_Syntax_Util.is_constructor wp_head _149_808))))) then begin
(FStar_All.failwith "mismatch")
end else begin
()
end
in (let _149_815 = (let _149_814 = (let _149_813 = (FStar_List.map2 (fun _57_1080 _57_1084 -> (match (((_57_1080), (_57_1084))) with
| ((arg, _57_1079), (wp_arg, _57_1083)) -> begin
(let _149_812 = (trans_F env arg wp_arg)
in (let _149_811 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_812), (_149_811))))
end)) args wp_args)
in ((head), (_149_813)))
in FStar_Syntax_Syntax.Tm_app (_149_814))
in (mk _149_815)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let binders = (FStar_Syntax_Subst.open_binders binders)
in (

let _57_1092 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (_57_1092) with
| (binders, comp) -> begin
(

let _57_1101 = (let _149_827 = (FStar_List.map (fun _57_1095 -> (match (_57_1095) with
| (bv, q) -> begin
(

let h = bv.FStar_Syntax_Syntax.sort
in if (is_C h) then begin
(

let w' = (let _149_817 = (star_type env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-w\'") None _149_817))
in (let _149_823 = (let _149_822 = (FStar_Syntax_Syntax.mk_binder w')
in (let _149_821 = (let _149_820 = (let _149_819 = (let _149_818 = (FStar_Syntax_Syntax.bv_to_name bv)
in (trans_F env h _149_818))
in (FStar_Syntax_Syntax.null_binder _149_819))
in (_149_820)::[])
in (_149_822)::_149_821))
in ((w'), (_149_823))))
end else begin
(

let x = (let _149_824 = (star_type env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-x") None _149_824))
in (let _149_826 = (let _149_825 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_825)::[])
in ((x), (_149_826))))
end)
end)) binders)
in (FStar_List.split _149_827))
in (match (_57_1101) with
| (bvs, binders) -> begin
(

let binders = (FStar_List.flatten binders)
in (

let app = (let _149_833 = (let _149_832 = (let _149_831 = (FStar_List.map (fun bv -> (let _149_830 = (FStar_Syntax_Syntax.bv_to_name bv)
in (let _149_829 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_830), (_149_829))))) bvs)
in ((wp), (_149_831)))
in FStar_Syntax_Syntax.Tm_app (_149_832))
in (mk _149_833))
in (

let comp = (let _149_835 = (type_of_comp comp)
in (let _149_834 = (is_monadic_comp comp)
in (trans_G env _149_835 _149_834 app)))
in (

let comp = (FStar_Syntax_Subst.close_comp binders comp)
in (

let binders = (FStar_Syntax_Subst.close_binders binders)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp))))))))))
end))
end)))
end
| _57_1109 -> begin
(FStar_All.failwith "impossible trans_F")
end))))
and trans_G : env_  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env h is_monadic wp -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None h.FStar_Syntax_Syntax.pos))
in if is_monadic then begin
(let _149_846 = (let _149_845 = (star_type env h)
in (let _149_844 = (let _149_843 = (let _149_842 = (FStar_Syntax_Syntax.as_implicit false)
in ((wp), (_149_842)))
in (_149_843)::[])
in {FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _149_845; FStar_Syntax_Syntax.effect_args = _149_844; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp _149_846))
end else begin
(let _149_847 = (trans_F env h wp)
in (FStar_Syntax_Syntax.mk_Total _149_847))
end))


let star_expr_definition : env  ->  FStar_Syntax_Syntax.term  ->  (env * (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)) = (fun env t -> (star_definition env t (fun env e -> (

let _57_1123 = (check_n env e)
in (match (_57_1123) with
| (t, s_e, s_u) -> begin
((t), (((s_e), (s_u))))
end)))))




