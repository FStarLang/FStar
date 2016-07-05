
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
in FStar_Syntax_Syntax.Tm_arrow ((binders, comp))))
end
| FStar_Syntax_Syntax.Tm_abs (binders, term, comp) -> begin
(

let comp = (visit_maybe_lcomp comp)
in (

let term = (visit_term term)
in (

let binders = (FStar_List.map visit_binder binders)
in FStar_Syntax_Syntax.Tm_abs ((binders, term, comp)))))
end
| _57_39 -> begin
tm.FStar_Syntax_Syntax.n
end)
in (

let _57_41 = tm
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_41.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_41.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_41.FStar_Syntax_Syntax.vars})))
and visit_binder = (fun _57_45 -> (match (_57_45) with
| (bv, a) -> begin
(let _149_28 = (

let _57_46 = bv
in (let _149_26 = (visit_term bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_46.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_46.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_26}))
in (let _149_27 = (FStar_Syntax_Syntax.as_implicit false)
in (_149_28, _149_27)))
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

let _57_60 = comp
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_60.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_60.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_60.FStar_Syntax_Syntax.vars})))
and visit_args = (fun args -> (FStar_List.map (fun _57_65 -> (match (_57_65) with
| (tm, q) -> begin
(let _149_39 = (visit_term tm)
in (_149_39, q))
end)) args))
in (visit_term tm))))
in (

let check = (fun str t -> if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _57_69 = (let _149_44 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Generated term for %s: %s\n" str _149_44))
in (

let t = (normalize t)
in (

let t = (FStar_Syntax_Subst.compress t)
in (

let _57_84 = (tc_term env t)
in (match (_57_84) with
| (e, {FStar_Syntax_Syntax.eff_name = _57_80; FStar_Syntax_Syntax.res_typ = res_typ; FStar_Syntax_Syntax.cflags = _57_77; FStar_Syntax_Syntax.comp = _57_75}, _57_83) -> begin
(

let _57_85 = (let _149_47 = (let _149_46 = (normalize res_typ)
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
| _57_96 -> begin
(FStar_All.failwith "wp_a contains non-Tot arrow")
end)
in (let _149_53 = (collect_binders rest)
in (FStar_List.append bs _149_53)))
end
| FStar_Syntax_Syntax.Tm_type (_57_99) -> begin
[]
end
| _57_102 -> begin
(FStar_All.failwith "wp_a doesn\'t end in Type0")
end))
in (

let _57_117 = (

let i = (FStar_ST.alloc 0)
in (

let wp_binders = (let _149_60 = (normalize wp_a)
in (collect_binders _149_60))
in ((fun t -> (let _149_66 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow wp_binders _149_66))), (fun t -> (let _149_69 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow wp_binders _149_69))), (fun _57_107 -> (match (()) with
| () -> begin
(FStar_List.map (fun _57_111 -> (match (_57_111) with
| (bv, _57_110) -> begin
(

let _57_112 = (let _149_73 = ((FStar_ST.read i) + 1)
in (FStar_ST.op_Colon_Equals i _149_73))
in (let _149_76 = (let _149_75 = (let _149_74 = (FStar_ST.read i)
in (FStar_Util.string_of_int _149_74))
in (Prims.strcat "g" _149_75))
in (FStar_Syntax_Syntax.gen_bv _149_76 None bv.FStar_Syntax_Syntax.sort)))
end)) wp_binders)
end)))))
in (match (_57_117) with
| (mk_ctx, mk_gctx, mk_gamma) -> begin
(

let binders_of_list = (FStar_List.map (fun _57_120 -> (match (_57_120) with
| (t, b) -> begin
(let _149_82 = (FStar_Syntax_Syntax.as_implicit b)
in (t, _149_82))
end)))
in (

let implicit_binders_of_list = (FStar_List.map (fun t -> (let _149_85 = (FStar_Syntax_Syntax.as_implicit true)
in (t, _149_85))))
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
in (let _149_97 = (binders_of_list (((t, true))::((x, false))::[]))
in (FStar_Syntax_Util.abs _149_97 body ret)))))))
in (

let _57_132 = (let _149_101 = (let _149_100 = (let _149_99 = (let _149_98 = (FStar_Syntax_Syntax.mk_binder a)
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
in (let _149_124 = (binders_of_list (((t1, true))::((t2, true))::((l, false))::((r, false))::[]))
in (FStar_Syntax_Util.abs _149_124 outer_body ret))))))))
in (

let _57_144 = (let _149_128 = (let _149_127 = (let _149_126 = (let _149_125 = (FStar_Syntax_Syntax.mk_binder a)
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
in (let _149_153 = (binders_of_list (((t1, true))::((t2, true))::((f, false))::((a1, false))::[]))
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

let _57_154 = (let _149_157 = (let _149_156 = (let _149_155 = (let _149_154 = (FStar_Syntax_Syntax.mk_binder a)
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
in (let _149_194 = (binders_of_list (((t1, true))::((t2, true))::((t3, true))::((f, false))::((a1, false))::((a2, false))::[]))
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

let _57_165 = (let _149_198 = (let _149_197 = (let _149_196 = (let _149_195 = (FStar_Syntax_Syntax.mk_binder a)
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
in (let _149_226 = (binders_of_list (((t1, true))::((t2, true))::((f, false))::[]))
in (FStar_Syntax_Util.abs _149_226 body ret))))))))))
in (

let _57_176 = (let _149_230 = (let _149_229 = (let _149_228 = (let _149_227 = (FStar_Syntax_Syntax.mk_binder a)
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

let _57_183 = (let _149_245 = (FStar_Syntax_Util.abs binders wp_if_then_else None)
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

let _57_191 = (let _149_261 = (FStar_Syntax_Util.abs binders wp_assert None)
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

let _57_199 = (let _149_277 = (FStar_Syntax_Util.abs binders wp_assume None)
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

let _57_208 = (let _149_299 = (FStar_Syntax_Util.abs binders wp_close None)
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
in (tforall, _149_314))
in FStar_Syntax_Syntax.Tm_app (_149_315))
in (FStar_Syntax_Syntax.mk _149_316 None FStar_Range.dummyRange))))
in (

let rec mk_leq = (fun t x y -> (match ((let _149_324 = (let _149_323 = (FStar_Syntax_Subst.compress t)
in (normalize _149_323))
in _149_324.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_220) -> begin
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

let _57_256 = t
in (let _149_341 = (let _149_340 = (let _149_339 = (let _149_338 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _149_338))
in ((binder)::[], _149_339))
in FStar_Syntax_Syntax.Tm_arrow (_149_340))
in {FStar_Syntax_Syntax.n = _149_341; FStar_Syntax_Syntax.tk = _57_256.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_256.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_256.FStar_Syntax_Syntax.vars}))
in (mk_leq t x y))
end
| FStar_Syntax_Syntax.Tm_arrow (_57_260) -> begin
(FStar_All.failwith "unhandled arrow")
end
| _57_263 -> begin
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

let _57_268 = (let _149_348 = (let _149_347 = (let _149_346 = (let _149_345 = (FStar_Syntax_Syntax.mk_binder a)
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

let _57_275 = (let _149_358 = (FStar_Syntax_Util.abs binders wp_trivial None)
in (check "wp_trivial" _149_358))
in (

let _57_277 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_277.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_277.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_277.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_277.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_277.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _57_277.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _57_277.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = ([], wp_if_then_else); FStar_Syntax_Syntax.ite_wp = _57_277.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _57_277.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = ([], wp_close); FStar_Syntax_Syntax.assert_p = ([], wp_assert); FStar_Syntax_Syntax.assume_p = ([], wp_assume); FStar_Syntax_Syntax.null_wp = _57_277.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = ([], wp_trivial); FStar_Syntax_Syntax.repr = _57_277.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _57_277.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _57_277.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _57_277.FStar_Syntax_Syntax.actions}))))))))))))))))))))))))))))))))))))))
end))))))))


type env =
{env : FStar_TypeChecker_Env.env; definitions : (FStar_Ident.lid * FStar_Syntax_Syntax.typ) Prims.list}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))


let empty : FStar_TypeChecker_Env.env  ->  env = (fun env -> {env = env; definitions = []})


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
| N (_57_285) -> begin
_57_285
end))


let ___M____0 = (fun projectee -> (match (projectee) with
| M (_57_288) -> begin
_57_288
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
| _57_295 -> begin
(FStar_All.failwith "[nm_of_comp]: impossible")
end))


let is_monadic_arrow : FStar_Syntax_Syntax.term'  ->  nm = (fun n -> (match (n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_298, {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_304; FStar_Syntax_Syntax.pos = _57_302; FStar_Syntax_Syntax.vars = _57_300}) -> begin
(nm_of_comp n)
end
| _57_310 -> begin
(FStar_All.failwith "unexpected_argument: [is_monadic_arrow]")
end))


let rec mk_star_to_type : (FStar_Syntax_Syntax.term'  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun mk env a -> (let _149_420 = (let _149_419 = (let _149_418 = (let _149_416 = (let _149_415 = (let _149_413 = (star_type env a)
in (FStar_Syntax_Syntax.null_bv _149_413))
in (let _149_414 = (FStar_Syntax_Syntax.as_implicit false)
in (_149_415, _149_414)))
in (_149_416)::[])
in (let _149_417 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype)
in (_149_418, _149_417)))
in FStar_Syntax_Syntax.Tm_arrow (_149_419))
in (mk _149_420)))
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
| FStar_Syntax_Syntax.Tm_arrow (binders, _57_324) -> begin
(

let binders = (FStar_List.map (fun _57_329 -> (match (_57_329) with
| (bv, aqual) -> begin
(let _149_430 = (

let _57_330 = bv
in (let _149_429 = (star_type env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_330.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_330.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_429}))
in (_149_430, aqual))
end)) binders)
in (match ((is_monadic_arrow t.FStar_Syntax_Syntax.n)) with
| N (hn) -> begin
(let _149_434 = (let _149_433 = (let _149_432 = (let _149_431 = (star_type env hn)
in (FStar_Syntax_Syntax.mk_Total _149_431))
in (binders, _149_432))
in FStar_Syntax_Syntax.Tm_arrow (_149_433))
in (mk _149_434))
end
| M (a) -> begin
(let _149_443 = (let _149_442 = (let _149_441 = (let _149_439 = (let _149_438 = (let _149_437 = (let _149_435 = (mk_star_to_type env a)
in (FStar_Syntax_Syntax.null_bv _149_435))
in (let _149_436 = (FStar_Syntax_Syntax.as_implicit false)
in (_149_437, _149_436)))
in (_149_438)::[])
in (FStar_List.append binders _149_439))
in (let _149_440 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype)
in (_149_441, _149_440)))
in FStar_Syntax_Syntax.Tm_arrow (_149_442))
in (mk _149_443))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let rec is_valid_application = (fun head -> (match ((let _149_446 = (FStar_Syntax_Subst.compress head)
in _149_446.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.option_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.either_lid)) || (let _149_447 = (FStar_Syntax_Subst.compress head)
in (FStar_Syntax_Util.is_tuple_constructor _149_447))) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uinst (head, _57_347) -> begin
(is_valid_application head)
end
| _57_351 -> begin
false
end))
in if (is_valid_application head) then begin
(let _149_452 = (let _149_451 = (let _149_450 = (FStar_List.map (fun _57_354 -> (match (_57_354) with
| (t, qual) -> begin
(let _149_449 = (star_type env t)
in (_149_449, qual))
end)) args)
in (head, _149_450))
in FStar_Syntax_Syntax.Tm_app (_149_451))
in (mk _149_452))
end else begin
(let _149_455 = (let _149_454 = (let _149_453 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "For now, only [either] and [option] are supported in the definition language (got: %s)" _149_453))
in FStar_Syntax_Syntax.Err (_149_454))
in (Prims.raise _149_455))
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

let _57_374 = env
in (let _149_456 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _149_456; definitions = _57_374.definitions}))
in (

let repr = (star_type env repr)
in (

let repr = (FStar_Syntax_Subst.close binders repr)
in (mk (FStar_Syntax_Syntax.Tm_abs ((binders, repr, something)))))))))
end
| (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_match (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _149_459 = (let _149_458 = (let _149_457 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "The following term is outside of the definition language: %s" _149_457))
in FStar_Syntax_Syntax.Err (_149_458))
in (Prims.raise _149_459))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_408) -> begin
(FStar_All.failwith "impossible")
end)))))))


let star_definition = (fun env t f -> (match ((let _149_472 = (FStar_Syntax_Subst.compress t)
in _149_472.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = lid; FStar_Syntax_Syntax.fv_delta = _57_416; FStar_Syntax_Syntax.fv_qual = _57_414}) -> begin
(

let _57_420 = (FStar_Util.print1 "Recording definition of %s\n" (FStar_Ident.text_of_lid lid.FStar_Syntax_Syntax.v))
in (

let _57_434 = (match ((let _149_474 = (FStar_TypeChecker_Env.lookup_definition (FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant)) env.env lid.FStar_Syntax_Syntax.v)
in (let _149_473 = (FStar_TypeChecker_Env.lookup_lid env.env lid.FStar_Syntax_Syntax.v)
in (_149_474, _149_473)))) with
| (Some ([], e), ([], t)) -> begin
(f env e)
end
| _57_431 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Bad definition in [star_type_definition]")))
end)
in (match (_57_434) with
| (store, ret) -> begin
((

let _57_435 = env
in {env = _57_435.env; definitions = ((lid.FStar_Syntax_Syntax.v, store))::env.definitions}), ret)
end)))
end
| FStar_Syntax_Syntax.Tm_uinst (_57_438) -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Ill-formed definition (hint: use Type0, not Type)")))
end
| _57_441 -> begin
(let _149_477 = (let _149_476 = (let _149_475 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Ill-formed definition: %s" _149_475))
in FStar_Syntax_Syntax.Err (_149_476))
in (Prims.raise _149_477))
end))


let star_type_definition : env  ->  FStar_Syntax_Syntax.term  ->  (env * FStar_Syntax_Syntax.term) = (fun env t -> (star_definition env t (fun env e -> (

let t = (star_type env e)
in (t, t)))))


let is_monadic : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  Prims.bool = (fun _57_2 -> (match (_57_2) with
| None -> begin
(FStar_All.failwith "un-annotated lambda?!")
end
| (Some (FStar_Util.Inl ({FStar_Syntax_Syntax.eff_name = lid; FStar_Syntax_Syntax.res_typ = _; FStar_Syntax_Syntax.cflags = _; FStar_Syntax_Syntax.comp = _}))) | (Some (FStar_Util.Inr (lid))) -> begin
(FStar_Ident.lid_equals lid FStar_Syntax_Const.monadic_lid)
end))


let mk_return : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let p_type = (mk_star_to_type mk env t)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p" None p_type)
in (

let body = (let _149_499 = (let _149_498 = (let _149_497 = (mk (FStar_Syntax_Syntax.Tm_bvar (p)))
in (let _149_496 = (let _149_495 = (let _149_494 = (FStar_Syntax_Syntax.as_implicit false)
in (e, _149_494))
in (_149_495)::[])
in (_149_497, _149_496)))
in FStar_Syntax_Syntax.Tm_app (_149_498))
in (mk _149_499))
in (let _149_501 = (let _149_500 = (FStar_Syntax_Syntax.mk_binder p)
in (_149_500)::[])
in (FStar_Syntax_Util.abs _149_501 body None)))))))


let is_unknown : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun _57_3 -> (match (_57_3) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| _57_472 -> begin
false
end))


let rec check : env  ->  FStar_Syntax_Syntax.term  ->  nm  ->  (nm * FStar_Syntax_Syntax.term) = (fun env e context_nm -> (

let _57_476 = (let _149_539 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "[debug]: check %s\n" _149_539))
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let return_if = (fun _57_483 -> (match (_57_483) with
| (rec_nm, e) -> begin
(

let check = (fun t1 t2 -> if ((not ((is_unknown t2.FStar_Syntax_Syntax.n))) && (not ((let _149_548 = (FStar_TypeChecker_Rel.teq env.env t1 t2)
in (FStar_TypeChecker_Rel.is_trivial _149_548))))) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("[check]: term does not have the expected type")))
end else begin
()
end)
in (match ((rec_nm, e, context_nm)) with
| ((N (t1), e, N (t2))) | ((M (t1), e, M (t2))) -> begin
(

let _57_496 = (check t1 t2)
in (rec_nm, e))
end
| (N (t1), e, M (t2)) -> begin
(

let _57_504 = (check t1 t2)
in (let _149_549 = (mk_return env t1 e)
in (M (t1), _149_549)))
end
| (M (_57_507), _57_510, N (_57_512)) -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("[check]: got an effectful computation in lieu of a pure computation")))
end))
end))
in (match ((let _149_550 = (FStar_Syntax_Subst.compress e)
in _149_550.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_bvar (bv)) | (FStar_Syntax_Syntax.Tm_name (bv)) -> begin
(

let t' = (FStar_TypeChecker_Env.lookup_bv env.env bv)
in (return_if (N (t'), e)))
end
| FStar_Syntax_Syntax.Tm_abs (_57_520) -> begin
(let _149_551 = (infer env e)
in (return_if _149_551))
end
| FStar_Syntax_Syntax.Tm_app (_57_523) -> begin
(let _149_552 = (infer env e)
in (return_if _149_552))
end
| FStar_Syntax_Syntax.Tm_let ((false, (binding)::[]), e2) -> begin
(mk_let env binding e2 (fun env e2 -> (check env e2 context_nm)) (fun env e2 -> (

let strip_m = (fun _57_4 -> (match (_57_4) with
| (M (t), e) -> begin
(t, e)
end
| _57_540 -> begin
(FStar_All.failwith "impossible")
end))
in (match (context_nm) with
| N (t) -> begin
(let _149_559 = (check env e2 (M (t)))
in (strip_m _149_559))
end
| M (_57_545) -> begin
(let _149_560 = (check env e2 context_nm)
in (strip_m _149_560))
end))))
end
| FStar_Syntax_Syntax.Tm_match (e0, branches) -> begin
(mk_match env e0 branches (fun env body -> (check env body context_nm)))
end
| _57_556 -> begin
(let _149_566 = (let _149_565 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: todo %s" _149_565))
in (FStar_All.failwith _149_566))
end)))))
and infer : env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term) = (fun env e -> (

let _57_559 = (let _149_569 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "[debug]: infer %s\n" _149_569))
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.env)
in (match ((let _149_573 = (FStar_Syntax_Subst.compress e)
in _149_573.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_bvar (bv)) | (FStar_Syntax_Syntax.Tm_name (bv)) -> begin
(let _149_575 = (let _149_574 = (FStar_TypeChecker_Env.lookup_bv env.env bv)
in N (_149_574))
in (_149_575, e))
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

let _57_575 = env
in (let _149_576 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _149_576; definitions = _57_575.definitions}))
in (

let binders = (FStar_List.map (fun _57_580 -> (match (_57_580) with
| (bv, qual) -> begin
(

let sort = (star_type env bv.FStar_Syntax_Syntax.sort)
in ((

let _57_582 = bv
in {FStar_Syntax_Syntax.ppname = _57_582.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_582.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort}), qual))
end)) binders)
in (

let _57_591 = (

let check_what = if (is_monadic what) then begin
check_m
end else begin
check_n
end
in (

let _57_588 = (check_what env body)
in (match (_57_588) with
| (t, body) -> begin
(let _149_583 = (let _149_582 = if (is_monadic what) then begin
M (t)
end else begin
N (t)
end
in (comp_of_nm _149_582))
in (_149_583, body))
end)))
in (match (_57_591) with
| (comp, body) -> begin
(

let body = (FStar_Syntax_Subst.close binders body)
in (

let t = (

let binders = (FStar_List.map (fun _57_596 -> (match (_57_596) with
| (bv, _57_595) -> begin
(let _149_585 = (FStar_Syntax_Syntax.null_bv bv.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_binder _149_585))
end)) binders)
in (

let binders = (FStar_Syntax_Subst.close_binders binders)
in (mk (FStar_Syntax_Syntax.Tm_arrow ((binders, comp))))))
in (

let binders = (FStar_Syntax_Subst.close_binders binders)
in (let _149_586 = (mk (FStar_Syntax_Syntax.Tm_abs ((binders, body, what))))
in (N (t), _149_586)))))
end)))))))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_607 = (check_n env head)
in (match (_57_607) with
| (t_head, head) -> begin
(

let t_head = (normalize t_head)
in (match ((let _149_587 = (FStar_Syntax_Subst.compress t_head)
in _149_587.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let _57_615 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (_57_615) with
| (binders, comp) -> begin
(

let _57_629 = (let _149_590 = (FStar_List.map2 (fun _57_619 _57_622 -> (match ((_57_619, _57_622)) with
| ((bv, _57_618), (arg, q)) -> begin
(

let _57_626 = (check env arg (N (bv.FStar_Syntax_Syntax.sort)))
in (match (_57_626) with
| (_57_624, starred_arg) -> begin
((starred_arg, q), FStar_Syntax_Syntax.NT ((bv, arg)))
end))
end)) binders args)
in (FStar_List.split _149_590))
in (match (_57_629) with
| (args, subst_elts) -> begin
(

let comp = (FStar_Syntax_Subst.subst_comp subst_elts comp)
in (let _149_592 = (nm_of_comp comp.FStar_Syntax_Syntax.n)
in (let _149_591 = (mk (FStar_Syntax_Syntax.Tm_app ((head, args))))
in (_149_592, _149_591))))
end))
end))
end
| _57_632 -> begin
(let _149_595 = (let _149_594 = (let _149_593 = (FStar_Syntax_Print.term_to_string t_head)
in (FStar_Util.format1 "%s: not a function type" _149_593))
in FStar_Syntax_Syntax.Err (_149_594))
in (Prims.raise _149_595))
end))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, (binding)::[]), e2) -> begin
(mk_let env binding e2 infer check_m)
end
| FStar_Syntax_Syntax.Tm_match (e0, branches) -> begin
(mk_match env e0 branches infer)
end
| _57_645 -> begin
(let _149_597 = (let _149_596 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: todo %s" _149_596))
in (FStar_All.failwith _149_597))
end)))))
and mk_match : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term))  ->  (nm * FStar_Syntax_Syntax.term) = (fun env e0 branches f -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e0.FStar_Syntax_Syntax.pos))
in (

let _57_655 = (check_n env e0)
in (match (_57_655) with
| (_57_653, e0) -> begin
(

let _57_671 = (let _149_613 = (FStar_List.map (fun b -> (match ((FStar_Syntax_Subst.open_branch b)) with
| (pat, None, body) -> begin
(

let env = (

let _57_661 = env
in (let _149_612 = (let _149_611 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env.env _149_611))
in {env = _149_612; definitions = _57_661.definitions}))
in (

let _57_666 = (f env body)
in (match (_57_666) with
| (nm, body) -> begin
(nm, (pat, None, body))
end)))
end
| _57_668 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("No when clauses in the definition language")))
end)) branches)
in (FStar_List.split _149_613))
in (match (_57_671) with
| (nms, branches) -> begin
(

let t1 = (match ((FStar_List.hd nms)) with
| (M (t1)) | (N (t1)) -> begin
t1
end)
in (

let has_m = (FStar_List.existsb (fun _57_5 -> (match (_57_5) with
| M (_57_678) -> begin
true
end
| _57_681 -> begin
false
end)) nms)
in (

let _57_713 = (let _149_624 = (FStar_List.map2 (fun nm _57_687 -> (match (_57_687) with
| (pat, guard, body) -> begin
(

let check = (fun t t' -> if (not ((let _149_621 = (FStar_TypeChecker_Rel.teq env.env t' t)
in (FStar_TypeChecker_Rel.is_trivial _149_621)))) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("[infer]: branches do not have the same type")))
end else begin
()
end)
in (match ((nm, has_m)) with
| ((N (t2), false)) | ((M (t2), true)) -> begin
(

let _57_698 = (check t2 t1)
in (nm, (pat, guard, body)))
end
| (N (t2), true) -> begin
(

let _57_704 = (check t2 t1)
in (let _149_623 = (let _149_622 = (mk_return env t2 body)
in (pat, guard, _149_622))
in (M (t2), _149_623)))
end
| (M (_57_707), false) -> begin
(FStar_All.failwith "impossible")
end))
end)) nms branches)
in (FStar_List.split _149_624))
in (match (_57_713) with
| (nms, branches) -> begin
(

let branches = (FStar_List.map FStar_Syntax_Subst.close_branch branches)
in (let _149_625 = (mk (FStar_Syntax_Syntax.Tm_match ((e0, branches))))
in (if has_m then begin
M (t1)
end else begin
N (t1)
end, _149_625)))
end))))
end))
end))))
and mk_let : env_  ->  FStar_Syntax_Syntax.letbinding  ->  FStar_Syntax_Syntax.term  ->  (env_  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term))  ->  (env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (nm * FStar_Syntax_Syntax.term) = (fun env binding e2 proceed ensure_m -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e2.FStar_Syntax_Syntax.pos))
in (

let e1 = binding.FStar_Syntax_Syntax.lbdef
in (

let x = (FStar_Util.left binding.FStar_Syntax_Syntax.lbname)
in (

let x_binders = (let _149_645 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_645)::[])
in (

let _57_727 = (FStar_Syntax_Subst.open_term x_binders e2)
in (match (_57_727) with
| (x_binders, e2) -> begin
(match ((infer env e1)) with
| (N (t1), e1) -> begin
(

let env = (

let _57_732 = env
in (let _149_646 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_734 = x
in {FStar_Syntax_Syntax.ppname = _57_734.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_734.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _149_646; definitions = _57_732.definitions}))
in (

let _57_739 = (proceed env e2)
in (match (_57_739) with
| (nm_rec, e2) -> begin
(let _149_650 = (let _149_649 = (let _149_648 = (let _149_647 = (FStar_Syntax_Subst.close x_binders e2)
in ((false, ((

let _57_740 = binding
in {FStar_Syntax_Syntax.lbname = _57_740.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_740.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_740.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_740.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e1}))::[]), _149_647))
in FStar_Syntax_Syntax.Tm_let (_149_648))
in (mk _149_649))
in (nm_rec, _149_650))
end)))
end
| (M (t1), e1) -> begin
(

let _57_748 = (ensure_m env e2)
in (match (_57_748) with
| (t2, e2) -> begin
(

let p_type = (mk_star_to_type mk env t2)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p" None p_type)
in (

let e2 = (let _149_656 = (let _149_655 = (let _149_654 = (let _149_653 = (let _149_652 = (mk (FStar_Syntax_Syntax.Tm_bvar (p)))
in (let _149_651 = (FStar_Syntax_Syntax.as_implicit false)
in (_149_652, _149_651)))
in (_149_653)::[])
in (e2, _149_654))
in FStar_Syntax_Syntax.Tm_app (_149_655))
in (mk _149_656))
in (

let e2 = (FStar_Syntax_Util.abs x_binders e2 None)
in (

let body = (let _149_661 = (let _149_660 = (let _149_659 = (let _149_658 = (let _149_657 = (FStar_Syntax_Syntax.as_implicit false)
in (e2, _149_657))
in (_149_658)::[])
in (e1, _149_659))
in FStar_Syntax_Syntax.Tm_app (_149_660))
in (mk _149_661))
in (let _149_664 = (let _149_663 = (let _149_662 = (FStar_Syntax_Syntax.mk_binder p)
in (_149_662)::[])
in (FStar_Syntax_Util.abs _149_663 body None))
in (M (t2), _149_664)))))))
end))
end)
end)))))))
and check_n : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _149_667 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in N (_149_667))
in (match ((check env e mn)) with
| (N (t), e) -> begin
(t, e)
end
| _57_762 -> begin
(FStar_All.failwith "[check_n]: impossible")
end)))
and check_m : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _149_670 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in M (_149_670))
in (match ((check env e mn)) with
| (M (t), e) -> begin
(t, e)
end
| _57_771 -> begin
(FStar_All.failwith "[check_m]: impossible")
end)))
and comp_of_nm : nm_  ->  FStar_Syntax_Syntax.comp = (fun nm -> (match (nm) with
| N (t) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| M (t) -> begin
(mk_M t)
end))
and mk_M : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun t -> (let _149_676 = (let _149_675 = (let _149_674 = (let _149_673 = (FStar_Syntax_Syntax.as_implicit false)
in (t, _149_673))
in (_149_674)::[])
in {FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.monadic_lid; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = _149_675; FStar_Syntax_Syntax.flags = []})
in (FStar_Syntax_Syntax.mk_Comp _149_676)))


let star_expr_definition : env  ->  FStar_Syntax_Syntax.term  ->  (env * FStar_Syntax_Syntax.term) = (fun env t -> (star_definition env t check_n))




