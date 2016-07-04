
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
| _57_35 -> begin
tm.FStar_Syntax_Syntax.n
end)
in (

let _57_37 = tm
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_37.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_37.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_37.FStar_Syntax_Syntax.vars})))
and visit_binder = (fun _57_41 -> (match (_57_41) with
| (bv, a) -> begin
(let _149_28 = (

let _57_42 = bv
in (let _149_26 = (visit_term bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_42.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_42.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_26}))
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

let _57_56 = comp
in {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_56.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_56.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_56.FStar_Syntax_Syntax.vars})))
and visit_args = (fun args -> (FStar_List.map (fun _57_61 -> (match (_57_61) with
| (tm, q) -> begin
(let _149_39 = (visit_term tm)
in (_149_39, q))
end)) args))
in (visit_term tm))))
in (

let check = (fun str t -> if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _57_65 = (let _149_44 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Generated term for %s: %s\n" str _149_44))
in (

let t = (normalize t)
in (

let t = (FStar_Syntax_Subst.compress t)
in (

let _57_80 = (tc_term env t)
in (match (_57_80) with
| (e, {FStar_Syntax_Syntax.eff_name = _57_76; FStar_Syntax_Syntax.res_typ = res_typ; FStar_Syntax_Syntax.cflags = _57_73; FStar_Syntax_Syntax.comp = _57_71}, _57_79) -> begin
(

let _57_81 = (let _149_47 = (let _149_46 = (normalize res_typ)
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
| _57_92 -> begin
(FStar_All.failwith "wp_a contains non-Tot arrow")
end)
in (let _149_53 = (collect_binders rest)
in (FStar_List.append bs _149_53)))
end
| FStar_Syntax_Syntax.Tm_type (_57_95) -> begin
[]
end
| _57_98 -> begin
(FStar_All.failwith "wp_a doesn\'t end in Type0")
end))
in (

let _57_113 = (

let i = (FStar_ST.alloc 0)
in (

let wp_binders = (let _149_60 = (normalize wp_a)
in (collect_binders _149_60))
in ((fun t -> (let _149_66 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow wp_binders _149_66))), (fun t -> (let _149_69 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow wp_binders _149_69))), (fun _57_103 -> (match (()) with
| () -> begin
(FStar_List.map (fun _57_107 -> (match (_57_107) with
| (bv, _57_106) -> begin
(

let _57_108 = (let _149_73 = ((FStar_ST.read i) + 1)
in (FStar_ST.op_Colon_Equals i _149_73))
in (let _149_76 = (let _149_75 = (let _149_74 = (FStar_ST.read i)
in (FStar_Util.string_of_int _149_74))
in (Prims.strcat "g" _149_75))
in (FStar_Syntax_Syntax.gen_bv _149_76 None bv.FStar_Syntax_Syntax.sort)))
end)) wp_binders)
end)))))
in (match (_57_113) with
| (mk_ctx, mk_gctx, mk_gamma) -> begin
(

let binders_of_list = (FStar_List.map (fun _57_116 -> (match (_57_116) with
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

let _57_128 = (let _149_101 = (let _149_100 = (let _149_99 = (let _149_98 = (FStar_Syntax_Syntax.mk_binder a)
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

let _57_140 = (let _149_128 = (let _149_127 = (let _149_126 = (let _149_125 = (FStar_Syntax_Syntax.mk_binder a)
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

let _57_150 = (let _149_157 = (let _149_156 = (let _149_155 = (let _149_154 = (FStar_Syntax_Syntax.mk_binder a)
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

let _57_161 = (let _149_198 = (let _149_197 = (let _149_196 = (let _149_195 = (FStar_Syntax_Syntax.mk_binder a)
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

let _57_172 = (let _149_230 = (let _149_229 = (let _149_228 = (let _149_227 = (FStar_Syntax_Syntax.mk_binder a)
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

let _57_179 = (let _149_245 = (FStar_Syntax_Util.abs binders wp_if_then_else None)
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

let _57_187 = (let _149_261 = (FStar_Syntax_Util.abs binders wp_assert None)
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

let _57_195 = (let _149_277 = (FStar_Syntax_Util.abs binders wp_assume None)
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

let _57_204 = (let _149_299 = (FStar_Syntax_Util.abs binders wp_close None)
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
| FStar_Syntax_Syntax.Tm_type (_57_216) -> begin
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

let _57_252 = t
in (let _149_341 = (let _149_340 = (let _149_339 = (let _149_338 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _149_338))
in ((binder)::[], _149_339))
in FStar_Syntax_Syntax.Tm_arrow (_149_340))
in {FStar_Syntax_Syntax.n = _149_341; FStar_Syntax_Syntax.tk = _57_252.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_252.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_252.FStar_Syntax_Syntax.vars}))
in (mk_leq t x y))
end
| FStar_Syntax_Syntax.Tm_arrow (_57_256) -> begin
(FStar_All.failwith "unhandled arrow")
end
| _57_259 -> begin
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

let _57_264 = (let _149_348 = (let _149_347 = (let _149_346 = (let _149_345 = (FStar_Syntax_Syntax.mk_binder a)
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

let _57_271 = (let _149_358 = (FStar_Syntax_Util.abs binders wp_trivial None)
in (check "wp_trivial" _149_358))
in (

let _57_273 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_273.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_273.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_273.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_273.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_273.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _57_273.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _57_273.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = ([], wp_if_then_else); FStar_Syntax_Syntax.ite_wp = _57_273.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _57_273.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = ([], wp_close); FStar_Syntax_Syntax.assert_p = ([], wp_assert); FStar_Syntax_Syntax.assume_p = ([], wp_assume); FStar_Syntax_Syntax.null_wp = _57_273.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = ([], wp_trivial); FStar_Syntax_Syntax.repr = _57_273.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _57_273.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _57_273.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _57_273.FStar_Syntax_Syntax.actions}))))))))))))))))))))))))))))))))))))))
end))))))))


type n_or_t =
| N of FStar_Syntax_Syntax.typ
| T of FStar_Syntax_Syntax.typ


let is_N = (fun _discr_ -> (match (_discr_) with
| N (_) -> begin
true
end
| _ -> begin
false
end))


let is_T = (fun _discr_ -> (match (_discr_) with
| T (_) -> begin
true
end
| _ -> begin
false
end))


let ___N____0 = (fun projectee -> (match (projectee) with
| N (_57_277) -> begin
_57_277
end))


let ___T____0 = (fun projectee -> (match (projectee) with
| T (_57_280) -> begin
_57_280
end))


let is_monadic : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  Prims.bool = (fun _57_1 -> (match (_57_1) with
| None -> begin
(FStar_All.failwith "un-annotated lambda?!")
end
| (Some (FStar_Util.Inl ({FStar_Syntax_Syntax.eff_name = lid; FStar_Syntax_Syntax.res_typ = _; FStar_Syntax_Syntax.cflags = _; FStar_Syntax_Syntax.comp = _}))) | (Some (FStar_Util.Inr (lid))) -> begin
(FStar_Ident.lid_equals lid FStar_Syntax_Const.monadic_lid)
end))


let is_monadic_arrow : FStar_Syntax_Syntax.term'  ->  n_or_t = (fun n -> (match (n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_297, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = _57_303; FStar_Syntax_Syntax.pos = _57_301; FStar_Syntax_Syntax.vars = _57_299}) when (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.monadic_lid) -> begin
T (c.FStar_Syntax_Syntax.result_typ)
end
| FStar_Syntax_Syntax.Tm_arrow (_57_310, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (t); FStar_Syntax_Syntax.tk = _57_316; FStar_Syntax_Syntax.pos = _57_314; FStar_Syntax_Syntax.vars = _57_312}) -> begin
N (t)
end
| FStar_Syntax_Syntax.Tm_arrow (_57_323) -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Prims.M and Prims.Tot are the only possible effects in the definition language")))
end
| _57_326 -> begin
(FStar_All.failwith "unexpected_argument: [is_monadic_arrow]")
end))


let rec mk_star_to_type : (FStar_Syntax_Syntax.term'  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun mk a -> (let _149_408 = (let _149_407 = (let _149_406 = (let _149_404 = (let _149_403 = (let _149_401 = (star_type a)
in (FStar_Syntax_Syntax.null_bv _149_401))
in (let _149_402 = (FStar_Syntax_Syntax.as_implicit false)
in (_149_403, _149_402)))
in (_149_404)::[])
in (let _149_405 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype)
in (_149_406, _149_405)))
in FStar_Syntax_Syntax.Tm_arrow (_149_407))
in (mk _149_408)))
and star_type : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun t -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None t.FStar_Syntax_Syntax.pos))
in (

let mk_star_to_type = (mk_star_to_type mk)
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _57_336) -> begin
(

let binders = (FStar_List.map (fun _57_341 -> (match (_57_341) with
| (bv, aqual) -> begin
(let _149_415 = (

let _57_342 = bv
in (let _149_414 = (star_type bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_342.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_342.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_414}))
in (_149_415, aqual))
end)) binders)
in (match ((is_monadic_arrow t.FStar_Syntax_Syntax.n)) with
| N (hn) -> begin
(let _149_419 = (let _149_418 = (let _149_417 = (let _149_416 = (star_type hn)
in (FStar_Syntax_Syntax.mk_Total _149_416))
in (binders, _149_417))
in FStar_Syntax_Syntax.Tm_arrow (_149_418))
in (mk _149_419))
end
| T (a) -> begin
(let _149_428 = (let _149_427 = (let _149_426 = (let _149_424 = (let _149_423 = (let _149_422 = (let _149_420 = (mk_star_to_type a)
in (FStar_Syntax_Syntax.null_bv _149_420))
in (let _149_421 = (FStar_Syntax_Syntax.as_implicit false)
in (_149_422, _149_421)))
in (_149_423)::[])
in (FStar_List.append binders _149_424))
in (let _149_425 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype)
in (_149_426, _149_425)))
in FStar_Syntax_Syntax.Tm_arrow (_149_427))
in (mk _149_428))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let rec is_valid_application = (fun head -> (match ((let _149_431 = (FStar_Syntax_Subst.compress head)
in _149_431.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.option_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.either_lid)) || (let _149_432 = (FStar_Syntax_Subst.compress head)
in (FStar_Syntax_Util.is_tuple_constructor _149_432))) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uinst (head, _57_359) -> begin
(is_valid_application head)
end
| _57_363 -> begin
false
end))
in if (is_valid_application head) then begin
(let _149_437 = (let _149_436 = (let _149_435 = (FStar_List.map (fun _57_366 -> (match (_57_366) with
| (t, qual) -> begin
(let _149_434 = (star_type t)
in (_149_434, qual))
end)) args)
in (head, _149_435))
in FStar_Syntax_Syntax.Tm_app (_149_436))
in (mk _149_437))
end else begin
(let _149_440 = (let _149_439 = (let _149_438 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "For now, only [either] and [option] are supported in the definition language (got: %s)" _149_438))
in FStar_Syntax_Syntax.Err (_149_439))
in (Prims.raise _149_440))
end)
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_match (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _149_443 = (let _149_442 = (let _149_441 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "The following term is outside of the definition language: %s" _149_441))
in FStar_Syntax_Syntax.Err (_149_442))
in (Prims.raise _149_443))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_408) -> begin
(FStar_All.failwith "impossible")
end)))))


type mode =
| InMonad of FStar_Syntax_Syntax.typ
| InPure


let is_InMonad = (fun _discr_ -> (match (_discr_) with
| InMonad (_) -> begin
true
end
| _ -> begin
false
end))


let is_InPure = (fun _discr_ -> (match (_discr_) with
| InPure (_) -> begin
true
end
| _ -> begin
false
end))


let ___InMonad____0 = (fun projectee -> (match (projectee) with
| InMonad (_57_412) -> begin
_57_412
end))


let wrap_if : mode  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun m e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let mk_star_to_type = (mk_star_to_type mk)
in (match (m) with
| InPure -> begin
e
end
| InMonad (t) -> begin
(

let p_type = (mk_star_to_type t)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p" None p_type)
in (

let body = (let _149_474 = (let _149_473 = (let _149_472 = (mk (FStar_Syntax_Syntax.Tm_bvar (p)))
in (let _149_471 = (let _149_470 = (let _149_469 = (FStar_Syntax_Syntax.as_implicit false)
in (e, _149_469))
in (_149_470)::[])
in (_149_472, _149_471)))
in FStar_Syntax_Syntax.Tm_app (_149_473))
in (mk _149_474))
in (let _149_476 = (let _149_475 = (FStar_Syntax_Syntax.mk_binder p)
in (_149_475)::[])
in (FStar_Syntax_Util.abs _149_476 body None)))))
end))))


let rec star_expr : FStar_Syntax_Syntax.term  ->  mode  ->  FStar_Syntax_Syntax.term = (fun e m -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let mk_star_to_type = (mk_star_to_type mk)
in (match ((let _149_484 = (FStar_Syntax_Subst.compress e)
in _149_484.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((false, (binding)::[]), e2) -> begin
(

let is_monadic = (FStar_Ident.lid_equals binding.FStar_Syntax_Syntax.lbeff FStar_Syntax_Const.monadic_lid)
in (

let e1 = binding.FStar_Syntax_Syntax.lbdef
in (

let x = (FStar_Util.left binding.FStar_Syntax_Syntax.lbname)
in (

let x_binders = (let _149_485 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_485)::[])
in (

let _57_442 = (FStar_Syntax_Subst.open_term x_binders e2)
in (match (_57_442) with
| (x_binders, e2) -> begin
if is_monadic then begin
(match (m) with
| InPure -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("monadic [let] in a context that does not return [M]")))
end
| InMonad (t) -> begin
(

let p_type = (mk_star_to_type t)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p" None p_type)
in (

let e1 = (star_expr e1 InPure)
in (

let e2 = (star_expr e2 m)
in (

let e2 = (let _149_491 = (let _149_490 = (let _149_489 = (let _149_488 = (let _149_487 = (mk (FStar_Syntax_Syntax.Tm_bvar (p)))
in (let _149_486 = (FStar_Syntax_Syntax.as_implicit false)
in (_149_487, _149_486)))
in (_149_488)::[])
in (e2, _149_489))
in FStar_Syntax_Syntax.Tm_app (_149_490))
in (mk _149_491))
in (

let e2 = (FStar_Syntax_Util.abs x_binders e2 None)
in (

let body = (let _149_496 = (let _149_495 = (let _149_494 = (let _149_493 = (let _149_492 = (FStar_Syntax_Syntax.as_implicit false)
in (e2, _149_492))
in (_149_493)::[])
in (e1, _149_494))
in FStar_Syntax_Syntax.Tm_app (_149_495))
in (mk _149_496))
in (let _149_498 = (let _149_497 = (FStar_Syntax_Syntax.mk_binder p)
in (_149_497)::[])
in (FStar_Syntax_Util.abs _149_498 body None)))))))))
end)
end else begin
(

let e1 = (star_expr e1 InPure)
in (

let e2 = (star_expr e2 InPure)
in (let _149_501 = (let _149_500 = (let _149_499 = (FStar_Syntax_Subst.close x_binders e2)
in ((false, ((

let _57_455 = binding
in {FStar_Syntax_Syntax.lbname = _57_455.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_455.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_455.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_455.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e1}))::[]), _149_499))
in FStar_Syntax_Syntax.Tm_let (_149_500))
in (mk _149_501))))
end
end))))))
end
| FStar_Syntax_Syntax.Tm_let (_57_458) -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("[let rec] and [let and] not supported in the definition\n        language")))
end
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let binders = (FStar_Syntax_Subst.open_binders binders)
in (

let subst = (FStar_Syntax_Subst.opening_of_binders binders)
in (

let body = (FStar_Syntax_Subst.subst subst body)
in (

let ret_type = (match (what) with
| Some (FStar_Util.Inl ({FStar_Syntax_Syntax.eff_name = _57_474; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _57_471; FStar_Syntax_Syntax.comp = _57_469})) -> begin
t
end
| _57_479 -> begin
(FStar_All.failwith "what impossible")
end)
in (

let binders = (FStar_List.map (fun _57_483 -> (match (_57_483) with
| (bv, qual) -> begin
(

let sort = (star_type bv.FStar_Syntax_Syntax.sort)
in ((

let _57_485 = bv
in {FStar_Syntax_Syntax.ppname = _57_485.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_485.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort}), qual))
end)) binders)
in (

let body = (let _149_504 = if (is_monadic what) then begin
InMonad (ret_type)
end else begin
InPure
end
in (star_expr body _149_504))
in (

let body = (FStar_Syntax_Subst.close binders body)
in (

let binders = (FStar_Syntax_Subst.close_binders binders)
in (let _149_505 = (mk (FStar_Syntax_Syntax.Tm_abs ((binders, body, what))))
in (wrap_if m _149_505))))))))))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, _57_493, _57_495) -> begin
(star_expr e m)
end
| FStar_Syntax_Syntax.Tm_match (e0, branches) -> begin
(

let e0 = (star_expr e0 InPure)
in (

let branches = (FStar_List.map (fun b -> (match ((FStar_Syntax_Subst.open_branch b)) with
| (pat, None, body) -> begin
(

let body = (star_expr body m)
in (FStar_Syntax_Subst.close_branch (pat, None, body)))
end
| _57_510 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("No when clauses in the definition language")))
end)) branches)
in (mk (FStar_Syntax_Syntax.Tm_match ((e0, branches))))))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (star_expr head InPure)
in (

let args = (FStar_List.map (fun _57_519 -> (match (_57_519) with
| (arg, qual) -> begin
(let _149_508 = (star_expr arg InPure)
in (_149_508, qual))
end)) args)
in (

let t = (mk (FStar_Syntax_Syntax.Tm_app ((head, args))))
in (wrap_if m t))))
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(wrap_if m e)
end
| FStar_Syntax_Syntax.Tm_uinst (_57_532) -> begin
(FStar_All.failwith "TODO: Tm_uinst")
end
| FStar_Syntax_Syntax.Tm_constant (_57_535) -> begin
(FStar_All.failwith "TODO: Tm_constant")
end
| FStar_Syntax_Syntax.Tm_type (_57_538) -> begin
(FStar_All.failwith "TODO: Tm_type")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_541) -> begin
(FStar_All.failwith "TODO: Tm_arrow")
end
| FStar_Syntax_Syntax.Tm_refine (_57_544) -> begin
(FStar_All.failwith "TODO: Tm_refine")
end
| FStar_Syntax_Syntax.Tm_uvar (_57_547) -> begin
(FStar_All.failwith "TODO: Tm_uvar")
end
| FStar_Syntax_Syntax.Tm_meta (_57_550) -> begin
(FStar_All.failwith "TODO: Tm_meta")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(FStar_All.failwith "TODO: Tm_unknown")
end
| FStar_Syntax_Syntax.Tm_delayed (_57_554) -> begin
(FStar_All.failwith "Impossible")
end))))


let star_expression : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun e t -> (match ((let _149_516 = (FStar_Syntax_Subst.compress e)
in _149_516.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_57_559, _57_561, what) -> begin
if (is_monadic what) then begin
(star_expr e InPure)
end else begin
(let _149_520 = (let _149_519 = (let _149_518 = (FStar_Syntax_Print.term_to_string e)
in (let _149_517 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "The following effect combinator should return in [M]: %s; instead, it has type: %s\n" _149_518 _149_517)))
in FStar_Syntax_Syntax.Err (_149_519))
in (Prims.raise _149_520))
end
end
| _57_566 -> begin
(FStar_All.failwith "Not an arrow?!")
end))




