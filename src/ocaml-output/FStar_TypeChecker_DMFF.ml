
open Prims

let gen_wps_for_free : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.sigelts * FStar_Syntax_Syntax.eff_decl) = (fun env binders a wp_a ed -> (

let wp_a = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env wp_a)
in (

let a = (

let _57_13 = a
in (let _152_11 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env a.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_13.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_13.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _152_11}))
in (

let d = (fun s -> (FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s))
in (

let _57_20 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _57_18 = (d "Elaborating extra WP combinators")
in (let _152_14 = (FStar_Syntax_Print.term_to_string wp_a)
in (FStar_Util.print1 "wp_a is: %s\n" _152_14)))
end else begin
()
end
in (

let rec collect_binders = (fun t -> (match ((let _152_18 = (let _152_17 = (FStar_Syntax_Subst.compress t)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe _152_17))
in _152_18.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let rest = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _57_30) -> begin
t
end
| _57_34 -> begin
(FStar_All.failwith "wp_a contains non-Tot arrow")
end)
in (let _152_19 = (collect_binders rest)
in (FStar_List.append bs _152_19)))
end
| FStar_Syntax_Syntax.Tm_type (_57_37) -> begin
[]
end
| _57_40 -> begin
(FStar_All.failwith "wp_a doesn\'t end in Type0")
end))
in (

let mk_lid = (fun name -> (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" name))) FStar_Range.dummyRange))
in (

let gamma = (let _152_22 = (collect_binders wp_a)
in (FStar_All.pipe_right _152_22 FStar_Syntax_Util.name_binders))
in (

let _57_44 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _152_24 = (let _152_23 = (FStar_Syntax_Print.binders_to_string ", " gamma)
in (FStar_Util.format1 "Gamma is %s\n" _152_23))
in (d _152_24))
end else begin
()
end
in (

let unknown = FStar_Syntax_Syntax.tun
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None FStar_Range.dummyRange))
in (

let sigelts = (FStar_ST.alloc [])
in (

let register = (fun env lident def -> (

let _57_56 = (FStar_TypeChecker_Util.mk_toplevel_definition env lident def)
in (match (_57_56) with
| (sigelt, fv) -> begin
(

let _57_57 = (let _152_34 = (let _152_33 = (FStar_ST.read sigelts)
in (sigelt)::_152_33)
in (FStar_ST.op_Colon_Equals sigelts _152_34))
in fv)
end)))
in (

let binders_of_list = (FStar_List.map (fun _57_61 -> (match (_57_61) with
| (t, b) -> begin
(let _152_37 = (FStar_Syntax_Syntax.as_implicit b)
in ((t), (_152_37)))
end)))
in (

let mk_all_implicit = (FStar_List.map (fun t -> (let _152_40 = (FStar_Syntax_Syntax.as_implicit true)
in (((Prims.fst t)), (_152_40)))))
in (

let args_of_binders = (FStar_List.map (fun bv -> (let _152_43 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst bv))
in (FStar_Syntax_Syntax.as_arg _152_43))))
in (

let _57_88 = (

let _57_73 = (

let mk = (fun f -> (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let body = (let _152_56 = (let _152_55 = (FStar_Syntax_Syntax.bv_to_name t)
in (f _152_55))
in (FStar_Syntax_Util.arrow gamma _152_56))
in (let _152_61 = (let _152_60 = (let _152_59 = (FStar_Syntax_Syntax.mk_binder a)
in (let _152_58 = (let _152_57 = (FStar_Syntax_Syntax.mk_binder t)
in (_152_57)::[])
in (_152_59)::_152_58))
in (FStar_List.append binders _152_60))
in (FStar_Syntax_Util.abs _152_61 body None)))))
in (let _152_63 = (mk FStar_Syntax_Syntax.mk_Total)
in (let _152_62 = (mk FStar_Syntax_Syntax.mk_GTotal)
in ((_152_63), (_152_62)))))
in (match (_57_73) with
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

let mk_app = (fun fv t -> (let _152_85 = (let _152_84 = (let _152_83 = (let _152_82 = (FStar_List.map (fun _57_84 -> (match (_57_84) with
| (bv, _57_83) -> begin
(let _152_74 = (FStar_Syntax_Syntax.bv_to_name bv)
in (let _152_73 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_74), (_152_73))))
end)) binders)
in (let _152_81 = (let _152_80 = (let _152_76 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _152_75 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_76), (_152_75))))
in (let _152_79 = (let _152_78 = (let _152_77 = (FStar_Syntax_Syntax.as_implicit false)
in ((t), (_152_77)))
in (_152_78)::[])
in (_152_80)::_152_79))
in (FStar_List.append _152_82 _152_81)))
in ((fv), (_152_83)))
in FStar_Syntax_Syntax.Tm_app (_152_84))
in (mk _152_85)))
in ((env), ((mk_app ctx_fv)), ((mk_app gctx_fv))))))))
end))
in (match (_57_88) with
| (env, mk_ctx, mk_gctx) -> begin
(

let c_pure = (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let x = (let _152_90 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" None _152_90))
in (

let ret = (let _152_95 = (let _152_94 = (let _152_93 = (let _152_92 = (let _152_91 = (FStar_Syntax_Syntax.bv_to_name t)
in (mk_ctx _152_91))
in (FStar_Syntax_Syntax.mk_Total _152_92))
in (FStar_Syntax_Util.lcomp_of_comp _152_93))
in FStar_Util.Inl (_152_94))
in Some (_152_95))
in (

let body = (let _152_96 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs gamma _152_96 ret))
in (let _152_99 = (let _152_98 = (mk_all_implicit binders)
in (let _152_97 = (binders_of_list ((((a), (true)))::(((t), (true)))::(((x), (false)))::[]))
in (FStar_List.append _152_98 _152_97)))
in (FStar_Syntax_Util.abs _152_99 body ret))))))
in (

let c_pure = (let _152_100 = (mk_lid "pure")
in (register env _152_100 c_pure))
in (

let c_app = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let l = (let _152_108 = (let _152_107 = (let _152_106 = (let _152_103 = (let _152_102 = (let _152_101 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv None _152_101))
in (FStar_Syntax_Syntax.mk_binder _152_102))
in (_152_103)::[])
in (let _152_105 = (let _152_104 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _152_104))
in (FStar_Syntax_Util.arrow _152_106 _152_105)))
in (mk_gctx _152_107))
in (FStar_Syntax_Syntax.gen_bv "l" None _152_108))
in (

let r = (let _152_110 = (let _152_109 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _152_109))
in (FStar_Syntax_Syntax.gen_bv "r" None _152_110))
in (

let ret = (let _152_115 = (let _152_114 = (let _152_113 = (let _152_112 = (let _152_111 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _152_111))
in (FStar_Syntax_Syntax.mk_Total _152_112))
in (FStar_Syntax_Util.lcomp_of_comp _152_113))
in FStar_Util.Inl (_152_114))
in Some (_152_115))
in (

let outer_body = (

let gamma_as_args = (args_of_binders gamma)
in (

let inner_body = (let _152_121 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _152_120 = (let _152_119 = (let _152_118 = (let _152_117 = (let _152_116 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app _152_116 gamma_as_args))
in (FStar_Syntax_Syntax.as_arg _152_117))
in (_152_118)::[])
in (FStar_List.append gamma_as_args _152_119))
in (FStar_Syntax_Util.mk_app _152_121 _152_120)))
in (FStar_Syntax_Util.abs gamma inner_body ret)))
in (let _152_124 = (let _152_123 = (mk_all_implicit binders)
in (let _152_122 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((l), (false)))::(((r), (false)))::[]))
in (FStar_List.append _152_123 _152_122)))
in (FStar_Syntax_Util.abs _152_124 outer_body ret))))))))
in (

let c_app = (let _152_125 = (mk_lid "app")
in (register env _152_125 c_app))
in (

let c_lift1 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _152_130 = (let _152_127 = (let _152_126 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _152_126))
in (_152_127)::[])
in (let _152_129 = (let _152_128 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _152_128))
in (FStar_Syntax_Util.arrow _152_130 _152_129)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _152_132 = (let _152_131 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _152_131))
in (FStar_Syntax_Syntax.gen_bv "a1" None _152_132))
in (

let ret = (let _152_137 = (let _152_136 = (let _152_135 = (let _152_134 = (let _152_133 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _152_133))
in (FStar_Syntax_Syntax.mk_Total _152_134))
in (FStar_Syntax_Util.lcomp_of_comp _152_135))
in FStar_Util.Inl (_152_136))
in Some (_152_137))
in (let _152_149 = (let _152_139 = (mk_all_implicit binders)
in (let _152_138 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::(((a1), (false)))::[]))
in (FStar_List.append _152_139 _152_138)))
in (let _152_148 = (let _152_147 = (let _152_146 = (let _152_145 = (let _152_142 = (let _152_141 = (let _152_140 = (FStar_Syntax_Syntax.bv_to_name f)
in (_152_140)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_141))
in (FStar_Syntax_Util.mk_app c_pure _152_142))
in (let _152_144 = (let _152_143 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_152_143)::[])
in (_152_145)::_152_144))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_146))
in (FStar_Syntax_Util.mk_app c_app _152_147))
in (FStar_Syntax_Util.abs _152_149 _152_148 ret)))))))))
in (

let c_lift1 = (let _152_150 = (mk_lid "lift1")
in (register env _152_150 c_lift1))
in (

let c_lift2 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t3 = (FStar_Syntax_Syntax.gen_bv "t3" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _152_158 = (let _152_155 = (let _152_151 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _152_151))
in (let _152_154 = (let _152_153 = (let _152_152 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.null_binder _152_152))
in (_152_153)::[])
in (_152_155)::_152_154))
in (let _152_157 = (let _152_156 = (FStar_Syntax_Syntax.bv_to_name t3)
in (FStar_Syntax_Syntax.mk_GTotal _152_156))
in (FStar_Syntax_Util.arrow _152_158 _152_157)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _152_160 = (let _152_159 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _152_159))
in (FStar_Syntax_Syntax.gen_bv "a1" None _152_160))
in (

let a2 = (let _152_162 = (let _152_161 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _152_161))
in (FStar_Syntax_Syntax.gen_bv "a2" None _152_162))
in (

let ret = (let _152_167 = (let _152_166 = (let _152_165 = (let _152_164 = (let _152_163 = (FStar_Syntax_Syntax.bv_to_name t3)
in (mk_gctx _152_163))
in (FStar_Syntax_Syntax.mk_Total _152_164))
in (FStar_Syntax_Util.lcomp_of_comp _152_165))
in FStar_Util.Inl (_152_166))
in Some (_152_167))
in (let _152_184 = (let _152_169 = (mk_all_implicit binders)
in (let _152_168 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((t3), (true)))::(((f), (false)))::(((a1), (false)))::(((a2), (false)))::[]))
in (FStar_List.append _152_169 _152_168)))
in (let _152_183 = (let _152_182 = (let _152_181 = (let _152_180 = (let _152_177 = (let _152_176 = (let _152_175 = (let _152_172 = (let _152_171 = (let _152_170 = (FStar_Syntax_Syntax.bv_to_name f)
in (_152_170)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_171))
in (FStar_Syntax_Util.mk_app c_pure _152_172))
in (let _152_174 = (let _152_173 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_152_173)::[])
in (_152_175)::_152_174))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_176))
in (FStar_Syntax_Util.mk_app c_app _152_177))
in (let _152_179 = (let _152_178 = (FStar_Syntax_Syntax.bv_to_name a2)
in (_152_178)::[])
in (_152_180)::_152_179))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_181))
in (FStar_Syntax_Util.mk_app c_app _152_182))
in (FStar_Syntax_Util.abs _152_184 _152_183 ret)))))))))))
in (

let c_lift2 = (let _152_185 = (mk_lid "lift2")
in (register env _152_185 c_lift2))
in (

let c_push = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _152_191 = (let _152_187 = (let _152_186 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _152_186))
in (_152_187)::[])
in (let _152_190 = (let _152_189 = (let _152_188 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _152_188))
in (FStar_Syntax_Syntax.mk_Total _152_189))
in (FStar_Syntax_Util.arrow _152_191 _152_190)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let ret = (let _152_201 = (let _152_200 = (let _152_199 = (let _152_198 = (let _152_197 = (let _152_196 = (let _152_193 = (let _152_192 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _152_192))
in (_152_193)::[])
in (let _152_195 = (let _152_194 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _152_194))
in (FStar_Syntax_Util.arrow _152_196 _152_195)))
in (mk_ctx _152_197))
in (FStar_Syntax_Syntax.mk_Total _152_198))
in (FStar_Syntax_Util.lcomp_of_comp _152_199))
in FStar_Util.Inl (_152_200))
in Some (_152_201))
in (

let e1 = (let _152_202 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" None _152_202))
in (

let body = (let _152_211 = (let _152_204 = (let _152_203 = (FStar_Syntax_Syntax.mk_binder e1)
in (_152_203)::[])
in (FStar_List.append gamma _152_204))
in (let _152_210 = (let _152_209 = (FStar_Syntax_Syntax.bv_to_name f)
in (let _152_208 = (let _152_207 = (let _152_205 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg _152_205))
in (let _152_206 = (args_of_binders gamma)
in (_152_207)::_152_206))
in (FStar_Syntax_Util.mk_app _152_209 _152_208)))
in (FStar_Syntax_Util.abs _152_211 _152_210 ret)))
in (let _152_214 = (let _152_213 = (mk_all_implicit binders)
in (let _152_212 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::[]))
in (FStar_List.append _152_213 _152_212)))
in (FStar_Syntax_Util.abs _152_214 body ret)))))))))
in (

let c_push = (let _152_215 = (mk_lid "push")
in (register env _152_215 c_push))
in (

let ret_tot_wp_a = (let _152_218 = (let _152_217 = (let _152_216 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.lcomp_of_comp _152_216))
in FStar_Util.Inl (_152_217))
in Some (_152_218))
in (

let mk_generic_app = (fun c -> if ((FStar_List.length binders) > (Prims.parse_int "0")) then begin
(let _152_223 = (let _152_222 = (let _152_221 = (args_of_binders binders)
in ((c), (_152_221)))
in FStar_Syntax_Syntax.Tm_app (_152_222))
in (mk _152_223))
end else begin
c
end)
in (

let wp_if_then_else = (

let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (let _152_241 = (let _152_224 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (FStar_List.append binders _152_224))
in (let _152_240 = (

let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "2"))) None)
in (let _152_239 = (let _152_230 = (let _152_229 = (let _152_228 = (let _152_227 = (let _152_226 = (let _152_225 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg _152_225))
in (_152_226)::[])
in (FStar_Syntax_Util.mk_app l_ite _152_227))
in (_152_228)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_229))
in (FStar_Syntax_Util.mk_app c_lift2 _152_230))
in (let _152_238 = (let _152_237 = (let _152_236 = (let _152_235 = (let _152_233 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _152_232 = (let _152_231 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_152_231)::[])
in (_152_233)::_152_232))
in (let _152_234 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _152_235 _152_234)))
in (FStar_Syntax_Syntax.mk_Total _152_236))
in FStar_Util.Inr (_152_237))
in (FStar_Syntax_Util.ascribe _152_239 _152_238))))
in (FStar_Syntax_Util.abs _152_241 _152_240 ret_tot_wp_a))))
in (

let wp_if_then_else = (let _152_242 = (mk_lid "wp_if_then_else")
in (register env _152_242 wp_if_then_else))
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

let body = (let _152_253 = (let _152_252 = (let _152_251 = (let _152_248 = (let _152_247 = (let _152_246 = (let _152_245 = (let _152_244 = (let _152_243 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _152_243))
in (_152_244)::[])
in (FStar_Syntax_Util.mk_app l_and _152_245))
in (_152_246)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_247))
in (FStar_Syntax_Util.mk_app c_pure _152_248))
in (let _152_250 = (let _152_249 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_152_249)::[])
in (_152_251)::_152_250))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_252))
in (FStar_Syntax_Util.mk_app c_app _152_253))
in (let _152_255 = (let _152_254 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders _152_254))
in (FStar_Syntax_Util.abs _152_255 body ret_tot_wp_a))))))
in (

let wp_assert = (let _152_256 = (mk_lid "wp_assert")
in (register env _152_256 wp_assert))
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

let body = (let _152_267 = (let _152_266 = (let _152_265 = (let _152_262 = (let _152_261 = (let _152_260 = (let _152_259 = (let _152_258 = (let _152_257 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _152_257))
in (_152_258)::[])
in (FStar_Syntax_Util.mk_app l_imp _152_259))
in (_152_260)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_261))
in (FStar_Syntax_Util.mk_app c_pure _152_262))
in (let _152_264 = (let _152_263 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_152_263)::[])
in (_152_265)::_152_264))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_266))
in (FStar_Syntax_Util.mk_app c_app _152_267))
in (let _152_269 = (let _152_268 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders _152_268))
in (FStar_Syntax_Util.abs _152_269 body ret_tot_wp_a))))))
in (

let wp_assume = (let _152_270 = (mk_lid "wp_assume")
in (register env _152_270 wp_assume))
in (

let wp_assume = (mk_generic_app wp_assume)
in (

let wp_close = (

let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _152_274 = (let _152_272 = (let _152_271 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _152_271))
in (_152_272)::[])
in (let _152_273 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _152_274 _152_273)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let body = (let _152_283 = (let _152_282 = (let _152_281 = (let _152_275 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((FStar_Syntax_Util.tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure _152_275))
in (let _152_280 = (let _152_279 = (let _152_278 = (let _152_277 = (let _152_276 = (FStar_Syntax_Syntax.bv_to_name f)
in (_152_276)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_277))
in (FStar_Syntax_Util.mk_app c_push _152_278))
in (_152_279)::[])
in (_152_281)::_152_280))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_282))
in (FStar_Syntax_Util.mk_app c_app _152_283))
in (let _152_285 = (let _152_284 = (FStar_Syntax_Syntax.binders_of_list ((a)::(b)::(f)::[]))
in (FStar_List.append binders _152_284))
in (FStar_Syntax_Util.abs _152_285 body ret_tot_wp_a))))))
in (

let wp_close = (let _152_286 = (mk_lid "wp_close")
in (register env _152_286 wp_close))
in (

let wp_close = (mk_generic_app wp_close)
in (

let ret_tot_type = (let _152_289 = (let _152_288 = (let _152_287 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_287))
in FStar_Util.Inl (_152_288))
in Some (_152_289))
in (

let ret_gtot_type = (let _152_292 = (let _152_291 = (let _152_290 = (FStar_Syntax_Syntax.mk_GTotal FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_290))
in FStar_Util.Inl (_152_291))
in Some (_152_292))
in (

let mk_forall = (fun x body -> (let _152_303 = (let _152_302 = (let _152_301 = (let _152_300 = (let _152_299 = (let _152_298 = (let _152_297 = (FStar_Syntax_Syntax.mk_binder x)
in (_152_297)::[])
in (FStar_Syntax_Util.abs _152_298 body ret_tot_type))
in (FStar_Syntax_Syntax.as_arg _152_299))
in (_152_300)::[])
in ((FStar_Syntax_Util.tforall), (_152_301)))
in FStar_Syntax_Syntax.Tm_app (_152_302))
in (FStar_Syntax_Syntax.mk _152_303 None FStar_Range.dummyRange)))
in (

let rec is_discrete = (fun t -> (match ((let _152_306 = (FStar_Syntax_Subst.compress t)
in _152_306.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_169) -> begin
false
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((FStar_List.for_all (fun _57_178 -> (match (_57_178) with
| (b, _57_177) -> begin
(is_discrete b.FStar_Syntax_Syntax.sort)
end)) bs) && (is_discrete (FStar_Syntax_Util.comp_result c)))
end
| _57_180 -> begin
true
end))
in (

let rec is_monotonic = (fun t -> (match ((let _152_310 = (FStar_Syntax_Subst.compress t)
in _152_310.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_184) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((FStar_List.for_all (fun _57_193 -> (match (_57_193) with
| (b, _57_192) -> begin
(is_discrete b.FStar_Syntax_Syntax.sort)
end)) bs) && (is_monotonic (FStar_Syntax_Util.comp_result c)))
end
| _57_195 -> begin
(is_discrete t)
end))
in (

let rec mk_rel = (fun rel t x y -> (

let mk_rel = (mk_rel rel)
in (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (match ((let _152_333 = (FStar_Syntax_Subst.compress t)
in _152_333.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_204) -> begin
(rel x y)
end
| (FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(

let a = (Prims.fst binder).FStar_Syntax_Syntax.sort
in if ((is_monotonic a) || (is_monotonic b)) then begin
(

let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (

let body = (let _152_341 = (let _152_336 = (let _152_335 = (let _152_334 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _152_334))
in (_152_335)::[])
in (FStar_Syntax_Util.mk_app x _152_336))
in (let _152_340 = (let _152_339 = (let _152_338 = (let _152_337 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _152_337))
in (_152_338)::[])
in (FStar_Syntax_Util.mk_app y _152_339))
in (mk_rel b _152_341 _152_340)))
in (mk_forall a1 body)))
end else begin
(

let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (

let a2 = (FStar_Syntax_Syntax.gen_bv "a2" None a)
in (

let body = (let _152_353 = (let _152_343 = (FStar_Syntax_Syntax.bv_to_name a1)
in (let _152_342 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_rel a _152_343 _152_342)))
in (let _152_352 = (let _152_351 = (let _152_346 = (let _152_345 = (let _152_344 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _152_344))
in (_152_345)::[])
in (FStar_Syntax_Util.mk_app x _152_346))
in (let _152_350 = (let _152_349 = (let _152_348 = (let _152_347 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg _152_347))
in (_152_348)::[])
in (FStar_Syntax_Util.mk_app y _152_349))
in (mk_rel b _152_351 _152_350)))
in (FStar_Syntax_Util.mk_imp _152_353 _152_352)))
in (let _152_354 = (mk_forall a2 body)
in (mk_forall a1 _152_354)))))
end)
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::binders, comp) -> begin
(

let t = (

let _57_248 = t
in (let _152_358 = (let _152_357 = (let _152_356 = (let _152_355 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _152_355))
in (((binder)::[]), (_152_356)))
in FStar_Syntax_Syntax.Tm_arrow (_152_357))
in {FStar_Syntax_Syntax.n = _152_358; FStar_Syntax_Syntax.tk = _57_248.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_248.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_248.FStar_Syntax_Syntax.vars}))
in (mk_rel t x y))
end
| FStar_Syntax_Syntax.Tm_arrow (_57_252) -> begin
(FStar_All.failwith "unhandled arrow")
end
| _57_255 -> begin
(FStar_Syntax_Util.mk_eq t t x y)
end))))
in (

let stronger = (

let wp1 = (FStar_Syntax_Syntax.gen_bv "wp1" None wp_a)
in (

let wp2 = (FStar_Syntax_Syntax.gen_bv "wp2" None wp_a)
in (

let body = (let _152_360 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (let _152_359 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_rel FStar_Syntax_Util.mk_imp wp_a _152_360 _152_359)))
in (let _152_362 = (let _152_361 = (binders_of_list ((((a), (false)))::(((wp1), (false)))::(((wp2), (false)))::[]))
in (FStar_List.append binders _152_361))
in (FStar_Syntax_Util.abs _152_362 body ret_tot_type)))))
in (

let stronger = (let _152_363 = (mk_lid "stronger")
in (register env _152_363 stronger))
in (

let stronger = (mk_generic_app stronger)
in (

let wp_ite = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let _57_265 = (FStar_Util.prefix gamma)
in (match (_57_265) with
| (wp_args, post) -> begin
(

let k = (FStar_Syntax_Syntax.gen_bv "k" None (Prims.fst post).FStar_Syntax_Syntax.sort)
in (

let equiv = (

let k_tm = (FStar_Syntax_Syntax.bv_to_name k)
in (

let eq = (let _152_364 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst post))
in (mk_rel FStar_Syntax_Util.mk_iff k.FStar_Syntax_Syntax.sort k_tm _152_364))
in (match ((FStar_Syntax_Util.destruct_typ_as_formula eq)) with
| Some (FStar_Syntax_Util.QAll (binders, [], body)) -> begin
(

let k_app = (let _152_365 = (args_of_binders binders)
in (FStar_Syntax_Util.mk_app k_tm _152_365))
in (

let guard_free = (let _152_366 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.guard_free FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _152_366))
in (

let pat = (let _152_368 = (let _152_367 = (FStar_Syntax_Syntax.as_arg k_app)
in (_152_367)::[])
in (FStar_Syntax_Util.mk_app guard_free _152_368))
in (

let pattern_guarded_body = (let _152_374 = (let _152_373 = (let _152_372 = (let _152_371 = (let _152_370 = (let _152_369 = (FStar_Syntax_Syntax.as_arg pat)
in (_152_369)::[])
in (_152_370)::[])
in FStar_Syntax_Syntax.Meta_pattern (_152_371))
in ((body), (_152_372)))
in FStar_Syntax_Syntax.Tm_meta (_152_373))
in (mk _152_374))
in (FStar_Syntax_Util.close_forall binders pattern_guarded_body)))))
end
| _57_280 -> begin
(FStar_All.failwith "Impossible: Expected the equivalence to be a quantified formula")
end)))
in (

let body = (let _152_383 = (let _152_382 = (let _152_381 = (let _152_380 = (FStar_Syntax_Syntax.bv_to_name wp)
in (let _152_379 = (let _152_378 = (args_of_binders wp_args)
in (let _152_377 = (let _152_376 = (let _152_375 = (FStar_Syntax_Syntax.bv_to_name k)
in (FStar_Syntax_Syntax.as_arg _152_375))
in (_152_376)::[])
in (FStar_List.append _152_378 _152_377)))
in (FStar_Syntax_Util.mk_app _152_380 _152_379)))
in (FStar_Syntax_Util.mk_imp equiv _152_381))
in (FStar_Syntax_Util.mk_forall k _152_382))
in (FStar_Syntax_Util.abs gamma _152_383 ret_gtot_type))
in (let _152_385 = (let _152_384 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders _152_384))
in (FStar_Syntax_Util.abs _152_385 body ret_gtot_type)))))
end)))
in (

let wp_ite = (let _152_386 = (mk_lid "wp_ite")
in (register env _152_386 wp_ite))
in (

let wp_ite = (mk_generic_app wp_ite)
in (

let null_wp = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let _57_289 = (FStar_Util.prefix gamma)
in (match (_57_289) with
| (wp_args, post) -> begin
(

let x = (FStar_Syntax_Syntax.gen_bv "x" None FStar_Syntax_Syntax.tun)
in (

let body = (let _152_391 = (let _152_390 = (FStar_All.pipe_left FStar_Syntax_Syntax.bv_to_name (Prims.fst post))
in (let _152_389 = (let _152_388 = (let _152_387 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _152_387))
in (_152_388)::[])
in (FStar_Syntax_Util.mk_app _152_390 _152_389)))
in (FStar_Syntax_Util.mk_forall x _152_391))
in (let _152_394 = (let _152_393 = (let _152_392 = (FStar_Syntax_Syntax.binders_of_list ((a)::[]))
in (FStar_List.append _152_392 gamma))
in (FStar_List.append binders _152_393))
in (FStar_Syntax_Util.abs _152_394 body ret_gtot_type))))
end)))
in (

let null_wp = (let _152_395 = (mk_lid "null_wp")
in (register env _152_395 null_wp))
in (

let null_wp = (mk_generic_app null_wp)
in (

let wp_trivial = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let body = (let _152_405 = (let _152_404 = (let _152_403 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _152_402 = (let _152_401 = (let _152_398 = (let _152_397 = (let _152_396 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg _152_396))
in (_152_397)::[])
in (FStar_Syntax_Util.mk_app null_wp _152_398))
in (let _152_400 = (let _152_399 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_152_399)::[])
in (_152_401)::_152_400))
in (_152_403)::_152_402))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_404))
in (FStar_Syntax_Util.mk_app stronger _152_405))
in (let _152_407 = (let _152_406 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders _152_406))
in (FStar_Syntax_Util.abs _152_407 body ret_tot_type))))
in (

let wp_trivial = (let _152_408 = (mk_lid "wp_trivial")
in (register env _152_408 wp_trivial))
in (

let wp_trivial = (mk_generic_app wp_trivial)
in (

let _57_300 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(d "End Dijkstra monads for free")
end else begin
()
end
in (

let c = (FStar_Syntax_Subst.close binders)
in (let _152_428 = (let _152_410 = (FStar_ST.read sigelts)
in (FStar_List.rev _152_410))
in (let _152_427 = (

let _57_303 = ed
in (let _152_426 = (let _152_411 = (c wp_if_then_else)
in (([]), (_152_411)))
in (let _152_425 = (let _152_412 = (c wp_ite)
in (([]), (_152_412)))
in (let _152_424 = (let _152_413 = (c stronger)
in (([]), (_152_413)))
in (let _152_423 = (let _152_414 = (c wp_close)
in (([]), (_152_414)))
in (let _152_422 = (let _152_415 = (c wp_assert)
in (([]), (_152_415)))
in (let _152_421 = (let _152_416 = (c wp_assume)
in (([]), (_152_416)))
in (let _152_420 = (let _152_417 = (c null_wp)
in (([]), (_152_417)))
in (let _152_419 = (let _152_418 = (c wp_trivial)
in (([]), (_152_418)))
in {FStar_Syntax_Syntax.qualifiers = _57_303.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_303.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_303.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_303.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_303.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _57_303.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _57_303.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _152_426; FStar_Syntax_Syntax.ite_wp = _152_425; FStar_Syntax_Syntax.stronger = _152_424; FStar_Syntax_Syntax.close_wp = _152_423; FStar_Syntax_Syntax.assert_p = _152_422; FStar_Syntax_Syntax.assume_p = _152_421; FStar_Syntax_Syntax.null_wp = _152_420; FStar_Syntax_Syntax.trivial = _152_419; FStar_Syntax_Syntax.repr = _57_303.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _57_303.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _57_303.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _57_303.FStar_Syntax_Syntax.actions})))))))))
in ((_152_428), (_152_427))))))))))))))))))))))))))))))))))))))))))))))))
end))))))))))))))))))


type env =
{env : FStar_TypeChecker_Env.env; subst : FStar_Syntax_Syntax.subst_elt Prims.list; tc_const : FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))


let empty : FStar_TypeChecker_Env.env  ->  (FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ)  ->  env = (fun env tc_const -> {env = env; subst = []; tc_const = tc_const})


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
| N (_57_313) -> begin
_57_313
end))


let ___M____0 = (fun projectee -> (match (projectee) with
| M (_57_316) -> begin
_57_316
end))


type nm_ =
nm


let nm_of_comp : FStar_Syntax_Syntax.comp'  ->  nm = (fun _57_1 -> (match (_57_1) with
| FStar_Syntax_Syntax.Total (t, _57_320) -> begin
N (t)
end
| FStar_Syntax_Syntax.Comp (c) when (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.monadic_lid) -> begin
M (c.FStar_Syntax_Syntax.result_typ)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(let _152_485 = (let _152_484 = (FStar_Ident.string_of_lid c.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format1 "[nm_of_comp]: impossible (%s)" _152_484))
in (FStar_All.failwith _152_485))
end
| FStar_Syntax_Syntax.GTotal (_57_328) -> begin
(FStar_All.failwith "[nm_of_comp]: impossible (GTot)")
end))


let string_of_nm : nm  ->  Prims.string = (fun _57_2 -> (match (_57_2) with
| N (t) -> begin
(let _152_488 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "N[%s]" _152_488))
end
| M (t) -> begin
(let _152_489 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "M[%s]" _152_489))
end))


let is_monadic_arrow : FStar_Syntax_Syntax.term'  ->  nm = (fun n -> (match (n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_337, {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_343; FStar_Syntax_Syntax.pos = _57_341; FStar_Syntax_Syntax.vars = _57_339}) -> begin
(nm_of_comp n)
end
| _57_349 -> begin
(FStar_All.failwith "unexpected_argument: [is_monadic_arrow]")
end))


let is_monadic_comp = (fun c -> (match ((nm_of_comp c.FStar_Syntax_Syntax.n)) with
| M (_57_352) -> begin
true
end
| N (_57_355) -> begin
false
end))


exception Not_found


let is_Not_found = (fun _discr_ -> (match (_discr_) with
| Not_found (_) -> begin
true
end
| _ -> begin
false
end))


let double_star : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun typ -> (

let star_once = (fun typ -> (let _152_501 = (let _152_499 = (let _152_498 = (FStar_Syntax_Syntax.new_bv None typ)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _152_498))
in (_152_499)::[])
in (let _152_500 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _152_501 _152_500))))
in (let _152_502 = (FStar_All.pipe_right typ star_once)
in (FStar_All.pipe_left star_once _152_502))))


let rec mk_star_to_type : (FStar_Syntax_Syntax.term'  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun mk env a -> (let _152_523 = (let _152_522 = (let _152_521 = (let _152_519 = (let _152_518 = (let _152_516 = (star_type' env a)
in (FStar_Syntax_Syntax.null_bv _152_516))
in (let _152_517 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_518), (_152_517))))
in (_152_519)::[])
in (let _152_520 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_152_521), (_152_520))))
in FStar_Syntax_Syntax.Tm_arrow (_152_522))
in (mk _152_523)))
and star_type' : env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None t.FStar_Syntax_Syntax.pos))
in (

let mk_star_to_type = (mk_star_to_type mk)
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _57_371) -> begin
(

let binders = (FStar_List.map (fun _57_376 -> (match (_57_376) with
| (bv, aqual) -> begin
(let _152_532 = (

let _57_377 = bv
in (let _152_531 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_377.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_377.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _152_531}))
in ((_152_532), (aqual)))
end)) binders)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_381, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (hn, _57_390); FStar_Syntax_Syntax.tk = _57_387; FStar_Syntax_Syntax.pos = _57_385; FStar_Syntax_Syntax.vars = _57_383}) -> begin
(let _152_536 = (let _152_535 = (let _152_534 = (let _152_533 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_GTotal _152_533))
in ((binders), (_152_534)))
in FStar_Syntax_Syntax.Tm_arrow (_152_535))
in (mk _152_536))
end
| _57_397 -> begin
(match ((is_monadic_arrow t.FStar_Syntax_Syntax.n)) with
| N (hn) -> begin
(let _152_540 = (let _152_539 = (let _152_538 = (let _152_537 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_Total _152_537))
in ((binders), (_152_538)))
in FStar_Syntax_Syntax.Tm_arrow (_152_539))
in (mk _152_540))
end
| M (a) -> begin
(let _152_549 = (let _152_548 = (let _152_547 = (let _152_545 = (let _152_544 = (let _152_543 = (let _152_541 = (mk_star_to_type env a)
in (FStar_Syntax_Syntax.null_bv _152_541))
in (let _152_542 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_543), (_152_542))))
in (_152_544)::[])
in (FStar_List.append binders _152_545))
in (let _152_546 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_152_547), (_152_546))))
in FStar_Syntax_Syntax.Tm_arrow (_152_548))
in (mk _152_549))
end)
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
in (

let _57_418 = (FStar_Util.string_builder_append strb "{")
in (

let _57_420 = (let _152_563 = (f x)
in (FStar_Util.string_builder_append strb _152_563))
in (

let _57_425 = (FStar_List.iter (fun x -> (

let _57_423 = (FStar_Util.string_builder_append strb ", ")
in (let _152_565 = (f x)
in (FStar_Util.string_builder_append strb _152_565)))) xs)
in (

let _57_427 = (FStar_Util.string_builder_append strb "}")
in (FStar_Util.string_of_string_builder strb))))))
end)))
in (let _152_567 = (FStar_Syntax_Print.term_to_string t)
in (let _152_566 = (string_of_set FStar_Syntax_Print.bv_to_string s)
in (FStar_Util.print2_warning "Dependency found in term %s : %s" _152_567 _152_566)))))
in (

let rec is_non_dependent_arrow = (fun ty n -> (match ((let _152_572 = (FStar_Syntax_Subst.compress ty)
in _152_572.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
if (not ((FStar_Syntax_Util.is_tot_or_gtot_comp c))) then begin
false
end else begin
try
(match (()) with
| () -> begin
(

let non_dependent_or_raise = (fun s ty -> (

let sinter = (let _152_578 = (FStar_Syntax_Free.names ty)
in (FStar_Util.set_intersect _152_578 s))
in if (not ((FStar_Util.set_is_empty sinter))) then begin
(

let _57_446 = (debug ty sinter)
in (Prims.raise Not_found))
end else begin
()
end))
in (

let _57_450 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_57_450) with
| (binders, c) -> begin
(

let s = (FStar_List.fold_left (fun s _57_455 -> (match (_57_455) with
| (bv, _57_454) -> begin
(

let _57_456 = (non_dependent_or_raise s bv.FStar_Syntax_Syntax.sort)
in (FStar_Util.set_add bv s))
end)) FStar_Syntax_Syntax.no_names binders)
in (

let ct = (FStar_Syntax_Util.comp_result c)
in (

let _57_460 = (non_dependent_or_raise s ct)
in (

let k = (n - (FStar_List.length binders))
in if (k > (Prims.parse_int "0")) then begin
(is_non_dependent_arrow ct k)
end else begin
true
end))))
end)))
end)
with
| Not_found -> begin
false
end
end
end
| _57_464 -> begin
(

let _57_465 = (let _152_582 = (FStar_Syntax_Print.term_to_string ty)
in (FStar_Util.print1_warning "Not a dependent arrow : %s" _152_582))
in false)
end))
in (

let rec is_valid_application = (fun head -> (match ((let _152_585 = (FStar_Syntax_Subst.compress head)
in _152_585.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.option_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.either_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.eq2_lid)) || (let _152_586 = (FStar_Syntax_Subst.compress head)
in (FStar_Syntax_Util.is_tuple_constructor _152_586))) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (is_non_dependent_arrow fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty (FStar_List.length args)) -> begin
(

let res = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.env t)
in (match (res.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (_57_475) -> begin
true
end
| _57_478 -> begin
(

let _57_479 = (let _152_587 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.print1_warning "Got a term which might be a non-dependent user-defined data-type %s\n" _152_587))
in false)
end))
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uinst (t, _57_489) -> begin
(is_valid_application t)
end
| _57_493 -> begin
false
end))
in if (is_valid_application head) then begin
(let _152_592 = (let _152_591 = (let _152_590 = (FStar_List.map (fun _57_496 -> (match (_57_496) with
| (t, qual) -> begin
(let _152_589 = (star_type' env t)
in ((_152_589), (qual)))
end)) args)
in ((head), (_152_590)))
in FStar_Syntax_Syntax.Tm_app (_152_591))
in (mk _152_592))
end else begin
(let _152_595 = (let _152_594 = (let _152_593 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)" _152_593))
in FStar_Syntax_Syntax.Err (_152_594))
in (Prims.raise _152_595))
end)))
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_abs (binders, repr, something) -> begin
(

let _57_516 = (FStar_Syntax_Subst.open_term binders repr)
in (match (_57_516) with
| (binders, repr) -> begin
(

let env = (

let _57_517 = env
in (let _152_596 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _152_596; subst = _57_517.subst; tc_const = _57_517.tc_const}))
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

let _57_532 = x
in {FStar_Syntax_Syntax.ppname = _57_532.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_532.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (t))))))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(let _152_599 = (let _152_598 = (let _152_597 = (star_type' env t)
in ((_152_597), (m)))
in FStar_Syntax_Syntax.Tm_meta (_152_598))
in (mk _152_599))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), something) -> begin
(let _152_604 = (let _152_603 = (let _152_602 = (star_type' env e)
in (let _152_601 = (let _152_600 = (star_type' env t)
in FStar_Util.Inl (_152_600))
in ((_152_602), (_152_601), (something))))
in FStar_Syntax_Syntax.Tm_ascribed (_152_603))
in (mk _152_604))
end
| FStar_Syntax_Syntax.Tm_ascribed (_57_545) -> begin
(let _152_607 = (let _152_606 = (let _152_605 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_ascribed is outside of the definition language: %s" _152_605))
in FStar_Syntax_Syntax.Err (_152_606))
in (Prims.raise _152_607))
end
| FStar_Syntax_Syntax.Tm_refine (_57_548) -> begin
(let _152_610 = (let _152_609 = (let _152_608 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_refine is outside of the definition language: %s" _152_608))
in FStar_Syntax_Syntax.Err (_152_609))
in (Prims.raise _152_610))
end
| FStar_Syntax_Syntax.Tm_uinst (_57_551) -> begin
(let _152_613 = (let _152_612 = (let _152_611 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_uinst is outside of the definition language: %s" _152_611))
in FStar_Syntax_Syntax.Err (_152_612))
in (Prims.raise _152_613))
end
| FStar_Syntax_Syntax.Tm_constant (_57_554) -> begin
(let _152_616 = (let _152_615 = (let _152_614 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_constant is outside of the definition language: %s" _152_614))
in FStar_Syntax_Syntax.Err (_152_615))
in (Prims.raise _152_616))
end
| FStar_Syntax_Syntax.Tm_match (_57_557) -> begin
(let _152_619 = (let _152_618 = (let _152_617 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_match is outside of the definition language: %s" _152_617))
in FStar_Syntax_Syntax.Err (_152_618))
in (Prims.raise _152_619))
end
| FStar_Syntax_Syntax.Tm_let (_57_560) -> begin
(let _152_622 = (let _152_621 = (let _152_620 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_let is outside of the definition language: %s" _152_620))
in FStar_Syntax_Syntax.Err (_152_621))
in (Prims.raise _152_622))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_563) -> begin
(let _152_625 = (let _152_624 = (let _152_623 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_uvar is outside of the definition language: %s" _152_623))
in FStar_Syntax_Syntax.Err (_152_624))
in (Prims.raise _152_625))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _152_628 = (let _152_627 = (let _152_626 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_unknown is outside of the definition language: %s" _152_626))
in FStar_Syntax_Syntax.Err (_152_627))
in (Prims.raise _152_628))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_567) -> begin
(FStar_All.failwith "impossible")
end)))))


let is_monadic : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  Prims.bool = (fun _57_3 -> (match (_57_3) with
| None -> begin
(FStar_All.failwith "un-annotated lambda?!")
end
| (Some (FStar_Util.Inl ({FStar_Syntax_Syntax.eff_name = lid; FStar_Syntax_Syntax.res_typ = _; FStar_Syntax_Syntax.cflags = _; FStar_Syntax_Syntax.comp = _}))) | (Some (FStar_Util.Inr (lid))) -> begin
(FStar_Ident.lid_equals lid FStar_Syntax_Const.monadic_lid)
end))


let rec is_C : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match ((let _152_636 = (FStar_Syntax_Subst.compress t)
in _152_636.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) when (FStar_Syntax_Util.is_tuple_constructor head) -> begin
(

let r = (let _152_638 = (let _152_637 = (FStar_List.hd args)
in (Prims.fst _152_637))
in (is_C _152_638))
in if r then begin
(

let _57_593 = if (not ((FStar_List.for_all (fun _57_592 -> (match (_57_592) with
| (h, _57_591) -> begin
(is_C h)
end)) args))) then begin
(FStar_All.failwith "not a C (A * C)")
end else begin
()
end
in true)
end else begin
(

let _57_599 = if (not ((FStar_List.for_all (fun _57_598 -> (match (_57_598) with
| (h, _57_597) -> begin
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

let _57_607 = if (is_C t) then begin
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
| _57_627 -> begin
false
end))


let mk_return : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let p_type = (mk_star_to_type mk env t)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'" None p_type)
in (

let body = (let _152_654 = (let _152_653 = (let _152_652 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _152_651 = (let _152_650 = (let _152_649 = (FStar_Syntax_Syntax.as_implicit false)
in ((e), (_152_649)))
in (_152_650)::[])
in ((_152_652), (_152_651))))
in FStar_Syntax_Syntax.Tm_app (_152_653))
in (mk _152_654))
in (let _152_656 = (let _152_655 = (FStar_Syntax_Syntax.mk_binder p)
in (_152_655)::[])
in (FStar_Syntax_Util.abs _152_656 body None)))))))


let is_unknown : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun _57_4 -> (match (_57_4) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| _57_639 -> begin
false
end))


let rec check : env  ->  FStar_Syntax_Syntax.term  ->  nm  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e context_nm -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let return_if = (fun _57_649 -> (match (_57_649) with
| (rec_nm, s_e, u_e) -> begin
(

let check = (fun t1 t2 -> if ((not ((is_unknown t2.FStar_Syntax_Syntax.n))) && (not ((let _152_710 = (FStar_TypeChecker_Rel.teq env.env t1 t2)
in (FStar_TypeChecker_Rel.is_trivial _152_710))))) then begin
(let _152_715 = (let _152_714 = (let _152_713 = (FStar_Syntax_Print.term_to_string e)
in (let _152_712 = (FStar_Syntax_Print.term_to_string t1)
in (let _152_711 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check]: the expression [%s] has type [%s] but should have type [%s]" _152_713 _152_712 _152_711))))
in FStar_Syntax_Syntax.Err (_152_714))
in (Prims.raise _152_715))
end else begin
()
end)
in (match (((rec_nm), (context_nm))) with
| ((N (t1), N (t2))) | ((M (t1), M (t2))) -> begin
(

let _57_661 = (check t1 t2)
in ((rec_nm), (s_e), (u_e)))
end
| (N (t1), M (t2)) -> begin
(

let _57_668 = (check t1 t2)
in (let _152_716 = (mk_return env t1 s_e)
in ((M (t1)), (_152_716), (u_e))))
end
| (M (t1), N (t2)) -> begin
(let _152_721 = (let _152_720 = (let _152_719 = (FStar_Syntax_Print.term_to_string e)
in (let _152_718 = (FStar_Syntax_Print.term_to_string t1)
in (let _152_717 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]" _152_719 _152_718 _152_717))))
in FStar_Syntax_Syntax.Err (_152_720))
in (Prims.raise _152_721))
end))
end))
in (

let ensure_m = (fun env e2 -> (

let strip_m = (fun _57_5 -> (match (_57_5) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_685 -> begin
(FStar_All.failwith "impossible")
end))
in (match (context_nm) with
| N (t) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren\'t"), (e2.FStar_Syntax_Syntax.pos)))))
end
| M (_57_690) -> begin
(let _152_728 = (check env e2 context_nm)
in (strip_m _152_728))
end)))
in (match ((let _152_729 = (FStar_Syntax_Subst.compress e)
in _152_729.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
(let _152_730 = (infer env e)
in (return_if _152_730))
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
| FStar_Syntax_Syntax.Tm_let (_57_741) -> begin
(let _152_738 = (let _152_737 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_let %s" _152_737))
in (FStar_All.failwith _152_738))
end
| FStar_Syntax_Syntax.Tm_type (_57_744) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_747) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_57_750) -> begin
(let _152_740 = (let _152_739 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_refine %s" _152_739))
in (FStar_All.failwith _152_740))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_753) -> begin
(let _152_742 = (let _152_741 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_uvar %s" _152_741))
in (FStar_All.failwith _152_742))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_756) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _152_747 = (let _152_746 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_unknown %s" _152_746))
in (FStar_All.failwith _152_747))
end)))))
and infer : env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.env)
in (match ((let _152_753 = (FStar_Syntax_Subst.compress e)
in _152_753.FStar_Syntax_Syntax.n)) with
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

let _57_776 = env
in (let _152_754 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _152_754; subst = _57_776.subst; tc_const = _57_776.tc_const}))
in (

let s_binders = (FStar_List.map (fun _57_781 -> (match (_57_781) with
| (bv, qual) -> begin
(

let sort = (star_type' env bv.FStar_Syntax_Syntax.sort)
in (((

let _57_783 = bv
in {FStar_Syntax_Syntax.ppname = _57_783.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_783.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (qual)))
end)) binders)
in (

let _57_805 = (FStar_List.fold_left (fun _57_788 _57_791 -> (match (((_57_788), (_57_791))) with
| ((env, acc), (bv, qual)) -> begin
(

let c = bv.FStar_Syntax_Syntax.sort
in if (is_C c) then begin
(

let xw = (let _152_758 = (star_type' env c)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "^w") None _152_758))
in (

let x = (

let _57_794 = bv
in (let _152_760 = (let _152_759 = (FStar_Syntax_Syntax.bv_to_name xw)
in (trans_F_ env c _152_759))
in {FStar_Syntax_Syntax.ppname = _57_794.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_794.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _152_760}))
in (

let env = (

let _57_797 = env
in (let _152_764 = (let _152_763 = (let _152_762 = (let _152_761 = (FStar_Syntax_Syntax.bv_to_name xw)
in ((bv), (_152_761)))
in FStar_Syntax_Syntax.NT (_152_762))
in (_152_763)::env.subst)
in {env = _57_797.env; subst = _152_764; tc_const = _57_797.tc_const}))
in (let _152_768 = (let _152_767 = (FStar_Syntax_Syntax.mk_binder x)
in (let _152_766 = (let _152_765 = (FStar_Syntax_Syntax.mk_binder xw)
in (_152_765)::acc)
in (_152_767)::_152_766))
in ((env), (_152_768))))))
end else begin
(

let x = (

let _57_800 = bv
in (let _152_769 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_800.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_800.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _152_769}))
in (let _152_771 = (let _152_770 = (FStar_Syntax_Syntax.mk_binder x)
in (_152_770)::acc)
in ((env), (_152_771))))
end)
end)) ((env), ([])) binders)
in (match (_57_805) with
| (env, u_binders) -> begin
(

let u_binders = (FStar_List.rev u_binders)
in (

let print_what = (

let strb = (FStar_Util.new_string_builder ())
in (

let _57_819 = (match (what) with
| None -> begin
(FStar_Util.string_builder_append strb "None")
end
| Some (FStar_Util.Inl (lc)) -> begin
(

let _57_812 = (FStar_Util.string_builder_append strb "Some Inr ")
in (FStar_Util.string_builder_append strb (FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name)))
end
| Some (FStar_Util.Inr (lid)) -> begin
(

let _57_817 = (FStar_Util.string_builder_append strb "Some Inr ")
in (FStar_Util.string_builder_append strb (FStar_Ident.text_of_lid lid)))
end)
in (FStar_Util.string_of_string_builder strb)))
in (

let _57_822 = (let _152_772 = (FStar_Syntax_Print.term_to_string body)
in (FStar_Util.print2_warning "Term %s ::: what %s \n" _152_772 print_what))
in (

let _57_832 = (

let check_what = if (is_monadic what) then begin
check_m
end else begin
check_n
end
in (

let _57_828 = (check_what env body)
in (match (_57_828) with
| (t, s_body, u_body) -> begin
(let _152_778 = (let _152_777 = if (is_monadic what) then begin
M (t)
end else begin
N (t)
end
in (comp_of_nm _152_777))
in ((_152_778), (s_body), (u_body)))
end)))
in (match (_57_832) with
| (comp, s_body, u_body) -> begin
(

let t = (FStar_Syntax_Util.arrow binders comp)
in (

let s_what = (match (what) with
| None -> begin
None
end
| Some (FStar_Util.Inl (lc)) -> begin
if (FStar_Ident.lid_equals lc.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.monadic_lid) then begin
(let _152_784 = (let _152_783 = (let _152_782 = (let _152_781 = (let _152_780 = (let _152_779 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.comp_result _152_779))
in (FStar_All.pipe_left double_star _152_780))
in (FStar_Syntax_Syntax.mk_Total _152_781))
in (FStar_Syntax_Util.lcomp_of_comp _152_782))
in FStar_Util.Inl (_152_783))
in Some (_152_784))
end else begin
Some (FStar_Util.Inl ((

let _57_838 = lc
in {FStar_Syntax_Syntax.eff_name = _57_838.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _57_838.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _57_838.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _57_840 -> (match (()) with
| () -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let result_typ = (star_type' env (FStar_Syntax_Util.comp_result c))
in (FStar_Syntax_Util.set_result_typ c result_typ)))
end))})))
end
end
| Some (FStar_Util.Inr (lid)) -> begin
Some (FStar_Util.Inr (if (FStar_Ident.lid_equals lid FStar_Syntax_Const.monadic_lid) then begin
FStar_Syntax_Const.effect_Tot_lid
end else begin
lid
end))
end)
in (

let u_what = (

let comp = (let _152_787 = (is_monadic what)
in (let _152_786 = (FStar_Syntax_Subst.subst env.subst s_body)
in (trans_G env (FStar_Syntax_Util.comp_result comp) _152_787 _152_786)))
in Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp comp))))
in (

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
in ((N (t)), (s_term), (u_term)))))))))))
end)))))
end)))))))
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = {FStar_Syntax_Syntax.v = lid; FStar_Syntax_Syntax.ty = _57_862; FStar_Syntax_Syntax.p = _57_860}; FStar_Syntax_Syntax.fv_delta = _57_858; FStar_Syntax_Syntax.fv_qual = _57_856}) -> begin
(

let _57_870 = (FStar_TypeChecker_Env.lookup_lid env.env lid)
in (match (_57_870) with
| (_57_868, t) -> begin
(

let txt = (FStar_Ident.text_of_lid lid)
in (let _152_789 = (let _152_788 = (normalize t)
in N (_152_788))
in ((_152_789), (e), (e))))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_879 = (check_n env head)
in (match (_57_879) with
| (t_head, s_head, u_head) -> begin
(

let is_arrow = (fun t -> (match ((let _152_792 = (FStar_Syntax_Subst.compress t)
in _152_792.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_883) -> begin
true
end
| _57_886 -> begin
false
end))
in (

let rec flatten = (fun t -> (match ((let _152_795 = (FStar_Syntax_Subst.compress t)
in _152_795.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (t, _57_898); FStar_Syntax_Syntax.tk = _57_895; FStar_Syntax_Syntax.pos = _57_893; FStar_Syntax_Syntax.vars = _57_891}) when (is_arrow t) -> begin
(

let _57_906 = (flatten t)
in (match (_57_906) with
| (binders', comp) -> begin
(((FStar_List.append binders binders')), (comp))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
((binders), (comp))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, _57_913, _57_915) -> begin
(flatten e)
end
| _57_919 -> begin
(let _152_798 = (let _152_797 = (let _152_796 = (FStar_Syntax_Print.term_to_string t_head)
in (FStar_Util.format1 "%s: not a function type" _152_796))
in FStar_Syntax_Syntax.Err (_152_797))
in (Prims.raise _152_798))
end))
in (

let _57_922 = (flatten t_head)
in (match (_57_922) with
| (binders, comp) -> begin
(

let n = (FStar_List.length binders)
in (

let n' = (FStar_List.length args)
in (

let _57_925 = if ((FStar_List.length binders) < (FStar_List.length args)) then begin
(let _152_803 = (let _152_802 = (let _152_801 = (FStar_Util.string_of_int n)
in (let _152_800 = (FStar_Util.string_of_int (n' - n))
in (let _152_799 = (FStar_Util.string_of_int n)
in (FStar_Util.format3 "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments." _152_801 _152_800 _152_799))))
in FStar_Syntax_Syntax.Err (_152_802))
in (Prims.raise _152_803))
end else begin
()
end
in (

let _57_929 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (_57_929) with
| (binders, comp) -> begin
(

let rec final_type = (fun subst _57_934 args -> (match (_57_934) with
| (binders, comp) -> begin
(match (((binders), (args))) with
| ([], []) -> begin
(let _152_811 = (let _152_810 = (FStar_Syntax_Subst.subst_comp subst comp)
in _152_810.FStar_Syntax_Syntax.n)
in (nm_of_comp _152_811))
end
| (binders, []) -> begin
(match ((let _152_814 = (let _152_813 = (let _152_812 = (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))))
in (FStar_Syntax_Subst.subst subst _152_812))
in (FStar_Syntax_Subst.compress _152_813))
in _152_814.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(let _152_818 = (let _152_817 = (let _152_816 = (let _152_815 = (FStar_Syntax_Subst.close_comp binders comp)
in ((binders), (_152_815)))
in FStar_Syntax_Syntax.Tm_arrow (_152_816))
in (mk _152_817))
in N (_152_818))
end
| _57_947 -> begin
(FStar_All.failwith "wat?")
end)
end
| ([], (_57_952)::_57_950) -> begin
(FStar_All.failwith "just checked that?!")
end
| (((bv, _57_958))::binders, ((arg, _57_964))::args) -> begin
(final_type ((FStar_Syntax_Syntax.NT (((bv), (arg))))::subst) ((binders), (comp)) args)
end)
end))
in (

let final_type = (final_type [] ((binders), (comp)) args)
in (

let _57_972 = (FStar_List.splitAt n' binders)
in (match (_57_972) with
| (binders, _57_971) -> begin
(

let _57_993 = (let _152_833 = (FStar_List.map2 (fun _57_976 _57_979 -> (match (((_57_976), (_57_979))) with
| ((bv, _57_975), (arg, q)) -> begin
(match ((let _152_821 = (FStar_Syntax_Subst.compress bv.FStar_Syntax_Syntax.sort)
in _152_821.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_981) -> begin
(

let arg = ((arg), (q))
in ((arg), ((arg)::[])))
end
| _57_985 -> begin
(

let _57_990 = (check_n env arg)
in (match (_57_990) with
| (_57_987, s_arg, u_arg) -> begin
(let _152_832 = (let _152_822 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_arg), (_152_822)))
in (let _152_831 = if (is_C bv.FStar_Syntax_Syntax.sort) then begin
(let _152_828 = (let _152_824 = (FStar_Syntax_Subst.subst env.subst s_arg)
in (let _152_823 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_824), (_152_823))))
in (let _152_827 = (let _152_826 = (let _152_825 = (FStar_Syntax_Syntax.as_implicit false)
in ((u_arg), (_152_825)))
in (_152_826)::[])
in (_152_828)::_152_827))
end else begin
(let _152_830 = (let _152_829 = (FStar_Syntax_Syntax.as_implicit false)
in ((u_arg), (_152_829)))
in (_152_830)::[])
end
in ((_152_832), (_152_831))))
end))
end)
end)) binders args)
in (FStar_List.split _152_833))
in (match (_57_993) with
| (s_args, u_args) -> begin
(

let u_args = (FStar_List.flatten u_args)
in (let _152_835 = (mk (FStar_Syntax_Syntax.Tm_app (((s_head), (s_args)))))
in (let _152_834 = (mk (FStar_Syntax_Syntax.Tm_app (((u_head), (u_args)))))
in ((final_type), (_152_835), (_152_834)))))
end))
end))))
end)))))
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
(let _152_837 = (let _152_836 = (env.tc_const c)
in N (_152_836))
in ((_152_837), (e), (e)))
end
| FStar_Syntax_Syntax.Tm_let (_57_1024) -> begin
(let _152_839 = (let _152_838 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_let %s" _152_838))
in (FStar_All.failwith _152_839))
end
| FStar_Syntax_Syntax.Tm_type (_57_1027) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_1030) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_57_1033) -> begin
(let _152_841 = (let _152_840 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_refine %s" _152_840))
in (FStar_All.failwith _152_841))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_1036) -> begin
(let _152_843 = (let _152_842 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_uvar %s" _152_842))
in (FStar_All.failwith _152_843))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_1039) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _152_848 = (let _152_847 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_unknown %s" _152_847))
in (FStar_All.failwith _152_848))
end))))
and mk_match : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e0 branches f -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e0.FStar_Syntax_Syntax.pos))
in (

let _57_1052 = (check_n env e0)
in (match (_57_1052) with
| (_57_1049, s_e0, u_e0) -> begin
(

let _57_1069 = (let _152_864 = (FStar_List.map (fun b -> (match ((FStar_Syntax_Subst.open_branch b)) with
| (pat, None, body) -> begin
(

let env = (

let _57_1058 = env
in (let _152_863 = (let _152_862 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env.env _152_862))
in {env = _152_863; subst = _57_1058.subst; tc_const = _57_1058.tc_const}))
in (

let _57_1064 = (f env body)
in (match (_57_1064) with
| (nm, s_body, u_body) -> begin
((nm), (((pat), (None), (((s_body), (u_body), (body))))))
end)))
end
| _57_1066 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("No when clauses in the definition language")))
end)) branches)
in (FStar_List.split _152_864))
in (match (_57_1069) with
| (nms, branches) -> begin
(

let t1 = (match ((FStar_List.hd nms)) with
| (M (t1)) | (N (t1)) -> begin
t1
end)
in (

let has_m = (FStar_List.existsb (fun _57_6 -> (match (_57_6) with
| M (_57_1076) -> begin
true
end
| _57_1079 -> begin
false
end)) nms)
in (

let _57_1113 = (let _152_868 = (FStar_List.map2 (fun nm _57_1088 -> (match (_57_1088) with
| (pat, guard, (s_body, u_body, original_body)) -> begin
(match (((nm), (has_m))) with
| ((N (t2), false)) | ((M (t2), true)) -> begin
((nm), (((pat), (guard), (s_body))), (((pat), (guard), (u_body))))
end
| (N (t2), true) -> begin
(

let _57_1104 = (check env original_body (M (t2)))
in (match (_57_1104) with
| (_57_1101, s_body, u_body) -> begin
((M (t2)), (((pat), (guard), (s_body))), (((pat), (guard), (u_body))))
end))
end
| (M (_57_1106), false) -> begin
(FStar_All.failwith "impossible")
end)
end)) nms branches)
in (FStar_List.unzip3 _152_868))
in (match (_57_1113) with
| (nms, s_branches, u_branches) -> begin
if has_m then begin
(

let p_type = (mk_star_to_type mk env t1)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" None p_type)
in (

let s_branches = (FStar_List.map (fun _57_1119 -> (match (_57_1119) with
| (pat, guard, s_body) -> begin
(

let s_body = (let _152_875 = (let _152_874 = (let _152_873 = (let _152_872 = (let _152_871 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _152_870 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_871), (_152_870))))
in (_152_872)::[])
in ((s_body), (_152_873)))
in FStar_Syntax_Syntax.Tm_app (_152_874))
in (mk _152_875))
in ((pat), (guard), (s_body)))
end)) s_branches)
in (

let s_branches = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let s_e = (let _152_878 = (let _152_876 = (FStar_Syntax_Syntax.mk_binder p)
in (_152_876)::[])
in (let _152_877 = (mk (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches)))))
in (FStar_Syntax_Util.abs _152_878 _152_877 None)))
in (

let t1_star = (let _152_882 = (let _152_880 = (let _152_879 = (FStar_Syntax_Syntax.new_bv None p_type)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _152_879))
in (_152_880)::[])
in (let _152_881 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _152_882 _152_881)))
in (let _152_884 = (mk (FStar_Syntax_Syntax.Tm_ascribed (((s_e), (FStar_Util.Inl (t1_star)), (None)))))
in (let _152_883 = (mk (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches)))))
in ((M (t1)), (_152_884), (_152_883)))))))))))
end else begin
(

let s_branches = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let t1_star = t1
in (let _152_889 = (let _152_887 = (let _152_886 = (let _152_885 = (mk (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches)))))
in ((_152_885), (FStar_Util.Inl (t1_star)), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (_152_886))
in (mk _152_887))
in (let _152_888 = (mk (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches)))))
in ((N (t1)), (_152_889), (_152_888)))))))
end
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

let x_binders = (let _152_909 = (FStar_Syntax_Syntax.mk_binder x)
in (_152_909)::[])
in (

let _57_1141 = (FStar_Syntax_Subst.open_term x_binders e2)
in (match (_57_1141) with
| (x_binders, e2) -> begin
(

let s_binding = if (FStar_Ident.lid_equals FStar_Syntax_Const.monadic_lid binding.FStar_Syntax_Syntax.lbeff) then begin
(

let _57_1142 = binding
in (let _152_910 = (double_star binding.FStar_Syntax_Syntax.lbtyp)
in {FStar_Syntax_Syntax.lbname = _57_1142.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_1142.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _152_910; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _57_1142.FStar_Syntax_Syntax.lbdef}))
end else begin
(

let _57_1144 = binding
in (let _152_911 = (star_type' env binding.FStar_Syntax_Syntax.lbtyp)
in {FStar_Syntax_Syntax.lbname = _57_1144.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_1144.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _152_911; FStar_Syntax_Syntax.lbeff = _57_1144.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _57_1144.FStar_Syntax_Syntax.lbdef}))
end
in (match ((infer env e1)) with
| (N (t1), s_e1, u_e1) -> begin
(

let u_binding = if (is_C t1) then begin
(

let _57_1152 = binding
in (let _152_913 = (let _152_912 = (FStar_Syntax_Subst.subst env.subst s_e1)
in (trans_F_ env t1 _152_912))
in {FStar_Syntax_Syntax.lbname = _57_1152.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_1152.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _152_913; FStar_Syntax_Syntax.lbeff = _57_1152.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _57_1152.FStar_Syntax_Syntax.lbdef}))
end else begin
binding
end
in (

let env = (

let _57_1155 = env
in (let _152_914 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_1157 = x
in {FStar_Syntax_Syntax.ppname = _57_1157.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1157.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _152_914; subst = _57_1155.subst; tc_const = _57_1155.tc_const}))
in (

let _57_1163 = (proceed env e2)
in (match (_57_1163) with
| (nm_rec, s_e2, u_e2) -> begin
(let _152_922 = (let _152_917 = (let _152_916 = (let _152_915 = (FStar_Syntax_Subst.close x_binders s_e2)
in ((((false), (((

let _57_1164 = s_binding
in {FStar_Syntax_Syntax.lbname = _57_1164.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_1164.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1164.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1164.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = s_e1}))::[]))), (_152_915)))
in FStar_Syntax_Syntax.Tm_let (_152_916))
in (mk _152_917))
in (let _152_921 = (let _152_920 = (let _152_919 = (let _152_918 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _57_1166 = u_binding
in {FStar_Syntax_Syntax.lbname = _57_1166.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_1166.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1166.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1166.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_152_918)))
in FStar_Syntax_Syntax.Tm_let (_152_919))
in (mk _152_920))
in ((nm_rec), (_152_922), (_152_921))))
end))))
end
| (M (t1), s_e1, u_e1) -> begin
(

let u_binding = (

let _57_1173 = binding
in {FStar_Syntax_Syntax.lbname = _57_1173.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_1173.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.lbdef = _57_1173.FStar_Syntax_Syntax.lbdef})
in (

let env = (

let _57_1176 = env
in (let _152_923 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_1178 = x
in {FStar_Syntax_Syntax.ppname = _57_1178.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1178.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _152_923; subst = _57_1176.subst; tc_const = _57_1176.tc_const}))
in (

let _57_1184 = (ensure_m env e2)
in (match (_57_1184) with
| (t2, s_e2, u_e2) -> begin
(

let p_type = (mk_star_to_type mk env t2)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" None p_type)
in (

let s_e2 = (let _152_929 = (let _152_928 = (let _152_927 = (let _152_926 = (let _152_925 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _152_924 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_925), (_152_924))))
in (_152_926)::[])
in ((s_e2), (_152_927)))
in FStar_Syntax_Syntax.Tm_app (_152_928))
in (mk _152_929))
in (

let s_e2 = (FStar_Syntax_Util.abs x_binders s_e2 None)
in (

let body = (let _152_934 = (let _152_933 = (let _152_932 = (let _152_931 = (let _152_930 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_e2), (_152_930)))
in (_152_931)::[])
in ((s_e1), (_152_932)))
in FStar_Syntax_Syntax.Tm_app (_152_933))
in (mk _152_934))
in (let _152_941 = (let _152_936 = (let _152_935 = (FStar_Syntax_Syntax.mk_binder p)
in (_152_935)::[])
in (FStar_Syntax_Util.abs _152_936 body None))
in (let _152_940 = (let _152_939 = (let _152_938 = (let _152_937 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _57_1190 = u_binding
in {FStar_Syntax_Syntax.lbname = _57_1190.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_1190.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1190.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1190.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_152_937)))
in FStar_Syntax_Syntax.Tm_let (_152_938))
in (mk _152_939))
in ((M (t2)), (_152_941), (_152_940)))))))))
end))))
end))
end)))))))
and check_n : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _152_944 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in N (_152_944))
in (match ((check env e mn)) with
| (N (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_1201 -> begin
(FStar_All.failwith "[check_n]: impossible")
end)))
and check_m : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _152_947 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in M (_152_947))
in (match ((check env e mn)) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_1211 -> begin
(FStar_All.failwith "[check_m]: impossible")
end)))
and comp_of_nm : nm_  ->  FStar_Syntax_Syntax.comp = (fun nm -> (match (nm) with
| N (t) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| M (t) -> begin
(mk_M t)
end))
and mk_M : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun t -> (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_unknown)::[]; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.monadic_lid; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = []}))
and type_of_comp : (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.typ = (fun t -> (FStar_Syntax_Util.comp_result t))
and trans_F_ : env_  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> (

let _57_1222 = if (not ((is_C c))) then begin
(FStar_All.failwith "not a C")
end else begin
()
end
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos))
in (match ((let _152_956 = (FStar_Syntax_Subst.compress c)
in _152_956.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_1232 = (FStar_Syntax_Util.head_and_args wp)
in (match (_57_1232) with
| (wp_head, wp_args) -> begin
(

let _57_1233 = if ((not (((FStar_List.length wp_args) = (FStar_List.length args)))) || (not ((let _152_957 = (FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length wp_args) FStar_Range.dummyRange)
in (FStar_Syntax_Util.is_constructor wp_head _152_957))))) then begin
(FStar_All.failwith "mismatch")
end else begin
()
end
in (let _152_964 = (let _152_963 = (let _152_962 = (FStar_List.map2 (fun _57_1238 _57_1242 -> (match (((_57_1238), (_57_1242))) with
| ((arg, _57_1237), (wp_arg, _57_1241)) -> begin
(let _152_961 = (trans_F_ env arg wp_arg)
in (let _152_960 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_961), (_152_960))))
end)) args wp_args)
in ((head), (_152_962)))
in FStar_Syntax_Syntax.Tm_app (_152_963))
in (mk _152_964)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let binders = (FStar_Syntax_Util.name_binders binders)
in (

let _57_1250 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (_57_1250) with
| (binders_orig, comp) -> begin
(

let _57_1259 = (let _152_976 = (FStar_List.map (fun _57_1253 -> (match (_57_1253) with
| (bv, q) -> begin
(

let h = bv.FStar_Syntax_Syntax.sort
in if (is_C h) then begin
(

let w' = (let _152_966 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-w\'") None _152_966))
in (let _152_972 = (let _152_971 = (FStar_Syntax_Syntax.mk_binder w')
in (let _152_970 = (let _152_969 = (let _152_968 = (let _152_967 = (FStar_Syntax_Syntax.bv_to_name w')
in (trans_F_ env h _152_967))
in (FStar_Syntax_Syntax.null_binder _152_968))
in (_152_969)::[])
in (_152_971)::_152_970))
in ((w'), (_152_972))))
end else begin
(

let x = (let _152_973 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-x") None _152_973))
in (let _152_975 = (let _152_974 = (FStar_Syntax_Syntax.mk_binder x)
in (_152_974)::[])
in ((x), (_152_975))))
end)
end)) binders_orig)
in (FStar_List.split _152_976))
in (match (_57_1259) with
| (bvs, binders) -> begin
(

let binders = (FStar_List.flatten binders)
in (

let comp = (let _152_978 = (let _152_977 = (FStar_Syntax_Syntax.binders_of_list bvs)
in (FStar_Syntax_Util.rename_binders binders_orig _152_977))
in (FStar_Syntax_Subst.subst_comp _152_978 comp))
in (

let app = (let _152_984 = (let _152_983 = (let _152_982 = (FStar_List.map (fun bv -> (let _152_981 = (FStar_Syntax_Syntax.bv_to_name bv)
in (let _152_980 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_981), (_152_980))))) bvs)
in ((wp), (_152_982)))
in FStar_Syntax_Syntax.Tm_app (_152_983))
in (mk _152_984))
in (

let comp = (let _152_986 = (type_of_comp comp)
in (let _152_985 = (is_monadic_comp comp)
in (trans_G env _152_986 _152_985 app)))
in (FStar_Syntax_Util.arrow binders comp)))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, _57_1267, _57_1269) -> begin
(trans_F_ env e wp)
end
| _57_1273 -> begin
(FStar_All.failwith "impossible trans_F_")
end))))
and trans_G : env_  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env h is_monadic wp -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None h.FStar_Syntax_Syntax.pos))
in if is_monadic then begin
(let _152_997 = (let _152_996 = (star_type' env h)
in (let _152_995 = (let _152_994 = (let _152_993 = (FStar_Syntax_Syntax.as_implicit false)
in ((wp), (_152_993)))
in (_152_994)::[])
in {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_unknown)::[]; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _152_996; FStar_Syntax_Syntax.effect_args = _152_995; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp _152_997))
end else begin
(let _152_998 = (trans_F_ env h wp)
in (FStar_Syntax_Syntax.mk_Total _152_998))
end))


let n : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]))


let star_type : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _152_1005 = (n env.env t)
in (star_type' env _152_1005)))


let star_expr : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env t -> (let _152_1010 = (n env.env t)
in (check_n env _152_1010)))


let trans_F : env_  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> (let _152_1018 = (n env.env c)
in (let _152_1017 = (n env.env wp)
in (trans_F_ env _152_1018 _152_1017))))




