
open Prims

let gen_wps_for_free : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.sigelts * FStar_Syntax_Syntax.eff_decl) = (fun env binders a wp_a ed -> (

let wp_a = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env wp_a)
in (

let a = (

let _57_19 = a
in (let _152_11 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env a.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_19.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_19.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _152_11}))
in (

let d = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))
in (

let _57_26 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _57_24 = (d "Elaborating extra WP combinators")
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
| FStar_Syntax_Syntax.Total (t, _57_36) -> begin
t
end
| _57_40 -> begin
(FStar_All.failwith "wp_a contains non-Tot arrow")
end)
in (let _152_19 = (collect_binders rest)
in (FStar_List.append bs _152_19)))
end
| FStar_Syntax_Syntax.Tm_type (_57_43) -> begin
[]
end
| _57_46 -> begin
(FStar_All.failwith "wp_a doesn\'t end in Type0")
end))
in (

let mk_lid = (fun name -> (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" name))) FStar_Range.dummyRange))
in (

let gamma = (let _152_22 = (collect_binders wp_a)
in (FStar_All.pipe_right _152_22 FStar_Syntax_Util.name_binders))
in (

let _57_50 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
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

let _57_62 = (FStar_TypeChecker_Util.mk_toplevel_definition env lident def)
in (match (_57_62) with
| (sigelt, fv) -> begin
(

let _57_63 = (let _152_34 = (let _152_33 = (FStar_ST.read sigelts)
in (sigelt)::_152_33)
in (FStar_ST.op_Colon_Equals sigelts _152_34))
in fv)
end)))
in (

let binders_of_list = (FStar_List.map (fun _57_67 -> (match (_57_67) with
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

let _57_94 = (

let _57_79 = (

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
in (match (_57_79) with
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

let mk_app = (fun fv t -> (let _152_85 = (let _152_84 = (let _152_83 = (let _152_82 = (FStar_List.map (fun _57_90 -> (match (_57_90) with
| (bv, _57_89) -> begin
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
in (match (_57_94) with
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

let result_comp = (let _152_229 = (let _152_228 = (let _152_226 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _152_225 = (let _152_224 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_152_224)::[])
in (_152_226)::_152_225))
in (let _152_227 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _152_228 _152_227)))
in (FStar_Syntax_Syntax.mk_Total _152_229))
in (

let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (let _152_239 = (let _152_230 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (FStar_List.append binders _152_230))
in (let _152_238 = (

let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "2"))) None)
in (let _152_237 = (let _152_236 = (let _152_235 = (let _152_234 = (let _152_233 = (let _152_232 = (let _152_231 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg _152_231))
in (_152_232)::[])
in (FStar_Syntax_Util.mk_app l_ite _152_233))
in (_152_234)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_235))
in (FStar_Syntax_Util.mk_app c_lift2 _152_236))
in (FStar_Syntax_Util.ascribe _152_237 (FStar_Util.Inr (result_comp)))))
in (FStar_Syntax_Util.abs _152_239 _152_238 (Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp result_comp)))))))))
in (

let wp_if_then_else = (let _152_240 = (mk_lid "wp_if_then_else")
in (register env _152_240 wp_if_then_else))
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

let body = (let _152_251 = (let _152_250 = (let _152_249 = (let _152_246 = (let _152_245 = (let _152_244 = (let _152_243 = (let _152_242 = (let _152_241 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _152_241))
in (_152_242)::[])
in (FStar_Syntax_Util.mk_app l_and _152_243))
in (_152_244)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_245))
in (FStar_Syntax_Util.mk_app c_pure _152_246))
in (let _152_248 = (let _152_247 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_152_247)::[])
in (_152_249)::_152_248))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_250))
in (FStar_Syntax_Util.mk_app c_app _152_251))
in (let _152_253 = (let _152_252 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders _152_252))
in (FStar_Syntax_Util.abs _152_253 body ret_tot_wp_a))))))
in (

let wp_assert = (let _152_254 = (mk_lid "wp_assert")
in (register env _152_254 wp_assert))
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

let body = (let _152_265 = (let _152_264 = (let _152_263 = (let _152_260 = (let _152_259 = (let _152_258 = (let _152_257 = (let _152_256 = (let _152_255 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _152_255))
in (_152_256)::[])
in (FStar_Syntax_Util.mk_app l_imp _152_257))
in (_152_258)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_259))
in (FStar_Syntax_Util.mk_app c_pure _152_260))
in (let _152_262 = (let _152_261 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_152_261)::[])
in (_152_263)::_152_262))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_264))
in (FStar_Syntax_Util.mk_app c_app _152_265))
in (let _152_267 = (let _152_266 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders _152_266))
in (FStar_Syntax_Util.abs _152_267 body ret_tot_wp_a))))))
in (

let wp_assume = (let _152_268 = (mk_lid "wp_assume")
in (register env _152_268 wp_assume))
in (

let wp_assume = (mk_generic_app wp_assume)
in (

let wp_close = (

let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _152_272 = (let _152_270 = (let _152_269 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _152_269))
in (_152_270)::[])
in (let _152_271 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _152_272 _152_271)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let body = (let _152_281 = (let _152_280 = (let _152_279 = (let _152_273 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((FStar_Syntax_Util.tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure _152_273))
in (let _152_278 = (let _152_277 = (let _152_276 = (let _152_275 = (let _152_274 = (FStar_Syntax_Syntax.bv_to_name f)
in (_152_274)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_275))
in (FStar_Syntax_Util.mk_app c_push _152_276))
in (_152_277)::[])
in (_152_279)::_152_278))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_280))
in (FStar_Syntax_Util.mk_app c_app _152_281))
in (let _152_283 = (let _152_282 = (FStar_Syntax_Syntax.binders_of_list ((a)::(b)::(f)::[]))
in (FStar_List.append binders _152_282))
in (FStar_Syntax_Util.abs _152_283 body ret_tot_wp_a))))))
in (

let wp_close = (let _152_284 = (mk_lid "wp_close")
in (register env _152_284 wp_close))
in (

let wp_close = (mk_generic_app wp_close)
in (

let ret_tot_type = (let _152_287 = (let _152_286 = (let _152_285 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_285))
in FStar_Util.Inl (_152_286))
in Some (_152_287))
in (

let ret_gtot_type = (let _152_290 = (let _152_289 = (let _152_288 = (FStar_Syntax_Syntax.mk_GTotal FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_288))
in FStar_Util.Inl (_152_289))
in Some (_152_290))
in (

let mk_forall = (fun x body -> (let _152_301 = (let _152_300 = (let _152_299 = (let _152_298 = (let _152_297 = (let _152_296 = (let _152_295 = (FStar_Syntax_Syntax.mk_binder x)
in (_152_295)::[])
in (FStar_Syntax_Util.abs _152_296 body ret_tot_type))
in (FStar_Syntax_Syntax.as_arg _152_297))
in (_152_298)::[])
in ((FStar_Syntax_Util.tforall), (_152_299)))
in FStar_Syntax_Syntax.Tm_app (_152_300))
in (FStar_Syntax_Syntax.mk _152_301 None FStar_Range.dummyRange)))
in (

let rec is_discrete = (fun t -> (match ((let _152_304 = (FStar_Syntax_Subst.compress t)
in _152_304.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_176) -> begin
false
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((FStar_List.for_all (fun _57_185 -> (match (_57_185) with
| (b, _57_184) -> begin
(is_discrete b.FStar_Syntax_Syntax.sort)
end)) bs) && (is_discrete (FStar_Syntax_Util.comp_result c)))
end
| _57_187 -> begin
true
end))
in (

let rec is_monotonic = (fun t -> (match ((let _152_308 = (FStar_Syntax_Subst.compress t)
in _152_308.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_191) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((FStar_List.for_all (fun _57_200 -> (match (_57_200) with
| (b, _57_199) -> begin
(is_discrete b.FStar_Syntax_Syntax.sort)
end)) bs) && (is_monotonic (FStar_Syntax_Util.comp_result c)))
end
| _57_202 -> begin
(is_discrete t)
end))
in (

let rec mk_rel = (fun rel t x y -> (

let mk_rel = (mk_rel rel)
in (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (match ((let _152_331 = (FStar_Syntax_Subst.compress t)
in _152_331.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_211) -> begin
(rel x y)
end
| (FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(

let a = (Prims.fst binder).FStar_Syntax_Syntax.sort
in if ((is_monotonic a) || (is_monotonic b)) then begin
(

let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (

let body = (let _152_339 = (let _152_334 = (let _152_333 = (let _152_332 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _152_332))
in (_152_333)::[])
in (FStar_Syntax_Util.mk_app x _152_334))
in (let _152_338 = (let _152_337 = (let _152_336 = (let _152_335 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _152_335))
in (_152_336)::[])
in (FStar_Syntax_Util.mk_app y _152_337))
in (mk_rel b _152_339 _152_338)))
in (mk_forall a1 body)))
end else begin
(

let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (

let a2 = (FStar_Syntax_Syntax.gen_bv "a2" None a)
in (

let body = (let _152_351 = (let _152_341 = (FStar_Syntax_Syntax.bv_to_name a1)
in (let _152_340 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_rel a _152_341 _152_340)))
in (let _152_350 = (let _152_349 = (let _152_344 = (let _152_343 = (let _152_342 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _152_342))
in (_152_343)::[])
in (FStar_Syntax_Util.mk_app x _152_344))
in (let _152_348 = (let _152_347 = (let _152_346 = (let _152_345 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg _152_345))
in (_152_346)::[])
in (FStar_Syntax_Util.mk_app y _152_347))
in (mk_rel b _152_349 _152_348)))
in (FStar_Syntax_Util.mk_imp _152_351 _152_350)))
in (let _152_352 = (mk_forall a2 body)
in (mk_forall a1 _152_352)))))
end)
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::binders, comp) -> begin
(

let t = (

let _57_255 = t
in (let _152_356 = (let _152_355 = (let _152_354 = (let _152_353 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _152_353))
in (((binder)::[]), (_152_354)))
in FStar_Syntax_Syntax.Tm_arrow (_152_355))
in {FStar_Syntax_Syntax.n = _152_356; FStar_Syntax_Syntax.tk = _57_255.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_255.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_255.FStar_Syntax_Syntax.vars}))
in (mk_rel t x y))
end
| FStar_Syntax_Syntax.Tm_arrow (_57_259) -> begin
(FStar_All.failwith "unhandled arrow")
end
| _57_262 -> begin
(FStar_Syntax_Util.mk_eq t t x y)
end))))
in (

let stronger = (

let wp1 = (FStar_Syntax_Syntax.gen_bv "wp1" None wp_a)
in (

let wp2 = (FStar_Syntax_Syntax.gen_bv "wp2" None wp_a)
in (

let rec mk_stronger = (fun t x y -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (match ((let _152_363 = (FStar_Syntax_Subst.compress t)
in _152_363.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_271) -> begin
(FStar_Syntax_Util.mk_imp x y)
end
| FStar_Syntax_Syntax.Tm_app (head, args) when (let _152_364 = (FStar_Syntax_Subst.compress head)
in (FStar_Syntax_Util.is_tuple_constructor _152_364)) -> begin
(

let project = (fun i tuple -> (

let projector = (let _152_370 = (let _152_369 = (FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) FStar_Range.dummyRange)
in (FStar_TypeChecker_Env.lookup_projector env _152_369 i))
in (FStar_Syntax_Syntax.fvar _152_370 (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None))
in (FStar_Syntax_Util.mk_app projector ((((tuple), (None)))::[]))))
in (

let _57_291 = (match ((FStar_List.mapi (fun i _57_284 -> (match (_57_284) with
| (t, q) -> begin
(let _152_374 = (project i x)
in (let _152_373 = (project i y)
in (mk_stronger t _152_374 _152_373)))
end)) args)) with
| [] -> begin
(FStar_All.failwith "Impossible : Empty application when creating stronger relation in DM4F")
end
| (rel0)::rels -> begin
((rel0), (rels))
end)
in (match (_57_291) with
| (rel0, rels) -> begin
(FStar_List.fold_left FStar_Syntax_Util.mk_conj rel0 rels)
end)))
end
| (FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(

let bvs = (FStar_List.mapi (fun i _57_323 -> (match (_57_323) with
| (bv, q) -> begin
(let _152_378 = (let _152_377 = (FStar_Util.string_of_int i)
in (Prims.strcat "a" _152_377))
in (FStar_Syntax_Syntax.gen_bv _152_378 None bv.FStar_Syntax_Syntax.sort))
end)) binders)
in (

let args = (FStar_List.map (fun ai -> (let _152_380 = (FStar_Syntax_Syntax.bv_to_name ai)
in (FStar_Syntax_Syntax.as_arg _152_380))) bvs)
in (

let body = (let _152_382 = (FStar_Syntax_Util.mk_app x args)
in (let _152_381 = (FStar_Syntax_Util.mk_app y args)
in (mk_stronger b _152_382 _152_381)))
in (FStar_List.fold_right (fun bv body -> (mk_forall bv body)) bvs body))))
end
| _57_331 -> begin
(FStar_All.failwith "Not a DM elaborated type")
end)))
in (

let body = (let _152_387 = (FStar_Syntax_Util.unascribe wp_a)
in (let _152_386 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (let _152_385 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_stronger _152_387 _152_386 _152_385))))
in (let _152_389 = (let _152_388 = (binders_of_list ((((a), (false)))::(((wp1), (false)))::(((wp2), (false)))::[]))
in (FStar_List.append binders _152_388))
in (FStar_Syntax_Util.abs _152_389 body ret_tot_type))))))
in (

let stronger = (let _152_390 = (mk_lid "stronger")
in (register env _152_390 stronger))
in (

let stronger = (mk_generic_app stronger)
in (

let wp_ite = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let _57_339 = (FStar_Util.prefix gamma)
in (match (_57_339) with
| (wp_args, post) -> begin
(

let k = (FStar_Syntax_Syntax.gen_bv "k" None (Prims.fst post).FStar_Syntax_Syntax.sort)
in (

let equiv = (

let k_tm = (FStar_Syntax_Syntax.bv_to_name k)
in (

let eq = (let _152_391 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst post))
in (mk_rel FStar_Syntax_Util.mk_iff k.FStar_Syntax_Syntax.sort k_tm _152_391))
in (match ((FStar_Syntax_Util.destruct_typ_as_formula eq)) with
| Some (FStar_Syntax_Util.QAll (binders, [], body)) -> begin
(

let k_app = (let _152_392 = (args_of_binders binders)
in (FStar_Syntax_Util.mk_app k_tm _152_392))
in (

let guard_free = (let _152_393 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.guard_free FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _152_393))
in (

let pat = (let _152_395 = (let _152_394 = (FStar_Syntax_Syntax.as_arg k_app)
in (_152_394)::[])
in (FStar_Syntax_Util.mk_app guard_free _152_395))
in (

let pattern_guarded_body = (let _152_401 = (let _152_400 = (let _152_399 = (let _152_398 = (let _152_397 = (let _152_396 = (FStar_Syntax_Syntax.as_arg pat)
in (_152_396)::[])
in (_152_397)::[])
in FStar_Syntax_Syntax.Meta_pattern (_152_398))
in ((body), (_152_399)))
in FStar_Syntax_Syntax.Tm_meta (_152_400))
in (mk _152_401))
in (FStar_Syntax_Util.close_forall binders pattern_guarded_body)))))
end
| _57_354 -> begin
(FStar_All.failwith "Impossible: Expected the equivalence to be a quantified formula")
end)))
in (

let body = (let _152_410 = (let _152_409 = (let _152_408 = (let _152_407 = (FStar_Syntax_Syntax.bv_to_name wp)
in (let _152_406 = (let _152_405 = (args_of_binders wp_args)
in (let _152_404 = (let _152_403 = (let _152_402 = (FStar_Syntax_Syntax.bv_to_name k)
in (FStar_Syntax_Syntax.as_arg _152_402))
in (_152_403)::[])
in (FStar_List.append _152_405 _152_404)))
in (FStar_Syntax_Util.mk_app _152_407 _152_406)))
in (FStar_Syntax_Util.mk_imp equiv _152_408))
in (FStar_Syntax_Util.mk_forall k _152_409))
in (FStar_Syntax_Util.abs gamma _152_410 ret_gtot_type))
in (let _152_412 = (let _152_411 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders _152_411))
in (FStar_Syntax_Util.abs _152_412 body ret_gtot_type)))))
end)))
in (

let wp_ite = (let _152_413 = (mk_lid "wp_ite")
in (register env _152_413 wp_ite))
in (

let wp_ite = (mk_generic_app wp_ite)
in (

let null_wp = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let _57_363 = (FStar_Util.prefix gamma)
in (match (_57_363) with
| (wp_args, post) -> begin
(

let x = (FStar_Syntax_Syntax.gen_bv "x" None FStar_Syntax_Syntax.tun)
in (

let body = (let _152_418 = (let _152_417 = (FStar_All.pipe_left FStar_Syntax_Syntax.bv_to_name (Prims.fst post))
in (let _152_416 = (let _152_415 = (let _152_414 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _152_414))
in (_152_415)::[])
in (FStar_Syntax_Util.mk_app _152_417 _152_416)))
in (FStar_Syntax_Util.mk_forall x _152_418))
in (let _152_421 = (let _152_420 = (let _152_419 = (FStar_Syntax_Syntax.binders_of_list ((a)::[]))
in (FStar_List.append _152_419 gamma))
in (FStar_List.append binders _152_420))
in (FStar_Syntax_Util.abs _152_421 body ret_gtot_type))))
end)))
in (

let null_wp = (let _152_422 = (mk_lid "null_wp")
in (register env _152_422 null_wp))
in (

let null_wp = (mk_generic_app null_wp)
in (

let wp_trivial = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let body = (let _152_432 = (let _152_431 = (let _152_430 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _152_429 = (let _152_428 = (let _152_425 = (let _152_424 = (let _152_423 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg _152_423))
in (_152_424)::[])
in (FStar_Syntax_Util.mk_app null_wp _152_425))
in (let _152_427 = (let _152_426 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_152_426)::[])
in (_152_428)::_152_427))
in (_152_430)::_152_429))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_431))
in (FStar_Syntax_Util.mk_app stronger _152_432))
in (let _152_434 = (let _152_433 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders _152_433))
in (FStar_Syntax_Util.abs _152_434 body ret_tot_type))))
in (

let wp_trivial = (let _152_435 = (mk_lid "wp_trivial")
in (register env _152_435 wp_trivial))
in (

let wp_trivial = (mk_generic_app wp_trivial)
in (

let _57_374 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(d "End Dijkstra monads for free")
end else begin
()
end
in (

let c = (FStar_Syntax_Subst.close binders)
in (let _152_455 = (let _152_437 = (FStar_ST.read sigelts)
in (FStar_List.rev _152_437))
in (let _152_454 = (

let _57_377 = ed
in (let _152_453 = (let _152_438 = (c wp_if_then_else)
in (([]), (_152_438)))
in (let _152_452 = (let _152_439 = (c wp_ite)
in (([]), (_152_439)))
in (let _152_451 = (let _152_440 = (c stronger)
in (([]), (_152_440)))
in (let _152_450 = (let _152_441 = (c wp_close)
in (([]), (_152_441)))
in (let _152_449 = (let _152_442 = (c wp_assert)
in (([]), (_152_442)))
in (let _152_448 = (let _152_443 = (c wp_assume)
in (([]), (_152_443)))
in (let _152_447 = (let _152_444 = (c null_wp)
in (([]), (_152_444)))
in (let _152_446 = (let _152_445 = (c wp_trivial)
in (([]), (_152_445)))
in {FStar_Syntax_Syntax.qualifiers = _57_377.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = _57_377.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = _57_377.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_377.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_377.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_377.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _57_377.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _57_377.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _152_453; FStar_Syntax_Syntax.ite_wp = _152_452; FStar_Syntax_Syntax.stronger = _152_451; FStar_Syntax_Syntax.close_wp = _152_450; FStar_Syntax_Syntax.assert_p = _152_449; FStar_Syntax_Syntax.assume_p = _152_448; FStar_Syntax_Syntax.null_wp = _152_447; FStar_Syntax_Syntax.trivial = _152_446; FStar_Syntax_Syntax.repr = _57_377.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _57_377.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _57_377.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _57_377.FStar_Syntax_Syntax.actions})))))))))
in ((_152_455), (_152_454))))))))))))))))))))))))))))))))))))))))))))))))
end))))))))))))))))))


type env =
{env : FStar_TypeChecker_Env.env; subst : FStar_Syntax_Syntax.subst_elt Prims.list; tc_const : FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))


let empty : FStar_TypeChecker_Env.env  ->  (FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ)  ->  env = (fun env tc_const -> {env = env; subst = []; tc_const = tc_const})


type env_ =
env


let get_env : env  ->  FStar_TypeChecker_Env.env = (fun env -> env.env)


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
| N (_57_388) -> begin
_57_388
end))


let ___M____0 = (fun projectee -> (match (projectee) with
| M (_57_391) -> begin
_57_391
end))


type nm_ =
nm


let nm_of_comp : FStar_Syntax_Syntax.comp'  ->  nm = (fun _57_2 -> (match (_57_2) with
| FStar_Syntax_Syntax.Total (t, _57_395) -> begin
N (t)
end
| FStar_Syntax_Syntax.Comp (c) when (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _57_1 -> (match (_57_1) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| _57_403 -> begin
false
end)))) -> begin
M (c.FStar_Syntax_Syntax.result_typ)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(let _152_516 = (let _152_515 = (let _152_514 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _152_514))
in (FStar_Util.format1 "[nm_of_comp]: impossible (%s)" _152_515))
in (FStar_All.failwith _152_516))
end
| FStar_Syntax_Syntax.GTotal (_57_407) -> begin
(FStar_All.failwith "[nm_of_comp]: impossible (GTot)")
end))


let string_of_nm : nm  ->  Prims.string = (fun _57_3 -> (match (_57_3) with
| N (t) -> begin
(let _152_519 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "N[%s]" _152_519))
end
| M (t) -> begin
(let _152_520 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "M[%s]" _152_520))
end))


let is_monadic_arrow : FStar_Syntax_Syntax.term'  ->  nm = (fun n -> (match (n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_416, {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_422; FStar_Syntax_Syntax.pos = _57_420; FStar_Syntax_Syntax.vars = _57_418}) -> begin
(nm_of_comp n)
end
| _57_428 -> begin
(FStar_All.failwith "unexpected_argument: [is_monadic_arrow]")
end))


let is_monadic_comp = (fun c -> (match ((nm_of_comp c.FStar_Syntax_Syntax.n)) with
| M (_57_431) -> begin
true
end
| N (_57_434) -> begin
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

let star_once = (fun typ -> (let _152_532 = (let _152_530 = (let _152_529 = (FStar_Syntax_Syntax.new_bv None typ)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _152_529))
in (_152_530)::[])
in (let _152_531 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _152_532 _152_531))))
in (let _152_533 = (FStar_All.pipe_right typ star_once)
in (FStar_All.pipe_left star_once _152_533))))


let rec mk_star_to_type : (FStar_Syntax_Syntax.term'  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun mk env a -> (let _152_554 = (let _152_553 = (let _152_552 = (let _152_550 = (let _152_549 = (let _152_547 = (star_type' env a)
in (FStar_Syntax_Syntax.null_bv _152_547))
in (let _152_548 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_549), (_152_548))))
in (_152_550)::[])
in (let _152_551 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_152_552), (_152_551))))
in FStar_Syntax_Syntax.Tm_arrow (_152_553))
in (mk _152_554)))
and star_type' : env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None t.FStar_Syntax_Syntax.pos))
in (

let mk_star_to_type = (mk_star_to_type mk)
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _57_450) -> begin
(

let binders = (FStar_List.map (fun _57_455 -> (match (_57_455) with
| (bv, aqual) -> begin
(let _152_563 = (

let _57_456 = bv
in (let _152_562 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_456.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_456.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _152_562}))
in ((_152_563), (aqual)))
end)) binders)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_460, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (hn, _57_469); FStar_Syntax_Syntax.tk = _57_466; FStar_Syntax_Syntax.pos = _57_464; FStar_Syntax_Syntax.vars = _57_462}) -> begin
(let _152_567 = (let _152_566 = (let _152_565 = (let _152_564 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_GTotal _152_564))
in ((binders), (_152_565)))
in FStar_Syntax_Syntax.Tm_arrow (_152_566))
in (mk _152_567))
end
| _57_476 -> begin
(match ((is_monadic_arrow t.FStar_Syntax_Syntax.n)) with
| N (hn) -> begin
(let _152_571 = (let _152_570 = (let _152_569 = (let _152_568 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_Total _152_568))
in ((binders), (_152_569)))
in FStar_Syntax_Syntax.Tm_arrow (_152_570))
in (mk _152_571))
end
| M (a) -> begin
(let _152_580 = (let _152_579 = (let _152_578 = (let _152_576 = (let _152_575 = (let _152_574 = (let _152_572 = (mk_star_to_type env a)
in (FStar_Syntax_Syntax.null_bv _152_572))
in (let _152_573 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_574), (_152_573))))
in (_152_575)::[])
in (FStar_List.append binders _152_576))
in (let _152_577 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_152_578), (_152_577))))
in FStar_Syntax_Syntax.Tm_arrow (_152_579))
in (mk _152_580))
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

let _57_497 = (FStar_Util.string_builder_append strb "{")
in (

let _57_499 = (let _152_594 = (f x)
in (FStar_Util.string_builder_append strb _152_594))
in (

let _57_504 = (FStar_List.iter (fun x -> (

let _57_502 = (FStar_Util.string_builder_append strb ", ")
in (let _152_596 = (f x)
in (FStar_Util.string_builder_append strb _152_596)))) xs)
in (

let _57_506 = (FStar_Util.string_builder_append strb "}")
in (FStar_Util.string_of_string_builder strb))))))
end)))
in (let _152_598 = (FStar_Syntax_Print.term_to_string t)
in (let _152_597 = (string_of_set FStar_Syntax_Print.bv_to_string s)
in (FStar_Util.print2_warning "Dependency found in term %s : %s" _152_598 _152_597)))))
in (

let rec is_non_dependent_arrow = (fun ty n -> (match ((let _152_603 = (FStar_Syntax_Subst.compress ty)
in _152_603.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
if (not ((FStar_Syntax_Util.is_tot_or_gtot_comp c))) then begin
false
end else begin
try
(match (()) with
| () -> begin
(

let non_dependent_or_raise = (fun s ty -> (

let sinter = (let _152_609 = (FStar_Syntax_Free.names ty)
in (FStar_Util.set_intersect _152_609 s))
in if (not ((FStar_Util.set_is_empty sinter))) then begin
(

let _57_525 = (debug ty sinter)
in (Prims.raise Not_found))
end else begin
()
end))
in (

let _57_529 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_57_529) with
| (binders, c) -> begin
(

let s = (FStar_List.fold_left (fun s _57_534 -> (match (_57_534) with
| (bv, _57_533) -> begin
(

let _57_535 = (non_dependent_or_raise s bv.FStar_Syntax_Syntax.sort)
in (FStar_Util.set_add bv s))
end)) FStar_Syntax_Syntax.no_names binders)
in (

let ct = (FStar_Syntax_Util.comp_result c)
in (

let _57_539 = (non_dependent_or_raise s ct)
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
| _57_543 -> begin
(

let _57_544 = (let _152_613 = (FStar_Syntax_Print.term_to_string ty)
in (FStar_Util.print1_warning "Not a dependent arrow : %s" _152_613))
in false)
end))
in (

let rec is_valid_application = (fun head -> (match ((let _152_616 = (FStar_Syntax_Subst.compress head)
in _152_616.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.option_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.either_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.eq2_lid)) || (let _152_617 = (FStar_Syntax_Subst.compress head)
in (FStar_Syntax_Util.is_tuple_constructor _152_617))) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (is_non_dependent_arrow fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty (FStar_List.length args)) -> begin
(

let res = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.env t)
in (match (res.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (_57_554) -> begin
true
end
| _57_557 -> begin
(

let _57_558 = (let _152_618 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.print1_warning "Got a term which might be a non-dependent user-defined data-type %s\n" _152_618))
in false)
end))
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uinst (t, _57_568) -> begin
(is_valid_application t)
end
| _57_572 -> begin
false
end))
in if (is_valid_application head) then begin
(let _152_623 = (let _152_622 = (let _152_621 = (FStar_List.map (fun _57_575 -> (match (_57_575) with
| (t, qual) -> begin
(let _152_620 = (star_type' env t)
in ((_152_620), (qual)))
end)) args)
in ((head), (_152_621)))
in FStar_Syntax_Syntax.Tm_app (_152_622))
in (mk _152_623))
end else begin
(let _152_626 = (let _152_625 = (let _152_624 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)" _152_624))
in FStar_Syntax_Syntax.Err (_152_625))
in (Prims.raise _152_626))
end)))
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_abs (binders, repr, something) -> begin
(

let _57_595 = (FStar_Syntax_Subst.open_term binders repr)
in (match (_57_595) with
| (binders, repr) -> begin
(

let env = (

let _57_596 = env
in (let _152_627 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _152_627; subst = _57_596.subst; tc_const = _57_596.tc_const}))
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

let _57_611 = x
in {FStar_Syntax_Syntax.ppname = _57_611.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_611.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (t))))))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(let _152_630 = (let _152_629 = (let _152_628 = (star_type' env t)
in ((_152_628), (m)))
in FStar_Syntax_Syntax.Tm_meta (_152_629))
in (mk _152_630))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), something) -> begin
(let _152_635 = (let _152_634 = (let _152_633 = (star_type' env e)
in (let _152_632 = (let _152_631 = (star_type' env t)
in FStar_Util.Inl (_152_631))
in ((_152_633), (_152_632), (something))))
in FStar_Syntax_Syntax.Tm_ascribed (_152_634))
in (mk _152_635))
end
| FStar_Syntax_Syntax.Tm_ascribed (_57_624) -> begin
(let _152_638 = (let _152_637 = (let _152_636 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_ascribed is outside of the definition language: %s" _152_636))
in FStar_Syntax_Syntax.Err (_152_637))
in (Prims.raise _152_638))
end
| FStar_Syntax_Syntax.Tm_refine (_57_627) -> begin
(let _152_641 = (let _152_640 = (let _152_639 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_refine is outside of the definition language: %s" _152_639))
in FStar_Syntax_Syntax.Err (_152_640))
in (Prims.raise _152_641))
end
| FStar_Syntax_Syntax.Tm_uinst (_57_630) -> begin
(let _152_644 = (let _152_643 = (let _152_642 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_uinst is outside of the definition language: %s" _152_642))
in FStar_Syntax_Syntax.Err (_152_643))
in (Prims.raise _152_644))
end
| FStar_Syntax_Syntax.Tm_constant (_57_633) -> begin
(let _152_647 = (let _152_646 = (let _152_645 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_constant is outside of the definition language: %s" _152_645))
in FStar_Syntax_Syntax.Err (_152_646))
in (Prims.raise _152_647))
end
| FStar_Syntax_Syntax.Tm_match (_57_636) -> begin
(let _152_650 = (let _152_649 = (let _152_648 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_match is outside of the definition language: %s" _152_648))
in FStar_Syntax_Syntax.Err (_152_649))
in (Prims.raise _152_650))
end
| FStar_Syntax_Syntax.Tm_let (_57_639) -> begin
(let _152_653 = (let _152_652 = (let _152_651 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_let is outside of the definition language: %s" _152_651))
in FStar_Syntax_Syntax.Err (_152_652))
in (Prims.raise _152_653))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_642) -> begin
(let _152_656 = (let _152_655 = (let _152_654 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_uvar is outside of the definition language: %s" _152_654))
in FStar_Syntax_Syntax.Err (_152_655))
in (Prims.raise _152_656))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _152_659 = (let _152_658 = (let _152_657 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_unknown is outside of the definition language: %s" _152_657))
in FStar_Syntax_Syntax.Err (_152_658))
in (Prims.raise _152_659))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_646) -> begin
(FStar_All.failwith "impossible")
end)))))


let is_monadic = (fun _57_5 -> (match (_57_5) with
| None -> begin
(FStar_All.failwith "un-annotated lambda?!")
end
| (Some (FStar_Util.Inl ({FStar_Syntax_Syntax.eff_name = _; FStar_Syntax_Syntax.res_typ = _; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = _}))) | (Some (FStar_Util.Inr (_, flags))) -> begin
(FStar_All.pipe_right flags (FStar_Util.for_some (fun _57_4 -> (match (_57_4) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| _57_668 -> begin
false
end))))
end))


let rec is_C : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match ((let _152_667 = (FStar_Syntax_Subst.compress t)
in _152_667.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) when (FStar_Syntax_Util.is_tuple_constructor head) -> begin
(

let r = (let _152_669 = (let _152_668 = (FStar_List.hd args)
in (Prims.fst _152_668))
in (is_C _152_669))
in if r then begin
(

let _57_679 = if (not ((FStar_List.for_all (fun _57_678 -> (match (_57_678) with
| (h, _57_677) -> begin
(is_C h)
end)) args))) then begin
(FStar_All.failwith "not a C (A * C)")
end else begin
()
end
in true)
end else begin
(

let _57_685 = if (not ((FStar_List.for_all (fun _57_684 -> (match (_57_684) with
| (h, _57_683) -> begin
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

let _57_693 = if (is_C t) then begin
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
| _57_713 -> begin
false
end))


let mk_return : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let p_type = (mk_star_to_type mk env t)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'" None p_type)
in (

let body = (let _152_685 = (let _152_684 = (let _152_683 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _152_682 = (let _152_681 = (let _152_680 = (FStar_Syntax_Syntax.as_implicit false)
in ((e), (_152_680)))
in (_152_681)::[])
in ((_152_683), (_152_682))))
in FStar_Syntax_Syntax.Tm_app (_152_684))
in (mk _152_685))
in (let _152_687 = (let _152_686 = (FStar_Syntax_Syntax.mk_binder p)
in (_152_686)::[])
in (FStar_Syntax_Util.abs _152_687 body None)))))))


let is_unknown : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun _57_6 -> (match (_57_6) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| _57_725 -> begin
false
end))


let rec check : env  ->  FStar_Syntax_Syntax.term  ->  nm  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e context_nm -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let return_if = (fun _57_735 -> (match (_57_735) with
| (rec_nm, s_e, u_e) -> begin
(

let check = (fun t1 t2 -> if ((not ((is_unknown t2.FStar_Syntax_Syntax.n))) && (not ((let _152_741 = (FStar_TypeChecker_Rel.teq env.env t1 t2)
in (FStar_TypeChecker_Rel.is_trivial _152_741))))) then begin
(let _152_746 = (let _152_745 = (let _152_744 = (FStar_Syntax_Print.term_to_string e)
in (let _152_743 = (FStar_Syntax_Print.term_to_string t1)
in (let _152_742 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check]: the expression [%s] has type [%s] but should have type [%s]" _152_744 _152_743 _152_742))))
in FStar_Syntax_Syntax.Err (_152_745))
in (Prims.raise _152_746))
end else begin
()
end)
in (match (((rec_nm), (context_nm))) with
| ((N (t1), N (t2))) | ((M (t1), M (t2))) -> begin
(

let _57_747 = (check t1 t2)
in ((rec_nm), (s_e), (u_e)))
end
| (N (t1), M (t2)) -> begin
(

let _57_754 = (check t1 t2)
in (let _152_747 = (mk_return env t1 s_e)
in ((M (t1)), (_152_747), (u_e))))
end
| (M (t1), N (t2)) -> begin
(let _152_752 = (let _152_751 = (let _152_750 = (FStar_Syntax_Print.term_to_string e)
in (let _152_749 = (FStar_Syntax_Print.term_to_string t1)
in (let _152_748 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]" _152_750 _152_749 _152_748))))
in FStar_Syntax_Syntax.Err (_152_751))
in (Prims.raise _152_752))
end))
end))
in (

let ensure_m = (fun env e2 -> (

let strip_m = (fun _57_7 -> (match (_57_7) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_771 -> begin
(FStar_All.failwith "impossible")
end))
in (match (context_nm) with
| N (t) -> begin
(let _152_762 = (let _152_761 = (let _152_760 = (let _152_759 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren\'t : " _152_759))
in ((_152_760), (e2.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_152_761))
in (Prims.raise _152_762))
end
| M (_57_776) -> begin
(let _152_763 = (check env e2 context_nm)
in (strip_m _152_763))
end)))
in (match ((let _152_764 = (FStar_Syntax_Subst.compress e)
in _152_764.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
(let _152_765 = (infer env e)
in (return_if _152_765))
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
| FStar_Syntax_Syntax.Tm_let (_57_827) -> begin
(let _152_773 = (let _152_772 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_let %s" _152_772))
in (FStar_All.failwith _152_773))
end
| FStar_Syntax_Syntax.Tm_type (_57_830) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_833) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_57_836) -> begin
(let _152_775 = (let _152_774 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_refine %s" _152_774))
in (FStar_All.failwith _152_775))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_839) -> begin
(let _152_777 = (let _152_776 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_uvar %s" _152_776))
in (FStar_All.failwith _152_777))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_842) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _152_782 = (let _152_781 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_unknown %s" _152_781))
in (FStar_All.failwith _152_782))
end)))))
and infer : env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.env)
in (match ((let _152_788 = (FStar_Syntax_Subst.compress e)
in _152_788.FStar_Syntax_Syntax.n)) with
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

let _57_862 = env
in (let _152_789 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _152_789; subst = _57_862.subst; tc_const = _57_862.tc_const}))
in (

let s_binders = (FStar_List.map (fun _57_867 -> (match (_57_867) with
| (bv, qual) -> begin
(

let sort = (star_type' env bv.FStar_Syntax_Syntax.sort)
in (((

let _57_869 = bv
in {FStar_Syntax_Syntax.ppname = _57_869.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_869.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (qual)))
end)) binders)
in (

let _57_891 = (FStar_List.fold_left (fun _57_874 _57_877 -> (match (((_57_874), (_57_877))) with
| ((env, acc), (bv, qual)) -> begin
(

let c = bv.FStar_Syntax_Syntax.sort
in if (is_C c) then begin
(

let xw = (let _152_793 = (star_type' env c)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "^w") None _152_793))
in (

let x = (

let _57_880 = bv
in (let _152_795 = (let _152_794 = (FStar_Syntax_Syntax.bv_to_name xw)
in (trans_F_ env c _152_794))
in {FStar_Syntax_Syntax.ppname = _57_880.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_880.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _152_795}))
in (

let env = (

let _57_883 = env
in (let _152_799 = (let _152_798 = (let _152_797 = (let _152_796 = (FStar_Syntax_Syntax.bv_to_name xw)
in ((bv), (_152_796)))
in FStar_Syntax_Syntax.NT (_152_797))
in (_152_798)::env.subst)
in {env = _57_883.env; subst = _152_799; tc_const = _57_883.tc_const}))
in (let _152_803 = (let _152_802 = (FStar_Syntax_Syntax.mk_binder x)
in (let _152_801 = (let _152_800 = (FStar_Syntax_Syntax.mk_binder xw)
in (_152_800)::acc)
in (_152_802)::_152_801))
in ((env), (_152_803))))))
end else begin
(

let x = (

let _57_886 = bv
in (let _152_804 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_886.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_886.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _152_804}))
in (let _152_806 = (let _152_805 = (FStar_Syntax_Syntax.mk_binder x)
in (_152_805)::acc)
in ((env), (_152_806))))
end)
end)) ((env), ([])) binders)
in (match (_57_891) with
| (env, u_binders) -> begin
(

let u_binders = (FStar_List.rev u_binders)
in (

let _57_901 = (

let check_what = if (is_monadic what) then begin
check_m
end else begin
check_n
end
in (

let _57_897 = (check_what env body)
in (match (_57_897) with
| (t, s_body, u_body) -> begin
(let _152_812 = (let _152_811 = if (is_monadic what) then begin
M (t)
end else begin
N (t)
end
in (comp_of_nm _152_811))
in ((_152_812), (s_body), (u_body)))
end)))
in (match (_57_901) with
| (comp, s_body, u_body) -> begin
(

let t = (FStar_Syntax_Util.arrow binders comp)
in (

let s_what = (match (what) with
| None -> begin
None
end
| Some (FStar_Util.Inl (lc)) -> begin
if (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _57_8 -> (match (_57_8) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| _57_910 -> begin
false
end)))) then begin
(

let double_starred_comp = (let _152_816 = (let _152_815 = (let _152_814 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.comp_result _152_814))
in (FStar_All.pipe_left double_star _152_815))
in (FStar_Syntax_Syntax.mk_Total _152_816))
in (

let flags = (FStar_List.filter (fun _57_9 -> (match (_57_9) with
| FStar_Syntax_Syntax.CPS -> begin
false
end
| _57_915 -> begin
true
end)) lc.FStar_Syntax_Syntax.cflags)
in (let _152_820 = (let _152_819 = (let _152_818 = (FStar_Syntax_Util.comp_set_flags double_starred_comp flags)
in (FStar_Syntax_Util.lcomp_of_comp _152_818))
in FStar_Util.Inl (_152_819))
in Some (_152_820))))
end else begin
Some (FStar_Util.Inl ((

let _57_917 = lc
in {FStar_Syntax_Syntax.eff_name = _57_917.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _57_917.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _57_917.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _57_919 -> (match (()) with
| () -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let result_typ = (star_type' env (FStar_Syntax_Util.comp_result c))
in (FStar_Syntax_Util.set_result_typ c result_typ)))
end))})))
end
end
| Some (FStar_Util.Inr (lid, flags)) -> begin
(let _152_826 = (let _152_825 = if (FStar_All.pipe_right flags (FStar_Util.for_some (fun _57_10 -> (match (_57_10) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| _57_930 -> begin
false
end)))) then begin
(let _152_824 = (FStar_List.filter (fun _57_11 -> (match (_57_11) with
| FStar_Syntax_Syntax.CPS -> begin
false
end
| _57_934 -> begin
true
end)) flags)
in ((FStar_Syntax_Const.effect_Tot_lid), (_152_824)))
end else begin
((lid), (flags))
end
in FStar_Util.Inr (_152_825))
in Some (_152_826))
end)
in (

let _57_939 = (

let comp = (let _152_828 = (is_monadic what)
in (let _152_827 = (FStar_Syntax_Subst.subst env.subst s_body)
in (trans_G env (FStar_Syntax_Util.comp_result comp) _152_828 _152_827)))
in (let _152_829 = (FStar_Syntax_Util.ascribe u_body (FStar_Util.Inr (comp)))
in ((_152_829), (Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp comp)))))))
in (match (_57_939) with
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
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = {FStar_Syntax_Syntax.v = lid; FStar_Syntax_Syntax.ty = _57_953; FStar_Syntax_Syntax.p = _57_951}; FStar_Syntax_Syntax.fv_delta = _57_949; FStar_Syntax_Syntax.fv_qual = _57_947}) -> begin
(

let _57_961 = (FStar_TypeChecker_Env.lookup_lid env.env lid)
in (match (_57_961) with
| (_57_959, t) -> begin
(

let txt = (FStar_Ident.text_of_lid lid)
in (let _152_831 = (let _152_830 = (normalize t)
in N (_152_830))
in ((_152_831), (e), (e))))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_970 = (check_n env head)
in (match (_57_970) with
| (t_head, s_head, u_head) -> begin
(

let is_arrow = (fun t -> (match ((let _152_834 = (FStar_Syntax_Subst.compress t)
in _152_834.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_974) -> begin
true
end
| _57_977 -> begin
false
end))
in (

let rec flatten = (fun t -> (match ((let _152_837 = (FStar_Syntax_Subst.compress t)
in _152_837.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (t, _57_989); FStar_Syntax_Syntax.tk = _57_986; FStar_Syntax_Syntax.pos = _57_984; FStar_Syntax_Syntax.vars = _57_982}) when (is_arrow t) -> begin
(

let _57_997 = (flatten t)
in (match (_57_997) with
| (binders', comp) -> begin
(((FStar_List.append binders binders')), (comp))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
((binders), (comp))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, _57_1004, _57_1006) -> begin
(flatten e)
end
| _57_1010 -> begin
(let _152_840 = (let _152_839 = (let _152_838 = (FStar_Syntax_Print.term_to_string t_head)
in (FStar_Util.format1 "%s: not a function type" _152_838))
in FStar_Syntax_Syntax.Err (_152_839))
in (Prims.raise _152_840))
end))
in (

let _57_1013 = (flatten t_head)
in (match (_57_1013) with
| (binders, comp) -> begin
(

let n = (FStar_List.length binders)
in (

let n' = (FStar_List.length args)
in (

let _57_1016 = if ((FStar_List.length binders) < (FStar_List.length args)) then begin
(let _152_845 = (let _152_844 = (let _152_843 = (FStar_Util.string_of_int n)
in (let _152_842 = (FStar_Util.string_of_int (n' - n))
in (let _152_841 = (FStar_Util.string_of_int n)
in (FStar_Util.format3 "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments." _152_843 _152_842 _152_841))))
in FStar_Syntax_Syntax.Err (_152_844))
in (Prims.raise _152_845))
end else begin
()
end
in (

let _57_1020 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (_57_1020) with
| (binders, comp) -> begin
(

let rec final_type = (fun subst _57_1025 args -> (match (_57_1025) with
| (binders, comp) -> begin
(match (((binders), (args))) with
| ([], []) -> begin
(let _152_853 = (let _152_852 = (FStar_Syntax_Subst.subst_comp subst comp)
in _152_852.FStar_Syntax_Syntax.n)
in (nm_of_comp _152_853))
end
| (binders, []) -> begin
(match ((let _152_856 = (let _152_855 = (let _152_854 = (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))))
in (FStar_Syntax_Subst.subst subst _152_854))
in (FStar_Syntax_Subst.compress _152_855))
in _152_856.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(let _152_860 = (let _152_859 = (let _152_858 = (let _152_857 = (FStar_Syntax_Subst.close_comp binders comp)
in ((binders), (_152_857)))
in FStar_Syntax_Syntax.Tm_arrow (_152_858))
in (mk _152_859))
in N (_152_860))
end
| _57_1038 -> begin
(FStar_All.failwith "wat?")
end)
end
| ([], (_57_1043)::_57_1041) -> begin
(FStar_All.failwith "just checked that?!")
end
| (((bv, _57_1049))::binders, ((arg, _57_1055))::args) -> begin
(final_type ((FStar_Syntax_Syntax.NT (((bv), (arg))))::subst) ((binders), (comp)) args)
end)
end))
in (

let final_type = (final_type [] ((binders), (comp)) args)
in (

let _57_1063 = (FStar_List.splitAt n' binders)
in (match (_57_1063) with
| (binders, _57_1062) -> begin
(

let _57_1084 = (let _152_867 = (FStar_List.map2 (fun _57_1067 _57_1070 -> (match (((_57_1067), (_57_1070))) with
| ((bv, _57_1066), (arg, q)) -> begin
(match ((let _152_863 = (FStar_Syntax_Subst.compress bv.FStar_Syntax_Syntax.sort)
in _152_863.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_1072) -> begin
(

let arg = ((arg), (q))
in ((arg), ((arg)::[])))
end
| _57_1076 -> begin
(

let _57_1081 = (check_n env arg)
in (match (_57_1081) with
| (_57_1078, s_arg, u_arg) -> begin
(let _152_866 = if (is_C bv.FStar_Syntax_Syntax.sort) then begin
(let _152_865 = (let _152_864 = (FStar_Syntax_Subst.subst env.subst s_arg)
in ((_152_864), (q)))
in (_152_865)::(((u_arg), (q)))::[])
end else begin
(((u_arg), (q)))::[]
end
in ((((s_arg), (q))), (_152_866)))
end))
end)
end)) binders args)
in (FStar_List.split _152_867))
in (match (_57_1084) with
| (s_args, u_args) -> begin
(

let u_args = (FStar_List.flatten u_args)
in (let _152_869 = (mk (FStar_Syntax_Syntax.Tm_app (((s_head), (s_args)))))
in (let _152_868 = (mk (FStar_Syntax_Syntax.Tm_app (((u_head), (u_args)))))
in ((final_type), (_152_869), (_152_868)))))
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
(let _152_871 = (let _152_870 = (env.tc_const c)
in N (_152_870))
in ((_152_871), (e), (e)))
end
| FStar_Syntax_Syntax.Tm_let (_57_1115) -> begin
(let _152_873 = (let _152_872 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_let %s" _152_872))
in (FStar_All.failwith _152_873))
end
| FStar_Syntax_Syntax.Tm_type (_57_1118) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_1121) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_57_1124) -> begin
(let _152_875 = (let _152_874 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_refine %s" _152_874))
in (FStar_All.failwith _152_875))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_1127) -> begin
(let _152_877 = (let _152_876 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_uvar %s" _152_876))
in (FStar_All.failwith _152_877))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_1130) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _152_882 = (let _152_881 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_unknown %s" _152_881))
in (FStar_All.failwith _152_882))
end))))
and mk_match : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e0 branches f -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e0.FStar_Syntax_Syntax.pos))
in (

let _57_1143 = (check_n env e0)
in (match (_57_1143) with
| (_57_1140, s_e0, u_e0) -> begin
(

let _57_1160 = (let _152_898 = (FStar_List.map (fun b -> (match ((FStar_Syntax_Subst.open_branch b)) with
| (pat, None, body) -> begin
(

let env = (

let _57_1149 = env
in (let _152_897 = (let _152_896 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env.env _152_896))
in {env = _152_897; subst = _57_1149.subst; tc_const = _57_1149.tc_const}))
in (

let _57_1155 = (f env body)
in (match (_57_1155) with
| (nm, s_body, u_body) -> begin
((nm), (((pat), (None), (((s_body), (u_body), (body))))))
end)))
end
| _57_1157 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("No when clauses in the definition language")))
end)) branches)
in (FStar_List.split _152_898))
in (match (_57_1160) with
| (nms, branches) -> begin
(

let t1 = (match ((FStar_List.hd nms)) with
| (M (t1)) | (N (t1)) -> begin
t1
end)
in (

let has_m = (FStar_List.existsb (fun _57_12 -> (match (_57_12) with
| M (_57_1167) -> begin
true
end
| _57_1170 -> begin
false
end)) nms)
in (

let _57_1204 = (let _152_902 = (FStar_List.map2 (fun nm _57_1179 -> (match (_57_1179) with
| (pat, guard, (s_body, u_body, original_body)) -> begin
(match (((nm), (has_m))) with
| ((N (t2), false)) | ((M (t2), true)) -> begin
((nm), (((pat), (guard), (s_body))), (((pat), (guard), (u_body))))
end
| (N (t2), true) -> begin
(

let _57_1195 = (check env original_body (M (t2)))
in (match (_57_1195) with
| (_57_1192, s_body, u_body) -> begin
((M (t2)), (((pat), (guard), (s_body))), (((pat), (guard), (u_body))))
end))
end
| (M (_57_1197), false) -> begin
(FStar_All.failwith "impossible")
end)
end)) nms branches)
in (FStar_List.unzip3 _152_902))
in (match (_57_1204) with
| (nms, s_branches, u_branches) -> begin
if has_m then begin
(

let p_type = (mk_star_to_type mk env t1)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" None p_type)
in (

let s_branches = (FStar_List.map (fun _57_1210 -> (match (_57_1210) with
| (pat, guard, s_body) -> begin
(

let s_body = (let _152_909 = (let _152_908 = (let _152_907 = (let _152_906 = (let _152_905 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _152_904 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_905), (_152_904))))
in (_152_906)::[])
in ((s_body), (_152_907)))
in FStar_Syntax_Syntax.Tm_app (_152_908))
in (mk _152_909))
in ((pat), (guard), (s_body)))
end)) s_branches)
in (

let s_branches = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let s_e = (let _152_912 = (let _152_910 = (FStar_Syntax_Syntax.mk_binder p)
in (_152_910)::[])
in (let _152_911 = (mk (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches)))))
in (FStar_Syntax_Util.abs _152_912 _152_911 None)))
in (

let t1_star = (let _152_916 = (let _152_914 = (let _152_913 = (FStar_Syntax_Syntax.new_bv None p_type)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _152_913))
in (_152_914)::[])
in (let _152_915 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _152_916 _152_915)))
in (let _152_918 = (mk (FStar_Syntax_Syntax.Tm_ascribed (((s_e), (FStar_Util.Inl (t1_star)), (None)))))
in (let _152_917 = (mk (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches)))))
in ((M (t1)), (_152_918), (_152_917)))))))))))
end else begin
(

let s_branches = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let t1_star = t1
in (let _152_923 = (let _152_921 = (let _152_920 = (let _152_919 = (mk (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches)))))
in ((_152_919), (FStar_Util.Inl (t1_star)), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (_152_920))
in (mk _152_921))
in (let _152_922 = (mk (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches)))))
in ((N (t1)), (_152_923), (_152_922)))))))
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

let x_binders = (let _152_943 = (FStar_Syntax_Syntax.mk_binder x)
in (_152_943)::[])
in (

let _57_1232 = (FStar_Syntax_Subst.open_term x_binders e2)
in (match (_57_1232) with
| (x_binders, e2) -> begin
(match ((infer env e1)) with
| (N (t1), s_e1, u_e1) -> begin
(

let u_binding = if (is_C t1) then begin
(

let _57_1238 = binding
in (let _152_945 = (let _152_944 = (FStar_Syntax_Subst.subst env.subst s_e1)
in (trans_F_ env t1 _152_944))
in {FStar_Syntax_Syntax.lbname = _57_1238.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_1238.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _152_945; FStar_Syntax_Syntax.lbeff = _57_1238.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _57_1238.FStar_Syntax_Syntax.lbdef}))
end else begin
binding
end
in (

let env = (

let _57_1241 = env
in (let _152_946 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_1243 = x
in {FStar_Syntax_Syntax.ppname = _57_1243.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1243.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _152_946; subst = _57_1241.subst; tc_const = _57_1241.tc_const}))
in (

let _57_1249 = (proceed env e2)
in (match (_57_1249) with
| (nm_rec, s_e2, u_e2) -> begin
(

let s_binding = (

let _57_1250 = binding
in (let _152_947 = (star_type' env binding.FStar_Syntax_Syntax.lbtyp)
in {FStar_Syntax_Syntax.lbname = _57_1250.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_1250.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _152_947; FStar_Syntax_Syntax.lbeff = _57_1250.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _57_1250.FStar_Syntax_Syntax.lbdef}))
in (let _152_955 = (let _152_950 = (let _152_949 = (let _152_948 = (FStar_Syntax_Subst.close x_binders s_e2)
in ((((false), (((

let _57_1253 = s_binding
in {FStar_Syntax_Syntax.lbname = _57_1253.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_1253.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1253.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1253.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = s_e1}))::[]))), (_152_948)))
in FStar_Syntax_Syntax.Tm_let (_152_949))
in (mk _152_950))
in (let _152_954 = (let _152_953 = (let _152_952 = (let _152_951 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _57_1255 = u_binding
in {FStar_Syntax_Syntax.lbname = _57_1255.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_1255.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1255.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1255.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_152_951)))
in FStar_Syntax_Syntax.Tm_let (_152_952))
in (mk _152_953))
in ((nm_rec), (_152_955), (_152_954)))))
end))))
end
| (M (t1), s_e1, u_e1) -> begin
(

let u_binding = (

let _57_1262 = binding
in {FStar_Syntax_Syntax.lbname = _57_1262.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_1262.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.lbdef = _57_1262.FStar_Syntax_Syntax.lbdef})
in (

let env = (

let _57_1265 = env
in (let _152_956 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_1267 = x
in {FStar_Syntax_Syntax.ppname = _57_1267.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1267.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _152_956; subst = _57_1265.subst; tc_const = _57_1265.tc_const}))
in (

let _57_1273 = (ensure_m env e2)
in (match (_57_1273) with
| (t2, s_e2, u_e2) -> begin
(

let p_type = (mk_star_to_type mk env t2)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" None p_type)
in (

let s_e2 = (let _152_962 = (let _152_961 = (let _152_960 = (let _152_959 = (let _152_958 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _152_957 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_958), (_152_957))))
in (_152_959)::[])
in ((s_e2), (_152_960)))
in FStar_Syntax_Syntax.Tm_app (_152_961))
in (mk _152_962))
in (

let s_e2 = (FStar_Syntax_Util.abs x_binders s_e2 None)
in (

let body = (let _152_967 = (let _152_966 = (let _152_965 = (let _152_964 = (let _152_963 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_e2), (_152_963)))
in (_152_964)::[])
in ((s_e1), (_152_965)))
in FStar_Syntax_Syntax.Tm_app (_152_966))
in (mk _152_967))
in (let _152_974 = (let _152_969 = (let _152_968 = (FStar_Syntax_Syntax.mk_binder p)
in (_152_968)::[])
in (FStar_Syntax_Util.abs _152_969 body None))
in (let _152_973 = (let _152_972 = (let _152_971 = (let _152_970 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _57_1279 = u_binding
in {FStar_Syntax_Syntax.lbname = _57_1279.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_1279.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1279.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1279.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_152_970)))
in FStar_Syntax_Syntax.Tm_let (_152_971))
in (mk _152_972))
in ((M (t2)), (_152_974), (_152_973)))))))))
end))))
end)
end)))))))
and check_n : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _152_977 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in N (_152_977))
in (match ((check env e mn)) with
| (N (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_1290 -> begin
(FStar_All.failwith "[check_n]: impossible")
end)))
and check_m : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _152_980 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in M (_152_980))
in (match ((check env e mn)) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_1300 -> begin
(FStar_All.failwith "[check_m]: impossible")
end)))
and comp_of_nm : nm_  ->  FStar_Syntax_Syntax.comp = (fun nm -> (match (nm) with
| N (t) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| M (t) -> begin
(mk_M t)
end))
and mk_M : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun t -> (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_unknown)::[]; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.monadic_lid; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.CPS)::(FStar_Syntax_Syntax.TOTAL)::[]}))
and type_of_comp : (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.typ = (fun t -> (FStar_Syntax_Util.comp_result t))
and trans_F_ : env_  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> (

let _57_1311 = if (not ((is_C c))) then begin
(FStar_All.failwith "not a C")
end else begin
()
end
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos))
in (match ((let _152_989 = (FStar_Syntax_Subst.compress c)
in _152_989.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_1321 = (FStar_Syntax_Util.head_and_args wp)
in (match (_57_1321) with
| (wp_head, wp_args) -> begin
(

let _57_1322 = if ((not (((FStar_List.length wp_args) = (FStar_List.length args)))) || (not ((let _152_990 = (FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length wp_args) FStar_Range.dummyRange)
in (FStar_Syntax_Util.is_constructor wp_head _152_990))))) then begin
(FStar_All.failwith "mismatch")
end else begin
()
end
in (let _152_1000 = (let _152_999 = (let _152_998 = (FStar_List.map2 (fun _57_1326 _57_1329 -> (match (((_57_1326), (_57_1329))) with
| ((arg, q), (wp_arg, q')) -> begin
(

let print_implicit = (fun q -> if (FStar_Syntax_Syntax.is_implicit q) then begin
"implicit"
end else begin
"explicit"
end)
in (

let _57_1332 = if (q <> q') then begin
(let _152_996 = (print_implicit q)
in (let _152_995 = (print_implicit q')
in (FStar_Util.print2_warning "Incoherent implicit qualifiers %b %b" _152_996 _152_995)))
end else begin
()
end
in (let _152_997 = (trans_F_ env arg wp_arg)
in ((_152_997), (q)))))
end)) args wp_args)
in ((head), (_152_998)))
in FStar_Syntax_Syntax.Tm_app (_152_999))
in (mk _152_1000)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let binders = (FStar_Syntax_Util.name_binders binders)
in (

let _57_1341 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (_57_1341) with
| (binders_orig, comp) -> begin
(

let _57_1350 = (let _152_1010 = (FStar_List.map (fun _57_1344 -> (match (_57_1344) with
| (bv, q) -> begin
(

let h = bv.FStar_Syntax_Syntax.sort
in if (is_C h) then begin
(

let w' = (let _152_1002 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-w\'") None _152_1002))
in (let _152_1008 = (let _152_1007 = (let _152_1006 = (let _152_1005 = (let _152_1004 = (let _152_1003 = (FStar_Syntax_Syntax.bv_to_name w')
in (trans_F_ env h _152_1003))
in (FStar_Syntax_Syntax.null_bv _152_1004))
in ((_152_1005), (q)))
in (_152_1006)::[])
in (((w'), (q)))::_152_1007)
in ((w'), (_152_1008))))
end else begin
(

let x = (let _152_1009 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-x") None _152_1009))
in ((x), ((((x), (q)))::[])))
end)
end)) binders_orig)
in (FStar_List.split _152_1010))
in (match (_57_1350) with
| (bvs, binders) -> begin
(

let binders = (FStar_List.flatten binders)
in (

let comp = (let _152_1012 = (let _152_1011 = (FStar_Syntax_Syntax.binders_of_list bvs)
in (FStar_Syntax_Util.rename_binders binders_orig _152_1011))
in (FStar_Syntax_Subst.subst_comp _152_1012 comp))
in (

let app = (let _152_1018 = (let _152_1017 = (let _152_1016 = (FStar_List.map (fun bv -> (let _152_1015 = (FStar_Syntax_Syntax.bv_to_name bv)
in (let _152_1014 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_1015), (_152_1014))))) bvs)
in ((wp), (_152_1016)))
in FStar_Syntax_Syntax.Tm_app (_152_1017))
in (mk _152_1018))
in (

let comp = (let _152_1020 = (type_of_comp comp)
in (let _152_1019 = (is_monadic_comp comp)
in (trans_G env _152_1020 _152_1019 app)))
in (FStar_Syntax_Util.arrow binders comp)))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, _57_1358, _57_1360) -> begin
(trans_F_ env e wp)
end
| _57_1364 -> begin
(FStar_All.failwith "impossible trans_F_")
end))))
and trans_G : env_  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env h is_monadic wp -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None h.FStar_Syntax_Syntax.pos))
in if is_monadic then begin
(let _152_1031 = (let _152_1030 = (star_type' env h)
in (let _152_1029 = (let _152_1028 = (let _152_1027 = (FStar_Syntax_Syntax.as_implicit false)
in ((wp), (_152_1027)))
in (_152_1028)::[])
in {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_unknown)::[]; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _152_1030; FStar_Syntax_Syntax.effect_args = _152_1029; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp _152_1031))
end else begin
(let _152_1032 = (trans_F_ env h wp)
in (FStar_Syntax_Syntax.mk_Total _152_1032))
end))


let n : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]))


let star_type : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _152_1039 = (n env.env t)
in (star_type' env _152_1039)))


let star_expr : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env t -> (let _152_1044 = (n env.env t)
in (check_n env _152_1044)))


let trans_F : env_  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> (let _152_1052 = (n env.env c)
in (let _152_1051 = (n env.env wp)
in (trans_F_ env _152_1052 _152_1051))))




