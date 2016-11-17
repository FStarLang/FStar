
open Prims

let gen_wps_for_free : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.sigelts * FStar_Syntax_Syntax.eff_decl) = (fun env binders a wp_a ed -> (

let wp_a = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env wp_a)
in (

let a = (

let _58_13 = a
in (let _155_11 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env a.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _58_13.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_13.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _155_11}))
in (

let d = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))
in (

let _58_20 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _58_18 = (d "Elaborating extra WP combinators")
in (let _155_14 = (FStar_Syntax_Print.term_to_string wp_a)
in (FStar_Util.print1 "wp_a is: %s\n" _155_14)))
end else begin
()
end
in (

let rec collect_binders = (fun t -> (match ((let _155_18 = (let _155_17 = (FStar_Syntax_Subst.compress t)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe _155_17))
in _155_18.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let rest = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _58_30) -> begin
t
end
| _58_34 -> begin
(FStar_All.failwith "wp_a contains non-Tot arrow")
end)
in (let _155_19 = (collect_binders rest)
in (FStar_List.append bs _155_19)))
end
| FStar_Syntax_Syntax.Tm_type (_58_37) -> begin
[]
end
| _58_40 -> begin
(FStar_All.failwith "wp_a doesn\'t end in Type0")
end))
in (

let mk_lid = (fun name -> (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" name))) FStar_Range.dummyRange))
in (

let gamma = (let _155_22 = (collect_binders wp_a)
in (FStar_All.pipe_right _155_22 FStar_Syntax_Util.name_binders))
in (

let _58_44 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _155_24 = (let _155_23 = (FStar_Syntax_Print.binders_to_string ", " gamma)
in (FStar_Util.format1 "Gamma is %s\n" _155_23))
in (d _155_24))
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

let _58_56 = (FStar_TypeChecker_Util.mk_toplevel_definition env lident def)
in (match (_58_56) with
| (sigelt, fv) -> begin
(

let _58_57 = (let _155_34 = (let _155_33 = (FStar_ST.read sigelts)
in (sigelt)::_155_33)
in (FStar_ST.op_Colon_Equals sigelts _155_34))
in fv)
end)))
in (

let binders_of_list = (FStar_List.map (fun _58_61 -> (match (_58_61) with
| (t, b) -> begin
(let _155_37 = (FStar_Syntax_Syntax.as_implicit b)
in ((t), (_155_37)))
end)))
in (

let mk_all_implicit = (FStar_List.map (fun t -> (let _155_40 = (FStar_Syntax_Syntax.as_implicit true)
in (((Prims.fst t)), (_155_40)))))
in (

let args_of_binders = (FStar_List.map (fun bv -> (let _155_43 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst bv))
in (FStar_Syntax_Syntax.as_arg _155_43))))
in (

let _58_88 = (

let _58_73 = (

let mk = (fun f -> (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let body = (let _155_56 = (let _155_55 = (FStar_Syntax_Syntax.bv_to_name t)
in (f _155_55))
in (FStar_Syntax_Util.arrow gamma _155_56))
in (let _155_61 = (let _155_60 = (let _155_59 = (FStar_Syntax_Syntax.mk_binder a)
in (let _155_58 = (let _155_57 = (FStar_Syntax_Syntax.mk_binder t)
in (_155_57)::[])
in (_155_59)::_155_58))
in (FStar_List.append binders _155_60))
in (FStar_Syntax_Util.abs _155_61 body None)))))
in (let _155_63 = (mk FStar_Syntax_Syntax.mk_Total)
in (let _155_62 = (mk FStar_Syntax_Syntax.mk_GTotal)
in ((_155_63), (_155_62)))))
in (match (_58_73) with
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

let mk_app = (fun fv t -> (let _155_85 = (let _155_84 = (let _155_83 = (let _155_82 = (FStar_List.map (fun _58_84 -> (match (_58_84) with
| (bv, _58_83) -> begin
(let _155_74 = (FStar_Syntax_Syntax.bv_to_name bv)
in (let _155_73 = (FStar_Syntax_Syntax.as_implicit false)
in ((_155_74), (_155_73))))
end)) binders)
in (let _155_81 = (let _155_80 = (let _155_76 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _155_75 = (FStar_Syntax_Syntax.as_implicit false)
in ((_155_76), (_155_75))))
in (let _155_79 = (let _155_78 = (let _155_77 = (FStar_Syntax_Syntax.as_implicit false)
in ((t), (_155_77)))
in (_155_78)::[])
in (_155_80)::_155_79))
in (FStar_List.append _155_82 _155_81)))
in ((fv), (_155_83)))
in FStar_Syntax_Syntax.Tm_app (_155_84))
in (mk _155_85)))
in ((env), ((mk_app ctx_fv)), ((mk_app gctx_fv))))))))
end))
in (match (_58_88) with
| (env, mk_ctx, mk_gctx) -> begin
(

let c_pure = (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let x = (let _155_90 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" None _155_90))
in (

let ret = (let _155_95 = (let _155_94 = (let _155_93 = (let _155_92 = (let _155_91 = (FStar_Syntax_Syntax.bv_to_name t)
in (mk_ctx _155_91))
in (FStar_Syntax_Syntax.mk_Total _155_92))
in (FStar_Syntax_Util.lcomp_of_comp _155_93))
in FStar_Util.Inl (_155_94))
in Some (_155_95))
in (

let body = (let _155_96 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs gamma _155_96 ret))
in (let _155_99 = (let _155_98 = (mk_all_implicit binders)
in (let _155_97 = (binders_of_list ((((a), (true)))::(((t), (true)))::(((x), (false)))::[]))
in (FStar_List.append _155_98 _155_97)))
in (FStar_Syntax_Util.abs _155_99 body ret))))))
in (

let c_pure = (let _155_100 = (mk_lid "pure")
in (register env _155_100 c_pure))
in (

let c_app = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let l = (let _155_108 = (let _155_107 = (let _155_106 = (let _155_103 = (let _155_102 = (let _155_101 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv None _155_101))
in (FStar_Syntax_Syntax.mk_binder _155_102))
in (_155_103)::[])
in (let _155_105 = (let _155_104 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _155_104))
in (FStar_Syntax_Util.arrow _155_106 _155_105)))
in (mk_gctx _155_107))
in (FStar_Syntax_Syntax.gen_bv "l" None _155_108))
in (

let r = (let _155_110 = (let _155_109 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _155_109))
in (FStar_Syntax_Syntax.gen_bv "r" None _155_110))
in (

let ret = (let _155_115 = (let _155_114 = (let _155_113 = (let _155_112 = (let _155_111 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _155_111))
in (FStar_Syntax_Syntax.mk_Total _155_112))
in (FStar_Syntax_Util.lcomp_of_comp _155_113))
in FStar_Util.Inl (_155_114))
in Some (_155_115))
in (

let outer_body = (

let gamma_as_args = (args_of_binders gamma)
in (

let inner_body = (let _155_121 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _155_120 = (let _155_119 = (let _155_118 = (let _155_117 = (let _155_116 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app _155_116 gamma_as_args))
in (FStar_Syntax_Syntax.as_arg _155_117))
in (_155_118)::[])
in (FStar_List.append gamma_as_args _155_119))
in (FStar_Syntax_Util.mk_app _155_121 _155_120)))
in (FStar_Syntax_Util.abs gamma inner_body ret)))
in (let _155_124 = (let _155_123 = (mk_all_implicit binders)
in (let _155_122 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((l), (false)))::(((r), (false)))::[]))
in (FStar_List.append _155_123 _155_122)))
in (FStar_Syntax_Util.abs _155_124 outer_body ret))))))))
in (

let c_app = (let _155_125 = (mk_lid "app")
in (register env _155_125 c_app))
in (

let c_lift1 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _155_130 = (let _155_127 = (let _155_126 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _155_126))
in (_155_127)::[])
in (let _155_129 = (let _155_128 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _155_128))
in (FStar_Syntax_Util.arrow _155_130 _155_129)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _155_132 = (let _155_131 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _155_131))
in (FStar_Syntax_Syntax.gen_bv "a1" None _155_132))
in (

let ret = (let _155_137 = (let _155_136 = (let _155_135 = (let _155_134 = (let _155_133 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _155_133))
in (FStar_Syntax_Syntax.mk_Total _155_134))
in (FStar_Syntax_Util.lcomp_of_comp _155_135))
in FStar_Util.Inl (_155_136))
in Some (_155_137))
in (let _155_149 = (let _155_139 = (mk_all_implicit binders)
in (let _155_138 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::(((a1), (false)))::[]))
in (FStar_List.append _155_139 _155_138)))
in (let _155_148 = (let _155_147 = (let _155_146 = (let _155_145 = (let _155_142 = (let _155_141 = (let _155_140 = (FStar_Syntax_Syntax.bv_to_name f)
in (_155_140)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _155_141))
in (FStar_Syntax_Util.mk_app c_pure _155_142))
in (let _155_144 = (let _155_143 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_155_143)::[])
in (_155_145)::_155_144))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _155_146))
in (FStar_Syntax_Util.mk_app c_app _155_147))
in (FStar_Syntax_Util.abs _155_149 _155_148 ret)))))))))
in (

let c_lift1 = (let _155_150 = (mk_lid "lift1")
in (register env _155_150 c_lift1))
in (

let c_lift2 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t3 = (FStar_Syntax_Syntax.gen_bv "t3" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _155_158 = (let _155_155 = (let _155_151 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _155_151))
in (let _155_154 = (let _155_153 = (let _155_152 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.null_binder _155_152))
in (_155_153)::[])
in (_155_155)::_155_154))
in (let _155_157 = (let _155_156 = (FStar_Syntax_Syntax.bv_to_name t3)
in (FStar_Syntax_Syntax.mk_GTotal _155_156))
in (FStar_Syntax_Util.arrow _155_158 _155_157)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _155_160 = (let _155_159 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _155_159))
in (FStar_Syntax_Syntax.gen_bv "a1" None _155_160))
in (

let a2 = (let _155_162 = (let _155_161 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _155_161))
in (FStar_Syntax_Syntax.gen_bv "a2" None _155_162))
in (

let ret = (let _155_167 = (let _155_166 = (let _155_165 = (let _155_164 = (let _155_163 = (FStar_Syntax_Syntax.bv_to_name t3)
in (mk_gctx _155_163))
in (FStar_Syntax_Syntax.mk_Total _155_164))
in (FStar_Syntax_Util.lcomp_of_comp _155_165))
in FStar_Util.Inl (_155_166))
in Some (_155_167))
in (let _155_184 = (let _155_169 = (mk_all_implicit binders)
in (let _155_168 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((t3), (true)))::(((f), (false)))::(((a1), (false)))::(((a2), (false)))::[]))
in (FStar_List.append _155_169 _155_168)))
in (let _155_183 = (let _155_182 = (let _155_181 = (let _155_180 = (let _155_177 = (let _155_176 = (let _155_175 = (let _155_172 = (let _155_171 = (let _155_170 = (FStar_Syntax_Syntax.bv_to_name f)
in (_155_170)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _155_171))
in (FStar_Syntax_Util.mk_app c_pure _155_172))
in (let _155_174 = (let _155_173 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_155_173)::[])
in (_155_175)::_155_174))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _155_176))
in (FStar_Syntax_Util.mk_app c_app _155_177))
in (let _155_179 = (let _155_178 = (FStar_Syntax_Syntax.bv_to_name a2)
in (_155_178)::[])
in (_155_180)::_155_179))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _155_181))
in (FStar_Syntax_Util.mk_app c_app _155_182))
in (FStar_Syntax_Util.abs _155_184 _155_183 ret)))))))))))
in (

let c_lift2 = (let _155_185 = (mk_lid "lift2")
in (register env _155_185 c_lift2))
in (

let c_push = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _155_191 = (let _155_187 = (let _155_186 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _155_186))
in (_155_187)::[])
in (let _155_190 = (let _155_189 = (let _155_188 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _155_188))
in (FStar_Syntax_Syntax.mk_Total _155_189))
in (FStar_Syntax_Util.arrow _155_191 _155_190)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let ret = (let _155_201 = (let _155_200 = (let _155_199 = (let _155_198 = (let _155_197 = (let _155_196 = (let _155_193 = (let _155_192 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _155_192))
in (_155_193)::[])
in (let _155_195 = (let _155_194 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _155_194))
in (FStar_Syntax_Util.arrow _155_196 _155_195)))
in (mk_ctx _155_197))
in (FStar_Syntax_Syntax.mk_Total _155_198))
in (FStar_Syntax_Util.lcomp_of_comp _155_199))
in FStar_Util.Inl (_155_200))
in Some (_155_201))
in (

let e1 = (let _155_202 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" None _155_202))
in (

let body = (let _155_211 = (let _155_204 = (let _155_203 = (FStar_Syntax_Syntax.mk_binder e1)
in (_155_203)::[])
in (FStar_List.append gamma _155_204))
in (let _155_210 = (let _155_209 = (FStar_Syntax_Syntax.bv_to_name f)
in (let _155_208 = (let _155_207 = (let _155_205 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg _155_205))
in (let _155_206 = (args_of_binders gamma)
in (_155_207)::_155_206))
in (FStar_Syntax_Util.mk_app _155_209 _155_208)))
in (FStar_Syntax_Util.abs _155_211 _155_210 ret)))
in (let _155_214 = (let _155_213 = (mk_all_implicit binders)
in (let _155_212 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::[]))
in (FStar_List.append _155_213 _155_212)))
in (FStar_Syntax_Util.abs _155_214 body ret)))))))))
in (

let c_push = (let _155_215 = (mk_lid "push")
in (register env _155_215 c_push))
in (

let ret_tot_wp_a = (let _155_218 = (let _155_217 = (let _155_216 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.lcomp_of_comp _155_216))
in FStar_Util.Inl (_155_217))
in Some (_155_218))
in (

let mk_generic_app = (fun c -> if ((FStar_List.length binders) > (Prims.parse_int "0")) then begin
(let _155_223 = (let _155_222 = (let _155_221 = (args_of_binders binders)
in ((c), (_155_221)))
in FStar_Syntax_Syntax.Tm_app (_155_222))
in (mk _155_223))
end else begin
c
end)
in (

let wp_if_then_else = (

let result_comp = (let _155_229 = (let _155_228 = (let _155_226 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _155_225 = (let _155_224 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_155_224)::[])
in (_155_226)::_155_225))
in (let _155_227 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _155_228 _155_227)))
in (FStar_Syntax_Syntax.mk_Total _155_229))
in (

let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (let _155_239 = (let _155_230 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (FStar_List.append binders _155_230))
in (let _155_238 = (

let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "2"))) None)
in (let _155_237 = (let _155_236 = (let _155_235 = (let _155_234 = (let _155_233 = (let _155_232 = (let _155_231 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg _155_231))
in (_155_232)::[])
in (FStar_Syntax_Util.mk_app l_ite _155_233))
in (_155_234)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _155_235))
in (FStar_Syntax_Util.mk_app c_lift2 _155_236))
in (FStar_Syntax_Util.ascribe _155_237 (FStar_Util.Inr (result_comp)))))
in (FStar_Syntax_Util.abs _155_239 _155_238 (Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp result_comp)))))))))
in (

let wp_if_then_else = (let _155_240 = (mk_lid "wp_if_then_else")
in (register env _155_240 wp_if_then_else))
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

let body = (let _155_251 = (let _155_250 = (let _155_249 = (let _155_246 = (let _155_245 = (let _155_244 = (let _155_243 = (let _155_242 = (let _155_241 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _155_241))
in (_155_242)::[])
in (FStar_Syntax_Util.mk_app l_and _155_243))
in (_155_244)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _155_245))
in (FStar_Syntax_Util.mk_app c_pure _155_246))
in (let _155_248 = (let _155_247 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_155_247)::[])
in (_155_249)::_155_248))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _155_250))
in (FStar_Syntax_Util.mk_app c_app _155_251))
in (let _155_253 = (let _155_252 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders _155_252))
in (FStar_Syntax_Util.abs _155_253 body ret_tot_wp_a))))))
in (

let wp_assert = (let _155_254 = (mk_lid "wp_assert")
in (register env _155_254 wp_assert))
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

let body = (let _155_265 = (let _155_264 = (let _155_263 = (let _155_260 = (let _155_259 = (let _155_258 = (let _155_257 = (let _155_256 = (let _155_255 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _155_255))
in (_155_256)::[])
in (FStar_Syntax_Util.mk_app l_imp _155_257))
in (_155_258)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _155_259))
in (FStar_Syntax_Util.mk_app c_pure _155_260))
in (let _155_262 = (let _155_261 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_155_261)::[])
in (_155_263)::_155_262))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _155_264))
in (FStar_Syntax_Util.mk_app c_app _155_265))
in (let _155_267 = (let _155_266 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders _155_266))
in (FStar_Syntax_Util.abs _155_267 body ret_tot_wp_a))))))
in (

let wp_assume = (let _155_268 = (mk_lid "wp_assume")
in (register env _155_268 wp_assume))
in (

let wp_assume = (mk_generic_app wp_assume)
in (

let wp_close = (

let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _155_272 = (let _155_270 = (let _155_269 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _155_269))
in (_155_270)::[])
in (let _155_271 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _155_272 _155_271)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let body = (let _155_281 = (let _155_280 = (let _155_279 = (let _155_273 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((FStar_Syntax_Util.tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure _155_273))
in (let _155_278 = (let _155_277 = (let _155_276 = (let _155_275 = (let _155_274 = (FStar_Syntax_Syntax.bv_to_name f)
in (_155_274)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _155_275))
in (FStar_Syntax_Util.mk_app c_push _155_276))
in (_155_277)::[])
in (_155_279)::_155_278))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _155_280))
in (FStar_Syntax_Util.mk_app c_app _155_281))
in (let _155_283 = (let _155_282 = (FStar_Syntax_Syntax.binders_of_list ((a)::(b)::(f)::[]))
in (FStar_List.append binders _155_282))
in (FStar_Syntax_Util.abs _155_283 body ret_tot_wp_a))))))
in (

let wp_close = (let _155_284 = (mk_lid "wp_close")
in (register env _155_284 wp_close))
in (

let wp_close = (mk_generic_app wp_close)
in (

let ret_tot_type = (let _155_287 = (let _155_286 = (let _155_285 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _155_285))
in FStar_Util.Inl (_155_286))
in Some (_155_287))
in (

let ret_gtot_type = (let _155_290 = (let _155_289 = (let _155_288 = (FStar_Syntax_Syntax.mk_GTotal FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _155_288))
in FStar_Util.Inl (_155_289))
in Some (_155_290))
in (

let mk_forall = (fun x body -> (let _155_301 = (let _155_300 = (let _155_299 = (let _155_298 = (let _155_297 = (let _155_296 = (let _155_295 = (FStar_Syntax_Syntax.mk_binder x)
in (_155_295)::[])
in (FStar_Syntax_Util.abs _155_296 body ret_tot_type))
in (FStar_Syntax_Syntax.as_arg _155_297))
in (_155_298)::[])
in ((FStar_Syntax_Util.tforall), (_155_299)))
in FStar_Syntax_Syntax.Tm_app (_155_300))
in (FStar_Syntax_Syntax.mk _155_301 None FStar_Range.dummyRange)))
in (

let rec is_discrete = (fun t -> (match ((let _155_304 = (FStar_Syntax_Subst.compress t)
in _155_304.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_58_170) -> begin
false
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((FStar_List.for_all (fun _58_179 -> (match (_58_179) with
| (b, _58_178) -> begin
(is_discrete b.FStar_Syntax_Syntax.sort)
end)) bs) && (is_discrete (FStar_Syntax_Util.comp_result c)))
end
| _58_181 -> begin
true
end))
in (

let rec is_monotonic = (fun t -> (match ((let _155_308 = (FStar_Syntax_Subst.compress t)
in _155_308.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_58_185) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((FStar_List.for_all (fun _58_194 -> (match (_58_194) with
| (b, _58_193) -> begin
(is_discrete b.FStar_Syntax_Syntax.sort)
end)) bs) && (is_monotonic (FStar_Syntax_Util.comp_result c)))
end
| _58_196 -> begin
(is_discrete t)
end))
in (

let rec mk_rel = (fun rel t x y -> (

let mk_rel = (mk_rel rel)
in (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (match ((let _155_331 = (FStar_Syntax_Subst.compress t)
in _155_331.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_58_205) -> begin
(rel x y)
end
| (FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(

let a = (Prims.fst binder).FStar_Syntax_Syntax.sort
in if ((is_monotonic a) || (is_monotonic b)) then begin
(

let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (

let body = (let _155_339 = (let _155_334 = (let _155_333 = (let _155_332 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _155_332))
in (_155_333)::[])
in (FStar_Syntax_Util.mk_app x _155_334))
in (let _155_338 = (let _155_337 = (let _155_336 = (let _155_335 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _155_335))
in (_155_336)::[])
in (FStar_Syntax_Util.mk_app y _155_337))
in (mk_rel b _155_339 _155_338)))
in (mk_forall a1 body)))
end else begin
(

let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (

let a2 = (FStar_Syntax_Syntax.gen_bv "a2" None a)
in (

let body = (let _155_351 = (let _155_341 = (FStar_Syntax_Syntax.bv_to_name a1)
in (let _155_340 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_rel a _155_341 _155_340)))
in (let _155_350 = (let _155_349 = (let _155_344 = (let _155_343 = (let _155_342 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _155_342))
in (_155_343)::[])
in (FStar_Syntax_Util.mk_app x _155_344))
in (let _155_348 = (let _155_347 = (let _155_346 = (let _155_345 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg _155_345))
in (_155_346)::[])
in (FStar_Syntax_Util.mk_app y _155_347))
in (mk_rel b _155_349 _155_348)))
in (FStar_Syntax_Util.mk_imp _155_351 _155_350)))
in (let _155_352 = (mk_forall a2 body)
in (mk_forall a1 _155_352)))))
end)
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::binders, comp) -> begin
(

let t = (

let _58_249 = t
in (let _155_356 = (let _155_355 = (let _155_354 = (let _155_353 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _155_353))
in (((binder)::[]), (_155_354)))
in FStar_Syntax_Syntax.Tm_arrow (_155_355))
in {FStar_Syntax_Syntax.n = _155_356; FStar_Syntax_Syntax.tk = _58_249.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _58_249.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_249.FStar_Syntax_Syntax.vars}))
in (mk_rel t x y))
end
| FStar_Syntax_Syntax.Tm_arrow (_58_253) -> begin
(FStar_All.failwith "unhandled arrow")
end
| _58_256 -> begin
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
in (match ((let _155_363 = (FStar_Syntax_Subst.compress t)
in _155_363.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_58_265) -> begin
(FStar_Syntax_Util.mk_imp x y)
end
| FStar_Syntax_Syntax.Tm_app (head, args) when (let _155_364 = (FStar_Syntax_Subst.compress head)
in (FStar_Syntax_Util.is_tuple_constructor _155_364)) -> begin
(

let project = (fun i tuple -> (

let projector = (let _155_370 = (let _155_369 = (FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) FStar_Range.dummyRange)
in (FStar_TypeChecker_Env.lookup_projector env _155_369 i))
in (FStar_Syntax_Syntax.fvar _155_370 (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None))
in (FStar_Syntax_Util.mk_app projector ((((tuple), (None)))::[]))))
in (

let _58_281 = (FStar_List.mapi (fun i _58_278 -> (match (_58_278) with
| (t, q) -> begin
(let _155_374 = (project i x)
in (let _155_373 = (project i y)
in (mk_stronger t _155_374 _155_373)))
end)) args)
in (match (_58_281) with
| (rel0)::rels -> begin
(FStar_List.fold_left FStar_Syntax_Util.mk_conj rel0 rels)
end)))
end
| (FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(

let bvs = (FStar_List.mapi (fun i _58_313 -> (match (_58_313) with
| (bv, q) -> begin
(let _155_378 = (let _155_377 = (FStar_Util.string_of_int i)
in (Prims.strcat "a" _155_377))
in (FStar_Syntax_Syntax.gen_bv _155_378 None bv.FStar_Syntax_Syntax.sort))
end)) binders)
in (

let args = (FStar_List.map (fun ai -> (let _155_380 = (FStar_Syntax_Syntax.bv_to_name ai)
in (FStar_Syntax_Syntax.as_arg _155_380))) bvs)
in (

let body = (let _155_382 = (FStar_Syntax_Util.mk_app x args)
in (let _155_381 = (FStar_Syntax_Util.mk_app y args)
in (mk_stronger b _155_382 _155_381)))
in (FStar_List.fold_right (fun bv body -> (mk_forall bv body)) bvs body))))
end
| _58_321 -> begin
(FStar_All.failwith "Not a DM elaborated type")
end)))
in (

let body = (let _155_387 = (FStar_Syntax_Util.unascribe wp_a)
in (let _155_386 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (let _155_385 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_stronger _155_387 _155_386 _155_385))))
in (let _155_389 = (let _155_388 = (binders_of_list ((((a), (false)))::(((wp1), (false)))::(((wp2), (false)))::[]))
in (FStar_List.append binders _155_388))
in (FStar_Syntax_Util.abs _155_389 body ret_tot_type))))))
in (

let stronger = (let _155_390 = (mk_lid "stronger")
in (register env _155_390 stronger))
in (

let stronger = (mk_generic_app stronger)
in (

let wp_ite = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let _58_329 = (FStar_Util.prefix gamma)
in (match (_58_329) with
| (wp_args, post) -> begin
(

let k = (FStar_Syntax_Syntax.gen_bv "k" None (Prims.fst post).FStar_Syntax_Syntax.sort)
in (

let equiv = (

let k_tm = (FStar_Syntax_Syntax.bv_to_name k)
in (

let eq = (let _155_391 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst post))
in (mk_rel FStar_Syntax_Util.mk_iff k.FStar_Syntax_Syntax.sort k_tm _155_391))
in (match ((FStar_Syntax_Util.destruct_typ_as_formula eq)) with
| Some (FStar_Syntax_Util.QAll (binders, [], body)) -> begin
(

let k_app = (let _155_392 = (args_of_binders binders)
in (FStar_Syntax_Util.mk_app k_tm _155_392))
in (

let guard_free = (let _155_393 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.guard_free FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _155_393))
in (

let pat = (let _155_395 = (let _155_394 = (FStar_Syntax_Syntax.as_arg k_app)
in (_155_394)::[])
in (FStar_Syntax_Util.mk_app guard_free _155_395))
in (

let pattern_guarded_body = (let _155_401 = (let _155_400 = (let _155_399 = (let _155_398 = (let _155_397 = (let _155_396 = (FStar_Syntax_Syntax.as_arg pat)
in (_155_396)::[])
in (_155_397)::[])
in FStar_Syntax_Syntax.Meta_pattern (_155_398))
in ((body), (_155_399)))
in FStar_Syntax_Syntax.Tm_meta (_155_400))
in (mk _155_401))
in (FStar_Syntax_Util.close_forall binders pattern_guarded_body)))))
end
| _58_344 -> begin
(FStar_All.failwith "Impossible: Expected the equivalence to be a quantified formula")
end)))
in (

let body = (let _155_410 = (let _155_409 = (let _155_408 = (let _155_407 = (FStar_Syntax_Syntax.bv_to_name wp)
in (let _155_406 = (let _155_405 = (args_of_binders wp_args)
in (let _155_404 = (let _155_403 = (let _155_402 = (FStar_Syntax_Syntax.bv_to_name k)
in (FStar_Syntax_Syntax.as_arg _155_402))
in (_155_403)::[])
in (FStar_List.append _155_405 _155_404)))
in (FStar_Syntax_Util.mk_app _155_407 _155_406)))
in (FStar_Syntax_Util.mk_imp equiv _155_408))
in (FStar_Syntax_Util.mk_forall k _155_409))
in (FStar_Syntax_Util.abs gamma _155_410 ret_gtot_type))
in (let _155_412 = (let _155_411 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders _155_411))
in (FStar_Syntax_Util.abs _155_412 body ret_gtot_type)))))
end)))
in (

let wp_ite = (let _155_413 = (mk_lid "wp_ite")
in (register env _155_413 wp_ite))
in (

let wp_ite = (mk_generic_app wp_ite)
in (

let null_wp = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let _58_353 = (FStar_Util.prefix gamma)
in (match (_58_353) with
| (wp_args, post) -> begin
(

let x = (FStar_Syntax_Syntax.gen_bv "x" None FStar_Syntax_Syntax.tun)
in (

let body = (let _155_418 = (let _155_417 = (FStar_All.pipe_left FStar_Syntax_Syntax.bv_to_name (Prims.fst post))
in (let _155_416 = (let _155_415 = (let _155_414 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _155_414))
in (_155_415)::[])
in (FStar_Syntax_Util.mk_app _155_417 _155_416)))
in (FStar_Syntax_Util.mk_forall x _155_418))
in (let _155_421 = (let _155_420 = (let _155_419 = (FStar_Syntax_Syntax.binders_of_list ((a)::[]))
in (FStar_List.append _155_419 gamma))
in (FStar_List.append binders _155_420))
in (FStar_Syntax_Util.abs _155_421 body ret_gtot_type))))
end)))
in (

let null_wp = (let _155_422 = (mk_lid "null_wp")
in (register env _155_422 null_wp))
in (

let null_wp = (mk_generic_app null_wp)
in (

let wp_trivial = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let body = (let _155_432 = (let _155_431 = (let _155_430 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _155_429 = (let _155_428 = (let _155_425 = (let _155_424 = (let _155_423 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg _155_423))
in (_155_424)::[])
in (FStar_Syntax_Util.mk_app null_wp _155_425))
in (let _155_427 = (let _155_426 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_155_426)::[])
in (_155_428)::_155_427))
in (_155_430)::_155_429))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _155_431))
in (FStar_Syntax_Util.mk_app stronger _155_432))
in (let _155_434 = (let _155_433 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders _155_433))
in (FStar_Syntax_Util.abs _155_434 body ret_tot_type))))
in (

let wp_trivial = (let _155_435 = (mk_lid "wp_trivial")
in (register env _155_435 wp_trivial))
in (

let wp_trivial = (mk_generic_app wp_trivial)
in (

let _58_364 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(d "End Dijkstra monads for free")
end else begin
()
end
in (

let c = (FStar_Syntax_Subst.close binders)
in (let _155_455 = (let _155_437 = (FStar_ST.read sigelts)
in (FStar_List.rev _155_437))
in (let _155_454 = (

let _58_367 = ed
in (let _155_453 = (let _155_438 = (c wp_if_then_else)
in (([]), (_155_438)))
in (let _155_452 = (let _155_439 = (c wp_ite)
in (([]), (_155_439)))
in (let _155_451 = (let _155_440 = (c stronger)
in (([]), (_155_440)))
in (let _155_450 = (let _155_441 = (c wp_close)
in (([]), (_155_441)))
in (let _155_449 = (let _155_442 = (c wp_assert)
in (([]), (_155_442)))
in (let _155_448 = (let _155_443 = (c wp_assume)
in (([]), (_155_443)))
in (let _155_447 = (let _155_444 = (c null_wp)
in (([]), (_155_444)))
in (let _155_446 = (let _155_445 = (c wp_trivial)
in (([]), (_155_445)))
in {FStar_Syntax_Syntax.qualifiers = _58_367.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _58_367.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _58_367.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _58_367.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _58_367.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _58_367.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _58_367.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _155_453; FStar_Syntax_Syntax.ite_wp = _155_452; FStar_Syntax_Syntax.stronger = _155_451; FStar_Syntax_Syntax.close_wp = _155_450; FStar_Syntax_Syntax.assert_p = _155_449; FStar_Syntax_Syntax.assume_p = _155_448; FStar_Syntax_Syntax.null_wp = _155_447; FStar_Syntax_Syntax.trivial = _155_446; FStar_Syntax_Syntax.repr = _58_367.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _58_367.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _58_367.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _58_367.FStar_Syntax_Syntax.actions})))))))))
in ((_155_455), (_155_454))))))))))))))))))))))))))))))))))))))))))))))))
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
| N (_58_378) -> begin
_58_378
end))


let ___M____0 = (fun projectee -> (match (projectee) with
| M (_58_381) -> begin
_58_381
end))


type nm_ =
nm


let nm_of_comp : FStar_Syntax_Syntax.comp'  ->  nm = (fun _58_1 -> (match (_58_1) with
| FStar_Syntax_Syntax.Total (t, _58_385) -> begin
N (t)
end
| FStar_Syntax_Syntax.Comp (c) when (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.monadic_lid) -> begin
M (c.FStar_Syntax_Syntax.result_typ)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(let _155_514 = (let _155_513 = (FStar_Ident.string_of_lid c.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format1 "[nm_of_comp]: impossible (%s)" _155_513))
in (FStar_All.failwith _155_514))
end
| FStar_Syntax_Syntax.GTotal (_58_393) -> begin
(FStar_All.failwith "[nm_of_comp]: impossible (GTot)")
end))


let string_of_nm : nm  ->  Prims.string = (fun _58_2 -> (match (_58_2) with
| N (t) -> begin
(let _155_517 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "N[%s]" _155_517))
end
| M (t) -> begin
(let _155_518 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "M[%s]" _155_518))
end))


let is_monadic_arrow : FStar_Syntax_Syntax.term'  ->  nm = (fun n -> (match (n) with
| FStar_Syntax_Syntax.Tm_arrow (_58_402, {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _58_408; FStar_Syntax_Syntax.pos = _58_406; FStar_Syntax_Syntax.vars = _58_404}) -> begin
(nm_of_comp n)
end
| _58_414 -> begin
(FStar_All.failwith "unexpected_argument: [is_monadic_arrow]")
end))


let is_monadic_comp = (fun c -> (match ((nm_of_comp c.FStar_Syntax_Syntax.n)) with
| M (_58_417) -> begin
true
end
| N (_58_420) -> begin
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

let star_once = (fun typ -> (let _155_530 = (let _155_528 = (let _155_527 = (FStar_Syntax_Syntax.new_bv None typ)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _155_527))
in (_155_528)::[])
in (let _155_529 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _155_530 _155_529))))
in (let _155_531 = (FStar_All.pipe_right typ star_once)
in (FStar_All.pipe_left star_once _155_531))))


let rec mk_star_to_type : (FStar_Syntax_Syntax.term'  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun mk env a -> (let _155_552 = (let _155_551 = (let _155_550 = (let _155_548 = (let _155_547 = (let _155_545 = (star_type' env a)
in (FStar_Syntax_Syntax.null_bv _155_545))
in (let _155_546 = (FStar_Syntax_Syntax.as_implicit false)
in ((_155_547), (_155_546))))
in (_155_548)::[])
in (let _155_549 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_155_550), (_155_549))))
in FStar_Syntax_Syntax.Tm_arrow (_155_551))
in (mk _155_552)))
and star_type' : env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None t.FStar_Syntax_Syntax.pos))
in (

let mk_star_to_type = (mk_star_to_type mk)
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _58_436) -> begin
(

let binders = (FStar_List.map (fun _58_441 -> (match (_58_441) with
| (bv, aqual) -> begin
(let _155_561 = (

let _58_442 = bv
in (let _155_560 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _58_442.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_442.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _155_560}))
in ((_155_561), (aqual)))
end)) binders)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_58_446, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (hn, _58_455); FStar_Syntax_Syntax.tk = _58_452; FStar_Syntax_Syntax.pos = _58_450; FStar_Syntax_Syntax.vars = _58_448}) -> begin
(let _155_565 = (let _155_564 = (let _155_563 = (let _155_562 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_GTotal _155_562))
in ((binders), (_155_563)))
in FStar_Syntax_Syntax.Tm_arrow (_155_564))
in (mk _155_565))
end
| _58_462 -> begin
(match ((is_monadic_arrow t.FStar_Syntax_Syntax.n)) with
| N (hn) -> begin
(let _155_569 = (let _155_568 = (let _155_567 = (let _155_566 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_Total _155_566))
in ((binders), (_155_567)))
in FStar_Syntax_Syntax.Tm_arrow (_155_568))
in (mk _155_569))
end
| M (a) -> begin
(let _155_578 = (let _155_577 = (let _155_576 = (let _155_574 = (let _155_573 = (let _155_572 = (let _155_570 = (mk_star_to_type env a)
in (FStar_Syntax_Syntax.null_bv _155_570))
in (let _155_571 = (FStar_Syntax_Syntax.as_implicit false)
in ((_155_572), (_155_571))))
in (_155_573)::[])
in (FStar_List.append binders _155_574))
in (let _155_575 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_155_576), (_155_575))))
in FStar_Syntax_Syntax.Tm_arrow (_155_577))
in (mk _155_578))
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

let _58_483 = (FStar_Util.string_builder_append strb "{")
in (

let _58_485 = (let _155_592 = (f x)
in (FStar_Util.string_builder_append strb _155_592))
in (

let _58_490 = (FStar_List.iter (fun x -> (

let _58_488 = (FStar_Util.string_builder_append strb ", ")
in (let _155_594 = (f x)
in (FStar_Util.string_builder_append strb _155_594)))) xs)
in (

let _58_492 = (FStar_Util.string_builder_append strb "}")
in (FStar_Util.string_of_string_builder strb))))))
end)))
in (let _155_596 = (FStar_Syntax_Print.term_to_string t)
in (let _155_595 = (string_of_set FStar_Syntax_Print.bv_to_string s)
in (FStar_Util.print2_warning "Dependency found in term %s : %s" _155_596 _155_595)))))
in (

let rec is_non_dependent_arrow = (fun ty n -> (match ((let _155_601 = (FStar_Syntax_Subst.compress ty)
in _155_601.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
if (not ((FStar_Syntax_Util.is_tot_or_gtot_comp c))) then begin
false
end else begin
try
(match (()) with
| () -> begin
(

let non_dependent_or_raise = (fun s ty -> (

let sinter = (let _155_607 = (FStar_Syntax_Free.names ty)
in (FStar_Util.set_intersect _155_607 s))
in if (not ((FStar_Util.set_is_empty sinter))) then begin
(

let _58_511 = (debug ty sinter)
in (Prims.raise Not_found))
end else begin
()
end))
in (

let _58_515 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_58_515) with
| (binders, c) -> begin
(

let s = (FStar_List.fold_left (fun s _58_520 -> (match (_58_520) with
| (bv, _58_519) -> begin
(

let _58_521 = (non_dependent_or_raise s bv.FStar_Syntax_Syntax.sort)
in (FStar_Util.set_add bv s))
end)) FStar_Syntax_Syntax.no_names binders)
in (

let ct = (FStar_Syntax_Util.comp_result c)
in (

let _58_525 = (non_dependent_or_raise s ct)
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
| _58_529 -> begin
(

let _58_530 = (let _155_611 = (FStar_Syntax_Print.term_to_string ty)
in (FStar_Util.print1_warning "Not a dependent arrow : %s" _155_611))
in false)
end))
in (

let rec is_valid_application = (fun head -> (match ((let _155_614 = (FStar_Syntax_Subst.compress head)
in _155_614.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.option_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.either_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.eq2_lid)) || (let _155_615 = (FStar_Syntax_Subst.compress head)
in (FStar_Syntax_Util.is_tuple_constructor _155_615))) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (is_non_dependent_arrow fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty (FStar_List.length args)) -> begin
(

let res = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.env t)
in (match (res.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (_58_540) -> begin
true
end
| _58_543 -> begin
(

let _58_544 = (let _155_616 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.print1_warning "Got a term which might be a non-dependent user-defined data-type %s\n" _155_616))
in false)
end))
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uinst (t, _58_554) -> begin
(is_valid_application t)
end
| _58_558 -> begin
false
end))
in if (is_valid_application head) then begin
(let _155_621 = (let _155_620 = (let _155_619 = (FStar_List.map (fun _58_561 -> (match (_58_561) with
| (t, qual) -> begin
(let _155_618 = (star_type' env t)
in ((_155_618), (qual)))
end)) args)
in ((head), (_155_619)))
in FStar_Syntax_Syntax.Tm_app (_155_620))
in (mk _155_621))
end else begin
(let _155_624 = (let _155_623 = (let _155_622 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)" _155_622))
in FStar_Syntax_Syntax.Err (_155_623))
in (Prims.raise _155_624))
end)))
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_abs (binders, repr, something) -> begin
(

let _58_581 = (FStar_Syntax_Subst.open_term binders repr)
in (match (_58_581) with
| (binders, repr) -> begin
(

let env = (

let _58_582 = env
in (let _155_625 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _155_625; subst = _58_582.subst; tc_const = _58_582.tc_const}))
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

let _58_597 = x
in {FStar_Syntax_Syntax.ppname = _58_597.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_597.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (t))))))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(let _155_628 = (let _155_627 = (let _155_626 = (star_type' env t)
in ((_155_626), (m)))
in FStar_Syntax_Syntax.Tm_meta (_155_627))
in (mk _155_628))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), something) -> begin
(let _155_633 = (let _155_632 = (let _155_631 = (star_type' env e)
in (let _155_630 = (let _155_629 = (star_type' env t)
in FStar_Util.Inl (_155_629))
in ((_155_631), (_155_630), (something))))
in FStar_Syntax_Syntax.Tm_ascribed (_155_632))
in (mk _155_633))
end
| FStar_Syntax_Syntax.Tm_ascribed (_58_610) -> begin
(let _155_636 = (let _155_635 = (let _155_634 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_ascribed is outside of the definition language: %s" _155_634))
in FStar_Syntax_Syntax.Err (_155_635))
in (Prims.raise _155_636))
end
| FStar_Syntax_Syntax.Tm_refine (_58_613) -> begin
(let _155_639 = (let _155_638 = (let _155_637 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_refine is outside of the definition language: %s" _155_637))
in FStar_Syntax_Syntax.Err (_155_638))
in (Prims.raise _155_639))
end
| FStar_Syntax_Syntax.Tm_uinst (_58_616) -> begin
(let _155_642 = (let _155_641 = (let _155_640 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_uinst is outside of the definition language: %s" _155_640))
in FStar_Syntax_Syntax.Err (_155_641))
in (Prims.raise _155_642))
end
| FStar_Syntax_Syntax.Tm_constant (_58_619) -> begin
(let _155_645 = (let _155_644 = (let _155_643 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_constant is outside of the definition language: %s" _155_643))
in FStar_Syntax_Syntax.Err (_155_644))
in (Prims.raise _155_645))
end
| FStar_Syntax_Syntax.Tm_match (_58_622) -> begin
(let _155_648 = (let _155_647 = (let _155_646 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_match is outside of the definition language: %s" _155_646))
in FStar_Syntax_Syntax.Err (_155_647))
in (Prims.raise _155_648))
end
| FStar_Syntax_Syntax.Tm_let (_58_625) -> begin
(let _155_651 = (let _155_650 = (let _155_649 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_let is outside of the definition language: %s" _155_649))
in FStar_Syntax_Syntax.Err (_155_650))
in (Prims.raise _155_651))
end
| FStar_Syntax_Syntax.Tm_uvar (_58_628) -> begin
(let _155_654 = (let _155_653 = (let _155_652 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_uvar is outside of the definition language: %s" _155_652))
in FStar_Syntax_Syntax.Err (_155_653))
in (Prims.raise _155_654))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _155_657 = (let _155_656 = (let _155_655 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_unknown is outside of the definition language: %s" _155_655))
in FStar_Syntax_Syntax.Err (_155_656))
in (Prims.raise _155_657))
end
| FStar_Syntax_Syntax.Tm_delayed (_58_632) -> begin
(FStar_All.failwith "impossible")
end)))))


let is_monadic : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  Prims.bool = (fun _58_3 -> (match (_58_3) with
| None -> begin
(FStar_All.failwith "un-annotated lambda?!")
end
| (Some (FStar_Util.Inl ({FStar_Syntax_Syntax.eff_name = lid; FStar_Syntax_Syntax.res_typ = _; FStar_Syntax_Syntax.cflags = _; FStar_Syntax_Syntax.comp = _}))) | (Some (FStar_Util.Inr (lid))) -> begin
(FStar_Ident.lid_equals lid FStar_Syntax_Const.monadic_lid)
end))


let rec is_C : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match ((let _155_665 = (FStar_Syntax_Subst.compress t)
in _155_665.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) when (FStar_Syntax_Util.is_tuple_constructor head) -> begin
(

let r = (let _155_667 = (let _155_666 = (FStar_List.hd args)
in (Prims.fst _155_666))
in (is_C _155_667))
in if r then begin
(

let _58_658 = if (not ((FStar_List.for_all (fun _58_657 -> (match (_58_657) with
| (h, _58_656) -> begin
(is_C h)
end)) args))) then begin
(FStar_All.failwith "not a C (A * C)")
end else begin
()
end
in true)
end else begin
(

let _58_664 = if (not ((FStar_List.for_all (fun _58_663 -> (match (_58_663) with
| (h, _58_662) -> begin
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

let _58_672 = if (is_C t) then begin
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
| _58_692 -> begin
false
end))


let mk_return : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let p_type = (mk_star_to_type mk env t)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'" None p_type)
in (

let body = (let _155_683 = (let _155_682 = (let _155_681 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _155_680 = (let _155_679 = (let _155_678 = (FStar_Syntax_Syntax.as_implicit false)
in ((e), (_155_678)))
in (_155_679)::[])
in ((_155_681), (_155_680))))
in FStar_Syntax_Syntax.Tm_app (_155_682))
in (mk _155_683))
in (let _155_685 = (let _155_684 = (FStar_Syntax_Syntax.mk_binder p)
in (_155_684)::[])
in (FStar_Syntax_Util.abs _155_685 body None)))))))


let is_unknown : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun _58_4 -> (match (_58_4) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| _58_704 -> begin
false
end))


let rec check : env  ->  FStar_Syntax_Syntax.term  ->  nm  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e context_nm -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let return_if = (fun _58_714 -> (match (_58_714) with
| (rec_nm, s_e, u_e) -> begin
(

let check = (fun t1 t2 -> if ((not ((is_unknown t2.FStar_Syntax_Syntax.n))) && (not ((let _155_739 = (FStar_TypeChecker_Rel.teq env.env t1 t2)
in (FStar_TypeChecker_Rel.is_trivial _155_739))))) then begin
(let _155_744 = (let _155_743 = (let _155_742 = (FStar_Syntax_Print.term_to_string e)
in (let _155_741 = (FStar_Syntax_Print.term_to_string t1)
in (let _155_740 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check]: the expression [%s] has type [%s] but should have type [%s]" _155_742 _155_741 _155_740))))
in FStar_Syntax_Syntax.Err (_155_743))
in (Prims.raise _155_744))
end else begin
()
end)
in (match (((rec_nm), (context_nm))) with
| ((N (t1), N (t2))) | ((M (t1), M (t2))) -> begin
(

let _58_726 = (check t1 t2)
in ((rec_nm), (s_e), (u_e)))
end
| (N (t1), M (t2)) -> begin
(

let _58_733 = (check t1 t2)
in (let _155_745 = (mk_return env t1 s_e)
in ((M (t1)), (_155_745), (u_e))))
end
| (M (t1), N (t2)) -> begin
(let _155_750 = (let _155_749 = (let _155_748 = (FStar_Syntax_Print.term_to_string e)
in (let _155_747 = (FStar_Syntax_Print.term_to_string t1)
in (let _155_746 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]" _155_748 _155_747 _155_746))))
in FStar_Syntax_Syntax.Err (_155_749))
in (Prims.raise _155_750))
end))
end))
in (

let ensure_m = (fun env e2 -> (

let strip_m = (fun _58_5 -> (match (_58_5) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _58_750 -> begin
(FStar_All.failwith "impossible")
end))
in (match (context_nm) with
| N (t) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren\'t"), (e2.FStar_Syntax_Syntax.pos)))))
end
| M (_58_755) -> begin
(let _155_757 = (check env e2 context_nm)
in (strip_m _155_757))
end)))
in (match ((let _155_758 = (FStar_Syntax_Subst.compress e)
in _155_758.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
(let _155_759 = (infer env e)
in (return_if _155_759))
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
| FStar_Syntax_Syntax.Tm_let (_58_806) -> begin
(let _155_767 = (let _155_766 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_let %s" _155_766))
in (FStar_All.failwith _155_767))
end
| FStar_Syntax_Syntax.Tm_type (_58_809) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_58_812) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_58_815) -> begin
(let _155_769 = (let _155_768 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_refine %s" _155_768))
in (FStar_All.failwith _155_769))
end
| FStar_Syntax_Syntax.Tm_uvar (_58_818) -> begin
(let _155_771 = (let _155_770 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_uvar %s" _155_770))
in (FStar_All.failwith _155_771))
end
| FStar_Syntax_Syntax.Tm_delayed (_58_821) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _155_776 = (let _155_775 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_unknown %s" _155_775))
in (FStar_All.failwith _155_776))
end)))))
and infer : env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.env)
in (match ((let _155_782 = (FStar_Syntax_Subst.compress e)
in _155_782.FStar_Syntax_Syntax.n)) with
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

let _58_841 = env
in (let _155_783 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _155_783; subst = _58_841.subst; tc_const = _58_841.tc_const}))
in (

let s_binders = (FStar_List.map (fun _58_846 -> (match (_58_846) with
| (bv, qual) -> begin
(

let sort = (star_type' env bv.FStar_Syntax_Syntax.sort)
in (((

let _58_848 = bv
in {FStar_Syntax_Syntax.ppname = _58_848.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_848.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (qual)))
end)) binders)
in (

let _58_870 = (FStar_List.fold_left (fun _58_853 _58_856 -> (match (((_58_853), (_58_856))) with
| ((env, acc), (bv, qual)) -> begin
(

let c = bv.FStar_Syntax_Syntax.sort
in if (is_C c) then begin
(

let xw = (let _155_787 = (star_type' env c)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "^w") None _155_787))
in (

let x = (

let _58_859 = bv
in (let _155_789 = (let _155_788 = (FStar_Syntax_Syntax.bv_to_name xw)
in (trans_F_ env c _155_788))
in {FStar_Syntax_Syntax.ppname = _58_859.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_859.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _155_789}))
in (

let env = (

let _58_862 = env
in (let _155_793 = (let _155_792 = (let _155_791 = (let _155_790 = (FStar_Syntax_Syntax.bv_to_name xw)
in ((bv), (_155_790)))
in FStar_Syntax_Syntax.NT (_155_791))
in (_155_792)::env.subst)
in {env = _58_862.env; subst = _155_793; tc_const = _58_862.tc_const}))
in (let _155_797 = (let _155_796 = (FStar_Syntax_Syntax.mk_binder x)
in (let _155_795 = (let _155_794 = (FStar_Syntax_Syntax.mk_binder xw)
in (_155_794)::acc)
in (_155_796)::_155_795))
in ((env), (_155_797))))))
end else begin
(

let x = (

let _58_865 = bv
in (let _155_798 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _58_865.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_865.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _155_798}))
in (let _155_800 = (let _155_799 = (FStar_Syntax_Syntax.mk_binder x)
in (_155_799)::acc)
in ((env), (_155_800))))
end)
end)) ((env), ([])) binders)
in (match (_58_870) with
| (env, u_binders) -> begin
(

let u_binders = (FStar_List.rev u_binders)
in (

let _58_880 = (

let check_what = if (is_monadic what) then begin
check_m
end else begin
check_n
end
in (

let _58_876 = (check_what env body)
in (match (_58_876) with
| (t, s_body, u_body) -> begin
(let _155_806 = (let _155_805 = if (is_monadic what) then begin
M (t)
end else begin
N (t)
end
in (comp_of_nm _155_805))
in ((_155_806), (s_body), (u_body)))
end)))
in (match (_58_880) with
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
(let _155_812 = (let _155_811 = (let _155_810 = (let _155_809 = (let _155_808 = (let _155_807 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.comp_result _155_807))
in (FStar_All.pipe_left double_star _155_808))
in (FStar_Syntax_Syntax.mk_Total _155_809))
in (FStar_Syntax_Util.lcomp_of_comp _155_810))
in FStar_Util.Inl (_155_811))
in Some (_155_812))
end else begin
Some (FStar_Util.Inl ((

let _58_886 = lc
in {FStar_Syntax_Syntax.eff_name = _58_886.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _58_886.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _58_886.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _58_888 -> (match (()) with
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

let _58_898 = (

let comp = (let _155_815 = (is_monadic what)
in (let _155_814 = (FStar_Syntax_Subst.subst env.subst s_body)
in (trans_G env (FStar_Syntax_Util.comp_result comp) _155_815 _155_814)))
in (let _155_816 = (FStar_Syntax_Util.ascribe u_body (FStar_Util.Inr (comp)))
in ((_155_816), (Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp comp)))))))
in (match (_58_898) with
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
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = {FStar_Syntax_Syntax.v = lid; FStar_Syntax_Syntax.ty = _58_912; FStar_Syntax_Syntax.p = _58_910}; FStar_Syntax_Syntax.fv_delta = _58_908; FStar_Syntax_Syntax.fv_qual = _58_906}) -> begin
(

let _58_920 = (FStar_TypeChecker_Env.lookup_lid env.env lid)
in (match (_58_920) with
| (_58_918, t) -> begin
(

let txt = (FStar_Ident.text_of_lid lid)
in (let _155_818 = (let _155_817 = (normalize t)
in N (_155_817))
in ((_155_818), (e), (e))))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _58_929 = (check_n env head)
in (match (_58_929) with
| (t_head, s_head, u_head) -> begin
(

let is_arrow = (fun t -> (match ((let _155_821 = (FStar_Syntax_Subst.compress t)
in _155_821.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_933) -> begin
true
end
| _58_936 -> begin
false
end))
in (

let rec flatten = (fun t -> (match ((let _155_824 = (FStar_Syntax_Subst.compress t)
in _155_824.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (t, _58_948); FStar_Syntax_Syntax.tk = _58_945; FStar_Syntax_Syntax.pos = _58_943; FStar_Syntax_Syntax.vars = _58_941}) when (is_arrow t) -> begin
(

let _58_956 = (flatten t)
in (match (_58_956) with
| (binders', comp) -> begin
(((FStar_List.append binders binders')), (comp))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
((binders), (comp))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, _58_963, _58_965) -> begin
(flatten e)
end
| _58_969 -> begin
(let _155_827 = (let _155_826 = (let _155_825 = (FStar_Syntax_Print.term_to_string t_head)
in (FStar_Util.format1 "%s: not a function type" _155_825))
in FStar_Syntax_Syntax.Err (_155_826))
in (Prims.raise _155_827))
end))
in (

let _58_972 = (flatten t_head)
in (match (_58_972) with
| (binders, comp) -> begin
(

let n = (FStar_List.length binders)
in (

let n' = (FStar_List.length args)
in (

let _58_975 = if ((FStar_List.length binders) < (FStar_List.length args)) then begin
(let _155_832 = (let _155_831 = (let _155_830 = (FStar_Util.string_of_int n)
in (let _155_829 = (FStar_Util.string_of_int (n' - n))
in (let _155_828 = (FStar_Util.string_of_int n)
in (FStar_Util.format3 "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments." _155_830 _155_829 _155_828))))
in FStar_Syntax_Syntax.Err (_155_831))
in (Prims.raise _155_832))
end else begin
()
end
in (

let _58_979 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (_58_979) with
| (binders, comp) -> begin
(

let rec final_type = (fun subst _58_984 args -> (match (_58_984) with
| (binders, comp) -> begin
(match (((binders), (args))) with
| ([], []) -> begin
(let _155_840 = (let _155_839 = (FStar_Syntax_Subst.subst_comp subst comp)
in _155_839.FStar_Syntax_Syntax.n)
in (nm_of_comp _155_840))
end
| (binders, []) -> begin
(match ((let _155_843 = (let _155_842 = (let _155_841 = (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))))
in (FStar_Syntax_Subst.subst subst _155_841))
in (FStar_Syntax_Subst.compress _155_842))
in _155_843.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(let _155_847 = (let _155_846 = (let _155_845 = (let _155_844 = (FStar_Syntax_Subst.close_comp binders comp)
in ((binders), (_155_844)))
in FStar_Syntax_Syntax.Tm_arrow (_155_845))
in (mk _155_846))
in N (_155_847))
end
| _58_997 -> begin
(FStar_All.failwith "wat?")
end)
end
| ([], (_58_1002)::_58_1000) -> begin
(FStar_All.failwith "just checked that?!")
end
| (((bv, _58_1008))::binders, ((arg, _58_1014))::args) -> begin
(final_type ((FStar_Syntax_Syntax.NT (((bv), (arg))))::subst) ((binders), (comp)) args)
end)
end))
in (

let final_type = (final_type [] ((binders), (comp)) args)
in (

let _58_1022 = (FStar_List.splitAt n' binders)
in (match (_58_1022) with
| (binders, _58_1021) -> begin
(

let _58_1043 = (let _155_854 = (FStar_List.map2 (fun _58_1026 _58_1029 -> (match (((_58_1026), (_58_1029))) with
| ((bv, _58_1025), (arg, q)) -> begin
(match ((let _155_850 = (FStar_Syntax_Subst.compress bv.FStar_Syntax_Syntax.sort)
in _155_850.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_58_1031) -> begin
(

let arg = ((arg), (q))
in ((arg), ((arg)::[])))
end
| _58_1035 -> begin
(

let _58_1040 = (check_n env arg)
in (match (_58_1040) with
| (_58_1037, s_arg, u_arg) -> begin
(let _155_853 = if (is_C bv.FStar_Syntax_Syntax.sort) then begin
(let _155_852 = (let _155_851 = (FStar_Syntax_Subst.subst env.subst s_arg)
in ((_155_851), (q)))
in (_155_852)::(((u_arg), (q)))::[])
end else begin
(((u_arg), (q)))::[]
end
in ((((s_arg), (q))), (_155_853)))
end))
end)
end)) binders args)
in (FStar_List.split _155_854))
in (match (_58_1043) with
| (s_args, u_args) -> begin
(

let u_args = (FStar_List.flatten u_args)
in (let _155_856 = (mk (FStar_Syntax_Syntax.Tm_app (((s_head), (s_args)))))
in (let _155_855 = (mk (FStar_Syntax_Syntax.Tm_app (((u_head), (u_args)))))
in ((final_type), (_155_856), (_155_855)))))
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
(let _155_858 = (let _155_857 = (env.tc_const c)
in N (_155_857))
in ((_155_858), (e), (e)))
end
| FStar_Syntax_Syntax.Tm_let (_58_1074) -> begin
(let _155_860 = (let _155_859 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_let %s" _155_859))
in (FStar_All.failwith _155_860))
end
| FStar_Syntax_Syntax.Tm_type (_58_1077) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_58_1080) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_58_1083) -> begin
(let _155_862 = (let _155_861 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_refine %s" _155_861))
in (FStar_All.failwith _155_862))
end
| FStar_Syntax_Syntax.Tm_uvar (_58_1086) -> begin
(let _155_864 = (let _155_863 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_uvar %s" _155_863))
in (FStar_All.failwith _155_864))
end
| FStar_Syntax_Syntax.Tm_delayed (_58_1089) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _155_869 = (let _155_868 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_unknown %s" _155_868))
in (FStar_All.failwith _155_869))
end))))
and mk_match : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e0 branches f -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e0.FStar_Syntax_Syntax.pos))
in (

let _58_1102 = (check_n env e0)
in (match (_58_1102) with
| (_58_1099, s_e0, u_e0) -> begin
(

let _58_1119 = (let _155_885 = (FStar_List.map (fun b -> (match ((FStar_Syntax_Subst.open_branch b)) with
| (pat, None, body) -> begin
(

let env = (

let _58_1108 = env
in (let _155_884 = (let _155_883 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env.env _155_883))
in {env = _155_884; subst = _58_1108.subst; tc_const = _58_1108.tc_const}))
in (

let _58_1114 = (f env body)
in (match (_58_1114) with
| (nm, s_body, u_body) -> begin
((nm), (((pat), (None), (((s_body), (u_body), (body))))))
end)))
end
| _58_1116 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("No when clauses in the definition language")))
end)) branches)
in (FStar_List.split _155_885))
in (match (_58_1119) with
| (nms, branches) -> begin
(

let t1 = (match ((FStar_List.hd nms)) with
| (M (t1)) | (N (t1)) -> begin
t1
end)
in (

let has_m = (FStar_List.existsb (fun _58_6 -> (match (_58_6) with
| M (_58_1126) -> begin
true
end
| _58_1129 -> begin
false
end)) nms)
in (

let _58_1163 = (let _155_889 = (FStar_List.map2 (fun nm _58_1138 -> (match (_58_1138) with
| (pat, guard, (s_body, u_body, original_body)) -> begin
(match (((nm), (has_m))) with
| ((N (t2), false)) | ((M (t2), true)) -> begin
((nm), (((pat), (guard), (s_body))), (((pat), (guard), (u_body))))
end
| (N (t2), true) -> begin
(

let _58_1154 = (check env original_body (M (t2)))
in (match (_58_1154) with
| (_58_1151, s_body, u_body) -> begin
((M (t2)), (((pat), (guard), (s_body))), (((pat), (guard), (u_body))))
end))
end
| (M (_58_1156), false) -> begin
(FStar_All.failwith "impossible")
end)
end)) nms branches)
in (FStar_List.unzip3 _155_889))
in (match (_58_1163) with
| (nms, s_branches, u_branches) -> begin
if has_m then begin
(

let p_type = (mk_star_to_type mk env t1)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" None p_type)
in (

let s_branches = (FStar_List.map (fun _58_1169 -> (match (_58_1169) with
| (pat, guard, s_body) -> begin
(

let s_body = (let _155_896 = (let _155_895 = (let _155_894 = (let _155_893 = (let _155_892 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _155_891 = (FStar_Syntax_Syntax.as_implicit false)
in ((_155_892), (_155_891))))
in (_155_893)::[])
in ((s_body), (_155_894)))
in FStar_Syntax_Syntax.Tm_app (_155_895))
in (mk _155_896))
in ((pat), (guard), (s_body)))
end)) s_branches)
in (

let s_branches = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let s_e = (let _155_899 = (let _155_897 = (FStar_Syntax_Syntax.mk_binder p)
in (_155_897)::[])
in (let _155_898 = (mk (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches)))))
in (FStar_Syntax_Util.abs _155_899 _155_898 None)))
in (

let t1_star = (let _155_903 = (let _155_901 = (let _155_900 = (FStar_Syntax_Syntax.new_bv None p_type)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _155_900))
in (_155_901)::[])
in (let _155_902 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _155_903 _155_902)))
in (let _155_905 = (mk (FStar_Syntax_Syntax.Tm_ascribed (((s_e), (FStar_Util.Inl (t1_star)), (None)))))
in (let _155_904 = (mk (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches)))))
in ((M (t1)), (_155_905), (_155_904)))))))))))
end else begin
(

let s_branches = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let t1_star = t1
in (let _155_910 = (let _155_908 = (let _155_907 = (let _155_906 = (mk (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches)))))
in ((_155_906), (FStar_Util.Inl (t1_star)), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (_155_907))
in (mk _155_908))
in (let _155_909 = (mk (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches)))))
in ((N (t1)), (_155_910), (_155_909)))))))
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

let x_binders = (let _155_930 = (FStar_Syntax_Syntax.mk_binder x)
in (_155_930)::[])
in (

let _58_1191 = (FStar_Syntax_Subst.open_term x_binders e2)
in (match (_58_1191) with
| (x_binders, e2) -> begin
(

let s_binding = if (FStar_Ident.lid_equals FStar_Syntax_Const.monadic_lid binding.FStar_Syntax_Syntax.lbeff) then begin
(

let _58_1192 = binding
in (let _155_931 = (double_star binding.FStar_Syntax_Syntax.lbtyp)
in {FStar_Syntax_Syntax.lbname = _58_1192.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _58_1192.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _155_931; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _58_1192.FStar_Syntax_Syntax.lbdef}))
end else begin
(

let _58_1194 = binding
in (let _155_932 = (star_type' env binding.FStar_Syntax_Syntax.lbtyp)
in {FStar_Syntax_Syntax.lbname = _58_1194.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _58_1194.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _155_932; FStar_Syntax_Syntax.lbeff = _58_1194.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _58_1194.FStar_Syntax_Syntax.lbdef}))
end
in (match ((infer env e1)) with
| (N (t1), s_e1, u_e1) -> begin
(

let u_binding = if (is_C t1) then begin
(

let _58_1202 = binding
in (let _155_934 = (let _155_933 = (FStar_Syntax_Subst.subst env.subst s_e1)
in (trans_F_ env t1 _155_933))
in {FStar_Syntax_Syntax.lbname = _58_1202.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _58_1202.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _155_934; FStar_Syntax_Syntax.lbeff = _58_1202.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _58_1202.FStar_Syntax_Syntax.lbdef}))
end else begin
binding
end
in (

let env = (

let _58_1205 = env
in (let _155_935 = (FStar_TypeChecker_Env.push_bv env.env (

let _58_1207 = x
in {FStar_Syntax_Syntax.ppname = _58_1207.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1207.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _155_935; subst = _58_1205.subst; tc_const = _58_1205.tc_const}))
in (

let _58_1213 = (proceed env e2)
in (match (_58_1213) with
| (nm_rec, s_e2, u_e2) -> begin
(let _155_943 = (let _155_938 = (let _155_937 = (let _155_936 = (FStar_Syntax_Subst.close x_binders s_e2)
in ((((false), (((

let _58_1214 = s_binding
in {FStar_Syntax_Syntax.lbname = _58_1214.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _58_1214.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _58_1214.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _58_1214.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = s_e1}))::[]))), (_155_936)))
in FStar_Syntax_Syntax.Tm_let (_155_937))
in (mk _155_938))
in (let _155_942 = (let _155_941 = (let _155_940 = (let _155_939 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _58_1216 = u_binding
in {FStar_Syntax_Syntax.lbname = _58_1216.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _58_1216.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _58_1216.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _58_1216.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_155_939)))
in FStar_Syntax_Syntax.Tm_let (_155_940))
in (mk _155_941))
in ((nm_rec), (_155_943), (_155_942))))
end))))
end
| (M (t1), s_e1, u_e1) -> begin
(

let u_binding = (

let _58_1223 = binding
in {FStar_Syntax_Syntax.lbname = _58_1223.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _58_1223.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.lbdef = _58_1223.FStar_Syntax_Syntax.lbdef})
in (

let env = (

let _58_1226 = env
in (let _155_944 = (FStar_TypeChecker_Env.push_bv env.env (

let _58_1228 = x
in {FStar_Syntax_Syntax.ppname = _58_1228.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1228.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _155_944; subst = _58_1226.subst; tc_const = _58_1226.tc_const}))
in (

let _58_1234 = (ensure_m env e2)
in (match (_58_1234) with
| (t2, s_e2, u_e2) -> begin
(

let p_type = (mk_star_to_type mk env t2)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" None p_type)
in (

let s_e2 = (let _155_950 = (let _155_949 = (let _155_948 = (let _155_947 = (let _155_946 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _155_945 = (FStar_Syntax_Syntax.as_implicit false)
in ((_155_946), (_155_945))))
in (_155_947)::[])
in ((s_e2), (_155_948)))
in FStar_Syntax_Syntax.Tm_app (_155_949))
in (mk _155_950))
in (

let s_e2 = (FStar_Syntax_Util.abs x_binders s_e2 None)
in (

let body = (let _155_955 = (let _155_954 = (let _155_953 = (let _155_952 = (let _155_951 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_e2), (_155_951)))
in (_155_952)::[])
in ((s_e1), (_155_953)))
in FStar_Syntax_Syntax.Tm_app (_155_954))
in (mk _155_955))
in (let _155_962 = (let _155_957 = (let _155_956 = (FStar_Syntax_Syntax.mk_binder p)
in (_155_956)::[])
in (FStar_Syntax_Util.abs _155_957 body None))
in (let _155_961 = (let _155_960 = (let _155_959 = (let _155_958 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _58_1240 = u_binding
in {FStar_Syntax_Syntax.lbname = _58_1240.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _58_1240.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _58_1240.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _58_1240.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_155_958)))
in FStar_Syntax_Syntax.Tm_let (_155_959))
in (mk _155_960))
in ((M (t2)), (_155_962), (_155_961)))))))))
end))))
end))
end)))))))
and check_n : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _155_965 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in N (_155_965))
in (match ((check env e mn)) with
| (N (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _58_1251 -> begin
(FStar_All.failwith "[check_n]: impossible")
end)))
and check_m : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _155_968 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in M (_155_968))
in (match ((check env e mn)) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _58_1261 -> begin
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

let _58_1272 = if (not ((is_C c))) then begin
(FStar_All.failwith "not a C")
end else begin
()
end
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos))
in (match ((let _155_977 = (FStar_Syntax_Subst.compress c)
in _155_977.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _58_1282 = (FStar_Syntax_Util.head_and_args wp)
in (match (_58_1282) with
| (wp_head, wp_args) -> begin
(

let _58_1283 = if ((not (((FStar_List.length wp_args) = (FStar_List.length args)))) || (not ((let _155_978 = (FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length wp_args) FStar_Range.dummyRange)
in (FStar_Syntax_Util.is_constructor wp_head _155_978))))) then begin
(FStar_All.failwith "mismatch")
end else begin
()
end
in (let _155_988 = (let _155_987 = (let _155_986 = (FStar_List.map2 (fun _58_1287 _58_1290 -> (match (((_58_1287), (_58_1290))) with
| ((arg, q), (wp_arg, q')) -> begin
(

let print_implicit = (fun q -> if (FStar_Syntax_Syntax.is_implicit q) then begin
"implicit"
end else begin
"explicit"
end)
in (

let _58_1293 = if (q <> q') then begin
(let _155_984 = (print_implicit q)
in (let _155_983 = (print_implicit q')
in (FStar_Util.print2_warning "Incoherent implicit qualifiers %b %b" _155_984 _155_983)))
end else begin
()
end
in (let _155_985 = (trans_F_ env arg wp_arg)
in ((_155_985), (q)))))
end)) args wp_args)
in ((head), (_155_986)))
in FStar_Syntax_Syntax.Tm_app (_155_987))
in (mk _155_988)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let binders = (FStar_Syntax_Util.name_binders binders)
in (

let _58_1302 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (_58_1302) with
| (binders_orig, comp) -> begin
(

let _58_1311 = (let _155_998 = (FStar_List.map (fun _58_1305 -> (match (_58_1305) with
| (bv, q) -> begin
(

let h = bv.FStar_Syntax_Syntax.sort
in if (is_C h) then begin
(

let w' = (let _155_990 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-w\'") None _155_990))
in (let _155_996 = (let _155_995 = (let _155_994 = (let _155_993 = (let _155_992 = (let _155_991 = (FStar_Syntax_Syntax.bv_to_name w')
in (trans_F_ env h _155_991))
in (FStar_Syntax_Syntax.null_bv _155_992))
in ((_155_993), (q)))
in (_155_994)::[])
in (((w'), (q)))::_155_995)
in ((w'), (_155_996))))
end else begin
(

let x = (let _155_997 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-x") None _155_997))
in ((x), ((((x), (q)))::[])))
end)
end)) binders_orig)
in (FStar_List.split _155_998))
in (match (_58_1311) with
| (bvs, binders) -> begin
(

let binders = (FStar_List.flatten binders)
in (

let comp = (let _155_1000 = (let _155_999 = (FStar_Syntax_Syntax.binders_of_list bvs)
in (FStar_Syntax_Util.rename_binders binders_orig _155_999))
in (FStar_Syntax_Subst.subst_comp _155_1000 comp))
in (

let app = (let _155_1006 = (let _155_1005 = (let _155_1004 = (FStar_List.map (fun bv -> (let _155_1003 = (FStar_Syntax_Syntax.bv_to_name bv)
in (let _155_1002 = (FStar_Syntax_Syntax.as_implicit false)
in ((_155_1003), (_155_1002))))) bvs)
in ((wp), (_155_1004)))
in FStar_Syntax_Syntax.Tm_app (_155_1005))
in (mk _155_1006))
in (

let comp = (let _155_1008 = (type_of_comp comp)
in (let _155_1007 = (is_monadic_comp comp)
in (trans_G env _155_1008 _155_1007 app)))
in (FStar_Syntax_Util.arrow binders comp)))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, _58_1319, _58_1321) -> begin
(trans_F_ env e wp)
end
| _58_1325 -> begin
(FStar_All.failwith "impossible trans_F_")
end))))
and trans_G : env_  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env h is_monadic wp -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None h.FStar_Syntax_Syntax.pos))
in if is_monadic then begin
(let _155_1019 = (let _155_1018 = (star_type' env h)
in (let _155_1017 = (let _155_1016 = (let _155_1015 = (FStar_Syntax_Syntax.as_implicit false)
in ((wp), (_155_1015)))
in (_155_1016)::[])
in {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_unknown)::[]; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _155_1018; FStar_Syntax_Syntax.effect_args = _155_1017; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp _155_1019))
end else begin
(let _155_1020 = (trans_F_ env h wp)
in (FStar_Syntax_Syntax.mk_Total _155_1020))
end))


let n : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]))


let star_type : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _155_1027 = (n env.env t)
in (star_type' env _155_1027)))


let star_expr : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env t -> (let _155_1032 = (n env.env t)
in (check_n env _155_1032)))


let trans_F : env_  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> (let _155_1040 = (n env.env c)
in (let _155_1039 = (n env.env wp)
in (trans_F_ env _155_1040 _155_1039))))




