
open Prims

let gen_wps_for_free : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.sigelts * FStar_Syntax_Syntax.eff_decl) = (fun env binders a wp_a ed -> (

let wp_a = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env wp_a)
in (

let a = (

let _57_13 = a
in (let _149_11 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env a.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_13.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_13.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_11}))
in (

let d = (fun s -> (FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s))
in (

let _57_20 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _57_18 = (d "Elaborating extra WP combinators")
in (let _149_14 = (FStar_Syntax_Print.term_to_string wp_a)
in (FStar_Util.print1 "wp_a is: %s\n" _149_14)))
end else begin
()
end
in (

let rec collect_binders = (fun t -> (match ((let _149_17 = (FStar_Syntax_Subst.compress t)
in _149_17.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let rest = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
t
end
| _57_31 -> begin
(FStar_All.failwith "wp_a contains non-Tot arrow")
end)
in (let _149_18 = (collect_binders rest)
in (FStar_List.append bs _149_18)))
end
| FStar_Syntax_Syntax.Tm_type (_57_34) -> begin
[]
end
| _57_37 -> begin
(FStar_All.failwith "wp_a doesn\'t end in Type0")
end))
in (

let mk_lid = (fun name -> (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" name))) FStar_Range.dummyRange))
in (

let gamma = (let _149_21 = (collect_binders wp_a)
in (FStar_All.pipe_right _149_21 FStar_Syntax_Util.name_binders))
in (

let _57_41 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _149_23 = (let _149_22 = (FStar_Syntax_Print.binders_to_string ", " gamma)
in (FStar_Util.format1 "Gamma is %s\n" _149_22))
in (d _149_23))
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

let _57_53 = (FStar_TypeChecker_Util.mk_toplevel_definition env lident def)
in (match (_57_53) with
| (sigelt, fv) -> begin
(

let _57_54 = (let _149_33 = (let _149_32 = (FStar_ST.read sigelts)
in (sigelt)::_149_32)
in (FStar_ST.op_Colon_Equals sigelts _149_33))
in fv)
end)))
in (

let binders_of_list = (FStar_List.map (fun _57_58 -> (match (_57_58) with
| (t, b) -> begin
(let _149_36 = (FStar_Syntax_Syntax.as_implicit b)
in ((t), (_149_36)))
end)))
in (

let mk_all_implicit = (FStar_List.map (fun t -> (let _149_39 = (FStar_Syntax_Syntax.as_implicit true)
in (((Prims.fst t)), (_149_39)))))
in (

let args_of_binders = (FStar_List.map (fun bv -> (let _149_42 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst bv))
in (FStar_Syntax_Syntax.as_arg _149_42))))
in (

let _57_85 = (

let _57_70 = (

let mk = (fun f -> (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let body = (let _149_55 = (let _149_54 = (FStar_Syntax_Syntax.bv_to_name t)
in (f _149_54))
in (FStar_Syntax_Util.arrow gamma _149_55))
in (let _149_60 = (let _149_59 = (let _149_58 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_57 = (let _149_56 = (FStar_Syntax_Syntax.mk_binder t)
in (_149_56)::[])
in (_149_58)::_149_57))
in (FStar_List.append binders _149_59))
in (FStar_Syntax_Util.abs _149_60 body None)))))
in (let _149_62 = (mk FStar_Syntax_Syntax.mk_Total)
in (let _149_61 = (mk FStar_Syntax_Syntax.mk_GTotal)
in ((_149_62), (_149_61)))))
in (match (_57_70) with
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

let mk_app = (fun fv t -> (let _149_84 = (let _149_83 = (let _149_82 = (let _149_81 = (FStar_List.map (fun _57_81 -> (match (_57_81) with
| (bv, _57_80) -> begin
(let _149_73 = (FStar_Syntax_Syntax.bv_to_name bv)
in (let _149_72 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_73), (_149_72))))
end)) binders)
in (let _149_80 = (let _149_79 = (let _149_75 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _149_74 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_75), (_149_74))))
in (let _149_78 = (let _149_77 = (let _149_76 = (FStar_Syntax_Syntax.as_implicit false)
in ((t), (_149_76)))
in (_149_77)::[])
in (_149_79)::_149_78))
in (FStar_List.append _149_81 _149_80)))
in ((fv), (_149_82)))
in FStar_Syntax_Syntax.Tm_app (_149_83))
in (mk _149_84)))
in ((env), ((mk_app ctx_fv)), ((mk_app gctx_fv))))))))
end))
in (match (_57_85) with
| (env, mk_ctx, mk_gctx) -> begin
(

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

let body = (let _149_95 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs gamma _149_95 ret))
in (let _149_98 = (let _149_97 = (mk_all_implicit binders)
in (let _149_96 = (binders_of_list ((((a), (true)))::(((t), (true)))::(((x), (false)))::[]))
in (FStar_List.append _149_97 _149_96)))
in (FStar_Syntax_Util.abs _149_98 body ret))))))
in (

let c_pure = (let _149_99 = (mk_lid "pure")
in (register env _149_99 c_pure))
in (

let c_app = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let l = (let _149_107 = (let _149_106 = (let _149_105 = (let _149_102 = (let _149_101 = (let _149_100 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv None _149_100))
in (FStar_Syntax_Syntax.mk_binder _149_101))
in (_149_102)::[])
in (let _149_104 = (let _149_103 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _149_103))
in (FStar_Syntax_Util.arrow _149_105 _149_104)))
in (mk_gctx _149_106))
in (FStar_Syntax_Syntax.gen_bv "l" None _149_107))
in (

let r = (let _149_109 = (let _149_108 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _149_108))
in (FStar_Syntax_Syntax.gen_bv "r" None _149_109))
in (

let ret = (let _149_114 = (let _149_113 = (let _149_112 = (let _149_111 = (let _149_110 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _149_110))
in (FStar_Syntax_Syntax.mk_Total _149_111))
in (FStar_Syntax_Util.lcomp_of_comp _149_112))
in FStar_Util.Inl (_149_113))
in Some (_149_114))
in (

let outer_body = (

let gamma_as_args = (args_of_binders gamma)
in (

let inner_body = (let _149_120 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _149_119 = (let _149_118 = (let _149_117 = (let _149_116 = (let _149_115 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app _149_115 gamma_as_args))
in (FStar_Syntax_Syntax.as_arg _149_116))
in (_149_117)::[])
in (FStar_List.append gamma_as_args _149_118))
in (FStar_Syntax_Util.mk_app _149_120 _149_119)))
in (FStar_Syntax_Util.abs gamma inner_body ret)))
in (let _149_123 = (let _149_122 = (mk_all_implicit binders)
in (let _149_121 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((l), (false)))::(((r), (false)))::[]))
in (FStar_List.append _149_122 _149_121)))
in (FStar_Syntax_Util.abs _149_123 outer_body ret))))))))
in (

let c_app = (let _149_124 = (mk_lid "app")
in (register env _149_124 c_app))
in (

let c_lift1 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _149_129 = (let _149_126 = (let _149_125 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _149_125))
in (_149_126)::[])
in (let _149_128 = (let _149_127 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _149_127))
in (FStar_Syntax_Util.arrow _149_129 _149_128)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _149_131 = (let _149_130 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _149_130))
in (FStar_Syntax_Syntax.gen_bv "a1" None _149_131))
in (

let ret = (let _149_136 = (let _149_135 = (let _149_134 = (let _149_133 = (let _149_132 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _149_132))
in (FStar_Syntax_Syntax.mk_Total _149_133))
in (FStar_Syntax_Util.lcomp_of_comp _149_134))
in FStar_Util.Inl (_149_135))
in Some (_149_136))
in (let _149_148 = (let _149_138 = (mk_all_implicit binders)
in (let _149_137 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::(((a1), (false)))::[]))
in (FStar_List.append _149_138 _149_137)))
in (let _149_147 = (let _149_146 = (let _149_145 = (let _149_144 = (let _149_141 = (let _149_140 = (let _149_139 = (FStar_Syntax_Syntax.bv_to_name f)
in (_149_139)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_140))
in (FStar_Syntax_Util.mk_app c_pure _149_141))
in (let _149_143 = (let _149_142 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_149_142)::[])
in (_149_144)::_149_143))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_145))
in (FStar_Syntax_Util.mk_app c_app _149_146))
in (FStar_Syntax_Util.abs _149_148 _149_147 ret)))))))))
in (

let c_lift1 = (let _149_149 = (mk_lid "lift1")
in (register env _149_149 c_lift1))
in (

let c_lift2 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t3 = (FStar_Syntax_Syntax.gen_bv "t3" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _149_157 = (let _149_154 = (let _149_150 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _149_150))
in (let _149_153 = (let _149_152 = (let _149_151 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.null_binder _149_151))
in (_149_152)::[])
in (_149_154)::_149_153))
in (let _149_156 = (let _149_155 = (FStar_Syntax_Syntax.bv_to_name t3)
in (FStar_Syntax_Syntax.mk_GTotal _149_155))
in (FStar_Syntax_Util.arrow _149_157 _149_156)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _149_159 = (let _149_158 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _149_158))
in (FStar_Syntax_Syntax.gen_bv "a1" None _149_159))
in (

let a2 = (let _149_161 = (let _149_160 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _149_160))
in (FStar_Syntax_Syntax.gen_bv "a2" None _149_161))
in (

let ret = (let _149_166 = (let _149_165 = (let _149_164 = (let _149_163 = (let _149_162 = (FStar_Syntax_Syntax.bv_to_name t3)
in (mk_gctx _149_162))
in (FStar_Syntax_Syntax.mk_Total _149_163))
in (FStar_Syntax_Util.lcomp_of_comp _149_164))
in FStar_Util.Inl (_149_165))
in Some (_149_166))
in (let _149_182 = (let _149_167 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((t3), (true)))::(((f), (false)))::(((a1), (false)))::(((a2), (false)))::[]))
in (FStar_List.append binders _149_167))
in (let _149_181 = (let _149_180 = (let _149_179 = (let _149_178 = (let _149_175 = (let _149_174 = (let _149_173 = (let _149_170 = (let _149_169 = (let _149_168 = (FStar_Syntax_Syntax.bv_to_name f)
in (_149_168)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_169))
in (FStar_Syntax_Util.mk_app c_pure _149_170))
in (let _149_172 = (let _149_171 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_149_171)::[])
in (_149_173)::_149_172))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_174))
in (FStar_Syntax_Util.mk_app c_app _149_175))
in (let _149_177 = (let _149_176 = (FStar_Syntax_Syntax.bv_to_name a2)
in (_149_176)::[])
in (_149_178)::_149_177))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_179))
in (FStar_Syntax_Util.mk_app c_app _149_180))
in (FStar_Syntax_Util.abs _149_182 _149_181 ret)))))))))))
in (

let c_lift2 = (let _149_183 = (mk_lid "lift2")
in (register env _149_183 c_lift2))
in (

let c_push = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _149_189 = (let _149_185 = (let _149_184 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _149_184))
in (_149_185)::[])
in (let _149_188 = (let _149_187 = (let _149_186 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _149_186))
in (FStar_Syntax_Syntax.mk_Total _149_187))
in (FStar_Syntax_Util.arrow _149_189 _149_188)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let ret = (let _149_199 = (let _149_198 = (let _149_197 = (let _149_196 = (let _149_195 = (let _149_194 = (let _149_191 = (let _149_190 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _149_190))
in (_149_191)::[])
in (let _149_193 = (let _149_192 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _149_192))
in (FStar_Syntax_Util.arrow _149_194 _149_193)))
in (mk_ctx _149_195))
in (FStar_Syntax_Syntax.mk_Total _149_196))
in (FStar_Syntax_Util.lcomp_of_comp _149_197))
in FStar_Util.Inl (_149_198))
in Some (_149_199))
in (

let e1 = (let _149_200 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" None _149_200))
in (

let body = (let _149_209 = (let _149_202 = (let _149_201 = (FStar_Syntax_Syntax.mk_binder e1)
in (_149_201)::[])
in (FStar_List.append gamma _149_202))
in (let _149_208 = (let _149_207 = (FStar_Syntax_Syntax.bv_to_name f)
in (let _149_206 = (let _149_205 = (let _149_203 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg _149_203))
in (let _149_204 = (args_of_binders gamma)
in (_149_205)::_149_204))
in (FStar_Syntax_Util.mk_app _149_207 _149_206)))
in (FStar_Syntax_Util.abs _149_209 _149_208 ret)))
in (let _149_212 = (let _149_211 = (mk_all_implicit binders)
in (let _149_210 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::[]))
in (FStar_List.append _149_211 _149_210)))
in (FStar_Syntax_Util.abs _149_212 body ret)))))))))
in (

let c_push = (let _149_213 = (mk_lid "push")
in (register env _149_213 c_push))
in (

let ret_tot_wp_a = (let _149_216 = (let _149_215 = (let _149_214 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.lcomp_of_comp _149_214))
in FStar_Util.Inl (_149_215))
in Some (_149_216))
in (

let mk_generic_app = (fun c -> if ((FStar_List.length binders) > 0) then begin
(let _149_221 = (let _149_220 = (let _149_219 = (args_of_binders binders)
in ((c), (_149_219)))
in FStar_Syntax_Syntax.Tm_app (_149_220))
in (mk _149_221))
end else begin
c
end)
in (

let wp_if_then_else = (

let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (let _149_239 = (let _149_222 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (FStar_List.append binders _149_222))
in (let _149_238 = (

let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_unfoldable (2)) None)
in (let _149_237 = (let _149_228 = (let _149_227 = (let _149_226 = (let _149_225 = (let _149_224 = (let _149_223 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg _149_223))
in (_149_224)::[])
in (FStar_Syntax_Util.mk_app l_ite _149_225))
in (_149_226)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_227))
in (FStar_Syntax_Util.mk_app c_lift2 _149_228))
in (let _149_236 = (let _149_235 = (let _149_234 = (let _149_233 = (let _149_231 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _149_230 = (let _149_229 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_149_229)::[])
in (_149_231)::_149_230))
in (let _149_232 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _149_233 _149_232)))
in (FStar_Syntax_Syntax.mk_Total _149_234))
in FStar_Util.Inr (_149_235))
in (FStar_Syntax_Util.ascribe _149_237 _149_236))))
in (FStar_Syntax_Util.abs _149_239 _149_238 ret_tot_wp_a))))
in (

let wp_if_then_else = (let _149_240 = (mk_lid "wp_if_then_else")
in (register env _149_240 wp_if_then_else))
in (

let wp_if_then_else = (mk_generic_app wp_if_then_else)
in (

let wp_assert = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_and = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.and_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (

let body = (let _149_251 = (let _149_250 = (let _149_249 = (let _149_246 = (let _149_245 = (let _149_244 = (let _149_243 = (let _149_242 = (let _149_241 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _149_241))
in (_149_242)::[])
in (FStar_Syntax_Util.mk_app l_and _149_243))
in (_149_244)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_245))
in (FStar_Syntax_Util.mk_app c_pure _149_246))
in (let _149_248 = (let _149_247 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_149_247)::[])
in (_149_249)::_149_248))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_250))
in (FStar_Syntax_Util.mk_app c_app _149_251))
in (let _149_253 = (let _149_252 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders _149_252))
in (FStar_Syntax_Util.abs _149_253 body ret_tot_wp_a))))))
in (

let wp_assert = (let _149_254 = (mk_lid "wp_assert")
in (register env _149_254 wp_assert))
in (

let wp_assert = (mk_generic_app wp_assert)
in (

let wp_assume = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_imp = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.imp_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)) None)
in (

let body = (let _149_265 = (let _149_264 = (let _149_263 = (let _149_260 = (let _149_259 = (let _149_258 = (let _149_257 = (let _149_256 = (let _149_255 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _149_255))
in (_149_256)::[])
in (FStar_Syntax_Util.mk_app l_imp _149_257))
in (_149_258)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_259))
in (FStar_Syntax_Util.mk_app c_pure _149_260))
in (let _149_262 = (let _149_261 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_149_261)::[])
in (_149_263)::_149_262))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_264))
in (FStar_Syntax_Util.mk_app c_app _149_265))
in (let _149_267 = (let _149_266 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders _149_266))
in (FStar_Syntax_Util.abs _149_267 body ret_tot_wp_a))))))
in (

let wp_assume = (let _149_268 = (mk_lid "wp_assume")
in (register env _149_268 wp_assume))
in (

let wp_assume = (mk_generic_app wp_assume)
in (

let wp_close = (

let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _149_272 = (let _149_270 = (let _149_269 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _149_269))
in (_149_270)::[])
in (let _149_271 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _149_272 _149_271)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let body = (let _149_281 = (let _149_280 = (let _149_279 = (let _149_273 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((FStar_Syntax_Util.tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure _149_273))
in (let _149_278 = (let _149_277 = (let _149_276 = (let _149_275 = (let _149_274 = (FStar_Syntax_Syntax.bv_to_name f)
in (_149_274)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_275))
in (FStar_Syntax_Util.mk_app c_push _149_276))
in (_149_277)::[])
in (_149_279)::_149_278))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_280))
in (FStar_Syntax_Util.mk_app c_app _149_281))
in (let _149_283 = (let _149_282 = (FStar_Syntax_Syntax.binders_of_list ((a)::(b)::(f)::[]))
in (FStar_List.append binders _149_282))
in (FStar_Syntax_Util.abs _149_283 body ret_tot_wp_a))))))
in (

let wp_close = (let _149_284 = (mk_lid "wp_close")
in (register env _149_284 wp_close))
in (

let wp_close = (mk_generic_app wp_close)
in (

let ret_tot_type = (let _149_287 = (let _149_286 = (let _149_285 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _149_285))
in FStar_Util.Inl (_149_286))
in Some (_149_287))
in (

let ret_gtot_type = (let _149_290 = (let _149_289 = (let _149_288 = (FStar_Syntax_Syntax.mk_GTotal FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _149_288))
in FStar_Util.Inl (_149_289))
in Some (_149_290))
in (

let mk_forall = (fun x body -> (let _149_301 = (let _149_300 = (let _149_299 = (let _149_298 = (let _149_297 = (let _149_296 = (let _149_295 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_295)::[])
in (FStar_Syntax_Util.abs _149_296 body ret_tot_type))
in (FStar_Syntax_Syntax.as_arg _149_297))
in (_149_298)::[])
in ((FStar_Syntax_Util.tforall), (_149_299)))
in FStar_Syntax_Syntax.Tm_app (_149_300))
in (FStar_Syntax_Syntax.mk _149_301 None FStar_Range.dummyRange)))
in (

let is_zero_order = (fun t -> (match ((let _149_304 = (FStar_Syntax_Subst.compress t)
in _149_304.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
false
end
| _57_172 -> begin
true
end))
in (

let rec mk_rel = (fun rel t x y -> (

let mk_rel = (mk_rel rel)
in (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (match ((let _149_326 = (FStar_Syntax_Subst.compress t)
in _149_326.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_181) -> begin
(rel x y)
end
| (FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(

let a = (Prims.fst binder).FStar_Syntax_Syntax.sort
in if (is_zero_order a) then begin
(

let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (

let body = (let _149_334 = (let _149_329 = (let _149_328 = (let _149_327 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _149_327))
in (_149_328)::[])
in (FStar_Syntax_Util.mk_app x _149_329))
in (let _149_333 = (let _149_332 = (let _149_331 = (let _149_330 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _149_330))
in (_149_331)::[])
in (FStar_Syntax_Util.mk_app y _149_332))
in (mk_rel b _149_334 _149_333)))
in (mk_forall a1 body)))
end else begin
(

let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (

let a2 = (FStar_Syntax_Syntax.gen_bv "a2" None a)
in (

let body = (let _149_346 = (let _149_336 = (FStar_Syntax_Syntax.bv_to_name a1)
in (let _149_335 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_rel a _149_336 _149_335)))
in (let _149_345 = (let _149_344 = (let _149_339 = (let _149_338 = (let _149_337 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _149_337))
in (_149_338)::[])
in (FStar_Syntax_Util.mk_app x _149_339))
in (let _149_343 = (let _149_342 = (let _149_341 = (let _149_340 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg _149_340))
in (_149_341)::[])
in (FStar_Syntax_Util.mk_app y _149_342))
in (mk_rel b _149_344 _149_343)))
in (FStar_Syntax_Util.mk_imp _149_346 _149_345)))
in (let _149_347 = (mk_forall a2 body)
in (mk_forall a1 _149_347)))))
end)
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::binders, comp) -> begin
(

let t = (

let _57_219 = t
in (let _149_351 = (let _149_350 = (let _149_349 = (let _149_348 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _149_348))
in (((binder)::[]), (_149_349)))
in FStar_Syntax_Syntax.Tm_arrow (_149_350))
in {FStar_Syntax_Syntax.n = _149_351; FStar_Syntax_Syntax.tk = _57_219.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_219.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_219.FStar_Syntax_Syntax.vars}))
in (mk_rel t x y))
end
| FStar_Syntax_Syntax.Tm_arrow (_57_223) -> begin
(FStar_All.failwith "unhandled arrow")
end
| _57_226 -> begin
(FStar_Syntax_Util.mk_eq t t x y)
end))))
in (

let stronger = (

let wp1 = (FStar_Syntax_Syntax.gen_bv "wp1" None wp_a)
in (

let wp2 = (FStar_Syntax_Syntax.gen_bv "wp2" None wp_a)
in (

let body = (let _149_353 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (let _149_352 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_rel FStar_Syntax_Util.mk_imp wp_a _149_353 _149_352)))
in (let _149_355 = (let _149_354 = (binders_of_list ((((a), (false)))::(((wp1), (false)))::(((wp2), (false)))::[]))
in (FStar_List.append binders _149_354))
in (FStar_Syntax_Util.abs _149_355 body ret_tot_type)))))
in (

let stronger = (let _149_356 = (mk_lid "stronger")
in (register env _149_356 stronger))
in (

let stronger = (mk_generic_app stronger)
in (

let wp_ite = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let _57_236 = (FStar_Util.prefix gamma)
in (match (_57_236) with
| (wp_args, post) -> begin
(

let k = (FStar_Syntax_Syntax.gen_bv "k" None (Prims.fst post).FStar_Syntax_Syntax.sort)
in (

let equiv = (

let k_tm = (FStar_Syntax_Syntax.bv_to_name k)
in (

let eq = (let _149_357 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst post))
in (mk_rel FStar_Syntax_Util.mk_iff k.FStar_Syntax_Syntax.sort k_tm _149_357))
in (match ((FStar_Syntax_Util.destruct_typ_as_formula eq)) with
| Some (FStar_Syntax_Util.QAll (binders, [], body)) -> begin
(

let k_app = (let _149_358 = (args_of_binders binders)
in (FStar_Syntax_Util.mk_app k_tm _149_358))
in (

let guard_free = (let _149_359 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.guard_free FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _149_359))
in (

let pat = (let _149_361 = (let _149_360 = (FStar_Syntax_Syntax.as_arg k_app)
in (_149_360)::[])
in (FStar_Syntax_Util.mk_app guard_free _149_361))
in (

let pattern_guarded_body = (let _149_367 = (let _149_366 = (let _149_365 = (let _149_364 = (let _149_363 = (let _149_362 = (FStar_Syntax_Syntax.as_arg pat)
in (_149_362)::[])
in (_149_363)::[])
in FStar_Syntax_Syntax.Meta_pattern (_149_364))
in ((body), (_149_365)))
in FStar_Syntax_Syntax.Tm_meta (_149_366))
in (mk _149_367))
in (FStar_Syntax_Util.close_forall binders pattern_guarded_body)))))
end
| _57_251 -> begin
(FStar_All.failwith "Impossible: Expected the equivalence to be a quantified formula")
end)))
in (

let body = (let _149_376 = (let _149_375 = (let _149_374 = (let _149_373 = (FStar_Syntax_Syntax.bv_to_name wp)
in (let _149_372 = (let _149_371 = (args_of_binders wp_args)
in (let _149_370 = (let _149_369 = (let _149_368 = (FStar_Syntax_Syntax.bv_to_name k)
in (FStar_Syntax_Syntax.as_arg _149_368))
in (_149_369)::[])
in (FStar_List.append _149_371 _149_370)))
in (FStar_Syntax_Util.mk_app _149_373 _149_372)))
in (FStar_Syntax_Util.mk_imp equiv _149_374))
in (FStar_Syntax_Util.mk_forall k _149_375))
in (FStar_Syntax_Util.abs gamma _149_376 ret_gtot_type))
in (let _149_378 = (let _149_377 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders _149_377))
in (FStar_Syntax_Util.abs _149_378 body ret_gtot_type)))))
end)))
in (

let wp_ite = (let _149_379 = (mk_lid "wp_ite")
in (register env _149_379 wp_ite))
in (

let null_wp = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let _57_259 = (FStar_Util.prefix gamma)
in (match (_57_259) with
| (wp_args, post) -> begin
(

let x = (FStar_Syntax_Syntax.gen_bv "x" None FStar_Syntax_Syntax.tun)
in (

let body = (let _149_384 = (let _149_383 = (FStar_All.pipe_left FStar_Syntax_Syntax.bv_to_name (Prims.fst post))
in (let _149_382 = (let _149_381 = (let _149_380 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _149_380))
in (_149_381)::[])
in (FStar_Syntax_Util.mk_app _149_383 _149_382)))
in (FStar_Syntax_Util.mk_forall x _149_384))
in (let _149_387 = (let _149_386 = (let _149_385 = (FStar_Syntax_Syntax.binders_of_list ((a)::[]))
in (FStar_List.append _149_385 gamma))
in (FStar_List.append binders _149_386))
in (FStar_Syntax_Util.abs _149_387 body ret_gtot_type))))
end)))
in (

let null_wp = (let _149_388 = (mk_lid "null_wp")
in (register env _149_388 null_wp))
in (

let wp_trivial = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let body = (let _149_398 = (let _149_397 = (let _149_396 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _149_395 = (let _149_394 = (let _149_391 = (let _149_390 = (let _149_389 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg _149_389))
in (_149_390)::[])
in (FStar_Syntax_Util.mk_app null_wp _149_391))
in (let _149_393 = (let _149_392 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_149_392)::[])
in (_149_394)::_149_393))
in (_149_396)::_149_395))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_397))
in (FStar_Syntax_Util.mk_app stronger _149_398))
in (let _149_400 = (let _149_399 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders _149_399))
in (FStar_Syntax_Util.abs _149_400 body ret_tot_type))))
in (

let wp_trivial = (let _149_401 = (mk_lid "wp_trivial")
in (register env _149_401 wp_trivial))
in (

let wp_trivial = (mk_generic_app wp_trivial)
in (

let _57_269 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(d "End Dijkstra monads for free")
end else begin
()
end
in (let _149_403 = (let _149_402 = (FStar_ST.read sigelts)
in (FStar_List.rev _149_402))
in ((_149_403), ((

let _57_271 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_271.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_271.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_271.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_271.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_271.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _57_271.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _57_271.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = (([]), (wp_if_then_else)); FStar_Syntax_Syntax.ite_wp = (([]), (wp_ite)); FStar_Syntax_Syntax.stronger = (([]), (stronger)); FStar_Syntax_Syntax.close_wp = (([]), (wp_close)); FStar_Syntax_Syntax.assert_p = (([]), (wp_assert)); FStar_Syntax_Syntax.assume_p = (([]), (wp_assume)); FStar_Syntax_Syntax.null_wp = (([]), (null_wp)); FStar_Syntax_Syntax.trivial = (([]), (wp_trivial)); FStar_Syntax_Syntax.repr = _57_271.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _57_271.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _57_271.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _57_271.FStar_Syntax_Syntax.actions}))))))))))))))))))))))))))))))))))))))))))))
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
| N (_57_281) -> begin
_57_281
end))


let ___M____0 = (fun projectee -> (match (projectee) with
| M (_57_284) -> begin
_57_284
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
| _57_291 -> begin
(FStar_All.failwith "[nm_of_comp]: impossible")
end))


let string_of_nm : nm  ->  Prims.string = (fun _57_2 -> (match (_57_2) with
| N (t) -> begin
(let _149_461 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "N[%s]" _149_461))
end
| M (t) -> begin
(let _149_462 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "M[%s]" _149_462))
end))


let is_monadic_arrow : FStar_Syntax_Syntax.term'  ->  nm = (fun n -> (match (n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_299, {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_305; FStar_Syntax_Syntax.pos = _57_303; FStar_Syntax_Syntax.vars = _57_301}) -> begin
(nm_of_comp n)
end
| _57_311 -> begin
(FStar_All.failwith "unexpected_argument: [is_monadic_arrow]")
end))


let is_monadic_comp = (fun c -> (match ((nm_of_comp c.FStar_Syntax_Syntax.n)) with
| M (_57_314) -> begin
true
end
| N (_57_317) -> begin
false
end))


let rec mk_star_to_type : (FStar_Syntax_Syntax.term'  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun mk env a -> (let _149_486 = (let _149_485 = (let _149_484 = (let _149_482 = (let _149_481 = (let _149_479 = (star_type' env a)
in (FStar_Syntax_Syntax.null_bv _149_479))
in (let _149_480 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_481), (_149_480))))
in (_149_482)::[])
in (let _149_483 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_149_484), (_149_483))))
in FStar_Syntax_Syntax.Tm_arrow (_149_485))
in (mk _149_486)))
and star_type' : env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None t.FStar_Syntax_Syntax.pos))
in (

let mk_star_to_type = (mk_star_to_type mk)
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _57_330) -> begin
(

let binders = (FStar_List.map (fun _57_335 -> (match (_57_335) with
| (bv, aqual) -> begin
(let _149_495 = (

let _57_336 = bv
in (let _149_494 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_336.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_336.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_494}))
in ((_149_495), (aqual)))
end)) binders)
in (match ((is_monadic_arrow t.FStar_Syntax_Syntax.n)) with
| N (hn) -> begin
(let _149_499 = (let _149_498 = (let _149_497 = (let _149_496 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_Total _149_496))
in ((binders), (_149_497)))
in FStar_Syntax_Syntax.Tm_arrow (_149_498))
in (mk _149_499))
end
| M (a) -> begin
(let _149_508 = (let _149_507 = (let _149_506 = (let _149_504 = (let _149_503 = (let _149_502 = (let _149_500 = (mk_star_to_type env a)
in (FStar_Syntax_Syntax.null_bv _149_500))
in (let _149_501 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_502), (_149_501))))
in (_149_503)::[])
in (FStar_List.append binders _149_504))
in (let _149_505 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_149_506), (_149_505))))
in FStar_Syntax_Syntax.Tm_arrow (_149_507))
in (mk _149_508))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let is_valid_application = (fun head -> (match ((let _149_511 = (FStar_Syntax_Subst.compress head)
in _149_511.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.option_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.either_lid)) || (let _149_512 = (FStar_Syntax_Subst.compress head)
in (FStar_Syntax_Util.is_tuple_constructor _149_512))) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uinst (_57_352) -> begin
(FStar_All.failwith "impossible (Tm_uinst)")
end
| _57_355 -> begin
false
end))
in if (is_valid_application head) then begin
(let _149_517 = (let _149_516 = (let _149_515 = (FStar_List.map (fun _57_358 -> (match (_57_358) with
| (t, qual) -> begin
(let _149_514 = (star_type' env t)
in ((_149_514), (qual)))
end)) args)
in ((head), (_149_515)))
in FStar_Syntax_Syntax.Tm_app (_149_516))
in (mk _149_517))
end else begin
(let _149_520 = (let _149_519 = (let _149_518 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "For now, only [either] and [option] are supported in the definition language (got: %s)" _149_518))
in FStar_Syntax_Syntax.Err (_149_519))
in (Prims.raise _149_520))
end)
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_abs (binders, repr, something) -> begin
(

let _57_378 = (FStar_Syntax_Subst.open_term binders repr)
in (match (_57_378) with
| (binders, repr) -> begin
(

let env = (

let _57_379 = env
in (let _149_521 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _149_521; subst = _57_379.subst; tc_const = _57_379.tc_const}))
in (

let repr = (star_type' env repr)
in (FStar_Syntax_Util.abs binders repr something)))
end))
end
| (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_match (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _149_524 = (let _149_523 = (let _149_522 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "The following term is outside of the definition language: %s" _149_522))
in FStar_Syntax_Syntax.Err (_149_523))
in (Prims.raise _149_524))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_412) -> begin
(FStar_All.failwith "impossible")
end)))))


let is_monadic : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  Prims.bool = (fun _57_3 -> (match (_57_3) with
| None -> begin
(FStar_All.failwith "un-annotated lambda?!")
end
| (Some (FStar_Util.Inl ({FStar_Syntax_Syntax.eff_name = lid; FStar_Syntax_Syntax.res_typ = _; FStar_Syntax_Syntax.cflags = _; FStar_Syntax_Syntax.comp = _}))) | (Some (FStar_Util.Inr (lid))) -> begin
(FStar_Ident.lid_equals lid FStar_Syntax_Const.monadic_lid)
end))


let rec is_C : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match ((let _149_532 = (FStar_Syntax_Subst.compress t)
in _149_532.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) when (FStar_Syntax_Util.is_tuple_constructor head) -> begin
(

let r = (let _149_534 = (let _149_533 = (FStar_List.hd args)
in (Prims.fst _149_533))
in (is_C _149_534))
in if r then begin
(

let _57_438 = if (not ((FStar_List.for_all (fun _57_437 -> (match (_57_437) with
| (h, _57_436) -> begin
(is_C h)
end)) args))) then begin
(FStar_All.failwith "not a C (A * C)")
end else begin
()
end
in true)
end else begin
(

let _57_444 = if (not ((FStar_List.for_all (fun _57_443 -> (match (_57_443) with
| (h, _57_442) -> begin
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

let _57_452 = if (is_C t) then begin
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
| _57_472 -> begin
false
end))


let mk_return : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let p_type = (mk_star_to_type mk env t)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'" None p_type)
in (

let body = (let _149_550 = (let _149_549 = (let _149_548 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _149_547 = (let _149_546 = (let _149_545 = (FStar_Syntax_Syntax.as_implicit false)
in ((e), (_149_545)))
in (_149_546)::[])
in ((_149_548), (_149_547))))
in FStar_Syntax_Syntax.Tm_app (_149_549))
in (mk _149_550))
in (let _149_552 = (let _149_551 = (FStar_Syntax_Syntax.mk_binder p)
in (_149_551)::[])
in (FStar_Syntax_Util.abs _149_552 body None)))))))


let is_unknown : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun _57_4 -> (match (_57_4) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| _57_484 -> begin
false
end))


let rec check : env  ->  FStar_Syntax_Syntax.term  ->  nm  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e context_nm -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let return_if = (fun _57_494 -> (match (_57_494) with
| (rec_nm, s_e, u_e) -> begin
(

let check = (fun t1 t2 -> if ((not ((is_unknown t2.FStar_Syntax_Syntax.n))) && (not ((let _149_606 = (FStar_TypeChecker_Rel.teq env.env t1 t2)
in (FStar_TypeChecker_Rel.is_trivial _149_606))))) then begin
(let _149_611 = (let _149_610 = (let _149_609 = (FStar_Syntax_Print.term_to_string e)
in (let _149_608 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_607 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check]: the expression [%s] has type [%s] but should have type [%s]" _149_609 _149_608 _149_607))))
in FStar_Syntax_Syntax.Err (_149_610))
in (Prims.raise _149_611))
end else begin
()
end)
in (match (((rec_nm), (context_nm))) with
| ((N (t1), N (t2))) | ((M (t1), M (t2))) -> begin
(

let _57_506 = (check t1 t2)
in ((rec_nm), (s_e), (u_e)))
end
| (N (t1), M (t2)) -> begin
(

let _57_513 = (check t1 t2)
in (let _149_612 = (mk_return env t1 s_e)
in ((M (t1)), (_149_612), (u_e))))
end
| (M (t1), N (t2)) -> begin
(let _149_617 = (let _149_616 = (let _149_615 = (FStar_Syntax_Print.term_to_string e)
in (let _149_614 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_613 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]" _149_615 _149_614 _149_613))))
in FStar_Syntax_Syntax.Err (_149_616))
in (Prims.raise _149_617))
end))
end))
in (

let ensure_m = (fun env e2 -> (

let strip_m = (fun _57_5 -> (match (_57_5) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_530 -> begin
(FStar_All.failwith "impossible")
end))
in (match (context_nm) with
| N (t) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren\'t"), (e2.FStar_Syntax_Syntax.pos)))))
end
| M (_57_535) -> begin
(let _149_624 = (check env e2 context_nm)
in (strip_m _149_624))
end)))
in (match ((let _149_625 = (FStar_Syntax_Subst.compress e)
in _149_625.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
(let _149_626 = (infer env e)
in (return_if _149_626))
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
| FStar_Syntax_Syntax.Tm_let (_57_586) -> begin
(let _149_634 = (let _149_633 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_let %s" _149_633))
in (FStar_All.failwith _149_634))
end
| FStar_Syntax_Syntax.Tm_type (_57_589) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_592) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_57_595) -> begin
(let _149_636 = (let _149_635 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_refine %s" _149_635))
in (FStar_All.failwith _149_636))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_598) -> begin
(let _149_638 = (let _149_637 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_uvar %s" _149_637))
in (FStar_All.failwith _149_638))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_601) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _149_643 = (let _149_642 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_unknown %s" _149_642))
in (FStar_All.failwith _149_643))
end)))))
and infer : env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.env)
in (match ((let _149_649 = (FStar_Syntax_Subst.compress e)
in _149_649.FStar_Syntax_Syntax.n)) with
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

let _57_621 = env
in (let _149_650 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _149_650; subst = _57_621.subst; tc_const = _57_621.tc_const}))
in (

let s_binders = (FStar_List.map (fun _57_626 -> (match (_57_626) with
| (bv, qual) -> begin
(

let sort = (star_type' env bv.FStar_Syntax_Syntax.sort)
in (((

let _57_628 = bv
in {FStar_Syntax_Syntax.ppname = _57_628.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_628.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (qual)))
end)) binders)
in (

let _57_650 = (FStar_List.fold_left (fun _57_633 _57_636 -> (match (((_57_633), (_57_636))) with
| ((env, acc), (bv, qual)) -> begin
(

let c = bv.FStar_Syntax_Syntax.sort
in if (is_C c) then begin
(

let xw = (let _149_654 = (star_type' env c)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "^w") None _149_654))
in (

let x = (

let _57_639 = bv
in (let _149_656 = (let _149_655 = (FStar_Syntax_Syntax.bv_to_name xw)
in (trans_F_ env c _149_655))
in {FStar_Syntax_Syntax.ppname = _57_639.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_639.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_656}))
in (

let env = (

let _57_642 = env
in (let _149_660 = (let _149_659 = (let _149_658 = (let _149_657 = (FStar_Syntax_Syntax.bv_to_name xw)
in ((bv), (_149_657)))
in FStar_Syntax_Syntax.NT (_149_658))
in (_149_659)::env.subst)
in {env = _57_642.env; subst = _149_660; tc_const = _57_642.tc_const}))
in (let _149_664 = (let _149_663 = (FStar_Syntax_Syntax.mk_binder x)
in (let _149_662 = (let _149_661 = (FStar_Syntax_Syntax.mk_binder xw)
in (_149_661)::acc)
in (_149_663)::_149_662))
in ((env), (_149_664))))))
end else begin
(

let x = (

let _57_645 = bv
in (let _149_665 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_645.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_645.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_665}))
in (let _149_667 = (let _149_666 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_666)::acc)
in ((env), (_149_667))))
end)
end)) ((env), ([])) binders)
in (match (_57_650) with
| (env, u_binders) -> begin
(

let u_binders = (FStar_List.rev u_binders)
in (

let _57_660 = (

let check_what = if (is_monadic what) then begin
check_m
end else begin
check_n
end
in (

let _57_656 = (check_what env body)
in (match (_57_656) with
| (t, s_body, u_body) -> begin
(let _149_673 = (let _149_672 = if (is_monadic what) then begin
M (t)
end else begin
N (t)
end
in (comp_of_nm _149_672))
in ((_149_673), (s_body), (u_body)))
end)))
in (match (_57_660) with
| (comp, s_body, u_body) -> begin
(

let t = (

let binders = (FStar_List.map (fun _57_664 -> (match (_57_664) with
| (bv, _57_663) -> begin
(let _149_675 = (FStar_Syntax_Syntax.null_bv bv.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_binder _149_675))
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
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = {FStar_Syntax_Syntax.v = lid; FStar_Syntax_Syntax.ty = _57_681; FStar_Syntax_Syntax.p = _57_679}; FStar_Syntax_Syntax.fv_delta = _57_677; FStar_Syntax_Syntax.fv_qual = _57_675}) -> begin
(

let _57_689 = (FStar_TypeChecker_Env.lookup_lid env.env lid)
in (match (_57_689) with
| (_57_687, t) -> begin
(

let txt = (FStar_Ident.text_of_lid lid)
in (

let allowed_prefixes = ("Mktuple")::("Left")::("Right")::("Some")::("None")::[]
in if (FStar_List.existsb (fun s -> (FStar_Util.starts_with txt (Prims.strcat "Prims." s))) allowed_prefixes) then begin
(let _149_678 = (let _149_677 = (normalize t)
in N (_149_677))
in ((_149_678), (e), (e)))
end else begin
(let _149_680 = (let _149_679 = (FStar_Util.format1 "The %s constructor has not been whitelisted for the definition language; if this is a function application, consider using [inline]" txt)
in FStar_Syntax_Syntax.Err (_149_679))
in (Prims.raise _149_680))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_700 = (check_n env head)
in (match (_57_700) with
| (t_head, s_head, u_head) -> begin
(

let is_arrow = (fun t -> (match ((let _149_683 = (FStar_Syntax_Subst.compress t)
in _149_683.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_704) -> begin
true
end
| _57_707 -> begin
false
end))
in (

let rec flatten = (fun t -> (match ((let _149_686 = (FStar_Syntax_Subst.compress t)
in _149_686.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (t); FStar_Syntax_Syntax.tk = _57_716; FStar_Syntax_Syntax.pos = _57_714; FStar_Syntax_Syntax.vars = _57_712}) when (is_arrow t) -> begin
(

let _57_724 = (flatten t)
in (match (_57_724) with
| (binders', comp) -> begin
(((FStar_List.append binders binders')), (comp))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
((binders), (comp))
end
| _57_730 -> begin
(let _149_689 = (let _149_688 = (let _149_687 = (FStar_Syntax_Print.term_to_string t_head)
in (FStar_Util.format1 "%s: not a function type" _149_687))
in FStar_Syntax_Syntax.Err (_149_688))
in (Prims.raise _149_689))
end))
in (

let _57_733 = (flatten t_head)
in (match (_57_733) with
| (binders, comp) -> begin
(

let n = (FStar_List.length binders)
in (

let n' = (FStar_List.length args)
in (

let _57_736 = if ((FStar_List.length binders) < (FStar_List.length args)) then begin
(let _149_694 = (let _149_693 = (let _149_692 = (FStar_Util.string_of_int n)
in (let _149_691 = (FStar_Util.string_of_int (n' - n))
in (let _149_690 = (FStar_Util.string_of_int n)
in (FStar_Util.format3 "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments." _149_692 _149_691 _149_690))))
in FStar_Syntax_Syntax.Err (_149_693))
in (Prims.raise _149_694))
end else begin
()
end
in (

let _57_740 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (_57_740) with
| (binders, comp) -> begin
(

let rec final_type = (fun subst _57_745 args -> (match (_57_745) with
| (binders, comp) -> begin
(match (((binders), (args))) with
| ([], []) -> begin
(let _149_702 = (let _149_701 = (FStar_Syntax_Subst.subst_comp subst comp)
in _149_701.FStar_Syntax_Syntax.n)
in (nm_of_comp _149_702))
end
| (binders, []) -> begin
(match ((let _149_705 = (let _149_704 = (let _149_703 = (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))))
in (FStar_Syntax_Subst.subst subst _149_703))
in (FStar_Syntax_Subst.compress _149_704))
in _149_705.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(let _149_709 = (let _149_708 = (let _149_707 = (let _149_706 = (FStar_Syntax_Subst.close_comp binders comp)
in ((binders), (_149_706)))
in FStar_Syntax_Syntax.Tm_arrow (_149_707))
in (mk _149_708))
in N (_149_709))
end
| _57_758 -> begin
(FStar_All.failwith "wat?")
end)
end
| ([], (_57_763)::_57_761) -> begin
(FStar_All.failwith "just checked that?!")
end
| (((bv, _57_769))::binders, ((arg, _57_775))::args) -> begin
(final_type ((FStar_Syntax_Syntax.NT (((bv), (arg))))::subst) ((binders), (comp)) args)
end)
end))
in (

let final_type = (final_type [] ((binders), (comp)) args)
in (

let _57_800 = (let _149_724 = (FStar_List.map2 (fun _57_783 _57_786 -> (match (((_57_783), (_57_786))) with
| ((bv, _57_782), (arg, q)) -> begin
(match ((let _149_712 = (FStar_Syntax_Subst.compress bv.FStar_Syntax_Syntax.sort)
in _149_712.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_788) -> begin
(

let arg = ((arg), (q))
in ((arg), ((arg)::[])))
end
| _57_792 -> begin
(

let _57_797 = (check_n env arg)
in (match (_57_797) with
| (_57_794, s_arg, u_arg) -> begin
(let _149_723 = (let _149_713 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_arg), (_149_713)))
in (let _149_722 = if (is_C bv.FStar_Syntax_Syntax.sort) then begin
(let _149_719 = (let _149_715 = (FStar_Syntax_Subst.subst env.subst s_arg)
in (let _149_714 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_715), (_149_714))))
in (let _149_718 = (let _149_717 = (let _149_716 = (FStar_Syntax_Syntax.as_implicit false)
in ((u_arg), (_149_716)))
in (_149_717)::[])
in (_149_719)::_149_718))
end else begin
(let _149_721 = (let _149_720 = (FStar_Syntax_Syntax.as_implicit false)
in ((u_arg), (_149_720)))
in (_149_721)::[])
end
in ((_149_723), (_149_722))))
end))
end)
end)) binders args)
in (FStar_List.split _149_724))
in (match (_57_800) with
| (s_args, u_args) -> begin
(

let u_args = (FStar_List.flatten u_args)
in (let _149_726 = (mk (FStar_Syntax_Syntax.Tm_app (((s_head), (s_args)))))
in (let _149_725 = (mk (FStar_Syntax_Syntax.Tm_app (((u_head), (u_args)))))
in ((final_type), (_149_726), (_149_725)))))
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
(let _149_728 = (let _149_727 = (env.tc_const c)
in N (_149_727))
in ((_149_728), (e), (e)))
end
| FStar_Syntax_Syntax.Tm_let (_57_831) -> begin
(let _149_730 = (let _149_729 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_let %s" _149_729))
in (FStar_All.failwith _149_730))
end
| FStar_Syntax_Syntax.Tm_type (_57_834) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_837) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_57_840) -> begin
(let _149_732 = (let _149_731 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_refine %s" _149_731))
in (FStar_All.failwith _149_732))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_843) -> begin
(let _149_734 = (let _149_733 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_uvar %s" _149_733))
in (FStar_All.failwith _149_734))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_846) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _149_739 = (let _149_738 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_unknown %s" _149_738))
in (FStar_All.failwith _149_739))
end))))
and mk_match : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e0 branches f -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e0.FStar_Syntax_Syntax.pos))
in (

let _57_859 = (check_n env e0)
in (match (_57_859) with
| (_57_856, s_e0, u_e0) -> begin
(

let _57_876 = (let _149_755 = (FStar_List.map (fun b -> (match ((FStar_Syntax_Subst.open_branch b)) with
| (pat, None, body) -> begin
(

let env = (

let _57_865 = env
in (let _149_754 = (let _149_753 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env.env _149_753))
in {env = _149_754; subst = _57_865.subst; tc_const = _57_865.tc_const}))
in (

let _57_871 = (f env body)
in (match (_57_871) with
| (nm, s_body, u_body) -> begin
((nm), (((pat), (None), (((s_body), (u_body), (body))))))
end)))
end
| _57_873 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("No when clauses in the definition language")))
end)) branches)
in (FStar_List.split _149_755))
in (match (_57_876) with
| (nms, branches) -> begin
(

let t1 = (match ((FStar_List.hd nms)) with
| (M (t1)) | (N (t1)) -> begin
t1
end)
in (

let has_m = (FStar_List.existsb (fun _57_6 -> (match (_57_6) with
| M (_57_883) -> begin
true
end
| _57_886 -> begin
false
end)) nms)
in (

let _57_920 = (let _149_759 = (FStar_List.map2 (fun nm _57_895 -> (match (_57_895) with
| (pat, guard, (s_body, u_body, original_body)) -> begin
(match (((nm), (has_m))) with
| ((N (t2), false)) | ((M (t2), true)) -> begin
((nm), (((pat), (guard), (s_body))), (((pat), (guard), (u_body))))
end
| (N (t2), true) -> begin
(

let _57_911 = (check env original_body (M (t2)))
in (match (_57_911) with
| (_57_908, s_body, u_body) -> begin
((M (t2)), (((pat), (guard), (s_body))), (((pat), (guard), (u_body))))
end))
end
| (M (_57_913), false) -> begin
(FStar_All.failwith "impossible")
end)
end)) nms branches)
in (FStar_List.unzip3 _149_759))
in (match (_57_920) with
| (nms, s_branches, u_branches) -> begin
(

let s_branches = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let t1_star = if has_m then begin
(let _149_764 = (let _149_762 = (let _149_761 = (let _149_760 = (mk_star_to_type mk env t1)
in (FStar_Syntax_Syntax.new_bv None _149_760))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _149_761))
in (_149_762)::[])
in (let _149_763 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _149_764 _149_763)))
end else begin
t1
end
in (let _149_769 = (let _149_767 = (let _149_766 = (let _149_765 = (mk (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches)))))
in ((_149_765), (FStar_Util.Inl (t1_star)), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (_149_766))
in (mk _149_767))
in (let _149_768 = (mk (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches)))))
in ((if has_m then begin
M (t1)
end else begin
N (t1)
end), (_149_769), (_149_768)))))))
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

let x_binders = (let _149_789 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_789)::[])
in (

let _57_936 = (FStar_Syntax_Subst.open_term x_binders e2)
in (match (_57_936) with
| (x_binders, e2) -> begin
(match ((infer env e1)) with
| (N (t1), s_e1, u_e1) -> begin
(

let env = (

let _57_942 = env
in (let _149_790 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_944 = x
in {FStar_Syntax_Syntax.ppname = _57_944.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_944.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _149_790; subst = _57_942.subst; tc_const = _57_942.tc_const}))
in (

let _57_950 = (proceed env e2)
in (match (_57_950) with
| (nm_rec, s_e2, u_e2) -> begin
(let _149_798 = (let _149_793 = (let _149_792 = (let _149_791 = (FStar_Syntax_Subst.close x_binders s_e2)
in ((((false), (((

let _57_951 = binding
in {FStar_Syntax_Syntax.lbname = _57_951.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_951.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_951.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_951.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = s_e1}))::[]))), (_149_791)))
in FStar_Syntax_Syntax.Tm_let (_149_792))
in (mk _149_793))
in (let _149_797 = (let _149_796 = (let _149_795 = (let _149_794 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _57_953 = binding
in {FStar_Syntax_Syntax.lbname = _57_953.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_953.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_953.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_953.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_149_794)))
in FStar_Syntax_Syntax.Tm_let (_149_795))
in (mk _149_796))
in ((nm_rec), (_149_798), (_149_797))))
end)))
end
| (M (t1), s_e1, u_e1) -> begin
(

let env = (

let _57_960 = env
in (let _149_799 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_962 = x
in {FStar_Syntax_Syntax.ppname = _57_962.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_962.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _149_799; subst = _57_960.subst; tc_const = _57_960.tc_const}))
in (

let _57_968 = (ensure_m env e2)
in (match (_57_968) with
| (t2, s_e2, u_e2) -> begin
(

let p_type = (mk_star_to_type mk env t2)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" None p_type)
in (

let s_e2 = (let _149_805 = (let _149_804 = (let _149_803 = (let _149_802 = (let _149_801 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _149_800 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_801), (_149_800))))
in (_149_802)::[])
in ((s_e2), (_149_803)))
in FStar_Syntax_Syntax.Tm_app (_149_804))
in (mk _149_805))
in (

let s_e2 = (FStar_Syntax_Util.abs x_binders s_e2 None)
in (

let body = (let _149_810 = (let _149_809 = (let _149_808 = (let _149_807 = (let _149_806 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_e2), (_149_806)))
in (_149_807)::[])
in ((s_e1), (_149_808)))
in FStar_Syntax_Syntax.Tm_app (_149_809))
in (mk _149_810))
in (let _149_817 = (let _149_812 = (let _149_811 = (FStar_Syntax_Syntax.mk_binder p)
in (_149_811)::[])
in (FStar_Syntax_Util.abs _149_812 body None))
in (let _149_816 = (let _149_815 = (let _149_814 = (let _149_813 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _57_974 = binding
in {FStar_Syntax_Syntax.lbname = _57_974.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_974.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_974.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_974.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_149_813)))
in FStar_Syntax_Syntax.Tm_let (_149_814))
in (mk _149_815))
in ((M (t2)), (_149_817), (_149_816)))))))))
end)))
end)
end)))))))
and check_n : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _149_820 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in N (_149_820))
in (match ((check env e mn)) with
| (N (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_985 -> begin
(FStar_All.failwith "[check_n]: impossible")
end)))
and check_m : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _149_823 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in M (_149_823))
in (match ((check env e mn)) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_995 -> begin
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
and trans_F_ : env_  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> (

let _57_1017 = if (not ((is_C c))) then begin
(FStar_All.failwith "not a C")
end else begin
()
end
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos))
in (match ((let _149_832 = (FStar_Syntax_Subst.compress c)
in _149_832.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_1027 = (FStar_Syntax_Util.head_and_args wp)
in (match (_57_1027) with
| (wp_head, wp_args) -> begin
(

let _57_1028 = if ((not (((FStar_List.length wp_args) = (FStar_List.length args)))) || (not ((let _149_833 = (FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length wp_args) FStar_Range.dummyRange)
in (FStar_Syntax_Util.is_constructor wp_head _149_833))))) then begin
(FStar_All.failwith "mismatch")
end else begin
()
end
in (let _149_840 = (let _149_839 = (let _149_838 = (FStar_List.map2 (fun _57_1033 _57_1037 -> (match (((_57_1033), (_57_1037))) with
| ((arg, _57_1032), (wp_arg, _57_1036)) -> begin
(let _149_837 = (trans_F_ env arg wp_arg)
in (let _149_836 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_837), (_149_836))))
end)) args wp_args)
in ((head), (_149_838)))
in FStar_Syntax_Syntax.Tm_app (_149_839))
in (mk _149_840)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let binders = (FStar_Syntax_Util.name_binders binders)
in (

let binders = (FStar_Syntax_Subst.open_binders binders)
in (

let _57_1046 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (_57_1046) with
| (binders, comp) -> begin
(

let _57_1055 = (let _149_852 = (FStar_List.map (fun _57_1049 -> (match (_57_1049) with
| (bv, q) -> begin
(

let h = bv.FStar_Syntax_Syntax.sort
in if (is_C h) then begin
(

let w' = (let _149_842 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-w\'") None _149_842))
in (let _149_848 = (let _149_847 = (FStar_Syntax_Syntax.mk_binder w')
in (let _149_846 = (let _149_845 = (let _149_844 = (let _149_843 = (FStar_Syntax_Syntax.bv_to_name bv)
in (trans_F_ env h _149_843))
in (FStar_Syntax_Syntax.null_binder _149_844))
in (_149_845)::[])
in (_149_847)::_149_846))
in ((w'), (_149_848))))
end else begin
(

let x = (let _149_849 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-x") None _149_849))
in (let _149_851 = (let _149_850 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_850)::[])
in ((x), (_149_851))))
end)
end)) binders)
in (FStar_List.split _149_852))
in (match (_57_1055) with
| (bvs, binders) -> begin
(

let binders = (FStar_List.flatten binders)
in (

let app = (let _149_858 = (let _149_857 = (let _149_856 = (FStar_List.map (fun bv -> (let _149_855 = (FStar_Syntax_Syntax.bv_to_name bv)
in (let _149_854 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_855), (_149_854))))) bvs)
in ((wp), (_149_856)))
in FStar_Syntax_Syntax.Tm_app (_149_857))
in (mk _149_858))
in (

let comp = (let _149_860 = (type_of_comp comp)
in (let _149_859 = (is_monadic_comp comp)
in (trans_G env _149_860 _149_859 app)))
in (

let comp = (FStar_Syntax_Subst.close_comp binders comp)
in (

let binders = (FStar_Syntax_Subst.close_binders binders)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp))))))))))
end))
end))))
end
| _57_1063 -> begin
(FStar_All.failwith "impossible trans_F_")
end))))
and trans_G : env_  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env h is_monadic wp -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None h.FStar_Syntax_Syntax.pos))
in if is_monadic then begin
(let _149_871 = (let _149_870 = (star_type' env h)
in (let _149_869 = (let _149_868 = (let _149_867 = (FStar_Syntax_Syntax.as_implicit false)
in ((wp), (_149_867)))
in (_149_868)::[])
in {FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _149_870; FStar_Syntax_Syntax.effect_args = _149_869; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp _149_871))
end else begin
(let _149_872 = (trans_F_ env h wp)
in (FStar_Syntax_Syntax.mk_Total _149_872))
end))


let n : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.NoInline)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]))


let star_type : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _149_879 = (n env.env t)
in (star_type' env _149_879)))


let star_expr : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env t -> (let _149_884 = (n env.env t)
in (check_n env _149_884)))


let trans_F : env_  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> (let _149_892 = (n env.env c)
in (let _149_891 = (n env.env wp)
in (trans_F_ env _149_892 _149_891))))




