
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

let _57_18 = (d "Elaborating extra WP combinators")
in (

let _57_20 = (let _149_14 = (FStar_Syntax_Print.term_to_string wp_a)
in (FStar_Util.print1 "wp_a is: %s\n" _149_14))
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

let _57_41 = (let _149_23 = (let _149_22 = (FStar_Syntax_Print.binders_to_string ", " gamma)
in (FStar_Util.format1 "Gamma is %s\n" _149_22))
in (d _149_23))
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

let _57_269 = (d "End Dijkstra monads for free")
in (let _149_403 = (let _149_402 = (FStar_ST.read sigelts)
in (FStar_List.rev _149_402))
in ((_149_403), ((

let _57_271 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_271.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_271.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_271.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_271.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_271.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _57_271.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _57_271.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = (([]), (wp_if_then_else)); FStar_Syntax_Syntax.ite_wp = (([]), (wp_ite)); FStar_Syntax_Syntax.stronger = (([]), (stronger)); FStar_Syntax_Syntax.close_wp = (([]), (wp_close)); FStar_Syntax_Syntax.assert_p = (([]), (wp_assert)); FStar_Syntax_Syntax.assume_p = (([]), (wp_assume)); FStar_Syntax_Syntax.null_wp = (([]), (null_wp)); FStar_Syntax_Syntax.trivial = (([]), (wp_trivial)); FStar_Syntax_Syntax.repr = _57_271.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _57_271.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _57_271.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _57_271.FStar_Syntax_Syntax.actions}))))))))))))))))))))))))))))))))))))))))))))
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
| N (_57_282) -> begin
_57_282
end))


let ___M____0 = (fun projectee -> (match (projectee) with
| M (_57_285) -> begin
_57_285
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
| _57_292 -> begin
(FStar_All.failwith "[nm_of_comp]: impossible")
end))


let string_of_nm : nm  ->  Prims.string = (fun _57_2 -> (match (_57_2) with
| N (t) -> begin
(let _149_464 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "N[%s]" _149_464))
end
| M (t) -> begin
(let _149_465 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "M[%s]" _149_465))
end))


let is_monadic_arrow : FStar_Syntax_Syntax.term'  ->  nm = (fun n -> (match (n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_300, {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_306; FStar_Syntax_Syntax.pos = _57_304; FStar_Syntax_Syntax.vars = _57_302}) -> begin
(nm_of_comp n)
end
| _57_312 -> begin
(FStar_All.failwith "unexpected_argument: [is_monadic_arrow]")
end))


let is_monadic_comp = (fun c -> (match ((nm_of_comp c.FStar_Syntax_Syntax.n)) with
| M (_57_315) -> begin
true
end
| N (_57_318) -> begin
false
end))


let rec mk_star_to_type : (FStar_Syntax_Syntax.term'  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun mk env a -> (let _149_489 = (let _149_488 = (let _149_487 = (let _149_485 = (let _149_484 = (let _149_482 = (star_type env a)
in (FStar_Syntax_Syntax.null_bv _149_482))
in (let _149_483 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_484), (_149_483))))
in (_149_485)::[])
in (let _149_486 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_149_487), (_149_486))))
in FStar_Syntax_Syntax.Tm_arrow (_149_488))
in (mk _149_489)))
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
| FStar_Syntax_Syntax.Tm_arrow (binders, _57_333) -> begin
(

let binders = (FStar_List.map (fun _57_338 -> (match (_57_338) with
| (bv, aqual) -> begin
(let _149_499 = (

let _57_339 = bv
in (let _149_498 = (star_type env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_339.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_339.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_498}))
in ((_149_499), (aqual)))
end)) binders)
in (match ((is_monadic_arrow t.FStar_Syntax_Syntax.n)) with
| N (hn) -> begin
(let _149_503 = (let _149_502 = (let _149_501 = (let _149_500 = (star_type env hn)
in (FStar_Syntax_Syntax.mk_Total _149_500))
in ((binders), (_149_501)))
in FStar_Syntax_Syntax.Tm_arrow (_149_502))
in (mk _149_503))
end
| M (a) -> begin
(let _149_512 = (let _149_511 = (let _149_510 = (let _149_508 = (let _149_507 = (let _149_506 = (let _149_504 = (mk_star_to_type env a)
in (FStar_Syntax_Syntax.null_bv _149_504))
in (let _149_505 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_506), (_149_505))))
in (_149_507)::[])
in (FStar_List.append binders _149_508))
in (let _149_509 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_149_510), (_149_509))))
in FStar_Syntax_Syntax.Tm_arrow (_149_511))
in (mk _149_512))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let is_valid_application = (fun head -> (match ((let _149_515 = (FStar_Syntax_Subst.compress head)
in _149_515.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.option_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.either_lid)) || (let _149_516 = (FStar_Syntax_Subst.compress head)
in (FStar_Syntax_Util.is_tuple_constructor _149_516))) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uinst (_57_355) -> begin
(FStar_All.failwith "impossible")
end
| _57_358 -> begin
false
end))
in if (is_valid_application head) then begin
(let _149_521 = (let _149_520 = (let _149_519 = (FStar_List.map (fun _57_361 -> (match (_57_361) with
| (t, qual) -> begin
(let _149_518 = (star_type env t)
in ((_149_518), (qual)))
end)) args)
in ((head), (_149_519)))
in FStar_Syntax_Syntax.Tm_app (_149_520))
in (mk _149_521))
end else begin
(let _149_524 = (let _149_523 = (let _149_522 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "For now, only [either] and [option] are supported in the definition language (got: %s)" _149_522))
in FStar_Syntax_Syntax.Err (_149_523))
in (Prims.raise _149_524))
end)
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_abs (binders, repr, something) -> begin
(

let _57_381 = (FStar_Syntax_Subst.open_term binders repr)
in (match (_57_381) with
| (binders, repr) -> begin
(

let env = (

let _57_382 = env
in (let _149_525 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _149_525; definitions = _57_382.definitions; subst = _57_382.subst; tc_const = _57_382.tc_const}))
in (

let repr = (star_type env repr)
in (FStar_Syntax_Util.abs binders repr something)))
end))
end
| (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_match (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _149_528 = (let _149_527 = (let _149_526 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "The following term is outside of the definition language: %s" _149_526))
in FStar_Syntax_Syntax.Err (_149_527))
in (Prims.raise _149_528))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_415) -> begin
(FStar_All.failwith "impossible")
end)))))))


let star_definition = (fun env t f -> (match ((let _149_541 = (FStar_Syntax_Util.un_uinst t)
in _149_541.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = lid; FStar_Syntax_Syntax.fv_delta = _57_423; FStar_Syntax_Syntax.fv_qual = _57_421}) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.NoInline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.env t)
in (

let _57_428 = (FStar_Util.print1 "Recording definition of %s\n" (FStar_Ident.text_of_lid lid.FStar_Syntax_Syntax.v))
in (

let _57_432 = (f env t)
in (match (_57_432) with
| (keep, ret) -> begin
(((

let _57_433 = env
in {env = _57_433.env; definitions = (((lid.FStar_Syntax_Syntax.v), (keep)))::env.definitions; subst = _57_433.subst; tc_const = _57_433.tc_const})), (ret))
end))))
end
| _57_436 -> begin
(let _149_545 = (let _149_544 = (let _149_543 = (FStar_Syntax_Print.term_to_string t)
in (let _149_542 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format2 "Ill-formed definition: %s (%s)" _149_543 _149_542)))
in FStar_Syntax_Syntax.Err (_149_544))
in (Prims.raise _149_545))
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


let rec is_C : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match ((let _149_556 = (FStar_Syntax_Subst.compress t)
in _149_556.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) when (FStar_Syntax_Util.is_tuple_constructor head) -> begin
(

let r = (let _149_558 = (let _149_557 = (FStar_List.hd args)
in (Prims.fst _149_557))
in (is_C _149_558))
in if r then begin
(

let _57_466 = if (not ((FStar_List.for_all (fun _57_465 -> (match (_57_465) with
| (h, _57_464) -> begin
(is_C h)
end)) args))) then begin
(FStar_All.failwith "not a C (A * C)")
end else begin
()
end
in true)
end else begin
(

let _57_472 = if (not ((FStar_List.for_all (fun _57_471 -> (match (_57_471) with
| (h, _57_470) -> begin
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

let _57_480 = if (is_C t) then begin
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
| _57_500 -> begin
false
end))


let mk_return : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let p_type = (mk_star_to_type mk env t)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'" None p_type)
in (

let body = (let _149_574 = (let _149_573 = (let _149_572 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _149_571 = (let _149_570 = (let _149_569 = (FStar_Syntax_Syntax.as_implicit false)
in ((e), (_149_569)))
in (_149_570)::[])
in ((_149_572), (_149_571))))
in FStar_Syntax_Syntax.Tm_app (_149_573))
in (mk _149_574))
in (let _149_576 = (let _149_575 = (FStar_Syntax_Syntax.mk_binder p)
in (_149_575)::[])
in (FStar_Syntax_Util.abs _149_576 body None)))))))


let is_unknown : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun _57_4 -> (match (_57_4) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| _57_512 -> begin
false
end))


let rec check : env  ->  FStar_Syntax_Syntax.term  ->  nm  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e context_nm -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let return_if = (fun _57_522 -> (match (_57_522) with
| (rec_nm, s_e, u_e) -> begin
(

let check = (fun t1 t2 -> if ((not ((is_unknown t2.FStar_Syntax_Syntax.n))) && (not ((let _149_630 = (FStar_TypeChecker_Rel.teq env.env t1 t2)
in (FStar_TypeChecker_Rel.is_trivial _149_630))))) then begin
(let _149_635 = (let _149_634 = (let _149_633 = (FStar_Syntax_Print.term_to_string e)
in (let _149_632 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_631 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check]: the expression [%s] has type [%s] but should have type [%s]" _149_633 _149_632 _149_631))))
in FStar_Syntax_Syntax.Err (_149_634))
in (Prims.raise _149_635))
end else begin
()
end)
in (match (((rec_nm), (context_nm))) with
| ((N (t1), N (t2))) | ((M (t1), M (t2))) -> begin
(

let _57_534 = (check t1 t2)
in ((rec_nm), (s_e), (u_e)))
end
| (N (t1), M (t2)) -> begin
(

let _57_541 = (check t1 t2)
in (let _149_636 = (mk_return env t1 s_e)
in ((M (t1)), (_149_636), (u_e))))
end
| (M (t1), N (t2)) -> begin
(let _149_641 = (let _149_640 = (let _149_639 = (FStar_Syntax_Print.term_to_string e)
in (let _149_638 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_637 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]" _149_639 _149_638 _149_637))))
in FStar_Syntax_Syntax.Err (_149_640))
in (Prims.raise _149_641))
end))
end))
in (

let ensure_m = (fun env e2 -> (

let strip_m = (fun _57_5 -> (match (_57_5) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_558 -> begin
(FStar_All.failwith "impossible")
end))
in (match (context_nm) with
| N (t) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren\'t"), (e2.FStar_Syntax_Syntax.pos)))))
end
| M (_57_563) -> begin
(let _149_648 = (check env e2 context_nm)
in (strip_m _149_648))
end)))
in (match ((let _149_649 = (FStar_Syntax_Subst.compress e)
in _149_649.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
(let _149_650 = (infer env e)
in (return_if _149_650))
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
| FStar_Syntax_Syntax.Tm_let (_57_614) -> begin
(let _149_658 = (let _149_657 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_let %s" _149_657))
in (FStar_All.failwith _149_658))
end
| FStar_Syntax_Syntax.Tm_type (_57_617) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_620) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_57_623) -> begin
(let _149_660 = (let _149_659 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_refine %s" _149_659))
in (FStar_All.failwith _149_660))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_626) -> begin
(let _149_662 = (let _149_661 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_uvar %s" _149_661))
in (FStar_All.failwith _149_662))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_629) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _149_667 = (let _149_666 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_unknown %s" _149_666))
in (FStar_All.failwith _149_667))
end)))))
and infer : env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.env)
in (match ((let _149_673 = (FStar_Syntax_Subst.compress e)
in _149_673.FStar_Syntax_Syntax.n)) with
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

let _57_649 = env
in (let _149_674 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _149_674; definitions = _57_649.definitions; subst = _57_649.subst; tc_const = _57_649.tc_const}))
in (

let s_binders = (FStar_List.map (fun _57_654 -> (match (_57_654) with
| (bv, qual) -> begin
(

let sort = (star_type env bv.FStar_Syntax_Syntax.sort)
in (((

let _57_656 = bv
in {FStar_Syntax_Syntax.ppname = _57_656.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_656.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (qual)))
end)) binders)
in (

let _57_678 = (FStar_List.fold_left (fun _57_661 _57_664 -> (match (((_57_661), (_57_664))) with
| ((env, acc), (bv, qual)) -> begin
(

let c = (normalize bv.FStar_Syntax_Syntax.sort)
in if (is_C c) then begin
(

let xw = (let _149_678 = (star_type env c)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "^w") None _149_678))
in (

let x = (

let _57_667 = bv
in (let _149_680 = (let _149_679 = (FStar_Syntax_Syntax.bv_to_name xw)
in (trans_F_ env c _149_679))
in {FStar_Syntax_Syntax.ppname = _57_667.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_667.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_680}))
in (

let env = (

let _57_670 = env
in (let _149_684 = (let _149_683 = (let _149_682 = (let _149_681 = (FStar_Syntax_Syntax.bv_to_name xw)
in ((bv), (_149_681)))
in FStar_Syntax_Syntax.NT (_149_682))
in (_149_683)::env.subst)
in {env = _57_670.env; definitions = _57_670.definitions; subst = _149_684; tc_const = _57_670.tc_const}))
in (let _149_688 = (let _149_687 = (FStar_Syntax_Syntax.mk_binder x)
in (let _149_686 = (let _149_685 = (FStar_Syntax_Syntax.mk_binder xw)
in (_149_685)::acc)
in (_149_687)::_149_686))
in ((env), (_149_688))))))
end else begin
(

let x = (

let _57_673 = bv
in (let _149_689 = (star_type env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_673.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_673.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_689}))
in (let _149_691 = (let _149_690 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_690)::acc)
in ((env), (_149_691))))
end)
end)) ((env), ([])) binders)
in (match (_57_678) with
| (env, u_binders) -> begin
(

let u_binders = (FStar_List.rev u_binders)
in (

let _57_688 = (

let check_what = if (is_monadic what) then begin
check_m
end else begin
check_n
end
in (

let _57_684 = (check_what env body)
in (match (_57_684) with
| (t, s_body, u_body) -> begin
(let _149_697 = (let _149_696 = if (is_monadic what) then begin
M (t)
end else begin
N (t)
end
in (comp_of_nm _149_696))
in ((_149_697), (s_body), (u_body)))
end)))
in (match (_57_688) with
| (comp, s_body, u_body) -> begin
(

let t = (

let binders = (FStar_List.map (fun _57_692 -> (match (_57_692) with
| (bv, _57_691) -> begin
(let _149_700 = (let _149_699 = (normalize bv.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.null_bv _149_699))
in (FStar_Syntax_Syntax.mk_binder _149_700))
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
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = {FStar_Syntax_Syntax.v = lid; FStar_Syntax_Syntax.ty = _57_709; FStar_Syntax_Syntax.p = _57_707}; FStar_Syntax_Syntax.fv_delta = _57_705; FStar_Syntax_Syntax.fv_qual = _57_703}) -> begin
(match ((FStar_List.find (fun _57_717 -> (match (_57_717) with
| (lid', _57_716) -> begin
(FStar_Ident.lid_equals lid lid')
end)) env.definitions)) with
| Some (_57_719, t) -> begin
((N (t)), (e), (e))
end
| None -> begin
(

let _57_727 = (FStar_TypeChecker_Env.lookup_lid env.env lid)
in (match (_57_727) with
| (_57_725, t) -> begin
(

let txt = (FStar_Ident.text_of_lid lid)
in (

let allowed_prefixes = ("Mktuple")::("Left")::("Right")::("Some")::("None")::[]
in if (FStar_List.existsb (fun s -> (FStar_Util.starts_with txt (Prims.strcat "Prims." s))) allowed_prefixes) then begin
((N (t)), (e), (e))
end else begin
(let _149_704 = (let _149_703 = (FStar_Util.format1 "The %s constructor has not been whitelisted for the definition language" txt)
in FStar_Syntax_Syntax.Err (_149_703))
in (Prims.raise _149_704))
end))
end))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_738 = (check_n env head)
in (match (_57_738) with
| (t_head, s_head, u_head) -> begin
(

let t_head = (normalize t_head)
in (

let is_arrow = (fun t -> (match ((let _149_707 = (FStar_Syntax_Subst.compress t)
in _149_707.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_743) -> begin
true
end
| _57_746 -> begin
false
end))
in (

let rec flatten = (fun t -> (match ((let _149_710 = (FStar_Syntax_Subst.compress t)
in _149_710.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (t); FStar_Syntax_Syntax.tk = _57_755; FStar_Syntax_Syntax.pos = _57_753; FStar_Syntax_Syntax.vars = _57_751}) when (is_arrow t) -> begin
(

let _57_763 = (flatten t)
in (match (_57_763) with
| (binders', comp) -> begin
(((FStar_List.append binders binders')), (comp))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
((binders), (comp))
end
| _57_769 -> begin
(let _149_713 = (let _149_712 = (let _149_711 = (FStar_Syntax_Print.term_to_string t_head)
in (FStar_Util.format1 "%s: not a function type" _149_711))
in FStar_Syntax_Syntax.Err (_149_712))
in (Prims.raise _149_713))
end))
in (

let _57_772 = (flatten t_head)
in (match (_57_772) with
| (binders, comp) -> begin
(

let n = (FStar_List.length binders)
in (

let n' = (FStar_List.length args)
in (

let _57_775 = if ((FStar_List.length binders) < (FStar_List.length args)) then begin
(let _149_718 = (let _149_717 = (let _149_716 = (FStar_Util.string_of_int n)
in (let _149_715 = (FStar_Util.string_of_int (n' - n))
in (let _149_714 = (FStar_Util.string_of_int n)
in (FStar_Util.format3 "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments." _149_716 _149_715 _149_714))))
in FStar_Syntax_Syntax.Err (_149_717))
in (Prims.raise _149_718))
end else begin
()
end
in (

let _57_779 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (_57_779) with
| (binders, comp) -> begin
(

let rec final_type = (fun subst _57_784 args -> (match (_57_784) with
| (binders, comp) -> begin
(match (((binders), (args))) with
| ([], []) -> begin
(let _149_726 = (let _149_725 = (FStar_Syntax_Subst.subst_comp subst comp)
in _149_725.FStar_Syntax_Syntax.n)
in (nm_of_comp _149_726))
end
| (binders, []) -> begin
(match ((let _149_729 = (let _149_728 = (let _149_727 = (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))))
in (FStar_Syntax_Subst.subst subst _149_727))
in (FStar_Syntax_Subst.compress _149_728))
in _149_729.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(let _149_733 = (let _149_732 = (let _149_731 = (let _149_730 = (FStar_Syntax_Subst.close_comp binders comp)
in ((binders), (_149_730)))
in FStar_Syntax_Syntax.Tm_arrow (_149_731))
in (mk _149_732))
in N (_149_733))
end
| _57_797 -> begin
(FStar_All.failwith "wat?")
end)
end
| ([], (_57_802)::_57_800) -> begin
(FStar_All.failwith "just checked that?!")
end
| (((bv, _57_808))::binders, ((arg, _57_814))::args) -> begin
(final_type ((FStar_Syntax_Syntax.NT (((bv), (arg))))::subst) ((binders), (comp)) args)
end)
end))
in (

let final_type = (final_type [] ((binders), (comp)) args)
in (

let _57_839 = (let _149_750 = (FStar_List.map2 (fun _57_822 _57_825 -> (match (((_57_822), (_57_825))) with
| ((bv, _57_821), (arg, q)) -> begin
(match ((let _149_737 = (let _149_736 = (normalize bv.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Subst.compress _149_736))
in _149_737.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_827) -> begin
(

let arg = (let _149_738 = (normalize arg)
in ((_149_738), (q)))
in ((arg), ((arg)::[])))
end
| _57_831 -> begin
(

let _57_836 = (check_n env arg)
in (match (_57_836) with
| (_57_833, s_arg, u_arg) -> begin
(let _149_749 = (let _149_739 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_arg), (_149_739)))
in (let _149_748 = if (is_C bv.FStar_Syntax_Syntax.sort) then begin
(let _149_745 = (let _149_741 = (FStar_Syntax_Subst.subst env.subst s_arg)
in (let _149_740 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_741), (_149_740))))
in (let _149_744 = (let _149_743 = (let _149_742 = (FStar_Syntax_Syntax.as_implicit false)
in ((u_arg), (_149_742)))
in (_149_743)::[])
in (_149_745)::_149_744))
end else begin
(let _149_747 = (let _149_746 = (FStar_Syntax_Syntax.as_implicit false)
in ((u_arg), (_149_746)))
in (_149_747)::[])
end
in ((_149_749), (_149_748))))
end))
end)
end)) binders args)
in (FStar_List.split _149_750))
in (match (_57_839) with
| (s_args, u_args) -> begin
(

let u_args = (FStar_List.flatten u_args)
in (let _149_752 = (mk (FStar_Syntax_Syntax.Tm_app (((s_head), (s_args)))))
in (let _149_751 = (mk (FStar_Syntax_Syntax.Tm_app (((u_head), (u_args)))))
in ((final_type), (_149_752), (_149_751)))))
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
(let _149_754 = (let _149_753 = (env.tc_const c)
in N (_149_753))
in ((_149_754), (e), (e)))
end
| FStar_Syntax_Syntax.Tm_let (_57_870) -> begin
(let _149_756 = (let _149_755 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_let %s" _149_755))
in (FStar_All.failwith _149_756))
end
| FStar_Syntax_Syntax.Tm_type (_57_873) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_876) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_57_879) -> begin
(let _149_758 = (let _149_757 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_refine %s" _149_757))
in (FStar_All.failwith _149_758))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_882) -> begin
(let _149_760 = (let _149_759 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_uvar %s" _149_759))
in (FStar_All.failwith _149_760))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_885) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _149_765 = (let _149_764 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_unknown %s" _149_764))
in (FStar_All.failwith _149_765))
end))))
and mk_match : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e0 branches f -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e0.FStar_Syntax_Syntax.pos))
in (

let _57_898 = (check_n env e0)
in (match (_57_898) with
| (_57_895, s_e0, u_e0) -> begin
(

let _57_915 = (let _149_781 = (FStar_List.map (fun b -> (match ((FStar_Syntax_Subst.open_branch b)) with
| (pat, None, body) -> begin
(

let env = (

let _57_904 = env
in (let _149_780 = (let _149_779 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env.env _149_779))
in {env = _149_780; definitions = _57_904.definitions; subst = _57_904.subst; tc_const = _57_904.tc_const}))
in (

let _57_910 = (f env body)
in (match (_57_910) with
| (nm, s_body, u_body) -> begin
((nm), (((pat), (None), (((s_body), (u_body), (body))))))
end)))
end
| _57_912 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("No when clauses in the definition language")))
end)) branches)
in (FStar_List.split _149_781))
in (match (_57_915) with
| (nms, branches) -> begin
(

let t1 = (match ((FStar_List.hd nms)) with
| (M (t1)) | (N (t1)) -> begin
t1
end)
in (

let has_m = (FStar_List.existsb (fun _57_6 -> (match (_57_6) with
| M (_57_922) -> begin
true
end
| _57_925 -> begin
false
end)) nms)
in (

let _57_959 = (let _149_785 = (FStar_List.map2 (fun nm _57_934 -> (match (_57_934) with
| (pat, guard, (s_body, u_body, original_body)) -> begin
(match (((nm), (has_m))) with
| ((N (t2), false)) | ((M (t2), true)) -> begin
((nm), (((pat), (guard), (s_body))), (((pat), (guard), (u_body))))
end
| (N (t2), true) -> begin
(

let _57_950 = (check env original_body (M (t2)))
in (match (_57_950) with
| (_57_947, s_body, u_body) -> begin
((M (t2)), (((pat), (guard), (s_body))), (((pat), (guard), (u_body))))
end))
end
| (M (_57_952), false) -> begin
(FStar_All.failwith "impossible")
end)
end)) nms branches)
in (FStar_List.unzip3 _149_785))
in (match (_57_959) with
| (nms, s_branches, u_branches) -> begin
(

let s_branches = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let t1_star = if has_m then begin
(let _149_790 = (let _149_788 = (let _149_787 = (let _149_786 = (mk_star_to_type mk env t1)
in (FStar_Syntax_Syntax.new_bv None _149_786))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _149_787))
in (_149_788)::[])
in (let _149_789 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _149_790 _149_789)))
end else begin
t1
end
in (let _149_795 = (let _149_793 = (let _149_792 = (let _149_791 = (mk (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches)))))
in ((_149_791), (FStar_Util.Inl (t1_star)), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (_149_792))
in (mk _149_793))
in (let _149_794 = (mk (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches)))))
in ((if has_m then begin
M (t1)
end else begin
N (t1)
end), (_149_795), (_149_794)))))))
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

let x_binders = (let _149_815 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_815)::[])
in (

let _57_975 = (FStar_Syntax_Subst.open_term x_binders e2)
in (match (_57_975) with
| (x_binders, e2) -> begin
(match ((infer env e1)) with
| (N (t1), s_e1, u_e1) -> begin
(

let env = (

let _57_981 = env
in (let _149_816 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_983 = x
in {FStar_Syntax_Syntax.ppname = _57_983.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_983.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _149_816; definitions = _57_981.definitions; subst = _57_981.subst; tc_const = _57_981.tc_const}))
in (

let _57_989 = (proceed env e2)
in (match (_57_989) with
| (nm_rec, s_e2, u_e2) -> begin
(let _149_824 = (let _149_819 = (let _149_818 = (let _149_817 = (FStar_Syntax_Subst.close x_binders s_e2)
in ((((false), (((

let _57_990 = binding
in {FStar_Syntax_Syntax.lbname = _57_990.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_990.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_990.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_990.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = s_e1}))::[]))), (_149_817)))
in FStar_Syntax_Syntax.Tm_let (_149_818))
in (mk _149_819))
in (let _149_823 = (let _149_822 = (let _149_821 = (let _149_820 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _57_992 = binding
in {FStar_Syntax_Syntax.lbname = _57_992.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_992.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_992.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_992.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_149_820)))
in FStar_Syntax_Syntax.Tm_let (_149_821))
in (mk _149_822))
in ((nm_rec), (_149_824), (_149_823))))
end)))
end
| (M (t1), s_e1, u_e1) -> begin
(

let env = (

let _57_999 = env
in (let _149_825 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_1001 = x
in {FStar_Syntax_Syntax.ppname = _57_1001.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1001.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _149_825; definitions = _57_999.definitions; subst = _57_999.subst; tc_const = _57_999.tc_const}))
in (

let _57_1007 = (ensure_m env e2)
in (match (_57_1007) with
| (t2, s_e2, u_e2) -> begin
(

let p_type = (mk_star_to_type mk env t2)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" None p_type)
in (

let s_e2 = (let _149_831 = (let _149_830 = (let _149_829 = (let _149_828 = (let _149_827 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _149_826 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_827), (_149_826))))
in (_149_828)::[])
in ((s_e2), (_149_829)))
in FStar_Syntax_Syntax.Tm_app (_149_830))
in (mk _149_831))
in (

let s_e2 = (FStar_Syntax_Util.abs x_binders s_e2 None)
in (

let body = (let _149_836 = (let _149_835 = (let _149_834 = (let _149_833 = (let _149_832 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_e2), (_149_832)))
in (_149_833)::[])
in ((s_e1), (_149_834)))
in FStar_Syntax_Syntax.Tm_app (_149_835))
in (mk _149_836))
in (let _149_843 = (let _149_838 = (let _149_837 = (FStar_Syntax_Syntax.mk_binder p)
in (_149_837)::[])
in (FStar_Syntax_Util.abs _149_838 body None))
in (let _149_842 = (let _149_841 = (let _149_840 = (let _149_839 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _57_1013 = binding
in {FStar_Syntax_Syntax.lbname = _57_1013.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_1013.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1013.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1013.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_149_839)))
in FStar_Syntax_Syntax.Tm_let (_149_840))
in (mk _149_841))
in ((M (t2)), (_149_843), (_149_842)))))))))
end)))
end)
end)))))))
and check_n : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _149_846 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in N (_149_846))
in (match ((check env e mn)) with
| (N (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_1024 -> begin
(FStar_All.failwith "[check_n]: impossible")
end)))
and check_m : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _149_849 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in M (_149_849))
in (match ((check env e mn)) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_1034 -> begin
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

let _57_1056 = if (not ((is_C c))) then begin
(FStar_All.failwith "not a C")
end else begin
()
end
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos))
in (match ((let _149_858 = (FStar_Syntax_Subst.compress c)
in _149_858.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_1066 = (FStar_Syntax_Util.head_and_args wp)
in (match (_57_1066) with
| (wp_head, wp_args) -> begin
(

let _57_1067 = if ((not (((FStar_List.length wp_args) = (FStar_List.length args)))) || (not ((let _149_859 = (FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length wp_args) FStar_Range.dummyRange)
in (FStar_Syntax_Util.is_constructor wp_head _149_859))))) then begin
(FStar_All.failwith "mismatch")
end else begin
()
end
in (let _149_866 = (let _149_865 = (let _149_864 = (FStar_List.map2 (fun _57_1072 _57_1076 -> (match (((_57_1072), (_57_1076))) with
| ((arg, _57_1071), (wp_arg, _57_1075)) -> begin
(let _149_863 = (trans_F_ env arg wp_arg)
in (let _149_862 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_863), (_149_862))))
end)) args wp_args)
in ((head), (_149_864)))
in FStar_Syntax_Syntax.Tm_app (_149_865))
in (mk _149_866)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let binders = (FStar_Syntax_Util.name_binders binders)
in (

let binders = (FStar_Syntax_Subst.open_binders binders)
in (

let _57_1085 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (_57_1085) with
| (binders, comp) -> begin
(

let _57_1094 = (let _149_878 = (FStar_List.map (fun _57_1088 -> (match (_57_1088) with
| (bv, q) -> begin
(

let h = bv.FStar_Syntax_Syntax.sort
in if (is_C h) then begin
(

let w' = (let _149_868 = (star_type env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-w\'") None _149_868))
in (let _149_874 = (let _149_873 = (FStar_Syntax_Syntax.mk_binder w')
in (let _149_872 = (let _149_871 = (let _149_870 = (let _149_869 = (FStar_Syntax_Syntax.bv_to_name bv)
in (trans_F_ env h _149_869))
in (FStar_Syntax_Syntax.null_binder _149_870))
in (_149_871)::[])
in (_149_873)::_149_872))
in ((w'), (_149_874))))
end else begin
(

let x = (let _149_875 = (star_type env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-x") None _149_875))
in (let _149_877 = (let _149_876 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_876)::[])
in ((x), (_149_877))))
end)
end)) binders)
in (FStar_List.split _149_878))
in (match (_57_1094) with
| (bvs, binders) -> begin
(

let binders = (FStar_List.flatten binders)
in (

let app = (let _149_884 = (let _149_883 = (let _149_882 = (FStar_List.map (fun bv -> (let _149_881 = (FStar_Syntax_Syntax.bv_to_name bv)
in (let _149_880 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_881), (_149_880))))) bvs)
in ((wp), (_149_882)))
in FStar_Syntax_Syntax.Tm_app (_149_883))
in (mk _149_884))
in (

let comp = (let _149_886 = (type_of_comp comp)
in (let _149_885 = (is_monadic_comp comp)
in (trans_G env _149_886 _149_885 app)))
in (

let comp = (FStar_Syntax_Subst.close_comp binders comp)
in (

let binders = (FStar_Syntax_Subst.close_binders binders)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp))))))))))
end))
end))))
end
| _57_1102 -> begin
(FStar_All.failwith "impossible trans_F_")
end))))
and trans_G : env_  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env h is_monadic wp -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None h.FStar_Syntax_Syntax.pos))
in if is_monadic then begin
(let _149_897 = (let _149_896 = (star_type env h)
in (let _149_895 = (let _149_894 = (let _149_893 = (FStar_Syntax_Syntax.as_implicit false)
in ((wp), (_149_893)))
in (_149_894)::[])
in {FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _149_896; FStar_Syntax_Syntax.effect_args = _149_895; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp _149_897))
end else begin
(let _149_898 = (trans_F_ env h wp)
in (FStar_Syntax_Syntax.mk_Total _149_898))
end))


let star_expr_definition : env  ->  FStar_Syntax_Syntax.term  ->  (env * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)) = (fun env t -> (star_definition env t (fun env e -> (

let _57_1116 = (check_n env e)
in (match (_57_1116) with
| (t, s_e, s_u) -> begin
((t), (((t), (s_e), (s_u))))
end)))))


let trans_F : env_  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> (

let n = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.env)
in (

let c = (n c)
in (

let wp = (n wp)
in (trans_F_ env c wp)))))




