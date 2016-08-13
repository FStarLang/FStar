
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
in (let _149_183 = (let _149_168 = (mk_all_implicit binders)
in (let _149_167 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((t3), (true)))::(((f), (false)))::(((a1), (false)))::(((a2), (false)))::[]))
in (FStar_List.append _149_168 _149_167)))
in (let _149_182 = (let _149_181 = (let _149_180 = (let _149_179 = (let _149_176 = (let _149_175 = (let _149_174 = (let _149_171 = (let _149_170 = (let _149_169 = (FStar_Syntax_Syntax.bv_to_name f)
in (_149_169)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_170))
in (FStar_Syntax_Util.mk_app c_pure _149_171))
in (let _149_173 = (let _149_172 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_149_172)::[])
in (_149_174)::_149_173))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_175))
in (FStar_Syntax_Util.mk_app c_app _149_176))
in (let _149_178 = (let _149_177 = (FStar_Syntax_Syntax.bv_to_name a2)
in (_149_177)::[])
in (_149_179)::_149_178))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_180))
in (FStar_Syntax_Util.mk_app c_app _149_181))
in (FStar_Syntax_Util.abs _149_183 _149_182 ret)))))))))))
in (

let c_lift2 = (let _149_184 = (mk_lid "lift2")
in (register env _149_184 c_lift2))
in (

let c_push = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _149_190 = (let _149_186 = (let _149_185 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _149_185))
in (_149_186)::[])
in (let _149_189 = (let _149_188 = (let _149_187 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _149_187))
in (FStar_Syntax_Syntax.mk_Total _149_188))
in (FStar_Syntax_Util.arrow _149_190 _149_189)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let ret = (let _149_200 = (let _149_199 = (let _149_198 = (let _149_197 = (let _149_196 = (let _149_195 = (let _149_192 = (let _149_191 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _149_191))
in (_149_192)::[])
in (let _149_194 = (let _149_193 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _149_193))
in (FStar_Syntax_Util.arrow _149_195 _149_194)))
in (mk_ctx _149_196))
in (FStar_Syntax_Syntax.mk_Total _149_197))
in (FStar_Syntax_Util.lcomp_of_comp _149_198))
in FStar_Util.Inl (_149_199))
in Some (_149_200))
in (

let e1 = (let _149_201 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" None _149_201))
in (

let body = (let _149_210 = (let _149_203 = (let _149_202 = (FStar_Syntax_Syntax.mk_binder e1)
in (_149_202)::[])
in (FStar_List.append gamma _149_203))
in (let _149_209 = (let _149_208 = (FStar_Syntax_Syntax.bv_to_name f)
in (let _149_207 = (let _149_206 = (let _149_204 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg _149_204))
in (let _149_205 = (args_of_binders gamma)
in (_149_206)::_149_205))
in (FStar_Syntax_Util.mk_app _149_208 _149_207)))
in (FStar_Syntax_Util.abs _149_210 _149_209 ret)))
in (let _149_213 = (let _149_212 = (mk_all_implicit binders)
in (let _149_211 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::[]))
in (FStar_List.append _149_212 _149_211)))
in (FStar_Syntax_Util.abs _149_213 body ret)))))))))
in (

let c_push = (let _149_214 = (mk_lid "push")
in (register env _149_214 c_push))
in (

let ret_tot_wp_a = (let _149_217 = (let _149_216 = (let _149_215 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.lcomp_of_comp _149_215))
in FStar_Util.Inl (_149_216))
in Some (_149_217))
in (

let mk_generic_app = (fun c -> if ((FStar_List.length binders) > 0) then begin
(let _149_222 = (let _149_221 = (let _149_220 = (args_of_binders binders)
in ((c), (_149_220)))
in FStar_Syntax_Syntax.Tm_app (_149_221))
in (mk _149_222))
end else begin
c
end)
in (

let wp_if_then_else = (

let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (let _149_240 = (let _149_223 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (FStar_List.append binders _149_223))
in (let _149_239 = (

let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_unfoldable (2)) None)
in (let _149_238 = (let _149_229 = (let _149_228 = (let _149_227 = (let _149_226 = (let _149_225 = (let _149_224 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg _149_224))
in (_149_225)::[])
in (FStar_Syntax_Util.mk_app l_ite _149_226))
in (_149_227)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_228))
in (FStar_Syntax_Util.mk_app c_lift2 _149_229))
in (let _149_237 = (let _149_236 = (let _149_235 = (let _149_234 = (let _149_232 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _149_231 = (let _149_230 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_149_230)::[])
in (_149_232)::_149_231))
in (let _149_233 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _149_234 _149_233)))
in (FStar_Syntax_Syntax.mk_Total _149_235))
in FStar_Util.Inr (_149_236))
in (FStar_Syntax_Util.ascribe _149_238 _149_237))))
in (FStar_Syntax_Util.abs _149_240 _149_239 ret_tot_wp_a))))
in (

let wp_if_then_else = (let _149_241 = (mk_lid "wp_if_then_else")
in (register env _149_241 wp_if_then_else))
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

let body = (let _149_252 = (let _149_251 = (let _149_250 = (let _149_247 = (let _149_246 = (let _149_245 = (let _149_244 = (let _149_243 = (let _149_242 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _149_242))
in (_149_243)::[])
in (FStar_Syntax_Util.mk_app l_and _149_244))
in (_149_245)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_246))
in (FStar_Syntax_Util.mk_app c_pure _149_247))
in (let _149_249 = (let _149_248 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_149_248)::[])
in (_149_250)::_149_249))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_251))
in (FStar_Syntax_Util.mk_app c_app _149_252))
in (let _149_254 = (let _149_253 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders _149_253))
in (FStar_Syntax_Util.abs _149_254 body ret_tot_wp_a))))))
in (

let wp_assert = (let _149_255 = (mk_lid "wp_assert")
in (register env _149_255 wp_assert))
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

let body = (let _149_266 = (let _149_265 = (let _149_264 = (let _149_261 = (let _149_260 = (let _149_259 = (let _149_258 = (let _149_257 = (let _149_256 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _149_256))
in (_149_257)::[])
in (FStar_Syntax_Util.mk_app l_imp _149_258))
in (_149_259)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_260))
in (FStar_Syntax_Util.mk_app c_pure _149_261))
in (let _149_263 = (let _149_262 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_149_262)::[])
in (_149_264)::_149_263))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_265))
in (FStar_Syntax_Util.mk_app c_app _149_266))
in (let _149_268 = (let _149_267 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders _149_267))
in (FStar_Syntax_Util.abs _149_268 body ret_tot_wp_a))))))
in (

let wp_assume = (let _149_269 = (mk_lid "wp_assume")
in (register env _149_269 wp_assume))
in (

let wp_assume = (mk_generic_app wp_assume)
in (

let wp_close = (

let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _149_273 = (let _149_271 = (let _149_270 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _149_270))
in (_149_271)::[])
in (let _149_272 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _149_273 _149_272)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let body = (let _149_282 = (let _149_281 = (let _149_280 = (let _149_274 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((FStar_Syntax_Util.tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure _149_274))
in (let _149_279 = (let _149_278 = (let _149_277 = (let _149_276 = (let _149_275 = (FStar_Syntax_Syntax.bv_to_name f)
in (_149_275)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_276))
in (FStar_Syntax_Util.mk_app c_push _149_277))
in (_149_278)::[])
in (_149_280)::_149_279))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_281))
in (FStar_Syntax_Util.mk_app c_app _149_282))
in (let _149_284 = (let _149_283 = (FStar_Syntax_Syntax.binders_of_list ((a)::(b)::(f)::[]))
in (FStar_List.append binders _149_283))
in (FStar_Syntax_Util.abs _149_284 body ret_tot_wp_a))))))
in (

let wp_close = (let _149_285 = (mk_lid "wp_close")
in (register env _149_285 wp_close))
in (

let wp_close = (mk_generic_app wp_close)
in (

let ret_tot_type = (let _149_288 = (let _149_287 = (let _149_286 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _149_286))
in FStar_Util.Inl (_149_287))
in Some (_149_288))
in (

let ret_gtot_type = (let _149_291 = (let _149_290 = (let _149_289 = (FStar_Syntax_Syntax.mk_GTotal FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _149_289))
in FStar_Util.Inl (_149_290))
in Some (_149_291))
in (

let mk_forall = (fun x body -> (let _149_302 = (let _149_301 = (let _149_300 = (let _149_299 = (let _149_298 = (let _149_297 = (let _149_296 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_296)::[])
in (FStar_Syntax_Util.abs _149_297 body ret_tot_type))
in (FStar_Syntax_Syntax.as_arg _149_298))
in (_149_299)::[])
in ((FStar_Syntax_Util.tforall), (_149_300)))
in FStar_Syntax_Syntax.Tm_app (_149_301))
in (FStar_Syntax_Syntax.mk _149_302 None FStar_Range.dummyRange)))
in (

let is_zero_order = (fun t -> (match ((let _149_305 = (FStar_Syntax_Subst.compress t)
in _149_305.FStar_Syntax_Syntax.n)) with
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
in (match ((let _149_327 = (FStar_Syntax_Subst.compress t)
in _149_327.FStar_Syntax_Syntax.n)) with
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

let body = (let _149_335 = (let _149_330 = (let _149_329 = (let _149_328 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _149_328))
in (_149_329)::[])
in (FStar_Syntax_Util.mk_app x _149_330))
in (let _149_334 = (let _149_333 = (let _149_332 = (let _149_331 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _149_331))
in (_149_332)::[])
in (FStar_Syntax_Util.mk_app y _149_333))
in (mk_rel b _149_335 _149_334)))
in (mk_forall a1 body)))
end else begin
(

let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (

let a2 = (FStar_Syntax_Syntax.gen_bv "a2" None a)
in (

let body = (let _149_347 = (let _149_337 = (FStar_Syntax_Syntax.bv_to_name a1)
in (let _149_336 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_rel a _149_337 _149_336)))
in (let _149_346 = (let _149_345 = (let _149_340 = (let _149_339 = (let _149_338 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _149_338))
in (_149_339)::[])
in (FStar_Syntax_Util.mk_app x _149_340))
in (let _149_344 = (let _149_343 = (let _149_342 = (let _149_341 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg _149_341))
in (_149_342)::[])
in (FStar_Syntax_Util.mk_app y _149_343))
in (mk_rel b _149_345 _149_344)))
in (FStar_Syntax_Util.mk_imp _149_347 _149_346)))
in (let _149_348 = (mk_forall a2 body)
in (mk_forall a1 _149_348)))))
end)
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::binders, comp) -> begin
(

let t = (

let _57_219 = t
in (let _149_352 = (let _149_351 = (let _149_350 = (let _149_349 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _149_349))
in (((binder)::[]), (_149_350)))
in FStar_Syntax_Syntax.Tm_arrow (_149_351))
in {FStar_Syntax_Syntax.n = _149_352; FStar_Syntax_Syntax.tk = _57_219.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_219.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_219.FStar_Syntax_Syntax.vars}))
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

let body = (let _149_354 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (let _149_353 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_rel FStar_Syntax_Util.mk_imp wp_a _149_354 _149_353)))
in (let _149_356 = (let _149_355 = (binders_of_list ((((a), (false)))::(((wp1), (false)))::(((wp2), (false)))::[]))
in (FStar_List.append binders _149_355))
in (FStar_Syntax_Util.abs _149_356 body ret_tot_type)))))
in (

let stronger = (let _149_357 = (mk_lid "stronger")
in (register env _149_357 stronger))
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

let eq = (let _149_358 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst post))
in (mk_rel FStar_Syntax_Util.mk_iff k.FStar_Syntax_Syntax.sort k_tm _149_358))
in (match ((FStar_Syntax_Util.destruct_typ_as_formula eq)) with
| Some (FStar_Syntax_Util.QAll (binders, [], body)) -> begin
(

let k_app = (let _149_359 = (args_of_binders binders)
in (FStar_Syntax_Util.mk_app k_tm _149_359))
in (

let guard_free = (let _149_360 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.guard_free FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _149_360))
in (

let pat = (let _149_362 = (let _149_361 = (FStar_Syntax_Syntax.as_arg k_app)
in (_149_361)::[])
in (FStar_Syntax_Util.mk_app guard_free _149_362))
in (

let pattern_guarded_body = (let _149_368 = (let _149_367 = (let _149_366 = (let _149_365 = (let _149_364 = (let _149_363 = (FStar_Syntax_Syntax.as_arg pat)
in (_149_363)::[])
in (_149_364)::[])
in FStar_Syntax_Syntax.Meta_pattern (_149_365))
in ((body), (_149_366)))
in FStar_Syntax_Syntax.Tm_meta (_149_367))
in (mk _149_368))
in (FStar_Syntax_Util.close_forall binders pattern_guarded_body)))))
end
| _57_251 -> begin
(FStar_All.failwith "Impossible: Expected the equivalence to be a quantified formula")
end)))
in (

let body = (let _149_377 = (let _149_376 = (let _149_375 = (let _149_374 = (FStar_Syntax_Syntax.bv_to_name wp)
in (let _149_373 = (let _149_372 = (args_of_binders wp_args)
in (let _149_371 = (let _149_370 = (let _149_369 = (FStar_Syntax_Syntax.bv_to_name k)
in (FStar_Syntax_Syntax.as_arg _149_369))
in (_149_370)::[])
in (FStar_List.append _149_372 _149_371)))
in (FStar_Syntax_Util.mk_app _149_374 _149_373)))
in (FStar_Syntax_Util.mk_imp equiv _149_375))
in (FStar_Syntax_Util.mk_forall k _149_376))
in (FStar_Syntax_Util.abs gamma _149_377 ret_gtot_type))
in (let _149_379 = (let _149_378 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders _149_378))
in (FStar_Syntax_Util.abs _149_379 body ret_gtot_type)))))
end)))
in (

let wp_ite = (let _149_380 = (mk_lid "wp_ite")
in (register env _149_380 wp_ite))
in (

let wp_ite = (mk_generic_app wp_ite)
in (

let null_wp = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let _57_260 = (FStar_Util.prefix gamma)
in (match (_57_260) with
| (wp_args, post) -> begin
(

let x = (FStar_Syntax_Syntax.gen_bv "x" None FStar_Syntax_Syntax.tun)
in (

let body = (let _149_385 = (let _149_384 = (FStar_All.pipe_left FStar_Syntax_Syntax.bv_to_name (Prims.fst post))
in (let _149_383 = (let _149_382 = (let _149_381 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _149_381))
in (_149_382)::[])
in (FStar_Syntax_Util.mk_app _149_384 _149_383)))
in (FStar_Syntax_Util.mk_forall x _149_385))
in (let _149_388 = (let _149_387 = (let _149_386 = (FStar_Syntax_Syntax.binders_of_list ((a)::[]))
in (FStar_List.append _149_386 gamma))
in (FStar_List.append binders _149_387))
in (FStar_Syntax_Util.abs _149_388 body ret_gtot_type))))
end)))
in (

let null_wp = (let _149_389 = (mk_lid "null_wp")
in (register env _149_389 null_wp))
in (

let null_wp = (mk_generic_app null_wp)
in (

let wp_trivial = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let body = (let _149_399 = (let _149_398 = (let _149_397 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _149_396 = (let _149_395 = (let _149_392 = (let _149_391 = (let _149_390 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg _149_390))
in (_149_391)::[])
in (FStar_Syntax_Util.mk_app null_wp _149_392))
in (let _149_394 = (let _149_393 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_149_393)::[])
in (_149_395)::_149_394))
in (_149_397)::_149_396))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_398))
in (FStar_Syntax_Util.mk_app stronger _149_399))
in (let _149_401 = (let _149_400 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders _149_400))
in (FStar_Syntax_Util.abs _149_401 body ret_tot_type))))
in (

let wp_trivial = (let _149_402 = (mk_lid "wp_trivial")
in (register env _149_402 wp_trivial))
in (

let wp_trivial = (mk_generic_app wp_trivial)
in (

let _57_271 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(d "End Dijkstra monads for free")
end else begin
()
end
in (

let c = (FStar_Syntax_Subst.close binders)
in (let _149_422 = (let _149_404 = (FStar_ST.read sigelts)
in (FStar_List.rev _149_404))
in (let _149_421 = (

let _57_274 = ed
in (let _149_420 = (let _149_405 = (c wp_if_then_else)
in (([]), (_149_405)))
in (let _149_419 = (let _149_406 = (c wp_ite)
in (([]), (_149_406)))
in (let _149_418 = (let _149_407 = (c stronger)
in (([]), (_149_407)))
in (let _149_417 = (let _149_408 = (c wp_close)
in (([]), (_149_408)))
in (let _149_416 = (let _149_409 = (c wp_assert)
in (([]), (_149_409)))
in (let _149_415 = (let _149_410 = (c wp_assume)
in (([]), (_149_410)))
in (let _149_414 = (let _149_411 = (c null_wp)
in (([]), (_149_411)))
in (let _149_413 = (let _149_412 = (c wp_trivial)
in (([]), (_149_412)))
in {FStar_Syntax_Syntax.qualifiers = _57_274.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_274.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_274.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_274.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_274.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _57_274.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _57_274.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _149_420; FStar_Syntax_Syntax.ite_wp = _149_419; FStar_Syntax_Syntax.stronger = _149_418; FStar_Syntax_Syntax.close_wp = _149_417; FStar_Syntax_Syntax.assert_p = _149_416; FStar_Syntax_Syntax.assume_p = _149_415; FStar_Syntax_Syntax.null_wp = _149_414; FStar_Syntax_Syntax.trivial = _149_413; FStar_Syntax_Syntax.repr = _57_274.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _57_274.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _57_274.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _57_274.FStar_Syntax_Syntax.actions})))))))))
in ((_149_422), (_149_421)))))))))))))))))))))))))))))))))))))))))))))))
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
| N (_57_284) -> begin
_57_284
end))


let ___M____0 = (fun projectee -> (match (projectee) with
| M (_57_287) -> begin
_57_287
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
| _57_294 -> begin
(FStar_All.failwith "[nm_of_comp]: impossible")
end))


let string_of_nm : nm  ->  Prims.string = (fun _57_2 -> (match (_57_2) with
| N (t) -> begin
(let _149_480 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "N[%s]" _149_480))
end
| M (t) -> begin
(let _149_481 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "M[%s]" _149_481))
end))


let is_monadic_arrow : FStar_Syntax_Syntax.term'  ->  nm = (fun n -> (match (n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_302, {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_308; FStar_Syntax_Syntax.pos = _57_306; FStar_Syntax_Syntax.vars = _57_304}) -> begin
(nm_of_comp n)
end
| _57_314 -> begin
(FStar_All.failwith "unexpected_argument: [is_monadic_arrow]")
end))


let is_monadic_comp = (fun c -> (match ((nm_of_comp c.FStar_Syntax_Syntax.n)) with
| M (_57_317) -> begin
true
end
| N (_57_320) -> begin
false
end))


let rec mk_star_to_type : (FStar_Syntax_Syntax.term'  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun mk env a -> (let _149_505 = (let _149_504 = (let _149_503 = (let _149_501 = (let _149_500 = (let _149_498 = (star_type' env a)
in (FStar_Syntax_Syntax.null_bv _149_498))
in (let _149_499 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_500), (_149_499))))
in (_149_501)::[])
in (let _149_502 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_149_503), (_149_502))))
in FStar_Syntax_Syntax.Tm_arrow (_149_504))
in (mk _149_505)))
and star_type' : env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None t.FStar_Syntax_Syntax.pos))
in (

let mk_star_to_type = (mk_star_to_type mk)
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _57_333) -> begin
(

let binders = (FStar_List.map (fun _57_338 -> (match (_57_338) with
| (bv, aqual) -> begin
(let _149_514 = (

let _57_339 = bv
in (let _149_513 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_339.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_339.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_513}))
in ((_149_514), (aqual)))
end)) binders)
in (match ((is_monadic_arrow t.FStar_Syntax_Syntax.n)) with
| N (hn) -> begin
(let _149_518 = (let _149_517 = (let _149_516 = (let _149_515 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_Total _149_515))
in ((binders), (_149_516)))
in FStar_Syntax_Syntax.Tm_arrow (_149_517))
in (mk _149_518))
end
| M (a) -> begin
(let _149_527 = (let _149_526 = (let _149_525 = (let _149_523 = (let _149_522 = (let _149_521 = (let _149_519 = (mk_star_to_type env a)
in (FStar_Syntax_Syntax.null_bv _149_519))
in (let _149_520 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_521), (_149_520))))
in (_149_522)::[])
in (FStar_List.append binders _149_523))
in (let _149_524 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_149_525), (_149_524))))
in FStar_Syntax_Syntax.Tm_arrow (_149_526))
in (mk _149_527))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let is_valid_application = (fun head -> (match ((let _149_530 = (FStar_Syntax_Subst.compress head)
in _149_530.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.option_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.either_lid)) || (let _149_531 = (FStar_Syntax_Subst.compress head)
in (FStar_Syntax_Util.is_tuple_constructor _149_531))) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uinst (_57_355) -> begin
(FStar_All.failwith "impossible (Tm_uinst)")
end
| _57_358 -> begin
false
end))
in if (is_valid_application head) then begin
(let _149_536 = (let _149_535 = (let _149_534 = (FStar_List.map (fun _57_361 -> (match (_57_361) with
| (t, qual) -> begin
(let _149_533 = (star_type' env t)
in ((_149_533), (qual)))
end)) args)
in ((head), (_149_534)))
in FStar_Syntax_Syntax.Tm_app (_149_535))
in (mk _149_536))
end else begin
(let _149_539 = (let _149_538 = (let _149_537 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "For now, only [either] and [option] are supported in the definition language (got: %s)" _149_537))
in FStar_Syntax_Syntax.Err (_149_538))
in (Prims.raise _149_539))
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
in (let _149_540 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _149_540; subst = _57_382.subst; tc_const = _57_382.tc_const}))
in (

let repr = (star_type' env repr)
in (FStar_Syntax_Util.abs binders repr something)))
end))
end
| (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_match (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _149_543 = (let _149_542 = (let _149_541 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "The following term is outside of the definition language: %s" _149_541))
in FStar_Syntax_Syntax.Err (_149_542))
in (Prims.raise _149_543))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_415) -> begin
(FStar_All.failwith "impossible")
end)))))


let is_monadic : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  Prims.bool = (fun _57_3 -> (match (_57_3) with
| None -> begin
(FStar_All.failwith "un-annotated lambda?!")
end
| (Some (FStar_Util.Inl ({FStar_Syntax_Syntax.eff_name = lid; FStar_Syntax_Syntax.res_typ = _; FStar_Syntax_Syntax.cflags = _; FStar_Syntax_Syntax.comp = _}))) | (Some (FStar_Util.Inr (lid))) -> begin
(FStar_Ident.lid_equals lid FStar_Syntax_Const.monadic_lid)
end))


let rec is_C : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match ((let _149_551 = (FStar_Syntax_Subst.compress t)
in _149_551.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) when (FStar_Syntax_Util.is_tuple_constructor head) -> begin
(

let r = (let _149_553 = (let _149_552 = (FStar_List.hd args)
in (Prims.fst _149_552))
in (is_C _149_553))
in if r then begin
(

let _57_441 = if (not ((FStar_List.for_all (fun _57_440 -> (match (_57_440) with
| (h, _57_439) -> begin
(is_C h)
end)) args))) then begin
(FStar_All.failwith "not a C (A * C)")
end else begin
()
end
in true)
end else begin
(

let _57_447 = if (not ((FStar_List.for_all (fun _57_446 -> (match (_57_446) with
| (h, _57_445) -> begin
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

let _57_455 = if (is_C t) then begin
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
| _57_475 -> begin
false
end))


let mk_return : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let p_type = (mk_star_to_type mk env t)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'" None p_type)
in (

let body = (let _149_569 = (let _149_568 = (let _149_567 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _149_566 = (let _149_565 = (let _149_564 = (FStar_Syntax_Syntax.as_implicit false)
in ((e), (_149_564)))
in (_149_565)::[])
in ((_149_567), (_149_566))))
in FStar_Syntax_Syntax.Tm_app (_149_568))
in (mk _149_569))
in (let _149_571 = (let _149_570 = (FStar_Syntax_Syntax.mk_binder p)
in (_149_570)::[])
in (FStar_Syntax_Util.abs _149_571 body None)))))))


let is_unknown : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun _57_4 -> (match (_57_4) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| _57_487 -> begin
false
end))


let rec check : env  ->  FStar_Syntax_Syntax.term  ->  nm  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e context_nm -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let return_if = (fun _57_497 -> (match (_57_497) with
| (rec_nm, s_e, u_e) -> begin
(

let check = (fun t1 t2 -> if ((not ((is_unknown t2.FStar_Syntax_Syntax.n))) && (not ((let _149_625 = (FStar_TypeChecker_Rel.teq env.env t1 t2)
in (FStar_TypeChecker_Rel.is_trivial _149_625))))) then begin
(let _149_630 = (let _149_629 = (let _149_628 = (FStar_Syntax_Print.term_to_string e)
in (let _149_627 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_626 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check]: the expression [%s] has type [%s] but should have type [%s]" _149_628 _149_627 _149_626))))
in FStar_Syntax_Syntax.Err (_149_629))
in (Prims.raise _149_630))
end else begin
()
end)
in (match (((rec_nm), (context_nm))) with
| ((N (t1), N (t2))) | ((M (t1), M (t2))) -> begin
(

let _57_509 = (check t1 t2)
in ((rec_nm), (s_e), (u_e)))
end
| (N (t1), M (t2)) -> begin
(

let _57_516 = (check t1 t2)
in (let _149_631 = (mk_return env t1 s_e)
in ((M (t1)), (_149_631), (u_e))))
end
| (M (t1), N (t2)) -> begin
(let _149_636 = (let _149_635 = (let _149_634 = (FStar_Syntax_Print.term_to_string e)
in (let _149_633 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_632 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]" _149_634 _149_633 _149_632))))
in FStar_Syntax_Syntax.Err (_149_635))
in (Prims.raise _149_636))
end))
end))
in (

let ensure_m = (fun env e2 -> (

let strip_m = (fun _57_5 -> (match (_57_5) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_533 -> begin
(FStar_All.failwith "impossible")
end))
in (match (context_nm) with
| N (t) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren\'t"), (e2.FStar_Syntax_Syntax.pos)))))
end
| M (_57_538) -> begin
(let _149_643 = (check env e2 context_nm)
in (strip_m _149_643))
end)))
in (match ((let _149_644 = (FStar_Syntax_Subst.compress e)
in _149_644.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
(let _149_645 = (infer env e)
in (return_if _149_645))
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
| FStar_Syntax_Syntax.Tm_let (_57_589) -> begin
(let _149_653 = (let _149_652 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_let %s" _149_652))
in (FStar_All.failwith _149_653))
end
| FStar_Syntax_Syntax.Tm_type (_57_592) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_595) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_57_598) -> begin
(let _149_655 = (let _149_654 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_refine %s" _149_654))
in (FStar_All.failwith _149_655))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_601) -> begin
(let _149_657 = (let _149_656 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_uvar %s" _149_656))
in (FStar_All.failwith _149_657))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_604) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _149_662 = (let _149_661 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_unknown %s" _149_661))
in (FStar_All.failwith _149_662))
end)))))
and infer : env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.env)
in (match ((let _149_668 = (FStar_Syntax_Subst.compress e)
in _149_668.FStar_Syntax_Syntax.n)) with
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

let _57_624 = env
in (let _149_669 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _149_669; subst = _57_624.subst; tc_const = _57_624.tc_const}))
in (

let s_binders = (FStar_List.map (fun _57_629 -> (match (_57_629) with
| (bv, qual) -> begin
(

let sort = (star_type' env bv.FStar_Syntax_Syntax.sort)
in (((

let _57_631 = bv
in {FStar_Syntax_Syntax.ppname = _57_631.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_631.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (qual)))
end)) binders)
in (

let _57_653 = (FStar_List.fold_left (fun _57_636 _57_639 -> (match (((_57_636), (_57_639))) with
| ((env, acc), (bv, qual)) -> begin
(

let c = bv.FStar_Syntax_Syntax.sort
in if (is_C c) then begin
(

let xw = (let _149_673 = (star_type' env c)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "^w") None _149_673))
in (

let x = (

let _57_642 = bv
in (let _149_675 = (let _149_674 = (FStar_Syntax_Syntax.bv_to_name xw)
in (trans_F_ env c _149_674))
in {FStar_Syntax_Syntax.ppname = _57_642.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_642.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_675}))
in (

let env = (

let _57_645 = env
in (let _149_679 = (let _149_678 = (let _149_677 = (let _149_676 = (FStar_Syntax_Syntax.bv_to_name xw)
in ((bv), (_149_676)))
in FStar_Syntax_Syntax.NT (_149_677))
in (_149_678)::env.subst)
in {env = _57_645.env; subst = _149_679; tc_const = _57_645.tc_const}))
in (let _149_683 = (let _149_682 = (FStar_Syntax_Syntax.mk_binder x)
in (let _149_681 = (let _149_680 = (FStar_Syntax_Syntax.mk_binder xw)
in (_149_680)::acc)
in (_149_682)::_149_681))
in ((env), (_149_683))))))
end else begin
(

let x = (

let _57_648 = bv
in (let _149_684 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_648.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_648.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_684}))
in (let _149_686 = (let _149_685 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_685)::acc)
in ((env), (_149_686))))
end)
end)) ((env), ([])) binders)
in (match (_57_653) with
| (env, u_binders) -> begin
(

let u_binders = (FStar_List.rev u_binders)
in (

let _57_663 = (

let check_what = if (is_monadic what) then begin
check_m
end else begin
check_n
end
in (

let _57_659 = (check_what env body)
in (match (_57_659) with
| (t, s_body, u_body) -> begin
(let _149_692 = (let _149_691 = if (is_monadic what) then begin
M (t)
end else begin
N (t)
end
in (comp_of_nm _149_691))
in ((_149_692), (s_body), (u_body)))
end)))
in (match (_57_663) with
| (comp, s_body, u_body) -> begin
(

let t = (

let binders = (FStar_List.map (fun _57_667 -> (match (_57_667) with
| (bv, _57_666) -> begin
(let _149_694 = (FStar_Syntax_Syntax.null_bv bv.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_binder _149_694))
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
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = {FStar_Syntax_Syntax.v = lid; FStar_Syntax_Syntax.ty = _57_684; FStar_Syntax_Syntax.p = _57_682}; FStar_Syntax_Syntax.fv_delta = _57_680; FStar_Syntax_Syntax.fv_qual = _57_678}) -> begin
(

let _57_692 = (FStar_TypeChecker_Env.lookup_lid env.env lid)
in (match (_57_692) with
| (_57_690, t) -> begin
(

let txt = (FStar_Ident.text_of_lid lid)
in (

let allowed_prefixes = ("Mktuple")::("Left")::("Right")::("Some")::("None")::[]
in if (FStar_List.existsb (fun s -> (FStar_Util.starts_with txt (Prims.strcat "Prims." s))) allowed_prefixes) then begin
(let _149_697 = (let _149_696 = (normalize t)
in N (_149_696))
in ((_149_697), (e), (e)))
end else begin
(let _149_699 = (let _149_698 = (FStar_Util.format1 "The %s constructor has not been whitelisted for the definition language; if this is a function application, consider using [inline]" txt)
in FStar_Syntax_Syntax.Err (_149_698))
in (Prims.raise _149_699))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_703 = (check_n env head)
in (match (_57_703) with
| (t_head, s_head, u_head) -> begin
(

let is_arrow = (fun t -> (match ((let _149_702 = (FStar_Syntax_Subst.compress t)
in _149_702.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_707) -> begin
true
end
| _57_710 -> begin
false
end))
in (

let rec flatten = (fun t -> (match ((let _149_705 = (FStar_Syntax_Subst.compress t)
in _149_705.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (t); FStar_Syntax_Syntax.tk = _57_719; FStar_Syntax_Syntax.pos = _57_717; FStar_Syntax_Syntax.vars = _57_715}) when (is_arrow t) -> begin
(

let _57_727 = (flatten t)
in (match (_57_727) with
| (binders', comp) -> begin
(((FStar_List.append binders binders')), (comp))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
((binders), (comp))
end
| _57_733 -> begin
(let _149_708 = (let _149_707 = (let _149_706 = (FStar_Syntax_Print.term_to_string t_head)
in (FStar_Util.format1 "%s: not a function type" _149_706))
in FStar_Syntax_Syntax.Err (_149_707))
in (Prims.raise _149_708))
end))
in (

let _57_736 = (flatten t_head)
in (match (_57_736) with
| (binders, comp) -> begin
(

let n = (FStar_List.length binders)
in (

let n' = (FStar_List.length args)
in (

let _57_739 = if ((FStar_List.length binders) < (FStar_List.length args)) then begin
(let _149_713 = (let _149_712 = (let _149_711 = (FStar_Util.string_of_int n)
in (let _149_710 = (FStar_Util.string_of_int (n' - n))
in (let _149_709 = (FStar_Util.string_of_int n)
in (FStar_Util.format3 "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments." _149_711 _149_710 _149_709))))
in FStar_Syntax_Syntax.Err (_149_712))
in (Prims.raise _149_713))
end else begin
()
end
in (

let _57_743 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (_57_743) with
| (binders, comp) -> begin
(

let rec final_type = (fun subst _57_748 args -> (match (_57_748) with
| (binders, comp) -> begin
(match (((binders), (args))) with
| ([], []) -> begin
(let _149_721 = (let _149_720 = (FStar_Syntax_Subst.subst_comp subst comp)
in _149_720.FStar_Syntax_Syntax.n)
in (nm_of_comp _149_721))
end
| (binders, []) -> begin
(match ((let _149_724 = (let _149_723 = (let _149_722 = (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))))
in (FStar_Syntax_Subst.subst subst _149_722))
in (FStar_Syntax_Subst.compress _149_723))
in _149_724.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(let _149_728 = (let _149_727 = (let _149_726 = (let _149_725 = (FStar_Syntax_Subst.close_comp binders comp)
in ((binders), (_149_725)))
in FStar_Syntax_Syntax.Tm_arrow (_149_726))
in (mk _149_727))
in N (_149_728))
end
| _57_761 -> begin
(FStar_All.failwith "wat?")
end)
end
| ([], (_57_766)::_57_764) -> begin
(FStar_All.failwith "just checked that?!")
end
| (((bv, _57_772))::binders, ((arg, _57_778))::args) -> begin
(final_type ((FStar_Syntax_Syntax.NT (((bv), (arg))))::subst) ((binders), (comp)) args)
end)
end))
in (

let final_type = (final_type [] ((binders), (comp)) args)
in (

let _57_803 = (let _149_743 = (FStar_List.map2 (fun _57_786 _57_789 -> (match (((_57_786), (_57_789))) with
| ((bv, _57_785), (arg, q)) -> begin
(match ((let _149_731 = (FStar_Syntax_Subst.compress bv.FStar_Syntax_Syntax.sort)
in _149_731.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_791) -> begin
(

let arg = ((arg), (q))
in ((arg), ((arg)::[])))
end
| _57_795 -> begin
(

let _57_800 = (check_n env arg)
in (match (_57_800) with
| (_57_797, s_arg, u_arg) -> begin
(let _149_742 = (let _149_732 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_arg), (_149_732)))
in (let _149_741 = if (is_C bv.FStar_Syntax_Syntax.sort) then begin
(let _149_738 = (let _149_734 = (FStar_Syntax_Subst.subst env.subst s_arg)
in (let _149_733 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_734), (_149_733))))
in (let _149_737 = (let _149_736 = (let _149_735 = (FStar_Syntax_Syntax.as_implicit false)
in ((u_arg), (_149_735)))
in (_149_736)::[])
in (_149_738)::_149_737))
end else begin
(let _149_740 = (let _149_739 = (FStar_Syntax_Syntax.as_implicit false)
in ((u_arg), (_149_739)))
in (_149_740)::[])
end
in ((_149_742), (_149_741))))
end))
end)
end)) binders args)
in (FStar_List.split _149_743))
in (match (_57_803) with
| (s_args, u_args) -> begin
(

let u_args = (FStar_List.flatten u_args)
in (let _149_745 = (mk (FStar_Syntax_Syntax.Tm_app (((s_head), (s_args)))))
in (let _149_744 = (mk (FStar_Syntax_Syntax.Tm_app (((u_head), (u_args)))))
in ((final_type), (_149_745), (_149_744)))))
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
(let _149_747 = (let _149_746 = (env.tc_const c)
in N (_149_746))
in ((_149_747), (e), (e)))
end
| FStar_Syntax_Syntax.Tm_let (_57_834) -> begin
(let _149_749 = (let _149_748 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_let %s" _149_748))
in (FStar_All.failwith _149_749))
end
| FStar_Syntax_Syntax.Tm_type (_57_837) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_840) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_57_843) -> begin
(let _149_751 = (let _149_750 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_refine %s" _149_750))
in (FStar_All.failwith _149_751))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_846) -> begin
(let _149_753 = (let _149_752 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_uvar %s" _149_752))
in (FStar_All.failwith _149_753))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_849) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _149_758 = (let _149_757 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_unknown %s" _149_757))
in (FStar_All.failwith _149_758))
end))))
and mk_match : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e0 branches f -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e0.FStar_Syntax_Syntax.pos))
in (

let _57_862 = (check_n env e0)
in (match (_57_862) with
| (_57_859, s_e0, u_e0) -> begin
(

let _57_879 = (let _149_774 = (FStar_List.map (fun b -> (match ((FStar_Syntax_Subst.open_branch b)) with
| (pat, None, body) -> begin
(

let env = (

let _57_868 = env
in (let _149_773 = (let _149_772 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env.env _149_772))
in {env = _149_773; subst = _57_868.subst; tc_const = _57_868.tc_const}))
in (

let _57_874 = (f env body)
in (match (_57_874) with
| (nm, s_body, u_body) -> begin
((nm), (((pat), (None), (((s_body), (u_body), (body))))))
end)))
end
| _57_876 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("No when clauses in the definition language")))
end)) branches)
in (FStar_List.split _149_774))
in (match (_57_879) with
| (nms, branches) -> begin
(

let t1 = (match ((FStar_List.hd nms)) with
| (M (t1)) | (N (t1)) -> begin
t1
end)
in (

let has_m = (FStar_List.existsb (fun _57_6 -> (match (_57_6) with
| M (_57_886) -> begin
true
end
| _57_889 -> begin
false
end)) nms)
in (

let _57_923 = (let _149_778 = (FStar_List.map2 (fun nm _57_898 -> (match (_57_898) with
| (pat, guard, (s_body, u_body, original_body)) -> begin
(match (((nm), (has_m))) with
| ((N (t2), false)) | ((M (t2), true)) -> begin
((nm), (((pat), (guard), (s_body))), (((pat), (guard), (u_body))))
end
| (N (t2), true) -> begin
(

let _57_914 = (check env original_body (M (t2)))
in (match (_57_914) with
| (_57_911, s_body, u_body) -> begin
((M (t2)), (((pat), (guard), (s_body))), (((pat), (guard), (u_body))))
end))
end
| (M (_57_916), false) -> begin
(FStar_All.failwith "impossible")
end)
end)) nms branches)
in (FStar_List.unzip3 _149_778))
in (match (_57_923) with
| (nms, s_branches, u_branches) -> begin
(

let s_branches = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let t1_star = if has_m then begin
(let _149_783 = (let _149_781 = (let _149_780 = (let _149_779 = (mk_star_to_type mk env t1)
in (FStar_Syntax_Syntax.new_bv None _149_779))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _149_780))
in (_149_781)::[])
in (let _149_782 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _149_783 _149_782)))
end else begin
t1
end
in (let _149_788 = (let _149_786 = (let _149_785 = (let _149_784 = (mk (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches)))))
in ((_149_784), (FStar_Util.Inl (t1_star)), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (_149_785))
in (mk _149_786))
in (let _149_787 = (mk (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches)))))
in ((if has_m then begin
M (t1)
end else begin
N (t1)
end), (_149_788), (_149_787)))))))
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

let x_binders = (let _149_808 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_808)::[])
in (

let _57_939 = (FStar_Syntax_Subst.open_term x_binders e2)
in (match (_57_939) with
| (x_binders, e2) -> begin
(match ((infer env e1)) with
| (N (t1), s_e1, u_e1) -> begin
(

let env = (

let _57_945 = env
in (let _149_809 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_947 = x
in {FStar_Syntax_Syntax.ppname = _57_947.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_947.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _149_809; subst = _57_945.subst; tc_const = _57_945.tc_const}))
in (

let _57_953 = (proceed env e2)
in (match (_57_953) with
| (nm_rec, s_e2, u_e2) -> begin
(let _149_817 = (let _149_812 = (let _149_811 = (let _149_810 = (FStar_Syntax_Subst.close x_binders s_e2)
in ((((false), (((

let _57_954 = binding
in {FStar_Syntax_Syntax.lbname = _57_954.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_954.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_954.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_954.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = s_e1}))::[]))), (_149_810)))
in FStar_Syntax_Syntax.Tm_let (_149_811))
in (mk _149_812))
in (let _149_816 = (let _149_815 = (let _149_814 = (let _149_813 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _57_956 = binding
in {FStar_Syntax_Syntax.lbname = _57_956.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_956.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_956.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_956.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_149_813)))
in FStar_Syntax_Syntax.Tm_let (_149_814))
in (mk _149_815))
in ((nm_rec), (_149_817), (_149_816))))
end)))
end
| (M (t1), s_e1, u_e1) -> begin
(

let env = (

let _57_963 = env
in (let _149_818 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_965 = x
in {FStar_Syntax_Syntax.ppname = _57_965.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_965.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _149_818; subst = _57_963.subst; tc_const = _57_963.tc_const}))
in (

let _57_971 = (ensure_m env e2)
in (match (_57_971) with
| (t2, s_e2, u_e2) -> begin
(

let p_type = (mk_star_to_type mk env t2)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" None p_type)
in (

let s_e2 = (let _149_824 = (let _149_823 = (let _149_822 = (let _149_821 = (let _149_820 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _149_819 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_820), (_149_819))))
in (_149_821)::[])
in ((s_e2), (_149_822)))
in FStar_Syntax_Syntax.Tm_app (_149_823))
in (mk _149_824))
in (

let s_e2 = (FStar_Syntax_Util.abs x_binders s_e2 None)
in (

let body = (let _149_829 = (let _149_828 = (let _149_827 = (let _149_826 = (let _149_825 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_e2), (_149_825)))
in (_149_826)::[])
in ((s_e1), (_149_827)))
in FStar_Syntax_Syntax.Tm_app (_149_828))
in (mk _149_829))
in (let _149_836 = (let _149_831 = (let _149_830 = (FStar_Syntax_Syntax.mk_binder p)
in (_149_830)::[])
in (FStar_Syntax_Util.abs _149_831 body None))
in (let _149_835 = (let _149_834 = (let _149_833 = (let _149_832 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _57_977 = binding
in {FStar_Syntax_Syntax.lbname = _57_977.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_977.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_977.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_977.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_149_832)))
in FStar_Syntax_Syntax.Tm_let (_149_833))
in (mk _149_834))
in ((M (t2)), (_149_836), (_149_835)))))))))
end)))
end)
end)))))))
and check_n : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _149_839 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in N (_149_839))
in (match ((check env e mn)) with
| (N (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_988 -> begin
(FStar_All.failwith "[check_n]: impossible")
end)))
and check_m : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _149_842 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in M (_149_842))
in (match ((check env e mn)) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_998 -> begin
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

let _57_1020 = if (not ((is_C c))) then begin
(FStar_All.failwith "not a C")
end else begin
()
end
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos))
in (match ((let _149_851 = (FStar_Syntax_Subst.compress c)
in _149_851.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_1030 = (FStar_Syntax_Util.head_and_args wp)
in (match (_57_1030) with
| (wp_head, wp_args) -> begin
(

let _57_1031 = if ((not (((FStar_List.length wp_args) = (FStar_List.length args)))) || (not ((let _149_852 = (FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length wp_args) FStar_Range.dummyRange)
in (FStar_Syntax_Util.is_constructor wp_head _149_852))))) then begin
(FStar_All.failwith "mismatch")
end else begin
()
end
in (let _149_859 = (let _149_858 = (let _149_857 = (FStar_List.map2 (fun _57_1036 _57_1040 -> (match (((_57_1036), (_57_1040))) with
| ((arg, _57_1035), (wp_arg, _57_1039)) -> begin
(let _149_856 = (trans_F_ env arg wp_arg)
in (let _149_855 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_856), (_149_855))))
end)) args wp_args)
in ((head), (_149_857)))
in FStar_Syntax_Syntax.Tm_app (_149_858))
in (mk _149_859)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let binders = (FStar_Syntax_Util.name_binders binders)
in (

let binders = (FStar_Syntax_Subst.open_binders binders)
in (

let _57_1049 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (_57_1049) with
| (binders, comp) -> begin
(

let _57_1058 = (let _149_871 = (FStar_List.map (fun _57_1052 -> (match (_57_1052) with
| (bv, q) -> begin
(

let h = bv.FStar_Syntax_Syntax.sort
in if (is_C h) then begin
(

let w' = (let _149_861 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-w\'") None _149_861))
in (let _149_867 = (let _149_866 = (FStar_Syntax_Syntax.mk_binder w')
in (let _149_865 = (let _149_864 = (let _149_863 = (let _149_862 = (FStar_Syntax_Syntax.bv_to_name bv)
in (trans_F_ env h _149_862))
in (FStar_Syntax_Syntax.null_binder _149_863))
in (_149_864)::[])
in (_149_866)::_149_865))
in ((w'), (_149_867))))
end else begin
(

let x = (let _149_868 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-x") None _149_868))
in (let _149_870 = (let _149_869 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_869)::[])
in ((x), (_149_870))))
end)
end)) binders)
in (FStar_List.split _149_871))
in (match (_57_1058) with
| (bvs, binders) -> begin
(

let binders = (FStar_List.flatten binders)
in (

let app = (let _149_877 = (let _149_876 = (let _149_875 = (FStar_List.map (fun bv -> (let _149_874 = (FStar_Syntax_Syntax.bv_to_name bv)
in (let _149_873 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_874), (_149_873))))) bvs)
in ((wp), (_149_875)))
in FStar_Syntax_Syntax.Tm_app (_149_876))
in (mk _149_877))
in (

let comp = (let _149_879 = (type_of_comp comp)
in (let _149_878 = (is_monadic_comp comp)
in (trans_G env _149_879 _149_878 app)))
in (

let comp = (FStar_Syntax_Subst.close_comp binders comp)
in (

let binders = (FStar_Syntax_Subst.close_binders binders)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp))))))))))
end))
end))))
end
| _57_1066 -> begin
(FStar_All.failwith "impossible trans_F_")
end))))
and trans_G : env_  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env h is_monadic wp -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None h.FStar_Syntax_Syntax.pos))
in if is_monadic then begin
(let _149_890 = (let _149_889 = (star_type' env h)
in (let _149_888 = (let _149_887 = (let _149_886 = (FStar_Syntax_Syntax.as_implicit false)
in ((wp), (_149_886)))
in (_149_887)::[])
in {FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _149_889; FStar_Syntax_Syntax.effect_args = _149_888; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp _149_890))
end else begin
(let _149_891 = (trans_F_ env h wp)
in (FStar_Syntax_Syntax.mk_Total _149_891))
end))


let n : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.NoInline)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]))


let star_type : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _149_898 = (n env.env t)
in (star_type' env _149_898)))


let star_expr : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env t -> (let _149_903 = (n env.env t)
in (check_n env _149_903)))


let trans_F : env_  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> (let _149_911 = (n env.env c)
in (let _149_910 = (n env.env wp)
in (trans_F_ env _149_911 _149_910))))




