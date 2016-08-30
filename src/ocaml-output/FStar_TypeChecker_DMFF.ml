
open Prims

let gen_wps_for_free : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.sigelts * FStar_Syntax_Syntax.eff_decl) = (fun env binders a wp_a ed -> (

let wp_a = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env wp_a)
in (

let a = (

let _57_13 = a
in (let _150_11 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env a.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_13.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_13.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_11}))
in (

let d = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))
in (

let _57_20 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _57_18 = (d "Elaborating extra WP combinators")
in (let _150_14 = (FStar_Syntax_Print.term_to_string wp_a)
in (FStar_Util.print1 "wp_a is: %s\n" _150_14)))
end else begin
()
end
in (

let rec collect_binders = (fun t -> (match ((let _150_17 = (FStar_Syntax_Subst.compress t)
in _150_17.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let rest = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
t
end
| _57_31 -> begin
(FStar_All.failwith "wp_a contains non-Tot arrow")
end)
in (let _150_18 = (collect_binders rest)
in (FStar_List.append bs _150_18)))
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

let gamma = (let _150_21 = (collect_binders wp_a)
in (FStar_All.pipe_right _150_21 FStar_Syntax_Util.name_binders))
in (

let _57_41 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _150_23 = (let _150_22 = (FStar_Syntax_Print.binders_to_string ", " gamma)
in (FStar_Util.format1 "Gamma is %s\n" _150_22))
in (d _150_23))
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

let _57_54 = (let _150_33 = (let _150_32 = (FStar_ST.read sigelts)
in (sigelt)::_150_32)
in (FStar_ST.op_Colon_Equals sigelts _150_33))
in fv)
end)))
in (

let binders_of_list = (FStar_List.map (fun _57_58 -> (match (_57_58) with
| (t, b) -> begin
(let _150_36 = (FStar_Syntax_Syntax.as_implicit b)
in ((t), (_150_36)))
end)))
in (

let mk_all_implicit = (FStar_List.map (fun t -> (let _150_39 = (FStar_Syntax_Syntax.as_implicit true)
in (((Prims.fst t)), (_150_39)))))
in (

let args_of_binders = (FStar_List.map (fun bv -> (let _150_42 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst bv))
in (FStar_Syntax_Syntax.as_arg _150_42))))
in (

let _57_85 = (

let _57_70 = (

let mk = (fun f -> (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let body = (let _150_55 = (let _150_54 = (FStar_Syntax_Syntax.bv_to_name t)
in (f _150_54))
in (FStar_Syntax_Util.arrow gamma _150_55))
in (let _150_60 = (let _150_59 = (let _150_58 = (FStar_Syntax_Syntax.mk_binder a)
in (let _150_57 = (let _150_56 = (FStar_Syntax_Syntax.mk_binder t)
in (_150_56)::[])
in (_150_58)::_150_57))
in (FStar_List.append binders _150_59))
in (FStar_Syntax_Util.abs _150_60 body None)))))
in (let _150_62 = (mk FStar_Syntax_Syntax.mk_Total)
in (let _150_61 = (mk FStar_Syntax_Syntax.mk_GTotal)
in ((_150_62), (_150_61)))))
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

let mk_app = (fun fv t -> (let _150_84 = (let _150_83 = (let _150_82 = (let _150_81 = (FStar_List.map (fun _57_81 -> (match (_57_81) with
| (bv, _57_80) -> begin
(let _150_73 = (FStar_Syntax_Syntax.bv_to_name bv)
in (let _150_72 = (FStar_Syntax_Syntax.as_implicit false)
in ((_150_73), (_150_72))))
end)) binders)
in (let _150_80 = (let _150_79 = (let _150_75 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _150_74 = (FStar_Syntax_Syntax.as_implicit false)
in ((_150_75), (_150_74))))
in (let _150_78 = (let _150_77 = (let _150_76 = (FStar_Syntax_Syntax.as_implicit false)
in ((t), (_150_76)))
in (_150_77)::[])
in (_150_79)::_150_78))
in (FStar_List.append _150_81 _150_80)))
in ((fv), (_150_82)))
in FStar_Syntax_Syntax.Tm_app (_150_83))
in (mk _150_84)))
in ((env), ((mk_app ctx_fv)), ((mk_app gctx_fv))))))))
end))
in (match (_57_85) with
| (env, mk_ctx, mk_gctx) -> begin
(

let c_pure = (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let x = (let _150_89 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" None _150_89))
in (

let ret = (let _150_94 = (let _150_93 = (let _150_92 = (let _150_91 = (let _150_90 = (FStar_Syntax_Syntax.bv_to_name t)
in (mk_ctx _150_90))
in (FStar_Syntax_Syntax.mk_Total _150_91))
in (FStar_Syntax_Util.lcomp_of_comp _150_92))
in FStar_Util.Inl (_150_93))
in Some (_150_94))
in (

let body = (let _150_95 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs gamma _150_95 ret))
in (let _150_98 = (let _150_97 = (mk_all_implicit binders)
in (let _150_96 = (binders_of_list ((((a), (true)))::(((t), (true)))::(((x), (false)))::[]))
in (FStar_List.append _150_97 _150_96)))
in (FStar_Syntax_Util.abs _150_98 body ret))))))
in (

let c_pure = (let _150_99 = (mk_lid "pure")
in (register env _150_99 c_pure))
in (

let c_app = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let l = (let _150_107 = (let _150_106 = (let _150_105 = (let _150_102 = (let _150_101 = (let _150_100 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv None _150_100))
in (FStar_Syntax_Syntax.mk_binder _150_101))
in (_150_102)::[])
in (let _150_104 = (let _150_103 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _150_103))
in (FStar_Syntax_Util.arrow _150_105 _150_104)))
in (mk_gctx _150_106))
in (FStar_Syntax_Syntax.gen_bv "l" None _150_107))
in (

let r = (let _150_109 = (let _150_108 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _150_108))
in (FStar_Syntax_Syntax.gen_bv "r" None _150_109))
in (

let ret = (let _150_114 = (let _150_113 = (let _150_112 = (let _150_111 = (let _150_110 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _150_110))
in (FStar_Syntax_Syntax.mk_Total _150_111))
in (FStar_Syntax_Util.lcomp_of_comp _150_112))
in FStar_Util.Inl (_150_113))
in Some (_150_114))
in (

let outer_body = (

let gamma_as_args = (args_of_binders gamma)
in (

let inner_body = (let _150_120 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _150_119 = (let _150_118 = (let _150_117 = (let _150_116 = (let _150_115 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app _150_115 gamma_as_args))
in (FStar_Syntax_Syntax.as_arg _150_116))
in (_150_117)::[])
in (FStar_List.append gamma_as_args _150_118))
in (FStar_Syntax_Util.mk_app _150_120 _150_119)))
in (FStar_Syntax_Util.abs gamma inner_body ret)))
in (let _150_123 = (let _150_122 = (mk_all_implicit binders)
in (let _150_121 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((l), (false)))::(((r), (false)))::[]))
in (FStar_List.append _150_122 _150_121)))
in (FStar_Syntax_Util.abs _150_123 outer_body ret))))))))
in (

let c_app = (let _150_124 = (mk_lid "app")
in (register env _150_124 c_app))
in (

let c_lift1 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _150_129 = (let _150_126 = (let _150_125 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _150_125))
in (_150_126)::[])
in (let _150_128 = (let _150_127 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _150_127))
in (FStar_Syntax_Util.arrow _150_129 _150_128)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _150_131 = (let _150_130 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _150_130))
in (FStar_Syntax_Syntax.gen_bv "a1" None _150_131))
in (

let ret = (let _150_136 = (let _150_135 = (let _150_134 = (let _150_133 = (let _150_132 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _150_132))
in (FStar_Syntax_Syntax.mk_Total _150_133))
in (FStar_Syntax_Util.lcomp_of_comp _150_134))
in FStar_Util.Inl (_150_135))
in Some (_150_136))
in (let _150_148 = (let _150_138 = (mk_all_implicit binders)
in (let _150_137 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::(((a1), (false)))::[]))
in (FStar_List.append _150_138 _150_137)))
in (let _150_147 = (let _150_146 = (let _150_145 = (let _150_144 = (let _150_141 = (let _150_140 = (let _150_139 = (FStar_Syntax_Syntax.bv_to_name f)
in (_150_139)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _150_140))
in (FStar_Syntax_Util.mk_app c_pure _150_141))
in (let _150_143 = (let _150_142 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_150_142)::[])
in (_150_144)::_150_143))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _150_145))
in (FStar_Syntax_Util.mk_app c_app _150_146))
in (FStar_Syntax_Util.abs _150_148 _150_147 ret)))))))))
in (

let c_lift1 = (let _150_149 = (mk_lid "lift1")
in (register env _150_149 c_lift1))
in (

let c_lift2 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t3 = (FStar_Syntax_Syntax.gen_bv "t3" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _150_157 = (let _150_154 = (let _150_150 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _150_150))
in (let _150_153 = (let _150_152 = (let _150_151 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.null_binder _150_151))
in (_150_152)::[])
in (_150_154)::_150_153))
in (let _150_156 = (let _150_155 = (FStar_Syntax_Syntax.bv_to_name t3)
in (FStar_Syntax_Syntax.mk_GTotal _150_155))
in (FStar_Syntax_Util.arrow _150_157 _150_156)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _150_159 = (let _150_158 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _150_158))
in (FStar_Syntax_Syntax.gen_bv "a1" None _150_159))
in (

let a2 = (let _150_161 = (let _150_160 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _150_160))
in (FStar_Syntax_Syntax.gen_bv "a2" None _150_161))
in (

let ret = (let _150_166 = (let _150_165 = (let _150_164 = (let _150_163 = (let _150_162 = (FStar_Syntax_Syntax.bv_to_name t3)
in (mk_gctx _150_162))
in (FStar_Syntax_Syntax.mk_Total _150_163))
in (FStar_Syntax_Util.lcomp_of_comp _150_164))
in FStar_Util.Inl (_150_165))
in Some (_150_166))
in (let _150_183 = (let _150_168 = (mk_all_implicit binders)
in (let _150_167 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((t3), (true)))::(((f), (false)))::(((a1), (false)))::(((a2), (false)))::[]))
in (FStar_List.append _150_168 _150_167)))
in (let _150_182 = (let _150_181 = (let _150_180 = (let _150_179 = (let _150_176 = (let _150_175 = (let _150_174 = (let _150_171 = (let _150_170 = (let _150_169 = (FStar_Syntax_Syntax.bv_to_name f)
in (_150_169)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _150_170))
in (FStar_Syntax_Util.mk_app c_pure _150_171))
in (let _150_173 = (let _150_172 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_150_172)::[])
in (_150_174)::_150_173))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _150_175))
in (FStar_Syntax_Util.mk_app c_app _150_176))
in (let _150_178 = (let _150_177 = (FStar_Syntax_Syntax.bv_to_name a2)
in (_150_177)::[])
in (_150_179)::_150_178))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _150_180))
in (FStar_Syntax_Util.mk_app c_app _150_181))
in (FStar_Syntax_Util.abs _150_183 _150_182 ret)))))))))))
in (

let c_lift2 = (let _150_184 = (mk_lid "lift2")
in (register env _150_184 c_lift2))
in (

let c_push = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _150_190 = (let _150_186 = (let _150_185 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _150_185))
in (_150_186)::[])
in (let _150_189 = (let _150_188 = (let _150_187 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _150_187))
in (FStar_Syntax_Syntax.mk_Total _150_188))
in (FStar_Syntax_Util.arrow _150_190 _150_189)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let ret = (let _150_200 = (let _150_199 = (let _150_198 = (let _150_197 = (let _150_196 = (let _150_195 = (let _150_192 = (let _150_191 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _150_191))
in (_150_192)::[])
in (let _150_194 = (let _150_193 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _150_193))
in (FStar_Syntax_Util.arrow _150_195 _150_194)))
in (mk_ctx _150_196))
in (FStar_Syntax_Syntax.mk_Total _150_197))
in (FStar_Syntax_Util.lcomp_of_comp _150_198))
in FStar_Util.Inl (_150_199))
in Some (_150_200))
in (

let e1 = (let _150_201 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" None _150_201))
in (

let body = (let _150_210 = (let _150_203 = (let _150_202 = (FStar_Syntax_Syntax.mk_binder e1)
in (_150_202)::[])
in (FStar_List.append gamma _150_203))
in (let _150_209 = (let _150_208 = (FStar_Syntax_Syntax.bv_to_name f)
in (let _150_207 = (let _150_206 = (let _150_204 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg _150_204))
in (let _150_205 = (args_of_binders gamma)
in (_150_206)::_150_205))
in (FStar_Syntax_Util.mk_app _150_208 _150_207)))
in (FStar_Syntax_Util.abs _150_210 _150_209 ret)))
in (let _150_213 = (let _150_212 = (mk_all_implicit binders)
in (let _150_211 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::[]))
in (FStar_List.append _150_212 _150_211)))
in (FStar_Syntax_Util.abs _150_213 body ret)))))))))
in (

let c_push = (let _150_214 = (mk_lid "push")
in (register env _150_214 c_push))
in (

let ret_tot_wp_a = (let _150_217 = (let _150_216 = (let _150_215 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.lcomp_of_comp _150_215))
in FStar_Util.Inl (_150_216))
in Some (_150_217))
in (

let mk_generic_app = (fun c -> if ((FStar_List.length binders) > (Prims.parse_int "0")) then begin
(let _150_222 = (let _150_221 = (let _150_220 = (args_of_binders binders)
in ((c), (_150_220)))
in FStar_Syntax_Syntax.Tm_app (_150_221))
in (mk _150_222))
end else begin
c
end)
in (

let wp_if_then_else = (

let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (let _150_240 = (let _150_223 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (FStar_List.append binders _150_223))
in (let _150_239 = (

let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_unfoldable ((Prims.parse_int "2"))) None)
in (let _150_238 = (let _150_229 = (let _150_228 = (let _150_227 = (let _150_226 = (let _150_225 = (let _150_224 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg _150_224))
in (_150_225)::[])
in (FStar_Syntax_Util.mk_app l_ite _150_226))
in (_150_227)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _150_228))
in (FStar_Syntax_Util.mk_app c_lift2 _150_229))
in (let _150_237 = (let _150_236 = (let _150_235 = (let _150_234 = (let _150_232 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _150_231 = (let _150_230 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_150_230)::[])
in (_150_232)::_150_231))
in (let _150_233 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_234 _150_233)))
in (FStar_Syntax_Syntax.mk_Total _150_235))
in FStar_Util.Inr (_150_236))
in (FStar_Syntax_Util.ascribe _150_238 _150_237))))
in (FStar_Syntax_Util.abs _150_240 _150_239 ret_tot_wp_a))))
in (

let wp_if_then_else = (let _150_241 = (mk_lid "wp_if_then_else")
in (register env _150_241 wp_if_then_else))
in (

let wp_if_then_else = (mk_generic_app wp_if_then_else)
in (

let wp_assert = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_and = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.and_lid (FStar_Syntax_Syntax.Delta_unfoldable ((Prims.parse_int "1"))) None)
in (

let body = (let _150_252 = (let _150_251 = (let _150_250 = (let _150_247 = (let _150_246 = (let _150_245 = (let _150_244 = (let _150_243 = (let _150_242 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _150_242))
in (_150_243)::[])
in (FStar_Syntax_Util.mk_app l_and _150_244))
in (_150_245)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _150_246))
in (FStar_Syntax_Util.mk_app c_pure _150_247))
in (let _150_249 = (let _150_248 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_150_248)::[])
in (_150_250)::_150_249))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _150_251))
in (FStar_Syntax_Util.mk_app c_app _150_252))
in (let _150_254 = (let _150_253 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders _150_253))
in (FStar_Syntax_Util.abs _150_254 body ret_tot_wp_a))))))
in (

let wp_assert = (let _150_255 = (mk_lid "wp_assert")
in (register env _150_255 wp_assert))
in (

let wp_assert = (mk_generic_app wp_assert)
in (

let wp_assume = (

let q = (FStar_Syntax_Syntax.gen_bv "q" None FStar_Syntax_Util.ktype)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let l_imp = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.imp_lid (FStar_Syntax_Syntax.Delta_unfoldable ((Prims.parse_int "1"))) None)
in (

let body = (let _150_266 = (let _150_265 = (let _150_264 = (let _150_261 = (let _150_260 = (let _150_259 = (let _150_258 = (let _150_257 = (let _150_256 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _150_256))
in (_150_257)::[])
in (FStar_Syntax_Util.mk_app l_imp _150_258))
in (_150_259)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _150_260))
in (FStar_Syntax_Util.mk_app c_pure _150_261))
in (let _150_263 = (let _150_262 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_150_262)::[])
in (_150_264)::_150_263))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _150_265))
in (FStar_Syntax_Util.mk_app c_app _150_266))
in (let _150_268 = (let _150_267 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders _150_267))
in (FStar_Syntax_Util.abs _150_268 body ret_tot_wp_a))))))
in (

let wp_assume = (let _150_269 = (mk_lid "wp_assume")
in (register env _150_269 wp_assume))
in (

let wp_assume = (mk_generic_app wp_assume)
in (

let wp_close = (

let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _150_273 = (let _150_271 = (let _150_270 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _150_270))
in (_150_271)::[])
in (let _150_272 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _150_273 _150_272)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let body = (let _150_282 = (let _150_281 = (let _150_280 = (let _150_274 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((FStar_Syntax_Util.tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure _150_274))
in (let _150_279 = (let _150_278 = (let _150_277 = (let _150_276 = (let _150_275 = (FStar_Syntax_Syntax.bv_to_name f)
in (_150_275)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _150_276))
in (FStar_Syntax_Util.mk_app c_push _150_277))
in (_150_278)::[])
in (_150_280)::_150_279))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _150_281))
in (FStar_Syntax_Util.mk_app c_app _150_282))
in (let _150_284 = (let _150_283 = (FStar_Syntax_Syntax.binders_of_list ((a)::(b)::(f)::[]))
in (FStar_List.append binders _150_283))
in (FStar_Syntax_Util.abs _150_284 body ret_tot_wp_a))))))
in (

let wp_close = (let _150_285 = (mk_lid "wp_close")
in (register env _150_285 wp_close))
in (

let wp_close = (mk_generic_app wp_close)
in (

let ret_tot_type = (let _150_288 = (let _150_287 = (let _150_286 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_286))
in FStar_Util.Inl (_150_287))
in Some (_150_288))
in (

let ret_gtot_type = (let _150_291 = (let _150_290 = (let _150_289 = (FStar_Syntax_Syntax.mk_GTotal FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_289))
in FStar_Util.Inl (_150_290))
in Some (_150_291))
in (

let mk_forall = (fun x body -> (let _150_302 = (let _150_301 = (let _150_300 = (let _150_299 = (let _150_298 = (let _150_297 = (let _150_296 = (FStar_Syntax_Syntax.mk_binder x)
in (_150_296)::[])
in (FStar_Syntax_Util.abs _150_297 body ret_tot_type))
in (FStar_Syntax_Syntax.as_arg _150_298))
in (_150_299)::[])
in ((FStar_Syntax_Util.tforall), (_150_300)))
in FStar_Syntax_Syntax.Tm_app (_150_301))
in (FStar_Syntax_Syntax.mk _150_302 None FStar_Range.dummyRange)))
in (

let is_zero_order = (fun t -> (match ((let _150_305 = (FStar_Syntax_Subst.compress t)
in _150_305.FStar_Syntax_Syntax.n)) with
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
in (match ((let _150_327 = (FStar_Syntax_Subst.compress t)
in _150_327.FStar_Syntax_Syntax.n)) with
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

let body = (let _150_335 = (let _150_330 = (let _150_329 = (let _150_328 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _150_328))
in (_150_329)::[])
in (FStar_Syntax_Util.mk_app x _150_330))
in (let _150_334 = (let _150_333 = (let _150_332 = (let _150_331 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _150_331))
in (_150_332)::[])
in (FStar_Syntax_Util.mk_app y _150_333))
in (mk_rel b _150_335 _150_334)))
in (mk_forall a1 body)))
end else begin
(

let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (

let a2 = (FStar_Syntax_Syntax.gen_bv "a2" None a)
in (

let body = (let _150_347 = (let _150_337 = (FStar_Syntax_Syntax.bv_to_name a1)
in (let _150_336 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_rel a _150_337 _150_336)))
in (let _150_346 = (let _150_345 = (let _150_340 = (let _150_339 = (let _150_338 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _150_338))
in (_150_339)::[])
in (FStar_Syntax_Util.mk_app x _150_340))
in (let _150_344 = (let _150_343 = (let _150_342 = (let _150_341 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg _150_341))
in (_150_342)::[])
in (FStar_Syntax_Util.mk_app y _150_343))
in (mk_rel b _150_345 _150_344)))
in (FStar_Syntax_Util.mk_imp _150_347 _150_346)))
in (let _150_348 = (mk_forall a2 body)
in (mk_forall a1 _150_348)))))
end)
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::binders, comp) -> begin
(

let t = (

let _57_219 = t
in (let _150_352 = (let _150_351 = (let _150_350 = (let _150_349 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _150_349))
in (((binder)::[]), (_150_350)))
in FStar_Syntax_Syntax.Tm_arrow (_150_351))
in {FStar_Syntax_Syntax.n = _150_352; FStar_Syntax_Syntax.tk = _57_219.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_219.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_219.FStar_Syntax_Syntax.vars}))
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

let body = (let _150_354 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (let _150_353 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_rel FStar_Syntax_Util.mk_imp wp_a _150_354 _150_353)))
in (let _150_356 = (let _150_355 = (binders_of_list ((((a), (false)))::(((wp1), (false)))::(((wp2), (false)))::[]))
in (FStar_List.append binders _150_355))
in (FStar_Syntax_Util.abs _150_356 body ret_tot_type)))))
in (

let stronger = (let _150_357 = (mk_lid "stronger")
in (register env _150_357 stronger))
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

let eq = (let _150_358 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst post))
in (mk_rel FStar_Syntax_Util.mk_iff k.FStar_Syntax_Syntax.sort k_tm _150_358))
in (match ((FStar_Syntax_Util.destruct_typ_as_formula eq)) with
| Some (FStar_Syntax_Util.QAll (binders, [], body)) -> begin
(

let k_app = (let _150_359 = (args_of_binders binders)
in (FStar_Syntax_Util.mk_app k_tm _150_359))
in (

let guard_free = (let _150_360 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.guard_free FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _150_360))
in (

let pat = (let _150_362 = (let _150_361 = (FStar_Syntax_Syntax.as_arg k_app)
in (_150_361)::[])
in (FStar_Syntax_Util.mk_app guard_free _150_362))
in (

let pattern_guarded_body = (let _150_368 = (let _150_367 = (let _150_366 = (let _150_365 = (let _150_364 = (let _150_363 = (FStar_Syntax_Syntax.as_arg pat)
in (_150_363)::[])
in (_150_364)::[])
in FStar_Syntax_Syntax.Meta_pattern (_150_365))
in ((body), (_150_366)))
in FStar_Syntax_Syntax.Tm_meta (_150_367))
in (mk _150_368))
in (FStar_Syntax_Util.close_forall binders pattern_guarded_body)))))
end
| _57_251 -> begin
(FStar_All.failwith "Impossible: Expected the equivalence to be a quantified formula")
end)))
in (

let body = (let _150_377 = (let _150_376 = (let _150_375 = (let _150_374 = (FStar_Syntax_Syntax.bv_to_name wp)
in (let _150_373 = (let _150_372 = (args_of_binders wp_args)
in (let _150_371 = (let _150_370 = (let _150_369 = (FStar_Syntax_Syntax.bv_to_name k)
in (FStar_Syntax_Syntax.as_arg _150_369))
in (_150_370)::[])
in (FStar_List.append _150_372 _150_371)))
in (FStar_Syntax_Util.mk_app _150_374 _150_373)))
in (FStar_Syntax_Util.mk_imp equiv _150_375))
in (FStar_Syntax_Util.mk_forall k _150_376))
in (FStar_Syntax_Util.abs gamma _150_377 ret_gtot_type))
in (let _150_379 = (let _150_378 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders _150_378))
in (FStar_Syntax_Util.abs _150_379 body ret_gtot_type)))))
end)))
in (

let wp_ite = (let _150_380 = (mk_lid "wp_ite")
in (register env _150_380 wp_ite))
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

let body = (let _150_385 = (let _150_384 = (FStar_All.pipe_left FStar_Syntax_Syntax.bv_to_name (Prims.fst post))
in (let _150_383 = (let _150_382 = (let _150_381 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _150_381))
in (_150_382)::[])
in (FStar_Syntax_Util.mk_app _150_384 _150_383)))
in (FStar_Syntax_Util.mk_forall x _150_385))
in (let _150_388 = (let _150_387 = (let _150_386 = (FStar_Syntax_Syntax.binders_of_list ((a)::[]))
in (FStar_List.append _150_386 gamma))
in (FStar_List.append binders _150_387))
in (FStar_Syntax_Util.abs _150_388 body ret_gtot_type))))
end)))
in (

let null_wp = (let _150_389 = (mk_lid "null_wp")
in (register env _150_389 null_wp))
in (

let null_wp = (mk_generic_app null_wp)
in (

let wp_trivial = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let body = (let _150_399 = (let _150_398 = (let _150_397 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _150_396 = (let _150_395 = (let _150_392 = (let _150_391 = (let _150_390 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg _150_390))
in (_150_391)::[])
in (FStar_Syntax_Util.mk_app null_wp _150_392))
in (let _150_394 = (let _150_393 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_150_393)::[])
in (_150_395)::_150_394))
in (_150_397)::_150_396))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _150_398))
in (FStar_Syntax_Util.mk_app stronger _150_399))
in (let _150_401 = (let _150_400 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders _150_400))
in (FStar_Syntax_Util.abs _150_401 body ret_tot_type))))
in (

let wp_trivial = (let _150_402 = (mk_lid "wp_trivial")
in (register env _150_402 wp_trivial))
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
in (let _150_422 = (let _150_404 = (FStar_ST.read sigelts)
in (FStar_List.rev _150_404))
in (let _150_421 = (

let _57_274 = ed
in (let _150_420 = (let _150_405 = (c wp_if_then_else)
in (([]), (_150_405)))
in (let _150_419 = (let _150_406 = (c wp_ite)
in (([]), (_150_406)))
in (let _150_418 = (let _150_407 = (c stronger)
in (([]), (_150_407)))
in (let _150_417 = (let _150_408 = (c wp_close)
in (([]), (_150_408)))
in (let _150_416 = (let _150_409 = (c wp_assert)
in (([]), (_150_409)))
in (let _150_415 = (let _150_410 = (c wp_assume)
in (([]), (_150_410)))
in (let _150_414 = (let _150_411 = (c null_wp)
in (([]), (_150_411)))
in (let _150_413 = (let _150_412 = (c wp_trivial)
in (([]), (_150_412)))
in {FStar_Syntax_Syntax.qualifiers = _57_274.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_274.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_274.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_274.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_274.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _57_274.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _57_274.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _150_420; FStar_Syntax_Syntax.ite_wp = _150_419; FStar_Syntax_Syntax.stronger = _150_418; FStar_Syntax_Syntax.close_wp = _150_417; FStar_Syntax_Syntax.assert_p = _150_416; FStar_Syntax_Syntax.assume_p = _150_415; FStar_Syntax_Syntax.null_wp = _150_414; FStar_Syntax_Syntax.trivial = _150_413; FStar_Syntax_Syntax.repr = _57_274.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _57_274.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _57_274.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _57_274.FStar_Syntax_Syntax.actions})))))))))
in ((_150_422), (_150_421)))))))))))))))))))))))))))))))))))))))))))))))
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
(let _150_480 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "N[%s]" _150_480))
end
| M (t) -> begin
(let _150_481 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "M[%s]" _150_481))
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


let rec mk_star_to_type : (FStar_Syntax_Syntax.term'  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun mk env a -> (let _150_505 = (let _150_504 = (let _150_503 = (let _150_501 = (let _150_500 = (let _150_498 = (star_type' env a)
in (FStar_Syntax_Syntax.null_bv _150_498))
in (let _150_499 = (FStar_Syntax_Syntax.as_implicit false)
in ((_150_500), (_150_499))))
in (_150_501)::[])
in (let _150_502 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_150_503), (_150_502))))
in FStar_Syntax_Syntax.Tm_arrow (_150_504))
in (mk _150_505)))
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
(let _150_514 = (

let _57_339 = bv
in (let _150_513 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_339.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_339.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_513}))
in ((_150_514), (aqual)))
end)) binders)
in (match ((is_monadic_arrow t.FStar_Syntax_Syntax.n)) with
| N (hn) -> begin
(let _150_518 = (let _150_517 = (let _150_516 = (let _150_515 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_Total _150_515))
in ((binders), (_150_516)))
in FStar_Syntax_Syntax.Tm_arrow (_150_517))
in (mk _150_518))
end
| M (a) -> begin
(let _150_527 = (let _150_526 = (let _150_525 = (let _150_523 = (let _150_522 = (let _150_521 = (let _150_519 = (mk_star_to_type env a)
in (FStar_Syntax_Syntax.null_bv _150_519))
in (let _150_520 = (FStar_Syntax_Syntax.as_implicit false)
in ((_150_521), (_150_520))))
in (_150_522)::[])
in (FStar_List.append binders _150_523))
in (let _150_524 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_150_525), (_150_524))))
in FStar_Syntax_Syntax.Tm_arrow (_150_526))
in (mk _150_527))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let is_valid_application = (fun head -> (match ((let _150_530 = (FStar_Syntax_Subst.compress head)
in _150_530.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.option_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.either_lid)) || (let _150_531 = (FStar_Syntax_Subst.compress head)
in (FStar_Syntax_Util.is_tuple_constructor _150_531))) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uinst (_57_355) -> begin
(FStar_All.failwith "impossible (Tm_uinst)")
end
| _57_358 -> begin
false
end))
in if (is_valid_application head) then begin
(let _150_536 = (let _150_535 = (let _150_534 = (FStar_List.map (fun _57_361 -> (match (_57_361) with
| (t, qual) -> begin
(let _150_533 = (star_type' env t)
in ((_150_533), (qual)))
end)) args)
in ((head), (_150_534)))
in FStar_Syntax_Syntax.Tm_app (_150_535))
in (mk _150_536))
end else begin
(let _150_539 = (let _150_538 = (let _150_537 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "For now, only [either] and [option] are supported in the definition language (got: %s)" _150_537))
in FStar_Syntax_Syntax.Err (_150_538))
in (Prims.raise _150_539))
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
in (let _150_540 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _150_540; subst = _57_382.subst; tc_const = _57_382.tc_const}))
in (

let repr = (star_type' env repr)
in (FStar_Syntax_Util.abs binders repr something)))
end))
end
| (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_match (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _150_543 = (let _150_542 = (let _150_541 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "The following term is outside of the definition language: %s" _150_541))
in FStar_Syntax_Syntax.Err (_150_542))
in (Prims.raise _150_543))
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


let rec is_C : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match ((let _150_551 = (FStar_Syntax_Subst.compress t)
in _150_551.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) when (FStar_Syntax_Util.is_tuple_constructor head) -> begin
(

let r = (let _150_553 = (let _150_552 = (FStar_List.hd args)
in (Prims.fst _150_552))
in (is_C _150_553))
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

let body = (let _150_569 = (let _150_568 = (let _150_567 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _150_566 = (let _150_565 = (let _150_564 = (FStar_Syntax_Syntax.as_implicit false)
in ((e), (_150_564)))
in (_150_565)::[])
in ((_150_567), (_150_566))))
in FStar_Syntax_Syntax.Tm_app (_150_568))
in (mk _150_569))
in (let _150_571 = (let _150_570 = (FStar_Syntax_Syntax.mk_binder p)
in (_150_570)::[])
in (FStar_Syntax_Util.abs _150_571 body None)))))))


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

let check = (fun t1 t2 -> if ((not ((is_unknown t2.FStar_Syntax_Syntax.n))) && (not ((let _150_625 = (FStar_TypeChecker_Rel.teq env.env t1 t2)
in (FStar_TypeChecker_Rel.is_trivial _150_625))))) then begin
(let _150_630 = (let _150_629 = (let _150_628 = (FStar_Syntax_Print.term_to_string e)
in (let _150_627 = (FStar_Syntax_Print.term_to_string t1)
in (let _150_626 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check]: the expression [%s] has type [%s] but should have type [%s]" _150_628 _150_627 _150_626))))
in FStar_Syntax_Syntax.Err (_150_629))
in (Prims.raise _150_630))
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
in (let _150_631 = (mk_return env t1 s_e)
in ((M (t1)), (_150_631), (u_e))))
end
| (M (t1), N (t2)) -> begin
(let _150_636 = (let _150_635 = (let _150_634 = (FStar_Syntax_Print.term_to_string e)
in (let _150_633 = (FStar_Syntax_Print.term_to_string t1)
in (let _150_632 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]" _150_634 _150_633 _150_632))))
in FStar_Syntax_Syntax.Err (_150_635))
in (Prims.raise _150_636))
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
(let _150_643 = (check env e2 context_nm)
in (strip_m _150_643))
end)))
in (match ((let _150_644 = (FStar_Syntax_Subst.compress e)
in _150_644.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
(let _150_645 = (infer env e)
in (return_if _150_645))
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
(let _150_653 = (let _150_652 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_let %s" _150_652))
in (FStar_All.failwith _150_653))
end
| FStar_Syntax_Syntax.Tm_type (_57_592) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_595) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_57_598) -> begin
(let _150_655 = (let _150_654 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_refine %s" _150_654))
in (FStar_All.failwith _150_655))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_601) -> begin
(let _150_657 = (let _150_656 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_uvar %s" _150_656))
in (FStar_All.failwith _150_657))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_604) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _150_662 = (let _150_661 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_unknown %s" _150_661))
in (FStar_All.failwith _150_662))
end)))))
and infer : env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.env)
in (match ((let _150_668 = (FStar_Syntax_Subst.compress e)
in _150_668.FStar_Syntax_Syntax.n)) with
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
in (let _150_669 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _150_669; subst = _57_624.subst; tc_const = _57_624.tc_const}))
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

let xw = (let _150_673 = (star_type' env c)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "^w") None _150_673))
in (

let x = (

let _57_642 = bv
in (let _150_675 = (let _150_674 = (FStar_Syntax_Syntax.bv_to_name xw)
in (trans_F_ env c _150_674))
in {FStar_Syntax_Syntax.ppname = _57_642.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_642.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_675}))
in (

let env = (

let _57_645 = env
in (let _150_679 = (let _150_678 = (let _150_677 = (let _150_676 = (FStar_Syntax_Syntax.bv_to_name xw)
in ((bv), (_150_676)))
in FStar_Syntax_Syntax.NT (_150_677))
in (_150_678)::env.subst)
in {env = _57_645.env; subst = _150_679; tc_const = _57_645.tc_const}))
in (let _150_683 = (let _150_682 = (FStar_Syntax_Syntax.mk_binder x)
in (let _150_681 = (let _150_680 = (FStar_Syntax_Syntax.mk_binder xw)
in (_150_680)::acc)
in (_150_682)::_150_681))
in ((env), (_150_683))))))
end else begin
(

let x = (

let _57_648 = bv
in (let _150_684 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_648.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_648.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_684}))
in (let _150_686 = (let _150_685 = (FStar_Syntax_Syntax.mk_binder x)
in (_150_685)::acc)
in ((env), (_150_686))))
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
(let _150_692 = (let _150_691 = if (is_monadic what) then begin
M (t)
end else begin
N (t)
end
in (comp_of_nm _150_691))
in ((_150_692), (s_body), (u_body)))
end)))
in (match (_57_663) with
| (comp, s_body, u_body) -> begin
(

let t = (

let binders = (FStar_List.map (fun _57_667 -> (match (_57_667) with
| (bv, _57_666) -> begin
(let _150_694 = (FStar_Syntax_Syntax.null_bv bv.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_binder _150_694))
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
(let _150_697 = (let _150_696 = (normalize t)
in N (_150_696))
in ((_150_697), (e), (e)))
end else begin
(let _150_699 = (let _150_698 = (FStar_Util.format1 "The %s constructor has not been whitelisted for the definition language; if this is a function application, consider using [inline]" txt)
in FStar_Syntax_Syntax.Err (_150_698))
in (Prims.raise _150_699))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_703 = (check_n env head)
in (match (_57_703) with
| (t_head, s_head, u_head) -> begin
(

let is_arrow = (fun t -> (match ((let _150_702 = (FStar_Syntax_Subst.compress t)
in _150_702.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_707) -> begin
true
end
| _57_710 -> begin
false
end))
in (

let rec flatten = (fun t -> (match ((let _150_705 = (FStar_Syntax_Subst.compress t)
in _150_705.FStar_Syntax_Syntax.n)) with
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
(let _150_708 = (let _150_707 = (let _150_706 = (FStar_Syntax_Print.term_to_string t_head)
in (FStar_Util.format1 "%s: not a function type" _150_706))
in FStar_Syntax_Syntax.Err (_150_707))
in (Prims.raise _150_708))
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
(let _150_713 = (let _150_712 = (let _150_711 = (FStar_Util.string_of_int n)
in (let _150_710 = (FStar_Util.string_of_int (n' - n))
in (let _150_709 = (FStar_Util.string_of_int n)
in (FStar_Util.format3 "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments." _150_711 _150_710 _150_709))))
in FStar_Syntax_Syntax.Err (_150_712))
in (Prims.raise _150_713))
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
(let _150_721 = (let _150_720 = (FStar_Syntax_Subst.subst_comp subst comp)
in _150_720.FStar_Syntax_Syntax.n)
in (nm_of_comp _150_721))
end
| (binders, []) -> begin
(match ((let _150_724 = (let _150_723 = (let _150_722 = (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))))
in (FStar_Syntax_Subst.subst subst _150_722))
in (FStar_Syntax_Subst.compress _150_723))
in _150_724.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(let _150_728 = (let _150_727 = (let _150_726 = (let _150_725 = (FStar_Syntax_Subst.close_comp binders comp)
in ((binders), (_150_725)))
in FStar_Syntax_Syntax.Tm_arrow (_150_726))
in (mk _150_727))
in N (_150_728))
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

let _57_803 = (let _150_743 = (FStar_List.map2 (fun _57_786 _57_789 -> (match (((_57_786), (_57_789))) with
| ((bv, _57_785), (arg, q)) -> begin
(match ((let _150_731 = (FStar_Syntax_Subst.compress bv.FStar_Syntax_Syntax.sort)
in _150_731.FStar_Syntax_Syntax.n)) with
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
(let _150_742 = (let _150_732 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_arg), (_150_732)))
in (let _150_741 = if (is_C bv.FStar_Syntax_Syntax.sort) then begin
(let _150_738 = (let _150_734 = (FStar_Syntax_Subst.subst env.subst s_arg)
in (let _150_733 = (FStar_Syntax_Syntax.as_implicit false)
in ((_150_734), (_150_733))))
in (let _150_737 = (let _150_736 = (let _150_735 = (FStar_Syntax_Syntax.as_implicit false)
in ((u_arg), (_150_735)))
in (_150_736)::[])
in (_150_738)::_150_737))
end else begin
(let _150_740 = (let _150_739 = (FStar_Syntax_Syntax.as_implicit false)
in ((u_arg), (_150_739)))
in (_150_740)::[])
end
in ((_150_742), (_150_741))))
end))
end)
end)) binders args)
in (FStar_List.split _150_743))
in (match (_57_803) with
| (s_args, u_args) -> begin
(

let u_args = (FStar_List.flatten u_args)
in (let _150_745 = (mk (FStar_Syntax_Syntax.Tm_app (((s_head), (s_args)))))
in (let _150_744 = (mk (FStar_Syntax_Syntax.Tm_app (((u_head), (u_args)))))
in ((final_type), (_150_745), (_150_744)))))
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
(let _150_747 = (let _150_746 = (env.tc_const c)
in N (_150_746))
in ((_150_747), (e), (e)))
end
| FStar_Syntax_Syntax.Tm_let (_57_834) -> begin
(let _150_749 = (let _150_748 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_let %s" _150_748))
in (FStar_All.failwith _150_749))
end
| FStar_Syntax_Syntax.Tm_type (_57_837) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_840) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_57_843) -> begin
(let _150_751 = (let _150_750 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_refine %s" _150_750))
in (FStar_All.failwith _150_751))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_846) -> begin
(let _150_753 = (let _150_752 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_uvar %s" _150_752))
in (FStar_All.failwith _150_753))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_849) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _150_758 = (let _150_757 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_unknown %s" _150_757))
in (FStar_All.failwith _150_758))
end))))
and mk_match : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e0 branches f -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e0.FStar_Syntax_Syntax.pos))
in (

let _57_862 = (check_n env e0)
in (match (_57_862) with
| (_57_859, s_e0, u_e0) -> begin
(

let _57_879 = (let _150_774 = (FStar_List.map (fun b -> (match ((FStar_Syntax_Subst.open_branch b)) with
| (pat, None, body) -> begin
(

let env = (

let _57_868 = env
in (let _150_773 = (let _150_772 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env.env _150_772))
in {env = _150_773; subst = _57_868.subst; tc_const = _57_868.tc_const}))
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
in (FStar_List.split _150_774))
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

let _57_923 = (let _150_778 = (FStar_List.map2 (fun nm _57_898 -> (match (_57_898) with
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
in (FStar_List.unzip3 _150_778))
in (match (_57_923) with
| (nms, s_branches, u_branches) -> begin
(

let s_branches = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let t1_star = if has_m then begin
(let _150_783 = (let _150_781 = (let _150_780 = (let _150_779 = (mk_star_to_type mk env t1)
in (FStar_Syntax_Syntax.new_bv None _150_779))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _150_780))
in (_150_781)::[])
in (let _150_782 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _150_783 _150_782)))
end else begin
t1
end
in (let _150_788 = (let _150_786 = (let _150_785 = (let _150_784 = (mk (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches)))))
in ((_150_784), (FStar_Util.Inl (t1_star)), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (_150_785))
in (mk _150_786))
in (let _150_787 = (mk (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches)))))
in ((if has_m then begin
M (t1)
end else begin
N (t1)
end), (_150_788), (_150_787)))))))
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

let x_binders = (let _150_808 = (FStar_Syntax_Syntax.mk_binder x)
in (_150_808)::[])
in (

let _57_939 = (FStar_Syntax_Subst.open_term x_binders e2)
in (match (_57_939) with
| (x_binders, e2) -> begin
(match ((infer env e1)) with
| (N (t1), s_e1, u_e1) -> begin
(

let env = (

let _57_945 = env
in (let _150_809 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_947 = x
in {FStar_Syntax_Syntax.ppname = _57_947.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_947.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _150_809; subst = _57_945.subst; tc_const = _57_945.tc_const}))
in (

let _57_953 = (proceed env e2)
in (match (_57_953) with
| (nm_rec, s_e2, u_e2) -> begin
(let _150_817 = (let _150_812 = (let _150_811 = (let _150_810 = (FStar_Syntax_Subst.close x_binders s_e2)
in ((((false), (((

let _57_954 = binding
in {FStar_Syntax_Syntax.lbname = _57_954.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_954.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_954.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_954.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = s_e1}))::[]))), (_150_810)))
in FStar_Syntax_Syntax.Tm_let (_150_811))
in (mk _150_812))
in (let _150_816 = (let _150_815 = (let _150_814 = (let _150_813 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _57_956 = binding
in {FStar_Syntax_Syntax.lbname = _57_956.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_956.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_956.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_956.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_150_813)))
in FStar_Syntax_Syntax.Tm_let (_150_814))
in (mk _150_815))
in ((nm_rec), (_150_817), (_150_816))))
end)))
end
| (M (t1), s_e1, u_e1) -> begin
(

let env = (

let _57_963 = env
in (let _150_818 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_965 = x
in {FStar_Syntax_Syntax.ppname = _57_965.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_965.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _150_818; subst = _57_963.subst; tc_const = _57_963.tc_const}))
in (

let _57_971 = (ensure_m env e2)
in (match (_57_971) with
| (t2, s_e2, u_e2) -> begin
(

let p_type = (mk_star_to_type mk env t2)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" None p_type)
in (

let s_e2 = (let _150_824 = (let _150_823 = (let _150_822 = (let _150_821 = (let _150_820 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _150_819 = (FStar_Syntax_Syntax.as_implicit false)
in ((_150_820), (_150_819))))
in (_150_821)::[])
in ((s_e2), (_150_822)))
in FStar_Syntax_Syntax.Tm_app (_150_823))
in (mk _150_824))
in (

let s_e2 = (FStar_Syntax_Util.abs x_binders s_e2 None)
in (

let body = (let _150_829 = (let _150_828 = (let _150_827 = (let _150_826 = (let _150_825 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_e2), (_150_825)))
in (_150_826)::[])
in ((s_e1), (_150_827)))
in FStar_Syntax_Syntax.Tm_app (_150_828))
in (mk _150_829))
in (let _150_836 = (let _150_831 = (let _150_830 = (FStar_Syntax_Syntax.mk_binder p)
in (_150_830)::[])
in (FStar_Syntax_Util.abs _150_831 body None))
in (let _150_835 = (let _150_834 = (let _150_833 = (let _150_832 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _57_977 = binding
in {FStar_Syntax_Syntax.lbname = _57_977.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_977.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_977.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_977.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_150_832)))
in FStar_Syntax_Syntax.Tm_let (_150_833))
in (mk _150_834))
in ((M (t2)), (_150_836), (_150_835)))))))))
end)))
end)
end)))))))
and check_n : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _150_839 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in N (_150_839))
in (match ((check env e mn)) with
| (N (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_988 -> begin
(FStar_All.failwith "[check_n]: impossible")
end)))
and check_m : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _150_842 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in M (_150_842))
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
in (match ((let _150_851 = (FStar_Syntax_Subst.compress c)
in _150_851.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_1030 = (FStar_Syntax_Util.head_and_args wp)
in (match (_57_1030) with
| (wp_head, wp_args) -> begin
(

let _57_1031 = if ((not (((FStar_List.length wp_args) = (FStar_List.length args)))) || (not ((let _150_852 = (FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length wp_args) FStar_Range.dummyRange)
in (FStar_Syntax_Util.is_constructor wp_head _150_852))))) then begin
(FStar_All.failwith "mismatch")
end else begin
()
end
in (let _150_859 = (let _150_858 = (let _150_857 = (FStar_List.map2 (fun _57_1036 _57_1040 -> (match (((_57_1036), (_57_1040))) with
| ((arg, _57_1035), (wp_arg, _57_1039)) -> begin
(let _150_856 = (trans_F_ env arg wp_arg)
in (let _150_855 = (FStar_Syntax_Syntax.as_implicit false)
in ((_150_856), (_150_855))))
end)) args wp_args)
in ((head), (_150_857)))
in FStar_Syntax_Syntax.Tm_app (_150_858))
in (mk _150_859)))
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

let _57_1058 = (let _150_871 = (FStar_List.map (fun _57_1052 -> (match (_57_1052) with
| (bv, q) -> begin
(

let h = bv.FStar_Syntax_Syntax.sort
in if (is_C h) then begin
(

let w' = (let _150_861 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-w\'") None _150_861))
in (let _150_867 = (let _150_866 = (FStar_Syntax_Syntax.mk_binder w')
in (let _150_865 = (let _150_864 = (let _150_863 = (let _150_862 = (FStar_Syntax_Syntax.bv_to_name bv)
in (trans_F_ env h _150_862))
in (FStar_Syntax_Syntax.null_binder _150_863))
in (_150_864)::[])
in (_150_866)::_150_865))
in ((w'), (_150_867))))
end else begin
(

let x = (let _150_868 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-x") None _150_868))
in (let _150_870 = (let _150_869 = (FStar_Syntax_Syntax.mk_binder x)
in (_150_869)::[])
in ((x), (_150_870))))
end)
end)) binders)
in (FStar_List.split _150_871))
in (match (_57_1058) with
| (bvs, binders) -> begin
(

let binders = (FStar_List.flatten binders)
in (

let app = (let _150_877 = (let _150_876 = (let _150_875 = (FStar_List.map (fun bv -> (let _150_874 = (FStar_Syntax_Syntax.bv_to_name bv)
in (let _150_873 = (FStar_Syntax_Syntax.as_implicit false)
in ((_150_874), (_150_873))))) bvs)
in ((wp), (_150_875)))
in FStar_Syntax_Syntax.Tm_app (_150_876))
in (mk _150_877))
in (

let comp = (let _150_879 = (type_of_comp comp)
in (let _150_878 = (is_monadic_comp comp)
in (trans_G env _150_879 _150_878 app)))
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
(let _150_890 = (let _150_889 = (star_type' env h)
in (let _150_888 = (let _150_887 = (let _150_886 = (FStar_Syntax_Syntax.as_implicit false)
in ((wp), (_150_886)))
in (_150_887)::[])
in {FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _150_889; FStar_Syntax_Syntax.effect_args = _150_888; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp _150_890))
end else begin
(let _150_891 = (trans_F_ env h wp)
in (FStar_Syntax_Syntax.mk_Total _150_891))
end))


let n : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.NoInline)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]))


let star_type : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _150_898 = (n env.env t)
in (star_type' env _150_898)))


let star_expr : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env t -> (let _150_903 = (n env.env t)
in (check_n env _150_903)))


let trans_F : env_  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> (let _150_911 = (n env.env c)
in (let _150_910 = (n env.env wp)
in (trans_F_ env _150_911 _150_910))))




