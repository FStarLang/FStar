
open Prims

let gen_wps_for_free : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.sigelts * FStar_Syntax_Syntax.eff_decl) = (fun env binders a wp_a ed -> (

let wp_a = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env wp_a)
in (

let a = (

let _57_13 = a
in (let _151_11 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env a.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_13.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_13.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _151_11}))
in (

let d = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))
in (

let _57_20 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _57_18 = (d "Elaborating extra WP combinators")
in (let _151_14 = (FStar_Syntax_Print.term_to_string wp_a)
in (FStar_Util.print1 "wp_a is: %s\n" _151_14)))
end else begin
()
end
in (

let rec collect_binders = (fun t -> (match ((let _151_17 = (FStar_Syntax_Subst.compress t)
in _151_17.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let rest = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _57_30) -> begin
t
end
| _57_34 -> begin
(FStar_All.failwith "wp_a contains non-Tot arrow")
end)
in (let _151_18 = (collect_binders rest)
in (FStar_List.append bs _151_18)))
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

let gamma = (let _151_21 = (collect_binders wp_a)
in (FStar_All.pipe_right _151_21 FStar_Syntax_Util.name_binders))
in (

let _57_44 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _151_23 = (let _151_22 = (FStar_Syntax_Print.binders_to_string ", " gamma)
in (FStar_Util.format1 "Gamma is %s\n" _151_22))
in (d _151_23))
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

let _57_57 = (let _151_33 = (let _151_32 = (FStar_ST.read sigelts)
in (sigelt)::_151_32)
in (FStar_ST.op_Colon_Equals sigelts _151_33))
in fv)
end)))
in (

let binders_of_list = (FStar_List.map (fun _57_61 -> (match (_57_61) with
| (t, b) -> begin
(let _151_36 = (FStar_Syntax_Syntax.as_implicit b)
in ((t), (_151_36)))
end)))
in (

let mk_all_implicit = (FStar_List.map (fun t -> (let _151_39 = (FStar_Syntax_Syntax.as_implicit true)
in (((Prims.fst t)), (_151_39)))))
in (

let args_of_binders = (FStar_List.map (fun bv -> (let _151_42 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst bv))
in (FStar_Syntax_Syntax.as_arg _151_42))))
in (

let _57_88 = (

let _57_73 = (

let mk = (fun f -> (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let body = (let _151_55 = (let _151_54 = (FStar_Syntax_Syntax.bv_to_name t)
in (f _151_54))
in (FStar_Syntax_Util.arrow gamma _151_55))
in (let _151_60 = (let _151_59 = (let _151_58 = (FStar_Syntax_Syntax.mk_binder a)
in (let _151_57 = (let _151_56 = (FStar_Syntax_Syntax.mk_binder t)
in (_151_56)::[])
in (_151_58)::_151_57))
in (FStar_List.append binders _151_59))
in (FStar_Syntax_Util.abs _151_60 body None)))))
in (let _151_62 = (mk FStar_Syntax_Syntax.mk_Total)
in (let _151_61 = (mk FStar_Syntax_Syntax.mk_GTotal)
in ((_151_62), (_151_61)))))
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

let mk_app = (fun fv t -> (let _151_84 = (let _151_83 = (let _151_82 = (let _151_81 = (FStar_List.map (fun _57_84 -> (match (_57_84) with
| (bv, _57_83) -> begin
(let _151_73 = (FStar_Syntax_Syntax.bv_to_name bv)
in (let _151_72 = (FStar_Syntax_Syntax.as_implicit false)
in ((_151_73), (_151_72))))
end)) binders)
in (let _151_80 = (let _151_79 = (let _151_75 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _151_74 = (FStar_Syntax_Syntax.as_implicit false)
in ((_151_75), (_151_74))))
in (let _151_78 = (let _151_77 = (let _151_76 = (FStar_Syntax_Syntax.as_implicit false)
in ((t), (_151_76)))
in (_151_77)::[])
in (_151_79)::_151_78))
in (FStar_List.append _151_81 _151_80)))
in ((fv), (_151_82)))
in FStar_Syntax_Syntax.Tm_app (_151_83))
in (mk _151_84)))
in ((env), ((mk_app ctx_fv)), ((mk_app gctx_fv))))))))
end))
in (match (_57_88) with
| (env, mk_ctx, mk_gctx) -> begin
(

let c_pure = (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let x = (let _151_89 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" None _151_89))
in (

let ret = (let _151_94 = (let _151_93 = (let _151_92 = (let _151_91 = (let _151_90 = (FStar_Syntax_Syntax.bv_to_name t)
in (mk_ctx _151_90))
in (FStar_Syntax_Syntax.mk_Total _151_91))
in (FStar_Syntax_Util.lcomp_of_comp _151_92))
in FStar_Util.Inl (_151_93))
in Some (_151_94))
in (

let body = (let _151_95 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs gamma _151_95 ret))
in (let _151_98 = (let _151_97 = (mk_all_implicit binders)
in (let _151_96 = (binders_of_list ((((a), (true)))::(((t), (true)))::(((x), (false)))::[]))
in (FStar_List.append _151_97 _151_96)))
in (FStar_Syntax_Util.abs _151_98 body ret))))))
in (

let c_pure = (let _151_99 = (mk_lid "pure")
in (register env _151_99 c_pure))
in (

let c_app = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let l = (let _151_107 = (let _151_106 = (let _151_105 = (let _151_102 = (let _151_101 = (let _151_100 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv None _151_100))
in (FStar_Syntax_Syntax.mk_binder _151_101))
in (_151_102)::[])
in (let _151_104 = (let _151_103 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _151_103))
in (FStar_Syntax_Util.arrow _151_105 _151_104)))
in (mk_gctx _151_106))
in (FStar_Syntax_Syntax.gen_bv "l" None _151_107))
in (

let r = (let _151_109 = (let _151_108 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _151_108))
in (FStar_Syntax_Syntax.gen_bv "r" None _151_109))
in (

let ret = (let _151_114 = (let _151_113 = (let _151_112 = (let _151_111 = (let _151_110 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _151_110))
in (FStar_Syntax_Syntax.mk_Total _151_111))
in (FStar_Syntax_Util.lcomp_of_comp _151_112))
in FStar_Util.Inl (_151_113))
in Some (_151_114))
in (

let outer_body = (

let gamma_as_args = (args_of_binders gamma)
in (

let inner_body = (let _151_120 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _151_119 = (let _151_118 = (let _151_117 = (let _151_116 = (let _151_115 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app _151_115 gamma_as_args))
in (FStar_Syntax_Syntax.as_arg _151_116))
in (_151_117)::[])
in (FStar_List.append gamma_as_args _151_118))
in (FStar_Syntax_Util.mk_app _151_120 _151_119)))
in (FStar_Syntax_Util.abs gamma inner_body ret)))
in (let _151_123 = (let _151_122 = (mk_all_implicit binders)
in (let _151_121 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((l), (false)))::(((r), (false)))::[]))
in (FStar_List.append _151_122 _151_121)))
in (FStar_Syntax_Util.abs _151_123 outer_body ret))))))))
in (

let c_app = (let _151_124 = (mk_lid "app")
in (register env _151_124 c_app))
in (

let c_lift1 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _151_129 = (let _151_126 = (let _151_125 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _151_125))
in (_151_126)::[])
in (let _151_128 = (let _151_127 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _151_127))
in (FStar_Syntax_Util.arrow _151_129 _151_128)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _151_131 = (let _151_130 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _151_130))
in (FStar_Syntax_Syntax.gen_bv "a1" None _151_131))
in (

let ret = (let _151_136 = (let _151_135 = (let _151_134 = (let _151_133 = (let _151_132 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _151_132))
in (FStar_Syntax_Syntax.mk_Total _151_133))
in (FStar_Syntax_Util.lcomp_of_comp _151_134))
in FStar_Util.Inl (_151_135))
in Some (_151_136))
in (let _151_148 = (let _151_138 = (mk_all_implicit binders)
in (let _151_137 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::(((a1), (false)))::[]))
in (FStar_List.append _151_138 _151_137)))
in (let _151_147 = (let _151_146 = (let _151_145 = (let _151_144 = (let _151_141 = (let _151_140 = (let _151_139 = (FStar_Syntax_Syntax.bv_to_name f)
in (_151_139)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _151_140))
in (FStar_Syntax_Util.mk_app c_pure _151_141))
in (let _151_143 = (let _151_142 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_151_142)::[])
in (_151_144)::_151_143))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _151_145))
in (FStar_Syntax_Util.mk_app c_app _151_146))
in (FStar_Syntax_Util.abs _151_148 _151_147 ret)))))))))
in (

let c_lift1 = (let _151_149 = (mk_lid "lift1")
in (register env _151_149 c_lift1))
in (

let c_lift2 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t3 = (FStar_Syntax_Syntax.gen_bv "t3" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _151_157 = (let _151_154 = (let _151_150 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _151_150))
in (let _151_153 = (let _151_152 = (let _151_151 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.null_binder _151_151))
in (_151_152)::[])
in (_151_154)::_151_153))
in (let _151_156 = (let _151_155 = (FStar_Syntax_Syntax.bv_to_name t3)
in (FStar_Syntax_Syntax.mk_GTotal _151_155))
in (FStar_Syntax_Util.arrow _151_157 _151_156)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _151_159 = (let _151_158 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _151_158))
in (FStar_Syntax_Syntax.gen_bv "a1" None _151_159))
in (

let a2 = (let _151_161 = (let _151_160 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _151_160))
in (FStar_Syntax_Syntax.gen_bv "a2" None _151_161))
in (

let ret = (let _151_166 = (let _151_165 = (let _151_164 = (let _151_163 = (let _151_162 = (FStar_Syntax_Syntax.bv_to_name t3)
in (mk_gctx _151_162))
in (FStar_Syntax_Syntax.mk_Total _151_163))
in (FStar_Syntax_Util.lcomp_of_comp _151_164))
in FStar_Util.Inl (_151_165))
in Some (_151_166))
in (let _151_183 = (let _151_168 = (mk_all_implicit binders)
in (let _151_167 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((t3), (true)))::(((f), (false)))::(((a1), (false)))::(((a2), (false)))::[]))
in (FStar_List.append _151_168 _151_167)))
in (let _151_182 = (let _151_181 = (let _151_180 = (let _151_179 = (let _151_176 = (let _151_175 = (let _151_174 = (let _151_171 = (let _151_170 = (let _151_169 = (FStar_Syntax_Syntax.bv_to_name f)
in (_151_169)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _151_170))
in (FStar_Syntax_Util.mk_app c_pure _151_171))
in (let _151_173 = (let _151_172 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_151_172)::[])
in (_151_174)::_151_173))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _151_175))
in (FStar_Syntax_Util.mk_app c_app _151_176))
in (let _151_178 = (let _151_177 = (FStar_Syntax_Syntax.bv_to_name a2)
in (_151_177)::[])
in (_151_179)::_151_178))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _151_180))
in (FStar_Syntax_Util.mk_app c_app _151_181))
in (FStar_Syntax_Util.abs _151_183 _151_182 ret)))))))))))
in (

let c_lift2 = (let _151_184 = (mk_lid "lift2")
in (register env _151_184 c_lift2))
in (

let c_push = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _151_190 = (let _151_186 = (let _151_185 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _151_185))
in (_151_186)::[])
in (let _151_189 = (let _151_188 = (let _151_187 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _151_187))
in (FStar_Syntax_Syntax.mk_Total _151_188))
in (FStar_Syntax_Util.arrow _151_190 _151_189)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let ret = (let _151_200 = (let _151_199 = (let _151_198 = (let _151_197 = (let _151_196 = (let _151_195 = (let _151_192 = (let _151_191 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _151_191))
in (_151_192)::[])
in (let _151_194 = (let _151_193 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _151_193))
in (FStar_Syntax_Util.arrow _151_195 _151_194)))
in (mk_ctx _151_196))
in (FStar_Syntax_Syntax.mk_Total _151_197))
in (FStar_Syntax_Util.lcomp_of_comp _151_198))
in FStar_Util.Inl (_151_199))
in Some (_151_200))
in (

let e1 = (let _151_201 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" None _151_201))
in (

let body = (let _151_210 = (let _151_203 = (let _151_202 = (FStar_Syntax_Syntax.mk_binder e1)
in (_151_202)::[])
in (FStar_List.append gamma _151_203))
in (let _151_209 = (let _151_208 = (FStar_Syntax_Syntax.bv_to_name f)
in (let _151_207 = (let _151_206 = (let _151_204 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg _151_204))
in (let _151_205 = (args_of_binders gamma)
in (_151_206)::_151_205))
in (FStar_Syntax_Util.mk_app _151_208 _151_207)))
in (FStar_Syntax_Util.abs _151_210 _151_209 ret)))
in (let _151_213 = (let _151_212 = (mk_all_implicit binders)
in (let _151_211 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::[]))
in (FStar_List.append _151_212 _151_211)))
in (FStar_Syntax_Util.abs _151_213 body ret)))))))))
in (

let c_push = (let _151_214 = (mk_lid "push")
in (register env _151_214 c_push))
in (

let ret_tot_wp_a = (let _151_217 = (let _151_216 = (let _151_215 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.lcomp_of_comp _151_215))
in FStar_Util.Inl (_151_216))
in Some (_151_217))
in (

let mk_generic_app = (fun c -> if ((FStar_List.length binders) > (Prims.parse_int "0")) then begin
(let _151_222 = (let _151_221 = (let _151_220 = (args_of_binders binders)
in ((c), (_151_220)))
in FStar_Syntax_Syntax.Tm_app (_151_221))
in (mk _151_222))
end else begin
c
end)
in (

let wp_if_then_else = (

let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (let _151_240 = (let _151_223 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (FStar_List.append binders _151_223))
in (let _151_239 = (

let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_unfoldable ((Prims.parse_int "2"))) None)
in (let _151_238 = (let _151_229 = (let _151_228 = (let _151_227 = (let _151_226 = (let _151_225 = (let _151_224 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg _151_224))
in (_151_225)::[])
in (FStar_Syntax_Util.mk_app l_ite _151_226))
in (_151_227)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _151_228))
in (FStar_Syntax_Util.mk_app c_lift2 _151_229))
in (let _151_237 = (let _151_236 = (let _151_235 = (let _151_234 = (let _151_232 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _151_231 = (let _151_230 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_151_230)::[])
in (_151_232)::_151_231))
in (let _151_233 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_234 _151_233)))
in (FStar_Syntax_Syntax.mk_Total _151_235))
in FStar_Util.Inr (_151_236))
in (FStar_Syntax_Util.ascribe _151_238 _151_237))))
in (FStar_Syntax_Util.abs _151_240 _151_239 ret_tot_wp_a))))
in (

let wp_if_then_else = (let _151_241 = (mk_lid "wp_if_then_else")
in (register env _151_241 wp_if_then_else))
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

let body = (let _151_252 = (let _151_251 = (let _151_250 = (let _151_247 = (let _151_246 = (let _151_245 = (let _151_244 = (let _151_243 = (let _151_242 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _151_242))
in (_151_243)::[])
in (FStar_Syntax_Util.mk_app l_and _151_244))
in (_151_245)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _151_246))
in (FStar_Syntax_Util.mk_app c_pure _151_247))
in (let _151_249 = (let _151_248 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_151_248)::[])
in (_151_250)::_151_249))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _151_251))
in (FStar_Syntax_Util.mk_app c_app _151_252))
in (let _151_254 = (let _151_253 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders _151_253))
in (FStar_Syntax_Util.abs _151_254 body ret_tot_wp_a))))))
in (

let wp_assert = (let _151_255 = (mk_lid "wp_assert")
in (register env _151_255 wp_assert))
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

let body = (let _151_266 = (let _151_265 = (let _151_264 = (let _151_261 = (let _151_260 = (let _151_259 = (let _151_258 = (let _151_257 = (let _151_256 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _151_256))
in (_151_257)::[])
in (FStar_Syntax_Util.mk_app l_imp _151_258))
in (_151_259)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _151_260))
in (FStar_Syntax_Util.mk_app c_pure _151_261))
in (let _151_263 = (let _151_262 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_151_262)::[])
in (_151_264)::_151_263))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _151_265))
in (FStar_Syntax_Util.mk_app c_app _151_266))
in (let _151_268 = (let _151_267 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders _151_267))
in (FStar_Syntax_Util.abs _151_268 body ret_tot_wp_a))))))
in (

let wp_assume = (let _151_269 = (mk_lid "wp_assume")
in (register env _151_269 wp_assume))
in (

let wp_assume = (mk_generic_app wp_assume)
in (

let wp_close = (

let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _151_273 = (let _151_271 = (let _151_270 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _151_270))
in (_151_271)::[])
in (let _151_272 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _151_273 _151_272)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let body = (let _151_282 = (let _151_281 = (let _151_280 = (let _151_274 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((FStar_Syntax_Util.tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure _151_274))
in (let _151_279 = (let _151_278 = (let _151_277 = (let _151_276 = (let _151_275 = (FStar_Syntax_Syntax.bv_to_name f)
in (_151_275)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _151_276))
in (FStar_Syntax_Util.mk_app c_push _151_277))
in (_151_278)::[])
in (_151_280)::_151_279))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _151_281))
in (FStar_Syntax_Util.mk_app c_app _151_282))
in (let _151_284 = (let _151_283 = (FStar_Syntax_Syntax.binders_of_list ((a)::(b)::(f)::[]))
in (FStar_List.append binders _151_283))
in (FStar_Syntax_Util.abs _151_284 body ret_tot_wp_a))))))
in (

let wp_close = (let _151_285 = (mk_lid "wp_close")
in (register env _151_285 wp_close))
in (

let wp_close = (mk_generic_app wp_close)
in (

let ret_tot_type = (let _151_288 = (let _151_287 = (let _151_286 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _151_286))
in FStar_Util.Inl (_151_287))
in Some (_151_288))
in (

let ret_gtot_type = (let _151_291 = (let _151_290 = (let _151_289 = (FStar_Syntax_Syntax.mk_GTotal FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _151_289))
in FStar_Util.Inl (_151_290))
in Some (_151_291))
in (

let mk_forall = (fun x body -> (let _151_302 = (let _151_301 = (let _151_300 = (let _151_299 = (let _151_298 = (let _151_297 = (let _151_296 = (FStar_Syntax_Syntax.mk_binder x)
in (_151_296)::[])
in (FStar_Syntax_Util.abs _151_297 body ret_tot_type))
in (FStar_Syntax_Syntax.as_arg _151_298))
in (_151_299)::[])
in ((FStar_Syntax_Util.tforall), (_151_300)))
in FStar_Syntax_Syntax.Tm_app (_151_301))
in (FStar_Syntax_Syntax.mk _151_302 None FStar_Range.dummyRange)))
in (

let is_zero_order = (fun t -> (match ((let _151_305 = (FStar_Syntax_Subst.compress t)
in _151_305.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
false
end
| _57_175 -> begin
true
end))
in (

let rec mk_rel = (fun rel t x y -> (

let mk_rel = (mk_rel rel)
in (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (match ((let _151_327 = (FStar_Syntax_Subst.compress t)
in _151_327.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_184) -> begin
(rel x y)
end
| (FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(

let a = (Prims.fst binder).FStar_Syntax_Syntax.sort
in if (is_zero_order a) then begin
(

let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (

let body = (let _151_335 = (let _151_330 = (let _151_329 = (let _151_328 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _151_328))
in (_151_329)::[])
in (FStar_Syntax_Util.mk_app x _151_330))
in (let _151_334 = (let _151_333 = (let _151_332 = (let _151_331 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _151_331))
in (_151_332)::[])
in (FStar_Syntax_Util.mk_app y _151_333))
in (mk_rel b _151_335 _151_334)))
in (mk_forall a1 body)))
end else begin
(

let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (

let a2 = (FStar_Syntax_Syntax.gen_bv "a2" None a)
in (

let body = (let _151_347 = (let _151_337 = (FStar_Syntax_Syntax.bv_to_name a1)
in (let _151_336 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_rel a _151_337 _151_336)))
in (let _151_346 = (let _151_345 = (let _151_340 = (let _151_339 = (let _151_338 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _151_338))
in (_151_339)::[])
in (FStar_Syntax_Util.mk_app x _151_340))
in (let _151_344 = (let _151_343 = (let _151_342 = (let _151_341 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg _151_341))
in (_151_342)::[])
in (FStar_Syntax_Util.mk_app y _151_343))
in (mk_rel b _151_345 _151_344)))
in (FStar_Syntax_Util.mk_imp _151_347 _151_346)))
in (let _151_348 = (mk_forall a2 body)
in (mk_forall a1 _151_348)))))
end)
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::binders, comp) -> begin
(

let t = (

let _57_228 = t
in (let _151_352 = (let _151_351 = (let _151_350 = (let _151_349 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _151_349))
in (((binder)::[]), (_151_350)))
in FStar_Syntax_Syntax.Tm_arrow (_151_351))
in {FStar_Syntax_Syntax.n = _151_352; FStar_Syntax_Syntax.tk = _57_228.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_228.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_228.FStar_Syntax_Syntax.vars}))
in (mk_rel t x y))
end
| FStar_Syntax_Syntax.Tm_arrow (_57_232) -> begin
(FStar_All.failwith "unhandled arrow")
end
| _57_235 -> begin
(FStar_Syntax_Util.mk_eq t t x y)
end))))
in (

let stronger = (

let wp1 = (FStar_Syntax_Syntax.gen_bv "wp1" None wp_a)
in (

let wp2 = (FStar_Syntax_Syntax.gen_bv "wp2" None wp_a)
in (

let body = (let _151_354 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (let _151_353 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_rel FStar_Syntax_Util.mk_imp wp_a _151_354 _151_353)))
in (let _151_356 = (let _151_355 = (binders_of_list ((((a), (false)))::(((wp1), (false)))::(((wp2), (false)))::[]))
in (FStar_List.append binders _151_355))
in (FStar_Syntax_Util.abs _151_356 body ret_tot_type)))))
in (

let stronger = (let _151_357 = (mk_lid "stronger")
in (register env _151_357 stronger))
in (

let stronger = (mk_generic_app stronger)
in (

let wp_ite = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let _57_245 = (FStar_Util.prefix gamma)
in (match (_57_245) with
| (wp_args, post) -> begin
(

let k = (FStar_Syntax_Syntax.gen_bv "k" None (Prims.fst post).FStar_Syntax_Syntax.sort)
in (

let equiv = (

let k_tm = (FStar_Syntax_Syntax.bv_to_name k)
in (

let eq = (let _151_358 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst post))
in (mk_rel FStar_Syntax_Util.mk_iff k.FStar_Syntax_Syntax.sort k_tm _151_358))
in (match ((FStar_Syntax_Util.destruct_typ_as_formula eq)) with
| Some (FStar_Syntax_Util.QAll (binders, [], body)) -> begin
(

let k_app = (let _151_359 = (args_of_binders binders)
in (FStar_Syntax_Util.mk_app k_tm _151_359))
in (

let guard_free = (let _151_360 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.guard_free FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _151_360))
in (

let pat = (let _151_362 = (let _151_361 = (FStar_Syntax_Syntax.as_arg k_app)
in (_151_361)::[])
in (FStar_Syntax_Util.mk_app guard_free _151_362))
in (

let pattern_guarded_body = (let _151_368 = (let _151_367 = (let _151_366 = (let _151_365 = (let _151_364 = (let _151_363 = (FStar_Syntax_Syntax.as_arg pat)
in (_151_363)::[])
in (_151_364)::[])
in FStar_Syntax_Syntax.Meta_pattern (_151_365))
in ((body), (_151_366)))
in FStar_Syntax_Syntax.Tm_meta (_151_367))
in (mk _151_368))
in (FStar_Syntax_Util.close_forall binders pattern_guarded_body)))))
end
| _57_260 -> begin
(FStar_All.failwith "Impossible: Expected the equivalence to be a quantified formula")
end)))
in (

let body = (let _151_377 = (let _151_376 = (let _151_375 = (let _151_374 = (FStar_Syntax_Syntax.bv_to_name wp)
in (let _151_373 = (let _151_372 = (args_of_binders wp_args)
in (let _151_371 = (let _151_370 = (let _151_369 = (FStar_Syntax_Syntax.bv_to_name k)
in (FStar_Syntax_Syntax.as_arg _151_369))
in (_151_370)::[])
in (FStar_List.append _151_372 _151_371)))
in (FStar_Syntax_Util.mk_app _151_374 _151_373)))
in (FStar_Syntax_Util.mk_imp equiv _151_375))
in (FStar_Syntax_Util.mk_forall k _151_376))
in (FStar_Syntax_Util.abs gamma _151_377 ret_gtot_type))
in (let _151_379 = (let _151_378 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders _151_378))
in (FStar_Syntax_Util.abs _151_379 body ret_gtot_type)))))
end)))
in (

let wp_ite = (let _151_380 = (mk_lid "wp_ite")
in (register env _151_380 wp_ite))
in (

let wp_ite = (mk_generic_app wp_ite)
in (

let null_wp = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let _57_269 = (FStar_Util.prefix gamma)
in (match (_57_269) with
| (wp_args, post) -> begin
(

let x = (FStar_Syntax_Syntax.gen_bv "x" None FStar_Syntax_Syntax.tun)
in (

let body = (let _151_385 = (let _151_384 = (FStar_All.pipe_left FStar_Syntax_Syntax.bv_to_name (Prims.fst post))
in (let _151_383 = (let _151_382 = (let _151_381 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _151_381))
in (_151_382)::[])
in (FStar_Syntax_Util.mk_app _151_384 _151_383)))
in (FStar_Syntax_Util.mk_forall x _151_385))
in (let _151_388 = (let _151_387 = (let _151_386 = (FStar_Syntax_Syntax.binders_of_list ((a)::[]))
in (FStar_List.append _151_386 gamma))
in (FStar_List.append binders _151_387))
in (FStar_Syntax_Util.abs _151_388 body ret_gtot_type))))
end)))
in (

let null_wp = (let _151_389 = (mk_lid "null_wp")
in (register env _151_389 null_wp))
in (

let null_wp = (mk_generic_app null_wp)
in (

let wp_trivial = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let body = (let _151_399 = (let _151_398 = (let _151_397 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _151_396 = (let _151_395 = (let _151_392 = (let _151_391 = (let _151_390 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg _151_390))
in (_151_391)::[])
in (FStar_Syntax_Util.mk_app null_wp _151_392))
in (let _151_394 = (let _151_393 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_151_393)::[])
in (_151_395)::_151_394))
in (_151_397)::_151_396))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _151_398))
in (FStar_Syntax_Util.mk_app stronger _151_399))
in (let _151_401 = (let _151_400 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders _151_400))
in (FStar_Syntax_Util.abs _151_401 body ret_tot_type))))
in (

let wp_trivial = (let _151_402 = (mk_lid "wp_trivial")
in (register env _151_402 wp_trivial))
in (

let wp_trivial = (mk_generic_app wp_trivial)
in (

let _57_280 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(d "End Dijkstra monads for free")
end else begin
()
end
in (

let c = (FStar_Syntax_Subst.close binders)
in (let _151_422 = (let _151_404 = (FStar_ST.read sigelts)
in (FStar_List.rev _151_404))
in (let _151_421 = (

let _57_283 = ed
in (let _151_420 = (let _151_405 = (c wp_if_then_else)
in (([]), (_151_405)))
in (let _151_419 = (let _151_406 = (c wp_ite)
in (([]), (_151_406)))
in (let _151_418 = (let _151_407 = (c stronger)
in (([]), (_151_407)))
in (let _151_417 = (let _151_408 = (c wp_close)
in (([]), (_151_408)))
in (let _151_416 = (let _151_409 = (c wp_assert)
in (([]), (_151_409)))
in (let _151_415 = (let _151_410 = (c wp_assume)
in (([]), (_151_410)))
in (let _151_414 = (let _151_411 = (c null_wp)
in (([]), (_151_411)))
in (let _151_413 = (let _151_412 = (c wp_trivial)
in (([]), (_151_412)))
in {FStar_Syntax_Syntax.qualifiers = _57_283.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_283.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_283.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_283.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_283.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _57_283.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _57_283.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _151_420; FStar_Syntax_Syntax.ite_wp = _151_419; FStar_Syntax_Syntax.stronger = _151_418; FStar_Syntax_Syntax.close_wp = _151_417; FStar_Syntax_Syntax.assert_p = _151_416; FStar_Syntax_Syntax.assume_p = _151_415; FStar_Syntax_Syntax.null_wp = _151_414; FStar_Syntax_Syntax.trivial = _151_413; FStar_Syntax_Syntax.repr = _57_283.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _57_283.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _57_283.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _57_283.FStar_Syntax_Syntax.actions})))))))))
in ((_151_422), (_151_421)))))))))))))))))))))))))))))))))))))))))))))))
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
| N (_57_293) -> begin
_57_293
end))


let ___M____0 = (fun projectee -> (match (projectee) with
| M (_57_296) -> begin
_57_296
end))


type nm_ =
nm


let nm_of_comp : FStar_Syntax_Syntax.comp'  ->  nm = (fun _57_1 -> (match (_57_1) with
| FStar_Syntax_Syntax.Total (t, _57_300) -> begin
N (t)
end
| FStar_Syntax_Syntax.Comp (c) when (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.monadic_lid) -> begin
M (c.FStar_Syntax_Syntax.result_typ)
end
| _57_306 -> begin
(FStar_All.failwith "[nm_of_comp]: impossible")
end))


let string_of_nm : nm  ->  Prims.string = (fun _57_2 -> (match (_57_2) with
| N (t) -> begin
(let _151_480 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "N[%s]" _151_480))
end
| M (t) -> begin
(let _151_481 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "M[%s]" _151_481))
end))


let is_monadic_arrow : FStar_Syntax_Syntax.term'  ->  nm = (fun n -> (match (n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_314, {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_320; FStar_Syntax_Syntax.pos = _57_318; FStar_Syntax_Syntax.vars = _57_316}) -> begin
(nm_of_comp n)
end
| _57_326 -> begin
(FStar_All.failwith "unexpected_argument: [is_monadic_arrow]")
end))


let is_monadic_comp = (fun c -> (match ((nm_of_comp c.FStar_Syntax_Syntax.n)) with
| M (_57_329) -> begin
true
end
| N (_57_332) -> begin
false
end))


let rec mk_star_to_type : (FStar_Syntax_Syntax.term'  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun mk env a -> (let _151_505 = (let _151_504 = (let _151_503 = (let _151_501 = (let _151_500 = (let _151_498 = (star_type' env a)
in (FStar_Syntax_Syntax.null_bv _151_498))
in (let _151_499 = (FStar_Syntax_Syntax.as_implicit false)
in ((_151_500), (_151_499))))
in (_151_501)::[])
in (let _151_502 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_151_503), (_151_502))))
in FStar_Syntax_Syntax.Tm_arrow (_151_504))
in (mk _151_505)))
and star_type' : env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None t.FStar_Syntax_Syntax.pos))
in (

let mk_star_to_type = (mk_star_to_type mk)
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _57_345) -> begin
(

let binders = (FStar_List.map (fun _57_350 -> (match (_57_350) with
| (bv, aqual) -> begin
(let _151_514 = (

let _57_351 = bv
in (let _151_513 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_351.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_351.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _151_513}))
in ((_151_514), (aqual)))
end)) binders)
in (match ((is_monadic_arrow t.FStar_Syntax_Syntax.n)) with
| N (hn) -> begin
(let _151_518 = (let _151_517 = (let _151_516 = (let _151_515 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_Total _151_515))
in ((binders), (_151_516)))
in FStar_Syntax_Syntax.Tm_arrow (_151_517))
in (mk _151_518))
end
| M (a) -> begin
(let _151_527 = (let _151_526 = (let _151_525 = (let _151_523 = (let _151_522 = (let _151_521 = (let _151_519 = (mk_star_to_type env a)
in (FStar_Syntax_Syntax.null_bv _151_519))
in (let _151_520 = (FStar_Syntax_Syntax.as_implicit false)
in ((_151_521), (_151_520))))
in (_151_522)::[])
in (FStar_List.append binders _151_523))
in (let _151_524 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_151_525), (_151_524))))
in FStar_Syntax_Syntax.Tm_arrow (_151_526))
in (mk _151_527))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let is_valid_application = (fun head -> (match ((let _151_530 = (FStar_Syntax_Subst.compress head)
in _151_530.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.option_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.either_lid)) || (let _151_531 = (FStar_Syntax_Subst.compress head)
in (FStar_Syntax_Util.is_tuple_constructor _151_531))) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uinst (_57_367) -> begin
(FStar_All.failwith "impossible (Tm_uinst)")
end
| _57_370 -> begin
false
end))
in if (is_valid_application head) then begin
(let _151_536 = (let _151_535 = (let _151_534 = (FStar_List.map (fun _57_373 -> (match (_57_373) with
| (t, qual) -> begin
(let _151_533 = (star_type' env t)
in ((_151_533), (qual)))
end)) args)
in ((head), (_151_534)))
in FStar_Syntax_Syntax.Tm_app (_151_535))
in (mk _151_536))
end else begin
(let _151_539 = (let _151_538 = (let _151_537 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "For now, only [either] and [option] are supported in the definition language (got: %s)" _151_537))
in FStar_Syntax_Syntax.Err (_151_538))
in (Prims.raise _151_539))
end)
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_abs (binders, repr, something) -> begin
(

let _57_393 = (FStar_Syntax_Subst.open_term binders repr)
in (match (_57_393) with
| (binders, repr) -> begin
(

let env = (

let _57_394 = env
in (let _151_540 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _151_540; subst = _57_394.subst; tc_const = _57_394.tc_const}))
in (

let repr = (star_type' env repr)
in (FStar_Syntax_Util.abs binders repr something)))
end))
end
| (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_match (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _151_543 = (let _151_542 = (let _151_541 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "The following term is outside of the definition language: %s" _151_541))
in FStar_Syntax_Syntax.Err (_151_542))
in (Prims.raise _151_543))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_427) -> begin
(FStar_All.failwith "impossible")
end)))))


let is_monadic : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  Prims.bool = (fun _57_3 -> (match (_57_3) with
| None -> begin
(FStar_All.failwith "un-annotated lambda?!")
end
| (Some (FStar_Util.Inl ({FStar_Syntax_Syntax.eff_name = lid; FStar_Syntax_Syntax.res_typ = _; FStar_Syntax_Syntax.cflags = _; FStar_Syntax_Syntax.comp = _}))) | (Some (FStar_Util.Inr (lid))) -> begin
(FStar_Ident.lid_equals lid FStar_Syntax_Const.monadic_lid)
end))


let rec is_C : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match ((let _151_551 = (FStar_Syntax_Subst.compress t)
in _151_551.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) when (FStar_Syntax_Util.is_tuple_constructor head) -> begin
(

let r = (let _151_553 = (let _151_552 = (FStar_List.hd args)
in (Prims.fst _151_552))
in (is_C _151_553))
in if r then begin
(

let _57_453 = if (not ((FStar_List.for_all (fun _57_452 -> (match (_57_452) with
| (h, _57_451) -> begin
(is_C h)
end)) args))) then begin
(FStar_All.failwith "not a C (A * C)")
end else begin
()
end
in true)
end else begin
(

let _57_459 = if (not ((FStar_List.for_all (fun _57_458 -> (match (_57_458) with
| (h, _57_457) -> begin
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

let _57_467 = if (is_C t) then begin
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
| _57_487 -> begin
false
end))


let mk_return : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let p_type = (mk_star_to_type mk env t)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'" None p_type)
in (

let body = (let _151_569 = (let _151_568 = (let _151_567 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _151_566 = (let _151_565 = (let _151_564 = (FStar_Syntax_Syntax.as_implicit false)
in ((e), (_151_564)))
in (_151_565)::[])
in ((_151_567), (_151_566))))
in FStar_Syntax_Syntax.Tm_app (_151_568))
in (mk _151_569))
in (let _151_571 = (let _151_570 = (FStar_Syntax_Syntax.mk_binder p)
in (_151_570)::[])
in (FStar_Syntax_Util.abs _151_571 body None)))))))


let is_unknown : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun _57_4 -> (match (_57_4) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| _57_499 -> begin
false
end))


let rec check : env  ->  FStar_Syntax_Syntax.term  ->  nm  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e context_nm -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let return_if = (fun _57_509 -> (match (_57_509) with
| (rec_nm, s_e, u_e) -> begin
(

let check = (fun t1 t2 -> if ((not ((is_unknown t2.FStar_Syntax_Syntax.n))) && (not ((let _151_625 = (FStar_TypeChecker_Rel.teq env.env t1 t2)
in (FStar_TypeChecker_Rel.is_trivial _151_625))))) then begin
(let _151_630 = (let _151_629 = (let _151_628 = (FStar_Syntax_Print.term_to_string e)
in (let _151_627 = (FStar_Syntax_Print.term_to_string t1)
in (let _151_626 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check]: the expression [%s] has type [%s] but should have type [%s]" _151_628 _151_627 _151_626))))
in FStar_Syntax_Syntax.Err (_151_629))
in (Prims.raise _151_630))
end else begin
()
end)
in (match (((rec_nm), (context_nm))) with
| ((N (t1), N (t2))) | ((M (t1), M (t2))) -> begin
(

let _57_521 = (check t1 t2)
in ((rec_nm), (s_e), (u_e)))
end
| (N (t1), M (t2)) -> begin
(

let _57_528 = (check t1 t2)
in (let _151_631 = (mk_return env t1 s_e)
in ((M (t1)), (_151_631), (u_e))))
end
| (M (t1), N (t2)) -> begin
(let _151_636 = (let _151_635 = (let _151_634 = (FStar_Syntax_Print.term_to_string e)
in (let _151_633 = (FStar_Syntax_Print.term_to_string t1)
in (let _151_632 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]" _151_634 _151_633 _151_632))))
in FStar_Syntax_Syntax.Err (_151_635))
in (Prims.raise _151_636))
end))
end))
in (

let ensure_m = (fun env e2 -> (

let strip_m = (fun _57_5 -> (match (_57_5) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_545 -> begin
(FStar_All.failwith "impossible")
end))
in (match (context_nm) with
| N (t) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren\'t"), (e2.FStar_Syntax_Syntax.pos)))))
end
| M (_57_550) -> begin
(let _151_643 = (check env e2 context_nm)
in (strip_m _151_643))
end)))
in (match ((let _151_644 = (FStar_Syntax_Subst.compress e)
in _151_644.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
(let _151_645 = (infer env e)
in (return_if _151_645))
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
| FStar_Syntax_Syntax.Tm_let (_57_601) -> begin
(let _151_653 = (let _151_652 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_let %s" _151_652))
in (FStar_All.failwith _151_653))
end
| FStar_Syntax_Syntax.Tm_type (_57_604) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_607) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_57_610) -> begin
(let _151_655 = (let _151_654 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_refine %s" _151_654))
in (FStar_All.failwith _151_655))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_613) -> begin
(let _151_657 = (let _151_656 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_uvar %s" _151_656))
in (FStar_All.failwith _151_657))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_616) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _151_662 = (let _151_661 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_unknown %s" _151_661))
in (FStar_All.failwith _151_662))
end)))))
and infer : env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.env)
in (match ((let _151_668 = (FStar_Syntax_Subst.compress e)
in _151_668.FStar_Syntax_Syntax.n)) with
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

let _57_636 = env
in (let _151_669 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _151_669; subst = _57_636.subst; tc_const = _57_636.tc_const}))
in (

let s_binders = (FStar_List.map (fun _57_641 -> (match (_57_641) with
| (bv, qual) -> begin
(

let sort = (star_type' env bv.FStar_Syntax_Syntax.sort)
in (((

let _57_643 = bv
in {FStar_Syntax_Syntax.ppname = _57_643.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_643.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (qual)))
end)) binders)
in (

let _57_665 = (FStar_List.fold_left (fun _57_648 _57_651 -> (match (((_57_648), (_57_651))) with
| ((env, acc), (bv, qual)) -> begin
(

let c = bv.FStar_Syntax_Syntax.sort
in if (is_C c) then begin
(

let xw = (let _151_673 = (star_type' env c)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "^w") None _151_673))
in (

let x = (

let _57_654 = bv
in (let _151_675 = (let _151_674 = (FStar_Syntax_Syntax.bv_to_name xw)
in (trans_F_ env c _151_674))
in {FStar_Syntax_Syntax.ppname = _57_654.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_654.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _151_675}))
in (

let env = (

let _57_657 = env
in (let _151_679 = (let _151_678 = (let _151_677 = (let _151_676 = (FStar_Syntax_Syntax.bv_to_name xw)
in ((bv), (_151_676)))
in FStar_Syntax_Syntax.NT (_151_677))
in (_151_678)::env.subst)
in {env = _57_657.env; subst = _151_679; tc_const = _57_657.tc_const}))
in (let _151_683 = (let _151_682 = (FStar_Syntax_Syntax.mk_binder x)
in (let _151_681 = (let _151_680 = (FStar_Syntax_Syntax.mk_binder xw)
in (_151_680)::acc)
in (_151_682)::_151_681))
in ((env), (_151_683))))))
end else begin
(

let x = (

let _57_660 = bv
in (let _151_684 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_660.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_660.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _151_684}))
in (let _151_686 = (let _151_685 = (FStar_Syntax_Syntax.mk_binder x)
in (_151_685)::acc)
in ((env), (_151_686))))
end)
end)) ((env), ([])) binders)
in (match (_57_665) with
| (env, u_binders) -> begin
(

let u_binders = (FStar_List.rev u_binders)
in (

let _57_675 = (

let check_what = if (is_monadic what) then begin
check_m
end else begin
check_n
end
in (

let _57_671 = (check_what env body)
in (match (_57_671) with
| (t, s_body, u_body) -> begin
(let _151_692 = (let _151_691 = if (is_monadic what) then begin
M (t)
end else begin
N (t)
end
in (comp_of_nm _151_691))
in ((_151_692), (s_body), (u_body)))
end)))
in (match (_57_675) with
| (comp, s_body, u_body) -> begin
(

let t = (

let binders = (FStar_List.map (fun _57_679 -> (match (_57_679) with
| (bv, _57_678) -> begin
(let _151_694 = (FStar_Syntax_Syntax.null_bv bv.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_binder _151_694))
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
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = {FStar_Syntax_Syntax.v = lid; FStar_Syntax_Syntax.ty = _57_696; FStar_Syntax_Syntax.p = _57_694}; FStar_Syntax_Syntax.fv_delta = _57_692; FStar_Syntax_Syntax.fv_qual = _57_690}) -> begin
(

let _57_704 = (FStar_TypeChecker_Env.lookup_lid env.env lid)
in (match (_57_704) with
| (_57_702, t) -> begin
(

let txt = (FStar_Ident.text_of_lid lid)
in (

let allowed_prefixes = ("Mktuple")::("Left")::("Right")::("Some")::("None")::[]
in if (FStar_List.existsb (fun s -> (FStar_Util.starts_with txt (Prims.strcat "Prims." s))) allowed_prefixes) then begin
(let _151_697 = (let _151_696 = (normalize t)
in N (_151_696))
in ((_151_697), (e), (e)))
end else begin
(let _151_699 = (let _151_698 = (FStar_Util.format1 "The %s constructor has not been whitelisted for the definition language; if this is a function application, consider using [inline]" txt)
in FStar_Syntax_Syntax.Err (_151_698))
in (Prims.raise _151_699))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_715 = (check_n env head)
in (match (_57_715) with
| (t_head, s_head, u_head) -> begin
(

let is_arrow = (fun t -> (match ((let _151_702 = (FStar_Syntax_Subst.compress t)
in _151_702.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_719) -> begin
true
end
| _57_722 -> begin
false
end))
in (

let rec flatten = (fun t -> (match ((let _151_705 = (FStar_Syntax_Subst.compress t)
in _151_705.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (t, _57_734); FStar_Syntax_Syntax.tk = _57_731; FStar_Syntax_Syntax.pos = _57_729; FStar_Syntax_Syntax.vars = _57_727}) when (is_arrow t) -> begin
(

let _57_742 = (flatten t)
in (match (_57_742) with
| (binders', comp) -> begin
(((FStar_List.append binders binders')), (comp))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
((binders), (comp))
end
| _57_748 -> begin
(let _151_708 = (let _151_707 = (let _151_706 = (FStar_Syntax_Print.term_to_string t_head)
in (FStar_Util.format1 "%s: not a function type" _151_706))
in FStar_Syntax_Syntax.Err (_151_707))
in (Prims.raise _151_708))
end))
in (

let _57_751 = (flatten t_head)
in (match (_57_751) with
| (binders, comp) -> begin
(

let n = (FStar_List.length binders)
in (

let n' = (FStar_List.length args)
in (

let _57_754 = if ((FStar_List.length binders) < (FStar_List.length args)) then begin
(let _151_713 = (let _151_712 = (let _151_711 = (FStar_Util.string_of_int n)
in (let _151_710 = (FStar_Util.string_of_int (n' - n))
in (let _151_709 = (FStar_Util.string_of_int n)
in (FStar_Util.format3 "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments." _151_711 _151_710 _151_709))))
in FStar_Syntax_Syntax.Err (_151_712))
in (Prims.raise _151_713))
end else begin
()
end
in (

let _57_758 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (_57_758) with
| (binders, comp) -> begin
(

let rec final_type = (fun subst _57_763 args -> (match (_57_763) with
| (binders, comp) -> begin
(match (((binders), (args))) with
| ([], []) -> begin
(let _151_721 = (let _151_720 = (FStar_Syntax_Subst.subst_comp subst comp)
in _151_720.FStar_Syntax_Syntax.n)
in (nm_of_comp _151_721))
end
| (binders, []) -> begin
(match ((let _151_724 = (let _151_723 = (let _151_722 = (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))))
in (FStar_Syntax_Subst.subst subst _151_722))
in (FStar_Syntax_Subst.compress _151_723))
in _151_724.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(let _151_728 = (let _151_727 = (let _151_726 = (let _151_725 = (FStar_Syntax_Subst.close_comp binders comp)
in ((binders), (_151_725)))
in FStar_Syntax_Syntax.Tm_arrow (_151_726))
in (mk _151_727))
in N (_151_728))
end
| _57_776 -> begin
(FStar_All.failwith "wat?")
end)
end
| ([], (_57_781)::_57_779) -> begin
(FStar_All.failwith "just checked that?!")
end
| (((bv, _57_787))::binders, ((arg, _57_793))::args) -> begin
(final_type ((FStar_Syntax_Syntax.NT (((bv), (arg))))::subst) ((binders), (comp)) args)
end)
end))
in (

let final_type = (final_type [] ((binders), (comp)) args)
in (

let _57_818 = (let _151_743 = (FStar_List.map2 (fun _57_801 _57_804 -> (match (((_57_801), (_57_804))) with
| ((bv, _57_800), (arg, q)) -> begin
(match ((let _151_731 = (FStar_Syntax_Subst.compress bv.FStar_Syntax_Syntax.sort)
in _151_731.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_806) -> begin
(

let arg = ((arg), (q))
in ((arg), ((arg)::[])))
end
| _57_810 -> begin
(

let _57_815 = (check_n env arg)
in (match (_57_815) with
| (_57_812, s_arg, u_arg) -> begin
(let _151_742 = (let _151_732 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_arg), (_151_732)))
in (let _151_741 = if (is_C bv.FStar_Syntax_Syntax.sort) then begin
(let _151_738 = (let _151_734 = (FStar_Syntax_Subst.subst env.subst s_arg)
in (let _151_733 = (FStar_Syntax_Syntax.as_implicit false)
in ((_151_734), (_151_733))))
in (let _151_737 = (let _151_736 = (let _151_735 = (FStar_Syntax_Syntax.as_implicit false)
in ((u_arg), (_151_735)))
in (_151_736)::[])
in (_151_738)::_151_737))
end else begin
(let _151_740 = (let _151_739 = (FStar_Syntax_Syntax.as_implicit false)
in ((u_arg), (_151_739)))
in (_151_740)::[])
end
in ((_151_742), (_151_741))))
end))
end)
end)) binders args)
in (FStar_List.split _151_743))
in (match (_57_818) with
| (s_args, u_args) -> begin
(

let u_args = (FStar_List.flatten u_args)
in (let _151_745 = (mk (FStar_Syntax_Syntax.Tm_app (((s_head), (s_args)))))
in (let _151_744 = (mk (FStar_Syntax_Syntax.Tm_app (((u_head), (u_args)))))
in ((final_type), (_151_745), (_151_744)))))
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
(let _151_747 = (let _151_746 = (env.tc_const c)
in N (_151_746))
in ((_151_747), (e), (e)))
end
| FStar_Syntax_Syntax.Tm_let (_57_849) -> begin
(let _151_749 = (let _151_748 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_let %s" _151_748))
in (FStar_All.failwith _151_749))
end
| FStar_Syntax_Syntax.Tm_type (_57_852) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_855) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_57_858) -> begin
(let _151_751 = (let _151_750 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_refine %s" _151_750))
in (FStar_All.failwith _151_751))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_861) -> begin
(let _151_753 = (let _151_752 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_uvar %s" _151_752))
in (FStar_All.failwith _151_753))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_864) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _151_758 = (let _151_757 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_unknown %s" _151_757))
in (FStar_All.failwith _151_758))
end))))
and mk_match : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e0 branches f -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e0.FStar_Syntax_Syntax.pos))
in (

let _57_877 = (check_n env e0)
in (match (_57_877) with
| (_57_874, s_e0, u_e0) -> begin
(

let _57_894 = (let _151_774 = (FStar_List.map (fun b -> (match ((FStar_Syntax_Subst.open_branch b)) with
| (pat, None, body) -> begin
(

let env = (

let _57_883 = env
in (let _151_773 = (let _151_772 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env.env _151_772))
in {env = _151_773; subst = _57_883.subst; tc_const = _57_883.tc_const}))
in (

let _57_889 = (f env body)
in (match (_57_889) with
| (nm, s_body, u_body) -> begin
((nm), (((pat), (None), (((s_body), (u_body), (body))))))
end)))
end
| _57_891 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("No when clauses in the definition language")))
end)) branches)
in (FStar_List.split _151_774))
in (match (_57_894) with
| (nms, branches) -> begin
(

let t1 = (match ((FStar_List.hd nms)) with
| (M (t1)) | (N (t1)) -> begin
t1
end)
in (

let has_m = (FStar_List.existsb (fun _57_6 -> (match (_57_6) with
| M (_57_901) -> begin
true
end
| _57_904 -> begin
false
end)) nms)
in (

let _57_938 = (let _151_778 = (FStar_List.map2 (fun nm _57_913 -> (match (_57_913) with
| (pat, guard, (s_body, u_body, original_body)) -> begin
(match (((nm), (has_m))) with
| ((N (t2), false)) | ((M (t2), true)) -> begin
((nm), (((pat), (guard), (s_body))), (((pat), (guard), (u_body))))
end
| (N (t2), true) -> begin
(

let _57_929 = (check env original_body (M (t2)))
in (match (_57_929) with
| (_57_926, s_body, u_body) -> begin
((M (t2)), (((pat), (guard), (s_body))), (((pat), (guard), (u_body))))
end))
end
| (M (_57_931), false) -> begin
(FStar_All.failwith "impossible")
end)
end)) nms branches)
in (FStar_List.unzip3 _151_778))
in (match (_57_938) with
| (nms, s_branches, u_branches) -> begin
(

let s_branches = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let t1_star = if has_m then begin
(let _151_783 = (let _151_781 = (let _151_780 = (let _151_779 = (mk_star_to_type mk env t1)
in (FStar_Syntax_Syntax.new_bv None _151_779))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _151_780))
in (_151_781)::[])
in (let _151_782 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _151_783 _151_782)))
end else begin
t1
end
in (let _151_788 = (let _151_786 = (let _151_785 = (let _151_784 = (mk (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches)))))
in ((_151_784), (FStar_Util.Inl (t1_star)), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (_151_785))
in (mk _151_786))
in (let _151_787 = (mk (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches)))))
in ((if has_m then begin
M (t1)
end else begin
N (t1)
end), (_151_788), (_151_787)))))))
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

let x_binders = (let _151_808 = (FStar_Syntax_Syntax.mk_binder x)
in (_151_808)::[])
in (

let _57_954 = (FStar_Syntax_Subst.open_term x_binders e2)
in (match (_57_954) with
| (x_binders, e2) -> begin
(match ((infer env e1)) with
| (N (t1), s_e1, u_e1) -> begin
(

let env = (

let _57_960 = env
in (let _151_809 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_962 = x
in {FStar_Syntax_Syntax.ppname = _57_962.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_962.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _151_809; subst = _57_960.subst; tc_const = _57_960.tc_const}))
in (

let _57_968 = (proceed env e2)
in (match (_57_968) with
| (nm_rec, s_e2, u_e2) -> begin
(let _151_817 = (let _151_812 = (let _151_811 = (let _151_810 = (FStar_Syntax_Subst.close x_binders s_e2)
in ((((false), (((

let _57_969 = binding
in {FStar_Syntax_Syntax.lbname = _57_969.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_969.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_969.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_969.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = s_e1}))::[]))), (_151_810)))
in FStar_Syntax_Syntax.Tm_let (_151_811))
in (mk _151_812))
in (let _151_816 = (let _151_815 = (let _151_814 = (let _151_813 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _57_971 = binding
in {FStar_Syntax_Syntax.lbname = _57_971.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_971.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_971.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_971.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_151_813)))
in FStar_Syntax_Syntax.Tm_let (_151_814))
in (mk _151_815))
in ((nm_rec), (_151_817), (_151_816))))
end)))
end
| (M (t1), s_e1, u_e1) -> begin
(

let env = (

let _57_978 = env
in (let _151_818 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_980 = x
in {FStar_Syntax_Syntax.ppname = _57_980.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_980.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _151_818; subst = _57_978.subst; tc_const = _57_978.tc_const}))
in (

let _57_986 = (ensure_m env e2)
in (match (_57_986) with
| (t2, s_e2, u_e2) -> begin
(

let p_type = (mk_star_to_type mk env t2)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" None p_type)
in (

let s_e2 = (let _151_824 = (let _151_823 = (let _151_822 = (let _151_821 = (let _151_820 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _151_819 = (FStar_Syntax_Syntax.as_implicit false)
in ((_151_820), (_151_819))))
in (_151_821)::[])
in ((s_e2), (_151_822)))
in FStar_Syntax_Syntax.Tm_app (_151_823))
in (mk _151_824))
in (

let s_e2 = (FStar_Syntax_Util.abs x_binders s_e2 None)
in (

let body = (let _151_829 = (let _151_828 = (let _151_827 = (let _151_826 = (let _151_825 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_e2), (_151_825)))
in (_151_826)::[])
in ((s_e1), (_151_827)))
in FStar_Syntax_Syntax.Tm_app (_151_828))
in (mk _151_829))
in (let _151_836 = (let _151_831 = (let _151_830 = (FStar_Syntax_Syntax.mk_binder p)
in (_151_830)::[])
in (FStar_Syntax_Util.abs _151_831 body None))
in (let _151_835 = (let _151_834 = (let _151_833 = (let _151_832 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _57_992 = binding
in {FStar_Syntax_Syntax.lbname = _57_992.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_992.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_992.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_992.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_151_832)))
in FStar_Syntax_Syntax.Tm_let (_151_833))
in (mk _151_834))
in ((M (t2)), (_151_836), (_151_835)))))))))
end)))
end)
end)))))))
and check_n : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _151_839 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in N (_151_839))
in (match ((check env e mn)) with
| (N (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_1003 -> begin
(FStar_All.failwith "[check_n]: impossible")
end)))
and check_m : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _151_842 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in M (_151_842))
in (match ((check env e mn)) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_1013 -> begin
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

let _57_1024 = if (not ((is_C c))) then begin
(FStar_All.failwith "not a C")
end else begin
()
end
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos))
in (match ((let _151_851 = (FStar_Syntax_Subst.compress c)
in _151_851.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_1034 = (FStar_Syntax_Util.head_and_args wp)
in (match (_57_1034) with
| (wp_head, wp_args) -> begin
(

let _57_1035 = if ((not (((FStar_List.length wp_args) = (FStar_List.length args)))) || (not ((let _151_852 = (FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length wp_args) FStar_Range.dummyRange)
in (FStar_Syntax_Util.is_constructor wp_head _151_852))))) then begin
(FStar_All.failwith "mismatch")
end else begin
()
end
in (let _151_859 = (let _151_858 = (let _151_857 = (FStar_List.map2 (fun _57_1040 _57_1044 -> (match (((_57_1040), (_57_1044))) with
| ((arg, _57_1039), (wp_arg, _57_1043)) -> begin
(let _151_856 = (trans_F_ env arg wp_arg)
in (let _151_855 = (FStar_Syntax_Syntax.as_implicit false)
in ((_151_856), (_151_855))))
end)) args wp_args)
in ((head), (_151_857)))
in FStar_Syntax_Syntax.Tm_app (_151_858))
in (mk _151_859)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let binders = (FStar_Syntax_Util.name_binders binders)
in (

let binders = (FStar_Syntax_Subst.open_binders binders)
in (

let _57_1053 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (_57_1053) with
| (binders, comp) -> begin
(

let _57_1062 = (let _151_871 = (FStar_List.map (fun _57_1056 -> (match (_57_1056) with
| (bv, q) -> begin
(

let h = bv.FStar_Syntax_Syntax.sort
in if (is_C h) then begin
(

let w' = (let _151_861 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-w\'") None _151_861))
in (let _151_867 = (let _151_866 = (FStar_Syntax_Syntax.mk_binder w')
in (let _151_865 = (let _151_864 = (let _151_863 = (let _151_862 = (FStar_Syntax_Syntax.bv_to_name bv)
in (trans_F_ env h _151_862))
in (FStar_Syntax_Syntax.null_binder _151_863))
in (_151_864)::[])
in (_151_866)::_151_865))
in ((w'), (_151_867))))
end else begin
(

let x = (let _151_868 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-x") None _151_868))
in (let _151_870 = (let _151_869 = (FStar_Syntax_Syntax.mk_binder x)
in (_151_869)::[])
in ((x), (_151_870))))
end)
end)) binders)
in (FStar_List.split _151_871))
in (match (_57_1062) with
| (bvs, binders) -> begin
(

let binders = (FStar_List.flatten binders)
in (

let app = (let _151_877 = (let _151_876 = (let _151_875 = (FStar_List.map (fun bv -> (let _151_874 = (FStar_Syntax_Syntax.bv_to_name bv)
in (let _151_873 = (FStar_Syntax_Syntax.as_implicit false)
in ((_151_874), (_151_873))))) bvs)
in ((wp), (_151_875)))
in FStar_Syntax_Syntax.Tm_app (_151_876))
in (mk _151_877))
in (

let comp = (let _151_879 = (type_of_comp comp)
in (let _151_878 = (is_monadic_comp comp)
in (trans_G env _151_879 _151_878 app)))
in (

let comp = (FStar_Syntax_Subst.close_comp binders comp)
in (

let binders = (FStar_Syntax_Subst.close_binders binders)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp))))))))))
end))
end))))
end
| _57_1070 -> begin
(FStar_All.failwith "impossible trans_F_")
end))))
and trans_G : env_  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env h is_monadic wp -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None h.FStar_Syntax_Syntax.pos))
in if is_monadic then begin
(let _151_890 = (let _151_889 = (star_type' env h)
in (let _151_888 = (let _151_887 = (let _151_886 = (FStar_Syntax_Syntax.as_implicit false)
in ((wp), (_151_886)))
in (_151_887)::[])
in {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_unknown)::[]; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _151_889; FStar_Syntax_Syntax.effect_args = _151_888; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp _151_890))
end else begin
(let _151_891 = (trans_F_ env h wp)
in (FStar_Syntax_Syntax.mk_Total _151_891))
end))


let n : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.NoInline)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]))


let star_type : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _151_898 = (n env.env t)
in (star_type' env _151_898)))


let star_expr : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env t -> (let _151_903 = (n env.env t)
in (check_n env _151_903)))


let trans_F : env_  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> (let _151_911 = (n env.env c)
in (let _151_910 = (n env.env wp)
in (trans_F_ env _151_911 _151_910))))




