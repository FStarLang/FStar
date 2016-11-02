
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

let rec collect_binders = (fun t -> (match ((let _152_17 = (FStar_Syntax_Subst.compress t)
in _152_17.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let rest = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _57_30) -> begin
t
end
| _57_34 -> begin
(FStar_All.failwith "wp_a contains non-Tot arrow")
end)
in (let _152_18 = (collect_binders rest)
in (FStar_List.append bs _152_18)))
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

let gamma = (let _152_21 = (collect_binders wp_a)
in (FStar_All.pipe_right _152_21 FStar_Syntax_Util.name_binders))
in (

let _57_44 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _152_23 = (let _152_22 = (FStar_Syntax_Print.binders_to_string ", " gamma)
in (FStar_Util.format1 "Gamma is %s\n" _152_22))
in (d _152_23))
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

let _57_57 = (let _152_33 = (let _152_32 = (FStar_ST.read sigelts)
in (sigelt)::_152_32)
in (FStar_ST.op_Colon_Equals sigelts _152_33))
in fv)
end)))
in (

let binders_of_list = (FStar_List.map (fun _57_61 -> (match (_57_61) with
| (t, b) -> begin
(let _152_36 = (FStar_Syntax_Syntax.as_implicit b)
in ((t), (_152_36)))
end)))
in (

let mk_all_implicit = (FStar_List.map (fun t -> (let _152_39 = (FStar_Syntax_Syntax.as_implicit true)
in (((Prims.fst t)), (_152_39)))))
in (

let args_of_binders = (FStar_List.map (fun bv -> (let _152_42 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst bv))
in (FStar_Syntax_Syntax.as_arg _152_42))))
in (

let _57_88 = (

let _57_73 = (

let mk = (fun f -> (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let body = (let _152_55 = (let _152_54 = (FStar_Syntax_Syntax.bv_to_name t)
in (f _152_54))
in (FStar_Syntax_Util.arrow gamma _152_55))
in (let _152_60 = (let _152_59 = (let _152_58 = (FStar_Syntax_Syntax.mk_binder a)
in (let _152_57 = (let _152_56 = (FStar_Syntax_Syntax.mk_binder t)
in (_152_56)::[])
in (_152_58)::_152_57))
in (FStar_List.append binders _152_59))
in (FStar_Syntax_Util.abs _152_60 body None)))))
in (let _152_62 = (mk FStar_Syntax_Syntax.mk_Total)
in (let _152_61 = (mk FStar_Syntax_Syntax.mk_GTotal)
in ((_152_62), (_152_61)))))
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

let mk_app = (fun fv t -> (let _152_84 = (let _152_83 = (let _152_82 = (let _152_81 = (FStar_List.map (fun _57_84 -> (match (_57_84) with
| (bv, _57_83) -> begin
(let _152_73 = (FStar_Syntax_Syntax.bv_to_name bv)
in (let _152_72 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_73), (_152_72))))
end)) binders)
in (let _152_80 = (let _152_79 = (let _152_75 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _152_74 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_75), (_152_74))))
in (let _152_78 = (let _152_77 = (let _152_76 = (FStar_Syntax_Syntax.as_implicit false)
in ((t), (_152_76)))
in (_152_77)::[])
in (_152_79)::_152_78))
in (FStar_List.append _152_81 _152_80)))
in ((fv), (_152_82)))
in FStar_Syntax_Syntax.Tm_app (_152_83))
in (mk _152_84)))
in ((env), ((mk_app ctx_fv)), ((mk_app gctx_fv))))))))
end))
in (match (_57_88) with
| (env, mk_ctx, mk_gctx) -> begin
(

let c_pure = (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let x = (let _152_89 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" None _152_89))
in (

let ret = (let _152_94 = (let _152_93 = (let _152_92 = (let _152_91 = (let _152_90 = (FStar_Syntax_Syntax.bv_to_name t)
in (mk_ctx _152_90))
in (FStar_Syntax_Syntax.mk_Total _152_91))
in (FStar_Syntax_Util.lcomp_of_comp _152_92))
in FStar_Util.Inl (_152_93))
in Some (_152_94))
in (

let body = (let _152_95 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs gamma _152_95 ret))
in (let _152_98 = (let _152_97 = (mk_all_implicit binders)
in (let _152_96 = (binders_of_list ((((a), (true)))::(((t), (true)))::(((x), (false)))::[]))
in (FStar_List.append _152_97 _152_96)))
in (FStar_Syntax_Util.abs _152_98 body ret))))))
in (

let c_pure = (let _152_99 = (mk_lid "pure")
in (register env _152_99 c_pure))
in (

let c_app = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let l = (let _152_107 = (let _152_106 = (let _152_105 = (let _152_102 = (let _152_101 = (let _152_100 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv None _152_100))
in (FStar_Syntax_Syntax.mk_binder _152_101))
in (_152_102)::[])
in (let _152_104 = (let _152_103 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _152_103))
in (FStar_Syntax_Util.arrow _152_105 _152_104)))
in (mk_gctx _152_106))
in (FStar_Syntax_Syntax.gen_bv "l" None _152_107))
in (

let r = (let _152_109 = (let _152_108 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _152_108))
in (FStar_Syntax_Syntax.gen_bv "r" None _152_109))
in (

let ret = (let _152_114 = (let _152_113 = (let _152_112 = (let _152_111 = (let _152_110 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _152_110))
in (FStar_Syntax_Syntax.mk_Total _152_111))
in (FStar_Syntax_Util.lcomp_of_comp _152_112))
in FStar_Util.Inl (_152_113))
in Some (_152_114))
in (

let outer_body = (

let gamma_as_args = (args_of_binders gamma)
in (

let inner_body = (let _152_120 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _152_119 = (let _152_118 = (let _152_117 = (let _152_116 = (let _152_115 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app _152_115 gamma_as_args))
in (FStar_Syntax_Syntax.as_arg _152_116))
in (_152_117)::[])
in (FStar_List.append gamma_as_args _152_118))
in (FStar_Syntax_Util.mk_app _152_120 _152_119)))
in (FStar_Syntax_Util.abs gamma inner_body ret)))
in (let _152_123 = (let _152_122 = (mk_all_implicit binders)
in (let _152_121 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((l), (false)))::(((r), (false)))::[]))
in (FStar_List.append _152_122 _152_121)))
in (FStar_Syntax_Util.abs _152_123 outer_body ret))))))))
in (

let c_app = (let _152_124 = (mk_lid "app")
in (register env _152_124 c_app))
in (

let c_lift1 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _152_129 = (let _152_126 = (let _152_125 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _152_125))
in (_152_126)::[])
in (let _152_128 = (let _152_127 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _152_127))
in (FStar_Syntax_Util.arrow _152_129 _152_128)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _152_131 = (let _152_130 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _152_130))
in (FStar_Syntax_Syntax.gen_bv "a1" None _152_131))
in (

let ret = (let _152_136 = (let _152_135 = (let _152_134 = (let _152_133 = (let _152_132 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _152_132))
in (FStar_Syntax_Syntax.mk_Total _152_133))
in (FStar_Syntax_Util.lcomp_of_comp _152_134))
in FStar_Util.Inl (_152_135))
in Some (_152_136))
in (let _152_148 = (let _152_138 = (mk_all_implicit binders)
in (let _152_137 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::(((a1), (false)))::[]))
in (FStar_List.append _152_138 _152_137)))
in (let _152_147 = (let _152_146 = (let _152_145 = (let _152_144 = (let _152_141 = (let _152_140 = (let _152_139 = (FStar_Syntax_Syntax.bv_to_name f)
in (_152_139)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_140))
in (FStar_Syntax_Util.mk_app c_pure _152_141))
in (let _152_143 = (let _152_142 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_152_142)::[])
in (_152_144)::_152_143))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_145))
in (FStar_Syntax_Util.mk_app c_app _152_146))
in (FStar_Syntax_Util.abs _152_148 _152_147 ret)))))))))
in (

let c_lift1 = (let _152_149 = (mk_lid "lift1")
in (register env _152_149 c_lift1))
in (

let c_lift2 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t3 = (FStar_Syntax_Syntax.gen_bv "t3" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _152_157 = (let _152_154 = (let _152_150 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _152_150))
in (let _152_153 = (let _152_152 = (let _152_151 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.null_binder _152_151))
in (_152_152)::[])
in (_152_154)::_152_153))
in (let _152_156 = (let _152_155 = (FStar_Syntax_Syntax.bv_to_name t3)
in (FStar_Syntax_Syntax.mk_GTotal _152_155))
in (FStar_Syntax_Util.arrow _152_157 _152_156)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _152_159 = (let _152_158 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _152_158))
in (FStar_Syntax_Syntax.gen_bv "a1" None _152_159))
in (

let a2 = (let _152_161 = (let _152_160 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _152_160))
in (FStar_Syntax_Syntax.gen_bv "a2" None _152_161))
in (

let ret = (let _152_166 = (let _152_165 = (let _152_164 = (let _152_163 = (let _152_162 = (FStar_Syntax_Syntax.bv_to_name t3)
in (mk_gctx _152_162))
in (FStar_Syntax_Syntax.mk_Total _152_163))
in (FStar_Syntax_Util.lcomp_of_comp _152_164))
in FStar_Util.Inl (_152_165))
in Some (_152_166))
in (let _152_183 = (let _152_168 = (mk_all_implicit binders)
in (let _152_167 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((t3), (true)))::(((f), (false)))::(((a1), (false)))::(((a2), (false)))::[]))
in (FStar_List.append _152_168 _152_167)))
in (let _152_182 = (let _152_181 = (let _152_180 = (let _152_179 = (let _152_176 = (let _152_175 = (let _152_174 = (let _152_171 = (let _152_170 = (let _152_169 = (FStar_Syntax_Syntax.bv_to_name f)
in (_152_169)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_170))
in (FStar_Syntax_Util.mk_app c_pure _152_171))
in (let _152_173 = (let _152_172 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_152_172)::[])
in (_152_174)::_152_173))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_175))
in (FStar_Syntax_Util.mk_app c_app _152_176))
in (let _152_178 = (let _152_177 = (FStar_Syntax_Syntax.bv_to_name a2)
in (_152_177)::[])
in (_152_179)::_152_178))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_180))
in (FStar_Syntax_Util.mk_app c_app _152_181))
in (FStar_Syntax_Util.abs _152_183 _152_182 ret)))))))))))
in (

let c_lift2 = (let _152_184 = (mk_lid "lift2")
in (register env _152_184 c_lift2))
in (

let c_push = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _152_190 = (let _152_186 = (let _152_185 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _152_185))
in (_152_186)::[])
in (let _152_189 = (let _152_188 = (let _152_187 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _152_187))
in (FStar_Syntax_Syntax.mk_Total _152_188))
in (FStar_Syntax_Util.arrow _152_190 _152_189)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let ret = (let _152_200 = (let _152_199 = (let _152_198 = (let _152_197 = (let _152_196 = (let _152_195 = (let _152_192 = (let _152_191 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _152_191))
in (_152_192)::[])
in (let _152_194 = (let _152_193 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _152_193))
in (FStar_Syntax_Util.arrow _152_195 _152_194)))
in (mk_ctx _152_196))
in (FStar_Syntax_Syntax.mk_Total _152_197))
in (FStar_Syntax_Util.lcomp_of_comp _152_198))
in FStar_Util.Inl (_152_199))
in Some (_152_200))
in (

let e1 = (let _152_201 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" None _152_201))
in (

let body = (let _152_210 = (let _152_203 = (let _152_202 = (FStar_Syntax_Syntax.mk_binder e1)
in (_152_202)::[])
in (FStar_List.append gamma _152_203))
in (let _152_209 = (let _152_208 = (FStar_Syntax_Syntax.bv_to_name f)
in (let _152_207 = (let _152_206 = (let _152_204 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg _152_204))
in (let _152_205 = (args_of_binders gamma)
in (_152_206)::_152_205))
in (FStar_Syntax_Util.mk_app _152_208 _152_207)))
in (FStar_Syntax_Util.abs _152_210 _152_209 ret)))
in (let _152_213 = (let _152_212 = (mk_all_implicit binders)
in (let _152_211 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::[]))
in (FStar_List.append _152_212 _152_211)))
in (FStar_Syntax_Util.abs _152_213 body ret)))))))))
in (

let c_push = (let _152_214 = (mk_lid "push")
in (register env _152_214 c_push))
in (

let ret_tot_wp_a = (let _152_217 = (let _152_216 = (let _152_215 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.lcomp_of_comp _152_215))
in FStar_Util.Inl (_152_216))
in Some (_152_217))
in (

let mk_generic_app = (fun c -> if ((FStar_List.length binders) > (Prims.parse_int "0")) then begin
(let _152_222 = (let _152_221 = (let _152_220 = (args_of_binders binders)
in ((c), (_152_220)))
in FStar_Syntax_Syntax.Tm_app (_152_221))
in (mk _152_222))
end else begin
c
end)
in (

let wp_if_then_else = (

let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (let _152_240 = (let _152_223 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (FStar_List.append binders _152_223))
in (let _152_239 = (

let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "2"))) None)
in (let _152_238 = (let _152_229 = (let _152_228 = (let _152_227 = (let _152_226 = (let _152_225 = (let _152_224 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg _152_224))
in (_152_225)::[])
in (FStar_Syntax_Util.mk_app l_ite _152_226))
in (_152_227)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_228))
in (FStar_Syntax_Util.mk_app c_lift2 _152_229))
in (let _152_237 = (let _152_236 = (let _152_235 = (let _152_234 = (let _152_232 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _152_231 = (let _152_230 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_152_230)::[])
in (_152_232)::_152_231))
in (let _152_233 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _152_234 _152_233)))
in (FStar_Syntax_Syntax.mk_Total _152_235))
in FStar_Util.Inr (_152_236))
in (FStar_Syntax_Util.ascribe _152_238 _152_237))))
in (FStar_Syntax_Util.abs _152_240 _152_239 ret_tot_wp_a))))
in (

let wp_if_then_else = (let _152_241 = (mk_lid "wp_if_then_else")
in (register env _152_241 wp_if_then_else))
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

let body = (let _152_252 = (let _152_251 = (let _152_250 = (let _152_247 = (let _152_246 = (let _152_245 = (let _152_244 = (let _152_243 = (let _152_242 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _152_242))
in (_152_243)::[])
in (FStar_Syntax_Util.mk_app l_and _152_244))
in (_152_245)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_246))
in (FStar_Syntax_Util.mk_app c_pure _152_247))
in (let _152_249 = (let _152_248 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_152_248)::[])
in (_152_250)::_152_249))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_251))
in (FStar_Syntax_Util.mk_app c_app _152_252))
in (let _152_254 = (let _152_253 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders _152_253))
in (FStar_Syntax_Util.abs _152_254 body ret_tot_wp_a))))))
in (

let wp_assert = (let _152_255 = (mk_lid "wp_assert")
in (register env _152_255 wp_assert))
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

let body = (let _152_266 = (let _152_265 = (let _152_264 = (let _152_261 = (let _152_260 = (let _152_259 = (let _152_258 = (let _152_257 = (let _152_256 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _152_256))
in (_152_257)::[])
in (FStar_Syntax_Util.mk_app l_imp _152_258))
in (_152_259)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_260))
in (FStar_Syntax_Util.mk_app c_pure _152_261))
in (let _152_263 = (let _152_262 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_152_262)::[])
in (_152_264)::_152_263))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_265))
in (FStar_Syntax_Util.mk_app c_app _152_266))
in (let _152_268 = (let _152_267 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders _152_267))
in (FStar_Syntax_Util.abs _152_268 body ret_tot_wp_a))))))
in (

let wp_assume = (let _152_269 = (mk_lid "wp_assume")
in (register env _152_269 wp_assume))
in (

let wp_assume = (mk_generic_app wp_assume)
in (

let wp_close = (

let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _152_273 = (let _152_271 = (let _152_270 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _152_270))
in (_152_271)::[])
in (let _152_272 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _152_273 _152_272)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let body = (let _152_282 = (let _152_281 = (let _152_280 = (let _152_274 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((FStar_Syntax_Util.tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure _152_274))
in (let _152_279 = (let _152_278 = (let _152_277 = (let _152_276 = (let _152_275 = (FStar_Syntax_Syntax.bv_to_name f)
in (_152_275)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_276))
in (FStar_Syntax_Util.mk_app c_push _152_277))
in (_152_278)::[])
in (_152_280)::_152_279))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_281))
in (FStar_Syntax_Util.mk_app c_app _152_282))
in (let _152_284 = (let _152_283 = (FStar_Syntax_Syntax.binders_of_list ((a)::(b)::(f)::[]))
in (FStar_List.append binders _152_283))
in (FStar_Syntax_Util.abs _152_284 body ret_tot_wp_a))))))
in (

let wp_close = (let _152_285 = (mk_lid "wp_close")
in (register env _152_285 wp_close))
in (

let wp_close = (mk_generic_app wp_close)
in (

let ret_tot_type = (let _152_288 = (let _152_287 = (let _152_286 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_286))
in FStar_Util.Inl (_152_287))
in Some (_152_288))
in (

let ret_gtot_type = (let _152_291 = (let _152_290 = (let _152_289 = (FStar_Syntax_Syntax.mk_GTotal FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_289))
in FStar_Util.Inl (_152_290))
in Some (_152_291))
in (

let mk_forall = (fun x body -> (let _152_302 = (let _152_301 = (let _152_300 = (let _152_299 = (let _152_298 = (let _152_297 = (let _152_296 = (FStar_Syntax_Syntax.mk_binder x)
in (_152_296)::[])
in (FStar_Syntax_Util.abs _152_297 body ret_tot_type))
in (FStar_Syntax_Syntax.as_arg _152_298))
in (_152_299)::[])
in ((FStar_Syntax_Util.tforall), (_152_300)))
in FStar_Syntax_Syntax.Tm_app (_152_301))
in (FStar_Syntax_Syntax.mk _152_302 None FStar_Range.dummyRange)))
in (

let rec is_discrete = (fun t -> (match ((let _152_305 = (FStar_Syntax_Subst.compress t)
in _152_305.FStar_Syntax_Syntax.n)) with
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

let rec is_monotonic = (fun t -> (match ((let _152_309 = (FStar_Syntax_Subst.compress t)
in _152_309.FStar_Syntax_Syntax.n)) with
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
in (match ((let _152_332 = (FStar_Syntax_Subst.compress t)
in _152_332.FStar_Syntax_Syntax.n)) with
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

let body = (let _152_340 = (let _152_335 = (let _152_334 = (let _152_333 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _152_333))
in (_152_334)::[])
in (FStar_Syntax_Util.mk_app x _152_335))
in (let _152_339 = (let _152_338 = (let _152_337 = (let _152_336 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _152_336))
in (_152_337)::[])
in (FStar_Syntax_Util.mk_app y _152_338))
in (mk_rel b _152_340 _152_339)))
in (mk_forall a1 body)))
end else begin
(

let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (

let a2 = (FStar_Syntax_Syntax.gen_bv "a2" None a)
in (

let body = (let _152_352 = (let _152_342 = (FStar_Syntax_Syntax.bv_to_name a1)
in (let _152_341 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_rel a _152_342 _152_341)))
in (let _152_351 = (let _152_350 = (let _152_345 = (let _152_344 = (let _152_343 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _152_343))
in (_152_344)::[])
in (FStar_Syntax_Util.mk_app x _152_345))
in (let _152_349 = (let _152_348 = (let _152_347 = (let _152_346 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg _152_346))
in (_152_347)::[])
in (FStar_Syntax_Util.mk_app y _152_348))
in (mk_rel b _152_350 _152_349)))
in (FStar_Syntax_Util.mk_imp _152_352 _152_351)))
in (let _152_353 = (mk_forall a2 body)
in (mk_forall a1 _152_353)))))
end)
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::binders, comp) -> begin
(

let t = (

let _57_248 = t
in (let _152_357 = (let _152_356 = (let _152_355 = (let _152_354 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _152_354))
in (((binder)::[]), (_152_355)))
in FStar_Syntax_Syntax.Tm_arrow (_152_356))
in {FStar_Syntax_Syntax.n = _152_357; FStar_Syntax_Syntax.tk = _57_248.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_248.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_248.FStar_Syntax_Syntax.vars}))
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

let body = (let _152_359 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (let _152_358 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_rel FStar_Syntax_Util.mk_imp wp_a _152_359 _152_358)))
in (let _152_361 = (let _152_360 = (binders_of_list ((((a), (false)))::(((wp1), (false)))::(((wp2), (false)))::[]))
in (FStar_List.append binders _152_360))
in (FStar_Syntax_Util.abs _152_361 body ret_tot_type)))))
in (

let stronger = (let _152_362 = (mk_lid "stronger")
in (register env _152_362 stronger))
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

let eq = (let _152_363 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst post))
in (mk_rel FStar_Syntax_Util.mk_iff k.FStar_Syntax_Syntax.sort k_tm _152_363))
in (match ((FStar_Syntax_Util.destruct_typ_as_formula eq)) with
| Some (FStar_Syntax_Util.QAll (binders, [], body)) -> begin
(

let k_app = (let _152_364 = (args_of_binders binders)
in (FStar_Syntax_Util.mk_app k_tm _152_364))
in (

let guard_free = (let _152_365 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.guard_free FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _152_365))
in (

let pat = (let _152_367 = (let _152_366 = (FStar_Syntax_Syntax.as_arg k_app)
in (_152_366)::[])
in (FStar_Syntax_Util.mk_app guard_free _152_367))
in (

let pattern_guarded_body = (let _152_373 = (let _152_372 = (let _152_371 = (let _152_370 = (let _152_369 = (let _152_368 = (FStar_Syntax_Syntax.as_arg pat)
in (_152_368)::[])
in (_152_369)::[])
in FStar_Syntax_Syntax.Meta_pattern (_152_370))
in ((body), (_152_371)))
in FStar_Syntax_Syntax.Tm_meta (_152_372))
in (mk _152_373))
in (FStar_Syntax_Util.close_forall binders pattern_guarded_body)))))
end
| _57_280 -> begin
(FStar_All.failwith "Impossible: Expected the equivalence to be a quantified formula")
end)))
in (

let body = (let _152_382 = (let _152_381 = (let _152_380 = (let _152_379 = (FStar_Syntax_Syntax.bv_to_name wp)
in (let _152_378 = (let _152_377 = (args_of_binders wp_args)
in (let _152_376 = (let _152_375 = (let _152_374 = (FStar_Syntax_Syntax.bv_to_name k)
in (FStar_Syntax_Syntax.as_arg _152_374))
in (_152_375)::[])
in (FStar_List.append _152_377 _152_376)))
in (FStar_Syntax_Util.mk_app _152_379 _152_378)))
in (FStar_Syntax_Util.mk_imp equiv _152_380))
in (FStar_Syntax_Util.mk_forall k _152_381))
in (FStar_Syntax_Util.abs gamma _152_382 ret_gtot_type))
in (let _152_384 = (let _152_383 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders _152_383))
in (FStar_Syntax_Util.abs _152_384 body ret_gtot_type)))))
end)))
in (

let wp_ite = (let _152_385 = (mk_lid "wp_ite")
in (register env _152_385 wp_ite))
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

let body = (let _152_390 = (let _152_389 = (FStar_All.pipe_left FStar_Syntax_Syntax.bv_to_name (Prims.fst post))
in (let _152_388 = (let _152_387 = (let _152_386 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _152_386))
in (_152_387)::[])
in (FStar_Syntax_Util.mk_app _152_389 _152_388)))
in (FStar_Syntax_Util.mk_forall x _152_390))
in (let _152_393 = (let _152_392 = (let _152_391 = (FStar_Syntax_Syntax.binders_of_list ((a)::[]))
in (FStar_List.append _152_391 gamma))
in (FStar_List.append binders _152_392))
in (FStar_Syntax_Util.abs _152_393 body ret_gtot_type))))
end)))
in (

let null_wp = (let _152_394 = (mk_lid "null_wp")
in (register env _152_394 null_wp))
in (

let null_wp = (mk_generic_app null_wp)
in (

let wp_trivial = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let body = (let _152_404 = (let _152_403 = (let _152_402 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _152_401 = (let _152_400 = (let _152_397 = (let _152_396 = (let _152_395 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg _152_395))
in (_152_396)::[])
in (FStar_Syntax_Util.mk_app null_wp _152_397))
in (let _152_399 = (let _152_398 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_152_398)::[])
in (_152_400)::_152_399))
in (_152_402)::_152_401))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_403))
in (FStar_Syntax_Util.mk_app stronger _152_404))
in (let _152_406 = (let _152_405 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders _152_405))
in (FStar_Syntax_Util.abs _152_406 body ret_tot_type))))
in (

let wp_trivial = (let _152_407 = (mk_lid "wp_trivial")
in (register env _152_407 wp_trivial))
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
in (let _152_427 = (let _152_409 = (FStar_ST.read sigelts)
in (FStar_List.rev _152_409))
in (let _152_426 = (

let _57_303 = ed
in (let _152_425 = (let _152_410 = (c wp_if_then_else)
in (([]), (_152_410)))
in (let _152_424 = (let _152_411 = (c wp_ite)
in (([]), (_152_411)))
in (let _152_423 = (let _152_412 = (c stronger)
in (([]), (_152_412)))
in (let _152_422 = (let _152_413 = (c wp_close)
in (([]), (_152_413)))
in (let _152_421 = (let _152_414 = (c wp_assert)
in (([]), (_152_414)))
in (let _152_420 = (let _152_415 = (c wp_assume)
in (([]), (_152_415)))
in (let _152_419 = (let _152_416 = (c null_wp)
in (([]), (_152_416)))
in (let _152_418 = (let _152_417 = (c wp_trivial)
in (([]), (_152_417)))
in {FStar_Syntax_Syntax.qualifiers = _57_303.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_303.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_303.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_303.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_303.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _57_303.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _57_303.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _152_425; FStar_Syntax_Syntax.ite_wp = _152_424; FStar_Syntax_Syntax.stronger = _152_423; FStar_Syntax_Syntax.close_wp = _152_422; FStar_Syntax_Syntax.assert_p = _152_421; FStar_Syntax_Syntax.assume_p = _152_420; FStar_Syntax_Syntax.null_wp = _152_419; FStar_Syntax_Syntax.trivial = _152_418; FStar_Syntax_Syntax.repr = _57_303.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _57_303.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _57_303.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _57_303.FStar_Syntax_Syntax.actions})))))))))
in ((_152_427), (_152_426))))))))))))))))))))))))))))))))))))))))))))))))
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
(let _152_484 = (let _152_483 = (FStar_Ident.string_of_lid c.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format1 "[nm_of_comp]: impossible (%s)" _152_483))
in (FStar_All.failwith _152_484))
end
| FStar_Syntax_Syntax.GTotal (_57_328) -> begin
(FStar_All.failwith "[nm_of_comp]: impossible (GTot)")
end))


let string_of_nm : nm  ->  Prims.string = (fun _57_2 -> (match (_57_2) with
| N (t) -> begin
(let _152_487 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "N[%s]" _152_487))
end
| M (t) -> begin
(let _152_488 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "M[%s]" _152_488))
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


let rec mk_star_to_type : (FStar_Syntax_Syntax.term'  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun mk env a -> (let _152_513 = (let _152_512 = (let _152_511 = (let _152_509 = (let _152_508 = (let _152_506 = (star_type' env a)
in (FStar_Syntax_Syntax.null_bv _152_506))
in (let _152_507 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_508), (_152_507))))
in (_152_509)::[])
in (let _152_510 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_152_511), (_152_510))))
in FStar_Syntax_Syntax.Tm_arrow (_152_512))
in (mk _152_513)))
and star_type' : env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None t.FStar_Syntax_Syntax.pos))
in (

let mk_star_to_type = (mk_star_to_type mk)
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _57_368) -> begin
(

let binders = (FStar_List.map (fun _57_373 -> (match (_57_373) with
| (bv, aqual) -> begin
(let _152_522 = (

let _57_374 = bv
in (let _152_521 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_374.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_374.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _152_521}))
in ((_152_522), (aqual)))
end)) binders)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_378, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (hn, _57_387); FStar_Syntax_Syntax.tk = _57_384; FStar_Syntax_Syntax.pos = _57_382; FStar_Syntax_Syntax.vars = _57_380}) -> begin
(let _152_526 = (let _152_525 = (let _152_524 = (let _152_523 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_GTotal _152_523))
in ((binders), (_152_524)))
in FStar_Syntax_Syntax.Tm_arrow (_152_525))
in (mk _152_526))
end
| _57_394 -> begin
(match ((is_monadic_arrow t.FStar_Syntax_Syntax.n)) with
| N (hn) -> begin
(let _152_530 = (let _152_529 = (let _152_528 = (let _152_527 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_Total _152_527))
in ((binders), (_152_528)))
in FStar_Syntax_Syntax.Tm_arrow (_152_529))
in (mk _152_530))
end
| M (a) -> begin
(let _152_539 = (let _152_538 = (let _152_537 = (let _152_535 = (let _152_534 = (let _152_533 = (let _152_531 = (mk_star_to_type env a)
in (FStar_Syntax_Syntax.null_bv _152_531))
in (let _152_532 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_533), (_152_532))))
in (_152_534)::[])
in (FStar_List.append binders _152_535))
in (let _152_536 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_152_537), (_152_536))))
in FStar_Syntax_Syntax.Tm_arrow (_152_538))
in (mk _152_539))
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

let _57_415 = (FStar_Util.string_builder_append strb "{")
in (

let _57_417 = (let _152_553 = (f x)
in (FStar_Util.string_builder_append strb _152_553))
in (

let _57_422 = (FStar_List.iter (fun x -> (

let _57_420 = (FStar_Util.string_builder_append strb ", ")
in (let _152_555 = (f x)
in (FStar_Util.string_builder_append strb _152_555)))) xs)
in (

let _57_424 = (FStar_Util.string_builder_append strb "}")
in (FStar_Util.string_of_string_builder strb))))))
end)))
in (let _152_557 = (FStar_Syntax_Print.term_to_string t)
in (let _152_556 = (string_of_set FStar_Syntax_Print.bv_to_string s)
in (FStar_Util.print2_warning "Dependency found in term %s : %s" _152_557 _152_556)))))
in (

let rec is_non_dependent_arrow = (fun ty n -> (match ((let _152_562 = (FStar_Syntax_Subst.compress ty)
in _152_562.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
if (not ((FStar_Syntax_Util.is_tot_or_gtot_comp c))) then begin
false
end else begin
try
(match (()) with
| () -> begin
(

let non_dependent_or_raise = (fun s ty -> (

let sinter = (let _152_568 = (FStar_Syntax_Free.names ty)
in (FStar_Util.set_intersect _152_568 s))
in if (not ((FStar_Util.set_is_empty sinter))) then begin
(

let _57_443 = (debug ty sinter)
in (Prims.raise Not_found))
end else begin
()
end))
in (

let _57_447 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_57_447) with
| (binders, c) -> begin
(

let s = (FStar_List.fold_left (fun s _57_452 -> (match (_57_452) with
| (bv, _57_451) -> begin
(

let _57_453 = (non_dependent_or_raise s bv.FStar_Syntax_Syntax.sort)
in (FStar_Util.set_add bv s))
end)) FStar_Syntax_Syntax.no_names binders)
in (

let ct = (FStar_Syntax_Util.comp_result c)
in (

let _57_457 = (non_dependent_or_raise s ct)
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
| _57_461 -> begin
(

let _57_462 = (let _152_572 = (FStar_Syntax_Print.term_to_string ty)
in (FStar_Util.print1_warning "Not a dependent arrow : %s" _152_572))
in false)
end))
in (

let rec is_valid_application = (fun head -> (match ((let _152_575 = (FStar_Syntax_Subst.compress head)
in _152_575.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.option_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.either_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.eq2_lid)) || (let _152_576 = (FStar_Syntax_Subst.compress head)
in (FStar_Syntax_Util.is_tuple_constructor _152_576))) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (is_non_dependent_arrow fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty (FStar_List.length args)) -> begin
(

let res = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.env t)
in (match (res.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (_57_472) -> begin
true
end
| _57_475 -> begin
(

let _57_476 = (let _152_577 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.print1_warning "Got a term which might be a non-dependent user-defined data-type %s\n" _152_577))
in false)
end))
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uinst (t, _57_486) -> begin
(is_valid_application t)
end
| _57_490 -> begin
false
end))
in if (is_valid_application head) then begin
(let _152_582 = (let _152_581 = (let _152_580 = (FStar_List.map (fun _57_493 -> (match (_57_493) with
| (t, qual) -> begin
(let _152_579 = (star_type' env t)
in ((_152_579), (qual)))
end)) args)
in ((head), (_152_580)))
in FStar_Syntax_Syntax.Tm_app (_152_581))
in (mk _152_582))
end else begin
(let _152_585 = (let _152_584 = (let _152_583 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)" _152_583))
in FStar_Syntax_Syntax.Err (_152_584))
in (Prims.raise _152_585))
end)))
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_abs (binders, repr, something) -> begin
(

let _57_513 = (FStar_Syntax_Subst.open_term binders repr)
in (match (_57_513) with
| (binders, repr) -> begin
(

let env = (

let _57_514 = env
in (let _152_586 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _152_586; subst = _57_514.subst; tc_const = _57_514.tc_const}))
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

let _57_529 = x
in {FStar_Syntax_Syntax.ppname = _57_529.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_529.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (t))))))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(let _152_589 = (let _152_588 = (let _152_587 = (star_type' env t)
in ((_152_587), (m)))
in FStar_Syntax_Syntax.Tm_meta (_152_588))
in (mk _152_589))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), something) -> begin
(let _152_594 = (let _152_593 = (let _152_592 = (star_type' env e)
in (let _152_591 = (let _152_590 = (star_type' env t)
in FStar_Util.Inl (_152_590))
in ((_152_592), (_152_591), (something))))
in FStar_Syntax_Syntax.Tm_ascribed (_152_593))
in (mk _152_594))
end
| FStar_Syntax_Syntax.Tm_ascribed (_57_542) -> begin
(let _152_597 = (let _152_596 = (let _152_595 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_ascribed is outside of the definition language: %s" _152_595))
in FStar_Syntax_Syntax.Err (_152_596))
in (Prims.raise _152_597))
end
| FStar_Syntax_Syntax.Tm_refine (_57_545) -> begin
(let _152_600 = (let _152_599 = (let _152_598 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_refine is outside of the definition language: %s" _152_598))
in FStar_Syntax_Syntax.Err (_152_599))
in (Prims.raise _152_600))
end
| FStar_Syntax_Syntax.Tm_uinst (_57_548) -> begin
(let _152_603 = (let _152_602 = (let _152_601 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_uinst is outside of the definition language: %s" _152_601))
in FStar_Syntax_Syntax.Err (_152_602))
in (Prims.raise _152_603))
end
| FStar_Syntax_Syntax.Tm_constant (_57_551) -> begin
(let _152_606 = (let _152_605 = (let _152_604 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_constant is outside of the definition language: %s" _152_604))
in FStar_Syntax_Syntax.Err (_152_605))
in (Prims.raise _152_606))
end
| FStar_Syntax_Syntax.Tm_match (_57_554) -> begin
(let _152_609 = (let _152_608 = (let _152_607 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_match is outside of the definition language: %s" _152_607))
in FStar_Syntax_Syntax.Err (_152_608))
in (Prims.raise _152_609))
end
| FStar_Syntax_Syntax.Tm_let (_57_557) -> begin
(let _152_612 = (let _152_611 = (let _152_610 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_let is outside of the definition language: %s" _152_610))
in FStar_Syntax_Syntax.Err (_152_611))
in (Prims.raise _152_612))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_560) -> begin
(let _152_615 = (let _152_614 = (let _152_613 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_uvar is outside of the definition language: %s" _152_613))
in FStar_Syntax_Syntax.Err (_152_614))
in (Prims.raise _152_615))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _152_618 = (let _152_617 = (let _152_616 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_unknown is outside of the definition language: %s" _152_616))
in FStar_Syntax_Syntax.Err (_152_617))
in (Prims.raise _152_618))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_564) -> begin
(FStar_All.failwith "impossible")
end)))))


let is_monadic : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  Prims.bool = (fun _57_3 -> (match (_57_3) with
| None -> begin
(FStar_All.failwith "un-annotated lambda?!")
end
| (Some (FStar_Util.Inl ({FStar_Syntax_Syntax.eff_name = lid; FStar_Syntax_Syntax.res_typ = _; FStar_Syntax_Syntax.cflags = _; FStar_Syntax_Syntax.comp = _}))) | (Some (FStar_Util.Inr (lid))) -> begin
(FStar_Ident.lid_equals lid FStar_Syntax_Const.monadic_lid)
end))


let rec is_C : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match ((let _152_626 = (FStar_Syntax_Subst.compress t)
in _152_626.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) when (FStar_Syntax_Util.is_tuple_constructor head) -> begin
(

let r = (let _152_628 = (let _152_627 = (FStar_List.hd args)
in (Prims.fst _152_627))
in (is_C _152_628))
in if r then begin
(

let _57_590 = if (not ((FStar_List.for_all (fun _57_589 -> (match (_57_589) with
| (h, _57_588) -> begin
(is_C h)
end)) args))) then begin
(FStar_All.failwith "not a C (A * C)")
end else begin
()
end
in true)
end else begin
(

let _57_596 = if (not ((FStar_List.for_all (fun _57_595 -> (match (_57_595) with
| (h, _57_594) -> begin
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

let _57_604 = if (is_C t) then begin
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
| _57_624 -> begin
false
end))


let mk_return : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let p_type = (mk_star_to_type mk env t)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'" None p_type)
in (

let body = (let _152_644 = (let _152_643 = (let _152_642 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _152_641 = (let _152_640 = (let _152_639 = (FStar_Syntax_Syntax.as_implicit false)
in ((e), (_152_639)))
in (_152_640)::[])
in ((_152_642), (_152_641))))
in FStar_Syntax_Syntax.Tm_app (_152_643))
in (mk _152_644))
in (let _152_646 = (let _152_645 = (FStar_Syntax_Syntax.mk_binder p)
in (_152_645)::[])
in (FStar_Syntax_Util.abs _152_646 body None)))))))


let is_unknown : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun _57_4 -> (match (_57_4) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| _57_636 -> begin
false
end))


let rec check : env  ->  FStar_Syntax_Syntax.term  ->  nm  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e context_nm -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let return_if = (fun _57_646 -> (match (_57_646) with
| (rec_nm, s_e, u_e) -> begin
(

let check = (fun t1 t2 -> if ((not ((is_unknown t2.FStar_Syntax_Syntax.n))) && (not ((let _152_700 = (FStar_TypeChecker_Rel.teq env.env t1 t2)
in (FStar_TypeChecker_Rel.is_trivial _152_700))))) then begin
(let _152_705 = (let _152_704 = (let _152_703 = (FStar_Syntax_Print.term_to_string e)
in (let _152_702 = (FStar_Syntax_Print.term_to_string t1)
in (let _152_701 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check]: the expression [%s] has type [%s] but should have type [%s]" _152_703 _152_702 _152_701))))
in FStar_Syntax_Syntax.Err (_152_704))
in (Prims.raise _152_705))
end else begin
()
end)
in (match (((rec_nm), (context_nm))) with
| ((N (t1), N (t2))) | ((M (t1), M (t2))) -> begin
(

let _57_658 = (check t1 t2)
in ((rec_nm), (s_e), (u_e)))
end
| (N (t1), M (t2)) -> begin
(

let _57_665 = (check t1 t2)
in (let _152_706 = (mk_return env t1 s_e)
in ((M (t1)), (_152_706), (u_e))))
end
| (M (t1), N (t2)) -> begin
(let _152_711 = (let _152_710 = (let _152_709 = (FStar_Syntax_Print.term_to_string e)
in (let _152_708 = (FStar_Syntax_Print.term_to_string t1)
in (let _152_707 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]" _152_709 _152_708 _152_707))))
in FStar_Syntax_Syntax.Err (_152_710))
in (Prims.raise _152_711))
end))
end))
in (

let ensure_m = (fun env e2 -> (

let strip_m = (fun _57_5 -> (match (_57_5) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_682 -> begin
(FStar_All.failwith "impossible")
end))
in (match (context_nm) with
| N (t) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren\'t"), (e2.FStar_Syntax_Syntax.pos)))))
end
| M (_57_687) -> begin
(let _152_718 = (check env e2 context_nm)
in (strip_m _152_718))
end)))
in (match ((let _152_719 = (FStar_Syntax_Subst.compress e)
in _152_719.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
(let _152_720 = (infer env e)
in (return_if _152_720))
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
| FStar_Syntax_Syntax.Tm_let (_57_738) -> begin
(let _152_728 = (let _152_727 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_let %s" _152_727))
in (FStar_All.failwith _152_728))
end
| FStar_Syntax_Syntax.Tm_type (_57_741) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_744) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_57_747) -> begin
(let _152_730 = (let _152_729 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_refine %s" _152_729))
in (FStar_All.failwith _152_730))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_750) -> begin
(let _152_732 = (let _152_731 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_uvar %s" _152_731))
in (FStar_All.failwith _152_732))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_753) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _152_737 = (let _152_736 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_unknown %s" _152_736))
in (FStar_All.failwith _152_737))
end)))))
and infer : env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.env)
in (match ((let _152_743 = (FStar_Syntax_Subst.compress e)
in _152_743.FStar_Syntax_Syntax.n)) with
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

let _57_773 = env
in (let _152_744 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _152_744; subst = _57_773.subst; tc_const = _57_773.tc_const}))
in (

let s_binders = (FStar_List.map (fun _57_778 -> (match (_57_778) with
| (bv, qual) -> begin
(

let sort = (star_type' env bv.FStar_Syntax_Syntax.sort)
in (((

let _57_780 = bv
in {FStar_Syntax_Syntax.ppname = _57_780.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_780.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (qual)))
end)) binders)
in (

let _57_802 = (FStar_List.fold_left (fun _57_785 _57_788 -> (match (((_57_785), (_57_788))) with
| ((env, acc), (bv, qual)) -> begin
(

let c = bv.FStar_Syntax_Syntax.sort
in if (is_C c) then begin
(

let xw = (let _152_748 = (star_type' env c)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "^w") None _152_748))
in (

let x = (

let _57_791 = bv
in (let _152_750 = (let _152_749 = (FStar_Syntax_Syntax.bv_to_name xw)
in (trans_F_ env c _152_749))
in {FStar_Syntax_Syntax.ppname = _57_791.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_791.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _152_750}))
in (

let env = (

let _57_794 = env
in (let _152_754 = (let _152_753 = (let _152_752 = (let _152_751 = (FStar_Syntax_Syntax.bv_to_name xw)
in ((bv), (_152_751)))
in FStar_Syntax_Syntax.NT (_152_752))
in (_152_753)::env.subst)
in {env = _57_794.env; subst = _152_754; tc_const = _57_794.tc_const}))
in (let _152_758 = (let _152_757 = (FStar_Syntax_Syntax.mk_binder x)
in (let _152_756 = (let _152_755 = (FStar_Syntax_Syntax.mk_binder xw)
in (_152_755)::acc)
in (_152_757)::_152_756))
in ((env), (_152_758))))))
end else begin
(

let x = (

let _57_797 = bv
in (let _152_759 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_797.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_797.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _152_759}))
in (let _152_761 = (let _152_760 = (FStar_Syntax_Syntax.mk_binder x)
in (_152_760)::acc)
in ((env), (_152_761))))
end)
end)) ((env), ([])) binders)
in (match (_57_802) with
| (env, u_binders) -> begin
(

let u_binders = (FStar_List.rev u_binders)
in (

let _57_812 = (

let check_what = if (is_monadic what) then begin
check_m
end else begin
check_n
end
in (

let _57_808 = (check_what env body)
in (match (_57_808) with
| (t, s_body, u_body) -> begin
(let _152_767 = (let _152_766 = if (is_monadic what) then begin
M (t)
end else begin
N (t)
end
in (comp_of_nm _152_766))
in ((_152_767), (s_body), (u_body)))
end)))
in (match (_57_812) with
| (comp, s_body, u_body) -> begin
(

let t = (FStar_Syntax_Util.arrow binders comp)
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
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = {FStar_Syntax_Syntax.v = lid; FStar_Syntax_Syntax.ty = _57_827; FStar_Syntax_Syntax.p = _57_825}; FStar_Syntax_Syntax.fv_delta = _57_823; FStar_Syntax_Syntax.fv_qual = _57_821}) -> begin
(

let _57_835 = (FStar_TypeChecker_Env.lookup_lid env.env lid)
in (match (_57_835) with
| (_57_833, t) -> begin
(

let txt = (FStar_Ident.text_of_lid lid)
in (let _152_769 = (let _152_768 = (normalize t)
in N (_152_768))
in ((_152_769), (e), (e))))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_844 = (check_n env head)
in (match (_57_844) with
| (t_head, s_head, u_head) -> begin
(

let is_arrow = (fun t -> (match ((let _152_772 = (FStar_Syntax_Subst.compress t)
in _152_772.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_848) -> begin
true
end
| _57_851 -> begin
false
end))
in (

let rec flatten = (fun t -> (match ((let _152_775 = (FStar_Syntax_Subst.compress t)
in _152_775.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (t, _57_863); FStar_Syntax_Syntax.tk = _57_860; FStar_Syntax_Syntax.pos = _57_858; FStar_Syntax_Syntax.vars = _57_856}) when (is_arrow t) -> begin
(

let _57_871 = (flatten t)
in (match (_57_871) with
| (binders', comp) -> begin
(((FStar_List.append binders binders')), (comp))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
((binders), (comp))
end
| _57_877 -> begin
(let _152_778 = (let _152_777 = (let _152_776 = (FStar_Syntax_Print.term_to_string t_head)
in (FStar_Util.format1 "%s: not a function type" _152_776))
in FStar_Syntax_Syntax.Err (_152_777))
in (Prims.raise _152_778))
end))
in (

let _57_880 = (flatten t_head)
in (match (_57_880) with
| (binders, comp) -> begin
(

let n = (FStar_List.length binders)
in (

let n' = (FStar_List.length args)
in (

let _57_883 = if ((FStar_List.length binders) < (FStar_List.length args)) then begin
(let _152_783 = (let _152_782 = (let _152_781 = (FStar_Util.string_of_int n)
in (let _152_780 = (FStar_Util.string_of_int (n' - n))
in (let _152_779 = (FStar_Util.string_of_int n)
in (FStar_Util.format3 "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments." _152_781 _152_780 _152_779))))
in FStar_Syntax_Syntax.Err (_152_782))
in (Prims.raise _152_783))
end else begin
()
end
in (

let _57_887 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (_57_887) with
| (binders, comp) -> begin
(

let rec final_type = (fun subst _57_892 args -> (match (_57_892) with
| (binders, comp) -> begin
(match (((binders), (args))) with
| ([], []) -> begin
(let _152_791 = (let _152_790 = (FStar_Syntax_Subst.subst_comp subst comp)
in _152_790.FStar_Syntax_Syntax.n)
in (nm_of_comp _152_791))
end
| (binders, []) -> begin
(match ((let _152_794 = (let _152_793 = (let _152_792 = (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))))
in (FStar_Syntax_Subst.subst subst _152_792))
in (FStar_Syntax_Subst.compress _152_793))
in _152_794.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(let _152_798 = (let _152_797 = (let _152_796 = (let _152_795 = (FStar_Syntax_Subst.close_comp binders comp)
in ((binders), (_152_795)))
in FStar_Syntax_Syntax.Tm_arrow (_152_796))
in (mk _152_797))
in N (_152_798))
end
| _57_905 -> begin
(FStar_All.failwith "wat?")
end)
end
| ([], (_57_910)::_57_908) -> begin
(FStar_All.failwith "just checked that?!")
end
| (((bv, _57_916))::binders, ((arg, _57_922))::args) -> begin
(final_type ((FStar_Syntax_Syntax.NT (((bv), (arg))))::subst) ((binders), (comp)) args)
end)
end))
in (

let final_type = (final_type [] ((binders), (comp)) args)
in (

let _57_930 = (FStar_List.splitAt n' binders)
in (match (_57_930) with
| (binders, _57_929) -> begin
(

let _57_951 = (let _152_813 = (FStar_List.map2 (fun _57_934 _57_937 -> (match (((_57_934), (_57_937))) with
| ((bv, _57_933), (arg, q)) -> begin
(match ((let _152_801 = (FStar_Syntax_Subst.compress bv.FStar_Syntax_Syntax.sort)
in _152_801.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_939) -> begin
(

let arg = ((arg), (q))
in ((arg), ((arg)::[])))
end
| _57_943 -> begin
(

let _57_948 = (check_n env arg)
in (match (_57_948) with
| (_57_945, s_arg, u_arg) -> begin
(let _152_812 = (let _152_802 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_arg), (_152_802)))
in (let _152_811 = if (is_C bv.FStar_Syntax_Syntax.sort) then begin
(let _152_808 = (let _152_804 = (FStar_Syntax_Subst.subst env.subst s_arg)
in (let _152_803 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_804), (_152_803))))
in (let _152_807 = (let _152_806 = (let _152_805 = (FStar_Syntax_Syntax.as_implicit false)
in ((u_arg), (_152_805)))
in (_152_806)::[])
in (_152_808)::_152_807))
end else begin
(let _152_810 = (let _152_809 = (FStar_Syntax_Syntax.as_implicit false)
in ((u_arg), (_152_809)))
in (_152_810)::[])
end
in ((_152_812), (_152_811))))
end))
end)
end)) binders args)
in (FStar_List.split _152_813))
in (match (_57_951) with
| (s_args, u_args) -> begin
(

let u_args = (FStar_List.flatten u_args)
in (let _152_815 = (mk (FStar_Syntax_Syntax.Tm_app (((s_head), (s_args)))))
in (let _152_814 = (mk (FStar_Syntax_Syntax.Tm_app (((u_head), (u_args)))))
in ((final_type), (_152_815), (_152_814)))))
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
(let _152_817 = (let _152_816 = (env.tc_const c)
in N (_152_816))
in ((_152_817), (e), (e)))
end
| FStar_Syntax_Syntax.Tm_let (_57_982) -> begin
(let _152_819 = (let _152_818 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_let %s" _152_818))
in (FStar_All.failwith _152_819))
end
| FStar_Syntax_Syntax.Tm_type (_57_985) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_988) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_57_991) -> begin
(let _152_821 = (let _152_820 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_refine %s" _152_820))
in (FStar_All.failwith _152_821))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_994) -> begin
(let _152_823 = (let _152_822 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_uvar %s" _152_822))
in (FStar_All.failwith _152_823))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_997) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _152_828 = (let _152_827 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_unknown %s" _152_827))
in (FStar_All.failwith _152_828))
end))))
and mk_match : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e0 branches f -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e0.FStar_Syntax_Syntax.pos))
in (

let _57_1010 = (check_n env e0)
in (match (_57_1010) with
| (_57_1007, s_e0, u_e0) -> begin
(

let _57_1027 = (let _152_844 = (FStar_List.map (fun b -> (match ((FStar_Syntax_Subst.open_branch b)) with
| (pat, None, body) -> begin
(

let env = (

let _57_1016 = env
in (let _152_843 = (let _152_842 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env.env _152_842))
in {env = _152_843; subst = _57_1016.subst; tc_const = _57_1016.tc_const}))
in (

let _57_1022 = (f env body)
in (match (_57_1022) with
| (nm, s_body, u_body) -> begin
((nm), (((pat), (None), (((s_body), (u_body), (body))))))
end)))
end
| _57_1024 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("No when clauses in the definition language")))
end)) branches)
in (FStar_List.split _152_844))
in (match (_57_1027) with
| (nms, branches) -> begin
(

let t1 = (match ((FStar_List.hd nms)) with
| (M (t1)) | (N (t1)) -> begin
t1
end)
in (

let has_m = (FStar_List.existsb (fun _57_6 -> (match (_57_6) with
| M (_57_1034) -> begin
true
end
| _57_1037 -> begin
false
end)) nms)
in (

let _57_1071 = (let _152_848 = (FStar_List.map2 (fun nm _57_1046 -> (match (_57_1046) with
| (pat, guard, (s_body, u_body, original_body)) -> begin
(match (((nm), (has_m))) with
| ((N (t2), false)) | ((M (t2), true)) -> begin
((nm), (((pat), (guard), (s_body))), (((pat), (guard), (u_body))))
end
| (N (t2), true) -> begin
(

let _57_1062 = (check env original_body (M (t2)))
in (match (_57_1062) with
| (_57_1059, s_body, u_body) -> begin
((M (t2)), (((pat), (guard), (s_body))), (((pat), (guard), (u_body))))
end))
end
| (M (_57_1064), false) -> begin
(FStar_All.failwith "impossible")
end)
end)) nms branches)
in (FStar_List.unzip3 _152_848))
in (match (_57_1071) with
| (nms, s_branches, u_branches) -> begin
if has_m then begin
(

let p_type = (mk_star_to_type mk env t1)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" None p_type)
in (

let s_branches = (FStar_List.map (fun _57_1077 -> (match (_57_1077) with
| (pat, guard, s_body) -> begin
(

let s_body = (let _152_855 = (let _152_854 = (let _152_853 = (let _152_852 = (let _152_851 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _152_850 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_851), (_152_850))))
in (_152_852)::[])
in ((s_body), (_152_853)))
in FStar_Syntax_Syntax.Tm_app (_152_854))
in (mk _152_855))
in ((pat), (guard), (s_body)))
end)) s_branches)
in (

let s_branches = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let s_e = (let _152_858 = (let _152_856 = (FStar_Syntax_Syntax.mk_binder p)
in (_152_856)::[])
in (let _152_857 = (mk (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches)))))
in (FStar_Syntax_Util.abs _152_858 _152_857 None)))
in (

let t1_star = (let _152_862 = (let _152_860 = (let _152_859 = (FStar_Syntax_Syntax.new_bv None p_type)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _152_859))
in (_152_860)::[])
in (let _152_861 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _152_862 _152_861)))
in (let _152_864 = (mk (FStar_Syntax_Syntax.Tm_ascribed (((s_e), (FStar_Util.Inl (t1_star)), (None)))))
in (let _152_863 = (mk (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches)))))
in ((M (t1)), (_152_864), (_152_863)))))))))))
end else begin
(

let s_branches = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let t1_star = t1
in (let _152_869 = (let _152_867 = (let _152_866 = (let _152_865 = (mk (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches)))))
in ((_152_865), (FStar_Util.Inl (t1_star)), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (_152_866))
in (mk _152_867))
in (let _152_868 = (mk (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches)))))
in ((N (t1)), (_152_869), (_152_868)))))))
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

let x_binders = (let _152_889 = (FStar_Syntax_Syntax.mk_binder x)
in (_152_889)::[])
in (

let _57_1099 = (FStar_Syntax_Subst.open_term x_binders e2)
in (match (_57_1099) with
| (x_binders, e2) -> begin
(match ((infer env e1)) with
| (N (t1), s_e1, u_e1) -> begin
(

let env = (

let _57_1105 = env
in (let _152_890 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_1107 = x
in {FStar_Syntax_Syntax.ppname = _57_1107.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1107.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _152_890; subst = _57_1105.subst; tc_const = _57_1105.tc_const}))
in (

let _57_1113 = (proceed env e2)
in (match (_57_1113) with
| (nm_rec, s_e2, u_e2) -> begin
(let _152_898 = (let _152_893 = (let _152_892 = (let _152_891 = (FStar_Syntax_Subst.close x_binders s_e2)
in ((((false), (((

let _57_1114 = binding
in {FStar_Syntax_Syntax.lbname = _57_1114.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_1114.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1114.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1114.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = s_e1}))::[]))), (_152_891)))
in FStar_Syntax_Syntax.Tm_let (_152_892))
in (mk _152_893))
in (let _152_897 = (let _152_896 = (let _152_895 = (let _152_894 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _57_1116 = binding
in {FStar_Syntax_Syntax.lbname = _57_1116.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_1116.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1116.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1116.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_152_894)))
in FStar_Syntax_Syntax.Tm_let (_152_895))
in (mk _152_896))
in ((nm_rec), (_152_898), (_152_897))))
end)))
end
| (M (t1), s_e1, u_e1) -> begin
(

let env = (

let _57_1123 = env
in (let _152_899 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_1125 = x
in {FStar_Syntax_Syntax.ppname = _57_1125.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1125.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _152_899; subst = _57_1123.subst; tc_const = _57_1123.tc_const}))
in (

let _57_1131 = (ensure_m env e2)
in (match (_57_1131) with
| (t2, s_e2, u_e2) -> begin
(

let p_type = (mk_star_to_type mk env t2)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" None p_type)
in (

let s_e2 = (let _152_905 = (let _152_904 = (let _152_903 = (let _152_902 = (let _152_901 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _152_900 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_901), (_152_900))))
in (_152_902)::[])
in ((s_e2), (_152_903)))
in FStar_Syntax_Syntax.Tm_app (_152_904))
in (mk _152_905))
in (

let s_e2 = (FStar_Syntax_Util.abs x_binders s_e2 None)
in (

let body = (let _152_910 = (let _152_909 = (let _152_908 = (let _152_907 = (let _152_906 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_e2), (_152_906)))
in (_152_907)::[])
in ((s_e1), (_152_908)))
in FStar_Syntax_Syntax.Tm_app (_152_909))
in (mk _152_910))
in (let _152_917 = (let _152_912 = (let _152_911 = (FStar_Syntax_Syntax.mk_binder p)
in (_152_911)::[])
in (FStar_Syntax_Util.abs _152_912 body None))
in (let _152_916 = (let _152_915 = (let _152_914 = (let _152_913 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _57_1137 = binding
in {FStar_Syntax_Syntax.lbname = _57_1137.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_1137.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1137.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1137.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_152_913)))
in FStar_Syntax_Syntax.Tm_let (_152_914))
in (mk _152_915))
in ((M (t2)), (_152_917), (_152_916)))))))))
end)))
end)
end)))))))
and check_n : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _152_920 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in N (_152_920))
in (match ((check env e mn)) with
| (N (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_1148 -> begin
(FStar_All.failwith "[check_n]: impossible")
end)))
and check_m : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _152_923 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in M (_152_923))
in (match ((check env e mn)) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_1158 -> begin
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

let _57_1169 = if (not ((is_C c))) then begin
(FStar_All.failwith "not a C")
end else begin
()
end
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos))
in (match ((let _152_932 = (FStar_Syntax_Subst.compress c)
in _152_932.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_1179 = (FStar_Syntax_Util.head_and_args wp)
in (match (_57_1179) with
| (wp_head, wp_args) -> begin
(

let _57_1180 = if ((not (((FStar_List.length wp_args) = (FStar_List.length args)))) || (not ((let _152_933 = (FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length wp_args) FStar_Range.dummyRange)
in (FStar_Syntax_Util.is_constructor wp_head _152_933))))) then begin
(FStar_All.failwith "mismatch")
end else begin
()
end
in (let _152_940 = (let _152_939 = (let _152_938 = (FStar_List.map2 (fun _57_1185 _57_1189 -> (match (((_57_1185), (_57_1189))) with
| ((arg, _57_1184), (wp_arg, _57_1188)) -> begin
(let _152_937 = (trans_F_ env arg wp_arg)
in (let _152_936 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_937), (_152_936))))
end)) args wp_args)
in ((head), (_152_938)))
in FStar_Syntax_Syntax.Tm_app (_152_939))
in (mk _152_940)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let binders = (FStar_Syntax_Util.name_binders binders)
in (

let _57_1197 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (_57_1197) with
| (binders_orig, comp) -> begin
(

let _57_1206 = (let _152_952 = (FStar_List.map (fun _57_1200 -> (match (_57_1200) with
| (bv, q) -> begin
(

let h = bv.FStar_Syntax_Syntax.sort
in if (is_C h) then begin
(

let w' = (let _152_942 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-w\'") None _152_942))
in (let _152_948 = (let _152_947 = (FStar_Syntax_Syntax.mk_binder w')
in (let _152_946 = (let _152_945 = (let _152_944 = (let _152_943 = (FStar_Syntax_Syntax.bv_to_name bv)
in (trans_F_ env h _152_943))
in (FStar_Syntax_Syntax.null_binder _152_944))
in (_152_945)::[])
in (_152_947)::_152_946))
in ((w'), (_152_948))))
end else begin
(

let x = (let _152_949 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-x") None _152_949))
in (let _152_951 = (let _152_950 = (FStar_Syntax_Syntax.mk_binder x)
in (_152_950)::[])
in ((x), (_152_951))))
end)
end)) binders_orig)
in (FStar_List.split _152_952))
in (match (_57_1206) with
| (bvs, binders) -> begin
(

let binders = (FStar_List.flatten binders)
in (

let comp = (let _152_954 = (let _152_953 = (FStar_Syntax_Syntax.binders_of_list bvs)
in (FStar_Syntax_Util.rename_binders binders_orig _152_953))
in (FStar_Syntax_Subst.subst_comp _152_954 comp))
in (

let app = (let _152_960 = (let _152_959 = (let _152_958 = (FStar_List.map (fun bv -> (let _152_957 = (FStar_Syntax_Syntax.bv_to_name bv)
in (let _152_956 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_957), (_152_956))))) bvs)
in ((wp), (_152_958)))
in FStar_Syntax_Syntax.Tm_app (_152_959))
in (mk _152_960))
in (

let comp = (let _152_962 = (type_of_comp comp)
in (let _152_961 = (is_monadic_comp comp)
in (trans_G env _152_962 _152_961 app)))
in (FStar_Syntax_Util.arrow binders comp)))))
end))
end)))
end
| _57_1213 -> begin
(FStar_All.failwith "impossible trans_F_")
end))))
and trans_G : env_  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env h is_monadic wp -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None h.FStar_Syntax_Syntax.pos))
in if is_monadic then begin
(let _152_973 = (let _152_972 = (star_type' env h)
in (let _152_971 = (let _152_970 = (let _152_969 = (FStar_Syntax_Syntax.as_implicit false)
in ((wp), (_152_969)))
in (_152_970)::[])
in {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_unknown)::[]; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _152_972; FStar_Syntax_Syntax.effect_args = _152_971; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp _152_973))
end else begin
(let _152_974 = (trans_F_ env h wp)
in (FStar_Syntax_Syntax.mk_Total _152_974))
end))


let n : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]))


let star_type : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _152_981 = (n env.env t)
in (star_type' env _152_981)))


let star_expr : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env t -> (let _152_986 = (n env.env t)
in (check_n env _152_986)))


let trans_F : env_  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> (let _152_994 = (n env.env c)
in (let _152_993 = (n env.env wp)
in (trans_F_ env _152_994 _152_993))))




