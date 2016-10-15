
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

let is_zero_order = (fun t -> (match ((let _152_305 = (FStar_Syntax_Subst.compress t)
in _152_305.FStar_Syntax_Syntax.n)) with
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

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (match ((let _152_327 = (FStar_Syntax_Subst.compress t)
in _152_327.FStar_Syntax_Syntax.n)) with
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

let body = (let _152_335 = (let _152_330 = (let _152_329 = (let _152_328 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _152_328))
in (_152_329)::[])
in (FStar_Syntax_Util.mk_app x _152_330))
in (let _152_334 = (let _152_333 = (let _152_332 = (let _152_331 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _152_331))
in (_152_332)::[])
in (FStar_Syntax_Util.mk_app y _152_333))
in (mk_rel b _152_335 _152_334)))
in (mk_forall a1 body)))
end else begin
(

let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (

let a2 = (FStar_Syntax_Syntax.gen_bv "a2" None a)
in (

let body = (let _152_347 = (let _152_337 = (FStar_Syntax_Syntax.bv_to_name a1)
in (let _152_336 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_rel a _152_337 _152_336)))
in (let _152_346 = (let _152_345 = (let _152_340 = (let _152_339 = (let _152_338 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _152_338))
in (_152_339)::[])
in (FStar_Syntax_Util.mk_app x _152_340))
in (let _152_344 = (let _152_343 = (let _152_342 = (let _152_341 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg _152_341))
in (_152_342)::[])
in (FStar_Syntax_Util.mk_app y _152_343))
in (mk_rel b _152_345 _152_344)))
in (FStar_Syntax_Util.mk_imp _152_347 _152_346)))
in (let _152_348 = (mk_forall a2 body)
in (mk_forall a1 _152_348)))))
end)
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::binders, comp) -> begin
(

let t = (

let _57_228 = t
in (let _152_352 = (let _152_351 = (let _152_350 = (let _152_349 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _152_349))
in (((binder)::[]), (_152_350)))
in FStar_Syntax_Syntax.Tm_arrow (_152_351))
in {FStar_Syntax_Syntax.n = _152_352; FStar_Syntax_Syntax.tk = _57_228.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_228.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_228.FStar_Syntax_Syntax.vars}))
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

let body = (let _152_354 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (let _152_353 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_rel FStar_Syntax_Util.mk_imp wp_a _152_354 _152_353)))
in (let _152_356 = (let _152_355 = (binders_of_list ((((a), (false)))::(((wp1), (false)))::(((wp2), (false)))::[]))
in (FStar_List.append binders _152_355))
in (FStar_Syntax_Util.abs _152_356 body ret_tot_type)))))
in (

let stronger = (let _152_357 = (mk_lid "stronger")
in (register env _152_357 stronger))
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

let eq = (let _152_358 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst post))
in (mk_rel FStar_Syntax_Util.mk_iff k.FStar_Syntax_Syntax.sort k_tm _152_358))
in (match ((FStar_Syntax_Util.destruct_typ_as_formula eq)) with
| Some (FStar_Syntax_Util.QAll (binders, [], body)) -> begin
(

let k_app = (let _152_359 = (args_of_binders binders)
in (FStar_Syntax_Util.mk_app k_tm _152_359))
in (

let guard_free = (let _152_360 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.guard_free FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _152_360))
in (

let pat = (let _152_362 = (let _152_361 = (FStar_Syntax_Syntax.as_arg k_app)
in (_152_361)::[])
in (FStar_Syntax_Util.mk_app guard_free _152_362))
in (

let pattern_guarded_body = (let _152_368 = (let _152_367 = (let _152_366 = (let _152_365 = (let _152_364 = (let _152_363 = (FStar_Syntax_Syntax.as_arg pat)
in (_152_363)::[])
in (_152_364)::[])
in FStar_Syntax_Syntax.Meta_pattern (_152_365))
in ((body), (_152_366)))
in FStar_Syntax_Syntax.Tm_meta (_152_367))
in (mk _152_368))
in (FStar_Syntax_Util.close_forall binders pattern_guarded_body)))))
end
| _57_260 -> begin
(FStar_All.failwith "Impossible: Expected the equivalence to be a quantified formula")
end)))
in (

let body = (let _152_377 = (let _152_376 = (let _152_375 = (let _152_374 = (FStar_Syntax_Syntax.bv_to_name wp)
in (let _152_373 = (let _152_372 = (args_of_binders wp_args)
in (let _152_371 = (let _152_370 = (let _152_369 = (FStar_Syntax_Syntax.bv_to_name k)
in (FStar_Syntax_Syntax.as_arg _152_369))
in (_152_370)::[])
in (FStar_List.append _152_372 _152_371)))
in (FStar_Syntax_Util.mk_app _152_374 _152_373)))
in (FStar_Syntax_Util.mk_imp equiv _152_375))
in (FStar_Syntax_Util.mk_forall k _152_376))
in (FStar_Syntax_Util.abs gamma _152_377 ret_gtot_type))
in (let _152_379 = (let _152_378 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders _152_378))
in (FStar_Syntax_Util.abs _152_379 body ret_gtot_type)))))
end)))
in (

let wp_ite = (let _152_380 = (mk_lid "wp_ite")
in (register env _152_380 wp_ite))
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

let body = (let _152_385 = (let _152_384 = (FStar_All.pipe_left FStar_Syntax_Syntax.bv_to_name (Prims.fst post))
in (let _152_383 = (let _152_382 = (let _152_381 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _152_381))
in (_152_382)::[])
in (FStar_Syntax_Util.mk_app _152_384 _152_383)))
in (FStar_Syntax_Util.mk_forall x _152_385))
in (let _152_388 = (let _152_387 = (let _152_386 = (FStar_Syntax_Syntax.binders_of_list ((a)::[]))
in (FStar_List.append _152_386 gamma))
in (FStar_List.append binders _152_387))
in (FStar_Syntax_Util.abs _152_388 body ret_gtot_type))))
end)))
in (

let null_wp = (let _152_389 = (mk_lid "null_wp")
in (register env _152_389 null_wp))
in (

let null_wp = (mk_generic_app null_wp)
in (

let wp_trivial = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let body = (let _152_399 = (let _152_398 = (let _152_397 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _152_396 = (let _152_395 = (let _152_392 = (let _152_391 = (let _152_390 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg _152_390))
in (_152_391)::[])
in (FStar_Syntax_Util.mk_app null_wp _152_392))
in (let _152_394 = (let _152_393 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_152_393)::[])
in (_152_395)::_152_394))
in (_152_397)::_152_396))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _152_398))
in (FStar_Syntax_Util.mk_app stronger _152_399))
in (let _152_401 = (let _152_400 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders _152_400))
in (FStar_Syntax_Util.abs _152_401 body ret_tot_type))))
in (

let wp_trivial = (let _152_402 = (mk_lid "wp_trivial")
in (register env _152_402 wp_trivial))
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
in (let _152_422 = (let _152_404 = (FStar_ST.read sigelts)
in (FStar_List.rev _152_404))
in (let _152_421 = (

let _57_283 = ed
in (let _152_420 = (let _152_405 = (c wp_if_then_else)
in (([]), (_152_405)))
in (let _152_419 = (let _152_406 = (c wp_ite)
in (([]), (_152_406)))
in (let _152_418 = (let _152_407 = (c stronger)
in (([]), (_152_407)))
in (let _152_417 = (let _152_408 = (c wp_close)
in (([]), (_152_408)))
in (let _152_416 = (let _152_409 = (c wp_assert)
in (([]), (_152_409)))
in (let _152_415 = (let _152_410 = (c wp_assume)
in (([]), (_152_410)))
in (let _152_414 = (let _152_411 = (c null_wp)
in (([]), (_152_411)))
in (let _152_413 = (let _152_412 = (c wp_trivial)
in (([]), (_152_412)))
in {FStar_Syntax_Syntax.qualifiers = _57_283.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_283.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_283.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_283.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_283.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _57_283.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _57_283.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _152_420; FStar_Syntax_Syntax.ite_wp = _152_419; FStar_Syntax_Syntax.stronger = _152_418; FStar_Syntax_Syntax.close_wp = _152_417; FStar_Syntax_Syntax.assert_p = _152_416; FStar_Syntax_Syntax.assume_p = _152_415; FStar_Syntax_Syntax.null_wp = _152_414; FStar_Syntax_Syntax.trivial = _152_413; FStar_Syntax_Syntax.repr = _57_283.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _57_283.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _57_283.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _57_283.FStar_Syntax_Syntax.actions})))))))))
in ((_152_422), (_152_421)))))))))))))))))))))))))))))))))))))))))))))))
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
| FStar_Syntax_Syntax.Comp (c) -> begin
(let _152_479 = (let _152_478 = (FStar_Ident.string_of_lid c.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format1 "[nm_of_comp]: impossible (%s)" _152_478))
in (FStar_All.failwith _152_479))
end
| FStar_Syntax_Syntax.GTotal (_57_308) -> begin
(FStar_All.failwith "[nm_of_comp]: impossible (GTot)")
end))


let string_of_nm : nm  ->  Prims.string = (fun _57_2 -> (match (_57_2) with
| N (t) -> begin
(let _152_482 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "N[%s]" _152_482))
end
| M (t) -> begin
(let _152_483 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "M[%s]" _152_483))
end))


let is_monadic_arrow : FStar_Syntax_Syntax.term'  ->  nm = (fun n -> (match (n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_317, {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_323; FStar_Syntax_Syntax.pos = _57_321; FStar_Syntax_Syntax.vars = _57_319}) -> begin
(nm_of_comp n)
end
| _57_329 -> begin
(FStar_All.failwith "unexpected_argument: [is_monadic_arrow]")
end))


let is_monadic_comp = (fun c -> (match ((nm_of_comp c.FStar_Syntax_Syntax.n)) with
| M (_57_332) -> begin
true
end
| N (_57_335) -> begin
false
end))


let rec mk_star_to_type : (FStar_Syntax_Syntax.term'  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun mk env a -> (let _152_507 = (let _152_506 = (let _152_505 = (let _152_503 = (let _152_502 = (let _152_500 = (star_type' env a)
in (FStar_Syntax_Syntax.null_bv _152_500))
in (let _152_501 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_502), (_152_501))))
in (_152_503)::[])
in (let _152_504 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_152_505), (_152_504))))
in FStar_Syntax_Syntax.Tm_arrow (_152_506))
in (mk _152_507)))
and star_type' : env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None t.FStar_Syntax_Syntax.pos))
in (

let mk_star_to_type = (mk_star_to_type mk)
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _57_348) -> begin
(

let binders = (FStar_List.map (fun _57_353 -> (match (_57_353) with
| (bv, aqual) -> begin
(let _152_516 = (

let _57_354 = bv
in (let _152_515 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_354.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_354.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _152_515}))
in ((_152_516), (aqual)))
end)) binders)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_358, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (hn, _57_367); FStar_Syntax_Syntax.tk = _57_364; FStar_Syntax_Syntax.pos = _57_362; FStar_Syntax_Syntax.vars = _57_360}) -> begin
(let _152_520 = (let _152_519 = (let _152_518 = (let _152_517 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_GTotal _152_517))
in ((binders), (_152_518)))
in FStar_Syntax_Syntax.Tm_arrow (_152_519))
in (mk _152_520))
end
| _57_374 -> begin
(match ((is_monadic_arrow t.FStar_Syntax_Syntax.n)) with
| N (hn) -> begin
(let _152_524 = (let _152_523 = (let _152_522 = (let _152_521 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_Total _152_521))
in ((binders), (_152_522)))
in FStar_Syntax_Syntax.Tm_arrow (_152_523))
in (mk _152_524))
end
| M (a) -> begin
(let _152_533 = (let _152_532 = (let _152_531 = (let _152_529 = (let _152_528 = (let _152_527 = (let _152_525 = (mk_star_to_type env a)
in (FStar_Syntax_Syntax.null_bv _152_525))
in (let _152_526 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_527), (_152_526))))
in (_152_528)::[])
in (FStar_List.append binders _152_529))
in (let _152_530 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_152_531), (_152_530))))
in FStar_Syntax_Syntax.Tm_arrow (_152_532))
in (mk _152_533))
end)
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let rec is_valid_application = (fun head -> (match ((let _152_536 = (FStar_Syntax_Subst.compress head)
in _152_536.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.option_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.either_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.eq2_lid)) || (let _152_537 = (FStar_Syntax_Subst.compress head)
in (FStar_Syntax_Util.is_tuple_constructor _152_537))) -> begin
true
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uinst (t, _57_395) -> begin
(is_valid_application t)
end
| _57_399 -> begin
false
end))
in if (is_valid_application head) then begin
(let _152_542 = (let _152_541 = (let _152_540 = (FStar_List.map (fun _57_402 -> (match (_57_402) with
| (t, qual) -> begin
(let _152_539 = (star_type' env t)
in ((_152_539), (qual)))
end)) args)
in ((head), (_152_540)))
in FStar_Syntax_Syntax.Tm_app (_152_541))
in (mk _152_542))
end else begin
(let _152_545 = (let _152_544 = (let _152_543 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)" _152_543))
in FStar_Syntax_Syntax.Err (_152_544))
in (Prims.raise _152_545))
end)
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_abs (binders, repr, something) -> begin
(

let _57_422 = (FStar_Syntax_Subst.open_term binders repr)
in (match (_57_422) with
| (binders, repr) -> begin
(

let env = (

let _57_423 = env
in (let _152_546 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _152_546; subst = _57_423.subst; tc_const = _57_423.tc_const}))
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

let _57_438 = x
in {FStar_Syntax_Syntax.ppname = _57_438.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_438.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (t))))))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(let _152_549 = (let _152_548 = (let _152_547 = (star_type' env t)
in ((_152_547), (m)))
in FStar_Syntax_Syntax.Tm_meta (_152_548))
in (mk _152_549))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), something) -> begin
(let _152_554 = (let _152_553 = (let _152_552 = (star_type' env e)
in (let _152_551 = (let _152_550 = (star_type' env t)
in FStar_Util.Inl (_152_550))
in ((_152_552), (_152_551), (something))))
in FStar_Syntax_Syntax.Tm_ascribed (_152_553))
in (mk _152_554))
end
| FStar_Syntax_Syntax.Tm_ascribed (_57_451) -> begin
(let _152_557 = (let _152_556 = (let _152_555 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_ascribed is outside of the definition language: %s" _152_555))
in FStar_Syntax_Syntax.Err (_152_556))
in (Prims.raise _152_557))
end
| FStar_Syntax_Syntax.Tm_refine (_57_454) -> begin
(let _152_560 = (let _152_559 = (let _152_558 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_refine is outside of the definition language: %s" _152_558))
in FStar_Syntax_Syntax.Err (_152_559))
in (Prims.raise _152_560))
end
| FStar_Syntax_Syntax.Tm_uinst (_57_457) -> begin
(let _152_563 = (let _152_562 = (let _152_561 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_uinst is outside of the definition language: %s" _152_561))
in FStar_Syntax_Syntax.Err (_152_562))
in (Prims.raise _152_563))
end
| FStar_Syntax_Syntax.Tm_constant (_57_460) -> begin
(let _152_566 = (let _152_565 = (let _152_564 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_constant is outside of the definition language: %s" _152_564))
in FStar_Syntax_Syntax.Err (_152_565))
in (Prims.raise _152_566))
end
| FStar_Syntax_Syntax.Tm_match (_57_463) -> begin
(let _152_569 = (let _152_568 = (let _152_567 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_match is outside of the definition language: %s" _152_567))
in FStar_Syntax_Syntax.Err (_152_568))
in (Prims.raise _152_569))
end
| FStar_Syntax_Syntax.Tm_let (_57_466) -> begin
(let _152_572 = (let _152_571 = (let _152_570 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_let is outside of the definition language: %s" _152_570))
in FStar_Syntax_Syntax.Err (_152_571))
in (Prims.raise _152_572))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_469) -> begin
(let _152_575 = (let _152_574 = (let _152_573 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_uvar is outside of the definition language: %s" _152_573))
in FStar_Syntax_Syntax.Err (_152_574))
in (Prims.raise _152_575))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _152_578 = (let _152_577 = (let _152_576 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_unknown is outside of the definition language: %s" _152_576))
in FStar_Syntax_Syntax.Err (_152_577))
in (Prims.raise _152_578))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_473) -> begin
(FStar_All.failwith "impossible")
end)))))


let is_monadic : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  Prims.bool = (fun _57_3 -> (match (_57_3) with
| None -> begin
(FStar_All.failwith "un-annotated lambda?!")
end
| (Some (FStar_Util.Inl ({FStar_Syntax_Syntax.eff_name = lid; FStar_Syntax_Syntax.res_typ = _; FStar_Syntax_Syntax.cflags = _; FStar_Syntax_Syntax.comp = _}))) | (Some (FStar_Util.Inr (lid))) -> begin
(FStar_Ident.lid_equals lid FStar_Syntax_Const.monadic_lid)
end))


let rec is_C : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match ((let _152_586 = (FStar_Syntax_Subst.compress t)
in _152_586.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) when (FStar_Syntax_Util.is_tuple_constructor head) -> begin
(

let r = (let _152_588 = (let _152_587 = (FStar_List.hd args)
in (Prims.fst _152_587))
in (is_C _152_588))
in if r then begin
(

let _57_499 = if (not ((FStar_List.for_all (fun _57_498 -> (match (_57_498) with
| (h, _57_497) -> begin
(is_C h)
end)) args))) then begin
(FStar_All.failwith "not a C (A * C)")
end else begin
()
end
in true)
end else begin
(

let _57_505 = if (not ((FStar_List.for_all (fun _57_504 -> (match (_57_504) with
| (h, _57_503) -> begin
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

let _57_513 = if (is_C t) then begin
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
| _57_533 -> begin
false
end))


let mk_return : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let p_type = (mk_star_to_type mk env t)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'" None p_type)
in (

let body = (let _152_604 = (let _152_603 = (let _152_602 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _152_601 = (let _152_600 = (let _152_599 = (FStar_Syntax_Syntax.as_implicit false)
in ((e), (_152_599)))
in (_152_600)::[])
in ((_152_602), (_152_601))))
in FStar_Syntax_Syntax.Tm_app (_152_603))
in (mk _152_604))
in (let _152_606 = (let _152_605 = (FStar_Syntax_Syntax.mk_binder p)
in (_152_605)::[])
in (FStar_Syntax_Util.abs _152_606 body None)))))))


let is_unknown : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun _57_4 -> (match (_57_4) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| _57_545 -> begin
false
end))


let rec check : env  ->  FStar_Syntax_Syntax.term  ->  nm  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e context_nm -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let return_if = (fun _57_555 -> (match (_57_555) with
| (rec_nm, s_e, u_e) -> begin
(

let check = (fun t1 t2 -> if ((not ((is_unknown t2.FStar_Syntax_Syntax.n))) && (not ((let _152_660 = (FStar_TypeChecker_Rel.teq env.env t1 t2)
in (FStar_TypeChecker_Rel.is_trivial _152_660))))) then begin
(let _152_665 = (let _152_664 = (let _152_663 = (FStar_Syntax_Print.term_to_string e)
in (let _152_662 = (FStar_Syntax_Print.term_to_string t1)
in (let _152_661 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check]: the expression [%s] has type [%s] but should have type [%s]" _152_663 _152_662 _152_661))))
in FStar_Syntax_Syntax.Err (_152_664))
in (Prims.raise _152_665))
end else begin
()
end)
in (match (((rec_nm), (context_nm))) with
| ((N (t1), N (t2))) | ((M (t1), M (t2))) -> begin
(

let _57_567 = (check t1 t2)
in ((rec_nm), (s_e), (u_e)))
end
| (N (t1), M (t2)) -> begin
(

let _57_574 = (check t1 t2)
in (let _152_666 = (mk_return env t1 s_e)
in ((M (t1)), (_152_666), (u_e))))
end
| (M (t1), N (t2)) -> begin
(let _152_671 = (let _152_670 = (let _152_669 = (FStar_Syntax_Print.term_to_string e)
in (let _152_668 = (FStar_Syntax_Print.term_to_string t1)
in (let _152_667 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]" _152_669 _152_668 _152_667))))
in FStar_Syntax_Syntax.Err (_152_670))
in (Prims.raise _152_671))
end))
end))
in (

let ensure_m = (fun env e2 -> (

let strip_m = (fun _57_5 -> (match (_57_5) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_591 -> begin
(FStar_All.failwith "impossible")
end))
in (match (context_nm) with
| N (t) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren\'t"), (e2.FStar_Syntax_Syntax.pos)))))
end
| M (_57_596) -> begin
(let _152_678 = (check env e2 context_nm)
in (strip_m _152_678))
end)))
in (match ((let _152_679 = (FStar_Syntax_Subst.compress e)
in _152_679.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
(let _152_680 = (infer env e)
in (return_if _152_680))
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
| FStar_Syntax_Syntax.Tm_let (_57_647) -> begin
(let _152_688 = (let _152_687 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_let %s" _152_687))
in (FStar_All.failwith _152_688))
end
| FStar_Syntax_Syntax.Tm_type (_57_650) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_653) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_57_656) -> begin
(let _152_690 = (let _152_689 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_refine %s" _152_689))
in (FStar_All.failwith _152_690))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_659) -> begin
(let _152_692 = (let _152_691 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_uvar %s" _152_691))
in (FStar_All.failwith _152_692))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_662) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _152_697 = (let _152_696 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_unknown %s" _152_696))
in (FStar_All.failwith _152_697))
end)))))
and infer : env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.env)
in (match ((let _152_703 = (FStar_Syntax_Subst.compress e)
in _152_703.FStar_Syntax_Syntax.n)) with
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

let _57_682 = env
in (let _152_704 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _152_704; subst = _57_682.subst; tc_const = _57_682.tc_const}))
in (

let s_binders = (FStar_List.map (fun _57_687 -> (match (_57_687) with
| (bv, qual) -> begin
(

let sort = (star_type' env bv.FStar_Syntax_Syntax.sort)
in (((

let _57_689 = bv
in {FStar_Syntax_Syntax.ppname = _57_689.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_689.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (qual)))
end)) binders)
in (

let _57_711 = (FStar_List.fold_left (fun _57_694 _57_697 -> (match (((_57_694), (_57_697))) with
| ((env, acc), (bv, qual)) -> begin
(

let c = bv.FStar_Syntax_Syntax.sort
in if (is_C c) then begin
(

let xw = (let _152_708 = (star_type' env c)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "^w") None _152_708))
in (

let x = (

let _57_700 = bv
in (let _152_710 = (let _152_709 = (FStar_Syntax_Syntax.bv_to_name xw)
in (trans_F_ env c _152_709))
in {FStar_Syntax_Syntax.ppname = _57_700.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_700.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _152_710}))
in (

let env = (

let _57_703 = env
in (let _152_714 = (let _152_713 = (let _152_712 = (let _152_711 = (FStar_Syntax_Syntax.bv_to_name xw)
in ((bv), (_152_711)))
in FStar_Syntax_Syntax.NT (_152_712))
in (_152_713)::env.subst)
in {env = _57_703.env; subst = _152_714; tc_const = _57_703.tc_const}))
in (let _152_718 = (let _152_717 = (FStar_Syntax_Syntax.mk_binder x)
in (let _152_716 = (let _152_715 = (FStar_Syntax_Syntax.mk_binder xw)
in (_152_715)::acc)
in (_152_717)::_152_716))
in ((env), (_152_718))))))
end else begin
(

let x = (

let _57_706 = bv
in (let _152_719 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_706.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_706.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _152_719}))
in (let _152_721 = (let _152_720 = (FStar_Syntax_Syntax.mk_binder x)
in (_152_720)::acc)
in ((env), (_152_721))))
end)
end)) ((env), ([])) binders)
in (match (_57_711) with
| (env, u_binders) -> begin
(

let u_binders = (FStar_List.rev u_binders)
in (

let _57_721 = (

let check_what = if (is_monadic what) then begin
check_m
end else begin
check_n
end
in (

let _57_717 = (check_what env body)
in (match (_57_717) with
| (t, s_body, u_body) -> begin
(let _152_727 = (let _152_726 = if (is_monadic what) then begin
M (t)
end else begin
N (t)
end
in (comp_of_nm _152_726))
in ((_152_727), (s_body), (u_body)))
end)))
in (match (_57_721) with
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
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = {FStar_Syntax_Syntax.v = lid; FStar_Syntax_Syntax.ty = _57_736; FStar_Syntax_Syntax.p = _57_734}; FStar_Syntax_Syntax.fv_delta = _57_732; FStar_Syntax_Syntax.fv_qual = _57_730}) -> begin
(

let _57_744 = (FStar_TypeChecker_Env.lookup_lid env.env lid)
in (match (_57_744) with
| (_57_742, t) -> begin
(

let txt = (FStar_Ident.text_of_lid lid)
in (let _152_729 = (let _152_728 = (normalize t)
in N (_152_728))
in ((_152_729), (e), (e))))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_753 = (check_n env head)
in (match (_57_753) with
| (t_head, s_head, u_head) -> begin
(

let is_arrow = (fun t -> (match ((let _152_732 = (FStar_Syntax_Subst.compress t)
in _152_732.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_757) -> begin
true
end
| _57_760 -> begin
false
end))
in (

let rec flatten = (fun t -> (match ((let _152_735 = (FStar_Syntax_Subst.compress t)
in _152_735.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (t, _57_772); FStar_Syntax_Syntax.tk = _57_769; FStar_Syntax_Syntax.pos = _57_767; FStar_Syntax_Syntax.vars = _57_765}) when (is_arrow t) -> begin
(

let _57_780 = (flatten t)
in (match (_57_780) with
| (binders', comp) -> begin
(((FStar_List.append binders binders')), (comp))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
((binders), (comp))
end
| _57_786 -> begin
(let _152_738 = (let _152_737 = (let _152_736 = (FStar_Syntax_Print.term_to_string t_head)
in (FStar_Util.format1 "%s: not a function type" _152_736))
in FStar_Syntax_Syntax.Err (_152_737))
in (Prims.raise _152_738))
end))
in (

let _57_789 = (flatten t_head)
in (match (_57_789) with
| (binders, comp) -> begin
(

let n = (FStar_List.length binders)
in (

let n' = (FStar_List.length args)
in (

let _57_792 = if ((FStar_List.length binders) < (FStar_List.length args)) then begin
(let _152_743 = (let _152_742 = (let _152_741 = (FStar_Util.string_of_int n)
in (let _152_740 = (FStar_Util.string_of_int (n' - n))
in (let _152_739 = (FStar_Util.string_of_int n)
in (FStar_Util.format3 "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments." _152_741 _152_740 _152_739))))
in FStar_Syntax_Syntax.Err (_152_742))
in (Prims.raise _152_743))
end else begin
()
end
in (

let _57_796 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (_57_796) with
| (binders, comp) -> begin
(

let rec final_type = (fun subst _57_801 args -> (match (_57_801) with
| (binders, comp) -> begin
(match (((binders), (args))) with
| ([], []) -> begin
(let _152_751 = (let _152_750 = (FStar_Syntax_Subst.subst_comp subst comp)
in _152_750.FStar_Syntax_Syntax.n)
in (nm_of_comp _152_751))
end
| (binders, []) -> begin
(match ((let _152_754 = (let _152_753 = (let _152_752 = (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))))
in (FStar_Syntax_Subst.subst subst _152_752))
in (FStar_Syntax_Subst.compress _152_753))
in _152_754.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(let _152_758 = (let _152_757 = (let _152_756 = (let _152_755 = (FStar_Syntax_Subst.close_comp binders comp)
in ((binders), (_152_755)))
in FStar_Syntax_Syntax.Tm_arrow (_152_756))
in (mk _152_757))
in N (_152_758))
end
| _57_814 -> begin
(FStar_All.failwith "wat?")
end)
end
| ([], (_57_819)::_57_817) -> begin
(FStar_All.failwith "just checked that?!")
end
| (((bv, _57_825))::binders, ((arg, _57_831))::args) -> begin
(final_type ((FStar_Syntax_Syntax.NT (((bv), (arg))))::subst) ((binders), (comp)) args)
end)
end))
in (

let final_type = (final_type [] ((binders), (comp)) args)
in (

let _57_839 = (FStar_List.splitAt n' binders)
in (match (_57_839) with
| (binders, _57_838) -> begin
(

let _57_860 = (let _152_773 = (FStar_List.map2 (fun _57_843 _57_846 -> (match (((_57_843), (_57_846))) with
| ((bv, _57_842), (arg, q)) -> begin
(match ((let _152_761 = (FStar_Syntax_Subst.compress bv.FStar_Syntax_Syntax.sort)
in _152_761.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_848) -> begin
(

let arg = ((arg), (q))
in ((arg), ((arg)::[])))
end
| _57_852 -> begin
(

let _57_857 = (check_n env arg)
in (match (_57_857) with
| (_57_854, s_arg, u_arg) -> begin
(let _152_772 = (let _152_762 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_arg), (_152_762)))
in (let _152_771 = if (is_C bv.FStar_Syntax_Syntax.sort) then begin
(let _152_768 = (let _152_764 = (FStar_Syntax_Subst.subst env.subst s_arg)
in (let _152_763 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_764), (_152_763))))
in (let _152_767 = (let _152_766 = (let _152_765 = (FStar_Syntax_Syntax.as_implicit false)
in ((u_arg), (_152_765)))
in (_152_766)::[])
in (_152_768)::_152_767))
end else begin
(let _152_770 = (let _152_769 = (FStar_Syntax_Syntax.as_implicit false)
in ((u_arg), (_152_769)))
in (_152_770)::[])
end
in ((_152_772), (_152_771))))
end))
end)
end)) binders args)
in (FStar_List.split _152_773))
in (match (_57_860) with
| (s_args, u_args) -> begin
(

let u_args = (FStar_List.flatten u_args)
in (let _152_775 = (mk (FStar_Syntax_Syntax.Tm_app (((s_head), (s_args)))))
in (let _152_774 = (mk (FStar_Syntax_Syntax.Tm_app (((u_head), (u_args)))))
in ((final_type), (_152_775), (_152_774)))))
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
(let _152_777 = (let _152_776 = (env.tc_const c)
in N (_152_776))
in ((_152_777), (e), (e)))
end
| FStar_Syntax_Syntax.Tm_let (_57_891) -> begin
(let _152_779 = (let _152_778 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_let %s" _152_778))
in (FStar_All.failwith _152_779))
end
| FStar_Syntax_Syntax.Tm_type (_57_894) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_897) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_57_900) -> begin
(let _152_781 = (let _152_780 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_refine %s" _152_780))
in (FStar_All.failwith _152_781))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_903) -> begin
(let _152_783 = (let _152_782 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_uvar %s" _152_782))
in (FStar_All.failwith _152_783))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_906) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _152_788 = (let _152_787 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_unknown %s" _152_787))
in (FStar_All.failwith _152_788))
end))))
and mk_match : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e0 branches f -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e0.FStar_Syntax_Syntax.pos))
in (

let _57_919 = (check_n env e0)
in (match (_57_919) with
| (_57_916, s_e0, u_e0) -> begin
(

let _57_936 = (let _152_804 = (FStar_List.map (fun b -> (match ((FStar_Syntax_Subst.open_branch b)) with
| (pat, None, body) -> begin
(

let env = (

let _57_925 = env
in (let _152_803 = (let _152_802 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env.env _152_802))
in {env = _152_803; subst = _57_925.subst; tc_const = _57_925.tc_const}))
in (

let _57_931 = (f env body)
in (match (_57_931) with
| (nm, s_body, u_body) -> begin
((nm), (((pat), (None), (((s_body), (u_body), (body))))))
end)))
end
| _57_933 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("No when clauses in the definition language")))
end)) branches)
in (FStar_List.split _152_804))
in (match (_57_936) with
| (nms, branches) -> begin
(

let t1 = (match ((FStar_List.hd nms)) with
| (M (t1)) | (N (t1)) -> begin
t1
end)
in (

let has_m = (FStar_List.existsb (fun _57_6 -> (match (_57_6) with
| M (_57_943) -> begin
true
end
| _57_946 -> begin
false
end)) nms)
in (

let _57_980 = (let _152_808 = (FStar_List.map2 (fun nm _57_955 -> (match (_57_955) with
| (pat, guard, (s_body, u_body, original_body)) -> begin
(match (((nm), (has_m))) with
| ((N (t2), false)) | ((M (t2), true)) -> begin
((nm), (((pat), (guard), (s_body))), (((pat), (guard), (u_body))))
end
| (N (t2), true) -> begin
(

let _57_971 = (check env original_body (M (t2)))
in (match (_57_971) with
| (_57_968, s_body, u_body) -> begin
((M (t2)), (((pat), (guard), (s_body))), (((pat), (guard), (u_body))))
end))
end
| (M (_57_973), false) -> begin
(FStar_All.failwith "impossible")
end)
end)) nms branches)
in (FStar_List.unzip3 _152_808))
in (match (_57_980) with
| (nms, s_branches, u_branches) -> begin
(

let s_branches = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let t1_star = if has_m then begin
(let _152_813 = (let _152_811 = (let _152_810 = (let _152_809 = (mk_star_to_type mk env t1)
in (FStar_Syntax_Syntax.new_bv None _152_809))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _152_810))
in (_152_811)::[])
in (let _152_812 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _152_813 _152_812)))
end else begin
t1
end
in (let _152_818 = (let _152_816 = (let _152_815 = (let _152_814 = (mk (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches)))))
in ((_152_814), (FStar_Util.Inl (t1_star)), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (_152_815))
in (mk _152_816))
in (let _152_817 = (mk (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches)))))
in ((if has_m then begin
M (t1)
end else begin
N (t1)
end), (_152_818), (_152_817)))))))
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

let x_binders = (let _152_838 = (FStar_Syntax_Syntax.mk_binder x)
in (_152_838)::[])
in (

let _57_996 = (FStar_Syntax_Subst.open_term x_binders e2)
in (match (_57_996) with
| (x_binders, e2) -> begin
(match ((infer env e1)) with
| (N (t1), s_e1, u_e1) -> begin
(

let env = (

let _57_1002 = env
in (let _152_839 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_1004 = x
in {FStar_Syntax_Syntax.ppname = _57_1004.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1004.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _152_839; subst = _57_1002.subst; tc_const = _57_1002.tc_const}))
in (

let _57_1010 = (proceed env e2)
in (match (_57_1010) with
| (nm_rec, s_e2, u_e2) -> begin
(let _152_847 = (let _152_842 = (let _152_841 = (let _152_840 = (FStar_Syntax_Subst.close x_binders s_e2)
in ((((false), (((

let _57_1011 = binding
in {FStar_Syntax_Syntax.lbname = _57_1011.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_1011.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1011.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1011.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = s_e1}))::[]))), (_152_840)))
in FStar_Syntax_Syntax.Tm_let (_152_841))
in (mk _152_842))
in (let _152_846 = (let _152_845 = (let _152_844 = (let _152_843 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _57_1013 = binding
in {FStar_Syntax_Syntax.lbname = _57_1013.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_1013.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1013.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1013.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_152_843)))
in FStar_Syntax_Syntax.Tm_let (_152_844))
in (mk _152_845))
in ((nm_rec), (_152_847), (_152_846))))
end)))
end
| (M (t1), s_e1, u_e1) -> begin
(

let env = (

let _57_1020 = env
in (let _152_848 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_1022 = x
in {FStar_Syntax_Syntax.ppname = _57_1022.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1022.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _152_848; subst = _57_1020.subst; tc_const = _57_1020.tc_const}))
in (

let _57_1028 = (ensure_m env e2)
in (match (_57_1028) with
| (t2, s_e2, u_e2) -> begin
(

let p_type = (mk_star_to_type mk env t2)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" None p_type)
in (

let s_e2 = (let _152_854 = (let _152_853 = (let _152_852 = (let _152_851 = (let _152_850 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _152_849 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_850), (_152_849))))
in (_152_851)::[])
in ((s_e2), (_152_852)))
in FStar_Syntax_Syntax.Tm_app (_152_853))
in (mk _152_854))
in (

let s_e2 = (FStar_Syntax_Util.abs x_binders s_e2 None)
in (

let body = (let _152_859 = (let _152_858 = (let _152_857 = (let _152_856 = (let _152_855 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_e2), (_152_855)))
in (_152_856)::[])
in ((s_e1), (_152_857)))
in FStar_Syntax_Syntax.Tm_app (_152_858))
in (mk _152_859))
in (let _152_866 = (let _152_861 = (let _152_860 = (FStar_Syntax_Syntax.mk_binder p)
in (_152_860)::[])
in (FStar_Syntax_Util.abs _152_861 body None))
in (let _152_865 = (let _152_864 = (let _152_863 = (let _152_862 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _57_1034 = binding
in {FStar_Syntax_Syntax.lbname = _57_1034.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_1034.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1034.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1034.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_152_862)))
in FStar_Syntax_Syntax.Tm_let (_152_863))
in (mk _152_864))
in ((M (t2)), (_152_866), (_152_865)))))))))
end)))
end)
end)))))))
and check_n : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _152_869 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in N (_152_869))
in (match ((check env e mn)) with
| (N (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_1045 -> begin
(FStar_All.failwith "[check_n]: impossible")
end)))
and check_m : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _152_872 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in M (_152_872))
in (match ((check env e mn)) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_1055 -> begin
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

let _57_1066 = if (not ((is_C c))) then begin
(FStar_All.failwith "not a C")
end else begin
()
end
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos))
in (match ((let _152_881 = (FStar_Syntax_Subst.compress c)
in _152_881.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_1076 = (FStar_Syntax_Util.head_and_args wp)
in (match (_57_1076) with
| (wp_head, wp_args) -> begin
(

let _57_1077 = if ((not (((FStar_List.length wp_args) = (FStar_List.length args)))) || (not ((let _152_882 = (FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length wp_args) FStar_Range.dummyRange)
in (FStar_Syntax_Util.is_constructor wp_head _152_882))))) then begin
(FStar_All.failwith "mismatch")
end else begin
()
end
in (let _152_889 = (let _152_888 = (let _152_887 = (FStar_List.map2 (fun _57_1082 _57_1086 -> (match (((_57_1082), (_57_1086))) with
| ((arg, _57_1081), (wp_arg, _57_1085)) -> begin
(let _152_886 = (trans_F_ env arg wp_arg)
in (let _152_885 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_886), (_152_885))))
end)) args wp_args)
in ((head), (_152_887)))
in FStar_Syntax_Syntax.Tm_app (_152_888))
in (mk _152_889)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let binders = (FStar_Syntax_Util.name_binders binders)
in (

let _57_1094 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (_57_1094) with
| (binders_orig, comp) -> begin
(

let _57_1103 = (let _152_901 = (FStar_List.map (fun _57_1097 -> (match (_57_1097) with
| (bv, q) -> begin
(

let h = bv.FStar_Syntax_Syntax.sort
in if (is_C h) then begin
(

let w' = (let _152_891 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-w\'") None _152_891))
in (let _152_897 = (let _152_896 = (FStar_Syntax_Syntax.mk_binder w')
in (let _152_895 = (let _152_894 = (let _152_893 = (let _152_892 = (FStar_Syntax_Syntax.bv_to_name bv)
in (trans_F_ env h _152_892))
in (FStar_Syntax_Syntax.null_binder _152_893))
in (_152_894)::[])
in (_152_896)::_152_895))
in ((w'), (_152_897))))
end else begin
(

let x = (let _152_898 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-x") None _152_898))
in (let _152_900 = (let _152_899 = (FStar_Syntax_Syntax.mk_binder x)
in (_152_899)::[])
in ((x), (_152_900))))
end)
end)) binders_orig)
in (FStar_List.split _152_901))
in (match (_57_1103) with
| (bvs, binders) -> begin
(

let binders = (FStar_List.flatten binders)
in (

let comp = (let _152_903 = (let _152_902 = (FStar_Syntax_Syntax.binders_of_list bvs)
in (FStar_Syntax_Util.rename_binders binders_orig _152_902))
in (FStar_Syntax_Subst.subst_comp _152_903 comp))
in (

let app = (let _152_909 = (let _152_908 = (let _152_907 = (FStar_List.map (fun bv -> (let _152_906 = (FStar_Syntax_Syntax.bv_to_name bv)
in (let _152_905 = (FStar_Syntax_Syntax.as_implicit false)
in ((_152_906), (_152_905))))) bvs)
in ((wp), (_152_907)))
in FStar_Syntax_Syntax.Tm_app (_152_908))
in (mk _152_909))
in (

let comp = (let _152_911 = (type_of_comp comp)
in (let _152_910 = (is_monadic_comp comp)
in (trans_G env _152_911 _152_910 app)))
in (FStar_Syntax_Util.arrow binders comp)))))
end))
end)))
end
| _57_1110 -> begin
(FStar_All.failwith "impossible trans_F_")
end))))
and trans_G : env_  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env h is_monadic wp -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None h.FStar_Syntax_Syntax.pos))
in if is_monadic then begin
(let _152_922 = (let _152_921 = (star_type' env h)
in (let _152_920 = (let _152_919 = (let _152_918 = (FStar_Syntax_Syntax.as_implicit false)
in ((wp), (_152_918)))
in (_152_919)::[])
in {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_unknown)::[]; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _152_921; FStar_Syntax_Syntax.effect_args = _152_920; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp _152_922))
end else begin
(let _152_923 = (trans_F_ env h wp)
in (FStar_Syntax_Syntax.mk_Total _152_923))
end))


let n : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]))


let star_type : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _152_930 = (n env.env t)
in (star_type' env _152_930)))


let star_expr : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env t -> (let _152_935 = (n env.env t)
in (check_n env _152_935)))


let trans_F : env_  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> (let _152_943 = (n env.env c)
in (let _152_942 = (n env.env wp)
in (trans_F_ env _152_943 _152_942))))




