
open Prims

let gen_wps_for_free : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.sigelts * FStar_Syntax_Syntax.eff_decl) = (fun env binders a wp_a ed -> (

let wp_a = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env wp_a)
in (

let a = (

let _57_13 = a
in (let _154_11 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env a.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_13.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_13.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _154_11}))
in (

let d = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))
in (

let _57_20 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _57_18 = (d "Elaborating extra WP combinators")
in (let _154_14 = (FStar_Syntax_Print.term_to_string wp_a)
in (FStar_Util.print1 "wp_a is: %s\n" _154_14)))
end else begin
()
end
in (

let rec collect_binders = (fun t -> (match ((let _154_17 = (FStar_Syntax_Subst.compress t)
in _154_17.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let rest = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _57_30) -> begin
t
end
| _57_34 -> begin
(FStar_All.failwith "wp_a contains non-Tot arrow")
end)
in (let _154_18 = (collect_binders rest)
in (FStar_List.append bs _154_18)))
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

let gamma = (let _154_21 = (collect_binders wp_a)
in (FStar_All.pipe_right _154_21 FStar_Syntax_Util.name_binders))
in (

let _57_44 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _154_23 = (let _154_22 = (FStar_Syntax_Print.binders_to_string ", " gamma)
in (FStar_Util.format1 "Gamma is %s\n" _154_22))
in (d _154_23))
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

let _57_57 = (let _154_33 = (let _154_32 = (FStar_ST.read sigelts)
in (sigelt)::_154_32)
in (FStar_ST.op_Colon_Equals sigelts _154_33))
in fv)
end)))
in (

let binders_of_list = (FStar_List.map (fun _57_61 -> (match (_57_61) with
| (t, b) -> begin
(let _154_36 = (FStar_Syntax_Syntax.as_implicit b)
in ((t), (_154_36)))
end)))
in (

let mk_all_implicit = (FStar_List.map (fun t -> (let _154_39 = (FStar_Syntax_Syntax.as_implicit true)
in (((Prims.fst t)), (_154_39)))))
in (

let args_of_binders = (FStar_List.map (fun bv -> (let _154_42 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst bv))
in (FStar_Syntax_Syntax.as_arg _154_42))))
in (

let _57_88 = (

let _57_73 = (

let mk = (fun f -> (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let body = (let _154_55 = (let _154_54 = (FStar_Syntax_Syntax.bv_to_name t)
in (f _154_54))
in (FStar_Syntax_Util.arrow gamma _154_55))
in (let _154_60 = (let _154_59 = (let _154_58 = (FStar_Syntax_Syntax.mk_binder a)
in (let _154_57 = (let _154_56 = (FStar_Syntax_Syntax.mk_binder t)
in (_154_56)::[])
in (_154_58)::_154_57))
in (FStar_List.append binders _154_59))
in (FStar_Syntax_Util.abs _154_60 body None)))))
in (let _154_62 = (mk FStar_Syntax_Syntax.mk_Total)
in (let _154_61 = (mk FStar_Syntax_Syntax.mk_GTotal)
in ((_154_62), (_154_61)))))
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

let mk_app = (fun fv t -> (let _154_84 = (let _154_83 = (let _154_82 = (let _154_81 = (FStar_List.map (fun _57_84 -> (match (_57_84) with
| (bv, _57_83) -> begin
(let _154_73 = (FStar_Syntax_Syntax.bv_to_name bv)
in (let _154_72 = (FStar_Syntax_Syntax.as_implicit false)
in ((_154_73), (_154_72))))
end)) binders)
in (let _154_80 = (let _154_79 = (let _154_75 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _154_74 = (FStar_Syntax_Syntax.as_implicit false)
in ((_154_75), (_154_74))))
in (let _154_78 = (let _154_77 = (let _154_76 = (FStar_Syntax_Syntax.as_implicit false)
in ((t), (_154_76)))
in (_154_77)::[])
in (_154_79)::_154_78))
in (FStar_List.append _154_81 _154_80)))
in ((fv), (_154_82)))
in FStar_Syntax_Syntax.Tm_app (_154_83))
in (mk _154_84)))
in ((env), ((mk_app ctx_fv)), ((mk_app gctx_fv))))))))
end))
in (match (_57_88) with
| (env, mk_ctx, mk_gctx) -> begin
(

let c_pure = (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let x = (let _154_89 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" None _154_89))
in (

let ret = (let _154_94 = (let _154_93 = (let _154_92 = (let _154_91 = (let _154_90 = (FStar_Syntax_Syntax.bv_to_name t)
in (mk_ctx _154_90))
in (FStar_Syntax_Syntax.mk_Total _154_91))
in (FStar_Syntax_Util.lcomp_of_comp _154_92))
in FStar_Util.Inl (_154_93))
in Some (_154_94))
in (

let body = (let _154_95 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs gamma _154_95 ret))
in (let _154_98 = (let _154_97 = (mk_all_implicit binders)
in (let _154_96 = (binders_of_list ((((a), (true)))::(((t), (true)))::(((x), (false)))::[]))
in (FStar_List.append _154_97 _154_96)))
in (FStar_Syntax_Util.abs _154_98 body ret))))))
in (

let c_pure = (let _154_99 = (mk_lid "pure")
in (register env _154_99 c_pure))
in (

let c_app = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let l = (let _154_107 = (let _154_106 = (let _154_105 = (let _154_102 = (let _154_101 = (let _154_100 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv None _154_100))
in (FStar_Syntax_Syntax.mk_binder _154_101))
in (_154_102)::[])
in (let _154_104 = (let _154_103 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _154_103))
in (FStar_Syntax_Util.arrow _154_105 _154_104)))
in (mk_gctx _154_106))
in (FStar_Syntax_Syntax.gen_bv "l" None _154_107))
in (

let r = (let _154_109 = (let _154_108 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _154_108))
in (FStar_Syntax_Syntax.gen_bv "r" None _154_109))
in (

let ret = (let _154_114 = (let _154_113 = (let _154_112 = (let _154_111 = (let _154_110 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _154_110))
in (FStar_Syntax_Syntax.mk_Total _154_111))
in (FStar_Syntax_Util.lcomp_of_comp _154_112))
in FStar_Util.Inl (_154_113))
in Some (_154_114))
in (

let outer_body = (

let gamma_as_args = (args_of_binders gamma)
in (

let inner_body = (let _154_120 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _154_119 = (let _154_118 = (let _154_117 = (let _154_116 = (let _154_115 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app _154_115 gamma_as_args))
in (FStar_Syntax_Syntax.as_arg _154_116))
in (_154_117)::[])
in (FStar_List.append gamma_as_args _154_118))
in (FStar_Syntax_Util.mk_app _154_120 _154_119)))
in (FStar_Syntax_Util.abs gamma inner_body ret)))
in (let _154_123 = (let _154_122 = (mk_all_implicit binders)
in (let _154_121 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((l), (false)))::(((r), (false)))::[]))
in (FStar_List.append _154_122 _154_121)))
in (FStar_Syntax_Util.abs _154_123 outer_body ret))))))))
in (

let c_app = (let _154_124 = (mk_lid "app")
in (register env _154_124 c_app))
in (

let c_lift1 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _154_129 = (let _154_126 = (let _154_125 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _154_125))
in (_154_126)::[])
in (let _154_128 = (let _154_127 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _154_127))
in (FStar_Syntax_Util.arrow _154_129 _154_128)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _154_131 = (let _154_130 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _154_130))
in (FStar_Syntax_Syntax.gen_bv "a1" None _154_131))
in (

let ret = (let _154_136 = (let _154_135 = (let _154_134 = (let _154_133 = (let _154_132 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _154_132))
in (FStar_Syntax_Syntax.mk_Total _154_133))
in (FStar_Syntax_Util.lcomp_of_comp _154_134))
in FStar_Util.Inl (_154_135))
in Some (_154_136))
in (let _154_148 = (let _154_138 = (mk_all_implicit binders)
in (let _154_137 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::(((a1), (false)))::[]))
in (FStar_List.append _154_138 _154_137)))
in (let _154_147 = (let _154_146 = (let _154_145 = (let _154_144 = (let _154_141 = (let _154_140 = (let _154_139 = (FStar_Syntax_Syntax.bv_to_name f)
in (_154_139)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _154_140))
in (FStar_Syntax_Util.mk_app c_pure _154_141))
in (let _154_143 = (let _154_142 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_154_142)::[])
in (_154_144)::_154_143))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _154_145))
in (FStar_Syntax_Util.mk_app c_app _154_146))
in (FStar_Syntax_Util.abs _154_148 _154_147 ret)))))))))
in (

let c_lift1 = (let _154_149 = (mk_lid "lift1")
in (register env _154_149 c_lift1))
in (

let c_lift2 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t3 = (FStar_Syntax_Syntax.gen_bv "t3" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _154_157 = (let _154_154 = (let _154_150 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _154_150))
in (let _154_153 = (let _154_152 = (let _154_151 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.null_binder _154_151))
in (_154_152)::[])
in (_154_154)::_154_153))
in (let _154_156 = (let _154_155 = (FStar_Syntax_Syntax.bv_to_name t3)
in (FStar_Syntax_Syntax.mk_GTotal _154_155))
in (FStar_Syntax_Util.arrow _154_157 _154_156)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _154_159 = (let _154_158 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _154_158))
in (FStar_Syntax_Syntax.gen_bv "a1" None _154_159))
in (

let a2 = (let _154_161 = (let _154_160 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _154_160))
in (FStar_Syntax_Syntax.gen_bv "a2" None _154_161))
in (

let ret = (let _154_166 = (let _154_165 = (let _154_164 = (let _154_163 = (let _154_162 = (FStar_Syntax_Syntax.bv_to_name t3)
in (mk_gctx _154_162))
in (FStar_Syntax_Syntax.mk_Total _154_163))
in (FStar_Syntax_Util.lcomp_of_comp _154_164))
in FStar_Util.Inl (_154_165))
in Some (_154_166))
in (let _154_183 = (let _154_168 = (mk_all_implicit binders)
in (let _154_167 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((t3), (true)))::(((f), (false)))::(((a1), (false)))::(((a2), (false)))::[]))
in (FStar_List.append _154_168 _154_167)))
in (let _154_182 = (let _154_181 = (let _154_180 = (let _154_179 = (let _154_176 = (let _154_175 = (let _154_174 = (let _154_171 = (let _154_170 = (let _154_169 = (FStar_Syntax_Syntax.bv_to_name f)
in (_154_169)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _154_170))
in (FStar_Syntax_Util.mk_app c_pure _154_171))
in (let _154_173 = (let _154_172 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_154_172)::[])
in (_154_174)::_154_173))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _154_175))
in (FStar_Syntax_Util.mk_app c_app _154_176))
in (let _154_178 = (let _154_177 = (FStar_Syntax_Syntax.bv_to_name a2)
in (_154_177)::[])
in (_154_179)::_154_178))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _154_180))
in (FStar_Syntax_Util.mk_app c_app _154_181))
in (FStar_Syntax_Util.abs _154_183 _154_182 ret)))))))))))
in (

let c_lift2 = (let _154_184 = (mk_lid "lift2")
in (register env _154_184 c_lift2))
in (

let c_push = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _154_190 = (let _154_186 = (let _154_185 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _154_185))
in (_154_186)::[])
in (let _154_189 = (let _154_188 = (let _154_187 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _154_187))
in (FStar_Syntax_Syntax.mk_Total _154_188))
in (FStar_Syntax_Util.arrow _154_190 _154_189)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let ret = (let _154_200 = (let _154_199 = (let _154_198 = (let _154_197 = (let _154_196 = (let _154_195 = (let _154_192 = (let _154_191 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _154_191))
in (_154_192)::[])
in (let _154_194 = (let _154_193 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _154_193))
in (FStar_Syntax_Util.arrow _154_195 _154_194)))
in (mk_ctx _154_196))
in (FStar_Syntax_Syntax.mk_Total _154_197))
in (FStar_Syntax_Util.lcomp_of_comp _154_198))
in FStar_Util.Inl (_154_199))
in Some (_154_200))
in (

let e1 = (let _154_201 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" None _154_201))
in (

let body = (let _154_210 = (let _154_203 = (let _154_202 = (FStar_Syntax_Syntax.mk_binder e1)
in (_154_202)::[])
in (FStar_List.append gamma _154_203))
in (let _154_209 = (let _154_208 = (FStar_Syntax_Syntax.bv_to_name f)
in (let _154_207 = (let _154_206 = (let _154_204 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg _154_204))
in (let _154_205 = (args_of_binders gamma)
in (_154_206)::_154_205))
in (FStar_Syntax_Util.mk_app _154_208 _154_207)))
in (FStar_Syntax_Util.abs _154_210 _154_209 ret)))
in (let _154_213 = (let _154_212 = (mk_all_implicit binders)
in (let _154_211 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::[]))
in (FStar_List.append _154_212 _154_211)))
in (FStar_Syntax_Util.abs _154_213 body ret)))))))))
in (

let c_push = (let _154_214 = (mk_lid "push")
in (register env _154_214 c_push))
in (

let ret_tot_wp_a = (let _154_217 = (let _154_216 = (let _154_215 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.lcomp_of_comp _154_215))
in FStar_Util.Inl (_154_216))
in Some (_154_217))
in (

let mk_generic_app = (fun c -> if ((FStar_List.length binders) > (Prims.parse_int "0")) then begin
(let _154_222 = (let _154_221 = (let _154_220 = (args_of_binders binders)
in ((c), (_154_220)))
in FStar_Syntax_Syntax.Tm_app (_154_221))
in (mk _154_222))
end else begin
c
end)
in (

let wp_if_then_else = (

let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (let _154_240 = (let _154_223 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (FStar_List.append binders _154_223))
in (let _154_239 = (

let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_unfoldable ((Prims.parse_int "2"))) None)
in (let _154_238 = (let _154_229 = (let _154_228 = (let _154_227 = (let _154_226 = (let _154_225 = (let _154_224 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg _154_224))
in (_154_225)::[])
in (FStar_Syntax_Util.mk_app l_ite _154_226))
in (_154_227)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _154_228))
in (FStar_Syntax_Util.mk_app c_lift2 _154_229))
in (let _154_237 = (let _154_236 = (let _154_235 = (let _154_234 = (let _154_232 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _154_231 = (let _154_230 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_154_230)::[])
in (_154_232)::_154_231))
in (let _154_233 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _154_234 _154_233)))
in (FStar_Syntax_Syntax.mk_Total _154_235))
in FStar_Util.Inr (_154_236))
in (FStar_Syntax_Util.ascribe _154_238 _154_237))))
in (FStar_Syntax_Util.abs _154_240 _154_239 ret_tot_wp_a))))
in (

let wp_if_then_else = (let _154_241 = (mk_lid "wp_if_then_else")
in (register env _154_241 wp_if_then_else))
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

let body = (let _154_252 = (let _154_251 = (let _154_250 = (let _154_247 = (let _154_246 = (let _154_245 = (let _154_244 = (let _154_243 = (let _154_242 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _154_242))
in (_154_243)::[])
in (FStar_Syntax_Util.mk_app l_and _154_244))
in (_154_245)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _154_246))
in (FStar_Syntax_Util.mk_app c_pure _154_247))
in (let _154_249 = (let _154_248 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_154_248)::[])
in (_154_250)::_154_249))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _154_251))
in (FStar_Syntax_Util.mk_app c_app _154_252))
in (let _154_254 = (let _154_253 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders _154_253))
in (FStar_Syntax_Util.abs _154_254 body ret_tot_wp_a))))))
in (

let wp_assert = (let _154_255 = (mk_lid "wp_assert")
in (register env _154_255 wp_assert))
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

let body = (let _154_266 = (let _154_265 = (let _154_264 = (let _154_261 = (let _154_260 = (let _154_259 = (let _154_258 = (let _154_257 = (let _154_256 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _154_256))
in (_154_257)::[])
in (FStar_Syntax_Util.mk_app l_imp _154_258))
in (_154_259)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _154_260))
in (FStar_Syntax_Util.mk_app c_pure _154_261))
in (let _154_263 = (let _154_262 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_154_262)::[])
in (_154_264)::_154_263))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _154_265))
in (FStar_Syntax_Util.mk_app c_app _154_266))
in (let _154_268 = (let _154_267 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders _154_267))
in (FStar_Syntax_Util.abs _154_268 body ret_tot_wp_a))))))
in (

let wp_assume = (let _154_269 = (mk_lid "wp_assume")
in (register env _154_269 wp_assume))
in (

let wp_assume = (mk_generic_app wp_assume)
in (

let wp_close = (

let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _154_273 = (let _154_271 = (let _154_270 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _154_270))
in (_154_271)::[])
in (let _154_272 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _154_273 _154_272)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let body = (let _154_282 = (let _154_281 = (let _154_280 = (let _154_274 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((FStar_Syntax_Util.tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure _154_274))
in (let _154_279 = (let _154_278 = (let _154_277 = (let _154_276 = (let _154_275 = (FStar_Syntax_Syntax.bv_to_name f)
in (_154_275)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _154_276))
in (FStar_Syntax_Util.mk_app c_push _154_277))
in (_154_278)::[])
in (_154_280)::_154_279))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _154_281))
in (FStar_Syntax_Util.mk_app c_app _154_282))
in (let _154_284 = (let _154_283 = (FStar_Syntax_Syntax.binders_of_list ((a)::(b)::(f)::[]))
in (FStar_List.append binders _154_283))
in (FStar_Syntax_Util.abs _154_284 body ret_tot_wp_a))))))
in (

let wp_close = (let _154_285 = (mk_lid "wp_close")
in (register env _154_285 wp_close))
in (

let wp_close = (mk_generic_app wp_close)
in (

let ret_tot_type = (let _154_288 = (let _154_287 = (let _154_286 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _154_286))
in FStar_Util.Inl (_154_287))
in Some (_154_288))
in (

let ret_gtot_type = (let _154_291 = (let _154_290 = (let _154_289 = (FStar_Syntax_Syntax.mk_GTotal FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _154_289))
in FStar_Util.Inl (_154_290))
in Some (_154_291))
in (

let mk_forall = (fun x body -> (let _154_302 = (let _154_301 = (let _154_300 = (let _154_299 = (let _154_298 = (let _154_297 = (let _154_296 = (FStar_Syntax_Syntax.mk_binder x)
in (_154_296)::[])
in (FStar_Syntax_Util.abs _154_297 body ret_tot_type))
in (FStar_Syntax_Syntax.as_arg _154_298))
in (_154_299)::[])
in ((FStar_Syntax_Util.tforall), (_154_300)))
in FStar_Syntax_Syntax.Tm_app (_154_301))
in (FStar_Syntax_Syntax.mk _154_302 None FStar_Range.dummyRange)))
in (

let is_zero_order = (fun t -> (match ((let _154_305 = (FStar_Syntax_Subst.compress t)
in _154_305.FStar_Syntax_Syntax.n)) with
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
in (match ((let _154_327 = (FStar_Syntax_Subst.compress t)
in _154_327.FStar_Syntax_Syntax.n)) with
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

let body = (let _154_335 = (let _154_330 = (let _154_329 = (let _154_328 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _154_328))
in (_154_329)::[])
in (FStar_Syntax_Util.mk_app x _154_330))
in (let _154_334 = (let _154_333 = (let _154_332 = (let _154_331 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _154_331))
in (_154_332)::[])
in (FStar_Syntax_Util.mk_app y _154_333))
in (mk_rel b _154_335 _154_334)))
in (mk_forall a1 body)))
end else begin
(

let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (

let a2 = (FStar_Syntax_Syntax.gen_bv "a2" None a)
in (

let body = (let _154_347 = (let _154_337 = (FStar_Syntax_Syntax.bv_to_name a1)
in (let _154_336 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_rel a _154_337 _154_336)))
in (let _154_346 = (let _154_345 = (let _154_340 = (let _154_339 = (let _154_338 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _154_338))
in (_154_339)::[])
in (FStar_Syntax_Util.mk_app x _154_340))
in (let _154_344 = (let _154_343 = (let _154_342 = (let _154_341 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg _154_341))
in (_154_342)::[])
in (FStar_Syntax_Util.mk_app y _154_343))
in (mk_rel b _154_345 _154_344)))
in (FStar_Syntax_Util.mk_imp _154_347 _154_346)))
in (let _154_348 = (mk_forall a2 body)
in (mk_forall a1 _154_348)))))
end)
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::binders, comp) -> begin
(

let t = (

let _57_228 = t
in (let _154_352 = (let _154_351 = (let _154_350 = (let _154_349 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _154_349))
in (((binder)::[]), (_154_350)))
in FStar_Syntax_Syntax.Tm_arrow (_154_351))
in {FStar_Syntax_Syntax.n = _154_352; FStar_Syntax_Syntax.tk = _57_228.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_228.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_228.FStar_Syntax_Syntax.vars}))
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

let body = (let _154_354 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (let _154_353 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_rel FStar_Syntax_Util.mk_imp wp_a _154_354 _154_353)))
in (let _154_356 = (let _154_355 = (binders_of_list ((((a), (false)))::(((wp1), (false)))::(((wp2), (false)))::[]))
in (FStar_List.append binders _154_355))
in (FStar_Syntax_Util.abs _154_356 body ret_tot_type)))))
in (

let stronger = (let _154_357 = (mk_lid "stronger")
in (register env _154_357 stronger))
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

let eq = (let _154_358 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst post))
in (mk_rel FStar_Syntax_Util.mk_iff k.FStar_Syntax_Syntax.sort k_tm _154_358))
in (match ((FStar_Syntax_Util.destruct_typ_as_formula eq)) with
| Some (FStar_Syntax_Util.QAll (binders, [], body)) -> begin
(

let k_app = (let _154_359 = (args_of_binders binders)
in (FStar_Syntax_Util.mk_app k_tm _154_359))
in (

let guard_free = (let _154_360 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.guard_free FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _154_360))
in (

let pat = (let _154_362 = (let _154_361 = (FStar_Syntax_Syntax.as_arg k_app)
in (_154_361)::[])
in (FStar_Syntax_Util.mk_app guard_free _154_362))
in (

let pattern_guarded_body = (let _154_368 = (let _154_367 = (let _154_366 = (let _154_365 = (let _154_364 = (let _154_363 = (FStar_Syntax_Syntax.as_arg pat)
in (_154_363)::[])
in (_154_364)::[])
in FStar_Syntax_Syntax.Meta_pattern (_154_365))
in ((body), (_154_366)))
in FStar_Syntax_Syntax.Tm_meta (_154_367))
in (mk _154_368))
in (FStar_Syntax_Util.close_forall binders pattern_guarded_body)))))
end
| _57_260 -> begin
(FStar_All.failwith "Impossible: Expected the equivalence to be a quantified formula")
end)))
in (

let body = (let _154_377 = (let _154_376 = (let _154_375 = (let _154_374 = (FStar_Syntax_Syntax.bv_to_name wp)
in (let _154_373 = (let _154_372 = (args_of_binders wp_args)
in (let _154_371 = (let _154_370 = (let _154_369 = (FStar_Syntax_Syntax.bv_to_name k)
in (FStar_Syntax_Syntax.as_arg _154_369))
in (_154_370)::[])
in (FStar_List.append _154_372 _154_371)))
in (FStar_Syntax_Util.mk_app _154_374 _154_373)))
in (FStar_Syntax_Util.mk_imp equiv _154_375))
in (FStar_Syntax_Util.mk_forall k _154_376))
in (FStar_Syntax_Util.abs gamma _154_377 ret_gtot_type))
in (let _154_379 = (let _154_378 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders _154_378))
in (FStar_Syntax_Util.abs _154_379 body ret_gtot_type)))))
end)))
in (

let wp_ite = (let _154_380 = (mk_lid "wp_ite")
in (register env _154_380 wp_ite))
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

let body = (let _154_385 = (let _154_384 = (FStar_All.pipe_left FStar_Syntax_Syntax.bv_to_name (Prims.fst post))
in (let _154_383 = (let _154_382 = (let _154_381 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _154_381))
in (_154_382)::[])
in (FStar_Syntax_Util.mk_app _154_384 _154_383)))
in (FStar_Syntax_Util.mk_forall x _154_385))
in (let _154_388 = (let _154_387 = (let _154_386 = (FStar_Syntax_Syntax.binders_of_list ((a)::[]))
in (FStar_List.append _154_386 gamma))
in (FStar_List.append binders _154_387))
in (FStar_Syntax_Util.abs _154_388 body ret_gtot_type))))
end)))
in (

let null_wp = (let _154_389 = (mk_lid "null_wp")
in (register env _154_389 null_wp))
in (

let null_wp = (mk_generic_app null_wp)
in (

let wp_trivial = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let body = (let _154_399 = (let _154_398 = (let _154_397 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _154_396 = (let _154_395 = (let _154_392 = (let _154_391 = (let _154_390 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg _154_390))
in (_154_391)::[])
in (FStar_Syntax_Util.mk_app null_wp _154_392))
in (let _154_394 = (let _154_393 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_154_393)::[])
in (_154_395)::_154_394))
in (_154_397)::_154_396))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _154_398))
in (FStar_Syntax_Util.mk_app stronger _154_399))
in (let _154_401 = (let _154_400 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders _154_400))
in (FStar_Syntax_Util.abs _154_401 body ret_tot_type))))
in (

let wp_trivial = (let _154_402 = (mk_lid "wp_trivial")
in (register env _154_402 wp_trivial))
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
in (let _154_422 = (let _154_404 = (FStar_ST.read sigelts)
in (FStar_List.rev _154_404))
in (let _154_421 = (

let _57_283 = ed
in (let _154_420 = (let _154_405 = (c wp_if_then_else)
in (([]), (_154_405)))
in (let _154_419 = (let _154_406 = (c wp_ite)
in (([]), (_154_406)))
in (let _154_418 = (let _154_407 = (c stronger)
in (([]), (_154_407)))
in (let _154_417 = (let _154_408 = (c wp_close)
in (([]), (_154_408)))
in (let _154_416 = (let _154_409 = (c wp_assert)
in (([]), (_154_409)))
in (let _154_415 = (let _154_410 = (c wp_assume)
in (([]), (_154_410)))
in (let _154_414 = (let _154_411 = (c null_wp)
in (([]), (_154_411)))
in (let _154_413 = (let _154_412 = (c wp_trivial)
in (([]), (_154_412)))
in {FStar_Syntax_Syntax.qualifiers = _57_283.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_283.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_283.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_283.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_283.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _57_283.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _57_283.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _154_420; FStar_Syntax_Syntax.ite_wp = _154_419; FStar_Syntax_Syntax.stronger = _154_418; FStar_Syntax_Syntax.close_wp = _154_417; FStar_Syntax_Syntax.assert_p = _154_416; FStar_Syntax_Syntax.assume_p = _154_415; FStar_Syntax_Syntax.null_wp = _154_414; FStar_Syntax_Syntax.trivial = _154_413; FStar_Syntax_Syntax.repr = _57_283.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _57_283.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _57_283.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _57_283.FStar_Syntax_Syntax.actions})))))))))
in ((_154_422), (_154_421)))))))))))))))))))))))))))))))))))))))))))))))
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
(let _154_480 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "N[%s]" _154_480))
end
| M (t) -> begin
(let _154_481 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "M[%s]" _154_481))
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


let rec mk_star_to_type : (FStar_Syntax_Syntax.term'  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun mk env a -> (let _154_505 = (let _154_504 = (let _154_503 = (let _154_501 = (let _154_500 = (let _154_498 = (star_type' env a)
in (FStar_Syntax_Syntax.null_bv _154_498))
in (let _154_499 = (FStar_Syntax_Syntax.as_implicit false)
in ((_154_500), (_154_499))))
in (_154_501)::[])
in (let _154_502 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_154_503), (_154_502))))
in FStar_Syntax_Syntax.Tm_arrow (_154_504))
in (mk _154_505)))
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
(let _154_514 = (

let _57_351 = bv
in (let _154_513 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_351.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_351.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _154_513}))
in ((_154_514), (aqual)))
end)) binders)
in (match ((is_monadic_arrow t.FStar_Syntax_Syntax.n)) with
| N (hn) -> begin
(let _154_518 = (let _154_517 = (let _154_516 = (let _154_515 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_Total _154_515))
in ((binders), (_154_516)))
in FStar_Syntax_Syntax.Tm_arrow (_154_517))
in (mk _154_518))
end
| M (a) -> begin
(let _154_527 = (let _154_526 = (let _154_525 = (let _154_523 = (let _154_522 = (let _154_521 = (let _154_519 = (mk_star_to_type env a)
in (FStar_Syntax_Syntax.null_bv _154_519))
in (let _154_520 = (FStar_Syntax_Syntax.as_implicit false)
in ((_154_521), (_154_520))))
in (_154_522)::[])
in (FStar_List.append binders _154_523))
in (let _154_524 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_154_525), (_154_524))))
in FStar_Syntax_Syntax.Tm_arrow (_154_526))
in (mk _154_527))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let is_valid_application = (fun head -> (match ((let _154_530 = (FStar_Syntax_Subst.compress head)
in _154_530.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.option_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.either_lid)) || (let _154_531 = (FStar_Syntax_Subst.compress head)
in (FStar_Syntax_Util.is_tuple_constructor _154_531))) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uinst (_57_367) -> begin
(FStar_All.failwith "impossible (Tm_uinst)")
end
| _57_370 -> begin
false
end))
in if (is_valid_application head) then begin
(let _154_536 = (let _154_535 = (let _154_534 = (FStar_List.map (fun _57_373 -> (match (_57_373) with
| (t, qual) -> begin
(let _154_533 = (star_type' env t)
in ((_154_533), (qual)))
end)) args)
in ((head), (_154_534)))
in FStar_Syntax_Syntax.Tm_app (_154_535))
in (mk _154_536))
end else begin
(let _154_539 = (let _154_538 = (let _154_537 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "For now, only [either] and [option] are supported in the definition language (got: %s)" _154_537))
in FStar_Syntax_Syntax.Err (_154_538))
in (Prims.raise _154_539))
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
in (let _154_540 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _154_540; subst = _57_394.subst; tc_const = _57_394.tc_const}))
in (

let repr = (star_type' env repr)
in (FStar_Syntax_Util.abs binders repr something)))
end))
end
| (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_match (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _154_543 = (let _154_542 = (let _154_541 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "The following term is outside of the definition language: %s" _154_541))
in FStar_Syntax_Syntax.Err (_154_542))
in (Prims.raise _154_543))
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


let rec is_C : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match ((let _154_551 = (FStar_Syntax_Subst.compress t)
in _154_551.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) when (FStar_Syntax_Util.is_tuple_constructor head) -> begin
(

let r = (let _154_553 = (let _154_552 = (FStar_List.hd args)
in (Prims.fst _154_552))
in (is_C _154_553))
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

let body = (let _154_569 = (let _154_568 = (let _154_567 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _154_566 = (let _154_565 = (let _154_564 = (FStar_Syntax_Syntax.as_implicit false)
in ((e), (_154_564)))
in (_154_565)::[])
in ((_154_567), (_154_566))))
in FStar_Syntax_Syntax.Tm_app (_154_568))
in (mk _154_569))
in (let _154_571 = (let _154_570 = (FStar_Syntax_Syntax.mk_binder p)
in (_154_570)::[])
in (FStar_Syntax_Util.abs _154_571 body None)))))))


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

let check = (fun t1 t2 -> if ((not ((is_unknown t2.FStar_Syntax_Syntax.n))) && (not ((let _154_625 = (FStar_TypeChecker_Rel.teq env.env t1 t2)
in (FStar_TypeChecker_Rel.is_trivial _154_625))))) then begin
(let _154_630 = (let _154_629 = (let _154_628 = (FStar_Syntax_Print.term_to_string e)
in (let _154_627 = (FStar_Syntax_Print.term_to_string t1)
in (let _154_626 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check]: the expression [%s] has type [%s] but should have type [%s]" _154_628 _154_627 _154_626))))
in FStar_Syntax_Syntax.Err (_154_629))
in (Prims.raise _154_630))
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
in (let _154_631 = (mk_return env t1 s_e)
in ((M (t1)), (_154_631), (u_e))))
end
| (M (t1), N (t2)) -> begin
(let _154_636 = (let _154_635 = (let _154_634 = (FStar_Syntax_Print.term_to_string e)
in (let _154_633 = (FStar_Syntax_Print.term_to_string t1)
in (let _154_632 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]" _154_634 _154_633 _154_632))))
in FStar_Syntax_Syntax.Err (_154_635))
in (Prims.raise _154_636))
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
(let _154_643 = (check env e2 context_nm)
in (strip_m _154_643))
end)))
in (match ((let _154_644 = (FStar_Syntax_Subst.compress e)
in _154_644.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
(let _154_645 = (infer env e)
in (return_if _154_645))
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
(let _154_653 = (let _154_652 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_let %s" _154_652))
in (FStar_All.failwith _154_653))
end
| FStar_Syntax_Syntax.Tm_type (_57_604) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_607) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_57_610) -> begin
(let _154_655 = (let _154_654 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_refine %s" _154_654))
in (FStar_All.failwith _154_655))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_613) -> begin
(let _154_657 = (let _154_656 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_uvar %s" _154_656))
in (FStar_All.failwith _154_657))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_616) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _154_662 = (let _154_661 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_unknown %s" _154_661))
in (FStar_All.failwith _154_662))
end)))))
and infer : env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.env)
in (match ((let _154_668 = (FStar_Syntax_Subst.compress e)
in _154_668.FStar_Syntax_Syntax.n)) with
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
in (let _154_669 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _154_669; subst = _57_636.subst; tc_const = _57_636.tc_const}))
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

let xw = (let _154_673 = (star_type' env c)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "^w") None _154_673))
in (

let x = (

let _57_654 = bv
in (let _154_675 = (let _154_674 = (FStar_Syntax_Syntax.bv_to_name xw)
in (trans_F_ env c _154_674))
in {FStar_Syntax_Syntax.ppname = _57_654.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_654.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _154_675}))
in (

let env = (

let _57_657 = env
in (let _154_679 = (let _154_678 = (let _154_677 = (let _154_676 = (FStar_Syntax_Syntax.bv_to_name xw)
in ((bv), (_154_676)))
in FStar_Syntax_Syntax.NT (_154_677))
in (_154_678)::env.subst)
in {env = _57_657.env; subst = _154_679; tc_const = _57_657.tc_const}))
in (let _154_683 = (let _154_682 = (FStar_Syntax_Syntax.mk_binder x)
in (let _154_681 = (let _154_680 = (FStar_Syntax_Syntax.mk_binder xw)
in (_154_680)::acc)
in (_154_682)::_154_681))
in ((env), (_154_683))))))
end else begin
(

let x = (

let _57_660 = bv
in (let _154_684 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_660.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_660.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _154_684}))
in (let _154_686 = (let _154_685 = (FStar_Syntax_Syntax.mk_binder x)
in (_154_685)::acc)
in ((env), (_154_686))))
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
(let _154_692 = (let _154_691 = if (is_monadic what) then begin
M (t)
end else begin
N (t)
end
in (comp_of_nm _154_691))
in ((_154_692), (s_body), (u_body)))
end)))
in (match (_57_675) with
| (comp, s_body, u_body) -> begin
(

let t = (

let binders = (FStar_List.map (fun _57_679 -> (match (_57_679) with
| (bv, _57_678) -> begin
(let _154_694 = (FStar_Syntax_Syntax.null_bv bv.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_binder _154_694))
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
(let _154_697 = (let _154_696 = (normalize t)
in N (_154_696))
in ((_154_697), (e), (e)))
end else begin
(let _154_699 = (let _154_698 = (FStar_Util.format1 "The %s constructor has not been whitelisted for the definition language; if this is a function application, consider using [inline]" txt)
in FStar_Syntax_Syntax.Err (_154_698))
in (Prims.raise _154_699))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_715 = (check_n env head)
in (match (_57_715) with
| (t_head, s_head, u_head) -> begin
(

let is_arrow = (fun t -> (match ((let _154_702 = (FStar_Syntax_Subst.compress t)
in _154_702.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_719) -> begin
true
end
| _57_722 -> begin
false
end))
in (

let rec flatten = (fun t -> (match ((let _154_705 = (FStar_Syntax_Subst.compress t)
in _154_705.FStar_Syntax_Syntax.n)) with
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
(let _154_708 = (let _154_707 = (let _154_706 = (FStar_Syntax_Print.term_to_string t_head)
in (FStar_Util.format1 "%s: not a function type" _154_706))
in FStar_Syntax_Syntax.Err (_154_707))
in (Prims.raise _154_708))
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
(let _154_713 = (let _154_712 = (let _154_711 = (FStar_Util.string_of_int n)
in (let _154_710 = (FStar_Util.string_of_int (n' - n))
in (let _154_709 = (FStar_Util.string_of_int n)
in (FStar_Util.format3 "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments." _154_711 _154_710 _154_709))))
in FStar_Syntax_Syntax.Err (_154_712))
in (Prims.raise _154_713))
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
(let _154_721 = (let _154_720 = (FStar_Syntax_Subst.subst_comp subst comp)
in _154_720.FStar_Syntax_Syntax.n)
in (nm_of_comp _154_721))
end
| (binders, []) -> begin
(match ((let _154_724 = (let _154_723 = (let _154_722 = (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))))
in (FStar_Syntax_Subst.subst subst _154_722))
in (FStar_Syntax_Subst.compress _154_723))
in _154_724.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(let _154_728 = (let _154_727 = (let _154_726 = (let _154_725 = (FStar_Syntax_Subst.close_comp binders comp)
in ((binders), (_154_725)))
in FStar_Syntax_Syntax.Tm_arrow (_154_726))
in (mk _154_727))
in N (_154_728))
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

let _57_818 = (let _154_743 = (FStar_List.map2 (fun _57_801 _57_804 -> (match (((_57_801), (_57_804))) with
| ((bv, _57_800), (arg, q)) -> begin
(match ((let _154_731 = (FStar_Syntax_Subst.compress bv.FStar_Syntax_Syntax.sort)
in _154_731.FStar_Syntax_Syntax.n)) with
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
(let _154_742 = (let _154_732 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_arg), (_154_732)))
in (let _154_741 = if (is_C bv.FStar_Syntax_Syntax.sort) then begin
(let _154_738 = (let _154_734 = (FStar_Syntax_Subst.subst env.subst s_arg)
in (let _154_733 = (FStar_Syntax_Syntax.as_implicit false)
in ((_154_734), (_154_733))))
in (let _154_737 = (let _154_736 = (let _154_735 = (FStar_Syntax_Syntax.as_implicit false)
in ((u_arg), (_154_735)))
in (_154_736)::[])
in (_154_738)::_154_737))
end else begin
(let _154_740 = (let _154_739 = (FStar_Syntax_Syntax.as_implicit false)
in ((u_arg), (_154_739)))
in (_154_740)::[])
end
in ((_154_742), (_154_741))))
end))
end)
end)) binders args)
in (FStar_List.split _154_743))
in (match (_57_818) with
| (s_args, u_args) -> begin
(

let u_args = (FStar_List.flatten u_args)
in (let _154_745 = (mk (FStar_Syntax_Syntax.Tm_app (((s_head), (s_args)))))
in (let _154_744 = (mk (FStar_Syntax_Syntax.Tm_app (((u_head), (u_args)))))
in ((final_type), (_154_745), (_154_744)))))
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
(let _154_747 = (let _154_746 = (env.tc_const c)
in N (_154_746))
in ((_154_747), (e), (e)))
end
| FStar_Syntax_Syntax.Tm_let (_57_849) -> begin
(let _154_749 = (let _154_748 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_let %s" _154_748))
in (FStar_All.failwith _154_749))
end
| FStar_Syntax_Syntax.Tm_type (_57_852) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_855) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_57_858) -> begin
(let _154_751 = (let _154_750 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_refine %s" _154_750))
in (FStar_All.failwith _154_751))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_861) -> begin
(let _154_753 = (let _154_752 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_uvar %s" _154_752))
in (FStar_All.failwith _154_753))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_864) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _154_758 = (let _154_757 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_unknown %s" _154_757))
in (FStar_All.failwith _154_758))
end))))
and mk_match : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e0 branches f -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e0.FStar_Syntax_Syntax.pos))
in (

let _57_877 = (check_n env e0)
in (match (_57_877) with
| (_57_874, s_e0, u_e0) -> begin
(

let _57_894 = (let _154_774 = (FStar_List.map (fun b -> (match ((FStar_Syntax_Subst.open_branch b)) with
| (pat, None, body) -> begin
(

let env = (

let _57_883 = env
in (let _154_773 = (let _154_772 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env.env _154_772))
in {env = _154_773; subst = _57_883.subst; tc_const = _57_883.tc_const}))
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
in (FStar_List.split _154_774))
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

let _57_938 = (let _154_778 = (FStar_List.map2 (fun nm _57_913 -> (match (_57_913) with
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
in (FStar_List.unzip3 _154_778))
in (match (_57_938) with
| (nms, s_branches, u_branches) -> begin
(

let s_branches = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let t1_star = if has_m then begin
(let _154_783 = (let _154_781 = (let _154_780 = (let _154_779 = (mk_star_to_type mk env t1)
in (FStar_Syntax_Syntax.new_bv None _154_779))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _154_780))
in (_154_781)::[])
in (let _154_782 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _154_783 _154_782)))
end else begin
t1
end
in (let _154_788 = (let _154_786 = (let _154_785 = (let _154_784 = (mk (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches)))))
in ((_154_784), (FStar_Util.Inl (t1_star)), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (_154_785))
in (mk _154_786))
in (let _154_787 = (mk (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches)))))
in ((if has_m then begin
M (t1)
end else begin
N (t1)
end), (_154_788), (_154_787)))))))
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

let x_binders = (let _154_808 = (FStar_Syntax_Syntax.mk_binder x)
in (_154_808)::[])
in (

let _57_954 = (FStar_Syntax_Subst.open_term x_binders e2)
in (match (_57_954) with
| (x_binders, e2) -> begin
(match ((infer env e1)) with
| (N (t1), s_e1, u_e1) -> begin
(

let env = (

let _57_960 = env
in (let _154_809 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_962 = x
in {FStar_Syntax_Syntax.ppname = _57_962.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_962.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _154_809; subst = _57_960.subst; tc_const = _57_960.tc_const}))
in (

let _57_968 = (proceed env e2)
in (match (_57_968) with
| (nm_rec, s_e2, u_e2) -> begin
(let _154_817 = (let _154_812 = (let _154_811 = (let _154_810 = (FStar_Syntax_Subst.close x_binders s_e2)
in ((((false), (((

let _57_969 = binding
in {FStar_Syntax_Syntax.lbname = _57_969.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_969.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_969.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_969.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = s_e1}))::[]))), (_154_810)))
in FStar_Syntax_Syntax.Tm_let (_154_811))
in (mk _154_812))
in (let _154_816 = (let _154_815 = (let _154_814 = (let _154_813 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _57_971 = binding
in {FStar_Syntax_Syntax.lbname = _57_971.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_971.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_971.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_971.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_154_813)))
in FStar_Syntax_Syntax.Tm_let (_154_814))
in (mk _154_815))
in ((nm_rec), (_154_817), (_154_816))))
end)))
end
| (M (t1), s_e1, u_e1) -> begin
(

let env = (

let _57_978 = env
in (let _154_818 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_980 = x
in {FStar_Syntax_Syntax.ppname = _57_980.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_980.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _154_818; subst = _57_978.subst; tc_const = _57_978.tc_const}))
in (

let _57_986 = (ensure_m env e2)
in (match (_57_986) with
| (t2, s_e2, u_e2) -> begin
(

let p_type = (mk_star_to_type mk env t2)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" None p_type)
in (

let s_e2 = (let _154_824 = (let _154_823 = (let _154_822 = (let _154_821 = (let _154_820 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _154_819 = (FStar_Syntax_Syntax.as_implicit false)
in ((_154_820), (_154_819))))
in (_154_821)::[])
in ((s_e2), (_154_822)))
in FStar_Syntax_Syntax.Tm_app (_154_823))
in (mk _154_824))
in (

let s_e2 = (FStar_Syntax_Util.abs x_binders s_e2 None)
in (

let body = (let _154_829 = (let _154_828 = (let _154_827 = (let _154_826 = (let _154_825 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_e2), (_154_825)))
in (_154_826)::[])
in ((s_e1), (_154_827)))
in FStar_Syntax_Syntax.Tm_app (_154_828))
in (mk _154_829))
in (let _154_836 = (let _154_831 = (let _154_830 = (FStar_Syntax_Syntax.mk_binder p)
in (_154_830)::[])
in (FStar_Syntax_Util.abs _154_831 body None))
in (let _154_835 = (let _154_834 = (let _154_833 = (let _154_832 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _57_992 = binding
in {FStar_Syntax_Syntax.lbname = _57_992.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_992.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_992.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_992.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_154_832)))
in FStar_Syntax_Syntax.Tm_let (_154_833))
in (mk _154_834))
in ((M (t2)), (_154_836), (_154_835)))))))))
end)))
end)
end)))))))
and check_n : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _154_839 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in N (_154_839))
in (match ((check env e mn)) with
| (N (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_1003 -> begin
(FStar_All.failwith "[check_n]: impossible")
end)))
and check_m : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _154_842 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in M (_154_842))
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
in (match ((let _154_851 = (FStar_Syntax_Subst.compress c)
in _154_851.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_1034 = (FStar_Syntax_Util.head_and_args wp)
in (match (_57_1034) with
| (wp_head, wp_args) -> begin
(

let _57_1035 = if ((not (((FStar_List.length wp_args) = (FStar_List.length args)))) || (not ((let _154_852 = (FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length wp_args) FStar_Range.dummyRange)
in (FStar_Syntax_Util.is_constructor wp_head _154_852))))) then begin
(FStar_All.failwith "mismatch")
end else begin
()
end
in (let _154_859 = (let _154_858 = (let _154_857 = (FStar_List.map2 (fun _57_1040 _57_1044 -> (match (((_57_1040), (_57_1044))) with
| ((arg, _57_1039), (wp_arg, _57_1043)) -> begin
(let _154_856 = (trans_F_ env arg wp_arg)
in (let _154_855 = (FStar_Syntax_Syntax.as_implicit false)
in ((_154_856), (_154_855))))
end)) args wp_args)
in ((head), (_154_857)))
in FStar_Syntax_Syntax.Tm_app (_154_858))
in (mk _154_859)))
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

let _57_1062 = (let _154_871 = (FStar_List.map (fun _57_1056 -> (match (_57_1056) with
| (bv, q) -> begin
(

let h = bv.FStar_Syntax_Syntax.sort
in if (is_C h) then begin
(

let w' = (let _154_861 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-w\'") None _154_861))
in (let _154_867 = (let _154_866 = (FStar_Syntax_Syntax.mk_binder w')
in (let _154_865 = (let _154_864 = (let _154_863 = (let _154_862 = (FStar_Syntax_Syntax.bv_to_name bv)
in (trans_F_ env h _154_862))
in (FStar_Syntax_Syntax.null_binder _154_863))
in (_154_864)::[])
in (_154_866)::_154_865))
in ((w'), (_154_867))))
end else begin
(

let x = (let _154_868 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-x") None _154_868))
in (let _154_870 = (let _154_869 = (FStar_Syntax_Syntax.mk_binder x)
in (_154_869)::[])
in ((x), (_154_870))))
end)
end)) binders)
in (FStar_List.split _154_871))
in (match (_57_1062) with
| (bvs, binders) -> begin
(

let binders = (FStar_List.flatten binders)
in (

let app = (let _154_877 = (let _154_876 = (let _154_875 = (FStar_List.map (fun bv -> (let _154_874 = (FStar_Syntax_Syntax.bv_to_name bv)
in (let _154_873 = (FStar_Syntax_Syntax.as_implicit false)
in ((_154_874), (_154_873))))) bvs)
in ((wp), (_154_875)))
in FStar_Syntax_Syntax.Tm_app (_154_876))
in (mk _154_877))
in (

let comp = (let _154_879 = (type_of_comp comp)
in (let _154_878 = (is_monadic_comp comp)
in (trans_G env _154_879 _154_878 app)))
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
(let _154_890 = (let _154_889 = (star_type' env h)
in (let _154_888 = (let _154_887 = (let _154_886 = (FStar_Syntax_Syntax.as_implicit false)
in ((wp), (_154_886)))
in (_154_887)::[])
in {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_unknown)::[]; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _154_889; FStar_Syntax_Syntax.effect_args = _154_888; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp _154_890))
end else begin
(let _154_891 = (trans_F_ env h wp)
in (FStar_Syntax_Syntax.mk_Total _154_891))
end))


let n : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.NoInline)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]))


let star_type : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _154_898 = (n env.env t)
in (star_type' env _154_898)))


let star_expr : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env t -> (let _154_903 = (n env.env t)
in (check_n env _154_903)))


let trans_F : env_  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> (let _154_911 = (n env.env c)
in (let _154_910 = (n env.env wp)
in (trans_F_ env _154_911 _154_910))))




