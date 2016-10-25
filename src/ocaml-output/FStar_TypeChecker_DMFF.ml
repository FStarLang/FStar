
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

let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "2"))) None)
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

let l_and = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.and_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
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

let l_imp = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.imp_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
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

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
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
| FStar_Syntax_Syntax.Comp (c) -> begin
(let _154_479 = (let _154_478 = (FStar_Ident.string_of_lid c.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format1 "[nm_of_comp]: impossible (%s)" _154_478))
in (FStar_All.failwith _154_479))
end
| FStar_Syntax_Syntax.GTotal (_57_308) -> begin
(FStar_All.failwith "[nm_of_comp]: impossible (GTot)")
end))


let string_of_nm : nm  ->  Prims.string = (fun _57_2 -> (match (_57_2) with
| N (t) -> begin
(let _154_482 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "N[%s]" _154_482))
end
| M (t) -> begin
(let _154_483 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "M[%s]" _154_483))
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


let rec mk_star_to_type : (FStar_Syntax_Syntax.term'  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun mk env a -> (let _154_507 = (let _154_506 = (let _154_505 = (let _154_503 = (let _154_502 = (let _154_500 = (star_type' env a)
in (FStar_Syntax_Syntax.null_bv _154_500))
in (let _154_501 = (FStar_Syntax_Syntax.as_implicit false)
in ((_154_502), (_154_501))))
in (_154_503)::[])
in (let _154_504 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_154_505), (_154_504))))
in FStar_Syntax_Syntax.Tm_arrow (_154_506))
in (mk _154_507)))
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
(let _154_516 = (

let _57_354 = bv
in (let _154_515 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_354.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_354.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _154_515}))
in ((_154_516), (aqual)))
end)) binders)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_358, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (hn, _57_367); FStar_Syntax_Syntax.tk = _57_364; FStar_Syntax_Syntax.pos = _57_362; FStar_Syntax_Syntax.vars = _57_360}) -> begin
(let _154_520 = (let _154_519 = (let _154_518 = (let _154_517 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_GTotal _154_517))
in ((binders), (_154_518)))
in FStar_Syntax_Syntax.Tm_arrow (_154_519))
in (mk _154_520))
end
| _57_374 -> begin
(match ((is_monadic_arrow t.FStar_Syntax_Syntax.n)) with
| N (hn) -> begin
(let _154_524 = (let _154_523 = (let _154_522 = (let _154_521 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_Total _154_521))
in ((binders), (_154_522)))
in FStar_Syntax_Syntax.Tm_arrow (_154_523))
in (mk _154_524))
end
| M (a) -> begin
(let _154_533 = (let _154_532 = (let _154_531 = (let _154_529 = (let _154_528 = (let _154_527 = (let _154_525 = (mk_star_to_type env a)
in (FStar_Syntax_Syntax.null_bv _154_525))
in (let _154_526 = (FStar_Syntax_Syntax.as_implicit false)
in ((_154_527), (_154_526))))
in (_154_528)::[])
in (FStar_List.append binders _154_529))
in (let _154_530 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_154_531), (_154_530))))
in FStar_Syntax_Syntax.Tm_arrow (_154_532))
in (mk _154_533))
end)
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let rec is_valid_application = (fun head -> (match ((let _154_536 = (FStar_Syntax_Subst.compress head)
in _154_536.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.option_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.either_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.eq2_lid)) || (let _154_537 = (FStar_Syntax_Subst.compress head)
in (FStar_Syntax_Util.is_tuple_constructor _154_537))) -> begin
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
(let _154_542 = (let _154_541 = (let _154_540 = (FStar_List.map (fun _57_402 -> (match (_57_402) with
| (t, qual) -> begin
(let _154_539 = (star_type' env t)
in ((_154_539), (qual)))
end)) args)
in ((head), (_154_540)))
in FStar_Syntax_Syntax.Tm_app (_154_541))
in (mk _154_542))
end else begin
(let _154_545 = (let _154_544 = (let _154_543 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)" _154_543))
in FStar_Syntax_Syntax.Err (_154_544))
in (Prims.raise _154_545))
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
in (let _154_546 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _154_546; subst = _57_423.subst; tc_const = _57_423.tc_const}))
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
(let _154_549 = (let _154_548 = (let _154_547 = (star_type' env t)
in ((_154_547), (m)))
in FStar_Syntax_Syntax.Tm_meta (_154_548))
in (mk _154_549))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), something) -> begin
(let _154_554 = (let _154_553 = (let _154_552 = (star_type' env e)
in (let _154_551 = (let _154_550 = (star_type' env t)
in FStar_Util.Inl (_154_550))
in ((_154_552), (_154_551), (something))))
in FStar_Syntax_Syntax.Tm_ascribed (_154_553))
in (mk _154_554))
end
| FStar_Syntax_Syntax.Tm_ascribed (_57_451) -> begin
(let _154_557 = (let _154_556 = (let _154_555 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_ascribed is outside of the definition language: %s" _154_555))
in FStar_Syntax_Syntax.Err (_154_556))
in (Prims.raise _154_557))
end
| FStar_Syntax_Syntax.Tm_refine (_57_454) -> begin
(let _154_560 = (let _154_559 = (let _154_558 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_refine is outside of the definition language: %s" _154_558))
in FStar_Syntax_Syntax.Err (_154_559))
in (Prims.raise _154_560))
end
| FStar_Syntax_Syntax.Tm_uinst (_57_457) -> begin
(let _154_563 = (let _154_562 = (let _154_561 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_uinst is outside of the definition language: %s" _154_561))
in FStar_Syntax_Syntax.Err (_154_562))
in (Prims.raise _154_563))
end
| FStar_Syntax_Syntax.Tm_constant (_57_460) -> begin
(let _154_566 = (let _154_565 = (let _154_564 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_constant is outside of the definition language: %s" _154_564))
in FStar_Syntax_Syntax.Err (_154_565))
in (Prims.raise _154_566))
end
| FStar_Syntax_Syntax.Tm_match (_57_463) -> begin
(let _154_569 = (let _154_568 = (let _154_567 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_match is outside of the definition language: %s" _154_567))
in FStar_Syntax_Syntax.Err (_154_568))
in (Prims.raise _154_569))
end
| FStar_Syntax_Syntax.Tm_let (_57_466) -> begin
(let _154_572 = (let _154_571 = (let _154_570 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_let is outside of the definition language: %s" _154_570))
in FStar_Syntax_Syntax.Err (_154_571))
in (Prims.raise _154_572))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_469) -> begin
(let _154_575 = (let _154_574 = (let _154_573 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_uvar is outside of the definition language: %s" _154_573))
in FStar_Syntax_Syntax.Err (_154_574))
in (Prims.raise _154_575))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _154_578 = (let _154_577 = (let _154_576 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_unknown is outside of the definition language: %s" _154_576))
in FStar_Syntax_Syntax.Err (_154_577))
in (Prims.raise _154_578))
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


let rec is_C : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match ((let _154_586 = (FStar_Syntax_Subst.compress t)
in _154_586.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) when (FStar_Syntax_Util.is_tuple_constructor head) -> begin
(

let r = (let _154_588 = (let _154_587 = (FStar_List.hd args)
in (Prims.fst _154_587))
in (is_C _154_588))
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

let body = (let _154_604 = (let _154_603 = (let _154_602 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _154_601 = (let _154_600 = (let _154_599 = (FStar_Syntax_Syntax.as_implicit false)
in ((e), (_154_599)))
in (_154_600)::[])
in ((_154_602), (_154_601))))
in FStar_Syntax_Syntax.Tm_app (_154_603))
in (mk _154_604))
in (let _154_606 = (let _154_605 = (FStar_Syntax_Syntax.mk_binder p)
in (_154_605)::[])
in (FStar_Syntax_Util.abs _154_606 body None)))))))


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

let check = (fun t1 t2 -> if ((not ((is_unknown t2.FStar_Syntax_Syntax.n))) && (not ((let _154_660 = (FStar_TypeChecker_Rel.teq env.env t1 t2)
in (FStar_TypeChecker_Rel.is_trivial _154_660))))) then begin
(let _154_665 = (let _154_664 = (let _154_663 = (FStar_Syntax_Print.term_to_string e)
in (let _154_662 = (FStar_Syntax_Print.term_to_string t1)
in (let _154_661 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check]: the expression [%s] has type [%s] but should have type [%s]" _154_663 _154_662 _154_661))))
in FStar_Syntax_Syntax.Err (_154_664))
in (Prims.raise _154_665))
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
in (let _154_666 = (mk_return env t1 s_e)
in ((M (t1)), (_154_666), (u_e))))
end
| (M (t1), N (t2)) -> begin
(let _154_671 = (let _154_670 = (let _154_669 = (FStar_Syntax_Print.term_to_string e)
in (let _154_668 = (FStar_Syntax_Print.term_to_string t1)
in (let _154_667 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]" _154_669 _154_668 _154_667))))
in FStar_Syntax_Syntax.Err (_154_670))
in (Prims.raise _154_671))
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
(let _154_678 = (check env e2 context_nm)
in (strip_m _154_678))
end)))
in (match ((let _154_679 = (FStar_Syntax_Subst.compress e)
in _154_679.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
(let _154_680 = (infer env e)
in (return_if _154_680))
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
(let _154_688 = (let _154_687 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_let %s" _154_687))
in (FStar_All.failwith _154_688))
end
| FStar_Syntax_Syntax.Tm_type (_57_650) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_653) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_57_656) -> begin
(let _154_690 = (let _154_689 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_refine %s" _154_689))
in (FStar_All.failwith _154_690))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_659) -> begin
(let _154_692 = (let _154_691 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_uvar %s" _154_691))
in (FStar_All.failwith _154_692))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_662) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _154_697 = (let _154_696 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_unknown %s" _154_696))
in (FStar_All.failwith _154_697))
end)))))
and infer : env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.env)
in (match ((let _154_703 = (FStar_Syntax_Subst.compress e)
in _154_703.FStar_Syntax_Syntax.n)) with
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
in (let _154_704 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _154_704; subst = _57_682.subst; tc_const = _57_682.tc_const}))
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

let xw = (let _154_708 = (star_type' env c)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "^w") None _154_708))
in (

let x = (

let _57_700 = bv
in (let _154_710 = (let _154_709 = (FStar_Syntax_Syntax.bv_to_name xw)
in (trans_F_ env c _154_709))
in {FStar_Syntax_Syntax.ppname = _57_700.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_700.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _154_710}))
in (

let env = (

let _57_703 = env
in (let _154_714 = (let _154_713 = (let _154_712 = (let _154_711 = (FStar_Syntax_Syntax.bv_to_name xw)
in ((bv), (_154_711)))
in FStar_Syntax_Syntax.NT (_154_712))
in (_154_713)::env.subst)
in {env = _57_703.env; subst = _154_714; tc_const = _57_703.tc_const}))
in (let _154_718 = (let _154_717 = (FStar_Syntax_Syntax.mk_binder x)
in (let _154_716 = (let _154_715 = (FStar_Syntax_Syntax.mk_binder xw)
in (_154_715)::acc)
in (_154_717)::_154_716))
in ((env), (_154_718))))))
end else begin
(

let x = (

let _57_706 = bv
in (let _154_719 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_706.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_706.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _154_719}))
in (let _154_721 = (let _154_720 = (FStar_Syntax_Syntax.mk_binder x)
in (_154_720)::acc)
in ((env), (_154_721))))
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
(let _154_727 = (let _154_726 = if (is_monadic what) then begin
M (t)
end else begin
N (t)
end
in (comp_of_nm _154_726))
in ((_154_727), (s_body), (u_body)))
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
in (let _154_729 = (let _154_728 = (normalize t)
in N (_154_728))
in ((_154_729), (e), (e))))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_753 = (check_n env head)
in (match (_57_753) with
| (t_head, s_head, u_head) -> begin
(

let is_arrow = (fun t -> (match ((let _154_732 = (FStar_Syntax_Subst.compress t)
in _154_732.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_757) -> begin
true
end
| _57_760 -> begin
false
end))
in (

let rec flatten = (fun t -> (match ((let _154_735 = (FStar_Syntax_Subst.compress t)
in _154_735.FStar_Syntax_Syntax.n)) with
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
(let _154_738 = (let _154_737 = (let _154_736 = (FStar_Syntax_Print.term_to_string t_head)
in (FStar_Util.format1 "%s: not a function type" _154_736))
in FStar_Syntax_Syntax.Err (_154_737))
in (Prims.raise _154_738))
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
(let _154_743 = (let _154_742 = (let _154_741 = (FStar_Util.string_of_int n)
in (let _154_740 = (FStar_Util.string_of_int (n' - n))
in (let _154_739 = (FStar_Util.string_of_int n)
in (FStar_Util.format3 "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments." _154_741 _154_740 _154_739))))
in FStar_Syntax_Syntax.Err (_154_742))
in (Prims.raise _154_743))
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
(let _154_751 = (let _154_750 = (FStar_Syntax_Subst.subst_comp subst comp)
in _154_750.FStar_Syntax_Syntax.n)
in (nm_of_comp _154_751))
end
| (binders, []) -> begin
(match ((let _154_754 = (let _154_753 = (let _154_752 = (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))))
in (FStar_Syntax_Subst.subst subst _154_752))
in (FStar_Syntax_Subst.compress _154_753))
in _154_754.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(let _154_758 = (let _154_757 = (let _154_756 = (let _154_755 = (FStar_Syntax_Subst.close_comp binders comp)
in ((binders), (_154_755)))
in FStar_Syntax_Syntax.Tm_arrow (_154_756))
in (mk _154_757))
in N (_154_758))
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

let _57_860 = (let _154_773 = (FStar_List.map2 (fun _57_843 _57_846 -> (match (((_57_843), (_57_846))) with
| ((bv, _57_842), (arg, q)) -> begin
(match ((let _154_761 = (FStar_Syntax_Subst.compress bv.FStar_Syntax_Syntax.sort)
in _154_761.FStar_Syntax_Syntax.n)) with
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
(let _154_772 = (let _154_762 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_arg), (_154_762)))
in (let _154_771 = if (is_C bv.FStar_Syntax_Syntax.sort) then begin
(let _154_768 = (let _154_764 = (FStar_Syntax_Subst.subst env.subst s_arg)
in (let _154_763 = (FStar_Syntax_Syntax.as_implicit false)
in ((_154_764), (_154_763))))
in (let _154_767 = (let _154_766 = (let _154_765 = (FStar_Syntax_Syntax.as_implicit false)
in ((u_arg), (_154_765)))
in (_154_766)::[])
in (_154_768)::_154_767))
end else begin
(let _154_770 = (let _154_769 = (FStar_Syntax_Syntax.as_implicit false)
in ((u_arg), (_154_769)))
in (_154_770)::[])
end
in ((_154_772), (_154_771))))
end))
end)
end)) binders args)
in (FStar_List.split _154_773))
in (match (_57_860) with
| (s_args, u_args) -> begin
(

let u_args = (FStar_List.flatten u_args)
in (let _154_775 = (mk (FStar_Syntax_Syntax.Tm_app (((s_head), (s_args)))))
in (let _154_774 = (mk (FStar_Syntax_Syntax.Tm_app (((u_head), (u_args)))))
in ((final_type), (_154_775), (_154_774)))))
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
(let _154_777 = (let _154_776 = (env.tc_const c)
in N (_154_776))
in ((_154_777), (e), (e)))
end
| FStar_Syntax_Syntax.Tm_let (_57_891) -> begin
(let _154_779 = (let _154_778 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_let %s" _154_778))
in (FStar_All.failwith _154_779))
end
| FStar_Syntax_Syntax.Tm_type (_57_894) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_897) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_57_900) -> begin
(let _154_781 = (let _154_780 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_refine %s" _154_780))
in (FStar_All.failwith _154_781))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_903) -> begin
(let _154_783 = (let _154_782 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_uvar %s" _154_782))
in (FStar_All.failwith _154_783))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_906) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _154_788 = (let _154_787 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_unknown %s" _154_787))
in (FStar_All.failwith _154_788))
end))))
and mk_match : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e0 branches f -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e0.FStar_Syntax_Syntax.pos))
in (

let _57_919 = (check_n env e0)
in (match (_57_919) with
| (_57_916, s_e0, u_e0) -> begin
(

let _57_936 = (let _154_804 = (FStar_List.map (fun b -> (match ((FStar_Syntax_Subst.open_branch b)) with
| (pat, None, body) -> begin
(

let env = (

let _57_925 = env
in (let _154_803 = (let _154_802 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env.env _154_802))
in {env = _154_803; subst = _57_925.subst; tc_const = _57_925.tc_const}))
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
in (FStar_List.split _154_804))
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

let _57_980 = (let _154_808 = (FStar_List.map2 (fun nm _57_955 -> (match (_57_955) with
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
in (FStar_List.unzip3 _154_808))
in (match (_57_980) with
| (nms, s_branches, u_branches) -> begin
if has_m then begin
(

let p_type = (mk_star_to_type mk env t1)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" None p_type)
in (

let s_branches = (FStar_List.map (fun _57_986 -> (match (_57_986) with
| (pat, guard, s_body) -> begin
(

let s_body = (let _154_815 = (let _154_814 = (let _154_813 = (let _154_812 = (let _154_811 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _154_810 = (FStar_Syntax_Syntax.as_implicit false)
in ((_154_811), (_154_810))))
in (_154_812)::[])
in ((s_body), (_154_813)))
in FStar_Syntax_Syntax.Tm_app (_154_814))
in (mk _154_815))
in ((pat), (guard), (s_body)))
end)) s_branches)
in (

let s_branches = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let t1_star = (let _154_820 = (let _154_818 = (let _154_817 = (let _154_816 = (mk_star_to_type mk env t1)
in (FStar_Syntax_Syntax.new_bv None _154_816))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _154_817))
in (_154_818)::[])
in (let _154_819 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _154_820 _154_819)))
in (

let s_e = (let _154_823 = (let _154_821 = (FStar_Syntax_Syntax.mk_binder p)
in (_154_821)::[])
in (let _154_822 = (mk (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches)))))
in (FStar_Syntax_Util.abs _154_823 _154_822 None)))
in (let _154_825 = (mk (FStar_Syntax_Syntax.Tm_ascribed (((s_e), (FStar_Util.Inl (t1_star)), (None)))))
in (let _154_824 = (mk (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches)))))
in ((M (t1)), (_154_825), (_154_824)))))))))))
end else begin
(

let s_branches = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let t1_star = t1
in (let _154_830 = (let _154_828 = (let _154_827 = (let _154_826 = (mk (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches)))))
in ((_154_826), (FStar_Util.Inl (t1_star)), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (_154_827))
in (mk _154_828))
in (let _154_829 = (mk (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches)))))
in ((N (t1)), (_154_830), (_154_829)))))))
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

let x_binders = (let _154_850 = (FStar_Syntax_Syntax.mk_binder x)
in (_154_850)::[])
in (

let _57_1008 = (FStar_Syntax_Subst.open_term x_binders e2)
in (match (_57_1008) with
| (x_binders, e2) -> begin
(match ((infer env e1)) with
| (N (t1), s_e1, u_e1) -> begin
(

let env = (

let _57_1014 = env
in (let _154_851 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_1016 = x
in {FStar_Syntax_Syntax.ppname = _57_1016.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1016.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _154_851; subst = _57_1014.subst; tc_const = _57_1014.tc_const}))
in (

let _57_1022 = (proceed env e2)
in (match (_57_1022) with
| (nm_rec, s_e2, u_e2) -> begin
(let _154_859 = (let _154_854 = (let _154_853 = (let _154_852 = (FStar_Syntax_Subst.close x_binders s_e2)
in ((((false), (((

let _57_1023 = binding
in {FStar_Syntax_Syntax.lbname = _57_1023.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_1023.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1023.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1023.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = s_e1}))::[]))), (_154_852)))
in FStar_Syntax_Syntax.Tm_let (_154_853))
in (mk _154_854))
in (let _154_858 = (let _154_857 = (let _154_856 = (let _154_855 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _57_1025 = binding
in {FStar_Syntax_Syntax.lbname = _57_1025.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_1025.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1025.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1025.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_154_855)))
in FStar_Syntax_Syntax.Tm_let (_154_856))
in (mk _154_857))
in ((nm_rec), (_154_859), (_154_858))))
end)))
end
| (M (t1), s_e1, u_e1) -> begin
(

let env = (

let _57_1032 = env
in (let _154_860 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_1034 = x
in {FStar_Syntax_Syntax.ppname = _57_1034.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1034.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _154_860; subst = _57_1032.subst; tc_const = _57_1032.tc_const}))
in (

let _57_1040 = (ensure_m env e2)
in (match (_57_1040) with
| (t2, s_e2, u_e2) -> begin
(

let p_type = (mk_star_to_type mk env t2)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" None p_type)
in (

let s_e2 = (let _154_866 = (let _154_865 = (let _154_864 = (let _154_863 = (let _154_862 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _154_861 = (FStar_Syntax_Syntax.as_implicit false)
in ((_154_862), (_154_861))))
in (_154_863)::[])
in ((s_e2), (_154_864)))
in FStar_Syntax_Syntax.Tm_app (_154_865))
in (mk _154_866))
in (

let s_e2 = (FStar_Syntax_Util.abs x_binders s_e2 None)
in (

let body = (let _154_871 = (let _154_870 = (let _154_869 = (let _154_868 = (let _154_867 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_e2), (_154_867)))
in (_154_868)::[])
in ((s_e1), (_154_869)))
in FStar_Syntax_Syntax.Tm_app (_154_870))
in (mk _154_871))
in (let _154_878 = (let _154_873 = (let _154_872 = (FStar_Syntax_Syntax.mk_binder p)
in (_154_872)::[])
in (FStar_Syntax_Util.abs _154_873 body None))
in (let _154_877 = (let _154_876 = (let _154_875 = (let _154_874 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _57_1046 = binding
in {FStar_Syntax_Syntax.lbname = _57_1046.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_1046.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_1046.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_1046.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_154_874)))
in FStar_Syntax_Syntax.Tm_let (_154_875))
in (mk _154_876))
in ((M (t2)), (_154_878), (_154_877)))))))))
end)))
end)
end)))))))
and check_n : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _154_881 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in N (_154_881))
in (match ((check env e mn)) with
| (N (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_1057 -> begin
(FStar_All.failwith "[check_n]: impossible")
end)))
and check_m : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _154_884 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in M (_154_884))
in (match ((check env e mn)) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_1067 -> begin
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

let _57_1078 = if (not ((is_C c))) then begin
(FStar_All.failwith "not a C")
end else begin
()
end
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos))
in (match ((let _154_893 = (FStar_Syntax_Subst.compress c)
in _154_893.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_1088 = (FStar_Syntax_Util.head_and_args wp)
in (match (_57_1088) with
| (wp_head, wp_args) -> begin
(

let _57_1089 = if ((not (((FStar_List.length wp_args) = (FStar_List.length args)))) || (not ((let _154_894 = (FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length wp_args) FStar_Range.dummyRange)
in (FStar_Syntax_Util.is_constructor wp_head _154_894))))) then begin
(FStar_All.failwith "mismatch")
end else begin
()
end
in (let _154_901 = (let _154_900 = (let _154_899 = (FStar_List.map2 (fun _57_1094 _57_1098 -> (match (((_57_1094), (_57_1098))) with
| ((arg, _57_1093), (wp_arg, _57_1097)) -> begin
(let _154_898 = (trans_F_ env arg wp_arg)
in (let _154_897 = (FStar_Syntax_Syntax.as_implicit false)
in ((_154_898), (_154_897))))
end)) args wp_args)
in ((head), (_154_899)))
in FStar_Syntax_Syntax.Tm_app (_154_900))
in (mk _154_901)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let binders = (FStar_Syntax_Util.name_binders binders)
in (

let _57_1106 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (_57_1106) with
| (binders_orig, comp) -> begin
(

let _57_1115 = (let _154_913 = (FStar_List.map (fun _57_1109 -> (match (_57_1109) with
| (bv, q) -> begin
(

let h = bv.FStar_Syntax_Syntax.sort
in if (is_C h) then begin
(

let w' = (let _154_903 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-w\'") None _154_903))
in (let _154_909 = (let _154_908 = (FStar_Syntax_Syntax.mk_binder w')
in (let _154_907 = (let _154_906 = (let _154_905 = (let _154_904 = (FStar_Syntax_Syntax.bv_to_name bv)
in (trans_F_ env h _154_904))
in (FStar_Syntax_Syntax.null_binder _154_905))
in (_154_906)::[])
in (_154_908)::_154_907))
in ((w'), (_154_909))))
end else begin
(

let x = (let _154_910 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-x") None _154_910))
in (let _154_912 = (let _154_911 = (FStar_Syntax_Syntax.mk_binder x)
in (_154_911)::[])
in ((x), (_154_912))))
end)
end)) binders_orig)
in (FStar_List.split _154_913))
in (match (_57_1115) with
| (bvs, binders) -> begin
(

let binders = (FStar_List.flatten binders)
in (

let comp = (let _154_915 = (let _154_914 = (FStar_Syntax_Syntax.binders_of_list bvs)
in (FStar_Syntax_Util.rename_binders binders_orig _154_914))
in (FStar_Syntax_Subst.subst_comp _154_915 comp))
in (

let app = (let _154_921 = (let _154_920 = (let _154_919 = (FStar_List.map (fun bv -> (let _154_918 = (FStar_Syntax_Syntax.bv_to_name bv)
in (let _154_917 = (FStar_Syntax_Syntax.as_implicit false)
in ((_154_918), (_154_917))))) bvs)
in ((wp), (_154_919)))
in FStar_Syntax_Syntax.Tm_app (_154_920))
in (mk _154_921))
in (

let comp = (let _154_923 = (type_of_comp comp)
in (let _154_922 = (is_monadic_comp comp)
in (trans_G env _154_923 _154_922 app)))
in (FStar_Syntax_Util.arrow binders comp)))))
end))
end)))
end
| _57_1122 -> begin
(FStar_All.failwith "impossible trans_F_")
end))))
and trans_G : env_  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env h is_monadic wp -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None h.FStar_Syntax_Syntax.pos))
in if is_monadic then begin
(let _154_934 = (let _154_933 = (star_type' env h)
in (let _154_932 = (let _154_931 = (let _154_930 = (FStar_Syntax_Syntax.as_implicit false)
in ((wp), (_154_930)))
in (_154_931)::[])
in {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_unknown)::[]; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _154_933; FStar_Syntax_Syntax.effect_args = _154_932; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp _154_934))
end else begin
(let _154_935 = (trans_F_ env h wp)
in (FStar_Syntax_Syntax.mk_Total _154_935))
end))


let n : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]))


let star_type : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _154_942 = (n env.env t)
in (star_type' env _154_942)))


let star_expr : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env t -> (let _154_947 = (n env.env t)
in (check_n env _154_947)))


let trans_F : env_  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> (let _154_955 = (n env.env c)
in (let _154_954 = (n env.env wp)
in (trans_F_ env _154_955 _154_954))))




