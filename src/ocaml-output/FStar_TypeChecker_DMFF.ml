
open Prims

let gen_wps_for_free : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.sigelts * FStar_Syntax_Syntax.eff_decl) = (fun env binders a wp_a ed -> (

let wp_a = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env wp_a)
in (

let a = (

let _57_13 = a
in (let _149_11 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env a.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_13.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_13.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_11}))
in (

let d = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))
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

let gamma = (collect_binders wp_a)
in (

let _57_41 = (let _149_22 = (let _149_21 = (FStar_Syntax_Print.binders_to_string ", " gamma)
in (FStar_Util.format1 "Gamma is %s\n" _149_21))
in (d _149_22))
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

let _57_54 = (let _149_32 = (let _149_31 = (FStar_ST.read sigelts)
in (sigelt)::_149_31)
in (FStar_ST.op_Colon_Equals sigelts _149_32))
in fv)
end)))
in (

let binders_of_list = (FStar_List.map (fun _57_58 -> (match (_57_58) with
| (t, b) -> begin
(let _149_35 = (FStar_Syntax_Syntax.as_implicit b)
in ((t), (_149_35)))
end)))
in (

let mk_all_implicit = (FStar_List.map (fun t -> (let _149_38 = (FStar_Syntax_Syntax.as_implicit true)
in (((Prims.fst t)), (_149_38)))))
in (

let args_of_binders = (FStar_List.map (fun bv -> (let _149_41 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst bv))
in (FStar_Syntax_Syntax.as_arg _149_41))))
in (

let _57_85 = (

let _57_70 = (

let mk = (fun f -> (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let body = (let _149_54 = (let _149_53 = (FStar_Syntax_Syntax.bv_to_name t)
in (f _149_53))
in (FStar_Syntax_Util.arrow gamma _149_54))
in (let _149_59 = (let _149_58 = (let _149_57 = (FStar_Syntax_Syntax.mk_binder a)
in (let _149_56 = (let _149_55 = (FStar_Syntax_Syntax.mk_binder t)
in (_149_55)::[])
in (_149_57)::_149_56))
in (FStar_List.append binders _149_58))
in (FStar_Syntax_Util.abs _149_59 body None)))))
in (let _149_61 = (mk FStar_Syntax_Syntax.mk_Total)
in (let _149_60 = (mk FStar_Syntax_Syntax.mk_GTotal)
in ((_149_61), (_149_60)))))
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

let mk_app = (fun fv t -> (let _149_83 = (let _149_82 = (let _149_81 = (let _149_80 = (FStar_List.map (fun _57_81 -> (match (_57_81) with
| (bv, _57_80) -> begin
(let _149_72 = (FStar_Syntax_Syntax.bv_to_name bv)
in (let _149_71 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_72), (_149_71))))
end)) binders)
in (let _149_79 = (let _149_78 = (let _149_74 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _149_73 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_74), (_149_73))))
in (let _149_77 = (let _149_76 = (let _149_75 = (FStar_Syntax_Syntax.as_implicit false)
in ((t), (_149_75)))
in (_149_76)::[])
in (_149_78)::_149_77))
in (FStar_List.append _149_80 _149_79)))
in ((fv), (_149_81)))
in FStar_Syntax_Syntax.Tm_app (_149_82))
in (mk _149_83)))
in ((env), ((mk_app ctx_fv)), ((mk_app gctx_fv))))))))
end))
in (match (_57_85) with
| (env, mk_ctx, mk_gctx) -> begin
(

let c_pure = (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let x = (let _149_88 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" None _149_88))
in (

let ret = (let _149_93 = (let _149_92 = (let _149_91 = (let _149_90 = (let _149_89 = (FStar_Syntax_Syntax.bv_to_name t)
in (mk_ctx _149_89))
in (FStar_Syntax_Syntax.mk_Total _149_90))
in (FStar_Syntax_Util.lcomp_of_comp _149_91))
in FStar_Util.Inl (_149_92))
in Some (_149_93))
in (

let body = (let _149_94 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs gamma _149_94 ret))
in (let _149_97 = (let _149_96 = (mk_all_implicit binders)
in (let _149_95 = (binders_of_list ((((a), (true)))::(((t), (true)))::(((x), (false)))::[]))
in (FStar_List.append _149_96 _149_95)))
in (FStar_Syntax_Util.abs _149_97 body ret))))))
in (

let c_pure = (let _149_98 = (mk_lid "pure")
in (register env _149_98 c_pure))
in (

let c_app = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let l = (let _149_106 = (let _149_105 = (let _149_104 = (let _149_101 = (let _149_100 = (let _149_99 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv None _149_99))
in (FStar_Syntax_Syntax.mk_binder _149_100))
in (_149_101)::[])
in (let _149_103 = (let _149_102 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _149_102))
in (FStar_Syntax_Util.arrow _149_104 _149_103)))
in (mk_gctx _149_105))
in (FStar_Syntax_Syntax.gen_bv "l" None _149_106))
in (

let r = (let _149_108 = (let _149_107 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _149_107))
in (FStar_Syntax_Syntax.gen_bv "r" None _149_108))
in (

let ret = (let _149_113 = (let _149_112 = (let _149_111 = (let _149_110 = (let _149_109 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _149_109))
in (FStar_Syntax_Syntax.mk_Total _149_110))
in (FStar_Syntax_Util.lcomp_of_comp _149_111))
in FStar_Util.Inl (_149_112))
in Some (_149_113))
in (

let outer_body = (

let gamma_as_args = (args_of_binders gamma)
in (

let inner_body = (let _149_119 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _149_118 = (let _149_117 = (let _149_116 = (let _149_115 = (let _149_114 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app _149_114 gamma_as_args))
in (FStar_Syntax_Syntax.as_arg _149_115))
in (_149_116)::[])
in (FStar_List.append gamma_as_args _149_117))
in (FStar_Syntax_Util.mk_app _149_119 _149_118)))
in (FStar_Syntax_Util.abs gamma inner_body ret)))
in (let _149_122 = (let _149_121 = (mk_all_implicit binders)
in (let _149_120 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((l), (false)))::(((r), (false)))::[]))
in (FStar_List.append _149_121 _149_120)))
in (FStar_Syntax_Util.abs _149_122 outer_body ret))))))))
in (

let c_app = (let _149_123 = (mk_lid "app")
in (register env _149_123 c_app))
in (

let c_lift1 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _149_128 = (let _149_125 = (let _149_124 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _149_124))
in (_149_125)::[])
in (let _149_127 = (let _149_126 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _149_126))
in (FStar_Syntax_Util.arrow _149_128 _149_127)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _149_130 = (let _149_129 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _149_129))
in (FStar_Syntax_Syntax.gen_bv "a1" None _149_130))
in (

let ret = (let _149_135 = (let _149_134 = (let _149_133 = (let _149_132 = (let _149_131 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _149_131))
in (FStar_Syntax_Syntax.mk_Total _149_132))
in (FStar_Syntax_Util.lcomp_of_comp _149_133))
in FStar_Util.Inl (_149_134))
in Some (_149_135))
in (let _149_147 = (let _149_137 = (mk_all_implicit binders)
in (let _149_136 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::(((a1), (false)))::[]))
in (FStar_List.append _149_137 _149_136)))
in (let _149_146 = (let _149_145 = (let _149_144 = (let _149_143 = (let _149_140 = (let _149_139 = (let _149_138 = (FStar_Syntax_Syntax.bv_to_name f)
in (_149_138)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_139))
in (FStar_Syntax_Util.mk_app c_pure _149_140))
in (let _149_142 = (let _149_141 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_149_141)::[])
in (_149_143)::_149_142))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_144))
in (FStar_Syntax_Util.mk_app c_app _149_145))
in (FStar_Syntax_Util.abs _149_147 _149_146 ret)))))))))
in (

let c_lift1 = (let _149_148 = (mk_lid "lift1")
in (register env _149_148 c_lift1))
in (

let c_lift2 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t3 = (FStar_Syntax_Syntax.gen_bv "t3" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _149_156 = (let _149_153 = (let _149_149 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _149_149))
in (let _149_152 = (let _149_151 = (let _149_150 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.null_binder _149_150))
in (_149_151)::[])
in (_149_153)::_149_152))
in (let _149_155 = (let _149_154 = (FStar_Syntax_Syntax.bv_to_name t3)
in (FStar_Syntax_Syntax.mk_GTotal _149_154))
in (FStar_Syntax_Util.arrow _149_156 _149_155)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _149_158 = (let _149_157 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _149_157))
in (FStar_Syntax_Syntax.gen_bv "a1" None _149_158))
in (

let a2 = (let _149_160 = (let _149_159 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _149_159))
in (FStar_Syntax_Syntax.gen_bv "a2" None _149_160))
in (

let ret = (let _149_165 = (let _149_164 = (let _149_163 = (let _149_162 = (let _149_161 = (FStar_Syntax_Syntax.bv_to_name t3)
in (mk_gctx _149_161))
in (FStar_Syntax_Syntax.mk_Total _149_162))
in (FStar_Syntax_Util.lcomp_of_comp _149_163))
in FStar_Util.Inl (_149_164))
in Some (_149_165))
in (let _149_181 = (let _149_166 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((t3), (true)))::(((f), (false)))::(((a1), (false)))::(((a2), (false)))::[]))
in (FStar_List.append binders _149_166))
in (let _149_180 = (let _149_179 = (let _149_178 = (let _149_177 = (let _149_174 = (let _149_173 = (let _149_172 = (let _149_169 = (let _149_168 = (let _149_167 = (FStar_Syntax_Syntax.bv_to_name f)
in (_149_167)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_168))
in (FStar_Syntax_Util.mk_app c_pure _149_169))
in (let _149_171 = (let _149_170 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_149_170)::[])
in (_149_172)::_149_171))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_173))
in (FStar_Syntax_Util.mk_app c_app _149_174))
in (let _149_176 = (let _149_175 = (FStar_Syntax_Syntax.bv_to_name a2)
in (_149_175)::[])
in (_149_177)::_149_176))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_178))
in (FStar_Syntax_Util.mk_app c_app _149_179))
in (FStar_Syntax_Util.abs _149_181 _149_180 ret)))))))))))
in (

let c_lift2 = (let _149_182 = (mk_lid "lift2")
in (register env _149_182 c_lift2))
in (

let c_push = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _149_188 = (let _149_184 = (let _149_183 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _149_183))
in (_149_184)::[])
in (let _149_187 = (let _149_186 = (let _149_185 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _149_185))
in (FStar_Syntax_Syntax.mk_Total _149_186))
in (FStar_Syntax_Util.arrow _149_188 _149_187)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let ret = (let _149_198 = (let _149_197 = (let _149_196 = (let _149_195 = (let _149_194 = (let _149_193 = (let _149_190 = (let _149_189 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _149_189))
in (_149_190)::[])
in (let _149_192 = (let _149_191 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _149_191))
in (FStar_Syntax_Util.arrow _149_193 _149_192)))
in (mk_ctx _149_194))
in (FStar_Syntax_Syntax.mk_Total _149_195))
in (FStar_Syntax_Util.lcomp_of_comp _149_196))
in FStar_Util.Inl (_149_197))
in Some (_149_198))
in (

let e1 = (let _149_199 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" None _149_199))
in (

let body = (let _149_208 = (let _149_201 = (let _149_200 = (FStar_Syntax_Syntax.mk_binder e1)
in (_149_200)::[])
in (FStar_List.append gamma _149_201))
in (let _149_207 = (let _149_206 = (FStar_Syntax_Syntax.bv_to_name f)
in (let _149_205 = (let _149_204 = (let _149_202 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg _149_202))
in (let _149_203 = (args_of_binders gamma)
in (_149_204)::_149_203))
in (FStar_Syntax_Util.mk_app _149_206 _149_205)))
in (FStar_Syntax_Util.abs _149_208 _149_207 ret)))
in (let _149_211 = (let _149_210 = (mk_all_implicit binders)
in (let _149_209 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::[]))
in (FStar_List.append _149_210 _149_209)))
in (FStar_Syntax_Util.abs _149_211 body ret)))))))))
in (

let c_push = (let _149_212 = (mk_lid "push")
in (register env _149_212 c_push))
in (

let ret_tot_wp_a = (let _149_215 = (let _149_214 = (let _149_213 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.lcomp_of_comp _149_213))
in FStar_Util.Inl (_149_214))
in Some (_149_215))
in (

let mk_generic_app = (fun c -> if ((FStar_List.length binders) > 0) then begin
(let _149_220 = (let _149_219 = (let _149_218 = (args_of_binders binders)
in ((c), (_149_218)))
in FStar_Syntax_Syntax.Tm_app (_149_219))
in (mk _149_220))
end else begin
c
end)
in (

let wp_if_then_else = (

let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (let _149_238 = (let _149_221 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (FStar_List.append binders _149_221))
in (let _149_237 = (

let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_unfoldable (2)) None)
in (let _149_236 = (let _149_227 = (let _149_226 = (let _149_225 = (let _149_224 = (let _149_223 = (let _149_222 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg _149_222))
in (_149_223)::[])
in (FStar_Syntax_Util.mk_app l_ite _149_224))
in (_149_225)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_226))
in (FStar_Syntax_Util.mk_app c_lift2 _149_227))
in (let _149_235 = (let _149_234 = (let _149_233 = (let _149_232 = (let _149_230 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _149_229 = (let _149_228 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_149_228)::[])
in (_149_230)::_149_229))
in (let _149_231 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _149_232 _149_231)))
in (FStar_Syntax_Syntax.mk_Total _149_233))
in FStar_Util.Inr (_149_234))
in (FStar_Syntax_Util.ascribe _149_236 _149_235))))
in (FStar_Syntax_Util.abs _149_238 _149_237 ret_tot_wp_a))))
in (

let wp_if_then_else = (let _149_239 = (mk_lid "wp_if_then_else")
in (register env _149_239 wp_if_then_else))
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

let body = (let _149_250 = (let _149_249 = (let _149_248 = (let _149_245 = (let _149_244 = (let _149_243 = (let _149_242 = (let _149_241 = (let _149_240 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _149_240))
in (_149_241)::[])
in (FStar_Syntax_Util.mk_app l_and _149_242))
in (_149_243)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_244))
in (FStar_Syntax_Util.mk_app c_pure _149_245))
in (let _149_247 = (let _149_246 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_149_246)::[])
in (_149_248)::_149_247))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_249))
in (FStar_Syntax_Util.mk_app c_app _149_250))
in (let _149_252 = (let _149_251 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders _149_251))
in (FStar_Syntax_Util.abs _149_252 body ret_tot_wp_a))))))
in (

let wp_assert = (let _149_253 = (mk_lid "wp_assert")
in (register env _149_253 wp_assert))
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

let body = (let _149_264 = (let _149_263 = (let _149_262 = (let _149_259 = (let _149_258 = (let _149_257 = (let _149_256 = (let _149_255 = (let _149_254 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _149_254))
in (_149_255)::[])
in (FStar_Syntax_Util.mk_app l_imp _149_256))
in (_149_257)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_258))
in (FStar_Syntax_Util.mk_app c_pure _149_259))
in (let _149_261 = (let _149_260 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_149_260)::[])
in (_149_262)::_149_261))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_263))
in (FStar_Syntax_Util.mk_app c_app _149_264))
in (let _149_266 = (let _149_265 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders _149_265))
in (FStar_Syntax_Util.abs _149_266 body ret_tot_wp_a))))))
in (

let wp_assume = (let _149_267 = (mk_lid "wp_assume")
in (register env _149_267 wp_assume))
in (

let wp_assume = (mk_generic_app wp_assume)
in (

let wp_close = (

let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _149_271 = (let _149_269 = (let _149_268 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _149_268))
in (_149_269)::[])
in (let _149_270 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _149_271 _149_270)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let body = (let _149_280 = (let _149_279 = (let _149_278 = (let _149_272 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((FStar_Syntax_Util.tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure _149_272))
in (let _149_277 = (let _149_276 = (let _149_275 = (let _149_274 = (let _149_273 = (FStar_Syntax_Syntax.bv_to_name f)
in (_149_273)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_274))
in (FStar_Syntax_Util.mk_app c_push _149_275))
in (_149_276)::[])
in (_149_278)::_149_277))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_279))
in (FStar_Syntax_Util.mk_app c_app _149_280))
in (let _149_282 = (let _149_281 = (FStar_Syntax_Syntax.binders_of_list ((a)::(b)::(f)::[]))
in (FStar_List.append binders _149_281))
in (FStar_Syntax_Util.abs _149_282 body ret_tot_wp_a))))))
in (

let wp_close = (let _149_283 = (mk_lid "wp_close")
in (register env _149_283 wp_close))
in (

let wp_close = (mk_generic_app wp_close)
in (

let ret_tot_type = (let _149_286 = (let _149_285 = (let _149_284 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _149_284))
in FStar_Util.Inl (_149_285))
in Some (_149_286))
in (

let mk_forall = (fun x body -> (let _149_297 = (let _149_296 = (let _149_295 = (let _149_294 = (let _149_293 = (let _149_292 = (let _149_291 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_291)::[])
in (FStar_Syntax_Util.abs _149_292 body ret_tot_type))
in (FStar_Syntax_Syntax.as_arg _149_293))
in (_149_294)::[])
in ((FStar_Syntax_Util.tforall), (_149_295)))
in FStar_Syntax_Syntax.Tm_app (_149_296))
in (FStar_Syntax_Syntax.mk _149_297 None FStar_Range.dummyRange)))
in (

let rec mk_leq = (fun t x y -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (match ((let _149_304 = (FStar_Syntax_Subst.compress t)
in _149_304.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_168) -> begin
(FStar_Syntax_Util.mk_imp x y)
end
| (FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) when (FStar_Syntax_Syntax.is_null_binder binder) -> begin
(

let a = (Prims.fst binder).FStar_Syntax_Syntax.sort
in (

let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (

let a2 = (FStar_Syntax_Syntax.gen_bv "a2" None a)
in (

let body = (let _149_316 = (let _149_306 = (FStar_Syntax_Syntax.bv_to_name a1)
in (let _149_305 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_leq a _149_306 _149_305)))
in (let _149_315 = (let _149_314 = (let _149_309 = (let _149_308 = (let _149_307 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _149_307))
in (_149_308)::[])
in (FStar_Syntax_Util.mk_app x _149_309))
in (let _149_313 = (let _149_312 = (let _149_311 = (let _149_310 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg _149_310))
in (_149_311)::[])
in (FStar_Syntax_Util.mk_app y _149_312))
in (mk_leq b _149_314 _149_313)))
in (FStar_Syntax_Util.mk_imp _149_316 _149_315)))
in (let _149_317 = (mk_forall a2 body)
in (mk_forall a1 _149_317))))))
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::binders, comp) -> begin
(

let t = (

let _57_204 = t
in (let _149_321 = (let _149_320 = (let _149_319 = (let _149_318 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _149_318))
in (((binder)::[]), (_149_319)))
in FStar_Syntax_Syntax.Tm_arrow (_149_320))
in {FStar_Syntax_Syntax.n = _149_321; FStar_Syntax_Syntax.tk = _57_204.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _57_204.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_204.FStar_Syntax_Syntax.vars}))
in (mk_leq t x y))
end
| FStar_Syntax_Syntax.Tm_arrow (_57_208) -> begin
(FStar_All.failwith "unhandled arrow")
end
| _57_211 -> begin
(FStar_Syntax_Util.mk_eq t t x y)
end)))
in (

let stronger = (

let wp1 = (FStar_Syntax_Syntax.gen_bv "wp1" None wp_a)
in (

let wp2 = (FStar_Syntax_Syntax.gen_bv "wp2" None wp_a)
in (

let body = (let _149_323 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (let _149_322 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_leq wp_a _149_323 _149_322)))
in (let _149_325 = (let _149_324 = (binders_of_list ((((a), (false)))::(((wp1), (false)))::(((wp2), (false)))::[]))
in (FStar_List.append binders _149_324))
in (FStar_Syntax_Util.abs _149_325 body ret_tot_type)))))
in (

let stronger = (let _149_326 = (mk_lid "stronger")
in (register env _149_326 stronger))
in (

let stronger = (mk_generic_app stronger)
in (

let null_wp = (Prims.snd ed.FStar_Syntax_Syntax.null_wp)
in (

let wp_trivial = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let body = (let _149_336 = (let _149_335 = (let _149_334 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _149_333 = (let _149_332 = (let _149_329 = (let _149_328 = (let _149_327 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg _149_327))
in (_149_328)::[])
in (FStar_Syntax_Util.mk_app null_wp _149_329))
in (let _149_331 = (let _149_330 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_149_330)::[])
in (_149_332)::_149_331))
in (_149_334)::_149_333))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _149_335))
in (FStar_Syntax_Util.mk_app stronger _149_336))
in (let _149_338 = (let _149_337 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders _149_337))
in (FStar_Syntax_Util.abs _149_338 body ret_tot_type))))
in (

let wp_trivial = (let _149_339 = (mk_lid "wp_trivial")
in (register env _149_339 wp_trivial))
in (

let wp_trivial = (mk_generic_app wp_trivial)
in (

let _57_224 = (d "End Dijkstra monads for free")
in (let _149_341 = (let _149_340 = (FStar_ST.read sigelts)
in (FStar_List.rev _149_340))
in ((_149_341), ((

let _57_226 = ed
in {FStar_Syntax_Syntax.qualifiers = _57_226.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _57_226.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _57_226.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _57_226.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _57_226.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _57_226.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _57_226.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = (([]), (wp_if_then_else)); FStar_Syntax_Syntax.ite_wp = _57_226.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = (([]), (stronger)); FStar_Syntax_Syntax.close_wp = (([]), (wp_close)); FStar_Syntax_Syntax.assert_p = (([]), (wp_assert)); FStar_Syntax_Syntax.assume_p = (([]), (wp_assume)); FStar_Syntax_Syntax.null_wp = _57_226.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = (([]), (wp_trivial)); FStar_Syntax_Syntax.repr = _57_226.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _57_226.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _57_226.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _57_226.FStar_Syntax_Syntax.actions})))))))))))))))))))))))))))))))))))))))
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
| N (_57_237) -> begin
_57_237
end))


let ___M____0 = (fun projectee -> (match (projectee) with
| M (_57_240) -> begin
_57_240
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
| _57_247 -> begin
(FStar_All.failwith "[nm_of_comp]: impossible")
end))


let string_of_nm : nm  ->  Prims.string = (fun _57_2 -> (match (_57_2) with
| N (t) -> begin
(let _149_402 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "N[%s]" _149_402))
end
| M (t) -> begin
(let _149_403 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "M[%s]" _149_403))
end))


let is_monadic_arrow : FStar_Syntax_Syntax.term'  ->  nm = (fun n -> (match (n) with
| FStar_Syntax_Syntax.Tm_arrow (_57_255, {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _57_261; FStar_Syntax_Syntax.pos = _57_259; FStar_Syntax_Syntax.vars = _57_257}) -> begin
(nm_of_comp n)
end
| _57_267 -> begin
(FStar_All.failwith "unexpected_argument: [is_monadic_arrow]")
end))


let is_monadic_comp = (fun c -> (match ((nm_of_comp c.FStar_Syntax_Syntax.n)) with
| M (_57_270) -> begin
true
end
| N (_57_273) -> begin
false
end))


let rec mk_star_to_type : (FStar_Syntax_Syntax.term'  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun mk env a -> (let _149_427 = (let _149_426 = (let _149_425 = (let _149_423 = (let _149_422 = (let _149_420 = (star_type env a)
in (FStar_Syntax_Syntax.null_bv _149_420))
in (let _149_421 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_422), (_149_421))))
in (_149_423)::[])
in (let _149_424 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_149_425), (_149_424))))
in FStar_Syntax_Syntax.Tm_arrow (_149_426))
in (mk _149_427)))
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
| FStar_Syntax_Syntax.Tm_arrow (binders, _57_288) -> begin
(

let binders = (FStar_List.map (fun _57_293 -> (match (_57_293) with
| (bv, aqual) -> begin
(let _149_437 = (

let _57_294 = bv
in (let _149_436 = (star_type env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_294.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_294.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_436}))
in ((_149_437), (aqual)))
end)) binders)
in (match ((is_monadic_arrow t.FStar_Syntax_Syntax.n)) with
| N (hn) -> begin
(let _149_441 = (let _149_440 = (let _149_439 = (let _149_438 = (star_type env hn)
in (FStar_Syntax_Syntax.mk_Total _149_438))
in ((binders), (_149_439)))
in FStar_Syntax_Syntax.Tm_arrow (_149_440))
in (mk _149_441))
end
| M (a) -> begin
(let _149_450 = (let _149_449 = (let _149_448 = (let _149_446 = (let _149_445 = (let _149_444 = (let _149_442 = (mk_star_to_type env a)
in (FStar_Syntax_Syntax.null_bv _149_442))
in (let _149_443 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_444), (_149_443))))
in (_149_445)::[])
in (FStar_List.append binders _149_446))
in (let _149_447 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_149_448), (_149_447))))
in FStar_Syntax_Syntax.Tm_arrow (_149_449))
in (mk _149_450))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let is_valid_application = (fun head -> (match ((let _149_453 = (FStar_Syntax_Subst.compress head)
in _149_453.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.option_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.either_lid)) || (let _149_454 = (FStar_Syntax_Subst.compress head)
in (FStar_Syntax_Util.is_tuple_constructor _149_454))) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uinst (_57_310) -> begin
(FStar_All.failwith "impossible")
end
| _57_313 -> begin
false
end))
in if (is_valid_application head) then begin
(let _149_459 = (let _149_458 = (let _149_457 = (FStar_List.map (fun _57_316 -> (match (_57_316) with
| (t, qual) -> begin
(let _149_456 = (star_type env t)
in ((_149_456), (qual)))
end)) args)
in ((head), (_149_457)))
in FStar_Syntax_Syntax.Tm_app (_149_458))
in (mk _149_459))
end else begin
(let _149_462 = (let _149_461 = (let _149_460 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "For now, only [either] and [option] are supported in the definition language (got: %s)" _149_460))
in FStar_Syntax_Syntax.Err (_149_461))
in (Prims.raise _149_462))
end)
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_abs (binders, repr, something) -> begin
(

let subst = (FStar_Syntax_Subst.opening_of_binders binders)
in (

let repr = (FStar_Syntax_Subst.subst subst repr)
in (

let env = (

let _57_336 = env
in (let _149_463 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _149_463; definitions = _57_336.definitions; subst = _57_336.subst; tc_const = _57_336.tc_const}))
in (

let repr = (star_type env repr)
in (

let repr = (FStar_Syntax_Subst.close binders repr)
in (mk (FStar_Syntax_Syntax.Tm_abs (((binders), (repr), (something))))))))))
end
| (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_match (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _149_466 = (let _149_465 = (let _149_464 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "The following term is outside of the definition language: %s" _149_464))
in FStar_Syntax_Syntax.Err (_149_465))
in (Prims.raise _149_466))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_370) -> begin
(FStar_All.failwith "impossible")
end)))))))


let star_definition = (fun env t f -> (match ((let _149_480 = (let _149_479 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.env t)
in (FStar_Syntax_Subst.compress _149_479))
in _149_480.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = lid; FStar_Syntax_Syntax.fv_delta = _57_378; FStar_Syntax_Syntax.fv_qual = _57_376}) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.NoInline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.env t)
in (

let _57_383 = (FStar_Util.print1 "Recording definition of %s\n" (FStar_Ident.text_of_lid lid.FStar_Syntax_Syntax.v))
in (

let _57_387 = (f env t)
in (match (_57_387) with
| (keep, ret) -> begin
(((

let _57_388 = env
in {env = _57_388.env; definitions = (((lid.FStar_Syntax_Syntax.v), (keep)))::env.definitions; subst = _57_388.subst; tc_const = _57_388.tc_const})), (ret))
end))))
end
| _57_391 -> begin
(let _149_483 = (let _149_482 = (let _149_481 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Ill-formed definition: %s" _149_481))
in FStar_Syntax_Syntax.Err (_149_482))
in (Prims.raise _149_483))
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


let rec is_C : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match ((let _149_494 = (FStar_Syntax_Subst.compress t)
in _149_494.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) when (FStar_Syntax_Util.is_tuple_constructor head) -> begin
(

let r = (let _149_496 = (let _149_495 = (FStar_List.hd args)
in (Prims.fst _149_495))
in (is_C _149_496))
in if r then begin
(

let _57_421 = if (not ((FStar_List.for_all (fun _57_420 -> (match (_57_420) with
| (h, _57_419) -> begin
(is_C h)
end)) args))) then begin
(FStar_All.failwith "not a C (A * C)")
end else begin
()
end
in true)
end else begin
(

let _57_427 = if (not ((FStar_List.for_all (fun _57_426 -> (match (_57_426) with
| (h, _57_425) -> begin
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

let _57_435 = if (is_C t) then begin
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
| _57_455 -> begin
false
end))


let mk_return : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let p_type = (mk_star_to_type mk env t)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'" None p_type)
in (

let body = (let _149_512 = (let _149_511 = (let _149_510 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _149_509 = (let _149_508 = (let _149_507 = (FStar_Syntax_Syntax.as_implicit false)
in ((e), (_149_507)))
in (_149_508)::[])
in ((_149_510), (_149_509))))
in FStar_Syntax_Syntax.Tm_app (_149_511))
in (mk _149_512))
in (let _149_514 = (let _149_513 = (FStar_Syntax_Syntax.mk_binder p)
in (_149_513)::[])
in (FStar_Syntax_Util.abs _149_514 body None)))))))


let is_unknown : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun _57_4 -> (match (_57_4) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| _57_467 -> begin
false
end))


let rec check : env  ->  FStar_Syntax_Syntax.term  ->  nm  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e context_nm -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let return_if = (fun _57_477 -> (match (_57_477) with
| (rec_nm, s_e, u_e) -> begin
(

let check = (fun t1 t2 -> if ((not ((is_unknown t2.FStar_Syntax_Syntax.n))) && (not ((let _149_568 = (FStar_TypeChecker_Rel.teq env.env t1 t2)
in (FStar_TypeChecker_Rel.is_trivial _149_568))))) then begin
(let _149_573 = (let _149_572 = (let _149_571 = (FStar_Syntax_Print.term_to_string e)
in (let _149_570 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_569 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check]: the expression [%s] has type [%s] but should have type [%s]" _149_571 _149_570 _149_569))))
in FStar_Syntax_Syntax.Err (_149_572))
in (Prims.raise _149_573))
end else begin
()
end)
in (match (((rec_nm), (context_nm))) with
| ((N (t1), N (t2))) | ((M (t1), M (t2))) -> begin
(

let _57_489 = (check t1 t2)
in ((rec_nm), (s_e), (u_e)))
end
| (N (t1), M (t2)) -> begin
(

let _57_496 = (check t1 t2)
in (let _149_574 = (mk_return env t1 s_e)
in ((M (t1)), (_149_574), (u_e))))
end
| (M (t1), N (t2)) -> begin
(let _149_579 = (let _149_578 = (let _149_577 = (FStar_Syntax_Print.term_to_string e)
in (let _149_576 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_575 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]" _149_577 _149_576 _149_575))))
in FStar_Syntax_Syntax.Err (_149_578))
in (Prims.raise _149_579))
end))
end))
in (match ((let _149_580 = (FStar_Syntax_Subst.compress e)
in _149_580.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
(let _149_581 = (infer env e)
in (return_if _149_581))
end
| FStar_Syntax_Syntax.Tm_let ((false, (binding)::[]), e2) -> begin
(mk_let env binding e2 (fun env e2 -> (check env e2 context_nm)) (fun env e2 -> (

let strip_m = (fun _57_5 -> (match (_57_5) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_537 -> begin
(FStar_All.failwith "impossible")
end))
in (match (context_nm) with
| N (t) -> begin
(let _149_588 = (check env e2 (M (t)))
in (strip_m _149_588))
end
| M (_57_542) -> begin
(let _149_589 = (check env e2 context_nm)
in (strip_m _149_589))
end))))
end
| FStar_Syntax_Syntax.Tm_match (e0, branches) -> begin
(mk_match env e0 branches (fun env body -> (check env body context_nm)))
end
| (FStar_Syntax_Syntax.Tm_meta (e, _)) | (FStar_Syntax_Syntax.Tm_uinst (e, _)) | (FStar_Syntax_Syntax.Tm_ascribed (e, _, _)) -> begin
(check env e context_nm)
end
| FStar_Syntax_Syntax.Tm_let (_57_568) -> begin
(let _149_595 = (let _149_594 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_let %s" _149_594))
in (FStar_All.failwith _149_595))
end
| FStar_Syntax_Syntax.Tm_type (_57_571) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_574) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_57_577) -> begin
(let _149_597 = (let _149_596 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_refine %s" _149_596))
in (FStar_All.failwith _149_597))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_580) -> begin
(let _149_599 = (let _149_598 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_uvar %s" _149_598))
in (FStar_All.failwith _149_599))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_583) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _149_604 = (let _149_603 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_unknown %s" _149_603))
in (FStar_All.failwith _149_604))
end))))
and infer : env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.env)
in (match ((let _149_610 = (FStar_Syntax_Subst.compress e)
in _149_610.FStar_Syntax_Syntax.n)) with
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

let _57_603 = env
in (let _149_611 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _149_611; definitions = _57_603.definitions; subst = _57_603.subst; tc_const = _57_603.tc_const}))
in (

let s_binders = (FStar_List.map (fun _57_608 -> (match (_57_608) with
| (bv, qual) -> begin
(

let sort = (star_type env bv.FStar_Syntax_Syntax.sort)
in (((

let _57_610 = bv
in {FStar_Syntax_Syntax.ppname = _57_610.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_610.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (qual)))
end)) binders)
in (

let _57_632 = (FStar_List.fold_left (fun _57_615 _57_618 -> (match (((_57_615), (_57_618))) with
| ((env, acc), (bv, qual)) -> begin
(

let c = (normalize bv.FStar_Syntax_Syntax.sort)
in if (is_C c) then begin
(

let xw = (let _149_615 = (star_type env c)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "^w") None _149_615))
in (

let x = (

let _57_621 = bv
in (let _149_617 = (let _149_616 = (FStar_Syntax_Syntax.bv_to_name xw)
in (trans_F env c _149_616))
in {FStar_Syntax_Syntax.ppname = _57_621.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_621.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_617}))
in (

let env = (

let _57_624 = env
in (let _149_621 = (let _149_620 = (let _149_619 = (let _149_618 = (FStar_Syntax_Syntax.bv_to_name xw)
in ((bv), (_149_618)))
in FStar_Syntax_Syntax.NT (_149_619))
in (_149_620)::env.subst)
in {env = _57_624.env; definitions = _57_624.definitions; subst = _149_621; tc_const = _57_624.tc_const}))
in (let _149_625 = (let _149_624 = (FStar_Syntax_Syntax.mk_binder x)
in (let _149_623 = (let _149_622 = (FStar_Syntax_Syntax.mk_binder xw)
in (_149_622)::acc)
in (_149_624)::_149_623))
in ((env), (_149_625))))))
end else begin
(

let x = (

let _57_627 = bv
in (let _149_626 = (star_type env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_627.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_627.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_626}))
in (let _149_628 = (let _149_627 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_627)::acc)
in ((env), (_149_628))))
end)
end)) ((env), ([])) binders)
in (match (_57_632) with
| (env, u_binders) -> begin
(

let u_binders = (FStar_List.rev u_binders)
in (

let _57_642 = (

let check_what = if (is_monadic what) then begin
check_m
end else begin
check_n
end
in (

let _57_638 = (check_what env body)
in (match (_57_638) with
| (t, s_body, u_body) -> begin
(let _149_634 = (let _149_633 = if (is_monadic what) then begin
M (t)
end else begin
N (t)
end
in (comp_of_nm _149_633))
in ((_149_634), (s_body), (u_body)))
end)))
in (match (_57_642) with
| (comp, s_body, u_body) -> begin
(

let t = (

let binders = (FStar_List.map (fun _57_646 -> (match (_57_646) with
| (bv, _57_645) -> begin
(let _149_637 = (let _149_636 = (normalize bv.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.null_bv _149_636))
in (FStar_Syntax_Syntax.mk_binder _149_637))
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
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = {FStar_Syntax_Syntax.v = lid; FStar_Syntax_Syntax.ty = _57_663; FStar_Syntax_Syntax.p = _57_661}; FStar_Syntax_Syntax.fv_delta = _57_659; FStar_Syntax_Syntax.fv_qual = _57_657}) -> begin
(match ((FStar_List.find (fun _57_671 -> (match (_57_671) with
| (lid', _57_670) -> begin
(FStar_Ident.lid_equals lid lid')
end)) env.definitions)) with
| Some (_57_673, t) -> begin
((N (t)), (e), (e))
end
| None -> begin
(

let _57_681 = (FStar_TypeChecker_Env.lookup_lid env.env lid)
in (match (_57_681) with
| (_57_679, t) -> begin
(

let txt = (FStar_Ident.text_of_lid lid)
in (

let allowed_prefixes = ("Mktuple")::("Left")::("Right")::("Some")::("None")::[]
in if (FStar_List.existsb (fun s -> (FStar_Util.starts_with txt (Prims.strcat "Prims." s))) allowed_prefixes) then begin
((N (t)), (e), (e))
end else begin
(let _149_641 = (let _149_640 = (FStar_Util.format1 "The %s constructor has not been whitelisted for the definition language" txt)
in FStar_Syntax_Syntax.Err (_149_640))
in (Prims.raise _149_641))
end))
end))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_692 = (check_n env head)
in (match (_57_692) with
| (t_head, s_head, u_head) -> begin
(

let t_head = (normalize t_head)
in (

let is_arrow = (fun t -> (match ((let _149_644 = (FStar_Syntax_Subst.compress t)
in _149_644.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_697) -> begin
true
end
| _57_700 -> begin
false
end))
in (

let rec flatten = (fun t -> (match ((let _149_647 = (FStar_Syntax_Subst.compress t)
in _149_647.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (t); FStar_Syntax_Syntax.tk = _57_709; FStar_Syntax_Syntax.pos = _57_707; FStar_Syntax_Syntax.vars = _57_705}) when (is_arrow t) -> begin
(

let _57_717 = (flatten t)
in (match (_57_717) with
| (binders', comp) -> begin
(((FStar_List.append binders binders')), (comp))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
((binders), (comp))
end
| _57_723 -> begin
(let _149_650 = (let _149_649 = (let _149_648 = (FStar_Syntax_Print.term_to_string t_head)
in (FStar_Util.format1 "%s: not a function type" _149_648))
in FStar_Syntax_Syntax.Err (_149_649))
in (Prims.raise _149_650))
end))
in (

let _57_726 = (flatten t_head)
in (match (_57_726) with
| (binders, comp) -> begin
(

let n = (FStar_List.length binders)
in (

let n' = (FStar_List.length args)
in (

let _57_729 = if ((FStar_List.length binders) < (FStar_List.length args)) then begin
(let _149_655 = (let _149_654 = (let _149_653 = (FStar_Util.string_of_int n)
in (let _149_652 = (FStar_Util.string_of_int (n' - n))
in (let _149_651 = (FStar_Util.string_of_int n)
in (FStar_Util.format3 "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments." _149_653 _149_652 _149_651))))
in FStar_Syntax_Syntax.Err (_149_654))
in (Prims.raise _149_655))
end else begin
()
end
in (

let _57_733 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (_57_733) with
| (binders, comp) -> begin
(

let rec final_type = (fun subst _57_738 args -> (match (_57_738) with
| (binders, comp) -> begin
(match (((binders), (args))) with
| ([], []) -> begin
(let _149_663 = (let _149_662 = (FStar_Syntax_Subst.subst_comp subst comp)
in _149_662.FStar_Syntax_Syntax.n)
in (nm_of_comp _149_663))
end
| (binders, []) -> begin
(match ((let _149_666 = (let _149_665 = (let _149_664 = (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))))
in (FStar_Syntax_Subst.subst subst _149_664))
in (FStar_Syntax_Subst.compress _149_665))
in _149_666.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(let _149_670 = (let _149_669 = (let _149_668 = (let _149_667 = (FStar_Syntax_Subst.close_comp binders comp)
in ((binders), (_149_667)))
in FStar_Syntax_Syntax.Tm_arrow (_149_668))
in (mk _149_669))
in N (_149_670))
end
| _57_751 -> begin
(FStar_All.failwith "wat?")
end)
end
| ([], (_57_756)::_57_754) -> begin
(FStar_All.failwith "just checked that?!")
end
| (((bv, _57_762))::binders, ((arg, _57_768))::args) -> begin
(final_type ((FStar_Syntax_Syntax.NT (((bv), (arg))))::subst) ((binders), (comp)) args)
end)
end))
in (

let final_type = (final_type [] ((binders), (comp)) args)
in (

let _57_793 = (let _149_687 = (FStar_List.map2 (fun _57_776 _57_779 -> (match (((_57_776), (_57_779))) with
| ((bv, _57_775), (arg, q)) -> begin
(match ((let _149_674 = (let _149_673 = (normalize bv.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Subst.compress _149_673))
in _149_674.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_781) -> begin
(

let arg = (let _149_675 = (normalize arg)
in ((_149_675), (q)))
in ((arg), ((arg)::[])))
end
| _57_785 -> begin
(

let _57_790 = (check_n env arg)
in (match (_57_790) with
| (_57_787, s_arg, u_arg) -> begin
(let _149_686 = (let _149_676 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_arg), (_149_676)))
in (let _149_685 = if (is_C bv.FStar_Syntax_Syntax.sort) then begin
(let _149_682 = (let _149_678 = (FStar_Syntax_Subst.subst env.subst s_arg)
in (let _149_677 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_678), (_149_677))))
in (let _149_681 = (let _149_680 = (let _149_679 = (FStar_Syntax_Syntax.as_implicit false)
in ((u_arg), (_149_679)))
in (_149_680)::[])
in (_149_682)::_149_681))
end else begin
(let _149_684 = (let _149_683 = (FStar_Syntax_Syntax.as_implicit false)
in ((u_arg), (_149_683)))
in (_149_684)::[])
end
in ((_149_686), (_149_685))))
end))
end)
end)) binders args)
in (FStar_List.split _149_687))
in (match (_57_793) with
| (s_args, u_args) -> begin
(

let u_args = (FStar_List.flatten u_args)
in (let _149_689 = (mk (FStar_Syntax_Syntax.Tm_app (((s_head), (s_args)))))
in (let _149_688 = (mk (FStar_Syntax_Syntax.Tm_app (((u_head), (u_args)))))
in ((final_type), (_149_689), (_149_688)))))
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
(let _149_691 = (let _149_690 = (env.tc_const c)
in N (_149_690))
in ((_149_691), (e), (e)))
end
| FStar_Syntax_Syntax.Tm_let (_57_824) -> begin
(let _149_693 = (let _149_692 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_let %s" _149_692))
in (FStar_All.failwith _149_693))
end
| FStar_Syntax_Syntax.Tm_type (_57_827) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_57_830) -> begin
(FStar_All.failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_57_833) -> begin
(let _149_695 = (let _149_694 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_refine %s" _149_694))
in (FStar_All.failwith _149_695))
end
| FStar_Syntax_Syntax.Tm_uvar (_57_836) -> begin
(let _149_697 = (let _149_696 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_uvar %s" _149_696))
in (FStar_All.failwith _149_697))
end
| FStar_Syntax_Syntax.Tm_delayed (_57_839) -> begin
(FStar_All.failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _149_702 = (let _149_701 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_unknown %s" _149_701))
in (FStar_All.failwith _149_702))
end))))
and mk_match : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e0 branches f -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e0.FStar_Syntax_Syntax.pos))
in (

let _57_852 = (check_n env e0)
in (match (_57_852) with
| (_57_849, s_e0, u_e0) -> begin
(

let _57_869 = (let _149_718 = (FStar_List.map (fun b -> (match ((FStar_Syntax_Subst.open_branch b)) with
| (pat, None, body) -> begin
(

let env = (

let _57_858 = env
in (let _149_717 = (let _149_716 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env.env _149_716))
in {env = _149_717; definitions = _57_858.definitions; subst = _57_858.subst; tc_const = _57_858.tc_const}))
in (

let _57_864 = (f env body)
in (match (_57_864) with
| (nm, s_body, u_body) -> begin
((nm), (((pat), (None), (((s_body), (u_body))))))
end)))
end
| _57_866 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("No when clauses in the definition language")))
end)) branches)
in (FStar_List.split _149_718))
in (match (_57_869) with
| (nms, branches) -> begin
(

let t1 = (match ((FStar_List.hd nms)) with
| (M (t1)) | (N (t1)) -> begin
t1
end)
in (

let has_m = (FStar_List.existsb (fun _57_6 -> (match (_57_6) with
| M (_57_876) -> begin
true
end
| _57_879 -> begin
false
end)) nms)
in (

let _57_914 = (let _149_729 = (FStar_List.map2 (fun nm _57_887 -> (match (_57_887) with
| (pat, guard, (s_body, u_body)) -> begin
(

let check = (fun t t' -> if (not ((let _149_726 = (FStar_TypeChecker_Rel.teq env.env t' t)
in (FStar_TypeChecker_Rel.is_trivial _149_726)))) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("[infer]: branches do not have the same type")))
end else begin
()
end)
in (match (((nm), (has_m))) with
| ((N (t2), false)) | ((M (t2), true)) -> begin
(

let _57_898 = (check t2 t1)
in ((nm), (((pat), (guard), (s_body))), (((pat), (guard), (u_body)))))
end
| (N (t2), true) -> begin
(

let _57_904 = (check t2 t1)
in (let _149_728 = (let _149_727 = (mk_return env t2 s_body)
in ((pat), (guard), (_149_727)))
in ((M (t2)), (_149_728), (((pat), (guard), (u_body))))))
end
| (M (_57_907), false) -> begin
(FStar_All.failwith "impossible")
end))
end)) nms branches)
in (FStar_List.unzip3 _149_729))
in (match (_57_914) with
| (nms, s_branches, u_branches) -> begin
(

let s_branches = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (let _149_731 = (mk (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches)))))
in (let _149_730 = (mk (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches)))))
in ((if has_m then begin
M (t1)
end else begin
N (t1)
end), (_149_731), (_149_730))))))
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

let x_binders = (let _149_751 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_751)::[])
in (

let _57_929 = (FStar_Syntax_Subst.open_term x_binders e2)
in (match (_57_929) with
| (x_binders, e2) -> begin
(match ((infer env e1)) with
| (N (t1), s_e1, u_e1) -> begin
(

let env = (

let _57_935 = env
in (let _149_752 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_937 = x
in {FStar_Syntax_Syntax.ppname = _57_937.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_937.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _149_752; definitions = _57_935.definitions; subst = _57_935.subst; tc_const = _57_935.tc_const}))
in (

let _57_943 = (proceed env e2)
in (match (_57_943) with
| (nm_rec, s_e2, u_e2) -> begin
(let _149_760 = (let _149_755 = (let _149_754 = (let _149_753 = (FStar_Syntax_Subst.close x_binders s_e2)
in ((((false), (((

let _57_944 = binding
in {FStar_Syntax_Syntax.lbname = _57_944.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_944.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_944.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_944.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = s_e1}))::[]))), (_149_753)))
in FStar_Syntax_Syntax.Tm_let (_149_754))
in (mk _149_755))
in (let _149_759 = (let _149_758 = (let _149_757 = (let _149_756 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _57_946 = binding
in {FStar_Syntax_Syntax.lbname = _57_946.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_946.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_946.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_946.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_149_756)))
in FStar_Syntax_Syntax.Tm_let (_149_757))
in (mk _149_758))
in ((nm_rec), (_149_760), (_149_759))))
end)))
end
| (M (t1), s_e1, u_e1) -> begin
(

let env = (

let _57_953 = env
in (let _149_761 = (FStar_TypeChecker_Env.push_bv env.env (

let _57_955 = x
in {FStar_Syntax_Syntax.ppname = _57_955.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_955.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _149_761; definitions = _57_953.definitions; subst = _57_953.subst; tc_const = _57_953.tc_const}))
in (

let _57_961 = (ensure_m env e2)
in (match (_57_961) with
| (t2, s_e2, u_e2) -> begin
(

let p_type = (mk_star_to_type mk env t2)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" None p_type)
in (

let s_e2 = (let _149_767 = (let _149_766 = (let _149_765 = (let _149_764 = (let _149_763 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _149_762 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_763), (_149_762))))
in (_149_764)::[])
in ((s_e2), (_149_765)))
in FStar_Syntax_Syntax.Tm_app (_149_766))
in (mk _149_767))
in (

let s_e2 = (FStar_Syntax_Util.abs x_binders s_e2 None)
in (

let body = (let _149_772 = (let _149_771 = (let _149_770 = (let _149_769 = (let _149_768 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_e2), (_149_768)))
in (_149_769)::[])
in ((s_e1), (_149_770)))
in FStar_Syntax_Syntax.Tm_app (_149_771))
in (mk _149_772))
in (let _149_779 = (let _149_774 = (let _149_773 = (FStar_Syntax_Syntax.mk_binder p)
in (_149_773)::[])
in (FStar_Syntax_Util.abs _149_774 body None))
in (let _149_778 = (let _149_777 = (let _149_776 = (let _149_775 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _57_967 = binding
in {FStar_Syntax_Syntax.lbname = _57_967.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _57_967.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _57_967.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _57_967.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_149_775)))
in FStar_Syntax_Syntax.Tm_let (_149_776))
in (mk _149_777))
in ((M (t2)), (_149_779), (_149_778)))))))))
end)))
end)
end)))))))
and check_n : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _149_782 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in N (_149_782))
in (match ((check env e mn)) with
| (N (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_978 -> begin
(FStar_All.failwith "[check_n]: impossible")
end)))
and check_m : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _149_785 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in M (_149_785))
in (match ((check env e mn)) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _57_988 -> begin
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
and trans_F : env_  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> (

let _57_1010 = if (not ((is_C c))) then begin
(FStar_All.failwith "not a C")
end else begin
()
end
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos))
in (match ((let _149_794 = (FStar_Syntax_Subst.compress c)
in _149_794.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _57_1020 = (FStar_Syntax_Util.head_and_args wp)
in (match (_57_1020) with
| (wp_head, wp_args) -> begin
(

let _57_1021 = if ((not (((FStar_List.length wp_args) = (FStar_List.length args)))) || (not ((let _149_795 = (FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length wp_args) FStar_Range.dummyRange)
in (FStar_Syntax_Util.is_constructor wp_head _149_795))))) then begin
(FStar_All.failwith "mismatch")
end else begin
()
end
in (let _149_802 = (let _149_801 = (let _149_800 = (FStar_List.map2 (fun _57_1026 _57_1030 -> (match (((_57_1026), (_57_1030))) with
| ((arg, _57_1025), (wp_arg, _57_1029)) -> begin
(let _149_799 = (trans_F env arg wp_arg)
in (let _149_798 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_799), (_149_798))))
end)) args wp_args)
in ((head), (_149_800)))
in FStar_Syntax_Syntax.Tm_app (_149_801))
in (mk _149_802)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let binders = (FStar_Syntax_Subst.open_binders binders)
in (

let _57_1038 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (_57_1038) with
| (binders, comp) -> begin
(

let _57_1047 = (let _149_814 = (FStar_List.map (fun _57_1041 -> (match (_57_1041) with
| (bv, q) -> begin
(

let h = bv.FStar_Syntax_Syntax.sort
in if (is_C h) then begin
(

let w' = (let _149_804 = (star_type env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-w\'") None _149_804))
in (let _149_810 = (let _149_809 = (FStar_Syntax_Syntax.mk_binder w')
in (let _149_808 = (let _149_807 = (let _149_806 = (let _149_805 = (FStar_Syntax_Syntax.bv_to_name bv)
in (trans_F env h _149_805))
in (FStar_Syntax_Syntax.null_binder _149_806))
in (_149_807)::[])
in (_149_809)::_149_808))
in ((w'), (_149_810))))
end else begin
(

let x = (let _149_811 = (star_type env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-x") None _149_811))
in (let _149_813 = (let _149_812 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_812)::[])
in ((x), (_149_813))))
end)
end)) binders)
in (FStar_List.split _149_814))
in (match (_57_1047) with
| (bvs, binders) -> begin
(

let binders = (FStar_List.flatten binders)
in (

let app = (let _149_820 = (let _149_819 = (let _149_818 = (FStar_List.map (fun bv -> (let _149_817 = (FStar_Syntax_Syntax.bv_to_name bv)
in (let _149_816 = (FStar_Syntax_Syntax.as_implicit false)
in ((_149_817), (_149_816))))) bvs)
in ((wp), (_149_818)))
in FStar_Syntax_Syntax.Tm_app (_149_819))
in (mk _149_820))
in (

let comp = (let _149_822 = (type_of_comp comp)
in (let _149_821 = (is_monadic_comp comp)
in (trans_G env _149_822 _149_821 app)))
in (

let comp = (FStar_Syntax_Subst.close_comp binders comp)
in (

let binders = (FStar_Syntax_Subst.close_binders binders)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp))))))))))
end))
end)))
end
| _57_1055 -> begin
(FStar_All.failwith "impossible trans_F")
end))))
and trans_G : env_  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env h is_monadic wp -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None h.FStar_Syntax_Syntax.pos))
in if is_monadic then begin
(let _149_833 = (let _149_832 = (star_type env h)
in (let _149_831 = (let _149_830 = (let _149_829 = (FStar_Syntax_Syntax.as_implicit false)
in ((wp), (_149_829)))
in (_149_830)::[])
in {FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _149_832; FStar_Syntax_Syntax.effect_args = _149_831; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp _149_833))
end else begin
(let _149_834 = (trans_F env h wp)
in (FStar_Syntax_Syntax.mk_Total _149_834))
end))


let star_expr_definition : env  ->  FStar_Syntax_Syntax.term  ->  (env * (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)) = (fun env t -> (star_definition env t (fun env e -> (

let _57_1069 = (check_n env e)
in (match (_57_1069) with
| (t, s_e, s_u) -> begin
((t), (((s_e), (s_u))))
end)))))


let trans_FC : env_  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> (

let n = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.env)
in (

let c = (n c)
in (

let wp = (n wp)
in (trans_F env c wp)))))




