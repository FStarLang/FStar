
open Prims

type env =
{env : FStar_TypeChecker_Env.env; subst : FStar_Syntax_Syntax.subst_elt Prims.list; tc_const : FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkenv"))))


let empty : FStar_TypeChecker_Env.env  ->  (FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ)  ->  env = (fun env tc_const -> {env = env; subst = []; tc_const = tc_const})


let gen_wps_for_free : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.sigelts * FStar_Syntax_Syntax.eff_decl) = (fun env binders a wp_a ed -> (

let wp_a = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env wp_a)
in (

let a = (

let _60_13 = a
in (let _161_36 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env a.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _60_13.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _60_13.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _161_36}))
in (

let d = (fun s -> (FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s))
in (

let _60_20 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _60_18 = (d "Elaborating extra WP combinators")
in (let _161_39 = (FStar_Syntax_Print.term_to_string wp_a)
in (FStar_Util.print1 "wp_a is: %s\n" _161_39)))
end else begin
()
end
in (

let rec collect_binders = (fun t -> (match ((let _161_43 = (let _161_42 = (FStar_Syntax_Subst.compress t)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe _161_42))
in _161_43.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let rest = (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _60_30) -> begin
t
end
| _60_34 -> begin
(failwith "wp_a contains non-Tot arrow")
end)
in (let _161_44 = (collect_binders rest)
in (FStar_List.append bs _161_44)))
end
| FStar_Syntax_Syntax.Tm_type (_60_37) -> begin
[]
end
| _60_40 -> begin
(failwith "wp_a doesn\'t end in Type0")
end))
in (

let mk_lid = (fun name -> (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" name))) FStar_Range.dummyRange))
in (

let gamma = (let _161_47 = (collect_binders wp_a)
in (FStar_All.pipe_right _161_47 FStar_Syntax_Util.name_binders))
in (

let _60_44 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _161_49 = (let _161_48 = (FStar_Syntax_Print.binders_to_string ", " gamma)
in (FStar_Util.format1 "Gamma is %s\n" _161_48))
in (d _161_49))
end else begin
()
end
in (

let unknown = FStar_Syntax_Syntax.tun
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None FStar_Range.dummyRange))
in (

let sigelts = (FStar_Util.mk_ref [])
in (

let register = (fun env lident def -> (

let _60_56 = (FStar_TypeChecker_Util.mk_toplevel_definition env lident def)
in (match (_60_56) with
| (sigelt, fv) -> begin
(

let _60_57 = (let _161_59 = (let _161_58 = (FStar_ST.read sigelts)
in (sigelt)::_161_58)
in (FStar_ST.op_Colon_Equals sigelts _161_59))
in fv)
end)))
in (

let binders_of_list = (FStar_List.map (fun _60_61 -> (match (_60_61) with
| (t, b) -> begin
(let _161_62 = (FStar_Syntax_Syntax.as_implicit b)
in ((t), (_161_62)))
end)))
in (

let mk_all_implicit = (FStar_List.map (fun t -> (let _161_65 = (FStar_Syntax_Syntax.as_implicit true)
in (((Prims.fst t)), (_161_65)))))
in (

let args_of_binders = (FStar_List.map (fun bv -> (let _161_68 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst bv))
in (FStar_Syntax_Syntax.as_arg _161_68))))
in (

let _60_88 = (

let _60_73 = (

let mk = (fun f -> (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let body = (let _161_81 = (let _161_80 = (FStar_Syntax_Syntax.bv_to_name t)
in (f _161_80))
in (FStar_Syntax_Util.arrow gamma _161_81))
in (let _161_86 = (let _161_85 = (let _161_84 = (FStar_Syntax_Syntax.mk_binder a)
in (let _161_83 = (let _161_82 = (FStar_Syntax_Syntax.mk_binder t)
in (_161_82)::[])
in (_161_84)::_161_83))
in (FStar_List.append binders _161_85))
in (FStar_Syntax_Util.abs _161_86 body None)))))
in (let _161_88 = (mk FStar_Syntax_Syntax.mk_Total)
in (let _161_87 = (mk FStar_Syntax_Syntax.mk_GTotal)
in ((_161_88), (_161_87)))))
in (match (_60_73) with
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

let mk_app = (fun fv t -> (let _161_110 = (let _161_109 = (let _161_108 = (let _161_107 = (FStar_List.map (fun _60_84 -> (match (_60_84) with
| (bv, _60_83) -> begin
(let _161_99 = (FStar_Syntax_Syntax.bv_to_name bv)
in (let _161_98 = (FStar_Syntax_Syntax.as_implicit false)
in ((_161_99), (_161_98))))
end)) binders)
in (let _161_106 = (let _161_105 = (let _161_101 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _161_100 = (FStar_Syntax_Syntax.as_implicit false)
in ((_161_101), (_161_100))))
in (let _161_104 = (let _161_103 = (let _161_102 = (FStar_Syntax_Syntax.as_implicit false)
in ((t), (_161_102)))
in (_161_103)::[])
in (_161_105)::_161_104))
in (FStar_List.append _161_107 _161_106)))
in ((fv), (_161_108)))
in FStar_Syntax_Syntax.Tm_app (_161_109))
in (mk _161_110)))
in ((env), ((mk_app ctx_fv)), ((mk_app gctx_fv))))))))
end))
in (match (_60_88) with
| (env, mk_ctx, mk_gctx) -> begin
(

let c_pure = (

let t = (FStar_Syntax_Syntax.gen_bv "t" None FStar_Syntax_Util.ktype)
in (

let x = (let _161_115 = (FStar_Syntax_Syntax.bv_to_name t)
in (FStar_Syntax_Syntax.gen_bv "x" None _161_115))
in (

let ret = (let _161_120 = (let _161_119 = (let _161_118 = (let _161_117 = (let _161_116 = (FStar_Syntax_Syntax.bv_to_name t)
in (mk_ctx _161_116))
in (FStar_Syntax_Syntax.mk_Total _161_117))
in (FStar_Syntax_Util.lcomp_of_comp _161_118))
in FStar_Util.Inl (_161_119))
in Some (_161_120))
in (

let body = (let _161_121 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.abs gamma _161_121 ret))
in (let _161_124 = (let _161_123 = (mk_all_implicit binders)
in (let _161_122 = (binders_of_list ((((a), (true)))::(((t), (true)))::(((x), (false)))::[]))
in (FStar_List.append _161_123 _161_122)))
in (FStar_Syntax_Util.abs _161_124 body ret))))))
in (

let c_pure = (let _161_125 = (mk_lid "pure")
in (register env _161_125 c_pure))
in (

let c_app = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let l = (let _161_133 = (let _161_132 = (let _161_131 = (let _161_128 = (let _161_127 = (let _161_126 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.new_bv None _161_126))
in (FStar_Syntax_Syntax.mk_binder _161_127))
in (_161_128)::[])
in (let _161_130 = (let _161_129 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _161_129))
in (FStar_Syntax_Util.arrow _161_131 _161_130)))
in (mk_gctx _161_132))
in (FStar_Syntax_Syntax.gen_bv "l" None _161_133))
in (

let r = (let _161_135 = (let _161_134 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _161_134))
in (FStar_Syntax_Syntax.gen_bv "r" None _161_135))
in (

let ret = (let _161_140 = (let _161_139 = (let _161_138 = (let _161_137 = (let _161_136 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _161_136))
in (FStar_Syntax_Syntax.mk_Total _161_137))
in (FStar_Syntax_Util.lcomp_of_comp _161_138))
in FStar_Util.Inl (_161_139))
in Some (_161_140))
in (

let outer_body = (

let gamma_as_args = (args_of_binders gamma)
in (

let inner_body = (let _161_146 = (FStar_Syntax_Syntax.bv_to_name l)
in (let _161_145 = (let _161_144 = (let _161_143 = (let _161_142 = (let _161_141 = (FStar_Syntax_Syntax.bv_to_name r)
in (FStar_Syntax_Util.mk_app _161_141 gamma_as_args))
in (FStar_Syntax_Syntax.as_arg _161_142))
in (_161_143)::[])
in (FStar_List.append gamma_as_args _161_144))
in (FStar_Syntax_Util.mk_app _161_146 _161_145)))
in (FStar_Syntax_Util.abs gamma inner_body ret)))
in (let _161_149 = (let _161_148 = (mk_all_implicit binders)
in (let _161_147 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((l), (false)))::(((r), (false)))::[]))
in (FStar_List.append _161_148 _161_147)))
in (FStar_Syntax_Util.abs _161_149 outer_body ret))))))))
in (

let c_app = (let _161_150 = (mk_lid "app")
in (register env _161_150 c_app))
in (

let c_lift1 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _161_155 = (let _161_152 = (let _161_151 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _161_151))
in (_161_152)::[])
in (let _161_154 = (let _161_153 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _161_153))
in (FStar_Syntax_Util.arrow _161_155 _161_154)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _161_157 = (let _161_156 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _161_156))
in (FStar_Syntax_Syntax.gen_bv "a1" None _161_157))
in (

let ret = (let _161_162 = (let _161_161 = (let _161_160 = (let _161_159 = (let _161_158 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _161_158))
in (FStar_Syntax_Syntax.mk_Total _161_159))
in (FStar_Syntax_Util.lcomp_of_comp _161_160))
in FStar_Util.Inl (_161_161))
in Some (_161_162))
in (let _161_174 = (let _161_164 = (mk_all_implicit binders)
in (let _161_163 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::(((a1), (false)))::[]))
in (FStar_List.append _161_164 _161_163)))
in (let _161_173 = (let _161_172 = (let _161_171 = (let _161_170 = (let _161_167 = (let _161_166 = (let _161_165 = (FStar_Syntax_Syntax.bv_to_name f)
in (_161_165)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _161_166))
in (FStar_Syntax_Util.mk_app c_pure _161_167))
in (let _161_169 = (let _161_168 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_161_168)::[])
in (_161_170)::_161_169))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _161_171))
in (FStar_Syntax_Util.mk_app c_app _161_172))
in (FStar_Syntax_Util.abs _161_174 _161_173 ret)))))))))
in (

let c_lift1 = (let _161_175 = (mk_lid "lift1")
in (register env _161_175 c_lift1))
in (

let c_lift2 = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t3 = (FStar_Syntax_Syntax.gen_bv "t3" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _161_183 = (let _161_180 = (let _161_176 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _161_176))
in (let _161_179 = (let _161_178 = (let _161_177 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.null_binder _161_177))
in (_161_178)::[])
in (_161_180)::_161_179))
in (let _161_182 = (let _161_181 = (FStar_Syntax_Syntax.bv_to_name t3)
in (FStar_Syntax_Syntax.mk_GTotal _161_181))
in (FStar_Syntax_Util.arrow _161_183 _161_182)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let a1 = (let _161_185 = (let _161_184 = (FStar_Syntax_Syntax.bv_to_name t1)
in (mk_gctx _161_184))
in (FStar_Syntax_Syntax.gen_bv "a1" None _161_185))
in (

let a2 = (let _161_187 = (let _161_186 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _161_186))
in (FStar_Syntax_Syntax.gen_bv "a2" None _161_187))
in (

let ret = (let _161_192 = (let _161_191 = (let _161_190 = (let _161_189 = (let _161_188 = (FStar_Syntax_Syntax.bv_to_name t3)
in (mk_gctx _161_188))
in (FStar_Syntax_Syntax.mk_Total _161_189))
in (FStar_Syntax_Util.lcomp_of_comp _161_190))
in FStar_Util.Inl (_161_191))
in Some (_161_192))
in (let _161_209 = (let _161_194 = (mk_all_implicit binders)
in (let _161_193 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((t3), (true)))::(((f), (false)))::(((a1), (false)))::(((a2), (false)))::[]))
in (FStar_List.append _161_194 _161_193)))
in (let _161_208 = (let _161_207 = (let _161_206 = (let _161_205 = (let _161_202 = (let _161_201 = (let _161_200 = (let _161_197 = (let _161_196 = (let _161_195 = (FStar_Syntax_Syntax.bv_to_name f)
in (_161_195)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _161_196))
in (FStar_Syntax_Util.mk_app c_pure _161_197))
in (let _161_199 = (let _161_198 = (FStar_Syntax_Syntax.bv_to_name a1)
in (_161_198)::[])
in (_161_200)::_161_199))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _161_201))
in (FStar_Syntax_Util.mk_app c_app _161_202))
in (let _161_204 = (let _161_203 = (FStar_Syntax_Syntax.bv_to_name a2)
in (_161_203)::[])
in (_161_205)::_161_204))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _161_206))
in (FStar_Syntax_Util.mk_app c_app _161_207))
in (FStar_Syntax_Util.abs _161_209 _161_208 ret)))))))))))
in (

let c_lift2 = (let _161_210 = (mk_lid "lift2")
in (register env _161_210 c_lift2))
in (

let c_push = (

let t1 = (FStar_Syntax_Syntax.gen_bv "t1" None FStar_Syntax_Util.ktype)
in (

let t2 = (FStar_Syntax_Syntax.gen_bv "t2" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _161_216 = (let _161_212 = (let _161_211 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _161_211))
in (_161_212)::[])
in (let _161_215 = (let _161_214 = (let _161_213 = (FStar_Syntax_Syntax.bv_to_name t2)
in (mk_gctx _161_213))
in (FStar_Syntax_Syntax.mk_Total _161_214))
in (FStar_Syntax_Util.arrow _161_216 _161_215)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let ret = (let _161_226 = (let _161_225 = (let _161_224 = (let _161_223 = (let _161_222 = (let _161_221 = (let _161_218 = (let _161_217 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.null_binder _161_217))
in (_161_218)::[])
in (let _161_220 = (let _161_219 = (FStar_Syntax_Syntax.bv_to_name t2)
in (FStar_Syntax_Syntax.mk_GTotal _161_219))
in (FStar_Syntax_Util.arrow _161_221 _161_220)))
in (mk_ctx _161_222))
in (FStar_Syntax_Syntax.mk_Total _161_223))
in (FStar_Syntax_Util.lcomp_of_comp _161_224))
in FStar_Util.Inl (_161_225))
in Some (_161_226))
in (

let e1 = (let _161_227 = (FStar_Syntax_Syntax.bv_to_name t1)
in (FStar_Syntax_Syntax.gen_bv "e1" None _161_227))
in (

let body = (let _161_236 = (let _161_229 = (let _161_228 = (FStar_Syntax_Syntax.mk_binder e1)
in (_161_228)::[])
in (FStar_List.append gamma _161_229))
in (let _161_235 = (let _161_234 = (FStar_Syntax_Syntax.bv_to_name f)
in (let _161_233 = (let _161_232 = (let _161_230 = (FStar_Syntax_Syntax.bv_to_name e1)
in (FStar_Syntax_Syntax.as_arg _161_230))
in (let _161_231 = (args_of_binders gamma)
in (_161_232)::_161_231))
in (FStar_Syntax_Util.mk_app _161_234 _161_233)))
in (FStar_Syntax_Util.abs _161_236 _161_235 ret)))
in (let _161_239 = (let _161_238 = (mk_all_implicit binders)
in (let _161_237 = (binders_of_list ((((a), (true)))::(((t1), (true)))::(((t2), (true)))::(((f), (false)))::[]))
in (FStar_List.append _161_238 _161_237)))
in (FStar_Syntax_Util.abs _161_239 body ret)))))))))
in (

let c_push = (let _161_240 = (mk_lid "push")
in (register env _161_240 c_push))
in (

let ret_tot_wp_a = (let _161_243 = (let _161_242 = (let _161_241 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.lcomp_of_comp _161_241))
in FStar_Util.Inl (_161_242))
in Some (_161_243))
in (

let mk_generic_app = (fun c -> if ((FStar_List.length binders) > (Prims.parse_int "0")) then begin
(let _161_248 = (let _161_247 = (let _161_246 = (args_of_binders binders)
in ((c), (_161_246)))
in FStar_Syntax_Syntax.Tm_app (_161_247))
in (mk _161_248))
end else begin
c
end)
in (

let wp_if_then_else = (

let result_comp = (let _161_254 = (let _161_253 = (let _161_251 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _161_250 = (let _161_249 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_161_249)::[])
in (_161_251)::_161_250))
in (let _161_252 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _161_253 _161_252)))
in (FStar_Syntax_Syntax.mk_Total _161_254))
in (

let c = (FStar_Syntax_Syntax.gen_bv "c" None FStar_Syntax_Util.ktype)
in (let _161_264 = (let _161_255 = (FStar_Syntax_Syntax.binders_of_list ((a)::(c)::[]))
in (FStar_List.append binders _161_255))
in (let _161_263 = (

let l_ite = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.ite_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "2"))) None)
in (let _161_262 = (let _161_261 = (let _161_260 = (let _161_259 = (let _161_258 = (let _161_257 = (let _161_256 = (FStar_Syntax_Syntax.bv_to_name c)
in (FStar_Syntax_Syntax.as_arg _161_256))
in (_161_257)::[])
in (FStar_Syntax_Util.mk_app l_ite _161_258))
in (_161_259)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _161_260))
in (FStar_Syntax_Util.mk_app c_lift2 _161_261))
in (FStar_Syntax_Util.ascribe _161_262 (FStar_Util.Inr (result_comp)))))
in (FStar_Syntax_Util.abs _161_264 _161_263 (Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp result_comp)))))))))
in (

let wp_if_then_else = (let _161_265 = (mk_lid "wp_if_then_else")
in (register env _161_265 wp_if_then_else))
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

let body = (let _161_276 = (let _161_275 = (let _161_274 = (let _161_271 = (let _161_270 = (let _161_269 = (let _161_268 = (let _161_267 = (let _161_266 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _161_266))
in (_161_267)::[])
in (FStar_Syntax_Util.mk_app l_and _161_268))
in (_161_269)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _161_270))
in (FStar_Syntax_Util.mk_app c_pure _161_271))
in (let _161_273 = (let _161_272 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_161_272)::[])
in (_161_274)::_161_273))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _161_275))
in (FStar_Syntax_Util.mk_app c_app _161_276))
in (let _161_278 = (let _161_277 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders _161_277))
in (FStar_Syntax_Util.abs _161_278 body ret_tot_wp_a))))))
in (

let wp_assert = (let _161_279 = (mk_lid "wp_assert")
in (register env _161_279 wp_assert))
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

let body = (let _161_290 = (let _161_289 = (let _161_288 = (let _161_285 = (let _161_284 = (let _161_283 = (let _161_282 = (let _161_281 = (let _161_280 = (FStar_Syntax_Syntax.bv_to_name q)
in (FStar_Syntax_Syntax.as_arg _161_280))
in (_161_281)::[])
in (FStar_Syntax_Util.mk_app l_imp _161_282))
in (_161_283)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _161_284))
in (FStar_Syntax_Util.mk_app c_pure _161_285))
in (let _161_287 = (let _161_286 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_161_286)::[])
in (_161_288)::_161_287))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _161_289))
in (FStar_Syntax_Util.mk_app c_app _161_290))
in (let _161_292 = (let _161_291 = (FStar_Syntax_Syntax.binders_of_list ((a)::(q)::(wp)::[]))
in (FStar_List.append binders _161_291))
in (FStar_Syntax_Util.abs _161_292 body ret_tot_wp_a))))))
in (

let wp_assume = (let _161_293 = (mk_lid "wp_assume")
in (register env _161_293 wp_assume))
in (

let wp_assume = (mk_generic_app wp_assume)
in (

let wp_close = (

let b = (FStar_Syntax_Syntax.gen_bv "b" None FStar_Syntax_Util.ktype)
in (

let t_f = (let _161_297 = (let _161_295 = (let _161_294 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _161_294))
in (_161_295)::[])
in (let _161_296 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _161_297 _161_296)))
in (

let f = (FStar_Syntax_Syntax.gen_bv "f" None t_f)
in (

let body = (let _161_306 = (let _161_305 = (let _161_304 = (let _161_298 = (FStar_List.map FStar_Syntax_Syntax.as_arg ((FStar_Syntax_Util.tforall)::[]))
in (FStar_Syntax_Util.mk_app c_pure _161_298))
in (let _161_303 = (let _161_302 = (let _161_301 = (let _161_300 = (let _161_299 = (FStar_Syntax_Syntax.bv_to_name f)
in (_161_299)::[])
in (FStar_List.map FStar_Syntax_Syntax.as_arg _161_300))
in (FStar_Syntax_Util.mk_app c_push _161_301))
in (_161_302)::[])
in (_161_304)::_161_303))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _161_305))
in (FStar_Syntax_Util.mk_app c_app _161_306))
in (let _161_308 = (let _161_307 = (FStar_Syntax_Syntax.binders_of_list ((a)::(b)::(f)::[]))
in (FStar_List.append binders _161_307))
in (FStar_Syntax_Util.abs _161_308 body ret_tot_wp_a))))))
in (

let wp_close = (let _161_309 = (mk_lid "wp_close")
in (register env _161_309 wp_close))
in (

let wp_close = (mk_generic_app wp_close)
in (

let ret_tot_type = (let _161_312 = (let _161_311 = (let _161_310 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _161_310))
in FStar_Util.Inl (_161_311))
in Some (_161_312))
in (

let ret_gtot_type = (let _161_315 = (let _161_314 = (let _161_313 = (FStar_Syntax_Syntax.mk_GTotal FStar_Syntax_Util.ktype)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _161_313))
in FStar_Util.Inl (_161_314))
in Some (_161_315))
in (

let mk_forall = (fun x body -> (let _161_326 = (let _161_325 = (let _161_324 = (let _161_323 = (let _161_322 = (let _161_321 = (let _161_320 = (FStar_Syntax_Syntax.mk_binder x)
in (_161_320)::[])
in (FStar_Syntax_Util.abs _161_321 body ret_tot_type))
in (FStar_Syntax_Syntax.as_arg _161_322))
in (_161_323)::[])
in ((FStar_Syntax_Util.tforall), (_161_324)))
in FStar_Syntax_Syntax.Tm_app (_161_325))
in (FStar_Syntax_Syntax.mk _161_326 None FStar_Range.dummyRange)))
in (

let rec is_discrete = (fun t -> (match ((let _161_329 = (FStar_Syntax_Subst.compress t)
in _161_329.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_60_170) -> begin
false
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((FStar_List.for_all (fun _60_179 -> (match (_60_179) with
| (b, _60_178) -> begin
(is_discrete b.FStar_Syntax_Syntax.sort)
end)) bs) && (is_discrete (FStar_Syntax_Util.comp_result c)))
end
| _60_181 -> begin
true
end))
in (

let rec is_monotonic = (fun t -> (match ((let _161_333 = (FStar_Syntax_Subst.compress t)
in _161_333.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_60_185) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((FStar_List.for_all (fun _60_194 -> (match (_60_194) with
| (b, _60_193) -> begin
(is_discrete b.FStar_Syntax_Syntax.sort)
end)) bs) && (is_monotonic (FStar_Syntax_Util.comp_result c)))
end
| _60_196 -> begin
(is_discrete t)
end))
in (

let rec mk_rel = (fun rel t x y -> (

let mk_rel = (mk_rel rel)
in (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (match ((let _161_356 = (FStar_Syntax_Subst.compress t)
in _161_356.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_60_205) -> begin
(rel x y)
end
| (FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Tm_arrow ((binder)::[], {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(

let a = (Prims.fst binder).FStar_Syntax_Syntax.sort
in if ((is_monotonic a) || (is_monotonic b)) then begin
(

let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (

let body = (let _161_364 = (let _161_359 = (let _161_358 = (let _161_357 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _161_357))
in (_161_358)::[])
in (FStar_Syntax_Util.mk_app x _161_359))
in (let _161_363 = (let _161_362 = (let _161_361 = (let _161_360 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _161_360))
in (_161_361)::[])
in (FStar_Syntax_Util.mk_app y _161_362))
in (mk_rel b _161_364 _161_363)))
in (mk_forall a1 body)))
end else begin
(

let a1 = (FStar_Syntax_Syntax.gen_bv "a1" None a)
in (

let a2 = (FStar_Syntax_Syntax.gen_bv "a2" None a)
in (

let body = (let _161_376 = (let _161_366 = (FStar_Syntax_Syntax.bv_to_name a1)
in (let _161_365 = (FStar_Syntax_Syntax.bv_to_name a2)
in (mk_rel a _161_366 _161_365)))
in (let _161_375 = (let _161_374 = (let _161_369 = (let _161_368 = (let _161_367 = (FStar_Syntax_Syntax.bv_to_name a1)
in (FStar_Syntax_Syntax.as_arg _161_367))
in (_161_368)::[])
in (FStar_Syntax_Util.mk_app x _161_369))
in (let _161_373 = (let _161_372 = (let _161_371 = (let _161_370 = (FStar_Syntax_Syntax.bv_to_name a2)
in (FStar_Syntax_Syntax.as_arg _161_370))
in (_161_371)::[])
in (FStar_Syntax_Util.mk_app y _161_372))
in (mk_rel b _161_374 _161_373)))
in (FStar_Syntax_Util.mk_imp _161_376 _161_375)))
in (let _161_377 = (mk_forall a2 body)
in (mk_forall a1 _161_377)))))
end)
end
| FStar_Syntax_Syntax.Tm_arrow ((binder)::binders, comp) -> begin
(

let t = (

let _60_249 = t
in (let _161_381 = (let _161_380 = (let _161_379 = (let _161_378 = (FStar_Syntax_Util.arrow binders comp)
in (FStar_Syntax_Syntax.mk_Total _161_378))
in (((binder)::[]), (_161_379)))
in FStar_Syntax_Syntax.Tm_arrow (_161_380))
in {FStar_Syntax_Syntax.n = _161_381; FStar_Syntax_Syntax.tk = _60_249.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _60_249.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _60_249.FStar_Syntax_Syntax.vars}))
in (mk_rel t x y))
end
| FStar_Syntax_Syntax.Tm_arrow (_60_253) -> begin
(failwith "unhandled arrow")
end
| _60_256 -> begin
(FStar_Syntax_Util.mk_eq t t x y)
end))))
in (

let stronger = (

let wp1 = (FStar_Syntax_Syntax.gen_bv "wp1" None wp_a)
in (

let wp2 = (FStar_Syntax_Syntax.gen_bv "wp2" None wp_a)
in (

let rec mk_stronger = (fun t x y -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (match ((let _161_388 = (FStar_Syntax_Subst.compress t)
in _161_388.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_60_265) -> begin
(FStar_Syntax_Util.mk_imp x y)
end
| FStar_Syntax_Syntax.Tm_app (head, args) when (let _161_389 = (FStar_Syntax_Subst.compress head)
in (FStar_Syntax_Util.is_tuple_constructor _161_389)) -> begin
(

let project = (fun i tuple -> (

let projector = (let _161_395 = (let _161_394 = (FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) FStar_Range.dummyRange)
in (FStar_TypeChecker_Env.lookup_projector env _161_394 i))
in (FStar_Syntax_Syntax.fvar _161_395 (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None))
in (FStar_Syntax_Util.mk_app projector ((((tuple), (None)))::[]))))
in (

let _60_285 = (match ((FStar_List.mapi (fun i _60_278 -> (match (_60_278) with
| (t, q) -> begin
(let _161_399 = (project i x)
in (let _161_398 = (project i y)
in (mk_stronger t _161_399 _161_398)))
end)) args)) with
| [] -> begin
(failwith "Impossible : Empty application when creating stronger relation in DM4F")
end
| (rel0)::rels -> begin
((rel0), (rels))
end)
in (match (_60_285) with
| (rel0, rels) -> begin
(FStar_List.fold_left FStar_Syntax_Util.mk_conj rel0 rels)
end)))
end
| (FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (b, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (b, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(

let bvs = (FStar_List.mapi (fun i _60_317 -> (match (_60_317) with
| (bv, q) -> begin
(let _161_403 = (let _161_402 = (FStar_Util.string_of_int i)
in (Prims.strcat "a" _161_402))
in (FStar_Syntax_Syntax.gen_bv _161_403 None bv.FStar_Syntax_Syntax.sort))
end)) binders)
in (

let args = (FStar_List.map (fun ai -> (let _161_405 = (FStar_Syntax_Syntax.bv_to_name ai)
in (FStar_Syntax_Syntax.as_arg _161_405))) bvs)
in (

let body = (let _161_407 = (FStar_Syntax_Util.mk_app x args)
in (let _161_406 = (FStar_Syntax_Util.mk_app y args)
in (mk_stronger b _161_407 _161_406)))
in (FStar_List.fold_right (fun bv body -> (mk_forall bv body)) bvs body))))
end
| _60_325 -> begin
(failwith "Not a DM elaborated type")
end)))
in (

let body = (let _161_412 = (FStar_Syntax_Util.unascribe wp_a)
in (let _161_411 = (FStar_Syntax_Syntax.bv_to_name wp1)
in (let _161_410 = (FStar_Syntax_Syntax.bv_to_name wp2)
in (mk_stronger _161_412 _161_411 _161_410))))
in (let _161_414 = (let _161_413 = (binders_of_list ((((a), (false)))::(((wp1), (false)))::(((wp2), (false)))::[]))
in (FStar_List.append binders _161_413))
in (FStar_Syntax_Util.abs _161_414 body ret_tot_type))))))
in (

let stronger = (let _161_415 = (mk_lid "stronger")
in (register env _161_415 stronger))
in (

let stronger = (mk_generic_app stronger)
in (

let wp_ite = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let _60_333 = (FStar_Util.prefix gamma)
in (match (_60_333) with
| (wp_args, post) -> begin
(

let k = (FStar_Syntax_Syntax.gen_bv "k" None (Prims.fst post).FStar_Syntax_Syntax.sort)
in (

let equiv = (

let k_tm = (FStar_Syntax_Syntax.bv_to_name k)
in (

let eq = (let _161_416 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst post))
in (mk_rel FStar_Syntax_Util.mk_iff k.FStar_Syntax_Syntax.sort k_tm _161_416))
in (match ((FStar_Syntax_Util.destruct_typ_as_formula eq)) with
| Some (FStar_Syntax_Util.QAll (binders, [], body)) -> begin
(

let k_app = (let _161_417 = (args_of_binders binders)
in (FStar_Syntax_Util.mk_app k_tm _161_417))
in (

let guard_free = (let _161_418 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.guard_free FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _161_418))
in (

let pat = (let _161_420 = (let _161_419 = (FStar_Syntax_Syntax.as_arg k_app)
in (_161_419)::[])
in (FStar_Syntax_Util.mk_app guard_free _161_420))
in (

let pattern_guarded_body = (let _161_426 = (let _161_425 = (let _161_424 = (let _161_423 = (let _161_422 = (let _161_421 = (FStar_Syntax_Syntax.as_arg pat)
in (_161_421)::[])
in (_161_422)::[])
in FStar_Syntax_Syntax.Meta_pattern (_161_423))
in ((body), (_161_424)))
in FStar_Syntax_Syntax.Tm_meta (_161_425))
in (mk _161_426))
in (FStar_Syntax_Util.close_forall binders pattern_guarded_body)))))
end
| _60_348 -> begin
(failwith "Impossible: Expected the equivalence to be a quantified formula")
end)))
in (

let body = (let _161_435 = (let _161_434 = (let _161_433 = (let _161_432 = (FStar_Syntax_Syntax.bv_to_name wp)
in (let _161_431 = (let _161_430 = (args_of_binders wp_args)
in (let _161_429 = (let _161_428 = (let _161_427 = (FStar_Syntax_Syntax.bv_to_name k)
in (FStar_Syntax_Syntax.as_arg _161_427))
in (_161_428)::[])
in (FStar_List.append _161_430 _161_429)))
in (FStar_Syntax_Util.mk_app _161_432 _161_431)))
in (FStar_Syntax_Util.mk_imp equiv _161_433))
in (FStar_Syntax_Util.mk_forall k _161_434))
in (FStar_Syntax_Util.abs gamma _161_435 ret_gtot_type))
in (let _161_437 = (let _161_436 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders _161_436))
in (FStar_Syntax_Util.abs _161_437 body ret_gtot_type)))))
end)))
in (

let wp_ite = (let _161_438 = (mk_lid "wp_ite")
in (register env _161_438 wp_ite))
in (

let wp_ite = (mk_generic_app wp_ite)
in (

let null_wp = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let _60_357 = (FStar_Util.prefix gamma)
in (match (_60_357) with
| (wp_args, post) -> begin
(

let x = (FStar_Syntax_Syntax.gen_bv "x" None FStar_Syntax_Syntax.tun)
in (

let body = (let _161_443 = (let _161_442 = (FStar_All.pipe_left FStar_Syntax_Syntax.bv_to_name (Prims.fst post))
in (let _161_441 = (let _161_440 = (let _161_439 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _161_439))
in (_161_440)::[])
in (FStar_Syntax_Util.mk_app _161_442 _161_441)))
in (FStar_Syntax_Util.mk_forall x _161_443))
in (let _161_446 = (let _161_445 = (let _161_444 = (FStar_Syntax_Syntax.binders_of_list ((a)::[]))
in (FStar_List.append _161_444 gamma))
in (FStar_List.append binders _161_445))
in (FStar_Syntax_Util.abs _161_446 body ret_gtot_type))))
end)))
in (

let null_wp = (let _161_447 = (mk_lid "null_wp")
in (register env _161_447 null_wp))
in (

let null_wp = (mk_generic_app null_wp)
in (

let wp_trivial = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None wp_a)
in (

let body = (let _161_457 = (let _161_456 = (let _161_455 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _161_454 = (let _161_453 = (let _161_450 = (let _161_449 = (let _161_448 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.as_arg _161_448))
in (_161_449)::[])
in (FStar_Syntax_Util.mk_app null_wp _161_450))
in (let _161_452 = (let _161_451 = (FStar_Syntax_Syntax.bv_to_name wp)
in (_161_451)::[])
in (_161_453)::_161_452))
in (_161_455)::_161_454))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _161_456))
in (FStar_Syntax_Util.mk_app stronger _161_457))
in (let _161_459 = (let _161_458 = (FStar_Syntax_Syntax.binders_of_list ((a)::(wp)::[]))
in (FStar_List.append binders _161_458))
in (FStar_Syntax_Util.abs _161_459 body ret_tot_type))))
in (

let wp_trivial = (let _161_460 = (mk_lid "wp_trivial")
in (register env _161_460 wp_trivial))
in (

let wp_trivial = (mk_generic_app wp_trivial)
in (

let _60_368 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(d "End Dijkstra monads for free")
end else begin
()
end
in (

let c = (FStar_Syntax_Subst.close binders)
in (let _161_480 = (let _161_462 = (FStar_ST.read sigelts)
in (FStar_List.rev _161_462))
in (let _161_479 = (

let _60_371 = ed
in (let _161_478 = (let _161_463 = (c wp_if_then_else)
in (([]), (_161_463)))
in (let _161_477 = (let _161_464 = (c wp_ite)
in (([]), (_161_464)))
in (let _161_476 = (let _161_465 = (c stronger)
in (([]), (_161_465)))
in (let _161_475 = (let _161_466 = (c wp_close)
in (([]), (_161_466)))
in (let _161_474 = (let _161_467 = (c wp_assert)
in (([]), (_161_467)))
in (let _161_473 = (let _161_468 = (c wp_assume)
in (([]), (_161_468)))
in (let _161_472 = (let _161_469 = (c null_wp)
in (([]), (_161_469)))
in (let _161_471 = (let _161_470 = (c wp_trivial)
in (([]), (_161_470)))
in {FStar_Syntax_Syntax.qualifiers = _60_371.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = _60_371.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = _60_371.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _60_371.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _60_371.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _60_371.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _60_371.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _60_371.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _161_478; FStar_Syntax_Syntax.ite_wp = _161_477; FStar_Syntax_Syntax.stronger = _161_476; FStar_Syntax_Syntax.close_wp = _161_475; FStar_Syntax_Syntax.assert_p = _161_474; FStar_Syntax_Syntax.assume_p = _161_473; FStar_Syntax_Syntax.null_wp = _161_472; FStar_Syntax_Syntax.trivial = _161_471; FStar_Syntax_Syntax.repr = _60_371.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _60_371.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _60_371.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _60_371.FStar_Syntax_Syntax.actions})))))))))
in ((_161_480), (_161_479))))))))))))))))))))))))))))))))))))))))))))))))
end))))))))))))))))))


type env_ =
env


let get_env : env  ->  FStar_TypeChecker_Env.env = (fun env -> env.env)


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
| N (_60_376) -> begin
_60_376
end))


let ___M____0 = (fun projectee -> (match (projectee) with
| M (_60_379) -> begin
_60_379
end))


type nm_ =
nm


let nm_of_comp : FStar_Syntax_Syntax.comp'  ->  nm = (fun uu___321 -> (match (uu___321) with
| FStar_Syntax_Syntax.Total (t, _60_383) -> begin
N (t)
end
| FStar_Syntax_Syntax.Comp (c) when (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___320 -> (match (uu___320) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| _60_391 -> begin
false
end)))) -> begin
M (c.FStar_Syntax_Syntax.result_typ)
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(let _161_516 = (let _161_515 = (let _161_514 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _161_514))
in (FStar_Util.format1 "[nm_of_comp]: impossible (%s)" _161_515))
in (failwith _161_516))
end
| FStar_Syntax_Syntax.GTotal (_60_395) -> begin
(failwith "[nm_of_comp]: impossible (GTot)")
end))


let string_of_nm : nm  ->  Prims.string = (fun uu___322 -> (match (uu___322) with
| N (t) -> begin
(let _161_519 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "N[%s]" _161_519))
end
| M (t) -> begin
(let _161_520 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "M[%s]" _161_520))
end))


let is_monadic_arrow : FStar_Syntax_Syntax.term'  ->  nm = (fun n -> (match (n) with
| FStar_Syntax_Syntax.Tm_arrow (_60_404, {FStar_Syntax_Syntax.n = n; FStar_Syntax_Syntax.tk = _60_410; FStar_Syntax_Syntax.pos = _60_408; FStar_Syntax_Syntax.vars = _60_406}) -> begin
(nm_of_comp n)
end
| _60_416 -> begin
(failwith "unexpected_argument: [is_monadic_arrow]")
end))


let is_monadic_comp = (fun c -> (match ((nm_of_comp c.FStar_Syntax_Syntax.n)) with
| M (_60_419) -> begin
true
end
| N (_60_422) -> begin
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


let double_star : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun typ -> (

let star_once = (fun typ -> (let _161_532 = (let _161_530 = (let _161_529 = (FStar_Syntax_Syntax.new_bv None typ)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _161_529))
in (_161_530)::[])
in (let _161_531 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _161_532 _161_531))))
in (let _161_533 = (FStar_All.pipe_right typ star_once)
in (FStar_All.pipe_left star_once _161_533))))


let rec mk_star_to_type : (FStar_Syntax_Syntax.term'  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun mk env a -> (let _161_554 = (let _161_553 = (let _161_552 = (let _161_550 = (let _161_549 = (let _161_547 = (star_type' env a)
in (FStar_Syntax_Syntax.null_bv _161_547))
in (let _161_548 = (FStar_Syntax_Syntax.as_implicit false)
in ((_161_549), (_161_548))))
in (_161_550)::[])
in (let _161_551 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_161_552), (_161_551))))
in FStar_Syntax_Syntax.Tm_arrow (_161_553))
in (mk _161_554)))
and star_type' : env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None t.FStar_Syntax_Syntax.pos))
in (

let mk_star_to_type = (mk_star_to_type mk)
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _60_438) -> begin
(

let binders = (FStar_List.map (fun _60_443 -> (match (_60_443) with
| (bv, aqual) -> begin
(let _161_563 = (

let _60_444 = bv
in (let _161_562 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _60_444.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _60_444.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _161_562}))
in ((_161_563), (aqual)))
end)) binders)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_60_448, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (hn, _60_457); FStar_Syntax_Syntax.tk = _60_454; FStar_Syntax_Syntax.pos = _60_452; FStar_Syntax_Syntax.vars = _60_450}) -> begin
(let _161_567 = (let _161_566 = (let _161_565 = (let _161_564 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_GTotal _161_564))
in ((binders), (_161_565)))
in FStar_Syntax_Syntax.Tm_arrow (_161_566))
in (mk _161_567))
end
| _60_464 -> begin
(match ((is_monadic_arrow t.FStar_Syntax_Syntax.n)) with
| N (hn) -> begin
(let _161_571 = (let _161_570 = (let _161_569 = (let _161_568 = (star_type' env hn)
in (FStar_Syntax_Syntax.mk_Total _161_568))
in ((binders), (_161_569)))
in FStar_Syntax_Syntax.Tm_arrow (_161_570))
in (mk _161_571))
end
| M (a) -> begin
(let _161_580 = (let _161_579 = (let _161_578 = (let _161_576 = (let _161_575 = (let _161_574 = (let _161_572 = (mk_star_to_type env a)
in (FStar_Syntax_Syntax.null_bv _161_572))
in (let _161_573 = (FStar_Syntax_Syntax.as_implicit false)
in ((_161_574), (_161_573))))
in (_161_575)::[])
in (FStar_List.append binders _161_576))
in (let _161_577 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in ((_161_578), (_161_577))))
in FStar_Syntax_Syntax.Tm_arrow (_161_579))
in (mk _161_580))
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

let _60_485 = (FStar_Util.string_builder_append strb "{")
in (

let _60_487 = (let _161_594 = (f x)
in (FStar_Util.string_builder_append strb _161_594))
in (

let _60_492 = (FStar_List.iter (fun x -> (

let _60_490 = (FStar_Util.string_builder_append strb ", ")
in (let _161_596 = (f x)
in (FStar_Util.string_builder_append strb _161_596)))) xs)
in (

let _60_494 = (FStar_Util.string_builder_append strb "}")
in (FStar_Util.string_of_string_builder strb))))))
end)))
in (let _161_598 = (FStar_Syntax_Print.term_to_string t)
in (let _161_597 = (string_of_set FStar_Syntax_Print.bv_to_string s)
in (FStar_Util.print2_warning "Dependency found in term %s : %s" _161_598 _161_597)))))
in (

let rec is_non_dependent_arrow = (fun ty n -> (match ((let _161_603 = (FStar_Syntax_Subst.compress ty)
in _161_603.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
if (not ((FStar_Syntax_Util.is_tot_or_gtot_comp c))) then begin
false
end else begin
try
(match (()) with
| () -> begin
(

let non_dependent_or_raise = (fun s ty -> (

let sinter = (let _161_609 = (FStar_Syntax_Free.names ty)
in (FStar_Util.set_intersect _161_609 s))
in if (not ((FStar_Util.set_is_empty sinter))) then begin
(

let _60_511 = (debug ty sinter)
in (Prims.raise Not_found))
end else begin
()
end))
in (

let _60_515 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_60_515) with
| (binders, c) -> begin
(

let s = (FStar_List.fold_left (fun s _60_520 -> (match (_60_520) with
| (bv, _60_519) -> begin
(

let _60_521 = (non_dependent_or_raise s bv.FStar_Syntax_Syntax.sort)
in (FStar_Util.set_add bv s))
end)) FStar_Syntax_Syntax.no_names binders)
in (

let ct = (FStar_Syntax_Util.comp_result c)
in (

let _60_525 = (non_dependent_or_raise s ct)
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
| _60_529 -> begin
(

let _60_530 = (let _161_613 = (FStar_Syntax_Print.term_to_string ty)
in (FStar_Util.print1_warning "Not a dependent arrow : %s" _161_613))
in false)
end))
in (

let rec is_valid_application = (fun head -> (match ((let _161_616 = (FStar_Syntax_Subst.compress head)
in _161_616.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.option_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.either_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.eq2_lid)) || (let _161_617 = (FStar_Syntax_Subst.compress head)
in (FStar_Syntax_Util.is_tuple_constructor _161_617))) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (is_non_dependent_arrow fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty (FStar_List.length args)) -> begin
(

let res = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.env t)
in (match (res.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (_60_540) -> begin
true
end
| _60_543 -> begin
(

let _60_544 = (let _161_618 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.print1_warning "Got a term which might be a non-dependent user-defined data-type %s\n" _161_618))
in false)
end))
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uinst (t, _60_554) -> begin
(is_valid_application t)
end
| _60_558 -> begin
false
end))
in if (is_valid_application head) then begin
(let _161_623 = (let _161_622 = (let _161_621 = (FStar_List.map (fun _60_561 -> (match (_60_561) with
| (t, qual) -> begin
(let _161_620 = (star_type' env t)
in ((_161_620), (qual)))
end)) args)
in ((head), (_161_621)))
in FStar_Syntax_Syntax.Tm_app (_161_622))
in (mk _161_623))
end else begin
(let _161_626 = (let _161_625 = (let _161_624 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)" _161_624))
in FStar_Errors.Err (_161_625))
in (Prims.raise _161_626))
end)))
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_abs (binders, repr, something) -> begin
(

let _60_581 = (FStar_Syntax_Subst.open_term binders repr)
in (match (_60_581) with
| (binders, repr) -> begin
(

let env = (

let _60_582 = env
in (let _161_627 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _161_627; subst = _60_582.subst; tc_const = _60_582.tc_const}))
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

let _60_597 = x
in {FStar_Syntax_Syntax.ppname = _60_597.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _60_597.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (t))))))))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(let _161_630 = (let _161_629 = (let _161_628 = (star_type' env t)
in ((_161_628), (m)))
in FStar_Syntax_Syntax.Tm_meta (_161_629))
in (mk _161_630))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), something) -> begin
(let _161_635 = (let _161_634 = (let _161_633 = (star_type' env e)
in (let _161_632 = (let _161_631 = (star_type' env t)
in FStar_Util.Inl (_161_631))
in ((_161_633), (_161_632), (something))))
in FStar_Syntax_Syntax.Tm_ascribed (_161_634))
in (mk _161_635))
end
| FStar_Syntax_Syntax.Tm_ascribed (_60_610) -> begin
(let _161_638 = (let _161_637 = (let _161_636 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_ascribed is outside of the definition language: %s" _161_636))
in FStar_Errors.Err (_161_637))
in (Prims.raise _161_638))
end
| FStar_Syntax_Syntax.Tm_refine (_60_613) -> begin
(let _161_641 = (let _161_640 = (let _161_639 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_refine is outside of the definition language: %s" _161_639))
in FStar_Errors.Err (_161_640))
in (Prims.raise _161_641))
end
| FStar_Syntax_Syntax.Tm_uinst (_60_616) -> begin
(let _161_644 = (let _161_643 = (let _161_642 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_uinst is outside of the definition language: %s" _161_642))
in FStar_Errors.Err (_161_643))
in (Prims.raise _161_644))
end
| FStar_Syntax_Syntax.Tm_constant (_60_619) -> begin
(let _161_647 = (let _161_646 = (let _161_645 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_constant is outside of the definition language: %s" _161_645))
in FStar_Errors.Err (_161_646))
in (Prims.raise _161_647))
end
| FStar_Syntax_Syntax.Tm_match (_60_622) -> begin
(let _161_650 = (let _161_649 = (let _161_648 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_match is outside of the definition language: %s" _161_648))
in FStar_Errors.Err (_161_649))
in (Prims.raise _161_650))
end
| FStar_Syntax_Syntax.Tm_let (_60_625) -> begin
(let _161_653 = (let _161_652 = (let _161_651 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_let is outside of the definition language: %s" _161_651))
in FStar_Errors.Err (_161_652))
in (Prims.raise _161_653))
end
| FStar_Syntax_Syntax.Tm_uvar (_60_628) -> begin
(let _161_656 = (let _161_655 = (let _161_654 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_uvar is outside of the definition language: %s" _161_654))
in FStar_Errors.Err (_161_655))
in (Prims.raise _161_656))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _161_659 = (let _161_658 = (let _161_657 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Tm_unknown is outside of the definition language: %s" _161_657))
in FStar_Errors.Err (_161_658))
in (Prims.raise _161_659))
end
| FStar_Syntax_Syntax.Tm_delayed (_60_632) -> begin
(failwith "impossible")
end)))))


let is_monadic = (fun uu___324 -> (match (uu___324) with
| None -> begin
(failwith "un-annotated lambda?!")
end
| (Some (FStar_Util.Inl ({FStar_Syntax_Syntax.eff_name = _; FStar_Syntax_Syntax.res_typ = _; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = _}))) | (Some (FStar_Util.Inr (_, flags))) -> begin
(FStar_All.pipe_right flags (FStar_Util.for_some (fun uu___323 -> (match (uu___323) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| _60_654 -> begin
false
end))))
end))


let rec is_C : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match ((let _161_667 = (FStar_Syntax_Subst.compress t)
in _161_667.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) when (FStar_Syntax_Util.is_tuple_constructor head) -> begin
(

let r = (let _161_669 = (let _161_668 = (FStar_List.hd args)
in (Prims.fst _161_668))
in (is_C _161_669))
in if r then begin
(

let _60_665 = if (not ((FStar_List.for_all (fun _60_664 -> (match (_60_664) with
| (h, _60_663) -> begin
(is_C h)
end)) args))) then begin
(failwith "not a C (A * C)")
end else begin
()
end
in true)
end else begin
(

let _60_671 = if (not ((FStar_List.for_all (fun _60_670 -> (match (_60_670) with
| (h, _60_669) -> begin
(not ((is_C h)))
end)) args))) then begin
(failwith "not a C (C * A)")
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

let _60_679 = if (is_C t) then begin
(failwith "not a C (C -> C)")
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
| _60_699 -> begin
false
end))


let mk_return : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let p_type = (mk_star_to_type mk env t)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'" None p_type)
in (

let body = (let _161_685 = (let _161_684 = (let _161_683 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _161_682 = (let _161_681 = (let _161_680 = (FStar_Syntax_Syntax.as_implicit false)
in ((e), (_161_680)))
in (_161_681)::[])
in ((_161_683), (_161_682))))
in FStar_Syntax_Syntax.Tm_app (_161_684))
in (mk _161_685))
in (let _161_687 = (let _161_686 = (FStar_Syntax_Syntax.mk_binder p)
in (_161_686)::[])
in (FStar_Syntax_Util.abs _161_687 body None)))))))


let is_unknown : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun uu___325 -> (match (uu___325) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| _60_711 -> begin
false
end))


let rec check : env  ->  FStar_Syntax_Syntax.term  ->  nm  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e context_nm -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let return_if = (fun _60_721 -> (match (_60_721) with
| (rec_nm, s_e, u_e) -> begin
(

let check = (fun t1 t2 -> if ((not ((is_unknown t2.FStar_Syntax_Syntax.n))) && (not ((let _161_741 = (FStar_TypeChecker_Rel.teq env.env t1 t2)
in (FStar_TypeChecker_Rel.is_trivial _161_741))))) then begin
(let _161_746 = (let _161_745 = (let _161_744 = (FStar_Syntax_Print.term_to_string e)
in (let _161_743 = (FStar_Syntax_Print.term_to_string t1)
in (let _161_742 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check]: the expression [%s] has type [%s] but should have type [%s]" _161_744 _161_743 _161_742))))
in FStar_Errors.Err (_161_745))
in (Prims.raise _161_746))
end else begin
()
end)
in (match (((rec_nm), (context_nm))) with
| ((N (t1), N (t2))) | ((M (t1), M (t2))) -> begin
(

let _60_733 = (check t1 t2)
in ((rec_nm), (s_e), (u_e)))
end
| (N (t1), M (t2)) -> begin
(

let _60_740 = (check t1 t2)
in (let _161_747 = (mk_return env t1 s_e)
in ((M (t1)), (_161_747), (u_e))))
end
| (M (t1), N (t2)) -> begin
(let _161_752 = (let _161_751 = (let _161_750 = (FStar_Syntax_Print.term_to_string e)
in (let _161_749 = (FStar_Syntax_Print.term_to_string t1)
in (let _161_748 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format3 "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]" _161_750 _161_749 _161_748))))
in FStar_Errors.Err (_161_751))
in (Prims.raise _161_752))
end))
end))
in (

let ensure_m = (fun env e2 -> (

let strip_m = (fun uu___326 -> (match (uu___326) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _60_757 -> begin
(failwith "impossible")
end))
in (match (context_nm) with
| N (t) -> begin
(let _161_762 = (let _161_761 = (let _161_760 = (let _161_759 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren\'t : " _161_759))
in ((_161_760), (e2.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (_161_761))
in (Prims.raise _161_762))
end
| M (_60_762) -> begin
(let _161_763 = (check env e2 context_nm)
in (strip_m _161_763))
end)))
in (match ((let _161_764 = (FStar_Syntax_Subst.compress e)
in _161_764.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
(let _161_765 = (infer env e)
in (return_if _161_765))
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
| FStar_Syntax_Syntax.Tm_let (_60_813) -> begin
(let _161_773 = (let _161_772 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_let %s" _161_772))
in (failwith _161_773))
end
| FStar_Syntax_Syntax.Tm_type (_60_816) -> begin
(failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_60_819) -> begin
(failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_60_822) -> begin
(let _161_775 = (let _161_774 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_refine %s" _161_774))
in (failwith _161_775))
end
| FStar_Syntax_Syntax.Tm_uvar (_60_825) -> begin
(let _161_777 = (let _161_776 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_uvar %s" _161_776))
in (failwith _161_777))
end
| FStar_Syntax_Syntax.Tm_delayed (_60_828) -> begin
(failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _161_782 = (let _161_781 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[check]: Tm_unknown %s" _161_781))
in (failwith _161_782))
end)))))
and infer : env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e.FStar_Syntax_Syntax.pos))
in (

let normalize = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.env)
in (match ((let _161_788 = (FStar_Syntax_Subst.compress e)
in _161_788.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
(failwith "I failed to open a binder... boo")
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

let _60_848 = env
in (let _161_789 = (FStar_TypeChecker_Env.push_binders env.env binders)
in {env = _161_789; subst = _60_848.subst; tc_const = _60_848.tc_const}))
in (

let s_binders = (FStar_List.map (fun _60_853 -> (match (_60_853) with
| (bv, qual) -> begin
(

let sort = (star_type' env bv.FStar_Syntax_Syntax.sort)
in (((

let _60_855 = bv
in {FStar_Syntax_Syntax.ppname = _60_855.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _60_855.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})), (qual)))
end)) binders)
in (

let _60_877 = (FStar_List.fold_left (fun _60_860 _60_863 -> (match (((_60_860), (_60_863))) with
| ((env, acc), (bv, qual)) -> begin
(

let c = bv.FStar_Syntax_Syntax.sort
in if (is_C c) then begin
(

let xw = (let _161_793 = (star_type' env c)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "^w") None _161_793))
in (

let x = (

let _60_866 = bv
in (let _161_795 = (let _161_794 = (FStar_Syntax_Syntax.bv_to_name xw)
in (trans_F_ env c _161_794))
in {FStar_Syntax_Syntax.ppname = _60_866.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _60_866.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _161_795}))
in (

let env = (

let _60_869 = env
in (let _161_799 = (let _161_798 = (let _161_797 = (let _161_796 = (FStar_Syntax_Syntax.bv_to_name xw)
in ((bv), (_161_796)))
in FStar_Syntax_Syntax.NT (_161_797))
in (_161_798)::env.subst)
in {env = _60_869.env; subst = _161_799; tc_const = _60_869.tc_const}))
in (let _161_803 = (let _161_802 = (FStar_Syntax_Syntax.mk_binder x)
in (let _161_801 = (let _161_800 = (FStar_Syntax_Syntax.mk_binder xw)
in (_161_800)::acc)
in (_161_802)::_161_801))
in ((env), (_161_803))))))
end else begin
(

let x = (

let _60_872 = bv
in (let _161_804 = (star_type' env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _60_872.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _60_872.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _161_804}))
in (let _161_806 = (let _161_805 = (FStar_Syntax_Syntax.mk_binder x)
in (_161_805)::acc)
in ((env), (_161_806))))
end)
end)) ((env), ([])) binders)
in (match (_60_877) with
| (env, u_binders) -> begin
(

let u_binders = (FStar_List.rev u_binders)
in (

let _60_887 = (

let check_what = if (is_monadic what) then begin
check_m
end else begin
check_n
end
in (

let _60_883 = (check_what env body)
in (match (_60_883) with
| (t, s_body, u_body) -> begin
(let _161_812 = (let _161_811 = if (is_monadic what) then begin
M (t)
end else begin
N (t)
end
in (comp_of_nm _161_811))
in ((_161_812), (s_body), (u_body)))
end)))
in (match (_60_887) with
| (comp, s_body, u_body) -> begin
(

let t = (FStar_Syntax_Util.arrow binders comp)
in (

let s_what = (match (what) with
| None -> begin
None
end
| Some (FStar_Util.Inl (lc)) -> begin
if (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun uu___327 -> (match (uu___327) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| _60_896 -> begin
false
end)))) then begin
(

let double_starred_comp = (let _161_816 = (let _161_815 = (let _161_814 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.comp_result _161_814))
in (FStar_All.pipe_left double_star _161_815))
in (FStar_Syntax_Syntax.mk_Total _161_816))
in (

let flags = (FStar_List.filter (fun uu___328 -> (match (uu___328) with
| FStar_Syntax_Syntax.CPS -> begin
false
end
| _60_901 -> begin
true
end)) lc.FStar_Syntax_Syntax.cflags)
in (let _161_820 = (let _161_819 = (let _161_818 = (FStar_Syntax_Util.comp_set_flags double_starred_comp flags)
in (FStar_Syntax_Util.lcomp_of_comp _161_818))
in FStar_Util.Inl (_161_819))
in Some (_161_820))))
end else begin
Some (FStar_Util.Inl ((

let _60_903 = lc
in {FStar_Syntax_Syntax.eff_name = _60_903.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _60_903.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _60_903.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _60_905 -> (match (()) with
| () -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let result_typ = (star_type' env (FStar_Syntax_Util.comp_result c))
in (FStar_Syntax_Util.set_result_typ c result_typ)))
end))})))
end
end
| Some (FStar_Util.Inr (lid, flags)) -> begin
(let _161_826 = (let _161_825 = if (FStar_All.pipe_right flags (FStar_Util.for_some (fun uu___329 -> (match (uu___329) with
| FStar_Syntax_Syntax.CPS -> begin
true
end
| _60_916 -> begin
false
end)))) then begin
(let _161_824 = (FStar_List.filter (fun uu___330 -> (match (uu___330) with
| FStar_Syntax_Syntax.CPS -> begin
false
end
| _60_920 -> begin
true
end)) flags)
in ((FStar_Syntax_Const.effect_Tot_lid), (_161_824)))
end else begin
((lid), (flags))
end
in FStar_Util.Inr (_161_825))
in Some (_161_826))
end)
in (

let _60_925 = (

let comp = (let _161_828 = (is_monadic what)
in (let _161_827 = (FStar_Syntax_Subst.subst env.subst s_body)
in (trans_G env (FStar_Syntax_Util.comp_result comp) _161_828 _161_827)))
in (let _161_829 = (FStar_Syntax_Util.ascribe u_body (FStar_Util.Inr (comp)))
in ((_161_829), (Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp comp)))))))
in (match (_60_925) with
| (u_body, u_what) -> begin
(

let s_body = (FStar_Syntax_Subst.close s_binders s_body)
in (

let s_binders = (FStar_Syntax_Subst.close_binders s_binders)
in (

let s_term = (mk (FStar_Syntax_Syntax.Tm_abs (((s_binders), (s_body), (s_what)))))
in (

let u_body = (FStar_Syntax_Subst.close u_binders u_body)
in (

let u_binders = (FStar_Syntax_Subst.close_binders u_binders)
in (

let u_term = (mk (FStar_Syntax_Syntax.Tm_abs (((u_binders), (u_body), (u_what)))))
in ((N (t)), (s_term), (u_term))))))))
end))))
end)))
end)))))))
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = {FStar_Syntax_Syntax.v = lid; FStar_Syntax_Syntax.ty = _60_939; FStar_Syntax_Syntax.p = _60_937}; FStar_Syntax_Syntax.fv_delta = _60_935; FStar_Syntax_Syntax.fv_qual = _60_933}) -> begin
(

let _60_947 = (FStar_TypeChecker_Env.lookup_lid env.env lid)
in (match (_60_947) with
| (_60_945, t) -> begin
(

let txt = (FStar_Ident.text_of_lid lid)
in (let _161_831 = (let _161_830 = (normalize t)
in N (_161_830))
in ((_161_831), (e), (e))))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _60_956 = (check_n env head)
in (match (_60_956) with
| (t_head, s_head, u_head) -> begin
(

let is_arrow = (fun t -> (match ((let _161_834 = (FStar_Syntax_Subst.compress t)
in _161_834.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_60_960) -> begin
true
end
| _60_963 -> begin
false
end))
in (

let rec flatten = (fun t -> (match ((let _161_837 = (FStar_Syntax_Subst.compress t)
in _161_837.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (t, _60_975); FStar_Syntax_Syntax.tk = _60_972; FStar_Syntax_Syntax.pos = _60_970; FStar_Syntax_Syntax.vars = _60_968}) when (is_arrow t) -> begin
(

let _60_983 = (flatten t)
in (match (_60_983) with
| (binders', comp) -> begin
(((FStar_List.append binders binders')), (comp))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
((binders), (comp))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, _60_990, _60_992) -> begin
(flatten e)
end
| _60_996 -> begin
(let _161_840 = (let _161_839 = (let _161_838 = (FStar_Syntax_Print.term_to_string t_head)
in (FStar_Util.format1 "%s: not a function type" _161_838))
in FStar_Errors.Err (_161_839))
in (Prims.raise _161_840))
end))
in (

let _60_999 = (flatten t_head)
in (match (_60_999) with
| (binders, comp) -> begin
(

let n = (FStar_List.length binders)
in (

let n' = (FStar_List.length args)
in (

let _60_1002 = if ((FStar_List.length binders) < (FStar_List.length args)) then begin
(let _161_845 = (let _161_844 = (let _161_843 = (FStar_Util.string_of_int n)
in (let _161_842 = (FStar_Util.string_of_int (n' - n))
in (let _161_841 = (FStar_Util.string_of_int n)
in (FStar_Util.format3 "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments." _161_843 _161_842 _161_841))))
in FStar_Errors.Err (_161_844))
in (Prims.raise _161_845))
end else begin
()
end
in (

let _60_1006 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (_60_1006) with
| (binders, comp) -> begin
(

let rec final_type = (fun subst _60_1011 args -> (match (_60_1011) with
| (binders, comp) -> begin
(match (((binders), (args))) with
| ([], []) -> begin
(let _161_853 = (let _161_852 = (FStar_Syntax_Subst.subst_comp subst comp)
in _161_852.FStar_Syntax_Syntax.n)
in (nm_of_comp _161_853))
end
| (binders, []) -> begin
(match ((let _161_856 = (let _161_855 = (let _161_854 = (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))))
in (FStar_Syntax_Subst.subst subst _161_854))
in (FStar_Syntax_Subst.compress _161_855))
in _161_856.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(let _161_860 = (let _161_859 = (let _161_858 = (let _161_857 = (FStar_Syntax_Subst.close_comp binders comp)
in ((binders), (_161_857)))
in FStar_Syntax_Syntax.Tm_arrow (_161_858))
in (mk _161_859))
in N (_161_860))
end
| _60_1024 -> begin
(failwith "wat?")
end)
end
| ([], (_60_1029)::_60_1027) -> begin
(failwith "just checked that?!")
end
| (((bv, _60_1035))::binders, ((arg, _60_1041))::args) -> begin
(final_type ((FStar_Syntax_Syntax.NT (((bv), (arg))))::subst) ((binders), (comp)) args)
end)
end))
in (

let final_type = (final_type [] ((binders), (comp)) args)
in (

let _60_1049 = (FStar_List.splitAt n' binders)
in (match (_60_1049) with
| (binders, _60_1048) -> begin
(

let _60_1070 = (let _161_867 = (FStar_List.map2 (fun _60_1053 _60_1056 -> (match (((_60_1053), (_60_1056))) with
| ((bv, _60_1052), (arg, q)) -> begin
(match ((let _161_863 = (FStar_Syntax_Subst.compress bv.FStar_Syntax_Syntax.sort)
in _161_863.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_60_1058) -> begin
(

let arg = ((arg), (q))
in ((arg), ((arg)::[])))
end
| _60_1062 -> begin
(

let _60_1067 = (check_n env arg)
in (match (_60_1067) with
| (_60_1064, s_arg, u_arg) -> begin
(let _161_866 = if (is_C bv.FStar_Syntax_Syntax.sort) then begin
(let _161_865 = (let _161_864 = (FStar_Syntax_Subst.subst env.subst s_arg)
in ((_161_864), (q)))
in (_161_865)::(((u_arg), (q)))::[])
end else begin
(((u_arg), (q)))::[]
end
in ((((s_arg), (q))), (_161_866)))
end))
end)
end)) binders args)
in (FStar_List.split _161_867))
in (match (_60_1070) with
| (s_args, u_args) -> begin
(

let u_args = (FStar_List.flatten u_args)
in (let _161_869 = (mk (FStar_Syntax_Syntax.Tm_app (((s_head), (s_args)))))
in (let _161_868 = (mk (FStar_Syntax_Syntax.Tm_app (((u_head), (u_args)))))
in ((final_type), (_161_869), (_161_868)))))
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
(let _161_871 = (let _161_870 = (env.tc_const c)
in N (_161_870))
in ((_161_871), (e), (e)))
end
| FStar_Syntax_Syntax.Tm_let (_60_1101) -> begin
(let _161_873 = (let _161_872 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_let %s" _161_872))
in (failwith _161_873))
end
| FStar_Syntax_Syntax.Tm_type (_60_1104) -> begin
(failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_arrow (_60_1107) -> begin
(failwith "impossible (stratified)")
end
| FStar_Syntax_Syntax.Tm_refine (_60_1110) -> begin
(let _161_875 = (let _161_874 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_refine %s" _161_874))
in (failwith _161_875))
end
| FStar_Syntax_Syntax.Tm_uvar (_60_1113) -> begin
(let _161_877 = (let _161_876 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_uvar %s" _161_876))
in (failwith _161_877))
end
| FStar_Syntax_Syntax.Tm_delayed (_60_1116) -> begin
(failwith "impossible (compressed)")
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _161_882 = (let _161_881 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "[infer]: Tm_unknown %s" _161_881))
in (failwith _161_882))
end))))
and mk_match : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))  ->  (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e0 branches f -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None e0.FStar_Syntax_Syntax.pos))
in (

let _60_1129 = (check_n env e0)
in (match (_60_1129) with
| (_60_1126, s_e0, u_e0) -> begin
(

let _60_1146 = (let _161_898 = (FStar_List.map (fun b -> (match ((FStar_Syntax_Subst.open_branch b)) with
| (pat, None, body) -> begin
(

let env = (

let _60_1135 = env
in (let _161_897 = (let _161_896 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env.env _161_896))
in {env = _161_897; subst = _60_1135.subst; tc_const = _60_1135.tc_const}))
in (

let _60_1141 = (f env body)
in (match (_60_1141) with
| (nm, s_body, u_body) -> begin
((nm), (((pat), (None), (((s_body), (u_body), (body))))))
end)))
end
| _60_1143 -> begin
(Prims.raise (FStar_Errors.Err ("No when clauses in the definition language")))
end)) branches)
in (FStar_List.split _161_898))
in (match (_60_1146) with
| (nms, branches) -> begin
(

let t1 = (match ((FStar_List.hd nms)) with
| (M (t1)) | (N (t1)) -> begin
t1
end)
in (

let has_m = (FStar_List.existsb (fun uu___331 -> (match (uu___331) with
| M (_60_1153) -> begin
true
end
| _60_1156 -> begin
false
end)) nms)
in (

let _60_1190 = (let _161_902 = (FStar_List.map2 (fun nm _60_1165 -> (match (_60_1165) with
| (pat, guard, (s_body, u_body, original_body)) -> begin
(match (((nm), (has_m))) with
| ((N (t2), false)) | ((M (t2), true)) -> begin
((nm), (((pat), (guard), (s_body))), (((pat), (guard), (u_body))))
end
| (N (t2), true) -> begin
(

let _60_1181 = (check env original_body (M (t2)))
in (match (_60_1181) with
| (_60_1178, s_body, u_body) -> begin
((M (t2)), (((pat), (guard), (s_body))), (((pat), (guard), (u_body))))
end))
end
| (M (_60_1183), false) -> begin
(failwith "impossible")
end)
end)) nms branches)
in (FStar_List.unzip3 _161_902))
in (match (_60_1190) with
| (nms, s_branches, u_branches) -> begin
if has_m then begin
(

let p_type = (mk_star_to_type mk env t1)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" None p_type)
in (

let s_branches = (FStar_List.map (fun _60_1196 -> (match (_60_1196) with
| (pat, guard, s_body) -> begin
(

let s_body = (let _161_909 = (let _161_908 = (let _161_907 = (let _161_906 = (let _161_905 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _161_904 = (FStar_Syntax_Syntax.as_implicit false)
in ((_161_905), (_161_904))))
in (_161_906)::[])
in ((s_body), (_161_907)))
in FStar_Syntax_Syntax.Tm_app (_161_908))
in (mk _161_909))
in ((pat), (guard), (s_body)))
end)) s_branches)
in (

let s_branches = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let s_e = (let _161_912 = (let _161_910 = (FStar_Syntax_Syntax.mk_binder p)
in (_161_910)::[])
in (let _161_911 = (mk (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches)))))
in (FStar_Syntax_Util.abs _161_912 _161_911 None)))
in (

let t1_star = (let _161_916 = (let _161_914 = (let _161_913 = (FStar_Syntax_Syntax.new_bv None p_type)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _161_913))
in (_161_914)::[])
in (let _161_915 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _161_916 _161_915)))
in (let _161_918 = (mk (FStar_Syntax_Syntax.Tm_ascribed (((s_e), (FStar_Util.Inl (t1_star)), (None)))))
in (let _161_917 = (mk (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches)))))
in ((M (t1)), (_161_918), (_161_917)))))))))))
end else begin
(

let s_branches = (FStar_List.map FStar_Syntax_Subst.close_branch s_branches)
in (

let u_branches = (FStar_List.map FStar_Syntax_Subst.close_branch u_branches)
in (

let t1_star = t1
in (let _161_923 = (let _161_921 = (let _161_920 = (let _161_919 = (mk (FStar_Syntax_Syntax.Tm_match (((s_e0), (s_branches)))))
in ((_161_919), (FStar_Util.Inl (t1_star)), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (_161_920))
in (mk _161_921))
in (let _161_922 = (mk (FStar_Syntax_Syntax.Tm_match (((u_e0), (u_branches)))))
in ((N (t1)), (_161_923), (_161_922)))))))
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

let x_binders = (let _161_943 = (FStar_Syntax_Syntax.mk_binder x)
in (_161_943)::[])
in (

let _60_1218 = (FStar_Syntax_Subst.open_term x_binders e2)
in (match (_60_1218) with
| (x_binders, e2) -> begin
(match ((infer env e1)) with
| (N (t1), s_e1, u_e1) -> begin
(

let u_binding = if (is_C t1) then begin
(

let _60_1224 = binding
in (let _161_945 = (let _161_944 = (FStar_Syntax_Subst.subst env.subst s_e1)
in (trans_F_ env t1 _161_944))
in {FStar_Syntax_Syntax.lbname = _60_1224.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _60_1224.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _161_945; FStar_Syntax_Syntax.lbeff = _60_1224.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _60_1224.FStar_Syntax_Syntax.lbdef}))
end else begin
binding
end
in (

let env = (

let _60_1227 = env
in (let _161_946 = (FStar_TypeChecker_Env.push_bv env.env (

let _60_1229 = x
in {FStar_Syntax_Syntax.ppname = _60_1229.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _60_1229.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _161_946; subst = _60_1227.subst; tc_const = _60_1227.tc_const}))
in (

let _60_1235 = (proceed env e2)
in (match (_60_1235) with
| (nm_rec, s_e2, u_e2) -> begin
(

let s_binding = (

let _60_1236 = binding
in (let _161_947 = (star_type' env binding.FStar_Syntax_Syntax.lbtyp)
in {FStar_Syntax_Syntax.lbname = _60_1236.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _60_1236.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _161_947; FStar_Syntax_Syntax.lbeff = _60_1236.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _60_1236.FStar_Syntax_Syntax.lbdef}))
in (let _161_955 = (let _161_950 = (let _161_949 = (let _161_948 = (FStar_Syntax_Subst.close x_binders s_e2)
in ((((false), (((

let _60_1239 = s_binding
in {FStar_Syntax_Syntax.lbname = _60_1239.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _60_1239.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _60_1239.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _60_1239.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = s_e1}))::[]))), (_161_948)))
in FStar_Syntax_Syntax.Tm_let (_161_949))
in (mk _161_950))
in (let _161_954 = (let _161_953 = (let _161_952 = (let _161_951 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _60_1241 = u_binding
in {FStar_Syntax_Syntax.lbname = _60_1241.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _60_1241.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _60_1241.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _60_1241.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_161_951)))
in FStar_Syntax_Syntax.Tm_let (_161_952))
in (mk _161_953))
in ((nm_rec), (_161_955), (_161_954)))))
end))))
end
| (M (t1), s_e1, u_e1) -> begin
(

let u_binding = (

let _60_1248 = binding
in {FStar_Syntax_Syntax.lbname = _60_1248.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _60_1248.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.lbdef = _60_1248.FStar_Syntax_Syntax.lbdef})
in (

let env = (

let _60_1251 = env
in (let _161_956 = (FStar_TypeChecker_Env.push_bv env.env (

let _60_1253 = x
in {FStar_Syntax_Syntax.ppname = _60_1253.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _60_1253.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in {env = _161_956; subst = _60_1251.subst; tc_const = _60_1251.tc_const}))
in (

let _60_1259 = (ensure_m env e2)
in (match (_60_1259) with
| (t2, s_e2, u_e2) -> begin
(

let p_type = (mk_star_to_type mk env t2)
in (

let p = (FStar_Syntax_Syntax.gen_bv "p\'\'" None p_type)
in (

let s_e2 = (let _161_962 = (let _161_961 = (let _161_960 = (let _161_959 = (let _161_958 = (FStar_Syntax_Syntax.bv_to_name p)
in (let _161_957 = (FStar_Syntax_Syntax.as_implicit false)
in ((_161_958), (_161_957))))
in (_161_959)::[])
in ((s_e2), (_161_960)))
in FStar_Syntax_Syntax.Tm_app (_161_961))
in (mk _161_962))
in (

let s_e2 = (FStar_Syntax_Util.abs x_binders s_e2 None)
in (

let body = (let _161_967 = (let _161_966 = (let _161_965 = (let _161_964 = (let _161_963 = (FStar_Syntax_Syntax.as_implicit false)
in ((s_e2), (_161_963)))
in (_161_964)::[])
in ((s_e1), (_161_965)))
in FStar_Syntax_Syntax.Tm_app (_161_966))
in (mk _161_967))
in (let _161_974 = (let _161_969 = (let _161_968 = (FStar_Syntax_Syntax.mk_binder p)
in (_161_968)::[])
in (FStar_Syntax_Util.abs _161_969 body None))
in (let _161_973 = (let _161_972 = (let _161_971 = (let _161_970 = (FStar_Syntax_Subst.close x_binders u_e2)
in ((((false), (((

let _60_1265 = u_binding
in {FStar_Syntax_Syntax.lbname = _60_1265.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _60_1265.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _60_1265.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _60_1265.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = u_e1}))::[]))), (_161_970)))
in FStar_Syntax_Syntax.Tm_let (_161_971))
in (mk _161_972))
in ((M (t2)), (_161_974), (_161_973)))))))))
end))))
end)
end)))))))
and check_n : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _161_977 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in N (_161_977))
in (match ((check env e mn)) with
| (N (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _60_1276 -> begin
(failwith "[check_n]: impossible")
end)))
and check_m : env_  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env e -> (

let mn = (let _161_980 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None e.FStar_Syntax_Syntax.pos)
in M (_161_980))
in (match ((check env e mn)) with
| (M (t), s_e, u_e) -> begin
((t), (s_e), (u_e))
end
| _60_1286 -> begin
(failwith "[check_m]: impossible")
end)))
and comp_of_nm : nm_  ->  FStar_Syntax_Syntax.comp = (fun nm -> (match (nm) with
| N (t) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| M (t) -> begin
(mk_M t)
end))
and mk_M : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun t -> (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_unknown)::[]; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.monadic_lid; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.CPS)::(FStar_Syntax_Syntax.TOTAL)::[]}))
and type_of_comp : (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.typ = (fun t -> (FStar_Syntax_Util.comp_result t))
and trans_F_ : env_  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> (

let _60_1297 = if (not ((is_C c))) then begin
(failwith "not a C")
end else begin
()
end
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None c.FStar_Syntax_Syntax.pos))
in (match ((let _161_989 = (FStar_Syntax_Subst.compress c)
in _161_989.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let _60_1307 = (FStar_Syntax_Util.head_and_args wp)
in (match (_60_1307) with
| (wp_head, wp_args) -> begin
(

let _60_1308 = if ((not (((FStar_List.length wp_args) = (FStar_List.length args)))) || (not ((let _161_990 = (FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length wp_args) FStar_Range.dummyRange)
in (FStar_Syntax_Util.is_constructor wp_head _161_990))))) then begin
(failwith "mismatch")
end else begin
()
end
in (let _161_1000 = (let _161_999 = (let _161_998 = (FStar_List.map2 (fun _60_1312 _60_1315 -> (match (((_60_1312), (_60_1315))) with
| ((arg, q), (wp_arg, q')) -> begin
(

let print_implicit = (fun q -> if (FStar_Syntax_Syntax.is_implicit q) then begin
"implicit"
end else begin
"explicit"
end)
in (

let _60_1318 = if (q <> q') then begin
(let _161_996 = (print_implicit q)
in (let _161_995 = (print_implicit q')
in (FStar_Util.print2_warning "Incoherent implicit qualifiers %b %b" _161_996 _161_995)))
end else begin
()
end
in (let _161_997 = (trans_F_ env arg wp_arg)
in ((_161_997), (q)))))
end)) args wp_args)
in ((head), (_161_998)))
in FStar_Syntax_Syntax.Tm_app (_161_999))
in (mk _161_1000)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(

let binders = (FStar_Syntax_Util.name_binders binders)
in (

let _60_1327 = (FStar_Syntax_Subst.open_comp binders comp)
in (match (_60_1327) with
| (binders_orig, comp) -> begin
(

let _60_1336 = (let _161_1010 = (FStar_List.map (fun _60_1330 -> (match (_60_1330) with
| (bv, q) -> begin
(

let h = bv.FStar_Syntax_Syntax.sort
in if (is_C h) then begin
(

let w' = (let _161_1002 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-w\'") None _161_1002))
in (let _161_1008 = (let _161_1007 = (let _161_1006 = (let _161_1005 = (let _161_1004 = (let _161_1003 = (FStar_Syntax_Syntax.bv_to_name w')
in (trans_F_ env h _161_1003))
in (FStar_Syntax_Syntax.null_bv _161_1004))
in ((_161_1005), (q)))
in (_161_1006)::[])
in (((w'), (q)))::_161_1007)
in ((w'), (_161_1008))))
end else begin
(

let x = (let _161_1009 = (star_type' env h)
in (FStar_Syntax_Syntax.gen_bv (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "-x") None _161_1009))
in ((x), ((((x), (q)))::[])))
end)
end)) binders_orig)
in (FStar_List.split _161_1010))
in (match (_60_1336) with
| (bvs, binders) -> begin
(

let binders = (FStar_List.flatten binders)
in (

let comp = (let _161_1012 = (let _161_1011 = (FStar_Syntax_Syntax.binders_of_list bvs)
in (FStar_Syntax_Util.rename_binders binders_orig _161_1011))
in (FStar_Syntax_Subst.subst_comp _161_1012 comp))
in (

let app = (let _161_1018 = (let _161_1017 = (let _161_1016 = (FStar_List.map (fun bv -> (let _161_1015 = (FStar_Syntax_Syntax.bv_to_name bv)
in (let _161_1014 = (FStar_Syntax_Syntax.as_implicit false)
in ((_161_1015), (_161_1014))))) bvs)
in ((wp), (_161_1016)))
in FStar_Syntax_Syntax.Tm_app (_161_1017))
in (mk _161_1018))
in (

let comp = (let _161_1020 = (type_of_comp comp)
in (let _161_1019 = (is_monadic_comp comp)
in (trans_G env _161_1020 _161_1019 app)))
in (FStar_Syntax_Util.arrow binders comp)))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, _60_1344, _60_1346) -> begin
(trans_F_ env e wp)
end
| _60_1350 -> begin
(failwith "impossible trans_F_")
end))))
and trans_G : env_  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env h is_monadic wp -> (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None h.FStar_Syntax_Syntax.pos))
in if is_monadic then begin
(let _161_1031 = (let _161_1030 = (star_type' env h)
in (let _161_1029 = (let _161_1028 = (let _161_1027 = (FStar_Syntax_Syntax.as_implicit false)
in ((wp), (_161_1027)))
in (_161_1028)::[])
in {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_unknown)::[]; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _161_1030; FStar_Syntax_Syntax.effect_args = _161_1029; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp _161_1031))
end else begin
(let _161_1032 = (trans_F_ env h wp)
in (FStar_Syntax_Syntax.mk_Total _161_1032))
end))


let n : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]))


let star_type : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (let _161_1039 = (n env.env t)
in (star_type' env _161_1039)))


let star_expr : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun env t -> (let _161_1044 = (n env.env t)
in (check_n env _161_1044)))


let trans_F : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env c wp -> (let _161_1052 = (n env.env c)
in (let _161_1051 = (n env.env wp)
in (trans_F_ env _161_1052 _161_1051))))




