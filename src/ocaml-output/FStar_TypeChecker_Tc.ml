
open Prims

let set_hint_correlator : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env = (fun env se -> (match ((FStar_Options.reuse_hint_for ())) with
| Some (l) -> begin
(

let lid = (let _159_5 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_add_suffix _159_5 l))
in (

let _61_19 = env
in {FStar_TypeChecker_Env.solver = _61_19.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _61_19.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _61_19.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _61_19.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _61_19.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _61_19.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _61_19.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _61_19.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _61_19.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _61_19.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _61_19.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _61_19.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _61_19.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _61_19.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _61_19.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _61_19.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _61_19.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _61_19.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _61_19.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _61_19.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _61_19.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _61_19.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _61_19.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), ((Prims.parse_int "0"))))}))
end
| None -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (

let lid = (match (lids) with
| [] -> begin
(let _159_8 = (FStar_TypeChecker_Env.current_module env)
in (let _159_7 = (let _159_6 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_right _159_6 FStar_Util.string_of_int))
in (FStar_Ident.lid_add_suffix _159_8 _159_7)))
end
| (l)::_61_25 -> begin
l
end)
in (

let _61_29 = env
in {FStar_TypeChecker_Env.solver = _61_29.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _61_29.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _61_29.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _61_29.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _61_29.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _61_29.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _61_29.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _61_29.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _61_29.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _61_29.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _61_29.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _61_29.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _61_29.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _61_29.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _61_29.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _61_29.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _61_29.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _61_29.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _61_29.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _61_29.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _61_29.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _61_29.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _61_29.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), ((Prims.parse_int "0"))))})))
end))


let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_Options.log_types ()) && (not ((let _159_11 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _159_11))))))


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let _61_38 = (FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k)
in (match (_61_38) with
| (t, c, g) -> begin
(

let _61_39 = (FStar_ST.op_Colon_Equals t.FStar_Syntax_Syntax.tk (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)))
in (

let _61_41 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t))
end)))


let recheck_debug : Prims.string  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s env t -> (

let _61_46 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _159_24 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Term has been %s-transformed to:\n%s\n----------\n" s _159_24))
end else begin
()
end
in (

let _61_53 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (_61_53) with
| (t', _61_50, _61_52) -> begin
(

let _61_54 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _159_25 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print1 "Re-checked; got:\n%s\n----------\n" _159_25))
end else begin
()
end
in t)
end))))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _159_32 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _159_32)))


let check_nogen = (fun env t k -> (

let t = (tc_check_trivial_guard env t k)
in (let _159_36 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (([]), (_159_36)))))


let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let _61_69 = (FStar_TypeChecker_TcTerm.tc_binders env tps)
in (match (_61_69) with
| (tps, env, g, us) -> begin
(

let _61_70 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in ((tps), (env), (us)))
end)))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (

let fail = (fun _61_76 -> (match (()) with
| () -> begin
(let _159_51 = (let _159_50 = (let _159_49 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in ((_159_49), ((FStar_Ident.range_of_lid m))))
in FStar_Syntax_Syntax.Error (_159_50))
in (Prims.raise _159_51))
end))
in (

let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _61_89))::((wp, _61_85))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _61_93 -> begin
(fail ())
end))
end
| _61_95 -> begin
(fail ())
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let _61_102 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_61_102) with
| (uvs, c) -> begin
((uvs), ([]), (c))
end))
end
| _61_104 -> begin
(

let t' = (FStar_Syntax_Util.arrow binders c)
in (

let _61_108 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_61_108) with
| (uvs, t') -> begin
(match ((let _159_58 = (FStar_Syntax_Subst.compress t')
in _159_58.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
((uvs), (binders), (c))
end
| _61_114 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))


let rec tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (

let _61_117 = ()
in (

let _61_122 = (FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_61_122) with
| (effect_params_un, signature_un, opening) -> begin
(

let _61_127 = (tc_tparams env0 effect_params_un)
in (match (_61_127) with
| (effect_params, env, _61_126) -> begin
(

let _61_131 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (_61_131) with
| (signature, _61_130) -> begin
(

let ed = (

let _61_132 = ed
in {FStar_Syntax_Syntax.qualifiers = _61_132.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = _61_132.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = _61_132.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _61_132.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _61_132.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _61_132.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _61_132.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _61_132.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _61_132.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _61_132.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _61_132.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _61_132.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _61_132.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _61_132.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _61_132.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _61_132.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _61_132.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _61_132.FStar_Syntax_Syntax.actions})
in (

let ed = (match (effect_params) with
| [] -> begin
ed
end
| _61_137 -> begin
(

let op = (fun ts -> (

let _61_140 = ()
in (

let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in (([]), (t1)))))
in (

let _61_143 = ed
in (let _159_101 = (op ed.FStar_Syntax_Syntax.ret_wp)
in (let _159_100 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _159_99 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _159_98 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _159_97 = (op ed.FStar_Syntax_Syntax.stronger)
in (let _159_96 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _159_95 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _159_94 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _159_93 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _159_92 = (op ed.FStar_Syntax_Syntax.trivial)
in (let _159_91 = (let _159_82 = (op (([]), (ed.FStar_Syntax_Syntax.repr)))
in (Prims.snd _159_82))
in (let _159_90 = (op ed.FStar_Syntax_Syntax.return_repr)
in (let _159_89 = (op ed.FStar_Syntax_Syntax.bind_repr)
in (let _159_88 = (FStar_List.map (fun a -> (

let _61_146 = a
in (let _159_87 = (let _159_84 = (op (([]), (a.FStar_Syntax_Syntax.action_defn)))
in (Prims.snd _159_84))
in (let _159_86 = (let _159_85 = (op (([]), (a.FStar_Syntax_Syntax.action_typ)))
in (Prims.snd _159_85))
in {FStar_Syntax_Syntax.action_name = _61_146.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = _61_146.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = _61_146.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _159_87; FStar_Syntax_Syntax.action_typ = _159_86})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.qualifiers = _61_143.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = _61_143.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = _61_143.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _61_143.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _61_143.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _61_143.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _159_101; FStar_Syntax_Syntax.bind_wp = _159_100; FStar_Syntax_Syntax.if_then_else = _159_99; FStar_Syntax_Syntax.ite_wp = _159_98; FStar_Syntax_Syntax.stronger = _159_97; FStar_Syntax_Syntax.close_wp = _159_96; FStar_Syntax_Syntax.assert_p = _159_95; FStar_Syntax_Syntax.assume_p = _159_94; FStar_Syntax_Syntax.null_wp = _159_93; FStar_Syntax_Syntax.trivial = _159_92; FStar_Syntax_Syntax.repr = _159_91; FStar_Syntax_Syntax.return_repr = _159_90; FStar_Syntax_Syntax.bind_repr = _159_89; FStar_Syntax_Syntax.actions = _159_88}))))))))))))))))
end)
in (

let wp_with_fresh_result_type = (fun env mname signature -> (

let fail = (fun t -> (let _159_112 = (let _159_111 = (let _159_110 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in ((_159_110), ((FStar_Ident.range_of_lid mname))))
in FStar_Syntax_Syntax.Error (_159_111))
in (Prims.raise _159_112)))
in (match ((let _159_113 = (FStar_Syntax_Subst.compress signature)
in _159_113.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _61_166))::((wp, _61_162))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _61_170 -> begin
(fail signature)
end))
end
| _61_172 -> begin
(fail signature)
end)))
in (

let _61_175 = (wp_with_fresh_result_type env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_61_175) with
| (a, wp_a) -> begin
(

let fresh_effect_signature = (fun _61_177 -> (match (()) with
| () -> begin
(

let _61_181 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (_61_181) with
| (signature, _61_180) -> begin
(wp_with_fresh_result_type env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (

let env = (let _159_116 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _159_116))
in (

let _61_183 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _159_122 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _159_121 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _159_120 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _159_119 = (let _159_117 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Print.term_to_string _159_117))
in (let _159_118 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.sort)
in (FStar_Util.print5 "Checking effect signature: %s %s : %s\n(a is %s:%s)\n" _159_122 _159_121 _159_120 _159_119 _159_118))))))
end else begin
()
end
in (

let check_and_gen' = (fun env _61_190 k -> (match (_61_190) with
| (_61_188, t) -> begin
(check_and_gen env t k)
end))
in (

let return_wp = (

let expected_k = (let _159_134 = (let _159_132 = (FStar_Syntax_Syntax.mk_binder a)
in (let _159_131 = (let _159_130 = (let _159_129 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _159_129))
in (_159_130)::[])
in (_159_132)::_159_131))
in (let _159_133 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _159_134 _159_133)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret_wp expected_k))
in (

let bind_wp = (

let _61_196 = (fresh_effect_signature ())
in (match (_61_196) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _159_138 = (let _159_136 = (let _159_135 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _159_135))
in (_159_136)::[])
in (let _159_137 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _159_138 _159_137)))
in (

let expected_k = (let _159_149 = (let _159_147 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _159_146 = (let _159_145 = (FStar_Syntax_Syntax.mk_binder a)
in (let _159_144 = (let _159_143 = (FStar_Syntax_Syntax.mk_binder b)
in (let _159_142 = (let _159_141 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _159_140 = (let _159_139 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (_159_139)::[])
in (_159_141)::_159_140))
in (_159_143)::_159_142))
in (_159_145)::_159_144))
in (_159_147)::_159_146))
in (let _159_148 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _159_149 _159_148)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else = (

let p = (let _159_151 = (let _159_150 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _159_150 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _159_151))
in (

let expected_k = (let _159_160 = (let _159_158 = (FStar_Syntax_Syntax.mk_binder a)
in (let _159_157 = (let _159_156 = (FStar_Syntax_Syntax.mk_binder p)
in (let _159_155 = (let _159_154 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _159_153 = (let _159_152 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_159_152)::[])
in (_159_154)::_159_153))
in (_159_156)::_159_155))
in (_159_158)::_159_157))
in (let _159_159 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _159_160 _159_159)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (let _159_165 = (let _159_163 = (FStar_Syntax_Syntax.mk_binder a)
in (let _159_162 = (let _159_161 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_159_161)::[])
in (_159_163)::_159_162))
in (let _159_164 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _159_165 _159_164)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let _61_208 = (FStar_Syntax_Util.type_u ())
in (match (_61_208) with
| (t, _61_207) -> begin
(

let expected_k = (let _159_172 = (let _159_170 = (FStar_Syntax_Syntax.mk_binder a)
in (let _159_169 = (let _159_168 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _159_167 = (let _159_166 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_159_166)::[])
in (_159_168)::_159_167))
in (_159_170)::_159_169))
in (let _159_171 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _159_172 _159_171)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (let _159_174 = (let _159_173 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _159_173 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _159_174))
in (

let b_wp_a = (let _159_178 = (let _159_176 = (let _159_175 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _159_175))
in (_159_176)::[])
in (let _159_177 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _159_178 _159_177)))
in (

let expected_k = (let _159_185 = (let _159_183 = (FStar_Syntax_Syntax.mk_binder a)
in (let _159_182 = (let _159_181 = (FStar_Syntax_Syntax.mk_binder b)
in (let _159_180 = (let _159_179 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_159_179)::[])
in (_159_181)::_159_180))
in (_159_183)::_159_182))
in (let _159_184 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _159_185 _159_184)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (let _159_194 = (let _159_192 = (FStar_Syntax_Syntax.mk_binder a)
in (let _159_191 = (let _159_190 = (let _159_187 = (let _159_186 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _159_186 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _159_187))
in (let _159_189 = (let _159_188 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_159_188)::[])
in (_159_190)::_159_189))
in (_159_192)::_159_191))
in (let _159_193 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _159_194 _159_193)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (let _159_203 = (let _159_201 = (FStar_Syntax_Syntax.mk_binder a)
in (let _159_200 = (let _159_199 = (let _159_196 = (let _159_195 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _159_195 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _159_196))
in (let _159_198 = (let _159_197 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_159_197)::[])
in (_159_199)::_159_198))
in (_159_201)::_159_200))
in (let _159_202 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _159_203 _159_202)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (let _159_206 = (let _159_204 = (FStar_Syntax_Syntax.mk_binder a)
in (_159_204)::[])
in (let _159_205 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _159_206 _159_205)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let _61_224 = (FStar_Syntax_Util.type_u ())
in (match (_61_224) with
| (t, _61_223) -> begin
(

let expected_k = (let _159_211 = (let _159_209 = (FStar_Syntax_Syntax.mk_binder a)
in (let _159_208 = (let _159_207 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_159_207)::[])
in (_159_209)::_159_208))
in (let _159_210 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _159_211 _159_210)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let _61_368 = (match ((let _159_212 = (FStar_Syntax_Subst.compress ed.FStar_Syntax_Syntax.repr)
in _159_212.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((ed.FStar_Syntax_Syntax.repr), (ed.FStar_Syntax_Syntax.bind_repr), (ed.FStar_Syntax_Syntax.return_repr), (ed.FStar_Syntax_Syntax.actions))
end
| _61_229 -> begin
(

let repr = (

let _61_233 = (FStar_Syntax_Util.type_u ())
in (match (_61_233) with
| (t, _61_232) -> begin
(

let expected_k = (let _159_217 = (let _159_215 = (FStar_Syntax_Syntax.mk_binder a)
in (let _159_214 = (let _159_213 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_159_213)::[])
in (_159_215)::_159_214))
in (let _159_216 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _159_217 _159_216)))
in (tc_check_trivial_guard env ed.FStar_Syntax_Syntax.repr expected_k))
end))
in (

let mk_repr' = (fun t wp -> (

let repr = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env repr)
in (let _159_227 = (let _159_226 = (let _159_225 = (let _159_224 = (FStar_Syntax_Syntax.as_arg t)
in (let _159_223 = (let _159_222 = (FStar_Syntax_Syntax.as_arg wp)
in (_159_222)::[])
in (_159_224)::_159_223))
in ((repr), (_159_225)))
in FStar_Syntax_Syntax.Tm_app (_159_226))
in (FStar_Syntax_Syntax.mk _159_227 None FStar_Range.dummyRange))))
in (

let mk_repr = (fun a wp -> (let _159_232 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_repr' _159_232 wp)))
in (

let destruct_repr = (fun t -> (match ((let _159_235 = (FStar_Syntax_Subst.compress t)
in _159_235.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_61_246, ((t, _61_253))::((wp, _61_249))::[]) -> begin
((t), (wp))
end
| _61_259 -> begin
(FStar_All.failwith "Unexpected repr type")
end))
in (

let bind_repr = (

let r = (let _159_236 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_0 FStar_Syntax_Syntax.Delta_constant None)
in (FStar_All.pipe_right _159_236 FStar_Syntax_Syntax.fv_to_tm))
in (

let _61_263 = (fresh_effect_signature ())
in (match (_61_263) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _159_240 = (let _159_238 = (let _159_237 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _159_237))
in (_159_238)::[])
in (let _159_239 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _159_240 _159_239)))
in (

let wp_f = (FStar_Syntax_Syntax.gen_bv "wp_f" None wp_a)
in (

let wp_g = (FStar_Syntax_Syntax.gen_bv "wp_g" None a_wp_b)
in (

let x_a = (let _159_241 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _159_241))
in (

let wp_g_x = (let _159_245 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (let _159_244 = (let _159_243 = (let _159_242 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _159_242))
in (_159_243)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _159_245 _159_244 None FStar_Range.dummyRange)))
in (

let res = (

let wp = (let _159_257 = (let _159_246 = (FStar_TypeChecker_Env.inst_tscheme bind_wp)
in (FStar_All.pipe_right _159_246 Prims.snd))
in (let _159_256 = (let _159_255 = (let _159_254 = (let _159_253 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _159_252 = (let _159_251 = (FStar_Syntax_Syntax.bv_to_name b)
in (let _159_250 = (let _159_249 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (let _159_248 = (let _159_247 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (_159_247)::[])
in (_159_249)::_159_248))
in (_159_251)::_159_250))
in (_159_253)::_159_252))
in (r)::_159_254)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _159_255))
in (FStar_Syntax_Syntax.mk_Tm_app _159_257 _159_256 None FStar_Range.dummyRange)))
in (mk_repr b wp))
in (

let expected_k = (let _159_277 = (let _159_275 = (FStar_Syntax_Syntax.mk_binder a)
in (let _159_274 = (let _159_273 = (FStar_Syntax_Syntax.mk_binder b)
in (let _159_272 = (let _159_271 = (FStar_Syntax_Syntax.mk_binder wp_f)
in (let _159_270 = (let _159_269 = (let _159_259 = (let _159_258 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (mk_repr a _159_258))
in (FStar_Syntax_Syntax.null_binder _159_259))
in (let _159_268 = (let _159_267 = (FStar_Syntax_Syntax.mk_binder wp_g)
in (let _159_266 = (let _159_265 = (let _159_264 = (let _159_263 = (let _159_260 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_159_260)::[])
in (let _159_262 = (let _159_261 = (mk_repr b wp_g_x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _159_261))
in (FStar_Syntax_Util.arrow _159_263 _159_262)))
in (FStar_Syntax_Syntax.null_binder _159_264))
in (_159_265)::[])
in (_159_267)::_159_266))
in (_159_269)::_159_268))
in (_159_271)::_159_270))
in (_159_273)::_159_272))
in (_159_275)::_159_274))
in (let _159_276 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _159_277 _159_276)))
in (

let _61_277 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (_61_277) with
| (expected_k, _61_274, _61_276) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos)
in (

let env = (

let _61_279 = env
in {FStar_TypeChecker_Env.solver = _61_279.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _61_279.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _61_279.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _61_279.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _61_279.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _61_279.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _61_279.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _61_279.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _61_279.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _61_279.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _61_279.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _61_279.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _61_279.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _61_279.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _61_279.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _61_279.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _61_279.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _61_279.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _61_279.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _61_279.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _61_279.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _61_279.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _61_279.FStar_TypeChecker_Env.qname_and_index})
in (

let br = (check_and_gen' env ed.FStar_Syntax_Syntax.bind_repr expected_k)
in br)))
end)))))))))
end)))
in (

let return_repr = (

let x_a = (let _159_278 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _159_278))
in (

let res = (

let wp = (let _159_285 = (let _159_279 = (FStar_TypeChecker_Env.inst_tscheme return_wp)
in (FStar_All.pipe_right _159_279 Prims.snd))
in (let _159_284 = (let _159_283 = (let _159_282 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _159_281 = (let _159_280 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (_159_280)::[])
in (_159_282)::_159_281))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _159_283))
in (FStar_Syntax_Syntax.mk_Tm_app _159_285 _159_284 None FStar_Range.dummyRange)))
in (mk_repr a wp))
in (

let expected_k = (let _159_290 = (let _159_288 = (FStar_Syntax_Syntax.mk_binder a)
in (let _159_287 = (let _159_286 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_159_286)::[])
in (_159_288)::_159_287))
in (let _159_289 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _159_290 _159_289)))
in (

let _61_293 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (_61_293) with
| (expected_k, _61_290, _61_292) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos)
in (

let _61_297 = (check_and_gen' env ed.FStar_Syntax_Syntax.return_repr expected_k)
in (match (_61_297) with
| (univs, repr) -> begin
(match (univs) with
| [] -> begin
(([]), (repr))
end
| _61_300 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected universe-polymorphic return for effect"), (repr.FStar_Syntax_Syntax.pos)))))
end)
end)))
end)))))
in (

let actions = (

let check_action = (fun act -> (

let _61_308 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env act.FStar_Syntax_Syntax.action_typ)
in (match (_61_308) with
| (act_typ, _61_306, g_t) -> begin
(

let env' = (FStar_TypeChecker_Env.set_expected_typ env act_typ)
in (

let _61_310 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _159_294 = (FStar_Syntax_Print.term_to_string act.FStar_Syntax_Syntax.action_defn)
in (let _159_293 = (FStar_Syntax_Print.term_to_string act_typ)
in (FStar_Util.print3 "Checking action %s:\n[definition]: %s\n[cps\'d type]: %s\n" (FStar_Ident.text_of_lid act.FStar_Syntax_Syntax.action_name) _159_294 _159_293)))
end else begin
()
end
in (

let _61_316 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' act.FStar_Syntax_Syntax.action_defn)
in (match (_61_316) with
| (act_defn, _61_314, g_a) -> begin
(

let act_defn = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env act_defn)
in (

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
in (

let _61_339 = (

let act_typ = (FStar_Syntax_Subst.compress act_typ)
in (match (act_typ.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _61_327 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_61_327) with
| (bs, _61_326) -> begin
(

let res = (mk_repr' FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun)
in (

let k = (let _159_295 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs _159_295))
in (

let _61_334 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env k)
in (match (_61_334) with
| (k, _61_332, g) -> begin
((k), (g))
end))))
end))
end
| _61_336 -> begin
(let _159_300 = (let _159_299 = (let _159_298 = (let _159_297 = (FStar_Syntax_Print.term_to_string act_typ)
in (let _159_296 = (FStar_Syntax_Print.tag_of_term act_typ)
in (FStar_Util.format2 "Actions must have function types (not: %s, a.k.a. %s)" _159_297 _159_296)))
in ((_159_298), (act_defn.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_159_299))
in (Prims.raise _159_300))
end))
in (match (_61_339) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env act_typ expected_k)
in (

let _61_341 = (let _159_303 = (let _159_302 = (let _159_301 = (FStar_TypeChecker_Rel.conj_guard g_t g)
in (FStar_TypeChecker_Rel.conj_guard g_k _159_301))
in (FStar_TypeChecker_Rel.conj_guard g_a _159_302))
in (FStar_TypeChecker_Rel.force_trivial_guard env _159_303))
in (

let act_typ = (match ((let _159_304 = (FStar_Syntax_Subst.compress expected_k)
in _159_304.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _61_349 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_61_349) with
| (bs, c) -> begin
(

let _61_352 = (destruct_repr (FStar_Syntax_Util.comp_result c))
in (match (_61_352) with
| (a, wp) -> begin
(

let c = (let _159_308 = (let _159_305 = (env.FStar_TypeChecker_Env.universe_of env a)
in (_159_305)::[])
in (let _159_307 = (let _159_306 = (FStar_Syntax_Syntax.as_arg wp)
in (_159_306)::[])
in {FStar_Syntax_Syntax.comp_univs = _159_308; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a; FStar_Syntax_Syntax.effect_args = _159_307; FStar_Syntax_Syntax.flags = []}))
in (let _159_309 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Util.arrow bs _159_309)))
end))
end))
end
| _61_355 -> begin
(FStar_All.failwith "")
end)
in (

let _61_359 = (FStar_TypeChecker_Util.generalize_universes env act_defn)
in (match (_61_359) with
| (univs, act_defn) -> begin
(

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
in (

let _61_361 = act
in {FStar_Syntax_Syntax.action_name = _61_361.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = _61_361.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = act_defn; FStar_Syntax_Syntax.action_typ = act_typ}))
end)))))
end))))
end))))
end)))
in (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.map check_action)))
in ((repr), (bind_repr), (return_repr), (actions)))))))))
end)
in (match (_61_368) with
| (repr, bind_repr, return_repr, actions) -> begin
(

let t = (let _159_310 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _159_310))
in (

let _61_372 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_61_372) with
| (univs, t) -> begin
(

let signature = (match ((let _159_312 = (let _159_311 = (FStar_Syntax_Subst.compress t)
in _159_311.FStar_Syntax_Syntax.n)
in ((effect_params), (_159_312)))) with
| ([], _61_375) -> begin
t
end
| (_61_378, FStar_Syntax_Syntax.Tm_arrow (_61_380, c)) -> begin
(FStar_Syntax_Util.comp_result c)
end
| _61_386 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let close = (fun n ts -> (

let ts = (let _159_317 = (FStar_Syntax_Subst.close_tscheme effect_params ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _159_317))
in (

let m = (FStar_List.length (Prims.fst ts))
in (

let _61_394 = if (((n >= (Prims.parse_int "0")) && (not ((FStar_Syntax_Util.is_unknown (Prims.snd ts))))) && (m <> n)) then begin
(

let error = if (m < n) then begin
"not universe-polymorphic enough"
end else begin
"too universe-polymorphic"
end
in (let _159_320 = (let _159_319 = (FStar_Util.string_of_int n)
in (let _159_318 = (FStar_Syntax_Print.tscheme_to_string ts)
in (FStar_Util.format3 "The effect combinator is %s (n=%s) (%s)" error _159_319 _159_318)))
in (FStar_All.failwith _159_320)))
end else begin
()
end
in ts))))
in (

let close_action = (fun act -> (

let _61_400 = (close (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_defn)))
in (match (_61_400) with
| (univs, defn) -> begin
(

let _61_403 = (close (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_typ)))
in (match (_61_403) with
| (univs', typ) -> begin
(

let _61_404 = ()
in (

let _61_406 = act
in {FStar_Syntax_Syntax.action_name = _61_406.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = _61_406.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = defn; FStar_Syntax_Syntax.action_typ = typ}))
end))
end)))
in (

let nunivs = (FStar_List.length univs)
in (

let _61_409 = ()
in (

let ed = (

let _61_411 = ed
in (let _159_337 = (close (Prims.parse_int "0") return_wp)
in (let _159_336 = (close (Prims.parse_int "1") bind_wp)
in (let _159_335 = (close (Prims.parse_int "0") if_then_else)
in (let _159_334 = (close (Prims.parse_int "0") ite_wp)
in (let _159_333 = (close (Prims.parse_int "0") stronger)
in (let _159_332 = (close (Prims.parse_int "1") close_wp)
in (let _159_331 = (close (Prims.parse_int "0") assert_p)
in (let _159_330 = (close (Prims.parse_int "0") assume_p)
in (let _159_329 = (close (Prims.parse_int "0") null_wp)
in (let _159_328 = (close (Prims.parse_int "0") trivial_wp)
in (let _159_327 = (let _159_323 = (close (Prims.parse_int "0") (([]), (repr)))
in (Prims.snd _159_323))
in (let _159_326 = (close (Prims.parse_int "0") return_repr)
in (let _159_325 = (close (Prims.parse_int "1") bind_repr)
in (let _159_324 = (FStar_List.map close_action actions)
in {FStar_Syntax_Syntax.qualifiers = _61_411.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = _61_411.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = _61_411.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _159_337; FStar_Syntax_Syntax.bind_wp = _159_336; FStar_Syntax_Syntax.if_then_else = _159_335; FStar_Syntax_Syntax.ite_wp = _159_334; FStar_Syntax_Syntax.stronger = _159_333; FStar_Syntax_Syntax.close_wp = _159_332; FStar_Syntax_Syntax.assert_p = _159_331; FStar_Syntax_Syntax.assume_p = _159_330; FStar_Syntax_Syntax.null_wp = _159_329; FStar_Syntax_Syntax.trivial = _159_328; FStar_Syntax_Syntax.repr = _159_327; FStar_Syntax_Syntax.return_repr = _159_326; FStar_Syntax_Syntax.bind_repr = _159_325; FStar_Syntax_Syntax.actions = _159_324})))))))))))))))
in (

let _61_414 = if ((FStar_TypeChecker_Env.debug env FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ED")))) then begin
(let _159_338 = (FStar_Syntax_Print.eff_decl_to_string false ed)
in (FStar_Util.print_string _159_338))
end else begin
()
end
in ed)))))))
end)))
end))))))))))))))))
end)))))
end))
end))
end))))
and cps_and_elaborate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.sigelt Prims.option) = (fun env ed -> (

let _61_420 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_61_420) with
| (effect_binders_un, signature_un) -> begin
(

let _61_425 = (tc_tparams env effect_binders_un)
in (match (_61_425) with
| (effect_binders, env, _61_424) -> begin
(

let _61_429 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (_61_429) with
| (signature, _61_428) -> begin
(

let effect_binders = (FStar_List.map (fun _61_432 -> (match (_61_432) with
| (bv, qual) -> begin
(let _159_343 = (

let _61_433 = bv
in (let _159_342 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _61_433.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _61_433.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _159_342}))
in ((_159_343), (qual)))
end)) effect_binders)
in (

let _61_448 = (match ((let _159_344 = (FStar_Syntax_Subst.compress signature_un)
in _159_344.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (((a, _61_438))::[], effect_marker) -> begin
((a), (effect_marker))
end
| _61_445 -> begin
(FStar_All.failwith "bad shape for effect-for-free signature")
end)
in (match (_61_448) with
| (a, effect_marker) -> begin
(

let a = if (FStar_Syntax_Syntax.is_null_bv a) then begin
(let _159_346 = (let _159_345 = (FStar_Syntax_Syntax.range_of_bv a)
in Some (_159_345))
in (FStar_Syntax_Syntax.gen_bv "a" _159_346 a.FStar_Syntax_Syntax.sort))
end else begin
a
end
in (

let open_and_check = (fun t -> (

let subst = (FStar_Syntax_Subst.opening_of_binders effect_binders)
in (

let t = (FStar_Syntax_Subst.subst subst t)
in (

let _61_458 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (_61_458) with
| (t, comp, _61_457) -> begin
((t), (comp))
end)))))
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None signature.FStar_Syntax_Syntax.pos))
in (

let _61_463 = (open_and_check ed.FStar_Syntax_Syntax.repr)
in (match (_61_463) with
| (repr, _comp) -> begin
(

let _61_464 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _159_351 = (FStar_Syntax_Print.term_to_string repr)
in (FStar_Util.print1 "Representation is: %s\n" _159_351))
end else begin
()
end
in (

let dmff_env = (FStar_TypeChecker_DMFF.empty env (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange))
in (

let wp_type = (FStar_TypeChecker_DMFF.star_type dmff_env repr)
in (

let wp_type = (recheck_debug "*" env wp_type)
in (

let wp_a = (let _159_358 = (let _159_357 = (let _159_356 = (let _159_355 = (let _159_354 = (let _159_353 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _159_352 = (FStar_Syntax_Syntax.as_implicit false)
in ((_159_353), (_159_352))))
in (_159_354)::[])
in ((wp_type), (_159_355)))
in FStar_Syntax_Syntax.Tm_app (_159_356))
in (mk _159_357))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _159_358))
in (

let effect_signature = (

let binders = (let _159_363 = (let _159_359 = (FStar_Syntax_Syntax.as_implicit false)
in ((a), (_159_359)))
in (let _159_362 = (let _159_361 = (let _159_360 = (FStar_Syntax_Syntax.gen_bv "dijkstra_wp" None wp_a)
in (FStar_All.pipe_right _159_360 FStar_Syntax_Syntax.mk_binder))
in (_159_361)::[])
in (_159_363)::_159_362))
in (

let binders = (FStar_Syntax_Subst.close_binders binders)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (effect_marker)))))))
in (

let effect_signature = (recheck_debug "turned into the effect signature" env effect_signature)
in (

let sigelts = (FStar_ST.alloc [])
in (

let mk_lid = (fun name -> (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" name))) FStar_Range.dummyRange))
in (

let elaborate_and_star = (fun dmff_env item -> (

let _61_482 = item
in (match (_61_482) with
| (u_item, item) -> begin
(

let _61_485 = (open_and_check item)
in (match (_61_485) with
| (item, item_comp) -> begin
(

let _61_486 = if (not ((FStar_Syntax_Util.is_total_lcomp item_comp))) then begin
(let _159_373 = (let _159_372 = (let _159_371 = (FStar_Syntax_Print.term_to_string item)
in (let _159_370 = (FStar_Syntax_Print.lcomp_to_string item_comp)
in (FStar_Util.format2 "Computation for [%s] is not total : %s !" _159_371 _159_370)))
in FStar_Syntax_Syntax.Err (_159_372))
in (Prims.raise _159_373))
end else begin
()
end
in (

let _61_491 = (FStar_TypeChecker_DMFF.star_expr dmff_env item)
in (match (_61_491) with
| (item_t, item_wp, item_elab) -> begin
(

let item_wp = (recheck_debug "*" env item_wp)
in (

let item_elab = (recheck_debug "_" env item_elab)
in ((dmff_env), (item_t), (item_wp), (item_elab))))
end)))
end))
end)))
in (

let _61_499 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.bind_repr)
in (match (_61_499) with
| (dmff_env, _61_496, bind_wp, bind_elab) -> begin
(

let _61_505 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.return_repr)
in (match (_61_505) with
| (dmff_env, _61_502, return_wp, return_elab) -> begin
(

let lift_from_pure_wp = (match ((let _159_374 = (FStar_Syntax_Subst.compress return_wp)
in _159_374.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(

let _61_525 = (match ((let _159_375 = (FStar_Syntax_Util.abs bs body None)
in (FStar_Syntax_Subst.open_term ((b1)::(b2)::[]) _159_375))) with
| ((b1)::(b2)::[], body) -> begin
((b1), (b2), (body))
end
| _61_521 -> begin
(FStar_All.failwith "Impossible : open_term not preserving binders arity")
end)
in (match (_61_525) with
| (b1, b2, body) -> begin
(

let env0 = (FStar_TypeChecker_Env.push_binders (FStar_TypeChecker_DMFF.get_env dmff_env) ((b1)::(b2)::[]))
in (

let wp_b1 = (let _159_382 = (let _159_381 = (let _159_380 = (let _159_379 = (let _159_378 = (let _159_377 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b1))
in (let _159_376 = (FStar_Syntax_Syntax.as_implicit false)
in ((_159_377), (_159_376))))
in (_159_378)::[])
in ((wp_type), (_159_379)))
in FStar_Syntax_Syntax.Tm_app (_159_380))
in (mk _159_381))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env0 _159_382))
in (

let _61_531 = (let _159_384 = (let _159_383 = (FStar_Syntax_Util.unascribe wp_b1)
in (FStar_TypeChecker_Normalize.eta_expand_with_type body _159_383))
in (FStar_All.pipe_left FStar_Syntax_Util.abs_formals _159_384))
in (match (_61_531) with
| (bs, body, what') -> begin
(

let t2 = (Prims.fst b2).FStar_Syntax_Syntax.sort
in (

let pure_wp_type = (FStar_TypeChecker_DMFF.double_star t2)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None pure_wp_type)
in (

let body = (let _159_388 = (FStar_Syntax_Syntax.bv_to_name wp)
in (let _159_387 = (let _159_386 = (let _159_385 = (FStar_Syntax_Util.abs ((b2)::[]) body what')
in ((_159_385), (None)))
in (_159_386)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _159_388 _159_387 None FStar_Range.dummyRange)))
in (let _159_392 = (let _159_390 = (let _159_389 = (FStar_Syntax_Syntax.mk_binder wp)
in (_159_389)::[])
in (b1)::_159_390)
in (let _159_391 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs _159_392 _159_391 (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_GTot_lid), ([]))))))))))))
end))))
end))
end
| _61_537 -> begin
(FStar_All.failwith "unexpected shape for return")
end)
in (

let return_wp = (match ((let _159_393 = (FStar_Syntax_Subst.compress return_wp)
in _159_393.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(let _159_394 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs ((b1)::(b2)::[]) _159_394 (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_GTot_lid), ([])))))))
end
| _61_549 -> begin
(FStar_All.failwith "unexpected shape for return")
end)
in (

let bind_wp = (match ((let _159_395 = (FStar_Syntax_Subst.compress bind_wp)
in _159_395.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let r = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (let _159_399 = (let _159_398 = (let _159_397 = (let _159_396 = (mk (FStar_Syntax_Syntax.Tm_fvar (r)))
in (FStar_Syntax_Syntax.null_binder _159_396))
in (_159_397)::[])
in (FStar_List.append _159_398 binders))
in (FStar_Syntax_Util.abs _159_399 body what)))
end
| _61_558 -> begin
(FStar_All.failwith "unexpected shape for bind")
end)
in (

let apply_close = (fun t -> if ((FStar_List.length effect_binders) = (Prims.parse_int "0")) then begin
t
end else begin
(let _159_406 = (let _159_405 = (let _159_404 = (let _159_403 = (let _159_402 = (FStar_Syntax_Util.args_of_binders effect_binders)
in (Prims.snd _159_402))
in ((t), (_159_403)))
in FStar_Syntax_Syntax.Tm_app (_159_404))
in (mk _159_405))
in (FStar_Syntax_Subst.close effect_binders _159_406))
end)
in (

let register = (fun name item -> (

let _61_567 = (let _159_412 = (mk_lid name)
in (let _159_411 = (FStar_Syntax_Util.abs effect_binders item None)
in (FStar_TypeChecker_Util.mk_toplevel_definition env _159_412 _159_411)))
in (match (_61_567) with
| (sigelt, fv) -> begin
(

let _61_568 = (let _159_414 = (let _159_413 = (FStar_ST.read sigelts)
in (sigelt)::_159_413)
in (FStar_ST.op_Colon_Equals sigelts _159_414))
in fv)
end)))
in (

let lift_from_pure_wp = (register "lift_from_pure" lift_from_pure_wp)
in (

let return_wp = (register "return_wp" return_wp)
in (

let _61_572 = (let _159_416 = (let _159_415 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true")), (FStar_Range.dummyRange))))::_159_415)
in (FStar_ST.op_Colon_Equals sigelts _159_416))
in (

let return_elab = (register "return_elab" return_elab)
in (

let _61_575 = (let _159_418 = (let _159_417 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false")), (FStar_Range.dummyRange))))::_159_417)
in (FStar_ST.op_Colon_Equals sigelts _159_418))
in (

let bind_wp = (register "bind_wp" bind_wp)
in (

let _61_578 = (let _159_420 = (let _159_419 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true")), (FStar_Range.dummyRange))))::_159_419)
in (FStar_ST.op_Colon_Equals sigelts _159_420))
in (

let bind_elab = (register "bind_elab" bind_elab)
in (

let _61_581 = (let _159_422 = (let _159_421 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false")), (FStar_Range.dummyRange))))::_159_421)
in (FStar_ST.op_Colon_Equals sigelts _159_422))
in (

let _61_600 = (FStar_List.fold_left (fun _61_585 action -> (match (_61_585) with
| (dmff_env, actions) -> begin
(

let _61_591 = (elaborate_and_star dmff_env ((action.FStar_Syntax_Syntax.action_univs), (action.FStar_Syntax_Syntax.action_defn)))
in (match (_61_591) with
| (dmff_env, action_t, action_wp, action_elab) -> begin
(

let name = action.FStar_Syntax_Syntax.action_name.FStar_Ident.ident.FStar_Ident.idText
in (

let action_typ_with_wp = (FStar_TypeChecker_DMFF.trans_F dmff_env action_t action_wp)
in (

let action_elab = (register (Prims.strcat name "_elab") action_elab)
in (

let action_typ_with_wp = (register (Prims.strcat name "_complete_type") action_typ_with_wp)
in (let _159_428 = (let _159_427 = (

let _61_596 = action
in (let _159_426 = (apply_close action_elab)
in (let _159_425 = (apply_close action_typ_with_wp)
in {FStar_Syntax_Syntax.action_name = _61_596.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = _61_596.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = _61_596.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _159_426; FStar_Syntax_Syntax.action_typ = _159_425})))
in (_159_427)::actions)
in ((dmff_env), (_159_428)))))))
end))
end)) ((dmff_env), ([])) ed.FStar_Syntax_Syntax.actions)
in (match (_61_600) with
| (dmff_env, actions) -> begin
(

let actions = (FStar_List.rev actions)
in (

let repr = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp_a" None wp_a)
in (

let binders = (let _159_431 = (FStar_Syntax_Syntax.mk_binder a)
in (let _159_430 = (let _159_429 = (FStar_Syntax_Syntax.mk_binder wp)
in (_159_429)::[])
in (_159_431)::_159_430))
in (let _159_440 = (let _159_439 = (let _159_437 = (let _159_436 = (let _159_435 = (let _159_434 = (let _159_433 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _159_432 = (FStar_Syntax_Syntax.as_implicit false)
in ((_159_433), (_159_432))))
in (_159_434)::[])
in ((repr), (_159_435)))
in FStar_Syntax_Syntax.Tm_app (_159_436))
in (mk _159_437))
in (let _159_438 = (FStar_Syntax_Syntax.bv_to_name wp)
in (FStar_TypeChecker_DMFF.trans_F dmff_env _159_439 _159_438)))
in (FStar_Syntax_Util.abs binders _159_440 None))))
in (

let repr = (recheck_debug "FC" env repr)
in (

let repr = (register "repr" repr)
in (

let _61_651 = (match ((let _159_442 = (let _159_441 = (FStar_Syntax_Subst.compress wp_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe _159_441))
in _159_442.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((type_param)::effect_param, arrow, _61_612) -> begin
(

let _61_625 = (match ((FStar_Syntax_Subst.open_term ((type_param)::effect_param) arrow)) with
| ((b)::bs, body) -> begin
((b), (bs), (body))
end
| _61_621 -> begin
(FStar_All.failwith "Impossible : open_term nt preserving binders arity")
end)
in (match (_61_625) with
| (type_param, effect_param, arrow) -> begin
(match ((let _159_444 = (let _159_443 = (FStar_Syntax_Subst.compress arrow)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe _159_443))
in _159_444.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (wp_binders, c) -> begin
(

let _61_632 = (FStar_Syntax_Subst.open_comp wp_binders c)
in (match (_61_632) with
| (wp_binders, c) -> begin
(

let _61_639 = (FStar_List.partition (fun _61_636 -> (match (_61_636) with
| (bv, _61_635) -> begin
(let _159_447 = (let _159_446 = (FStar_Syntax_Free.names bv.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _159_446 (FStar_Util.set_mem (Prims.fst type_param))))
in (FStar_All.pipe_right _159_447 Prims.op_Negation))
end)) wp_binders)
in (match (_61_639) with
| (pre_args, post_args) -> begin
(

let post = (match (post_args) with
| (post)::[] -> begin
post
end
| _61_643 -> begin
(let _159_449 = (let _159_448 = (FStar_Syntax_Print.term_to_string arrow)
in (FStar_Util.format1 "Impossible: multiple post candidates %s" _159_448))
in (FStar_All.failwith _159_449))
end)
in (let _159_451 = (FStar_Syntax_Util.arrow pre_args c)
in (let _159_450 = (FStar_Syntax_Util.abs ((type_param)::effect_param) (Prims.fst post).FStar_Syntax_Syntax.sort None)
in ((_159_451), (_159_450)))))
end))
end))
end
| _61_646 -> begin
(let _159_453 = (let _159_452 = (FStar_Syntax_Print.term_to_string arrow)
in (FStar_Util.format1 "Impossible: pre/post arrow %s" _159_452))
in (FStar_All.failwith _159_453))
end)
end))
end
| _61_648 -> begin
(let _159_455 = (let _159_454 = (FStar_Syntax_Print.term_to_string wp_type)
in (FStar_Util.format1 "Impossible: pre/post abs %s" _159_454))
in (FStar_All.failwith _159_455))
end)
in (match (_61_651) with
| (pre, post) -> begin
(

let _61_652 = (let _159_456 = (register "pre" pre)
in (Prims.ignore _159_456))
in (

let _61_654 = (let _159_457 = (register "post" post)
in (Prims.ignore _159_457))
in (

let _61_656 = (let _159_458 = (register "wp" wp_type)
in (Prims.ignore _159_458))
in (

let ed = (

let _61_658 = ed
in (let _159_469 = (FStar_Syntax_Subst.close_binders effect_binders)
in (let _159_468 = (FStar_Syntax_Subst.close effect_binders effect_signature)
in (let _159_467 = (let _159_459 = (apply_close return_wp)
in (([]), (_159_459)))
in (let _159_466 = (let _159_460 = (apply_close bind_wp)
in (([]), (_159_460)))
in (let _159_465 = (apply_close repr)
in (let _159_464 = (let _159_461 = (apply_close return_elab)
in (([]), (_159_461)))
in (let _159_463 = (let _159_462 = (apply_close bind_elab)
in (([]), (_159_462)))
in {FStar_Syntax_Syntax.qualifiers = _61_658.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = _61_658.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = _61_658.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _61_658.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _159_469; FStar_Syntax_Syntax.signature = _159_468; FStar_Syntax_Syntax.ret_wp = _159_467; FStar_Syntax_Syntax.bind_wp = _159_466; FStar_Syntax_Syntax.if_then_else = _61_658.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _61_658.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _61_658.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _61_658.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _61_658.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _61_658.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _61_658.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _61_658.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _159_465; FStar_Syntax_Syntax.return_repr = _159_464; FStar_Syntax_Syntax.bind_repr = _159_463; FStar_Syntax_Syntax.actions = actions}))))))))
in (

let _61_663 = (FStar_TypeChecker_DMFF.gen_wps_for_free env effect_binders a wp_a ed)
in (match (_61_663) with
| (sigelts', ed) -> begin
(

let _61_664 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _159_470 = (FStar_Syntax_Print.eff_decl_to_string true ed)
in (FStar_Util.print_string _159_470))
end else begin
()
end
in (

let lift_from_pure_opt = if ((FStar_List.length effect_binders) = (Prims.parse_int "0")) then begin
(

let lift_from_pure = (let _159_473 = (let _159_472 = (let _159_471 = (apply_close lift_from_pure_wp)
in (([]), (_159_471)))
in Some (_159_472))
in {FStar_Syntax_Syntax.source = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.target = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.lift_wp = _159_473; FStar_Syntax_Syntax.lift = None})
in Some (FStar_Syntax_Syntax.Sig_sub_effect (((lift_from_pure), (FStar_Range.dummyRange)))))
end else begin
None
end
in (let _159_476 = (let _159_475 = (let _159_474 = (FStar_ST.read sigelts)
in (FStar_List.rev _159_474))
in (FStar_List.append _159_475 sigelts'))
in ((_159_476), (ed), (lift_from_pure_opt)))))
end))))))
end))))))
end))))))))))))))))
end))
end))))))))))))
end)))))
end)))
end))
end))
end)))
and tc_lex_t : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (

let _61_672 = ()
in (

let _61_680 = ()
in (match (ses) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _61_709, _61_711, [], r))::(FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, _159_481, [], _61_700, r1))::(FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, _159_482, [], _61_689, r2))::[] when (((_159_481 = (Prims.parse_int "0")) && (_159_482 = (Prims.parse_int "0"))) && (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid))) -> begin
(

let u = (FStar_Syntax_Syntax.new_univ_name (Some (r)))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (u))) None r)
in (

let t = (FStar_Syntax_Subst.close_univ_vars ((u)::[]) t)
in (

let tc = FStar_Syntax_Syntax.Sig_inductive_typ (((lex_t), ((u)::[]), ([]), (t), ([]), ((FStar_Syntax_Const.lextop_lid)::(FStar_Syntax_Const.lexcons_lid)::[]), ([]), (r)))
in (

let utop = (FStar_Syntax_Syntax.new_univ_name (Some (r1)))
in (

let lex_top_t = (let _159_485 = (let _159_484 = (let _159_483 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1) FStar_Syntax_Syntax.Delta_constant None)
in ((_159_483), ((FStar_Syntax_Syntax.U_name (utop))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_159_484))
in (FStar_Syntax_Syntax.mk _159_485 None r1))
in (

let lex_top_t = (FStar_Syntax_Subst.close_univ_vars ((utop)::[]) lex_top_t)
in (

let dc_lextop = FStar_Syntax_Syntax.Sig_datacon (((lex_top), ((utop)::[]), (lex_top_t), (FStar_Syntax_Const.lex_t_lid), ((Prims.parse_int "0")), ([]), ([]), (r1)))
in (

let ucons1 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (

let ucons2 = (FStar_Syntax_Syntax.new_univ_name (Some (r2)))
in (

let lex_cons_t = (

let a = (let _159_486 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _159_486))
in (

let hd = (let _159_487 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _159_487))
in (

let tl = (let _159_491 = (let _159_490 = (let _159_489 = (let _159_488 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2) FStar_Syntax_Syntax.Delta_constant None)
in ((_159_488), ((FStar_Syntax_Syntax.U_name (ucons2))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_159_489))
in (FStar_Syntax_Syntax.mk _159_490 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _159_491))
in (

let res = (let _159_494 = (let _159_493 = (let _159_492 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2) FStar_Syntax_Syntax.Delta_constant None)
in ((_159_492), ((FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_159_493))
in (FStar_Syntax_Syntax.mk _159_494 None r2))
in (let _159_495 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow ((((a), (Some (FStar_Syntax_Syntax.imp_tag))))::(((hd), (None)))::(((tl), (None)))::[]) _159_495))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon (((lex_cons), ((ucons1)::(ucons2)::[]), (lex_cons_t), (FStar_Syntax_Const.lex_t_lid), ((Prims.parse_int "0")), ([]), ([]), (r2)))
in (let _159_497 = (let _159_496 = (FStar_TypeChecker_Env.get_range env)
in (((tc)::(dc_lextop)::(dc_lexcons)::[]), ([]), (lids), (_159_496)))
in FStar_Syntax_Syntax.Sig_bundle (_159_497)))))))))))))))
end
| _61_735 -> begin
(let _159_499 = (let _159_498 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle (((ses), ([]), (lids), (FStar_Range.dummyRange)))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _159_498))
in (FStar_All.failwith _159_499))
end))))
and tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _61_745 = (FStar_Syntax_Util.type_u ())
in (match (_61_745) with
| (k, _61_744) -> begin
(

let phi = (let _159_505 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _159_505 (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env)))
in (

let _61_747 = (FStar_TypeChecker_Util.check_uvars r phi)
in FStar_Syntax_Syntax.Sig_assume (((lid), (phi), (quals), (r)))))
end))))
and tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env ses quals lids -> (

let warn_positivity = (fun l r -> (let _159_515 = (let _159_514 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _159_514))
in (FStar_TypeChecker_Errors.diag r _159_515)))
in (

let env0 = env
in (

let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(

let _61_770 = ()
in (

let _61_772 = (warn_positivity tc r)
in (

let _61_776 = (FStar_Syntax_Subst.open_term tps k)
in (match (_61_776) with
| (tps, k) -> begin
(

let _61_781 = (FStar_TypeChecker_TcTerm.tc_binders env tps)
in (match (_61_781) with
| (tps, env_tps, guard_params, us) -> begin
(

let _61_784 = (FStar_Syntax_Util.arrow_formals k)
in (match (_61_784) with
| (indices, t) -> begin
(

let _61_789 = (FStar_TypeChecker_TcTerm.tc_binders env_tps indices)
in (match (_61_789) with
| (indices, env', guard_indices, us') -> begin
(

let _61_797 = (

let _61_794 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' t)
in (match (_61_794) with
| (t, _61_792, g) -> begin
(let _159_522 = (let _159_521 = (let _159_520 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params _159_520))
in (FStar_TypeChecker_Rel.discharge_guard env' _159_521))
in ((t), (_159_522)))
end))
in (match (_61_797) with
| (t, guard) -> begin
(

let k = (let _159_523 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _159_523))
in (

let _61_801 = (FStar_Syntax_Util.type_u ())
in (match (_61_801) with
| (t_type, u) -> begin
(

let _61_802 = (let _159_524 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _159_524))
in (

let t_tc = (let _159_525 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _159_525))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _159_526 = (FStar_TypeChecker_Env.push_let_binding env (FStar_Util.Inr (fv_tc)) (([]), (t_tc)))
in ((_159_526), (FStar_Syntax_Syntax.Sig_inductive_typ (((tc), ([]), (tps), (k), (mutuals), (data), (quals), (r)))), (u), (guard))))))))
end)))
end))
end))
end))
end))
end))))
end
| _61_809 -> begin
(FStar_All.failwith "impossible")
end))
in (

let positive_if_pure = (fun _61_811 l -> ())
in (

let tc_data = (fun env tcs _61_1 -> (match (_61_1) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let _61_828 = ()
in (

let _61_865 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun _61_832 -> (match (_61_832) with
| (se, u_tc) -> begin
if (let _159_538 = (FStar_Util.must (FStar_Syntax_Util.lid_of_sigelt se))
in (FStar_Ident.lid_equals tc_lid _159_538)) then begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_61_834, _61_836, tps, _61_839, _61_841, _61_843, _61_845, _61_847) -> begin
(

let tps = (FStar_All.pipe_right tps (FStar_List.map (fun _61_853 -> (match (_61_853) with
| (x, _61_852) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let tps = (FStar_Syntax_Subst.open_binders tps)
in (let _159_541 = (let _159_540 = (FStar_TypeChecker_Env.push_binders env tps)
in ((_159_540), (tps), (u_tc)))
in Some (_159_541))))
end
| _61_857 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
None
end
end)))
in (match (tps_u_opt) with
| Some (x) -> begin
x
end
| None -> begin
if (FStar_Ident.lid_equals tc_lid FStar_Syntax_Const.exn_lid) then begin
((env), ([]), (FStar_Syntax_Syntax.U_zero))
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected data constructor"), (r)))))
end
end))
in (match (_61_865) with
| (env, tps, u_tc) -> begin
(

let _61_885 = (match ((let _159_542 = (FStar_Syntax_Subst.compress t)
in _159_542.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let _61_873 = (FStar_Util.first_N ntps bs)
in (match (_61_873) with
| (_61_871, bs') -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs'), (res)))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _61_879 -> (match (_61_879) with
| (x, _61_878) -> begin
FStar_Syntax_Syntax.DB ((((ntps - ((Prims.parse_int "1") + i))), (x)))
end))))
in (let _159_545 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _159_545))))
end))
end
| _61_882 -> begin
(([]), (t))
end)
in (match (_61_885) with
| (arguments, result) -> begin
(

let _61_886 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _159_548 = (FStar_Syntax_Print.lid_to_string c)
in (let _159_547 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _159_546 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _159_548 _159_547 _159_546))))
end else begin
()
end
in (

let _61_891 = (tc_tparams env arguments)
in (match (_61_891) with
| (arguments, env', us) -> begin
(

let _61_894 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env' result)
in (match (_61_894) with
| (result, res_lcomp) -> begin
(

let _61_899 = (match ((let _159_549 = (FStar_Syntax_Subst.compress res_lcomp.FStar_Syntax_Syntax.res_typ)
in _159_549.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_61_896) -> begin
()
end
| ty -> begin
(let _159_554 = (let _159_553 = (let _159_552 = (let _159_551 = (FStar_Syntax_Print.term_to_string result)
in (let _159_550 = (FStar_Syntax_Print.term_to_string res_lcomp.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "The type of %s is %s, but since this is the result type of a constructor its type should be Type" _159_551 _159_550)))
in ((_159_552), (r)))
in FStar_Syntax_Syntax.Error (_159_553))
in (Prims.raise _159_554))
end)
in (

let _61_904 = (FStar_Syntax_Util.head_and_args result)
in (match (_61_904) with
| (head, _61_903) -> begin
(

let _61_909 = (match ((let _159_555 = (FStar_Syntax_Subst.compress head)
in _159_555.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _61_908 -> begin
(let _159_560 = (let _159_559 = (let _159_558 = (let _159_557 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (let _159_556 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" _159_557 _159_556)))
in ((_159_558), (r)))
in FStar_Syntax_Syntax.Error (_159_559))
in (Prims.raise _159_560))
end)
in (

let g = (FStar_List.fold_left2 (fun g _61_915 u_x -> (match (_61_915) with
| (x, _61_914) -> begin
(

let _61_917 = ()
in (let _159_564 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _159_564)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _159_568 = (let _159_566 = (FStar_All.pipe_right tps (FStar_List.map (fun _61_923 -> (match (_61_923) with
| (x, _61_922) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append _159_566 arguments))
in (let _159_567 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _159_568 _159_567)))
in ((FStar_Syntax_Syntax.Sig_datacon (((c), ([]), (t), (tc_lid), (ntps), (quals), ([]), (r)))), (g)))))
end)))
end))
end)))
end))
end)))
end
| _61_926 -> begin
(FStar_All.failwith "impossible")
end))
in (

let generalize_and_inst_within = (fun env g tcs datas -> (

let _61_932 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _61_2 -> (match (_61_2) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_61_936, _61_938, tps, k, _61_942, _61_944, _61_946, _61_948) -> begin
(let _159_579 = (let _159_578 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _159_578))
in (FStar_Syntax_Syntax.null_binder _159_579))
end
| _61_952 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _61_3 -> (match (_61_3) with
| FStar_Syntax_Syntax.Sig_datacon (_61_956, _61_958, t, _61_961, _61_963, _61_965, _61_967, _61_969) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _61_973 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let t = (let _159_581 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _159_581))
in (

let _61_976 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _159_582 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _159_582))
end else begin
()
end
in (

let _61_980 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_61_980) with
| (uvs, t) -> begin
(

let _61_982 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _159_586 = (let _159_584 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _159_584 (FStar_String.concat ", ")))
in (let _159_585 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _159_586 _159_585)))
end else begin
()
end
in (

let _61_986 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_61_986) with
| (uvs, t) -> begin
(

let _61_990 = (FStar_Syntax_Util.arrow_formals t)
in (match (_61_990) with
| (args, _61_989) -> begin
(

let _61_993 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_61_993) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun _61_997 se -> (match (_61_997) with
| (x, _61_996) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _61_1001, tps, _61_1004, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let _61_1027 = (match ((let _159_589 = (FStar_Syntax_Subst.compress ty)
in _159_589.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _61_1018 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_61_1018) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _61_1021 -> begin
(let _159_590 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) _159_590 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in ((tps), (t)))
end))
end
| _61_1024 -> begin
(([]), (ty))
end)
in (match (_61_1027) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs), (tps), (t), (mutuals), (datas), (quals), (r)))
end)))
end
| _61_1029 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| _61_1033 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _159_591 -> FStar_Syntax_Syntax.U_name (_159_591))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _61_4 -> (match (_61_4) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _61_1038, _61_1040, _61_1042, _61_1044, _61_1046, _61_1048, _61_1050) -> begin
((tc), (uvs_universes))
end
| _61_1054 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _61_1059 d -> (match (_61_1059) with
| (t, _61_1058) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _61_1063, _61_1065, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (let _159_595 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _159_595 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon (((l), (uvs), (ty), (tc), (ntps), (quals), (mutuals), (r))))
end
| _61_1075 -> begin
(FStar_All.failwith "Impossible")
end)
end)) data_types datas)))
end)
in ((tcs), (datas))))
end))
end))
end)))
end))))))))
in (

let _61_1085 = (FStar_All.pipe_right ses (FStar_List.partition (fun _61_5 -> (match (_61_5) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_61_1079) -> begin
true
end
| _61_1082 -> begin
false
end))))
in (match (_61_1085) with
| (tys, datas) -> begin
(

let _61_1092 = if (FStar_All.pipe_right datas (FStar_Util.for_some (fun _61_6 -> (match (_61_6) with
| FStar_Syntax_Syntax.Sig_datacon (_61_1088) -> begin
false
end
| _61_1091 -> begin
true
end)))) then begin
(let _159_600 = (let _159_599 = (let _159_598 = (FStar_TypeChecker_Env.get_range env)
in (("Mutually defined type contains a non-inductive element"), (_159_598)))
in FStar_Syntax_Syntax.Error (_159_599))
in (Prims.raise _159_600))
end else begin
()
end
in (

let env0 = env
in (

let _61_1111 = (FStar_List.fold_right (fun tc _61_1099 -> (match (_61_1099) with
| (env, all_tcs, g) -> begin
(

let _61_1104 = (tc_tycon env tc)
in (match (_61_1104) with
| (env, tc, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (

let _61_1106 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _159_603 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _159_603))
end else begin
()
end
in (let _159_605 = (let _159_604 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g _159_604))
in ((env), ((((tc), (tc_u)))::all_tcs), (_159_605)))))
end))
end)) tys ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (_61_1111) with
| (env, tcs, g) -> begin
(

let _61_1121 = (FStar_List.fold_right (fun se _61_1115 -> (match (_61_1115) with
| (datas, g) -> begin
(

let _61_1118 = (tc_data env tcs se)
in (match (_61_1118) with
| (data, g') -> begin
(let _159_608 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((data)::datas), (_159_608)))
end))
end)) datas (([]), (g)))
in (match (_61_1121) with
| (datas, g) -> begin
(

let _61_1124 = (let _159_609 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _159_609 datas))
in (match (_61_1124) with
| (tcs, datas) -> begin
(

let sig_bndle = (let _159_611 = (let _159_610 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_159_610)))
in FStar_Syntax_Syntax.Sig_bundle (_159_611))
in (

let data_ops_ses = (let _159_612 = (FStar_List.map (FStar_TypeChecker_Util.mk_data_operations quals env tcs) datas)
in (FStar_All.pipe_right _159_612 FStar_List.flatten))
in (

let datacon_typ = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (_61_1130, _61_1132, t, _61_1135, _61_1137, _61_1139, _61_1141, _61_1143) -> begin
t
end
| _61_1147 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let dr = FStar_Range.dummyRange
in (

let optimized_haseq_scheme = (fun _61_1150 -> (

let haseq_ty = (fun usubst us acc ty -> (

let _61_1177 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _61_1159, bs, t, _61_1163, d_lids, _61_1166, _61_1168) -> begin
((lid), (bs), (t), (d_lids))
end
| _61_1172 -> begin
(FStar_All.failwith "Impossible!")
end)
in (match (_61_1177) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _159_625 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _159_625 t))
in (

let _61_1182 = (FStar_Syntax_Subst.open_term bs t)
in (match (_61_1182) with
| (bs, t) -> begin
(

let ibs = (match ((let _159_626 = (FStar_Syntax_Subst.compress t)
in _159_626.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _61_1185) -> begin
ibs
end
| _61_1189 -> begin
[]
end)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _159_629 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _159_628 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _159_629 _159_628)))
in (

let ind = (let _159_632 = (FStar_List.map (fun _61_1196 -> (match (_61_1196) with
| (bv, aq) -> begin
(let _159_631 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_159_631), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _159_632 None dr))
in (

let ind = (let _159_635 = (FStar_List.map (fun _61_1200 -> (match (_61_1200) with
| (bv, aq) -> begin
(let _159_634 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_159_634), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _159_635 None dr))
in (

let haseq_ind = (let _159_637 = (let _159_636 = (FStar_Syntax_Syntax.as_arg ind)
in (_159_636)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _159_637 None dr))
in (

let bs' = (FStar_List.filter (fun b -> (

let _61_1211 = acc
in (match (_61_1211) with
| (_61_1205, en, _61_1208, _61_1210) -> begin
(

let opt = (let _159_640 = (let _159_639 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _159_639))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort _159_640 false))
in (match (opt) with
| None -> begin
false
end
| Some (_61_1215) -> begin
true
end))
end))) bs)
in (

let haseq_bs = (FStar_List.fold_left (fun t b -> (let _159_646 = (let _159_645 = (let _159_644 = (let _159_643 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b))
in (FStar_Syntax_Syntax.as_arg _159_643))
in (_159_644)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _159_645 None dr))
in (FStar_Syntax_Util.mk_conj t _159_646))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml = (

let _61_1222 = fml
in (let _159_652 = (let _159_651 = (let _159_650 = (let _159_649 = (let _159_648 = (let _159_647 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_159_647)::[])
in (_159_648)::[])
in FStar_Syntax_Syntax.Meta_pattern (_159_649))
in ((fml), (_159_650)))
in FStar_Syntax_Syntax.Tm_meta (_159_651))
in {FStar_Syntax_Syntax.n = _159_652; FStar_Syntax_Syntax.tk = _61_1222.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _61_1222.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _61_1222.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _159_658 = (let _159_657 = (let _159_656 = (let _159_655 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _159_655 None))
in (FStar_Syntax_Syntax.as_arg _159_656))
in (_159_657)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _159_658 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _159_664 = (let _159_663 = (let _159_662 = (let _159_661 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _159_661 None))
in (FStar_Syntax_Syntax.as_arg _159_662))
in (_159_663)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _159_664 None dr))) bs fml)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let _61_1236 = acc
in (match (_61_1236) with
| (l_axioms, env, guard', cond') -> begin
(

let env = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env = (FStar_TypeChecker_Env.push_binders env ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (_61_1241, _61_1243, _61_1245, t_lid, _61_1248, _61_1250, _61_1252, _61_1254) -> begin
(t_lid = lid)
end
| _61_1258 -> begin
(FStar_All.failwith "Impossible")
end)) datas)
in (

let haseq_data = (fun data -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (match ((let _159_668 = (FStar_Syntax_Subst.compress dt)
in _159_668.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _61_1266) -> begin
(

let dbs = (let _159_669 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _159_669))
in (

let dbs = (let _159_670 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _159_670 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let haseq_b = (let _159_674 = (let _159_673 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_159_673)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _159_674 None dr))
in (

let sort_range = (Prims.fst b).FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos
in (

let haseq_b = (let _159_676 = (let _159_675 = (FStar_Syntax_Print.term_to_string ind)
in (FStar_Util.format1 "Failed to prove that the type \'%s\' supports decidable equality because of this argument; add the \'noeq\' qualifier" _159_675))
in (FStar_TypeChecker_Util.label _159_676 sort_range haseq_b))
in (FStar_Syntax_Util.mk_conj t haseq_b))))) FStar_Syntax_Util.t_true dbs)
in (FStar_List.fold_right (fun b t -> (let _159_682 = (let _159_681 = (let _159_680 = (let _159_679 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _159_679 None))
in (FStar_Syntax_Syntax.as_arg _159_680))
in (_159_681)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _159_682 None dr))) dbs cond)))))
end
| _61_1281 -> begin
FStar_Syntax_Util.t_true
end))))
in (

let cond = (FStar_List.fold_left (fun acc d -> (let _159_685 = (haseq_data d)
in (FStar_Syntax_Util.mk_conj acc _159_685))) FStar_Syntax_Util.t_true t_datas)
in (

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (let _159_687 = (FStar_Syntax_Util.mk_conj guard' guard)
in (let _159_686 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml)))::[]))), (env), (_159_687), (_159_686))))))))))
end)))))))))))))))
end))))
end)))
in (

let us = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_61_1288, us, _61_1291, _61_1293, _61_1295, _61_1297, _61_1299, _61_1301) -> begin
us
end
| _61_1305 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let _61_1309 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (_61_1309) with
| (usubst, us) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (

let _61_1311 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq")
in (

let _61_1313 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle)
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let _61_1320 = (FStar_List.fold_left (haseq_ty usubst us) (([]), (env), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (_61_1320) with
| (axioms, env, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let _61_1325 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env phi)
in (match (_61_1325) with
| (phi, _61_1324) -> begin
(

let _61_1326 = if (FStar_TypeChecker_Env.should_verify env) then begin
(let _159_688 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi)))
in (FStar_TypeChecker_Rel.force_trivial_guard env _159_688))
end else begin
()
end
in (

let ses = (FStar_List.fold_left (fun l _61_1331 -> (match (_61_1331) with
| (lid, fml) -> begin
(

let se = (tc_assume env lid fml [] dr)
in (FStar_List.append l ((se)::[])))
end)) [] axioms)
in (

let _61_1334 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq")
in ses)))
end)))
end))))))
end)))))
in (

let unoptimized_haseq_scheme = (fun _61_1337 -> (

let mutuals = (FStar_List.map (fun ty -> (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _61_1342, _61_1344, _61_1346, _61_1348, _61_1350, _61_1352, _61_1354) -> begin
lid
end
| _61_1358 -> begin
(FStar_All.failwith "Impossible!")
end)) tcs)
in (

let haseq_ty = (fun usubst us acc ty -> (

let _61_1385 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _61_1367, bs, t, _61_1371, d_lids, _61_1374, _61_1376) -> begin
((lid), (bs), (t), (d_lids))
end
| _61_1380 -> begin
(FStar_All.failwith "Impossible!")
end)
in (match (_61_1385) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _159_702 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _159_702 t))
in (

let _61_1390 = (FStar_Syntax_Subst.open_term bs t)
in (match (_61_1390) with
| (bs, t) -> begin
(

let ibs = (match ((let _159_703 = (FStar_Syntax_Subst.compress t)
in _159_703.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _61_1393) -> begin
ibs
end
| _61_1397 -> begin
[]
end)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _159_706 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _159_705 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _159_706 _159_705)))
in (

let ind = (let _159_709 = (FStar_List.map (fun _61_1404 -> (match (_61_1404) with
| (bv, aq) -> begin
(let _159_708 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_159_708), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _159_709 None dr))
in (

let ind = (let _159_712 = (FStar_List.map (fun _61_1408 -> (match (_61_1408) with
| (bv, aq) -> begin
(let _159_711 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_159_711), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _159_712 None dr))
in (

let haseq_ind = (let _159_714 = (let _159_713 = (FStar_Syntax_Syntax.as_arg ind)
in (_159_713)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _159_714 None dr))
in (

let rec is_mutual = (fun t -> (match ((let _159_718 = (FStar_Syntax_Subst.compress t)
in _159_718.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.existsb (fun lid -> (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) mutuals)
end
| FStar_Syntax_Syntax.Tm_uinst (t', _61_1419) -> begin
(is_mutual t')
end
| FStar_Syntax_Syntax.Tm_refine (bv, t') -> begin
(is_mutual bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_app (t', args) -> begin
if (is_mutual t') then begin
true
end else begin
(let _159_720 = (FStar_List.map Prims.fst args)
in (exists_mutual _159_720))
end
end
| FStar_Syntax_Syntax.Tm_meta (t', _61_1432) -> begin
(is_mutual t')
end
| _61_1436 -> begin
false
end))
and exists_mutual = (fun _61_7 -> (match (_61_7) with
| [] -> begin
false
end
| (hd)::tl -> begin
((is_mutual hd) || (exists_mutual tl))
end))
in (

let haseq_data = (fun acc data -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (match ((let _159_726 = (FStar_Syntax_Subst.compress dt)
in _159_726.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _61_1449) -> begin
(

let dbs = (let _159_727 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _159_727))
in (

let dbs = (let _159_728 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _159_728 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let sort = (Prims.fst b).FStar_Syntax_Syntax.sort
in (

let haseq_sort = (let _159_732 = (let _159_731 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_159_731)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _159_732 None dr))
in (

let haseq_sort = if (is_mutual sort) then begin
(FStar_Syntax_Util.mk_imp haseq_ind haseq_sort)
end else begin
haseq_sort
end
in (FStar_Syntax_Util.mk_conj t haseq_sort))))) FStar_Syntax_Util.t_true dbs)
in (

let cond = (FStar_List.fold_right (fun b t -> (let _159_738 = (let _159_737 = (let _159_736 = (let _159_735 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _159_735 None))
in (FStar_Syntax_Syntax.as_arg _159_736))
in (_159_737)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _159_738 None dr))) dbs cond)
in (FStar_Syntax_Util.mk_conj acc cond))))))
end
| _61_1465 -> begin
acc
end))))
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (_61_1468, _61_1470, _61_1472, t_lid, _61_1475, _61_1477, _61_1479, _61_1481) -> begin
(t_lid = lid)
end
| _61_1485 -> begin
(FStar_All.failwith "Impossible")
end)) datas)
in (

let data_cond = (FStar_List.fold_left haseq_data FStar_Syntax_Util.t_true t_datas)
in (

let fml = (FStar_Syntax_Util.mk_imp data_cond haseq_ind)
in (

let fml = (

let _61_1489 = fml
in (let _159_745 = (let _159_744 = (let _159_743 = (let _159_742 = (let _159_741 = (let _159_740 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_159_740)::[])
in (_159_741)::[])
in FStar_Syntax_Syntax.Meta_pattern (_159_742))
in ((fml), (_159_743)))
in FStar_Syntax_Syntax.Tm_meta (_159_744))
in {FStar_Syntax_Syntax.n = _159_745; FStar_Syntax_Syntax.tk = _61_1489.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _61_1489.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _61_1489.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _159_751 = (let _159_750 = (let _159_749 = (let _159_748 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _159_748 None))
in (FStar_Syntax_Syntax.as_arg _159_749))
in (_159_750)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _159_751 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _159_757 = (let _159_756 = (let _159_755 = (let _159_754 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _159_754 None))
in (FStar_Syntax_Syntax.as_arg _159_755))
in (_159_756)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _159_757 None dr))) bs fml)
in (FStar_Syntax_Util.mk_conj acc fml)))))))))))))))
end))))
end)))
in (

let _61_1519 = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, _61_1502, _61_1504, _61_1506, _61_1508, _61_1510, _61_1512) -> begin
((lid), (us))
end
| _61_1516 -> begin
(FStar_All.failwith "Impossible!")
end))
in (match (_61_1519) with
| (lid, us) -> begin
(

let _61_1522 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (_61_1522) with
| (usubst, us) -> begin
(

let fml = (FStar_List.fold_left (haseq_ty usubst us) FStar_Syntax_Util.t_true tcs)
in (

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (

let _61_1525 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq")
in (

let _61_1527 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle)
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let se = (let _159_758 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (tc_assume env _159_758 fml [] dr))
in (

let _61_1531 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq")
in (se)::[])))))))
end))
end)))))
in (

let skip_prims_type = (fun _61_1534 -> (

let lid = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _61_1539, _61_1541, _61_1543, _61_1545, _61_1547, _61_1549, _61_1551) -> begin
lid
end
| _61_1555 -> begin
(FStar_All.failwith "Impossible")
end))
in (

let types_to_skip = ("c_False")::("c_True")::("equals")::("h_equals")::("c_and")::("c_or")::[]
in (FStar_List.existsb (fun s -> (s = lid.FStar_Ident.ident.FStar_Ident.idText)) types_to_skip))))
in (

let is_noeq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Noeq)) quals)
in if ((((FStar_List.length tcs) = (Prims.parse_int "0")) || ((FStar_Ident.lid_equals env.FStar_TypeChecker_Env.curmodule FStar_Syntax_Const.prims_lid) && (skip_prims_type ()))) || is_noeq) then begin
(((sig_bndle)::[]), (data_ops_ses))
end else begin
(

let is_unopteq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Unopteq)) quals)
in (

let ses = if is_unopteq then begin
(unoptimized_haseq_scheme ())
end else begin
(optimized_haseq_scheme ())
end
in (let _159_767 = (let _159_766 = (let _159_765 = (let _159_764 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_159_764)))
in FStar_Syntax_Syntax.Sig_bundle (_159_765))
in (_159_766)::ses)
in ((_159_767), (data_ops_ses)))))
end))))))))
end))
end))
end))))
end)))))))))
and tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env se -> (

let env = (set_hint_correlator env se)
in (

let _61_1567 = (FStar_TypeChecker_Util.check_sigelt_quals env se)
in (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let se = (tc_lex_t env ses quals lids)
in (let _159_770 = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (_159_770), ([])))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _61_1592 = (tc_inductive env ses quals lids)
in (match (_61_1592) with
| (ses, projectors_ses) -> begin
(

let env = (FStar_List.fold_left (fun env' se -> (FStar_TypeChecker_Env.push_sigelt env' se)) env ses)
in ((ses), (env), (projectors_ses)))
end)))
end
| FStar_Syntax_Syntax.Sig_pragma (p, r) -> begin
(

let set_options = (fun t s -> (match ((FStar_Options.set_options t s)) with
| FStar_Getopt.Success -> begin
()
end
| FStar_Getopt.Help -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Failed to process pragma: use \'fstar --help\' to see which options are available"), (r)))))
end
| FStar_Getopt.Error (s) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Failed to process pragma: " s)), (r)))))
end))
in (match (p) with
| FStar_Syntax_Syntax.SetOptions (o) -> begin
(

let _61_1609 = (set_options FStar_Options.Set o)
in (((se)::[]), (env), ([])))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(

let _61_1613 = (let _159_777 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _159_777 Prims.ignore))
in (

let _61_1618 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (

let _61_1620 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (((se)::[]), (env), ([])))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_61_1623) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(

let ne = (tc_eff_decl env ne)
in (

let se = FStar_Syntax_Syntax.Sig_new_effect (((ne), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (

let _61_1639 = (FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun _61_1634 a -> (match (_61_1634) with
| (env, ses) -> begin
(

let se_let = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a)
in (let _159_780 = (FStar_TypeChecker_Env.push_sigelt env se_let)
in ((_159_780), ((se_let)::ses))))
end)) ((env), ((se)::[]))))
in (match (_61_1639) with
| (env, ses) -> begin
(((se)::[]), (env), ([]))
end)))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(

let ed_src = (FStar_TypeChecker_Env.get_effect_decl env sub.FStar_Syntax_Syntax.source)
in (

let ed_tgt = (FStar_TypeChecker_Env.get_effect_decl env sub.FStar_Syntax_Syntax.target)
in (

let _61_1648 = (let _159_781 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _159_781))
in (match (_61_1648) with
| (a, wp_a_src) -> begin
(

let _61_1651 = (let _159_782 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _159_782))
in (match (_61_1651) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (let _159_786 = (let _159_785 = (let _159_784 = (let _159_783 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (_159_783)))
in FStar_Syntax_Syntax.NT (_159_784))
in (_159_785)::[])
in (FStar_Syntax_Subst.subst _159_786 wp_b_tgt))
in (

let expected_k = (let _159_791 = (let _159_789 = (FStar_Syntax_Syntax.mk_binder a)
in (let _159_788 = (let _159_787 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_159_787)::[])
in (_159_789)::_159_788))
in (let _159_790 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _159_791 _159_790)))
in (

let repr_type = (fun eff_name a wp -> (

let no_reify = (fun l -> (let _159_803 = (let _159_802 = (let _159_801 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _159_800 = (FStar_TypeChecker_Env.get_range env)
in ((_159_801), (_159_800))))
in FStar_Syntax_Syntax.Error (_159_802))
in (Prims.raise _159_803)))
in (match ((FStar_TypeChecker_Env.effect_decl_opt env eff_name)) with
| None -> begin
(no_reify eff_name)
end
| Some (ed) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((FStar_Syntax_Syntax.U_unknown)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in if (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)))) then begin
(no_reify eff_name)
end else begin
(let _159_810 = (let _159_808 = (let _159_807 = (let _159_806 = (FStar_Syntax_Syntax.as_arg a)
in (let _159_805 = (let _159_804 = (FStar_Syntax_Syntax.as_arg wp)
in (_159_804)::[])
in (_159_806)::_159_805))
in ((repr), (_159_807)))
in FStar_Syntax_Syntax.Tm_app (_159_808))
in (let _159_809 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _159_810 None _159_809)))
end)
end)))
in (

let _61_1692 = (match (((sub.FStar_Syntax_Syntax.lift), (sub.FStar_Syntax_Syntax.lift_wp))) with
| (None, None) -> begin
(FStar_All.failwith "Impossible")
end
| (lift, Some (_61_1669, lift_wp)) -> begin
(let _159_811 = (check_and_gen env lift_wp expected_k)
in ((lift), (_159_811)))
end
| (Some (what, lift), None) -> begin
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange))
in (

let _61_1685 = (FStar_TypeChecker_DMFF.star_expr dmff_env lift)
in (match (_61_1685) with
| (_61_1682, lift_wp, lift_elab) -> begin
(

let _61_1686 = (recheck_debug "lift-wp" env lift_wp)
in (

let _61_1688 = (recheck_debug "lift-elab" env lift_elab)
in ((Some ((([]), (lift_elab)))), ((([]), (lift_wp))))))
end)))
end)
in (match (_61_1692) with
| (lift, lift_wp) -> begin
(

let lax = env.FStar_TypeChecker_Env.lax
in (

let env = (

let _61_1694 = env
in {FStar_TypeChecker_Env.solver = _61_1694.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _61_1694.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _61_1694.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _61_1694.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _61_1694.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _61_1694.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _61_1694.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _61_1694.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _61_1694.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _61_1694.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _61_1694.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _61_1694.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _61_1694.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _61_1694.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _61_1694.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _61_1694.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _61_1694.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _61_1694.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _61_1694.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _61_1694.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _61_1694.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _61_1694.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _61_1694.FStar_TypeChecker_Env.qname_and_index})
in (

let lift = (match (lift) with
| None -> begin
None
end
| Some (_61_1699, lift) -> begin
(

let _61_1705 = (let _159_812 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _159_812))
in (match (_61_1705) with
| (a, wp_a_src) -> begin
(

let wp_a = (FStar_Syntax_Syntax.new_bv None wp_a_src)
in (

let a_typ = (FStar_Syntax_Syntax.bv_to_name a)
in (

let wp_a_typ = (FStar_Syntax_Syntax.bv_to_name wp_a)
in (

let repr_f = (repr_type sub.FStar_Syntax_Syntax.source a_typ wp_a_typ)
in (

let repr_result = (

let lift_wp = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env (Prims.snd lift_wp))
in (

let lift_wp_a = (let _159_819 = (let _159_817 = (let _159_816 = (let _159_815 = (FStar_Syntax_Syntax.as_arg a_typ)
in (let _159_814 = (let _159_813 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (_159_813)::[])
in (_159_815)::_159_814))
in ((lift_wp), (_159_816)))
in FStar_Syntax_Syntax.Tm_app (_159_817))
in (let _159_818 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _159_819 None _159_818)))
in (repr_type sub.FStar_Syntax_Syntax.target a_typ lift_wp_a)))
in (

let expected_k = (let _159_826 = (let _159_824 = (FStar_Syntax_Syntax.mk_binder a)
in (let _159_823 = (let _159_822 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (let _159_821 = (let _159_820 = (FStar_Syntax_Syntax.null_binder repr_f)
in (_159_820)::[])
in (_159_822)::_159_821))
in (_159_824)::_159_823))
in (let _159_825 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow _159_826 _159_825)))
in (

let _61_1719 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (_61_1719) with
| (expected_k, _61_1716, _61_1718) -> begin
(

let lift = (check_and_gen env lift expected_k)
in Some (lift))
end))))))))
end))
end)
in (

let env = (

let _61_1722 = env
in {FStar_TypeChecker_Env.solver = _61_1722.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _61_1722.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _61_1722.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _61_1722.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _61_1722.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _61_1722.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _61_1722.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _61_1722.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _61_1722.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _61_1722.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _61_1722.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _61_1722.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _61_1722.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _61_1722.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _61_1722.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _61_1722.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _61_1722.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _61_1722.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = lax; FStar_TypeChecker_Env.lax_universes = _61_1722.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _61_1722.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _61_1722.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _61_1722.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _61_1722.FStar_TypeChecker_Env.qname_and_index})
in (

let sub = (

let _61_1725 = sub
in {FStar_Syntax_Syntax.source = _61_1725.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _61_1725.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = Some (lift_wp); FStar_Syntax_Syntax.lift = lift})
in (

let se = FStar_Syntax_Syntax.Sig_sub_effect (((sub), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env), ([])))))))))
end)))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, flags, r) -> begin
(

let _61_1739 = ()
in (

let env0 = env
in (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _61_1745 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_61_1745) with
| (tps, c) -> begin
(

let _61_1749 = (tc_tparams env tps)
in (match (_61_1749) with
| (tps, env, us) -> begin
(

let _61_1753 = (FStar_TypeChecker_TcTerm.tc_comp env c)
in (match (_61_1753) with
| (c, u, g) -> begin
(

let _61_1754 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

let _61_1760 = (let _159_827 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _159_827))
in (match (_61_1760) with
| (uvs, t) -> begin
(

let _61_1779 = (match ((let _159_829 = (let _159_828 = (FStar_Syntax_Subst.compress t)
in _159_828.FStar_Syntax_Syntax.n)
in ((tps), (_159_829)))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_61_1763, c)) -> begin
(([]), (c))
end
| (_61_1769, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
((tps), (c))
end
| _61_1776 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_61_1779) with
| (tps, c) -> begin
(

let _61_1784 = if (((FStar_List.length uvs) <> (Prims.parse_int "1")) && (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid)))) then begin
(

let _61_1783 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_61_1783) with
| (_61_1781, t) -> begin
(let _159_835 = (let _159_834 = (let _159_833 = (let _159_832 = (FStar_Syntax_Print.lid_to_string lid)
in (let _159_831 = (FStar_All.pipe_right (FStar_List.length uvs) FStar_Util.string_of_int)
in (let _159_830 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)" _159_832 _159_831 _159_830))))
in ((_159_833), (r)))
in FStar_Syntax_Syntax.Error (_159_834))
in (Prims.raise _159_835))
end))
end else begin
()
end
in (

let se = FStar_Syntax_Syntax.Sig_effect_abbrev (((lid), (uvs), (tps), (c), (tags), (flags), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env0 se)
in (((se)::[]), (env), ([])))))
end))
end)))))
end))
end))
end)))))
end
| (FStar_Syntax_Syntax.Sig_declare_typ (_, _, _, quals, _)) | (FStar_Syntax_Syntax.Sig_let (_, _, _, quals, _)) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _61_8 -> (match (_61_8) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| _61_1812 -> begin
false
end)))) -> begin
(([]), (env), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t, quals, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _61_1826 = if (uvs = []) then begin
(let _159_838 = (let _159_837 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _159_837))
in (check_and_gen env t _159_838))
end else begin
(

let _61_1823 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_61_1823) with
| (uvs, t) -> begin
(let _159_842 = (let _159_841 = (let _159_840 = (let _159_839 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _159_839))
in (tc_check_trivial_guard env t _159_840))
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) _159_841))
in ((uvs), (_159_842)))
end))
end
in (match (_61_1826) with
| (uvs, t) -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (uvs), (t), (quals), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env), ([]))))
end)))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(

let se = (tc_assume env lid phi quals r)
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env), ([]))))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (

let _61_1846 = (FStar_TypeChecker_TcTerm.tc_term env e)
in (match (_61_1846) with
| (e, c, g1) -> begin
(

let _61_1851 = (let _159_846 = (let _159_843 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_159_843))
in (let _159_845 = (let _159_844 = (c.FStar_Syntax_Syntax.comp ())
in ((e), (_159_844)))
in (FStar_TypeChecker_TcTerm.check_expected_effect env _159_846 _159_845)))
in (match (_61_1851) with
| (e, _61_1849, g) -> begin
(

let _61_1852 = (let _159_847 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _159_847))
in (

let se = FStar_Syntax_Syntax.Sig_main (((e), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env), ([])))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, lids, quals, attrs) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let check_quals_eq = (fun l qopt q -> (match (qopt) with
| None -> begin
Some (q)
end
| Some (q') -> begin
if (((FStar_List.length q) = (FStar_List.length q')) && (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q q')) then begin
Some (q)
end else begin
(let _159_859 = (let _159_858 = (let _159_857 = (let _159_856 = (FStar_Syntax_Print.lid_to_string l)
in (let _159_855 = (FStar_Syntax_Print.quals_to_string q)
in (let _159_854 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _159_856 _159_855 _159_854))))
in ((_159_857), (r)))
in FStar_Syntax_Syntax.Error (_159_858))
in (Prims.raise _159_859))
end
end))
in (

let _61_1899 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _61_1874 lb -> (match (_61_1874) with
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _61_1895 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
((false), (lb), (quals_opt))
end else begin
((gen), (lb), (quals_opt))
end
end
| Some ((uvs, tval), quals) -> begin
(

let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (

let _61_1888 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _61_1887 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (

let _61_1890 = if ((lb.FStar_Syntax_Syntax.lbunivs <> []) && ((FStar_List.length lb.FStar_Syntax_Syntax.lbunivs) <> (FStar_List.length uvs))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inline universes are incoherent with annotation from val declaration"), (r)))))
end else begin
()
end
in (let _159_862 = (FStar_Syntax_Syntax.mk_lb ((FStar_Util.Inr (lbname)), (uvs), (FStar_Syntax_Const.effect_ALL_lid), (tval), (lb.FStar_Syntax_Syntax.lbdef)))
in ((false), (_159_862), (quals_opt))))))
end)
in (match (_61_1895) with
| (gen, lb, quals_opt) -> begin
((gen), ((lb)::lbs), (quals_opt))
end)))
end)) ((true), ([]), (if (quals = []) then begin
None
end else begin
Some (quals)
end))))
in (match (_61_1899) with
| (should_generalize, lbs', quals_opt) -> begin
(

let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Visible_default)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _61_9 -> (match (_61_9) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Visible_default) | (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> begin
true
end
| _61_1908 -> begin
false
end)))) then begin
q
end else begin
(FStar_Syntax_Syntax.Visible_default)::q
end
end)
in (

let lbs' = (FStar_List.rev lbs')
in (

let e = (let _159_866 = (let _159_865 = (let _159_864 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((((Prims.fst lbs)), (lbs'))), (_159_864)))
in FStar_Syntax_Syntax.Tm_let (_159_865))
in (FStar_Syntax_Syntax.mk _159_866 None r))
in (

let _61_1942 = (match ((FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term (

let _61_1912 = env
in {FStar_TypeChecker_Env.solver = _61_1912.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _61_1912.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _61_1912.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _61_1912.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _61_1912.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _61_1912.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _61_1912.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _61_1912.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _61_1912.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _61_1912.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _61_1912.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _61_1912.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _61_1912.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _61_1912.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _61_1912.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _61_1912.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _61_1912.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _61_1912.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _61_1912.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _61_1912.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _61_1912.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _61_1912.FStar_TypeChecker_Env.qname_and_index}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _61_1919; FStar_Syntax_Syntax.pos = _61_1917; FStar_Syntax_Syntax.vars = _61_1915}, _61_1926, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_61_1930, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _61_1936 -> begin
quals
end)
in ((FStar_Syntax_Syntax.Sig_let (((lbs), (r), (lids), (quals), (attrs)))), (lbs)))
end
| _61_1939 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_61_1942) with
| (se, lbs) -> begin
(

let _61_1948 = if (log env) then begin
(let _159_874 = (let _159_873 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (match ((let _159_870 = (let _159_869 = (let _159_868 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _159_868.FStar_Syntax_Syntax.fv_name)
in _159_869.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _159_870))) with
| None -> begin
true
end
| _61_1946 -> begin
false
end)
in if should_log then begin
(let _159_872 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _159_871 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _159_872 _159_871)))
end else begin
""
end))))
in (FStar_All.pipe_right _159_873 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _159_874))
end else begin
()
end
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env), ([]))))
end)))))
end))))
end))))


let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _61_10 -> (match (_61_10) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _61_1958 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _61_1968 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_61_1970) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _61_1981, r) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _61_1988 -> (match (_61_1988) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _61_1994, _61_1996, quals, r) -> begin
(

let dec = (let _159_888 = (let _159_887 = (let _159_886 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow bs _159_886))
in ((l), (us), (_159_887), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (_159_888))
in (((dec)::out), (hidden)))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _61_2006, _61_2008, _61_2010, _61_2012, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]), (r)))
in (((dec)::out), ((l)::hidden)))
end
| _61_2018 -> begin
((out), (hidden))
end)
end)) ses (([]), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end
| FStar_Syntax_Syntax.Sig_assume (_61_2020, _61_2022, quals, _61_2025) -> begin
if (is_abstract quals) then begin
(([]), (hidden))
end else begin
(((se)::[]), (hidden))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, us, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) then begin
(((FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]), (r))))::[]), ((l)::hidden))
end else begin
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _61_11 -> (match (_61_11) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _61_2044 -> begin
false
end)))) then begin
(((se)::[]), (hidden))
end else begin
(([]), (hidden))
end
end
end
| FStar_Syntax_Syntax.Sig_main (_61_2046) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _61_2065, _61_2067, quals, _61_2070) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if (FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))) then begin
(([]), (hidden))
end else begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::[]), ((FStar_Ident.range_of_lid lid))))
in (((dec)::[]), ((lid)::hidden)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals, _61_2081) -> begin
if (is_abstract quals) then begin
(let _159_895 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _159_894 = (let _159_893 = (let _159_892 = (let _159_891 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _159_891.FStar_Syntax_Syntax.fv_name)
in _159_892.FStar_Syntax_Syntax.v)
in ((_159_893), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (_159_894)))))
in ((_159_895), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let rec process_one_decl = (fun _61_2092 se -> (match (_61_2092) with
| (ses, exports, env, hidden) -> begin
(

let _61_2094 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _159_904 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _159_904))
end else begin
()
end
in (

let _61_2099 = (tc_decl env se)
in (match (_61_2099) with
| (ses', env, ses_elaborated) -> begin
(

let _61_2102 = if ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _159_909 = (FStar_List.fold_left (fun s se -> (let _159_908 = (let _159_907 = (FStar_Syntax_Print.sigelt_to_string se)
in (Prims.strcat _159_907 "\n"))
in (Prims.strcat s _159_908))) "" ses')
in (FStar_Util.print1 "Checked: %s\n" _159_909))
end else begin
()
end
in (

let _61_2105 = (FStar_List.iter (fun se -> (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)) ses')
in (

let _61_2114 = (FStar_List.fold_left (fun _61_2109 se -> (match (_61_2109) with
| (le, lh) -> begin
(

let tup = (for_export hidden se)
in (((FStar_List.rev_append (Prims.fst tup) le)), ((FStar_List.rev_append (Prims.snd tup) lh))))
end)) (([]), ([])) ses')
in (match (_61_2114) with
| (exported, hidden) -> begin
(FStar_List.fold_left process_one_decl (((FStar_List.rev_append ses' ses)), (((FStar_List.rev_append exported []))::exports), (env), (hidden)) ses_elaborated)
end))))
end)))
end))
in (

let _61_2144 = (FStar_List.fold_left (fun acc se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, r) -> begin
(

let _61_2128 = acc
in (match (_61_2128) with
| (_61_2122, _61_2124, env, _61_2127) -> begin
(

let _61_2132 = (cps_and_elaborate env ne)
in (match (_61_2132) with
| (ses, ne, lift_from_pure_opt) -> begin
(

let ses = (match (lift_from_pure_opt) with
| Some (lift) -> begin
(FStar_List.append ses ((FStar_Syntax_Syntax.Sig_new_effect (((ne), (r))))::(lift)::[]))
end
| None -> begin
(FStar_List.append ses ((FStar_Syntax_Syntax.Sig_new_effect (((ne), (r))))::[]))
end)
in (FStar_List.fold_left process_one_decl acc ses))
end))
end))
end
| _61_2138 -> begin
(process_one_decl acc se)
end)) (([]), ([]), (env), ([])) ses)
in (match (_61_2144) with
| (ses, exports, env, _61_2143) -> begin
(let _159_915 = (FStar_All.pipe_right (FStar_List.rev_append exports []) FStar_List.flatten)
in (((FStar_List.rev_append ses [])), (_159_915), (env)))
end))))


let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (

let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let msg = (Prims.strcat "Internals for " name)
in (

let env = (

let _61_2149 = env
in (let _159_920 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _61_2149.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _61_2149.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _61_2149.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _61_2149.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _61_2149.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _61_2149.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _61_2149.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _61_2149.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _61_2149.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _61_2149.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _61_2149.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _61_2149.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _61_2149.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _61_2149.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _61_2149.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _61_2149.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _159_920; FStar_TypeChecker_Env.lax = _61_2149.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _61_2149.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _61_2149.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _61_2149.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _61_2149.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _61_2149.FStar_TypeChecker_Env.qname_and_index}))
in (

let _61_2152 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
in (

let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

let _61_2158 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_61_2158) with
| (ses, exports, env) -> begin
(((

let _61_2159 = modul
in {FStar_Syntax_Syntax.name = _61_2159.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _61_2159.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _61_2159.FStar_Syntax_Syntax.is_interface})), (exports), (env))
end))))))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let _61_2167 = (tc_decls env decls)
in (match (_61_2167) with
| (ses, exports, env) -> begin
(

let modul = (

let _61_2168 = modul
in {FStar_Syntax_Syntax.name = _61_2168.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _61_2168.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _61_2168.FStar_Syntax_Syntax.is_interface})
in ((modul), (exports), (env)))
end)))


let check_exports : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env modul exports -> (

let env = (

let _61_2174 = env
in {FStar_TypeChecker_Env.solver = _61_2174.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _61_2174.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _61_2174.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _61_2174.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _61_2174.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _61_2174.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _61_2174.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _61_2174.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _61_2174.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _61_2174.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _61_2174.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _61_2174.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _61_2174.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _61_2174.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _61_2174.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _61_2174.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _61_2174.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = true; FStar_TypeChecker_Env.type_of = _61_2174.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _61_2174.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _61_2174.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _61_2174.FStar_TypeChecker_Env.qname_and_index})
in (

let check_term = (fun lid univs t -> (

let _61_2183 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_61_2183) with
| (univs, t) -> begin
(

let _61_2185 = if (let _159_940 = (let _159_939 = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (FStar_TypeChecker_Env.debug _159_939))
in (FStar_All.pipe_left _159_940 (FStar_Options.Other ("Exports")))) then begin
(let _159_945 = (FStar_Syntax_Print.lid_to_string lid)
in (let _159_944 = (let _159_942 = (FStar_All.pipe_right univs (FStar_List.map (fun x -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (x))))))
in (FStar_All.pipe_right _159_942 (FStar_String.concat ", ")))
in (let _159_943 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print3 "Checking for export %s <%s> : %s\n" _159_945 _159_944 _159_943))))
end else begin
()
end
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env univs)
in (let _159_946 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env t)
in (FStar_All.pipe_right _159_946 Prims.ignore))))
end)))
in (

let check_term = (fun lid univs t -> (

let _61_2192 = (let _159_955 = (let _159_954 = (FStar_Syntax_Print.lid_to_string modul.FStar_Syntax_Syntax.name)
in (let _159_953 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Interface of %s violates its abstraction (add a \'private\' qualifier to \'%s\'?)" _159_954 _159_953)))
in (FStar_TypeChecker_Errors.message_prefix.FStar_TypeChecker_Errors.set_prefix _159_955))
in (

let _61_2194 = (check_term lid univs t)
in (FStar_TypeChecker_Errors.message_prefix.FStar_TypeChecker_Errors.clear_prefix ()))))
in (

let rec check_sigelt = (fun _61_12 -> (match (_61_12) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _61_2201, _61_2203) -> begin
if (not ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private)))) then begin
(FStar_All.pipe_right ses (FStar_List.iter check_sigelt))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_inductive_typ (l, univs, binders, typ, _61_2211, _61_2213, _61_2215, r) -> begin
(

let t = (let _159_960 = (let _159_959 = (let _159_958 = (FStar_Syntax_Syntax.mk_Total typ)
in ((binders), (_159_958)))
in FStar_Syntax_Syntax.Tm_arrow (_159_959))
in (FStar_Syntax_Syntax.mk _159_960 None r))
in (check_term l univs t))
end
| FStar_Syntax_Syntax.Sig_datacon (l, univs, t, _61_2224, _61_2226, _61_2228, _61_2230, _61_2232) -> begin
(check_term l univs t)
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, univs, t, quals, _61_2240) -> begin
if (not ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private)))) then begin
(check_term l univs t)
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_let ((_61_2244, lbs), _61_2248, _61_2250, quals, _61_2253) -> begin
if (not ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private)))) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (check_term fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp)))))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, binders, comp, quals, flags, r) -> begin
if (not ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private)))) then begin
(

let arrow = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (comp)))) None r)
in (check_term l univs arrow))
end else begin
()
end
end
| (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_assume (_)) | (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) -> begin
()
end))
in if (FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name FStar_Syntax_Const.prims_lid) then begin
()
end else begin
(FStar_List.iter check_sigelt exports)
end)))))


let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (

let modul = (

let _61_2289 = modul
in {FStar_Syntax_Syntax.name = _61_2289.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _61_2289.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module env modul)
in (

let _61_2293 = (check_exports env modul exports)
in (

let _61_2295 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (

let _61_2297 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (

let _61_2299 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (

let _61_2301 = if (not ((FStar_Options.interactive ()))) then begin
(let _159_968 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _159_968 Prims.ignore))
end else begin
()
end
in ((modul), (env))))))))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let _61_2308 = (tc_partial_modul env modul)
in (match (_61_2308) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (

let _61_2311 = if (FStar_Options.debug_any ()) then begin
(let _159_977 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _159_977))
end else begin
()
end
in (

let _61_2315 = (tc_modul env m)
in (match (_61_2315) with
| (m, env) -> begin
(

let _61_2316 = if (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _159_978 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _159_978))
end else begin
()
end
in (

let _61_2337 = if ((FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) && (FStar_Options.debug_at_level m.FStar_Syntax_Syntax.name.FStar_Ident.str (FStar_Options.Other ("Normalize")))) then begin
(

let normalize_toplevel_lets = (fun _61_13 -> (match (_61_13) with
| FStar_Syntax_Syntax.Sig_let ((b, lbs), r, ids, qs, attrs) -> begin
(

let n = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env)
in (let _159_986 = (let _159_985 = (let _159_984 = (FStar_List.map (fun lb -> (

let _61_2330 = lb
in (let _159_983 = (n lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _61_2330.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _61_2330.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _61_2330.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _61_2330.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _159_983}))) lbs)
in ((b), (_159_984)))
in ((_159_985), (r), (ids), (qs), (attrs)))
in FStar_Syntax_Syntax.Sig_let (_159_986)))
end
| se -> begin
se
end))
in (

let normalized_module = (

let _61_2334 = m
in (let _159_987 = (FStar_List.map normalize_toplevel_lets m.FStar_Syntax_Syntax.declarations)
in {FStar_Syntax_Syntax.name = _61_2334.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _159_987; FStar_Syntax_Syntax.exports = _61_2334.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _61_2334.FStar_Syntax_Syntax.is_interface}))
in (let _159_988 = (FStar_Syntax_Print.modul_to_string normalized_module)
in (FStar_Util.print1 "%s\n" _159_988))))
end else begin
()
end
in ((m), (env))))
end))))




