
open Prims

let set_hint_correlator : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env = (fun env se -> (match ((FStar_Options.reuse_hint_for ())) with
| Some (l) -> begin
(

let lid = (let _153_5 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_add_suffix _153_5 l))
in (

let _59_16 = env
in {FStar_TypeChecker_Env.solver = _59_16.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_16.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_16.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_16.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_16.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_16.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_16.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_16.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_16.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_16.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_16.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_16.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_16.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_16.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_16.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_16.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_16.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_16.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_16.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _59_16.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_16.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_16.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), ((Prims.parse_int "0"))))}))
end
| None -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (

let lid = (match (lids) with
| [] -> begin
(let _153_8 = (FStar_TypeChecker_Env.current_module env)
in (let _153_7 = (let _153_6 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_right _153_6 FStar_Util.string_of_int))
in (FStar_Ident.lid_add_suffix _153_8 _153_7)))
end
| (l)::_59_22 -> begin
l
end)
in (

let _59_26 = env
in {FStar_TypeChecker_Env.solver = _59_26.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_26.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_26.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_26.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_26.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_26.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_26.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_26.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_26.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_26.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_26.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_26.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_26.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_26.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_26.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_26.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_26.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_26.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_26.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _59_26.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_26.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_26.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), ((Prims.parse_int "0"))))})))
end))


let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_Options.log_types ()) && (not ((let _153_11 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _153_11))))))


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let _59_35 = (FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k)
in (match (_59_35) with
| (t, c, g) -> begin
(

let _59_36 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t)
end)))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _153_24 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _153_24)))


let check_nogen = (fun env t k -> (

let t = (tc_check_trivial_guard env t k)
in (let _153_28 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (([]), (_153_28)))))


let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let _59_51 = (FStar_TypeChecker_TcTerm.tc_binders env tps)
in (match (_59_51) with
| (tps, env, g, us) -> begin
(

let _59_52 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in ((tps), (env), (us)))
end)))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (

let fail = (fun _59_58 -> (match (()) with
| () -> begin
(let _153_43 = (let _153_42 = (let _153_41 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in ((_153_41), ((FStar_Ident.range_of_lid m))))
in FStar_Syntax_Syntax.Error (_153_42))
in (Prims.raise _153_43))
end))
in (

let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _59_71))::((wp, _59_67))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _59_75 -> begin
(fail ())
end))
end
| _59_77 -> begin
(fail ())
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let _59_84 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_59_84) with
| (uvs, c) -> begin
((uvs), ([]), (c))
end))
end
| _59_86 -> begin
(

let t' = (FStar_Syntax_Util.arrow binders c)
in (

let _59_90 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_59_90) with
| (uvs, t') -> begin
(match ((let _153_50 = (FStar_Syntax_Subst.compress t')
in _153_50.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
((uvs), (binders), (c))
end
| _59_96 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))


let rec tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (

let _59_99 = ()
in (

let _59_104 = (FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_59_104) with
| (effect_params_un, signature_un, opening) -> begin
(

let _59_109 = (tc_tparams env0 effect_params_un)
in (match (_59_109) with
| (effect_params, env, _59_108) -> begin
(

let _59_113 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (_59_113) with
| (signature, _59_112) -> begin
(

let ed = (

let _59_114 = ed
in {FStar_Syntax_Syntax.qualifiers = _59_114.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _59_114.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _59_114.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _59_114.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _59_114.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _59_114.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _59_114.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _59_114.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _59_114.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _59_114.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _59_114.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _59_114.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _59_114.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _59_114.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _59_114.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _59_114.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _59_114.FStar_Syntax_Syntax.actions})
in (

let ed = (match (effect_params) with
| [] -> begin
ed
end
| _59_119 -> begin
(

let op = (fun ts -> (

let _59_122 = ()
in (

let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in (([]), (t1)))))
in (

let _59_125 = ed
in (let _153_93 = (op ed.FStar_Syntax_Syntax.ret_wp)
in (let _153_92 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _153_91 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _153_90 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _153_89 = (op ed.FStar_Syntax_Syntax.stronger)
in (let _153_88 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _153_87 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _153_86 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _153_85 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _153_84 = (op ed.FStar_Syntax_Syntax.trivial)
in (let _153_83 = (let _153_74 = (op (([]), (ed.FStar_Syntax_Syntax.repr)))
in (Prims.snd _153_74))
in (let _153_82 = (op ed.FStar_Syntax_Syntax.return_repr)
in (let _153_81 = (op ed.FStar_Syntax_Syntax.bind_repr)
in (let _153_80 = (FStar_List.map (fun a -> (

let _59_128 = a
in (let _153_79 = (let _153_76 = (op (([]), (a.FStar_Syntax_Syntax.action_defn)))
in (Prims.snd _153_76))
in (let _153_78 = (let _153_77 = (op (([]), (a.FStar_Syntax_Syntax.action_typ)))
in (Prims.snd _153_77))
in {FStar_Syntax_Syntax.action_name = _59_128.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = _59_128.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _153_79; FStar_Syntax_Syntax.action_typ = _153_78})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.qualifiers = _59_125.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _59_125.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _59_125.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _59_125.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _59_125.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _153_93; FStar_Syntax_Syntax.bind_wp = _153_92; FStar_Syntax_Syntax.if_then_else = _153_91; FStar_Syntax_Syntax.ite_wp = _153_90; FStar_Syntax_Syntax.stronger = _153_89; FStar_Syntax_Syntax.close_wp = _153_88; FStar_Syntax_Syntax.assert_p = _153_87; FStar_Syntax_Syntax.assume_p = _153_86; FStar_Syntax_Syntax.null_wp = _153_85; FStar_Syntax_Syntax.trivial = _153_84; FStar_Syntax_Syntax.repr = _153_83; FStar_Syntax_Syntax.return_repr = _153_82; FStar_Syntax_Syntax.bind_repr = _153_81; FStar_Syntax_Syntax.actions = _153_80}))))))))))))))))
end)
in (

let wp_with_fresh_result_type = (fun env mname signature -> (

let fail = (fun t -> (let _153_104 = (let _153_103 = (let _153_102 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in ((_153_102), ((FStar_Ident.range_of_lid mname))))
in FStar_Syntax_Syntax.Error (_153_103))
in (Prims.raise _153_104)))
in (match ((let _153_105 = (FStar_Syntax_Subst.compress signature)
in _153_105.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _59_148))::((wp, _59_144))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _59_152 -> begin
(fail signature)
end))
end
| _59_154 -> begin
(fail signature)
end)))
in (

let _59_157 = (wp_with_fresh_result_type env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_59_157) with
| (a, wp_a) -> begin
(

let fresh_effect_signature = (fun _59_159 -> (match (()) with
| () -> begin
(

let _59_163 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (_59_163) with
| (signature, _59_162) -> begin
(wp_with_fresh_result_type env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (

let env = (let _153_108 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _153_108))
in (

let _59_165 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _153_114 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _153_113 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _153_112 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _153_111 = (let _153_109 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Print.term_to_string _153_109))
in (let _153_110 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.sort)
in (FStar_Util.print5 "Checking effect signature: %s %s : %s\n(a is %s:%s)\n" _153_114 _153_113 _153_112 _153_111 _153_110))))))
end else begin
()
end
in (

let check_and_gen' = (fun env _59_172 k -> (match (_59_172) with
| (_59_170, t) -> begin
(check_and_gen env t k)
end))
in (

let return_wp = (

let expected_k = (let _153_126 = (let _153_124 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_123 = (let _153_122 = (let _153_121 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _153_121))
in (_153_122)::[])
in (_153_124)::_153_123))
in (let _153_125 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _153_126 _153_125)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret_wp expected_k))
in (

let bind_wp = (

let _59_178 = (fresh_effect_signature ())
in (match (_59_178) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _153_130 = (let _153_128 = (let _153_127 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _153_127))
in (_153_128)::[])
in (let _153_129 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _153_130 _153_129)))
in (

let expected_k = (let _153_141 = (let _153_139 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _153_138 = (let _153_137 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_136 = (let _153_135 = (FStar_Syntax_Syntax.mk_binder b)
in (let _153_134 = (let _153_133 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _153_132 = (let _153_131 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (_153_131)::[])
in (_153_133)::_153_132))
in (_153_135)::_153_134))
in (_153_137)::_153_136))
in (_153_139)::_153_138))
in (let _153_140 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _153_141 _153_140)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else = (

let p = (let _153_143 = (let _153_142 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _153_142 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _153_143))
in (

let expected_k = (let _153_152 = (let _153_150 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_149 = (let _153_148 = (FStar_Syntax_Syntax.mk_binder p)
in (let _153_147 = (let _153_146 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _153_145 = (let _153_144 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_144)::[])
in (_153_146)::_153_145))
in (_153_148)::_153_147))
in (_153_150)::_153_149))
in (let _153_151 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_152 _153_151)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (let _153_157 = (let _153_155 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_154 = (let _153_153 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_153)::[])
in (_153_155)::_153_154))
in (let _153_156 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_157 _153_156)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let _59_190 = (FStar_Syntax_Util.type_u ())
in (match (_59_190) with
| (t, _59_189) -> begin
(

let expected_k = (let _153_164 = (let _153_162 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_161 = (let _153_160 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _153_159 = (let _153_158 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_158)::[])
in (_153_160)::_153_159))
in (_153_162)::_153_161))
in (let _153_163 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _153_164 _153_163)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (let _153_166 = (let _153_165 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _153_165 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _153_166))
in (

let b_wp_a = (let _153_170 = (let _153_168 = (let _153_167 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _153_167))
in (_153_168)::[])
in (let _153_169 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_170 _153_169)))
in (

let expected_k = (let _153_177 = (let _153_175 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_174 = (let _153_173 = (FStar_Syntax_Syntax.mk_binder b)
in (let _153_172 = (let _153_171 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_153_171)::[])
in (_153_173)::_153_172))
in (_153_175)::_153_174))
in (let _153_176 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_177 _153_176)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (let _153_186 = (let _153_184 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_183 = (let _153_182 = (let _153_179 = (let _153_178 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _153_178 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _153_179))
in (let _153_181 = (let _153_180 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_180)::[])
in (_153_182)::_153_181))
in (_153_184)::_153_183))
in (let _153_185 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_186 _153_185)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (let _153_195 = (let _153_193 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_192 = (let _153_191 = (let _153_188 = (let _153_187 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _153_187 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _153_188))
in (let _153_190 = (let _153_189 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_189)::[])
in (_153_191)::_153_190))
in (_153_193)::_153_192))
in (let _153_194 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_195 _153_194)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (let _153_198 = (let _153_196 = (FStar_Syntax_Syntax.mk_binder a)
in (_153_196)::[])
in (let _153_197 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_198 _153_197)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let _59_206 = (FStar_Syntax_Util.type_u ())
in (match (_59_206) with
| (t, _59_205) -> begin
(

let expected_k = (let _153_203 = (let _153_201 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_200 = (let _153_199 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_199)::[])
in (_153_201)::_153_200))
in (let _153_202 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _153_203 _153_202)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let _59_347 = if ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) || (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reflectable))) then begin
(

let repr = (

let _59_212 = (FStar_Syntax_Util.type_u ())
in (match (_59_212) with
| (t, _59_211) -> begin
(

let expected_k = (let _153_208 = (let _153_206 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_205 = (let _153_204 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_204)::[])
in (_153_206)::_153_205))
in (let _153_207 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _153_208 _153_207)))
in (tc_check_trivial_guard env ed.FStar_Syntax_Syntax.repr expected_k))
end))
in (

let mk_repr' = (fun t wp -> (

let repr = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env repr)
in (let _153_218 = (let _153_217 = (let _153_216 = (let _153_215 = (FStar_Syntax_Syntax.as_arg t)
in (let _153_214 = (let _153_213 = (FStar_Syntax_Syntax.as_arg wp)
in (_153_213)::[])
in (_153_215)::_153_214))
in ((repr), (_153_216)))
in FStar_Syntax_Syntax.Tm_app (_153_217))
in (FStar_Syntax_Syntax.mk _153_218 None FStar_Range.dummyRange))))
in (

let mk_repr = (fun a wp -> (let _153_223 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_repr' _153_223 wp)))
in (

let destruct_repr = (fun t -> (match ((let _153_226 = (FStar_Syntax_Subst.compress t)
in _153_226.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_59_225, ((t, _59_232))::((wp, _59_228))::[]) -> begin
((t), (wp))
end
| _59_238 -> begin
(FStar_All.failwith "Unexpected repr type")
end))
in (

let bind_repr = (

let r = (let _153_227 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_0 FStar_Syntax_Syntax.Delta_constant None)
in (FStar_All.pipe_right _153_227 FStar_Syntax_Syntax.fv_to_tm))
in (

let _59_242 = (fresh_effect_signature ())
in (match (_59_242) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _153_231 = (let _153_229 = (let _153_228 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _153_228))
in (_153_229)::[])
in (let _153_230 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _153_231 _153_230)))
in (

let wp_f = (FStar_Syntax_Syntax.gen_bv "wp_f" None wp_a)
in (

let wp_g = (FStar_Syntax_Syntax.gen_bv "wp_g" None a_wp_b)
in (

let x_a = (let _153_232 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _153_232))
in (

let wp_g_x = (let _153_236 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (let _153_235 = (let _153_234 = (let _153_233 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _153_233))
in (_153_234)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _153_236 _153_235 None FStar_Range.dummyRange)))
in (

let res = (

let wp = (let _153_248 = (let _153_237 = (FStar_TypeChecker_Env.inst_tscheme bind_wp)
in (FStar_All.pipe_right _153_237 Prims.snd))
in (let _153_247 = (let _153_246 = (let _153_245 = (let _153_244 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _153_243 = (let _153_242 = (FStar_Syntax_Syntax.bv_to_name b)
in (let _153_241 = (let _153_240 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (let _153_239 = (let _153_238 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (_153_238)::[])
in (_153_240)::_153_239))
in (_153_242)::_153_241))
in (_153_244)::_153_243))
in (r)::_153_245)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _153_246))
in (FStar_Syntax_Syntax.mk_Tm_app _153_248 _153_247 None FStar_Range.dummyRange)))
in (mk_repr b wp))
in (

let expected_k = (let _153_268 = (let _153_266 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_265 = (let _153_264 = (FStar_Syntax_Syntax.mk_binder b)
in (let _153_263 = (let _153_262 = (FStar_Syntax_Syntax.mk_binder wp_f)
in (let _153_261 = (let _153_260 = (let _153_250 = (let _153_249 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (mk_repr a _153_249))
in (FStar_Syntax_Syntax.null_binder _153_250))
in (let _153_259 = (let _153_258 = (FStar_Syntax_Syntax.mk_binder wp_g)
in (let _153_257 = (let _153_256 = (let _153_255 = (let _153_254 = (let _153_251 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_153_251)::[])
in (let _153_253 = (let _153_252 = (mk_repr b wp_g_x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _153_252))
in (FStar_Syntax_Util.arrow _153_254 _153_253)))
in (FStar_Syntax_Syntax.null_binder _153_255))
in (_153_256)::[])
in (_153_258)::_153_257))
in (_153_260)::_153_259))
in (_153_262)::_153_261))
in (_153_264)::_153_263))
in (_153_266)::_153_265))
in (let _153_267 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _153_268 _153_267)))
in (

let _59_256 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (_59_256) with
| (expected_k, _59_253, _59_255) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos)
in (

let env = (

let _59_258 = env
in {FStar_TypeChecker_Env.solver = _59_258.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_258.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_258.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_258.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_258.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_258.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_258.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_258.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_258.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_258.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_258.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_258.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_258.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_258.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_258.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_258.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_258.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_258.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.type_of = _59_258.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_258.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_258.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_258.FStar_TypeChecker_Env.qname_and_index})
in (

let br = (check_and_gen' env ed.FStar_Syntax_Syntax.bind_repr expected_k)
in br)))
end)))))))))
end)))
in (

let return_repr = (

let x_a = (let _153_269 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _153_269))
in (

let res = (

let wp = (let _153_276 = (let _153_270 = (FStar_TypeChecker_Env.inst_tscheme return_wp)
in (FStar_All.pipe_right _153_270 Prims.snd))
in (let _153_275 = (let _153_274 = (let _153_273 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _153_272 = (let _153_271 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (_153_271)::[])
in (_153_273)::_153_272))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _153_274))
in (FStar_Syntax_Syntax.mk_Tm_app _153_276 _153_275 None FStar_Range.dummyRange)))
in (mk_repr a wp))
in (

let expected_k = (let _153_281 = (let _153_279 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_278 = (let _153_277 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_153_277)::[])
in (_153_279)::_153_278))
in (let _153_280 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _153_281 _153_280)))
in (

let _59_272 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (_59_272) with
| (expected_k, _59_269, _59_271) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos)
in (

let _59_276 = (check_and_gen' env ed.FStar_Syntax_Syntax.return_repr expected_k)
in (match (_59_276) with
| (univs, repr) -> begin
(match (univs) with
| [] -> begin
(([]), (repr))
end
| _59_279 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected universe-polymorphic return for effect"), (repr.FStar_Syntax_Syntax.pos)))))
end)
end)))
end)))))
in (

let actions = (

let check_action = (fun act -> (

let _59_287 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env act.FStar_Syntax_Syntax.action_typ)
in (match (_59_287) with
| (act_typ, _59_285, g_t) -> begin
(

let env' = (FStar_TypeChecker_Env.set_expected_typ env act_typ)
in (

let _59_289 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _153_285 = (FStar_Syntax_Print.term_to_string act.FStar_Syntax_Syntax.action_defn)
in (let _153_284 = (FStar_Syntax_Print.term_to_string act_typ)
in (FStar_Util.print3 "Checking action %s:\n[definition]: %s\n[cps\'d type]: %s\n" (FStar_Ident.text_of_lid act.FStar_Syntax_Syntax.action_name) _153_285 _153_284)))
end else begin
()
end
in (

let _59_295 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' act.FStar_Syntax_Syntax.action_defn)
in (match (_59_295) with
| (act_defn, _59_293, g_a) -> begin
(

let act_defn = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env act_defn)
in (

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
in (

let _59_318 = (

let act_typ = (FStar_Syntax_Subst.compress act_typ)
in (match (act_typ.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _59_306 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_59_306) with
| (bs, _59_305) -> begin
(

let res = (mk_repr' FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun)
in (

let k = (let _153_286 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs _153_286))
in (

let _59_313 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env k)
in (match (_59_313) with
| (k, _59_311, g) -> begin
((k), (g))
end))))
end))
end
| _59_315 -> begin
(let _153_291 = (let _153_290 = (let _153_289 = (let _153_288 = (FStar_Syntax_Print.term_to_string act_typ)
in (let _153_287 = (FStar_Syntax_Print.tag_of_term act_typ)
in (FStar_Util.format2 "Actions must have function types (not: %s, a.k.a. %s)" _153_288 _153_287)))
in ((_153_289), (act_defn.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_153_290))
in (Prims.raise _153_291))
end))
in (match (_59_318) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env act_typ expected_k)
in (

let _59_320 = (let _153_294 = (let _153_293 = (let _153_292 = (FStar_TypeChecker_Rel.conj_guard g_t g)
in (FStar_TypeChecker_Rel.conj_guard g_k _153_292))
in (FStar_TypeChecker_Rel.conj_guard g_a _153_293))
in (FStar_TypeChecker_Rel.force_trivial_guard env _153_294))
in (

let act_typ = (match ((let _153_295 = (FStar_Syntax_Subst.compress expected_k)
in _153_295.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _59_328 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_59_328) with
| (bs, c) -> begin
(

let _59_331 = (destruct_repr (FStar_Syntax_Util.comp_result c))
in (match (_59_331) with
| (a, wp) -> begin
(

let c = (let _153_297 = (let _153_296 = (FStar_Syntax_Syntax.as_arg wp)
in (_153_296)::[])
in {FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a; FStar_Syntax_Syntax.effect_args = _153_297; FStar_Syntax_Syntax.flags = []})
in (let _153_298 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Util.arrow bs _153_298)))
end))
end))
end
| _59_334 -> begin
(FStar_All.failwith "")
end)
in (

let _59_338 = (FStar_TypeChecker_Util.generalize_universes env act_defn)
in (match (_59_338) with
| (univs, act_defn) -> begin
(

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
in (

let _59_340 = act
in {FStar_Syntax_Syntax.action_name = _59_340.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = act_defn; FStar_Syntax_Syntax.action_typ = act_typ}))
end)))))
end))))
end))))
end)))
in (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.map check_action)))
in ((repr), (bind_repr), (return_repr), (actions)))))))))
end else begin
((ed.FStar_Syntax_Syntax.repr), (ed.FStar_Syntax_Syntax.bind_repr), (ed.FStar_Syntax_Syntax.return_repr), (ed.FStar_Syntax_Syntax.actions))
end
in (match (_59_347) with
| (repr, bind_repr, return_repr, actions) -> begin
(

let t = (let _153_299 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _153_299))
in (

let _59_351 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_59_351) with
| (univs, t) -> begin
(

let signature = (match ((let _153_301 = (let _153_300 = (FStar_Syntax_Subst.compress t)
in _153_300.FStar_Syntax_Syntax.n)
in ((effect_params), (_153_301)))) with
| ([], _59_354) -> begin
t
end
| (_59_357, FStar_Syntax_Syntax.Tm_arrow (_59_359, c)) -> begin
(FStar_Syntax_Util.comp_result c)
end
| _59_365 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let close = (fun n ts -> (

let ts = (let _153_306 = (FStar_Syntax_Subst.close_tscheme effect_params ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _153_306))
in (

let _59_371 = if (((n > (Prims.parse_int "0")) && (not ((FStar_Syntax_Util.is_unknown (Prims.snd ts))))) && ((FStar_List.length (Prims.fst ts)) <> n)) then begin
(let _153_309 = (let _153_308 = (FStar_Util.string_of_int n)
in (let _153_307 = (FStar_Syntax_Print.tscheme_to_string ts)
in (FStar_Util.format2 "The effect combinator is not universe-polymorphic enough (n=%s) (%s)" _153_308 _153_307)))
in (FStar_All.failwith _153_309))
end else begin
()
end
in ts)))
in (

let close_action = (fun act -> (

let _59_377 = (close (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_defn)))
in (match (_59_377) with
| (univs, defn) -> begin
(

let _59_380 = (close (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_typ)))
in (match (_59_380) with
| (univs', typ) -> begin
(

let _59_381 = ()
in (

let _59_383 = act
in {FStar_Syntax_Syntax.action_name = _59_383.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = defn; FStar_Syntax_Syntax.action_typ = typ}))
end))
end)))
in (

let _59_385 = ()
in (

let ed = (

let _59_387 = ed
in (let _153_326 = (close (Prims.parse_int "0") return_wp)
in (let _153_325 = (close (Prims.parse_int "1") bind_wp)
in (let _153_324 = (close (Prims.parse_int "0") if_then_else)
in (let _153_323 = (close (Prims.parse_int "0") ite_wp)
in (let _153_322 = (close (Prims.parse_int "0") stronger)
in (let _153_321 = (close (Prims.parse_int "1") close_wp)
in (let _153_320 = (close (Prims.parse_int "0") assert_p)
in (let _153_319 = (close (Prims.parse_int "0") assume_p)
in (let _153_318 = (close (Prims.parse_int "0") null_wp)
in (let _153_317 = (close (Prims.parse_int "0") trivial_wp)
in (let _153_316 = (let _153_312 = (close (Prims.parse_int "0") (([]), (repr)))
in (Prims.snd _153_312))
in (let _153_315 = (close (Prims.parse_int "0") return_repr)
in (let _153_314 = (close (Prims.parse_int "1") bind_repr)
in (let _153_313 = (FStar_List.map close_action actions)
in {FStar_Syntax_Syntax.qualifiers = _59_387.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _59_387.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _153_326; FStar_Syntax_Syntax.bind_wp = _153_325; FStar_Syntax_Syntax.if_then_else = _153_324; FStar_Syntax_Syntax.ite_wp = _153_323; FStar_Syntax_Syntax.stronger = _153_322; FStar_Syntax_Syntax.close_wp = _153_321; FStar_Syntax_Syntax.assert_p = _153_320; FStar_Syntax_Syntax.assume_p = _153_319; FStar_Syntax_Syntax.null_wp = _153_318; FStar_Syntax_Syntax.trivial = _153_317; FStar_Syntax_Syntax.repr = _153_316; FStar_Syntax_Syntax.return_repr = _153_315; FStar_Syntax_Syntax.bind_repr = _153_314; FStar_Syntax_Syntax.actions = _153_313})))))))))))))))
in (

let _59_390 = if ((FStar_TypeChecker_Env.debug env FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ED")))) then begin
(let _153_327 = (FStar_Syntax_Print.eff_decl_to_string false ed)
in (FStar_Util.print_string _153_327))
end else begin
()
end
in ed))))))
end)))
end))))))))))))))))
end)))))
end))
end))
end))))
and cps_and_elaborate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl) = (fun env ed -> (

let _59_396 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_59_396) with
| (effect_binders_un, signature_un) -> begin
(

let _59_401 = (tc_tparams env effect_binders_un)
in (match (_59_401) with
| (effect_binders, env, _59_400) -> begin
(

let _59_405 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (_59_405) with
| (signature, _59_404) -> begin
(

let effect_binders = (FStar_List.map (fun _59_408 -> (match (_59_408) with
| (bv, qual) -> begin
(let _153_332 = (

let _59_409 = bv
in (let _153_331 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _59_409.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_409.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _153_331}))
in ((_153_332), (qual)))
end)) effect_binders)
in (

let _59_424 = (match ((let _153_333 = (FStar_Syntax_Subst.compress signature_un)
in _153_333.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (((a, _59_414))::[], effect_marker) -> begin
((a), (effect_marker))
end
| _59_421 -> begin
(FStar_All.failwith "bad shape for effect-for-free signature")
end)
in (match (_59_424) with
| (a, effect_marker) -> begin
(

let open_and_check = (fun t -> (

let subst = (FStar_Syntax_Subst.opening_of_binders effect_binders)
in (

let t = (FStar_Syntax_Subst.subst subst t)
in (

let _59_433 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (_59_433) with
| (t, comp, _59_432) -> begin
((t), (comp))
end)))))
in (

let recheck_debug = (fun s env t -> (

let _59_438 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _153_342 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Term has been %s-transformed to:\n%s\n----------\n" s _153_342))
end else begin
()
end
in (

let _59_445 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (_59_445) with
| (t', _59_442, _59_444) -> begin
(

let _59_446 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _153_343 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print1 "Re-checked; got:\n%s\n----------\n" _153_343))
end else begin
()
end
in t)
end))))
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None signature.FStar_Syntax_Syntax.pos))
in (

let _59_452 = (open_and_check ed.FStar_Syntax_Syntax.repr)
in (match (_59_452) with
| (repr, _comp) -> begin
(

let _59_453 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _153_346 = (FStar_Syntax_Print.term_to_string repr)
in (FStar_Util.print1 "Representation is: %s\n" _153_346))
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

let wp_a = (let _153_353 = (let _153_352 = (let _153_351 = (let _153_350 = (let _153_349 = (let _153_348 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _153_347 = (FStar_Syntax_Syntax.as_implicit false)
in ((_153_348), (_153_347))))
in (_153_349)::[])
in ((wp_type), (_153_350)))
in FStar_Syntax_Syntax.Tm_app (_153_351))
in (mk _153_352))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _153_353))
in (

let effect_signature = (

let binders = (let _153_358 = (let _153_354 = (FStar_Syntax_Syntax.as_implicit false)
in ((a), (_153_354)))
in (let _153_357 = (let _153_356 = (let _153_355 = (FStar_Syntax_Syntax.gen_bv "dijkstra_wp" None wp_a)
in (FStar_All.pipe_right _153_355 FStar_Syntax_Syntax.mk_binder))
in (_153_356)::[])
in (_153_358)::_153_357))
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

let _59_471 = item
in (match (_59_471) with
| (u_item, item) -> begin
(

let _59_474 = (open_and_check item)
in (match (_59_474) with
| (item, item_comp) -> begin
(

let _59_475 = if (not ((FStar_Syntax_Util.is_total_lcomp item_comp))) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Computation for [item] is not total!")))
end else begin
()
end
in (

let _59_480 = (FStar_TypeChecker_DMFF.star_expr dmff_env item)
in (match (_59_480) with
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

let _59_488 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.bind_repr)
in (match (_59_488) with
| (dmff_env, _59_485, bind_wp, bind_elab) -> begin
(

let _59_494 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.return_repr)
in (match (_59_494) with
| (dmff_env, _59_491, return_wp, return_elab) -> begin
(

let return_wp = (match ((let _153_365 = (FStar_Syntax_Subst.compress return_wp)
in _153_365.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(let _153_366 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs ((b1)::(b2)::[]) _153_366 (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_GTot_lid)))))
end
| _59_505 -> begin
(FStar_All.failwith "unexpected shape for return")
end)
in (

let bind_wp = (match ((let _153_367 = (FStar_Syntax_Subst.compress bind_wp)
in _153_367.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let r = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_lid (FStar_Syntax_Syntax.Delta_unfoldable ((Prims.parse_int "1"))) None)
in (let _153_371 = (let _153_370 = (let _153_369 = (let _153_368 = (mk (FStar_Syntax_Syntax.Tm_fvar (r)))
in (FStar_Syntax_Syntax.null_binder _153_368))
in (_153_369)::[])
in (FStar_List.append _153_370 binders))
in (FStar_Syntax_Util.abs _153_371 body what)))
end
| _59_514 -> begin
(FStar_All.failwith "unexpected shape for bind")
end)
in (

let apply_close = (fun t -> if ((FStar_List.length effect_binders) = (Prims.parse_int "0")) then begin
t
end else begin
(let _153_378 = (let _153_377 = (let _153_376 = (let _153_375 = (let _153_374 = (FStar_Syntax_Util.args_of_binders effect_binders)
in (Prims.snd _153_374))
in ((t), (_153_375)))
in FStar_Syntax_Syntax.Tm_app (_153_376))
in (mk _153_377))
in (FStar_Syntax_Subst.close effect_binders _153_378))
end)
in (

let register = (fun name item -> (

let _59_523 = (let _153_384 = (mk_lid name)
in (let _153_383 = (FStar_Syntax_Util.abs effect_binders item None)
in (FStar_TypeChecker_Util.mk_toplevel_definition env _153_384 _153_383)))
in (match (_59_523) with
| (sigelt, fv) -> begin
(

let _59_524 = (let _153_386 = (let _153_385 = (FStar_ST.read sigelts)
in (sigelt)::_153_385)
in (FStar_ST.op_Colon_Equals sigelts _153_386))
in fv)
end)))
in (

let return_wp = (register "return_wp" return_wp)
in (

let return_elab = (register "return_elab" return_elab)
in (

let bind_wp = (register "bind_wp" bind_wp)
in (

let _59_529 = (let _153_388 = (let _153_387 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true")), (FStar_Range.dummyRange))))::_153_387)
in (FStar_ST.op_Colon_Equals sigelts _153_388))
in (

let bind_elab = (register "bind_elab" bind_elab)
in (

let _59_532 = (let _153_390 = (let _153_389 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false")), (FStar_Range.dummyRange))))::_153_389)
in (FStar_ST.op_Colon_Equals sigelts _153_390))
in (

let _59_551 = (FStar_List.fold_left (fun _59_536 action -> (match (_59_536) with
| (dmff_env, actions) -> begin
(

let _59_542 = (elaborate_and_star dmff_env ((action.FStar_Syntax_Syntax.action_univs), (action.FStar_Syntax_Syntax.action_defn)))
in (match (_59_542) with
| (dmff_env, action_t, action_wp, action_elab) -> begin
(

let name = action.FStar_Syntax_Syntax.action_name.FStar_Ident.ident.FStar_Ident.idText
in (

let action_typ_with_wp = (FStar_TypeChecker_DMFF.trans_F dmff_env action_t action_wp)
in (

let action_elab = (register (Prims.strcat name "_elab") action_elab)
in (

let action_typ_with_wp = (register (Prims.strcat name "_complete_type") action_typ_with_wp)
in (let _153_396 = (let _153_395 = (

let _59_547 = action
in (let _153_394 = (apply_close action_elab)
in (let _153_393 = (apply_close action_typ_with_wp)
in {FStar_Syntax_Syntax.action_name = _59_547.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = _59_547.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _153_394; FStar_Syntax_Syntax.action_typ = _153_393})))
in (_153_395)::actions)
in ((dmff_env), (_153_396)))))))
end))
end)) ((dmff_env), ([])) ed.FStar_Syntax_Syntax.actions)
in (match (_59_551) with
| (dmff_env, actions) -> begin
(

let actions = (FStar_List.rev actions)
in (

let repr = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp_a" None wp_a)
in (

let binders = (let _153_399 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_398 = (let _153_397 = (FStar_Syntax_Syntax.mk_binder wp)
in (_153_397)::[])
in (_153_399)::_153_398))
in (let _153_408 = (let _153_407 = (let _153_405 = (let _153_404 = (let _153_403 = (let _153_402 = (let _153_401 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _153_400 = (FStar_Syntax_Syntax.as_implicit false)
in ((_153_401), (_153_400))))
in (_153_402)::[])
in ((repr), (_153_403)))
in FStar_Syntax_Syntax.Tm_app (_153_404))
in (mk _153_405))
in (let _153_406 = (FStar_Syntax_Syntax.bv_to_name wp)
in (FStar_TypeChecker_DMFF.trans_F dmff_env _153_407 _153_406)))
in (FStar_Syntax_Util.abs binders _153_408 None))))
in (

let repr = (recheck_debug "FC" env repr)
in (

let repr = (register "repr" repr)
in (

let _59_583 = (match ((let _153_409 = (FStar_Syntax_Subst.compress wp_type)
in _153_409.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (effect_param, arrow, _59_561) -> begin
(

let _59_566 = (FStar_Syntax_Subst.open_term effect_param arrow)
in (match (_59_566) with
| (effect_param, arrow) -> begin
(match ((let _153_410 = (FStar_Syntax_Subst.compress arrow)
in _153_410.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (wp_binders, c) -> begin
(

let _59_573 = (FStar_Syntax_Subst.open_comp wp_binders c)
in (match (_59_573) with
| (wp_binders, c) -> begin
(

let _59_576 = (FStar_Util.prefix wp_binders)
in (match (_59_576) with
| (pre_args, post) -> begin
(let _153_412 = (FStar_Syntax_Util.arrow pre_args c)
in (let _153_411 = (FStar_Syntax_Util.abs effect_param (Prims.fst post).FStar_Syntax_Syntax.sort None)
in ((_153_412), (_153_411))))
end))
end))
end
| _59_578 -> begin
(let _153_414 = (let _153_413 = (FStar_Syntax_Print.term_to_string arrow)
in (FStar_Util.format1 "Impossible: pre/post arrow %s" _153_413))
in (FStar_All.failwith _153_414))
end)
end))
end
| _59_580 -> begin
(let _153_416 = (let _153_415 = (FStar_Syntax_Print.term_to_string wp_type)
in (FStar_Util.format1 "Impossible: pre/post abs %s" _153_415))
in (FStar_All.failwith _153_416))
end)
in (match (_59_583) with
| (pre, post) -> begin
(

let _59_584 = (let _153_417 = (register "pre" pre)
in (Prims.ignore _153_417))
in (

let _59_586 = (let _153_418 = (register "post" post)
in (Prims.ignore _153_418))
in (

let _59_588 = (let _153_419 = (register "wp" wp_type)
in (Prims.ignore _153_419))
in (

let ed = (

let _59_590 = ed
in (let _153_430 = (FStar_Syntax_Subst.close_binders effect_binders)
in (let _153_429 = (FStar_Syntax_Subst.close effect_binders effect_signature)
in (let _153_428 = (let _153_420 = (apply_close return_wp)
in (([]), (_153_420)))
in (let _153_427 = (let _153_421 = (apply_close bind_wp)
in (([]), (_153_421)))
in (let _153_426 = (apply_close repr)
in (let _153_425 = (let _153_422 = (apply_close return_elab)
in (([]), (_153_422)))
in (let _153_424 = (let _153_423 = (apply_close bind_elab)
in (([]), (_153_423)))
in {FStar_Syntax_Syntax.qualifiers = _59_590.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _59_590.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _59_590.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _153_430; FStar_Syntax_Syntax.signature = _153_429; FStar_Syntax_Syntax.ret_wp = _153_428; FStar_Syntax_Syntax.bind_wp = _153_427; FStar_Syntax_Syntax.if_then_else = _59_590.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _59_590.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _59_590.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _59_590.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _59_590.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _59_590.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _59_590.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _59_590.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _153_426; FStar_Syntax_Syntax.return_repr = _153_425; FStar_Syntax_Syntax.bind_repr = _153_424; FStar_Syntax_Syntax.actions = actions}))))))))
in (

let _59_595 = (FStar_TypeChecker_DMFF.gen_wps_for_free env effect_binders a wp_a ed)
in (match (_59_595) with
| (sigelts', ed) -> begin
(

let _59_596 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _153_431 = (FStar_Syntax_Print.eff_decl_to_string true ed)
in (FStar_Util.print_string _153_431))
end else begin
()
end
in (let _153_434 = (let _153_433 = (let _153_432 = (FStar_ST.read sigelts)
in (FStar_List.rev _153_432))
in (FStar_List.append _153_433 sigelts'))
in ((_153_434), (ed))))
end))))))
end))))))
end))))))))))))
end))
end))))))))))))
end)))))
end)))
end))
end))
end)))
and tc_lex_t : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (

let _59_602 = ()
in (

let _59_610 = ()
in (match (ses) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _59_639, _59_641, [], r))::(FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, _153_439, [], _59_630, r1))::(FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, _153_440, [], _59_619, r2))::[] when (((_153_439 = (Prims.parse_int "0")) && (_153_440 = (Prims.parse_int "0"))) && (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid))) -> begin
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

let lex_top_t = (let _153_444 = (let _153_443 = (let _153_442 = (let _153_441 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _153_441 FStar_Syntax_Syntax.Delta_constant None))
in ((_153_442), ((FStar_Syntax_Syntax.U_name (utop))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_153_443))
in (FStar_Syntax_Syntax.mk _153_444 None r1))
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

let a = (let _153_445 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _153_445))
in (

let hd = (let _153_446 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _153_446))
in (

let tl = (let _153_451 = (let _153_450 = (let _153_449 = (let _153_448 = (let _153_447 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _153_447 FStar_Syntax_Syntax.Delta_constant None))
in ((_153_448), ((FStar_Syntax_Syntax.U_name (ucons2))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_153_449))
in (FStar_Syntax_Syntax.mk _153_450 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _153_451))
in (

let res = (let _153_455 = (let _153_454 = (let _153_453 = (let _153_452 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _153_452 FStar_Syntax_Syntax.Delta_constant None))
in ((_153_453), ((FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_153_454))
in (FStar_Syntax_Syntax.mk _153_455 None r2))
in (let _153_456 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow ((((a), (Some (FStar_Syntax_Syntax.imp_tag))))::(((hd), (None)))::(((tl), (None)))::[]) _153_456))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon (((lex_cons), ((ucons1)::(ucons2)::[]), (lex_cons_t), (FStar_Syntax_Const.lex_t_lid), ((Prims.parse_int "0")), ([]), ([]), (r2)))
in (let _153_458 = (let _153_457 = (FStar_TypeChecker_Env.get_range env)
in (((tc)::(dc_lextop)::(dc_lexcons)::[]), ([]), (lids), (_153_457)))
in FStar_Syntax_Syntax.Sig_bundle (_153_458)))))))))))))))
end
| _59_665 -> begin
(let _153_460 = (let _153_459 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle (((ses), ([]), (lids), (FStar_Range.dummyRange)))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _153_459))
in (FStar_All.failwith _153_460))
end))))
and tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _59_675 = (FStar_Syntax_Util.type_u ())
in (match (_59_675) with
| (k, _59_674) -> begin
(

let phi = (let _153_466 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _153_466 (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]) env)))
in (

let _59_677 = (FStar_TypeChecker_Util.check_uvars r phi)
in FStar_Syntax_Syntax.Sig_assume (((lid), (phi), (quals), (r)))))
end))))
and tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun env ses quals lids -> (

let warn_positivity = (fun l r -> (let _153_476 = (let _153_475 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _153_475))
in (FStar_TypeChecker_Errors.diag r _153_476)))
in (

let env0 = env
in (

let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(

let _59_700 = ()
in (

let _59_702 = (warn_positivity tc r)
in (

let _59_706 = (FStar_Syntax_Subst.open_term tps k)
in (match (_59_706) with
| (tps, k) -> begin
(

let _59_711 = (FStar_TypeChecker_TcTerm.tc_binders env tps)
in (match (_59_711) with
| (tps, env_tps, guard_params, us) -> begin
(

let _59_714 = (FStar_Syntax_Util.arrow_formals k)
in (match (_59_714) with
| (indices, t) -> begin
(

let _59_719 = (FStar_TypeChecker_TcTerm.tc_binders env_tps indices)
in (match (_59_719) with
| (indices, env', guard_indices, us') -> begin
(

let _59_727 = (

let _59_724 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' t)
in (match (_59_724) with
| (t, _59_722, g) -> begin
(let _153_483 = (let _153_482 = (let _153_481 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params _153_481))
in (FStar_TypeChecker_Rel.discharge_guard env' _153_482))
in ((t), (_153_483)))
end))
in (match (_59_727) with
| (t, guard) -> begin
(

let k = (let _153_484 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _153_484))
in (

let _59_731 = (FStar_Syntax_Util.type_u ())
in (match (_59_731) with
| (t_type, u) -> begin
(

let _59_732 = (let _153_485 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _153_485))
in (

let t_tc = (let _153_486 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _153_486))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _153_487 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) (([]), (t_tc)))
in ((_153_487), (FStar_Syntax_Syntax.Sig_inductive_typ (((tc), ([]), (tps), (k), (mutuals), (data), (quals), (r)))), (u), (guard))))))))
end)))
end))
end))
end))
end))
end))))
end
| _59_739 -> begin
(FStar_All.failwith "impossible")
end))
in (

let positive_if_pure = (fun _59_741 l -> ())
in (

let tc_data = (fun env tcs _59_1 -> (match (_59_1) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let _59_758 = ()
in (

let _59_793 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun _59_762 -> (match (_59_762) with
| (se, u_tc) -> begin
if (let _153_500 = (let _153_499 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _153_499))
in (FStar_Ident.lid_equals tc_lid _153_500)) then begin
(

let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_59_764, _59_766, tps, _59_769, _59_771, _59_773, _59_775, _59_777) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _59_783 -> (match (_59_783) with
| (x, _59_782) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
end
| _59_785 -> begin
(FStar_All.failwith "Impossible")
end)
in Some (((tps), (u_tc))))
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
(([]), (FStar_Syntax_Syntax.U_zero))
end else begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected data constructor"), (r)))))
end
end))
in (match (_59_793) with
| (tps, u_tc) -> begin
(

let _59_813 = (match ((let _153_502 = (FStar_Syntax_Subst.compress t)
in _153_502.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let _59_801 = (FStar_Util.first_N ntps bs)
in (match (_59_801) with
| (_59_799, bs') -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs'), (res)))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _59_807 -> (match (_59_807) with
| (x, _59_806) -> begin
FStar_Syntax_Syntax.DB ((((ntps - ((Prims.parse_int "1") + i))), (x)))
end))))
in (let _153_505 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _153_505))))
end))
end
| _59_810 -> begin
(([]), (t))
end)
in (match (_59_813) with
| (arguments, result) -> begin
(

let _59_814 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_508 = (FStar_Syntax_Print.lid_to_string c)
in (let _153_507 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _153_506 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _153_508 _153_507 _153_506))))
end else begin
()
end
in (

let _59_819 = (tc_tparams env arguments)
in (match (_59_819) with
| (arguments, env', us) -> begin
(

let _59_823 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env' result)
in (match (_59_823) with
| (result, _59_822) -> begin
(

let _59_827 = (FStar_Syntax_Util.head_and_args result)
in (match (_59_827) with
| (head, _59_826) -> begin
(

let _59_832 = (match ((let _153_509 = (FStar_Syntax_Subst.compress head)
in _153_509.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _59_831 -> begin
(let _153_514 = (let _153_513 = (let _153_512 = (let _153_511 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (let _153_510 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" _153_511 _153_510)))
in ((_153_512), (r)))
in FStar_Syntax_Syntax.Error (_153_513))
in (Prims.raise _153_514))
end)
in (

let g = (FStar_List.fold_left2 (fun g _59_838 u_x -> (match (_59_838) with
| (x, _59_837) -> begin
(

let _59_840 = ()
in (let _153_518 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _153_518)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _153_522 = (let _153_520 = (FStar_All.pipe_right tps (FStar_List.map (fun _59_846 -> (match (_59_846) with
| (x, _59_845) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append _153_520 arguments))
in (let _153_521 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _153_522 _153_521)))
in ((FStar_Syntax_Syntax.Sig_datacon (((c), ([]), (t), (tc_lid), (ntps), (quals), ([]), (r)))), (g)))))
end))
end))
end)))
end))
end)))
end
| _59_849 -> begin
(FStar_All.failwith "impossible")
end))
in (

let generalize_and_inst_within = (fun env g tcs datas -> (

let _59_855 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _59_2 -> (match (_59_2) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_59_859, _59_861, tps, k, _59_865, _59_867, _59_869, _59_871) -> begin
(let _153_533 = (let _153_532 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _153_532))
in (FStar_Syntax_Syntax.null_binder _153_533))
end
| _59_875 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _59_3 -> (match (_59_3) with
| FStar_Syntax_Syntax.Sig_datacon (_59_879, _59_881, t, _59_884, _59_886, _59_888, _59_890, _59_892) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _59_896 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let t = (let _153_535 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _153_535))
in (

let _59_899 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_536 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _153_536))
end else begin
()
end
in (

let _59_903 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_59_903) with
| (uvs, t) -> begin
(

let _59_905 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_540 = (let _153_538 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _153_538 (FStar_String.concat ", ")))
in (let _153_539 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _153_540 _153_539)))
end else begin
()
end
in (

let _59_909 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_59_909) with
| (uvs, t) -> begin
(

let _59_913 = (FStar_Syntax_Util.arrow_formals t)
in (match (_59_913) with
| (args, _59_912) -> begin
(

let _59_916 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_59_916) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun _59_920 se -> (match (_59_920) with
| (x, _59_919) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _59_924, tps, _59_927, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let _59_950 = (match ((let _153_543 = (FStar_Syntax_Subst.compress ty)
in _153_543.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _59_941 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_59_941) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _59_944 -> begin
(let _153_544 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) _153_544 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in ((tps), (t)))
end))
end
| _59_947 -> begin
(([]), (ty))
end)
in (match (_59_950) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs), (tps), (t), (mutuals), (datas), (quals), (r)))
end)))
end
| _59_952 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| _59_956 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _153_545 -> FStar_Syntax_Syntax.U_name (_153_545))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _59_4 -> (match (_59_4) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _59_961, _59_963, _59_965, _59_967, _59_969, _59_971, _59_973) -> begin
((tc), (uvs_universes))
end
| _59_977 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _59_982 d -> (match (_59_982) with
| (t, _59_981) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _59_986, _59_988, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (let _153_549 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _153_549 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon (((l), (uvs), (ty), (tc), (ntps), (quals), (mutuals), (r))))
end
| _59_998 -> begin
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

let _59_1008 = (FStar_All.pipe_right ses (FStar_List.partition (fun _59_5 -> (match (_59_5) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_59_1002) -> begin
true
end
| _59_1005 -> begin
false
end))))
in (match (_59_1008) with
| (tys, datas) -> begin
(

let _59_1015 = if (FStar_All.pipe_right datas (FStar_Util.for_some (fun _59_6 -> (match (_59_6) with
| FStar_Syntax_Syntax.Sig_datacon (_59_1011) -> begin
false
end
| _59_1014 -> begin
true
end)))) then begin
(let _153_554 = (let _153_553 = (let _153_552 = (FStar_TypeChecker_Env.get_range env)
in (("Mutually defined type contains a non-inductive element"), (_153_552)))
in FStar_Syntax_Syntax.Error (_153_553))
in (Prims.raise _153_554))
end else begin
()
end
in (

let env0 = env
in (

let _59_1034 = (FStar_List.fold_right (fun tc _59_1022 -> (match (_59_1022) with
| (env, all_tcs, g) -> begin
(

let _59_1027 = (tc_tycon env tc)
in (match (_59_1027) with
| (env, tc, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (

let _59_1029 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_557 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _153_557))
end else begin
()
end
in (let _153_559 = (let _153_558 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g _153_558))
in ((env), ((((tc), (tc_u)))::all_tcs), (_153_559)))))
end))
end)) tys ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (_59_1034) with
| (env, tcs, g) -> begin
(

let _59_1044 = (FStar_List.fold_right (fun se _59_1038 -> (match (_59_1038) with
| (datas, g) -> begin
(

let _59_1041 = (tc_data env tcs se)
in (match (_59_1041) with
| (data, g') -> begin
(let _153_562 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((data)::datas), (_153_562)))
end))
end)) datas (([]), (g)))
in (match (_59_1044) with
| (datas, g) -> begin
(

let _59_1047 = (let _153_563 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _153_563 datas))
in (match (_59_1047) with
| (tcs, datas) -> begin
(

let sig_bndle = (let _153_565 = (let _153_564 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_153_564)))
in FStar_Syntax_Syntax.Sig_bundle (_153_565))
in (

let datacon_typ = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (_59_1052, _59_1054, t, _59_1057, _59_1059, _59_1061, _59_1063, _59_1065) -> begin
t
end
| _59_1069 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let dr = FStar_Range.dummyRange
in (

let optimized_haseq_scheme = (fun _59_1072 -> (

let haseq_ty = (fun usubst us acc ty -> (

let _59_1099 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _59_1081, bs, t, _59_1085, d_lids, _59_1088, _59_1090) -> begin
((lid), (bs), (t), (d_lids))
end
| _59_1094 -> begin
(FStar_All.failwith "Impossible!")
end)
in (match (_59_1099) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _153_578 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _153_578 t))
in (

let _59_1104 = (FStar_Syntax_Subst.open_term bs t)
in (match (_59_1104) with
| (bs, t) -> begin
(

let ibs = (match ((let _153_579 = (FStar_Syntax_Subst.compress t)
in _153_579.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _59_1107) -> begin
ibs
end
| _59_1111 -> begin
[]
end)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _153_582 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _153_581 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _153_582 _153_581)))
in (

let ind = (let _153_585 = (FStar_List.map (fun _59_1118 -> (match (_59_1118) with
| (bv, aq) -> begin
(let _153_584 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_153_584), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _153_585 None dr))
in (

let ind = (let _153_588 = (FStar_List.map (fun _59_1122 -> (match (_59_1122) with
| (bv, aq) -> begin
(let _153_587 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_153_587), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _153_588 None dr))
in (

let haseq_ind = (let _153_590 = (let _153_589 = (FStar_Syntax_Syntax.as_arg ind)
in (_153_589)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _153_590 None dr))
in (

let bs' = (FStar_List.filter (fun b -> (

let _59_1133 = acc
in (match (_59_1133) with
| (_59_1127, en, _59_1130, _59_1132) -> begin
(

let opt = (let _153_593 = (let _153_592 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _153_592))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort _153_593 false))
in (match (opt) with
| None -> begin
false
end
| Some (_59_1137) -> begin
true
end))
end))) bs)
in (

let haseq_bs = (FStar_List.fold_left (fun t b -> (let _153_599 = (let _153_598 = (let _153_597 = (let _153_596 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b))
in (FStar_Syntax_Syntax.as_arg _153_596))
in (_153_597)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _153_598 None dr))
in (FStar_Syntax_Util.mk_conj t _153_599))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml = (

let _59_1144 = fml
in (let _153_605 = (let _153_604 = (let _153_603 = (let _153_602 = (let _153_601 = (let _153_600 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_153_600)::[])
in (_153_601)::[])
in FStar_Syntax_Syntax.Meta_pattern (_153_602))
in ((fml), (_153_603)))
in FStar_Syntax_Syntax.Tm_meta (_153_604))
in {FStar_Syntax_Syntax.n = _153_605; FStar_Syntax_Syntax.tk = _59_1144.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _59_1144.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _59_1144.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _153_611 = (let _153_610 = (let _153_609 = (let _153_608 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _153_608 None))
in (FStar_Syntax_Syntax.as_arg _153_609))
in (_153_610)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _153_611 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _153_617 = (let _153_616 = (let _153_615 = (let _153_614 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _153_614 None))
in (FStar_Syntax_Syntax.as_arg _153_615))
in (_153_616)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _153_617 None dr))) bs fml)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let _59_1158 = acc
in (match (_59_1158) with
| (l_axioms, env, guard', cond') -> begin
(

let env = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env = (FStar_TypeChecker_Env.push_binders env ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (_59_1163, _59_1165, _59_1167, t_lid, _59_1170, _59_1172, _59_1174, _59_1176) -> begin
(t_lid = lid)
end
| _59_1180 -> begin
(FStar_All.failwith "Impossible")
end)) datas)
in (

let haseq_data = (fun data -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (match ((let _153_621 = (FStar_Syntax_Subst.compress dt)
in _153_621.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _59_1188) -> begin
(

let dbs = (let _153_622 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _153_622))
in (

let dbs = (let _153_623 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _153_623 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let haseq_b = (let _153_627 = (let _153_626 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_153_626)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _153_627 None dr))
in (

let sort_range = (Prims.fst b).FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos
in (

let haseq_b = (let _153_629 = (let _153_628 = (FStar_Syntax_Print.term_to_string ind)
in (FStar_Util.format1 "Failed to prove that the type \'%s\' supports decidable equality because of this argument; add the \'noeq\' qualifier" _153_628))
in (FStar_TypeChecker_Util.label _153_629 sort_range haseq_b))
in (FStar_Syntax_Util.mk_conj t haseq_b))))) FStar_Syntax_Util.t_true dbs)
in (FStar_List.fold_right (fun b t -> (let _153_635 = (let _153_634 = (let _153_633 = (let _153_632 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _153_632 None))
in (FStar_Syntax_Syntax.as_arg _153_633))
in (_153_634)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _153_635 None dr))) dbs cond)))))
end
| _59_1203 -> begin
FStar_Syntax_Util.t_true
end))))
in (

let cond = (FStar_List.fold_left (fun acc d -> (let _153_638 = (haseq_data d)
in (FStar_Syntax_Util.mk_conj acc _153_638))) FStar_Syntax_Util.t_true t_datas)
in (

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (let _153_640 = (FStar_Syntax_Util.mk_conj guard' guard)
in (let _153_639 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml)))::[]))), (env), (_153_640), (_153_639))))))))))
end)))))))))))))))
end))))
end)))
in (

let us = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_59_1210, us, _59_1213, _59_1215, _59_1217, _59_1219, _59_1221, _59_1223) -> begin
us
end
| _59_1227 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let _59_1231 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (_59_1231) with
| (usubst, us) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (

let _59_1233 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq")
in (

let _59_1235 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle)
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let _59_1242 = (FStar_List.fold_left (haseq_ty usubst us) (([]), (env), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (_59_1242) with
| (axioms, env, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let _59_1247 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env phi)
in (match (_59_1247) with
| (phi, _59_1246) -> begin
(

let _59_1248 = if (FStar_TypeChecker_Env.should_verify env) then begin
(let _153_641 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi)))
in (FStar_TypeChecker_Rel.force_trivial_guard env _153_641))
end else begin
()
end
in (

let ses = (FStar_List.fold_left (fun l _59_1253 -> (match (_59_1253) with
| (lid, fml) -> begin
(

let se = (tc_assume env lid fml [] dr)
in (FStar_List.append l ((se)::[])))
end)) [] axioms)
in (

let _59_1256 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq")
in ses)))
end)))
end))))))
end)))))
in (

let unoptimized_haseq_scheme = (fun _59_1259 -> (

let mutuals = (FStar_List.map (fun ty -> (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _59_1264, _59_1266, _59_1268, _59_1270, _59_1272, _59_1274, _59_1276) -> begin
lid
end
| _59_1280 -> begin
(FStar_All.failwith "Impossible!")
end)) tcs)
in (

let haseq_ty = (fun usubst us acc ty -> (

let _59_1307 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _59_1289, bs, t, _59_1293, d_lids, _59_1296, _59_1298) -> begin
((lid), (bs), (t), (d_lids))
end
| _59_1302 -> begin
(FStar_All.failwith "Impossible!")
end)
in (match (_59_1307) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _153_655 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _153_655 t))
in (

let _59_1312 = (FStar_Syntax_Subst.open_term bs t)
in (match (_59_1312) with
| (bs, t) -> begin
(

let ibs = (match ((let _153_656 = (FStar_Syntax_Subst.compress t)
in _153_656.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _59_1315) -> begin
ibs
end
| _59_1319 -> begin
[]
end)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _153_659 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _153_658 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _153_659 _153_658)))
in (

let ind = (let _153_662 = (FStar_List.map (fun _59_1326 -> (match (_59_1326) with
| (bv, aq) -> begin
(let _153_661 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_153_661), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _153_662 None dr))
in (

let ind = (let _153_665 = (FStar_List.map (fun _59_1330 -> (match (_59_1330) with
| (bv, aq) -> begin
(let _153_664 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_153_664), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _153_665 None dr))
in (

let haseq_ind = (let _153_667 = (let _153_666 = (FStar_Syntax_Syntax.as_arg ind)
in (_153_666)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _153_667 None dr))
in (

let rec is_mutual = (fun t -> (match ((let _153_671 = (FStar_Syntax_Subst.compress t)
in _153_671.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.existsb (fun lid -> (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) mutuals)
end
| FStar_Syntax_Syntax.Tm_uinst (t', _59_1341) -> begin
(is_mutual t')
end
| FStar_Syntax_Syntax.Tm_refine (bv, t') -> begin
(is_mutual bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_app (t', args) -> begin
if (is_mutual t') then begin
true
end else begin
(let _153_673 = (FStar_List.map Prims.fst args)
in (exists_mutual _153_673))
end
end
| FStar_Syntax_Syntax.Tm_meta (t', _59_1354) -> begin
(is_mutual t')
end
| _59_1358 -> begin
false
end))
and exists_mutual = (fun _59_7 -> (match (_59_7) with
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
in (match ((let _153_679 = (FStar_Syntax_Subst.compress dt)
in _153_679.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _59_1371) -> begin
(

let dbs = (let _153_680 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _153_680))
in (

let dbs = (let _153_681 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _153_681 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let sort = (Prims.fst b).FStar_Syntax_Syntax.sort
in (

let haseq_sort = (let _153_685 = (let _153_684 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_153_684)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _153_685 None dr))
in (

let haseq_sort = if (is_mutual sort) then begin
(FStar_Syntax_Util.mk_imp haseq_ind haseq_sort)
end else begin
haseq_sort
end
in (FStar_Syntax_Util.mk_conj t haseq_sort))))) FStar_Syntax_Util.t_true dbs)
in (

let cond = (FStar_List.fold_right (fun b t -> (let _153_691 = (let _153_690 = (let _153_689 = (let _153_688 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _153_688 None))
in (FStar_Syntax_Syntax.as_arg _153_689))
in (_153_690)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _153_691 None dr))) dbs cond)
in (FStar_Syntax_Util.mk_conj acc cond))))))
end
| _59_1387 -> begin
acc
end))))
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (_59_1390, _59_1392, _59_1394, t_lid, _59_1397, _59_1399, _59_1401, _59_1403) -> begin
(t_lid = lid)
end
| _59_1407 -> begin
(FStar_All.failwith "Impossible")
end)) datas)
in (

let data_cond = (FStar_List.fold_left haseq_data FStar_Syntax_Util.t_true t_datas)
in (

let fml = (FStar_Syntax_Util.mk_imp data_cond haseq_ind)
in (

let fml = (

let _59_1411 = fml
in (let _153_698 = (let _153_697 = (let _153_696 = (let _153_695 = (let _153_694 = (let _153_693 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_153_693)::[])
in (_153_694)::[])
in FStar_Syntax_Syntax.Meta_pattern (_153_695))
in ((fml), (_153_696)))
in FStar_Syntax_Syntax.Tm_meta (_153_697))
in {FStar_Syntax_Syntax.n = _153_698; FStar_Syntax_Syntax.tk = _59_1411.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _59_1411.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _59_1411.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _153_704 = (let _153_703 = (let _153_702 = (let _153_701 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _153_701 None))
in (FStar_Syntax_Syntax.as_arg _153_702))
in (_153_703)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _153_704 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _153_710 = (let _153_709 = (let _153_708 = (let _153_707 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _153_707 None))
in (FStar_Syntax_Syntax.as_arg _153_708))
in (_153_709)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _153_710 None dr))) bs fml)
in (FStar_Syntax_Util.mk_conj acc fml)))))))))))))))
end))))
end)))
in (

let _59_1441 = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, _59_1424, _59_1426, _59_1428, _59_1430, _59_1432, _59_1434) -> begin
((lid), (us))
end
| _59_1438 -> begin
(FStar_All.failwith "Impossible!")
end))
in (match (_59_1441) with
| (lid, us) -> begin
(

let _59_1444 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (_59_1444) with
| (usubst, us) -> begin
(

let fml = (FStar_List.fold_left (haseq_ty usubst us) FStar_Syntax_Util.t_true tcs)
in (

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (

let _59_1447 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq")
in (

let _59_1449 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle)
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let se = (let _153_711 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (tc_assume env _153_711 fml [] dr))
in (se)::[]))))))
end))
end)))))
in (

let is_noeq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Noeq)) quals)
in if (((FStar_Ident.lid_equals env.FStar_TypeChecker_Env.curmodule FStar_Syntax_Const.prims_lid) || is_noeq) || ((FStar_List.length tcs) = (Prims.parse_int "0"))) then begin
(sig_bndle)::[]
end else begin
(

let is_unopteq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Unopteq)) quals)
in (

let ses = if is_unopteq then begin
(unoptimized_haseq_scheme ())
end else begin
(optimized_haseq_scheme ())
end
in (let _153_716 = (let _153_715 = (let _153_714 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_153_714)))
in FStar_Syntax_Syntax.Sig_bundle (_153_715))
in (_153_716)::ses)))
end))))))
end))
end))
end))))
end)))))))))
and tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env se -> (

let env = (set_hint_correlator env se)
in (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let se = (tc_lex_t env ses quals lids)
in (let _153_719 = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (_153_719)))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let ses = (tc_inductive env ses quals lids)
in (

let env = (FStar_List.fold_left (fun env' se -> (FStar_TypeChecker_Env.push_sigelt env' se)) env ses)
in ((ses), (env)))))
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

let _59_1499 = (set_options FStar_Options.Set o)
in (((se)::[]), (env)))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(

let _59_1503 = (let _153_726 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _153_726 Prims.ignore))
in (

let _59_1508 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (

let _59_1510 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (((se)::[]), (env)))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_59_1513) -> begin
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

let _59_1529 = (FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun _59_1524 a -> (match (_59_1524) with
| (env, ses) -> begin
(

let se_let = (FStar_Syntax_Util.action_as_lb a)
in (let _153_729 = (FStar_TypeChecker_Env.push_sigelt env se_let)
in ((_153_729), ((se_let)::ses))))
end)) ((env), ((se)::[]))))
in (match (_59_1529) with
| (env, ses) -> begin
(((se)::[]), (env))
end)))))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub, r) -> begin
(

let ed_src = (FStar_TypeChecker_Env.get_effect_decl env sub.FStar_Syntax_Syntax.source)
in (

let ed_tgt = (FStar_TypeChecker_Env.get_effect_decl env sub.FStar_Syntax_Syntax.target)
in (

let _59_1538 = (let _153_730 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _153_730))
in (match (_59_1538) with
| (a, wp_a_src) -> begin
(

let _59_1541 = (let _153_731 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _153_731))
in (match (_59_1541) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (let _153_735 = (let _153_734 = (let _153_733 = (let _153_732 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (_153_732)))
in FStar_Syntax_Syntax.NT (_153_733))
in (_153_734)::[])
in (FStar_Syntax_Subst.subst _153_735 wp_b_tgt))
in (

let expected_k = (let _153_740 = (let _153_738 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_737 = (let _153_736 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_153_736)::[])
in (_153_738)::_153_737))
in (let _153_739 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _153_740 _153_739)))
in (

let lift_wp = (check_and_gen env (Prims.snd sub.FStar_Syntax_Syntax.lift_wp) expected_k)
in (

let repr_type = (fun eff_name a wp -> (

let no_reify = (fun l -> (let _153_752 = (let _153_751 = (let _153_750 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _153_749 = (FStar_TypeChecker_Env.get_range env)
in ((_153_750), (_153_749))))
in FStar_Syntax_Syntax.Error (_153_751))
in (Prims.raise _153_752)))
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
(let _153_759 = (let _153_757 = (let _153_756 = (let _153_755 = (FStar_Syntax_Syntax.as_arg a)
in (let _153_754 = (let _153_753 = (FStar_Syntax_Syntax.as_arg wp)
in (_153_753)::[])
in (_153_755)::_153_754))
in ((repr), (_153_756)))
in FStar_Syntax_Syntax.Tm_app (_153_757))
in (let _153_758 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _153_759 None _153_758)))
end)
end)))
in (

let lift = (match (sub.FStar_Syntax_Syntax.lift) with
| None -> begin
None
end
| Some (_59_1557, lift) -> begin
(

let _59_1563 = (let _153_760 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _153_760))
in (match (_59_1563) with
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

let lift_wp_a = (let _153_767 = (let _153_765 = (let _153_764 = (let _153_763 = (FStar_Syntax_Syntax.as_arg a_typ)
in (let _153_762 = (let _153_761 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (_153_761)::[])
in (_153_763)::_153_762))
in (((Prims.snd sub.FStar_Syntax_Syntax.lift_wp)), (_153_764)))
in FStar_Syntax_Syntax.Tm_app (_153_765))
in (let _153_766 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _153_767 None _153_766)))
in (repr_type sub.FStar_Syntax_Syntax.target a_typ lift_wp_a))
in (

let expected_k = (let _153_774 = (let _153_772 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_771 = (let _153_770 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (let _153_769 = (let _153_768 = (FStar_Syntax_Syntax.null_binder repr_f)
in (_153_768)::[])
in (_153_770)::_153_769))
in (_153_772)::_153_771))
in (let _153_773 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow _153_774 _153_773)))
in (

let _59_1576 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (_59_1576) with
| (expected_k, _59_1573, _59_1575) -> begin
(

let lift = (check_and_gen env lift expected_k)
in Some (lift))
end))))))))
end))
end)
in (

let sub = (

let _59_1579 = sub
in {FStar_Syntax_Syntax.source = _59_1579.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _59_1579.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift})
in (

let se = FStar_Syntax_Syntax.Sig_sub_effect (((sub), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env))))))))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, r) -> begin
(

let _59_1592 = ()
in (

let env0 = env
in (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _59_1598 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_59_1598) with
| (tps, c) -> begin
(

let _59_1602 = (tc_tparams env tps)
in (match (_59_1602) with
| (tps, env, us) -> begin
(

let _59_1606 = (FStar_TypeChecker_TcTerm.tc_comp env c)
in (match (_59_1606) with
| (c, u, g) -> begin
(

let _59_1607 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

let _59_1613 = (let _153_775 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _153_775))
in (match (_59_1613) with
| (uvs, t) -> begin
(

let _59_1632 = (match ((let _153_777 = (let _153_776 = (FStar_Syntax_Subst.compress t)
in _153_776.FStar_Syntax_Syntax.n)
in ((tps), (_153_777)))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_59_1616, c)) -> begin
(([]), (c))
end
| (_59_1622, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
((tps), (c))
end
| _59_1629 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_59_1632) with
| (tps, c) -> begin
(

let se = FStar_Syntax_Syntax.Sig_effect_abbrev (((lid), (uvs), (tps), (c), (tags), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env0 se)
in (((se)::[]), (env))))
end))
end)))))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t, quals, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _59_1643 = ()
in (

let _59_1647 = (let _153_779 = (let _153_778 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _153_778))
in (check_and_gen env t _153_779))
in (match (_59_1647) with
| (uvs, t) -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (uvs), (t), (quals), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env))))
end))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, phi, quals, r) -> begin
(

let se = (tc_assume env lid phi quals r)
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env))))
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (

let _59_1667 = (FStar_TypeChecker_TcTerm.tc_term env e)
in (match (_59_1667) with
| (e, c, g1) -> begin
(

let _59_1672 = (let _153_783 = (let _153_780 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_153_780))
in (let _153_782 = (let _153_781 = (c.FStar_Syntax_Syntax.comp ())
in ((e), (_153_781)))
in (FStar_TypeChecker_TcTerm.check_expected_effect env _153_783 _153_782)))
in (match (_59_1672) with
| (e, _59_1670, g) -> begin
(

let _59_1673 = (let _153_784 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _153_784))
in (

let se = FStar_Syntax_Syntax.Sig_main (((e), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env)))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, lids, quals) -> begin
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
(let _153_796 = (let _153_795 = (let _153_794 = (let _153_793 = (FStar_Syntax_Print.lid_to_string l)
in (let _153_792 = (FStar_Syntax_Print.quals_to_string q)
in (let _153_791 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _153_793 _153_792 _153_791))))
in ((_153_794), (r)))
in FStar_Syntax_Syntax.Error (_153_795))
in (Prims.raise _153_796))
end
end))
in (

let _59_1717 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _59_1694 lb -> (match (_59_1694) with
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _59_1713 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
((gen), (lb), (quals_opt))
end
| Some ((uvs, tval), quals) -> begin
(

let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (

let _59_1708 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _59_1707 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _153_799 = (FStar_Syntax_Syntax.mk_lb ((FStar_Util.Inr (lbname)), (uvs), (FStar_Syntax_Const.effect_ALL_lid), (tval), (lb.FStar_Syntax_Syntax.lbdef)))
in ((false), (_153_799), (quals_opt)))))
end)
in (match (_59_1713) with
| (gen, lb, quals_opt) -> begin
((gen), ((lb)::lbs), (quals_opt))
end)))
end)) ((true), ([]), (if (quals = []) then begin
None
end else begin
Some (quals)
end))))
in (match (_59_1717) with
| (should_generalize, lbs', quals_opt) -> begin
(

let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Unfoldable)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _59_8 -> (match (_59_8) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfoldable) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _59_1726 -> begin
false
end)))) then begin
q
end else begin
(FStar_Syntax_Syntax.Unfoldable)::q
end
end)
in (

let lbs' = (FStar_List.rev lbs')
in (

let e = (let _153_803 = (let _153_802 = (let _153_801 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((((Prims.fst lbs)), (lbs'))), (_153_801)))
in FStar_Syntax_Syntax.Tm_let (_153_802))
in (FStar_Syntax_Syntax.mk _153_803 None r))
in (

let _59_1760 = (match ((FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term (

let _59_1730 = env
in {FStar_TypeChecker_Env.solver = _59_1730.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_1730.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_1730.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_1730.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_1730.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_1730.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_1730.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_1730.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_1730.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_1730.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_1730.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _59_1730.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _59_1730.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_1730.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_1730.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_1730.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_1730.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _59_1730.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_1730.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_1730.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_1730.FStar_TypeChecker_Env.qname_and_index}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _59_1737; FStar_Syntax_Syntax.pos = _59_1735; FStar_Syntax_Syntax.vars = _59_1733}, _59_1744, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_59_1748, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _59_1754 -> begin
quals
end)
in ((FStar_Syntax_Syntax.Sig_let (((lbs), (r), (lids), (quals)))), (lbs)))
end
| _59_1757 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_59_1760) with
| (se, lbs) -> begin
(

let _59_1766 = if (log env) then begin
(let _153_811 = (let _153_810 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (match ((let _153_807 = (let _153_806 = (let _153_805 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _153_805.FStar_Syntax_Syntax.fv_name)
in _153_806.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _153_807))) with
| None -> begin
true
end
| _59_1764 -> begin
false
end)
in if should_log then begin
(let _153_809 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _153_808 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _153_809 _153_808)))
end else begin
""
end))))
in (FStar_All.pipe_right _153_810 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _153_811))
end else begin
()
end
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env))))
end)))))
end))))
end)))


let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _59_9 -> (match (_59_9) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _59_1776 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _59_1786 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_59_1788) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _59_1799, _59_1801) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _59_1807 -> (match (_59_1807) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _59_1813, _59_1815, quals, r) -> begin
(

let dec = (let _153_825 = (let _153_824 = (let _153_823 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow bs _153_823))
in ((l), (us), (_153_824), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (_153_825))
in (((dec)::out), (hidden)))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _59_1825, _59_1827, _59_1829, _59_1831, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]), (r)))
in (((dec)::out), ((l)::hidden)))
end
| _59_1837 -> begin
((out), (hidden))
end)
end)) ses (([]), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end
| FStar_Syntax_Syntax.Sig_assume (_59_1839, _59_1841, quals, _59_1844) -> begin
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
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _59_10 -> (match (_59_10) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _59_1863 -> begin
false
end)))) then begin
(((se)::[]), (hidden))
end else begin
(([]), (hidden))
end
end
end
| FStar_Syntax_Syntax.Sig_main (_59_1865) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _59_1884, _59_1886, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
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
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals) -> begin
if (is_abstract quals) then begin
(let _153_832 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _153_831 = (let _153_830 = (let _153_829 = (let _153_828 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _153_828.FStar_Syntax_Syntax.fv_name)
in _153_829.FStar_Syntax_Syntax.v)
in ((_153_830), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (_153_831)))))
in ((_153_832), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let process_one_decl = (fun _59_1907 se -> (match (_59_1907) with
| (ses, exports, env, hidden) -> begin
(

let _59_1909 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_841 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _153_841))
end else begin
()
end
in (

let _59_1913 = (tc_decl env se)
in (match (_59_1913) with
| (ses', env) -> begin
(

let _59_1916 = if ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _153_846 = (FStar_List.fold_left (fun s se -> (let _153_845 = (let _153_844 = (FStar_Syntax_Print.sigelt_to_string se)
in (Prims.strcat _153_844 "\n"))
in (Prims.strcat s _153_845))) "" ses')
in (FStar_Util.print1 "Checked: %s\n" _153_846))
end else begin
()
end
in (

let _59_1919 = (FStar_List.iter (fun se -> (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)) ses')
in (

let _59_1928 = (FStar_List.fold_left (fun _59_1923 se -> (match (_59_1923) with
| (le, lh) -> begin
(

let tup = (for_export hidden se)
in (((FStar_List.rev_append (Prims.fst tup) le)), ((FStar_List.rev_append (Prims.snd tup) lh))))
end)) (([]), ([])) ses')
in (match (_59_1928) with
| (exported, hidden) -> begin
(((FStar_List.rev_append ses' ses)), (((FStar_List.rev_append exported []))::exports), (env), (hidden))
end))))
end)))
end))
in (

let _59_1954 = (FStar_List.fold_left (fun acc se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, r) -> begin
(

let _59_1942 = acc
in (match (_59_1942) with
| (_59_1936, _59_1938, env, _59_1941) -> begin
(

let _59_1945 = (cps_and_elaborate env ne)
in (match (_59_1945) with
| (ses, ne) -> begin
(

let ses = (FStar_List.append ses ((FStar_Syntax_Syntax.Sig_new_effect (((ne), (r))))::[]))
in (FStar_List.fold_left process_one_decl acc ses))
end))
end))
end
| _59_1948 -> begin
(process_one_decl acc se)
end)) (([]), ([]), (env), ([])) ses)
in (match (_59_1954) with
| (ses, exports, env, _59_1953) -> begin
(let _153_852 = (FStar_All.pipe_right (FStar_List.rev_append exports []) FStar_List.flatten)
in (((FStar_List.rev_append ses [])), (_153_852), (env)))
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

let _59_1959 = env
in (let _153_857 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _59_1959.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_1959.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_1959.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_1959.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_1959.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_1959.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_1959.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_1959.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_1959.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_1959.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_1959.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_1959.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_1959.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_1959.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_1959.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_1959.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _153_857; FStar_TypeChecker_Env.lax = _59_1959.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _59_1959.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_1959.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_1959.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_1959.FStar_TypeChecker_Env.qname_and_index}))
in (

let _59_1962 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
in (

let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

let _59_1968 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_59_1968) with
| (ses, exports, env) -> begin
(((

let _59_1969 = modul
in {FStar_Syntax_Syntax.name = _59_1969.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _59_1969.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _59_1969.FStar_Syntax_Syntax.is_interface})), (exports), (env))
end))))))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let _59_1977 = (tc_decls env decls)
in (match (_59_1977) with
| (ses, exports, env) -> begin
(

let modul = (

let _59_1978 = modul
in {FStar_Syntax_Syntax.name = _59_1978.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _59_1978.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _59_1978.FStar_Syntax_Syntax.is_interface})
in ((modul), (exports), (env)))
end)))


let finish_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelts  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul exports -> (

let modul = (

let _59_1984 = modul
in {FStar_Syntax_Syntax.name = _59_1984.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _59_1984.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module env modul)
in (

let _59_1988 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (

let _59_1990 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (

let _59_1992 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (

let _59_1994 = (let _153_870 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _153_870 Prims.ignore))
in ((modul), (env)))))))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let _59_2001 = (tc_partial_modul env modul)
in (match (_59_2001) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (

let _59_2004 = if (FStar_Options.debug_any ()) then begin
(let _153_879 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _153_879))
end else begin
()
end
in (

let _59_2008 = (tc_modul env m)
in (match (_59_2008) with
| (m, env) -> begin
(

let _59_2009 = if (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _153_880 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _153_880))
end else begin
()
end
in ((m), (env)))
end))))




