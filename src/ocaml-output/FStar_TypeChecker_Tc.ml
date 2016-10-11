
open Prims

let set_hint_correlator : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env = (fun env se -> (match ((FStar_Options.reuse_hint_for ())) with
| Some (l) -> begin
(

let lid = (let _153_5 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_add_suffix _153_5 l))
in (

let _59_17 = env
in {FStar_TypeChecker_Env.solver = _59_17.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_17.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_17.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_17.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_17.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_17.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_17.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_17.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_17.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_17.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_17.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_17.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_17.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_17.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_17.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_17.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_17.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_17.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_17.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _59_17.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_17.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_17.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_17.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), ((Prims.parse_int "0"))))}))
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
| (l)::_59_23 -> begin
l
end)
in (

let _59_27 = env
in {FStar_TypeChecker_Env.solver = _59_27.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_27.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_27.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_27.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_27.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_27.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_27.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_27.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_27.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_27.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_27.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_27.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_27.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_27.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_27.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_27.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_27.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_27.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_27.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _59_27.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_27.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_27.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_27.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), ((Prims.parse_int "0"))))})))
end))


let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_Options.log_types ()) && (not ((let _153_11 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _153_11))))))


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let _59_36 = (FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k)
in (match (_59_36) with
| (t, c, g) -> begin
(

let _59_37 = (FStar_ST.op_Colon_Equals t.FStar_Syntax_Syntax.tk (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)))
in (

let _59_39 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t))
end)))


let recheck_debug : Prims.string  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s env t -> (

let _59_44 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _153_24 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Term has been %s-transformed to:\n%s\n----------\n" s _153_24))
end else begin
()
end
in (

let _59_51 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (_59_51) with
| (t', _59_48, _59_50) -> begin
(

let _59_52 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _153_25 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print1 "Re-checked; got:\n%s\n----------\n" _153_25))
end else begin
()
end
in t)
end))))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _153_32 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _153_32)))


let check_nogen = (fun env t k -> (

let t = (tc_check_trivial_guard env t k)
in (let _153_36 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (([]), (_153_36)))))


let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let _59_67 = (FStar_TypeChecker_TcTerm.tc_binders env tps)
in (match (_59_67) with
| (tps, env, g, us) -> begin
(

let _59_68 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in ((tps), (env), (us)))
end)))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (

let fail = (fun _59_74 -> (match (()) with
| () -> begin
(let _153_51 = (let _153_50 = (let _153_49 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in ((_153_49), ((FStar_Ident.range_of_lid m))))
in FStar_Syntax_Syntax.Error (_153_50))
in (Prims.raise _153_51))
end))
in (

let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _59_87))::((wp, _59_83))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _59_91 -> begin
(fail ())
end))
end
| _59_93 -> begin
(fail ())
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let _59_100 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_59_100) with
| (uvs, c) -> begin
((uvs), ([]), (c))
end))
end
| _59_102 -> begin
(

let t' = (FStar_Syntax_Util.arrow binders c)
in (

let _59_106 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_59_106) with
| (uvs, t') -> begin
(match ((let _153_58 = (FStar_Syntax_Subst.compress t')
in _153_58.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
((uvs), (binders), (c))
end
| _59_112 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))


let rec tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (

let _59_115 = ()
in (

let _59_120 = (FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_59_120) with
| (effect_params_un, signature_un, opening) -> begin
(

let _59_125 = (tc_tparams env0 effect_params_un)
in (match (_59_125) with
| (effect_params, env, _59_124) -> begin
(

let _59_129 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (_59_129) with
| (signature, _59_128) -> begin
(

let ed = (

let _59_130 = ed
in {FStar_Syntax_Syntax.qualifiers = _59_130.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _59_130.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _59_130.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _59_130.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _59_130.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _59_130.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _59_130.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _59_130.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _59_130.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _59_130.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _59_130.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _59_130.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _59_130.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _59_130.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _59_130.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _59_130.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _59_130.FStar_Syntax_Syntax.actions})
in (

let ed = (match (effect_params) with
| [] -> begin
ed
end
| _59_135 -> begin
(

let op = (fun ts -> (

let _59_138 = ()
in (

let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in (([]), (t1)))))
in (

let _59_141 = ed
in (let _153_101 = (op ed.FStar_Syntax_Syntax.ret_wp)
in (let _153_100 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _153_99 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _153_98 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _153_97 = (op ed.FStar_Syntax_Syntax.stronger)
in (let _153_96 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _153_95 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _153_94 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _153_93 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _153_92 = (op ed.FStar_Syntax_Syntax.trivial)
in (let _153_91 = (let _153_82 = (op (([]), (ed.FStar_Syntax_Syntax.repr)))
in (Prims.snd _153_82))
in (let _153_90 = (op ed.FStar_Syntax_Syntax.return_repr)
in (let _153_89 = (op ed.FStar_Syntax_Syntax.bind_repr)
in (let _153_88 = (FStar_List.map (fun a -> (

let _59_144 = a
in (let _153_87 = (let _153_84 = (op (([]), (a.FStar_Syntax_Syntax.action_defn)))
in (Prims.snd _153_84))
in (let _153_86 = (let _153_85 = (op (([]), (a.FStar_Syntax_Syntax.action_typ)))
in (Prims.snd _153_85))
in {FStar_Syntax_Syntax.action_name = _59_144.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = _59_144.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _153_87; FStar_Syntax_Syntax.action_typ = _153_86})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.qualifiers = _59_141.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _59_141.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _59_141.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _59_141.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _59_141.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _153_101; FStar_Syntax_Syntax.bind_wp = _153_100; FStar_Syntax_Syntax.if_then_else = _153_99; FStar_Syntax_Syntax.ite_wp = _153_98; FStar_Syntax_Syntax.stronger = _153_97; FStar_Syntax_Syntax.close_wp = _153_96; FStar_Syntax_Syntax.assert_p = _153_95; FStar_Syntax_Syntax.assume_p = _153_94; FStar_Syntax_Syntax.null_wp = _153_93; FStar_Syntax_Syntax.trivial = _153_92; FStar_Syntax_Syntax.repr = _153_91; FStar_Syntax_Syntax.return_repr = _153_90; FStar_Syntax_Syntax.bind_repr = _153_89; FStar_Syntax_Syntax.actions = _153_88}))))))))))))))))
end)
in (

let wp_with_fresh_result_type = (fun env mname signature -> (

let fail = (fun t -> (let _153_112 = (let _153_111 = (let _153_110 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in ((_153_110), ((FStar_Ident.range_of_lid mname))))
in FStar_Syntax_Syntax.Error (_153_111))
in (Prims.raise _153_112)))
in (match ((let _153_113 = (FStar_Syntax_Subst.compress signature)
in _153_113.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _59_164))::((wp, _59_160))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _59_168 -> begin
(fail signature)
end))
end
| _59_170 -> begin
(fail signature)
end)))
in (

let _59_173 = (wp_with_fresh_result_type env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_59_173) with
| (a, wp_a) -> begin
(

let fresh_effect_signature = (fun _59_175 -> (match (()) with
| () -> begin
(

let _59_179 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (_59_179) with
| (signature, _59_178) -> begin
(wp_with_fresh_result_type env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (

let env = (let _153_116 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _153_116))
in (

let _59_181 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _153_122 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _153_121 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _153_120 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _153_119 = (let _153_117 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Print.term_to_string _153_117))
in (let _153_118 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.sort)
in (FStar_Util.print5 "Checking effect signature: %s %s : %s\n(a is %s:%s)\n" _153_122 _153_121 _153_120 _153_119 _153_118))))))
end else begin
()
end
in (

let check_and_gen' = (fun env _59_188 k -> (match (_59_188) with
| (_59_186, t) -> begin
(check_and_gen env t k)
end))
in (

let return_wp = (

let expected_k = (let _153_134 = (let _153_132 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_131 = (let _153_130 = (let _153_129 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _153_129))
in (_153_130)::[])
in (_153_132)::_153_131))
in (let _153_133 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _153_134 _153_133)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret_wp expected_k))
in (

let bind_wp = (

let _59_194 = (fresh_effect_signature ())
in (match (_59_194) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _153_138 = (let _153_136 = (let _153_135 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _153_135))
in (_153_136)::[])
in (let _153_137 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _153_138 _153_137)))
in (

let expected_k = (let _153_149 = (let _153_147 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _153_146 = (let _153_145 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_144 = (let _153_143 = (FStar_Syntax_Syntax.mk_binder b)
in (let _153_142 = (let _153_141 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _153_140 = (let _153_139 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (_153_139)::[])
in (_153_141)::_153_140))
in (_153_143)::_153_142))
in (_153_145)::_153_144))
in (_153_147)::_153_146))
in (let _153_148 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _153_149 _153_148)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else = (

let p = (let _153_151 = (let _153_150 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _153_150 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _153_151))
in (

let expected_k = (let _153_160 = (let _153_158 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_157 = (let _153_156 = (FStar_Syntax_Syntax.mk_binder p)
in (let _153_155 = (let _153_154 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _153_153 = (let _153_152 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_152)::[])
in (_153_154)::_153_153))
in (_153_156)::_153_155))
in (_153_158)::_153_157))
in (let _153_159 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_160 _153_159)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (let _153_165 = (let _153_163 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_162 = (let _153_161 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_161)::[])
in (_153_163)::_153_162))
in (let _153_164 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_165 _153_164)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let _59_206 = (FStar_Syntax_Util.type_u ())
in (match (_59_206) with
| (t, _59_205) -> begin
(

let expected_k = (let _153_172 = (let _153_170 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_169 = (let _153_168 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _153_167 = (let _153_166 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_166)::[])
in (_153_168)::_153_167))
in (_153_170)::_153_169))
in (let _153_171 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _153_172 _153_171)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (let _153_174 = (let _153_173 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _153_173 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _153_174))
in (

let b_wp_a = (let _153_178 = (let _153_176 = (let _153_175 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _153_175))
in (_153_176)::[])
in (let _153_177 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_178 _153_177)))
in (

let expected_k = (let _153_185 = (let _153_183 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_182 = (let _153_181 = (FStar_Syntax_Syntax.mk_binder b)
in (let _153_180 = (let _153_179 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_153_179)::[])
in (_153_181)::_153_180))
in (_153_183)::_153_182))
in (let _153_184 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_185 _153_184)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (let _153_194 = (let _153_192 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_191 = (let _153_190 = (let _153_187 = (let _153_186 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _153_186 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _153_187))
in (let _153_189 = (let _153_188 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_188)::[])
in (_153_190)::_153_189))
in (_153_192)::_153_191))
in (let _153_193 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_194 _153_193)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (let _153_203 = (let _153_201 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_200 = (let _153_199 = (let _153_196 = (let _153_195 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _153_195 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _153_196))
in (let _153_198 = (let _153_197 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_197)::[])
in (_153_199)::_153_198))
in (_153_201)::_153_200))
in (let _153_202 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_203 _153_202)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (let _153_206 = (let _153_204 = (FStar_Syntax_Syntax.mk_binder a)
in (_153_204)::[])
in (let _153_205 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _153_206 _153_205)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let _59_222 = (FStar_Syntax_Util.type_u ())
in (match (_59_222) with
| (t, _59_221) -> begin
(

let expected_k = (let _153_211 = (let _153_209 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_208 = (let _153_207 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_207)::[])
in (_153_209)::_153_208))
in (let _153_210 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _153_211 _153_210)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let _59_366 = (match ((let _153_212 = (FStar_Syntax_Subst.compress ed.FStar_Syntax_Syntax.repr)
in _153_212.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((ed.FStar_Syntax_Syntax.repr), (ed.FStar_Syntax_Syntax.bind_repr), (ed.FStar_Syntax_Syntax.return_repr), (ed.FStar_Syntax_Syntax.actions))
end
| _59_227 -> begin
(

let repr = (

let _59_231 = (FStar_Syntax_Util.type_u ())
in (match (_59_231) with
| (t, _59_230) -> begin
(

let expected_k = (let _153_217 = (let _153_215 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_214 = (let _153_213 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_213)::[])
in (_153_215)::_153_214))
in (let _153_216 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _153_217 _153_216)))
in (tc_check_trivial_guard env ed.FStar_Syntax_Syntax.repr expected_k))
end))
in (

let mk_repr' = (fun t wp -> (

let repr = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env repr)
in (let _153_227 = (let _153_226 = (let _153_225 = (let _153_224 = (FStar_Syntax_Syntax.as_arg t)
in (let _153_223 = (let _153_222 = (FStar_Syntax_Syntax.as_arg wp)
in (_153_222)::[])
in (_153_224)::_153_223))
in ((repr), (_153_225)))
in FStar_Syntax_Syntax.Tm_app (_153_226))
in (FStar_Syntax_Syntax.mk _153_227 None FStar_Range.dummyRange))))
in (

let mk_repr = (fun a wp -> (let _153_232 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_repr' _153_232 wp)))
in (

let destruct_repr = (fun t -> (match ((let _153_235 = (FStar_Syntax_Subst.compress t)
in _153_235.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_59_244, ((t, _59_251))::((wp, _59_247))::[]) -> begin
((t), (wp))
end
| _59_257 -> begin
(FStar_All.failwith "Unexpected repr type")
end))
in (

let bind_repr = (

let r = (let _153_236 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_0 FStar_Syntax_Syntax.Delta_constant None)
in (FStar_All.pipe_right _153_236 FStar_Syntax_Syntax.fv_to_tm))
in (

let _59_261 = (fresh_effect_signature ())
in (match (_59_261) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _153_240 = (let _153_238 = (let _153_237 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _153_237))
in (_153_238)::[])
in (let _153_239 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _153_240 _153_239)))
in (

let wp_f = (FStar_Syntax_Syntax.gen_bv "wp_f" None wp_a)
in (

let wp_g = (FStar_Syntax_Syntax.gen_bv "wp_g" None a_wp_b)
in (

let x_a = (let _153_241 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _153_241))
in (

let wp_g_x = (let _153_245 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (let _153_244 = (let _153_243 = (let _153_242 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _153_242))
in (_153_243)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _153_245 _153_244 None FStar_Range.dummyRange)))
in (

let res = (

let wp = (let _153_257 = (let _153_246 = (FStar_TypeChecker_Env.inst_tscheme bind_wp)
in (FStar_All.pipe_right _153_246 Prims.snd))
in (let _153_256 = (let _153_255 = (let _153_254 = (let _153_253 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _153_252 = (let _153_251 = (FStar_Syntax_Syntax.bv_to_name b)
in (let _153_250 = (let _153_249 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (let _153_248 = (let _153_247 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (_153_247)::[])
in (_153_249)::_153_248))
in (_153_251)::_153_250))
in (_153_253)::_153_252))
in (r)::_153_254)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _153_255))
in (FStar_Syntax_Syntax.mk_Tm_app _153_257 _153_256 None FStar_Range.dummyRange)))
in (mk_repr b wp))
in (

let expected_k = (let _153_277 = (let _153_275 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_274 = (let _153_273 = (FStar_Syntax_Syntax.mk_binder b)
in (let _153_272 = (let _153_271 = (FStar_Syntax_Syntax.mk_binder wp_f)
in (let _153_270 = (let _153_269 = (let _153_259 = (let _153_258 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (mk_repr a _153_258))
in (FStar_Syntax_Syntax.null_binder _153_259))
in (let _153_268 = (let _153_267 = (FStar_Syntax_Syntax.mk_binder wp_g)
in (let _153_266 = (let _153_265 = (let _153_264 = (let _153_263 = (let _153_260 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_153_260)::[])
in (let _153_262 = (let _153_261 = (mk_repr b wp_g_x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _153_261))
in (FStar_Syntax_Util.arrow _153_263 _153_262)))
in (FStar_Syntax_Syntax.null_binder _153_264))
in (_153_265)::[])
in (_153_267)::_153_266))
in (_153_269)::_153_268))
in (_153_271)::_153_270))
in (_153_273)::_153_272))
in (_153_275)::_153_274))
in (let _153_276 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _153_277 _153_276)))
in (

let _59_275 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (_59_275) with
| (expected_k, _59_272, _59_274) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos)
in (

let env = (

let _59_277 = env
in {FStar_TypeChecker_Env.solver = _59_277.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_277.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_277.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_277.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_277.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_277.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_277.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_277.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_277.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_277.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_277.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_277.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_277.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_277.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_277.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_277.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_277.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_277.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _59_277.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_277.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_277.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_277.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_277.FStar_TypeChecker_Env.qname_and_index})
in (

let br = (check_and_gen' env ed.FStar_Syntax_Syntax.bind_repr expected_k)
in br)))
end)))))))))
end)))
in (

let return_repr = (

let x_a = (let _153_278 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _153_278))
in (

let res = (

let wp = (let _153_285 = (let _153_279 = (FStar_TypeChecker_Env.inst_tscheme return_wp)
in (FStar_All.pipe_right _153_279 Prims.snd))
in (let _153_284 = (let _153_283 = (let _153_282 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _153_281 = (let _153_280 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (_153_280)::[])
in (_153_282)::_153_281))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _153_283))
in (FStar_Syntax_Syntax.mk_Tm_app _153_285 _153_284 None FStar_Range.dummyRange)))
in (mk_repr a wp))
in (

let expected_k = (let _153_290 = (let _153_288 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_287 = (let _153_286 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_153_286)::[])
in (_153_288)::_153_287))
in (let _153_289 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _153_290 _153_289)))
in (

let _59_291 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (_59_291) with
| (expected_k, _59_288, _59_290) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos)
in (

let _59_295 = (check_and_gen' env ed.FStar_Syntax_Syntax.return_repr expected_k)
in (match (_59_295) with
| (univs, repr) -> begin
(match (univs) with
| [] -> begin
(([]), (repr))
end
| _59_298 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected universe-polymorphic return for effect"), (repr.FStar_Syntax_Syntax.pos)))))
end)
end)))
end)))))
in (

let actions = (

let check_action = (fun act -> (

let _59_306 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env act.FStar_Syntax_Syntax.action_typ)
in (match (_59_306) with
| (act_typ, _59_304, g_t) -> begin
(

let env' = (FStar_TypeChecker_Env.set_expected_typ env act_typ)
in (

let _59_308 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _153_294 = (FStar_Syntax_Print.term_to_string act.FStar_Syntax_Syntax.action_defn)
in (let _153_293 = (FStar_Syntax_Print.term_to_string act_typ)
in (FStar_Util.print3 "Checking action %s:\n[definition]: %s\n[cps\'d type]: %s\n" (FStar_Ident.text_of_lid act.FStar_Syntax_Syntax.action_name) _153_294 _153_293)))
end else begin
()
end
in (

let _59_314 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' act.FStar_Syntax_Syntax.action_defn)
in (match (_59_314) with
| (act_defn, _59_312, g_a) -> begin
(

let act_defn = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env act_defn)
in (

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
in (

let _59_337 = (

let act_typ = (FStar_Syntax_Subst.compress act_typ)
in (match (act_typ.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _59_325 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_59_325) with
| (bs, _59_324) -> begin
(

let res = (mk_repr' FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun)
in (

let k = (let _153_295 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs _153_295))
in (

let _59_332 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env k)
in (match (_59_332) with
| (k, _59_330, g) -> begin
((k), (g))
end))))
end))
end
| _59_334 -> begin
(let _153_300 = (let _153_299 = (let _153_298 = (let _153_297 = (FStar_Syntax_Print.term_to_string act_typ)
in (let _153_296 = (FStar_Syntax_Print.tag_of_term act_typ)
in (FStar_Util.format2 "Actions must have function types (not: %s, a.k.a. %s)" _153_297 _153_296)))
in ((_153_298), (act_defn.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_153_299))
in (Prims.raise _153_300))
end))
in (match (_59_337) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env act_typ expected_k)
in (

let _59_339 = (let _153_303 = (let _153_302 = (let _153_301 = (FStar_TypeChecker_Rel.conj_guard g_t g)
in (FStar_TypeChecker_Rel.conj_guard g_k _153_301))
in (FStar_TypeChecker_Rel.conj_guard g_a _153_302))
in (FStar_TypeChecker_Rel.force_trivial_guard env _153_303))
in (

let act_typ = (match ((let _153_304 = (FStar_Syntax_Subst.compress expected_k)
in _153_304.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _59_347 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_59_347) with
| (bs, c) -> begin
(

let _59_350 = (destruct_repr (FStar_Syntax_Util.comp_result c))
in (match (_59_350) with
| (a, wp) -> begin
(

let c = (let _153_308 = (let _153_305 = (env.FStar_TypeChecker_Env.universe_of env a)
in (_153_305)::[])
in (let _153_307 = (let _153_306 = (FStar_Syntax_Syntax.as_arg wp)
in (_153_306)::[])
in {FStar_Syntax_Syntax.comp_univs = _153_308; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a; FStar_Syntax_Syntax.effect_args = _153_307; FStar_Syntax_Syntax.flags = []}))
in (let _153_309 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Util.arrow bs _153_309)))
end))
end))
end
| _59_353 -> begin
(FStar_All.failwith "")
end)
in (

let _59_357 = (FStar_TypeChecker_Util.generalize_universes env act_defn)
in (match (_59_357) with
| (univs, act_defn) -> begin
(

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
in (

let _59_359 = act
in {FStar_Syntax_Syntax.action_name = _59_359.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = act_defn; FStar_Syntax_Syntax.action_typ = act_typ}))
end)))))
end))))
end))))
end)))
in (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.map check_action)))
in ((repr), (bind_repr), (return_repr), (actions)))))))))
end)
in (match (_59_366) with
| (repr, bind_repr, return_repr, actions) -> begin
(

let t = (let _153_310 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _153_310))
in (

let _59_370 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_59_370) with
| (univs, t) -> begin
(

let signature = (match ((let _153_312 = (let _153_311 = (FStar_Syntax_Subst.compress t)
in _153_311.FStar_Syntax_Syntax.n)
in ((effect_params), (_153_312)))) with
| ([], _59_373) -> begin
t
end
| (_59_376, FStar_Syntax_Syntax.Tm_arrow (_59_378, c)) -> begin
(FStar_Syntax_Util.comp_result c)
end
| _59_384 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let close = (fun n ts -> (

let ts = (let _153_317 = (FStar_Syntax_Subst.close_tscheme effect_params ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _153_317))
in (

let _59_390 = if (((n > (Prims.parse_int "0")) && (not ((FStar_Syntax_Util.is_unknown (Prims.snd ts))))) && ((FStar_List.length (Prims.fst ts)) <> n)) then begin
(let _153_320 = (let _153_319 = (FStar_Util.string_of_int n)
in (let _153_318 = (FStar_Syntax_Print.tscheme_to_string ts)
in (FStar_Util.format2 "The effect combinator is not universe-polymorphic enough (n=%s) (%s)" _153_319 _153_318)))
in (FStar_All.failwith _153_320))
end else begin
()
end
in ts)))
in (

let close_action = (fun act -> (

let _59_396 = (close (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_defn)))
in (match (_59_396) with
| (univs, defn) -> begin
(

let _59_399 = (close (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_typ)))
in (match (_59_399) with
| (univs', typ) -> begin
(

let _59_400 = ()
in (

let _59_402 = act
in {FStar_Syntax_Syntax.action_name = _59_402.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = defn; FStar_Syntax_Syntax.action_typ = typ}))
end))
end)))
in (

let _59_404 = ()
in (

let ed = (

let _59_406 = ed
in (let _153_337 = (close (Prims.parse_int "0") return_wp)
in (let _153_336 = (close (Prims.parse_int "1") bind_wp)
in (let _153_335 = (close (Prims.parse_int "0") if_then_else)
in (let _153_334 = (close (Prims.parse_int "0") ite_wp)
in (let _153_333 = (close (Prims.parse_int "0") stronger)
in (let _153_332 = (close (Prims.parse_int "1") close_wp)
in (let _153_331 = (close (Prims.parse_int "0") assert_p)
in (let _153_330 = (close (Prims.parse_int "0") assume_p)
in (let _153_329 = (close (Prims.parse_int "0") null_wp)
in (let _153_328 = (close (Prims.parse_int "0") trivial_wp)
in (let _153_327 = (let _153_323 = (close (Prims.parse_int "0") (([]), (repr)))
in (Prims.snd _153_323))
in (let _153_326 = (close (Prims.parse_int "0") return_repr)
in (let _153_325 = (close (Prims.parse_int "1") bind_repr)
in (let _153_324 = (FStar_List.map close_action actions)
in {FStar_Syntax_Syntax.qualifiers = _59_406.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _59_406.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _153_337; FStar_Syntax_Syntax.bind_wp = _153_336; FStar_Syntax_Syntax.if_then_else = _153_335; FStar_Syntax_Syntax.ite_wp = _153_334; FStar_Syntax_Syntax.stronger = _153_333; FStar_Syntax_Syntax.close_wp = _153_332; FStar_Syntax_Syntax.assert_p = _153_331; FStar_Syntax_Syntax.assume_p = _153_330; FStar_Syntax_Syntax.null_wp = _153_329; FStar_Syntax_Syntax.trivial = _153_328; FStar_Syntax_Syntax.repr = _153_327; FStar_Syntax_Syntax.return_repr = _153_326; FStar_Syntax_Syntax.bind_repr = _153_325; FStar_Syntax_Syntax.actions = _153_324})))))))))))))))
in (

let _59_409 = if ((FStar_TypeChecker_Env.debug env FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ED")))) then begin
(let _153_338 = (FStar_Syntax_Print.eff_decl_to_string false ed)
in (FStar_Util.print_string _153_338))
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

let _59_415 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_59_415) with
| (effect_binders_un, signature_un) -> begin
(

let _59_420 = (tc_tparams env effect_binders_un)
in (match (_59_420) with
| (effect_binders, env, _59_419) -> begin
(

let _59_424 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (_59_424) with
| (signature, _59_423) -> begin
(

let effect_binders = (FStar_List.map (fun _59_427 -> (match (_59_427) with
| (bv, qual) -> begin
(let _153_343 = (

let _59_428 = bv
in (let _153_342 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _59_428.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_428.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _153_342}))
in ((_153_343), (qual)))
end)) effect_binders)
in (

let _59_443 = (match ((let _153_344 = (FStar_Syntax_Subst.compress signature_un)
in _153_344.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (((a, _59_433))::[], effect_marker) -> begin
((a), (effect_marker))
end
| _59_440 -> begin
(FStar_All.failwith "bad shape for effect-for-free signature")
end)
in (match (_59_443) with
| (a, effect_marker) -> begin
(

let open_and_check = (fun t -> (

let subst = (FStar_Syntax_Subst.opening_of_binders effect_binders)
in (

let t = (FStar_Syntax_Subst.subst subst t)
in (

let _59_452 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (_59_452) with
| (t, comp, _59_451) -> begin
((t), (comp))
end)))))
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None signature.FStar_Syntax_Syntax.pos))
in (

let _59_457 = (open_and_check ed.FStar_Syntax_Syntax.repr)
in (match (_59_457) with
| (repr, _comp) -> begin
(

let _59_458 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _153_349 = (FStar_Syntax_Print.term_to_string repr)
in (FStar_Util.print1 "Representation is: %s\n" _153_349))
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

let wp_a = (let _153_356 = (let _153_355 = (let _153_354 = (let _153_353 = (let _153_352 = (let _153_351 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _153_350 = (FStar_Syntax_Syntax.as_implicit false)
in ((_153_351), (_153_350))))
in (_153_352)::[])
in ((wp_type), (_153_353)))
in FStar_Syntax_Syntax.Tm_app (_153_354))
in (mk _153_355))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _153_356))
in (

let effect_signature = (

let binders = (let _153_361 = (let _153_357 = (FStar_Syntax_Syntax.as_implicit false)
in ((a), (_153_357)))
in (let _153_360 = (let _153_359 = (let _153_358 = (FStar_Syntax_Syntax.gen_bv "dijkstra_wp" None wp_a)
in (FStar_All.pipe_right _153_358 FStar_Syntax_Syntax.mk_binder))
in (_153_359)::[])
in (_153_361)::_153_360))
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

let _59_476 = item
in (match (_59_476) with
| (u_item, item) -> begin
(

let _59_479 = (open_and_check item)
in (match (_59_479) with
| (item, item_comp) -> begin
(

let _59_480 = if (not ((FStar_Syntax_Util.is_total_lcomp item_comp))) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Computation for [item] is not total!")))
end else begin
()
end
in (

let _59_485 = (FStar_TypeChecker_DMFF.star_expr dmff_env item)
in (match (_59_485) with
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

let _59_493 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.bind_repr)
in (match (_59_493) with
| (dmff_env, _59_490, bind_wp, bind_elab) -> begin
(

let _59_499 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.return_repr)
in (match (_59_499) with
| (dmff_env, _59_496, return_wp, return_elab) -> begin
(

let return_wp = (match ((let _153_368 = (FStar_Syntax_Subst.compress return_wp)
in _153_368.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(let _153_369 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs ((b1)::(b2)::[]) _153_369 (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_GTot_lid)))))
end
| _59_510 -> begin
(FStar_All.failwith "unexpected shape for return")
end)
in (

let bind_wp = (match ((let _153_370 = (FStar_Syntax_Subst.compress bind_wp)
in _153_370.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let r = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_lid (FStar_Syntax_Syntax.Delta_unfoldable ((Prims.parse_int "1"))) None)
in (let _153_374 = (let _153_373 = (let _153_372 = (let _153_371 = (mk (FStar_Syntax_Syntax.Tm_fvar (r)))
in (FStar_Syntax_Syntax.null_binder _153_371))
in (_153_372)::[])
in (FStar_List.append _153_373 binders))
in (FStar_Syntax_Util.abs _153_374 body what)))
end
| _59_519 -> begin
(FStar_All.failwith "unexpected shape for bind")
end)
in (

let apply_close = (fun t -> if ((FStar_List.length effect_binders) = (Prims.parse_int "0")) then begin
t
end else begin
(let _153_381 = (let _153_380 = (let _153_379 = (let _153_378 = (let _153_377 = (FStar_Syntax_Util.args_of_binders effect_binders)
in (Prims.snd _153_377))
in ((t), (_153_378)))
in FStar_Syntax_Syntax.Tm_app (_153_379))
in (mk _153_380))
in (FStar_Syntax_Subst.close effect_binders _153_381))
end)
in (

let register = (fun name item -> (

let _59_528 = (let _153_387 = (mk_lid name)
in (let _153_386 = (FStar_Syntax_Util.abs effect_binders item None)
in (FStar_TypeChecker_Util.mk_toplevel_definition env _153_387 _153_386)))
in (match (_59_528) with
| (sigelt, fv) -> begin
(

let _59_529 = (let _153_389 = (let _153_388 = (FStar_ST.read sigelts)
in (sigelt)::_153_388)
in (FStar_ST.op_Colon_Equals sigelts _153_389))
in fv)
end)))
in (

let return_wp = (register "return_wp" return_wp)
in (

let return_elab = (register "return_elab" return_elab)
in (

let bind_wp = (register "bind_wp" bind_wp)
in (

let _59_534 = (let _153_391 = (let _153_390 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true")), (FStar_Range.dummyRange))))::_153_390)
in (FStar_ST.op_Colon_Equals sigelts _153_391))
in (

let bind_elab = (register "bind_elab" bind_elab)
in (

let _59_537 = (let _153_393 = (let _153_392 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false")), (FStar_Range.dummyRange))))::_153_392)
in (FStar_ST.op_Colon_Equals sigelts _153_393))
in (

let _59_556 = (FStar_List.fold_left (fun _59_541 action -> (match (_59_541) with
| (dmff_env, actions) -> begin
(

let _59_547 = (elaborate_and_star dmff_env ((action.FStar_Syntax_Syntax.action_univs), (action.FStar_Syntax_Syntax.action_defn)))
in (match (_59_547) with
| (dmff_env, action_t, action_wp, action_elab) -> begin
(

let name = action.FStar_Syntax_Syntax.action_name.FStar_Ident.ident.FStar_Ident.idText
in (

let action_typ_with_wp = (FStar_TypeChecker_DMFF.trans_F dmff_env action_t action_wp)
in (

let action_elab = (register (Prims.strcat name "_elab") action_elab)
in (

let action_typ_with_wp = (register (Prims.strcat name "_complete_type") action_typ_with_wp)
in (let _153_399 = (let _153_398 = (

let _59_552 = action
in (let _153_397 = (apply_close action_elab)
in (let _153_396 = (apply_close action_typ_with_wp)
in {FStar_Syntax_Syntax.action_name = _59_552.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = _59_552.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _153_397; FStar_Syntax_Syntax.action_typ = _153_396})))
in (_153_398)::actions)
in ((dmff_env), (_153_399)))))))
end))
end)) ((dmff_env), ([])) ed.FStar_Syntax_Syntax.actions)
in (match (_59_556) with
| (dmff_env, actions) -> begin
(

let actions = (FStar_List.rev actions)
in (

let repr = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp_a" None wp_a)
in (

let binders = (let _153_402 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_401 = (let _153_400 = (FStar_Syntax_Syntax.mk_binder wp)
in (_153_400)::[])
in (_153_402)::_153_401))
in (let _153_411 = (let _153_410 = (let _153_408 = (let _153_407 = (let _153_406 = (let _153_405 = (let _153_404 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _153_403 = (FStar_Syntax_Syntax.as_implicit false)
in ((_153_404), (_153_403))))
in (_153_405)::[])
in ((repr), (_153_406)))
in FStar_Syntax_Syntax.Tm_app (_153_407))
in (mk _153_408))
in (let _153_409 = (FStar_Syntax_Syntax.bv_to_name wp)
in (FStar_TypeChecker_DMFF.trans_F dmff_env _153_410 _153_409)))
in (FStar_Syntax_Util.abs binders _153_411 None))))
in (

let repr = (recheck_debug "FC" env repr)
in (

let repr = (register "repr" repr)
in (

let _59_588 = (match ((let _153_412 = (FStar_Syntax_Subst.compress wp_type)
in _153_412.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (effect_param, arrow, _59_566) -> begin
(

let _59_571 = (FStar_Syntax_Subst.open_term effect_param arrow)
in (match (_59_571) with
| (effect_param, arrow) -> begin
(match ((let _153_413 = (FStar_Syntax_Subst.compress arrow)
in _153_413.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (wp_binders, c) -> begin
(

let _59_578 = (FStar_Syntax_Subst.open_comp wp_binders c)
in (match (_59_578) with
| (wp_binders, c) -> begin
(

let _59_581 = (FStar_Util.prefix wp_binders)
in (match (_59_581) with
| (pre_args, post) -> begin
(let _153_415 = (FStar_Syntax_Util.arrow pre_args c)
in (let _153_414 = (FStar_Syntax_Util.abs effect_param (Prims.fst post).FStar_Syntax_Syntax.sort None)
in ((_153_415), (_153_414))))
end))
end))
end
| _59_583 -> begin
(let _153_417 = (let _153_416 = (FStar_Syntax_Print.term_to_string arrow)
in (FStar_Util.format1 "Impossible: pre/post arrow %s" _153_416))
in (FStar_All.failwith _153_417))
end)
end))
end
| _59_585 -> begin
(let _153_419 = (let _153_418 = (FStar_Syntax_Print.term_to_string wp_type)
in (FStar_Util.format1 "Impossible: pre/post abs %s" _153_418))
in (FStar_All.failwith _153_419))
end)
in (match (_59_588) with
| (pre, post) -> begin
(

let _59_589 = (let _153_420 = (register "pre" pre)
in (Prims.ignore _153_420))
in (

let _59_591 = (let _153_421 = (register "post" post)
in (Prims.ignore _153_421))
in (

let _59_593 = (let _153_422 = (register "wp" wp_type)
in (Prims.ignore _153_422))
in (

let ed = (

let _59_595 = ed
in (let _153_433 = (FStar_Syntax_Subst.close_binders effect_binders)
in (let _153_432 = (FStar_Syntax_Subst.close effect_binders effect_signature)
in (let _153_431 = (let _153_423 = (apply_close return_wp)
in (([]), (_153_423)))
in (let _153_430 = (let _153_424 = (apply_close bind_wp)
in (([]), (_153_424)))
in (let _153_429 = (apply_close repr)
in (let _153_428 = (let _153_425 = (apply_close return_elab)
in (([]), (_153_425)))
in (let _153_427 = (let _153_426 = (apply_close bind_elab)
in (([]), (_153_426)))
in {FStar_Syntax_Syntax.qualifiers = _59_595.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _59_595.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _59_595.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _153_433; FStar_Syntax_Syntax.signature = _153_432; FStar_Syntax_Syntax.ret_wp = _153_431; FStar_Syntax_Syntax.bind_wp = _153_430; FStar_Syntax_Syntax.if_then_else = _59_595.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _59_595.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _59_595.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _59_595.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _59_595.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _59_595.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _59_595.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _59_595.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _153_429; FStar_Syntax_Syntax.return_repr = _153_428; FStar_Syntax_Syntax.bind_repr = _153_427; FStar_Syntax_Syntax.actions = actions}))))))))
in (

let _59_600 = (FStar_TypeChecker_DMFF.gen_wps_for_free env effect_binders a wp_a ed)
in (match (_59_600) with
| (sigelts', ed) -> begin
(

let _59_601 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _153_434 = (FStar_Syntax_Print.eff_decl_to_string true ed)
in (FStar_Util.print_string _153_434))
end else begin
()
end
in (let _153_437 = (let _153_436 = (let _153_435 = (FStar_ST.read sigelts)
in (FStar_List.rev _153_435))
in (FStar_List.append _153_436 sigelts'))
in ((_153_437), (ed))))
end))))))
end))))))
end))))))))))))
end))
end))))))))))))
end))))
end)))
end))
end))
end)))
and tc_lex_t : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (

let _59_607 = ()
in (

let _59_615 = ()
in (match (ses) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _59_644, _59_646, [], r))::(FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, _153_442, [], _59_635, r1))::(FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, _153_443, [], _59_624, r2))::[] when (((_153_442 = (Prims.parse_int "0")) && (_153_443 = (Prims.parse_int "0"))) && (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid))) -> begin
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

let lex_top_t = (let _153_447 = (let _153_446 = (let _153_445 = (let _153_444 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _153_444 FStar_Syntax_Syntax.Delta_constant None))
in ((_153_445), ((FStar_Syntax_Syntax.U_name (utop))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_153_446))
in (FStar_Syntax_Syntax.mk _153_447 None r1))
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

let a = (let _153_448 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _153_448))
in (

let hd = (let _153_449 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _153_449))
in (

let tl = (let _153_454 = (let _153_453 = (let _153_452 = (let _153_451 = (let _153_450 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _153_450 FStar_Syntax_Syntax.Delta_constant None))
in ((_153_451), ((FStar_Syntax_Syntax.U_name (ucons2))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_153_452))
in (FStar_Syntax_Syntax.mk _153_453 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _153_454))
in (

let res = (let _153_458 = (let _153_457 = (let _153_456 = (let _153_455 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _153_455 FStar_Syntax_Syntax.Delta_constant None))
in ((_153_456), ((FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_153_457))
in (FStar_Syntax_Syntax.mk _153_458 None r2))
in (let _153_459 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow ((((a), (Some (FStar_Syntax_Syntax.imp_tag))))::(((hd), (None)))::(((tl), (None)))::[]) _153_459))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon (((lex_cons), ((ucons1)::(ucons2)::[]), (lex_cons_t), (FStar_Syntax_Const.lex_t_lid), ((Prims.parse_int "0")), ([]), ([]), (r2)))
in (let _153_461 = (let _153_460 = (FStar_TypeChecker_Env.get_range env)
in (((tc)::(dc_lextop)::(dc_lexcons)::[]), ([]), (lids), (_153_460)))
in FStar_Syntax_Syntax.Sig_bundle (_153_461)))))))))))))))
end
| _59_670 -> begin
(let _153_463 = (let _153_462 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle (((ses), ([]), (lids), (FStar_Range.dummyRange)))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _153_462))
in (FStar_All.failwith _153_463))
end))))
and tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _59_680 = (FStar_Syntax_Util.type_u ())
in (match (_59_680) with
| (k, _59_679) -> begin
(

let phi = (let _153_469 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _153_469 (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]) env)))
in (

let _59_682 = (FStar_TypeChecker_Util.check_uvars r phi)
in FStar_Syntax_Syntax.Sig_assume (((lid), (phi), (quals), (r)))))
end))))
and tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun env ses quals lids -> (

let warn_positivity = (fun l r -> (let _153_479 = (let _153_478 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _153_478))
in (FStar_TypeChecker_Errors.diag r _153_479)))
in (

let env0 = env
in (

let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(

let _59_705 = ()
in (

let _59_707 = (warn_positivity tc r)
in (

let _59_711 = (FStar_Syntax_Subst.open_term tps k)
in (match (_59_711) with
| (tps, k) -> begin
(

let _59_716 = (FStar_TypeChecker_TcTerm.tc_binders env tps)
in (match (_59_716) with
| (tps, env_tps, guard_params, us) -> begin
(

let _59_719 = (FStar_Syntax_Util.arrow_formals k)
in (match (_59_719) with
| (indices, t) -> begin
(

let _59_724 = (FStar_TypeChecker_TcTerm.tc_binders env_tps indices)
in (match (_59_724) with
| (indices, env', guard_indices, us') -> begin
(

let _59_732 = (

let _59_729 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' t)
in (match (_59_729) with
| (t, _59_727, g) -> begin
(let _153_486 = (let _153_485 = (let _153_484 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params _153_484))
in (FStar_TypeChecker_Rel.discharge_guard env' _153_485))
in ((t), (_153_486)))
end))
in (match (_59_732) with
| (t, guard) -> begin
(

let k = (let _153_487 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _153_487))
in (

let _59_736 = (FStar_Syntax_Util.type_u ())
in (match (_59_736) with
| (t_type, u) -> begin
(

let _59_737 = (let _153_488 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _153_488))
in (

let t_tc = (let _153_489 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _153_489))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _153_490 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) (([]), (t_tc)))
in ((_153_490), (FStar_Syntax_Syntax.Sig_inductive_typ (((tc), ([]), (tps), (k), (mutuals), (data), (quals), (r)))), (u), (guard))))))))
end)))
end))
end))
end))
end))
end))))
end
| _59_744 -> begin
(FStar_All.failwith "impossible")
end))
in (

let positive_if_pure = (fun _59_746 l -> ())
in (

let tc_data = (fun env tcs _59_1 -> (match (_59_1) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let _59_763 = ()
in (

let _59_798 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun _59_767 -> (match (_59_767) with
| (se, u_tc) -> begin
if (let _153_503 = (let _153_502 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _153_502))
in (FStar_Ident.lid_equals tc_lid _153_503)) then begin
(

let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_59_769, _59_771, tps, _59_774, _59_776, _59_778, _59_780, _59_782) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _59_788 -> (match (_59_788) with
| (x, _59_787) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
end
| _59_790 -> begin
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
in (match (_59_798) with
| (tps, u_tc) -> begin
(

let _59_818 = (match ((let _153_505 = (FStar_Syntax_Subst.compress t)
in _153_505.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let _59_806 = (FStar_Util.first_N ntps bs)
in (match (_59_806) with
| (_59_804, bs') -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs'), (res)))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _59_812 -> (match (_59_812) with
| (x, _59_811) -> begin
FStar_Syntax_Syntax.DB ((((ntps - ((Prims.parse_int "1") + i))), (x)))
end))))
in (let _153_508 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _153_508))))
end))
end
| _59_815 -> begin
(([]), (t))
end)
in (match (_59_818) with
| (arguments, result) -> begin
(

let _59_819 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_511 = (FStar_Syntax_Print.lid_to_string c)
in (let _153_510 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _153_509 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _153_511 _153_510 _153_509))))
end else begin
()
end
in (

let _59_824 = (tc_tparams env arguments)
in (match (_59_824) with
| (arguments, env', us) -> begin
(

let _59_828 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env' result)
in (match (_59_828) with
| (result, _59_827) -> begin
(

let _59_832 = (FStar_Syntax_Util.head_and_args result)
in (match (_59_832) with
| (head, _59_831) -> begin
(

let _59_837 = (match ((let _153_512 = (FStar_Syntax_Subst.compress head)
in _153_512.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _59_836 -> begin
(let _153_517 = (let _153_516 = (let _153_515 = (let _153_514 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (let _153_513 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" _153_514 _153_513)))
in ((_153_515), (r)))
in FStar_Syntax_Syntax.Error (_153_516))
in (Prims.raise _153_517))
end)
in (

let g = (FStar_List.fold_left2 (fun g _59_843 u_x -> (match (_59_843) with
| (x, _59_842) -> begin
(

let _59_845 = ()
in (let _153_521 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _153_521)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _153_525 = (let _153_523 = (FStar_All.pipe_right tps (FStar_List.map (fun _59_851 -> (match (_59_851) with
| (x, _59_850) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append _153_523 arguments))
in (let _153_524 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _153_525 _153_524)))
in ((FStar_Syntax_Syntax.Sig_datacon (((c), ([]), (t), (tc_lid), (ntps), (quals), ([]), (r)))), (g)))))
end))
end))
end)))
end))
end)))
end
| _59_854 -> begin
(FStar_All.failwith "impossible")
end))
in (

let generalize_and_inst_within = (fun env g tcs datas -> (

let _59_860 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _59_2 -> (match (_59_2) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_59_864, _59_866, tps, k, _59_870, _59_872, _59_874, _59_876) -> begin
(let _153_536 = (let _153_535 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _153_535))
in (FStar_Syntax_Syntax.null_binder _153_536))
end
| _59_880 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _59_3 -> (match (_59_3) with
| FStar_Syntax_Syntax.Sig_datacon (_59_884, _59_886, t, _59_889, _59_891, _59_893, _59_895, _59_897) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _59_901 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let t = (let _153_538 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _153_538))
in (

let _59_904 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_539 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _153_539))
end else begin
()
end
in (

let _59_908 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_59_908) with
| (uvs, t) -> begin
(

let _59_910 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_543 = (let _153_541 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _153_541 (FStar_String.concat ", ")))
in (let _153_542 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _153_543 _153_542)))
end else begin
()
end
in (

let _59_914 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_59_914) with
| (uvs, t) -> begin
(

let _59_918 = (FStar_Syntax_Util.arrow_formals t)
in (match (_59_918) with
| (args, _59_917) -> begin
(

let _59_921 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_59_921) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun _59_925 se -> (match (_59_925) with
| (x, _59_924) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _59_929, tps, _59_932, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let _59_955 = (match ((let _153_546 = (FStar_Syntax_Subst.compress ty)
in _153_546.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _59_946 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_59_946) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _59_949 -> begin
(let _153_547 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) _153_547 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in ((tps), (t)))
end))
end
| _59_952 -> begin
(([]), (ty))
end)
in (match (_59_955) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs), (tps), (t), (mutuals), (datas), (quals), (r)))
end)))
end
| _59_957 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| _59_961 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _153_548 -> FStar_Syntax_Syntax.U_name (_153_548))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _59_4 -> (match (_59_4) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _59_966, _59_968, _59_970, _59_972, _59_974, _59_976, _59_978) -> begin
((tc), (uvs_universes))
end
| _59_982 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _59_987 d -> (match (_59_987) with
| (t, _59_986) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _59_991, _59_993, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (let _153_552 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _153_552 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon (((l), (uvs), (ty), (tc), (ntps), (quals), (mutuals), (r))))
end
| _59_1003 -> begin
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

let _59_1013 = (FStar_All.pipe_right ses (FStar_List.partition (fun _59_5 -> (match (_59_5) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_59_1007) -> begin
true
end
| _59_1010 -> begin
false
end))))
in (match (_59_1013) with
| (tys, datas) -> begin
(

let _59_1020 = if (FStar_All.pipe_right datas (FStar_Util.for_some (fun _59_6 -> (match (_59_6) with
| FStar_Syntax_Syntax.Sig_datacon (_59_1016) -> begin
false
end
| _59_1019 -> begin
true
end)))) then begin
(let _153_557 = (let _153_556 = (let _153_555 = (FStar_TypeChecker_Env.get_range env)
in (("Mutually defined type contains a non-inductive element"), (_153_555)))
in FStar_Syntax_Syntax.Error (_153_556))
in (Prims.raise _153_557))
end else begin
()
end
in (

let env0 = env
in (

let _59_1039 = (FStar_List.fold_right (fun tc _59_1027 -> (match (_59_1027) with
| (env, all_tcs, g) -> begin
(

let _59_1032 = (tc_tycon env tc)
in (match (_59_1032) with
| (env, tc, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (

let _59_1034 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_560 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _153_560))
end else begin
()
end
in (let _153_562 = (let _153_561 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g _153_561))
in ((env), ((((tc), (tc_u)))::all_tcs), (_153_562)))))
end))
end)) tys ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (_59_1039) with
| (env, tcs, g) -> begin
(

let _59_1049 = (FStar_List.fold_right (fun se _59_1043 -> (match (_59_1043) with
| (datas, g) -> begin
(

let _59_1046 = (tc_data env tcs se)
in (match (_59_1046) with
| (data, g') -> begin
(let _153_565 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((data)::datas), (_153_565)))
end))
end)) datas (([]), (g)))
in (match (_59_1049) with
| (datas, g) -> begin
(

let _59_1052 = (let _153_566 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _153_566 datas))
in (match (_59_1052) with
| (tcs, datas) -> begin
(

let sig_bndle = (let _153_568 = (let _153_567 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_153_567)))
in FStar_Syntax_Syntax.Sig_bundle (_153_568))
in (

let datacon_typ = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (_59_1057, _59_1059, t, _59_1062, _59_1064, _59_1066, _59_1068, _59_1070) -> begin
t
end
| _59_1074 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let dr = FStar_Range.dummyRange
in (

let optimized_haseq_scheme = (fun _59_1077 -> (

let haseq_ty = (fun usubst us acc ty -> (

let _59_1104 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _59_1086, bs, t, _59_1090, d_lids, _59_1093, _59_1095) -> begin
((lid), (bs), (t), (d_lids))
end
| _59_1099 -> begin
(FStar_All.failwith "Impossible!")
end)
in (match (_59_1104) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _153_581 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _153_581 t))
in (

let _59_1109 = (FStar_Syntax_Subst.open_term bs t)
in (match (_59_1109) with
| (bs, t) -> begin
(

let ibs = (match ((let _153_582 = (FStar_Syntax_Subst.compress t)
in _153_582.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _59_1112) -> begin
ibs
end
| _59_1116 -> begin
[]
end)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _153_585 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _153_584 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _153_585 _153_584)))
in (

let ind = (let _153_588 = (FStar_List.map (fun _59_1123 -> (match (_59_1123) with
| (bv, aq) -> begin
(let _153_587 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_153_587), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _153_588 None dr))
in (

let ind = (let _153_591 = (FStar_List.map (fun _59_1127 -> (match (_59_1127) with
| (bv, aq) -> begin
(let _153_590 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_153_590), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _153_591 None dr))
in (

let haseq_ind = (let _153_593 = (let _153_592 = (FStar_Syntax_Syntax.as_arg ind)
in (_153_592)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _153_593 None dr))
in (

let bs' = (FStar_List.filter (fun b -> (

let _59_1138 = acc
in (match (_59_1138) with
| (_59_1132, en, _59_1135, _59_1137) -> begin
(

let opt = (let _153_596 = (let _153_595 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _153_595))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort _153_596 false))
in (match (opt) with
| None -> begin
false
end
| Some (_59_1142) -> begin
true
end))
end))) bs)
in (

let haseq_bs = (FStar_List.fold_left (fun t b -> (let _153_602 = (let _153_601 = (let _153_600 = (let _153_599 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b))
in (FStar_Syntax_Syntax.as_arg _153_599))
in (_153_600)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _153_601 None dr))
in (FStar_Syntax_Util.mk_conj t _153_602))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml = (

let _59_1149 = fml
in (let _153_608 = (let _153_607 = (let _153_606 = (let _153_605 = (let _153_604 = (let _153_603 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_153_603)::[])
in (_153_604)::[])
in FStar_Syntax_Syntax.Meta_pattern (_153_605))
in ((fml), (_153_606)))
in FStar_Syntax_Syntax.Tm_meta (_153_607))
in {FStar_Syntax_Syntax.n = _153_608; FStar_Syntax_Syntax.tk = _59_1149.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _59_1149.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _59_1149.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _153_614 = (let _153_613 = (let _153_612 = (let _153_611 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _153_611 None))
in (FStar_Syntax_Syntax.as_arg _153_612))
in (_153_613)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _153_614 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _153_620 = (let _153_619 = (let _153_618 = (let _153_617 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _153_617 None))
in (FStar_Syntax_Syntax.as_arg _153_618))
in (_153_619)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _153_620 None dr))) bs fml)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let _59_1163 = acc
in (match (_59_1163) with
| (l_axioms, env, guard', cond') -> begin
(

let env = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env = (FStar_TypeChecker_Env.push_binders env ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (_59_1168, _59_1170, _59_1172, t_lid, _59_1175, _59_1177, _59_1179, _59_1181) -> begin
(t_lid = lid)
end
| _59_1185 -> begin
(FStar_All.failwith "Impossible")
end)) datas)
in (

let haseq_data = (fun data -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (match ((let _153_624 = (FStar_Syntax_Subst.compress dt)
in _153_624.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _59_1193) -> begin
(

let dbs = (let _153_625 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _153_625))
in (

let dbs = (let _153_626 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _153_626 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let haseq_b = (let _153_630 = (let _153_629 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_153_629)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _153_630 None dr))
in (

let sort_range = (Prims.fst b).FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos
in (

let haseq_b = (let _153_632 = (let _153_631 = (FStar_Syntax_Print.term_to_string ind)
in (FStar_Util.format1 "Failed to prove that the type \'%s\' supports decidable equality because of this argument; add the \'noeq\' qualifier" _153_631))
in (FStar_TypeChecker_Util.label _153_632 sort_range haseq_b))
in (FStar_Syntax_Util.mk_conj t haseq_b))))) FStar_Syntax_Util.t_true dbs)
in (FStar_List.fold_right (fun b t -> (let _153_638 = (let _153_637 = (let _153_636 = (let _153_635 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _153_635 None))
in (FStar_Syntax_Syntax.as_arg _153_636))
in (_153_637)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _153_638 None dr))) dbs cond)))))
end
| _59_1208 -> begin
FStar_Syntax_Util.t_true
end))))
in (

let cond = (FStar_List.fold_left (fun acc d -> (let _153_641 = (haseq_data d)
in (FStar_Syntax_Util.mk_conj acc _153_641))) FStar_Syntax_Util.t_true t_datas)
in (

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (let _153_643 = (FStar_Syntax_Util.mk_conj guard' guard)
in (let _153_642 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml)))::[]))), (env), (_153_643), (_153_642))))))))))
end)))))))))))))))
end))))
end)))
in (

let us = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_59_1215, us, _59_1218, _59_1220, _59_1222, _59_1224, _59_1226, _59_1228) -> begin
us
end
| _59_1232 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let _59_1236 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (_59_1236) with
| (usubst, us) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (

let _59_1238 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq")
in (

let _59_1240 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle)
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let _59_1247 = (FStar_List.fold_left (haseq_ty usubst us) (([]), (env), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (_59_1247) with
| (axioms, env, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let _59_1252 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env phi)
in (match (_59_1252) with
| (phi, _59_1251) -> begin
(

let _59_1253 = if (FStar_TypeChecker_Env.should_verify env) then begin
(let _153_644 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi)))
in (FStar_TypeChecker_Rel.force_trivial_guard env _153_644))
end else begin
()
end
in (

let ses = (FStar_List.fold_left (fun l _59_1258 -> (match (_59_1258) with
| (lid, fml) -> begin
(

let se = (tc_assume env lid fml [] dr)
in (FStar_List.append l ((se)::[])))
end)) [] axioms)
in (

let _59_1261 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq")
in ses)))
end)))
end))))))
end)))))
in (

let unoptimized_haseq_scheme = (fun _59_1264 -> (

let mutuals = (FStar_List.map (fun ty -> (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _59_1269, _59_1271, _59_1273, _59_1275, _59_1277, _59_1279, _59_1281) -> begin
lid
end
| _59_1285 -> begin
(FStar_All.failwith "Impossible!")
end)) tcs)
in (

let haseq_ty = (fun usubst us acc ty -> (

let _59_1312 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _59_1294, bs, t, _59_1298, d_lids, _59_1301, _59_1303) -> begin
((lid), (bs), (t), (d_lids))
end
| _59_1307 -> begin
(FStar_All.failwith "Impossible!")
end)
in (match (_59_1312) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _153_658 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _153_658 t))
in (

let _59_1317 = (FStar_Syntax_Subst.open_term bs t)
in (match (_59_1317) with
| (bs, t) -> begin
(

let ibs = (match ((let _153_659 = (FStar_Syntax_Subst.compress t)
in _153_659.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _59_1320) -> begin
ibs
end
| _59_1324 -> begin
[]
end)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _153_662 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _153_661 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _153_662 _153_661)))
in (

let ind = (let _153_665 = (FStar_List.map (fun _59_1331 -> (match (_59_1331) with
| (bv, aq) -> begin
(let _153_664 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_153_664), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _153_665 None dr))
in (

let ind = (let _153_668 = (FStar_List.map (fun _59_1335 -> (match (_59_1335) with
| (bv, aq) -> begin
(let _153_667 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_153_667), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _153_668 None dr))
in (

let haseq_ind = (let _153_670 = (let _153_669 = (FStar_Syntax_Syntax.as_arg ind)
in (_153_669)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _153_670 None dr))
in (

let rec is_mutual = (fun t -> (match ((let _153_674 = (FStar_Syntax_Subst.compress t)
in _153_674.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.existsb (fun lid -> (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) mutuals)
end
| FStar_Syntax_Syntax.Tm_uinst (t', _59_1346) -> begin
(is_mutual t')
end
| FStar_Syntax_Syntax.Tm_refine (bv, t') -> begin
(is_mutual bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_app (t', args) -> begin
if (is_mutual t') then begin
true
end else begin
(let _153_676 = (FStar_List.map Prims.fst args)
in (exists_mutual _153_676))
end
end
| FStar_Syntax_Syntax.Tm_meta (t', _59_1359) -> begin
(is_mutual t')
end
| _59_1363 -> begin
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
in (match ((let _153_682 = (FStar_Syntax_Subst.compress dt)
in _153_682.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _59_1376) -> begin
(

let dbs = (let _153_683 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _153_683))
in (

let dbs = (let _153_684 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _153_684 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let sort = (Prims.fst b).FStar_Syntax_Syntax.sort
in (

let haseq_sort = (let _153_688 = (let _153_687 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_153_687)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _153_688 None dr))
in (

let haseq_sort = if (is_mutual sort) then begin
(FStar_Syntax_Util.mk_imp haseq_ind haseq_sort)
end else begin
haseq_sort
end
in (FStar_Syntax_Util.mk_conj t haseq_sort))))) FStar_Syntax_Util.t_true dbs)
in (

let cond = (FStar_List.fold_right (fun b t -> (let _153_694 = (let _153_693 = (let _153_692 = (let _153_691 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _153_691 None))
in (FStar_Syntax_Syntax.as_arg _153_692))
in (_153_693)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _153_694 None dr))) dbs cond)
in (FStar_Syntax_Util.mk_conj acc cond))))))
end
| _59_1392 -> begin
acc
end))))
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (_59_1395, _59_1397, _59_1399, t_lid, _59_1402, _59_1404, _59_1406, _59_1408) -> begin
(t_lid = lid)
end
| _59_1412 -> begin
(FStar_All.failwith "Impossible")
end)) datas)
in (

let data_cond = (FStar_List.fold_left haseq_data FStar_Syntax_Util.t_true t_datas)
in (

let fml = (FStar_Syntax_Util.mk_imp data_cond haseq_ind)
in (

let fml = (

let _59_1416 = fml
in (let _153_701 = (let _153_700 = (let _153_699 = (let _153_698 = (let _153_697 = (let _153_696 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_153_696)::[])
in (_153_697)::[])
in FStar_Syntax_Syntax.Meta_pattern (_153_698))
in ((fml), (_153_699)))
in FStar_Syntax_Syntax.Tm_meta (_153_700))
in {FStar_Syntax_Syntax.n = _153_701; FStar_Syntax_Syntax.tk = _59_1416.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _59_1416.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _59_1416.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _153_707 = (let _153_706 = (let _153_705 = (let _153_704 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _153_704 None))
in (FStar_Syntax_Syntax.as_arg _153_705))
in (_153_706)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _153_707 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _153_713 = (let _153_712 = (let _153_711 = (let _153_710 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _153_710 None))
in (FStar_Syntax_Syntax.as_arg _153_711))
in (_153_712)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _153_713 None dr))) bs fml)
in (FStar_Syntax_Util.mk_conj acc fml)))))))))))))))
end))))
end)))
in (

let _59_1446 = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, _59_1429, _59_1431, _59_1433, _59_1435, _59_1437, _59_1439) -> begin
((lid), (us))
end
| _59_1443 -> begin
(FStar_All.failwith "Impossible!")
end))
in (match (_59_1446) with
| (lid, us) -> begin
(

let _59_1449 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (_59_1449) with
| (usubst, us) -> begin
(

let fml = (FStar_List.fold_left (haseq_ty usubst us) FStar_Syntax_Util.t_true tcs)
in (

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (

let _59_1452 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq")
in (

let _59_1454 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle)
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let se = (let _153_714 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (tc_assume env _153_714 fml [] dr))
in (

let _59_1458 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq")
in (se)::[])))))))
end))
end)))))
in (

let skip_prims_type = (fun _59_1461 -> (

let lid = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _59_1466, _59_1468, _59_1470, _59_1472, _59_1474, _59_1476, _59_1478) -> begin
lid
end
| _59_1482 -> begin
(FStar_All.failwith "Impossible")
end))
in (

let types_to_skip = ("c_False")::("c_True")::("equals")::("h_equals")::("c_and")::("c_or")::[]
in (FStar_List.existsb (fun s -> (s = lid.FStar_Ident.ident.FStar_Ident.idText)) types_to_skip))))
in (

let is_noeq = (FStar_List.existsb (fun q -> (q = FStar_Syntax_Syntax.Noeq)) quals)
in if ((((FStar_List.length tcs) = (Prims.parse_int "0")) || ((FStar_Ident.lid_equals env.FStar_TypeChecker_Env.curmodule FStar_Syntax_Const.prims_lid) && (skip_prims_type ()))) || is_noeq) then begin
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
in (let _153_722 = (let _153_721 = (let _153_720 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_153_720)))
in FStar_Syntax_Syntax.Sig_bundle (_153_721))
in (_153_722)::ses)))
end)))))))
end))
end))
end))))
end)))))))))
and tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env se -> (

let env = (set_hint_correlator env se)
in (

let _59_1494 = (FStar_TypeChecker_Util.check_sigelt_quals se)
in (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let se = (tc_lex_t env ses quals lids)
in (let _153_725 = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (_153_725)))))
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

let _59_1534 = (set_options FStar_Options.Set o)
in (((se)::[]), (env)))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(

let _59_1538 = (let _153_732 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _153_732 Prims.ignore))
in (

let _59_1543 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (

let _59_1545 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (((se)::[]), (env)))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_59_1548) -> begin
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

let _59_1564 = (FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun _59_1559 a -> (match (_59_1559) with
| (env, ses) -> begin
(

let se_let = (FStar_Syntax_Util.action_as_lb a)
in (let _153_735 = (FStar_TypeChecker_Env.push_sigelt env se_let)
in ((_153_735), ((se_let)::ses))))
end)) ((env), ((se)::[]))))
in (match (_59_1564) with
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

let _59_1573 = (let _153_736 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _153_736))
in (match (_59_1573) with
| (a, wp_a_src) -> begin
(

let _59_1576 = (let _153_737 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _153_737))
in (match (_59_1576) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (let _153_741 = (let _153_740 = (let _153_739 = (let _153_738 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (_153_738)))
in FStar_Syntax_Syntax.NT (_153_739))
in (_153_740)::[])
in (FStar_Syntax_Subst.subst _153_741 wp_b_tgt))
in (

let expected_k = (let _153_746 = (let _153_744 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_743 = (let _153_742 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_153_742)::[])
in (_153_744)::_153_743))
in (let _153_745 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _153_746 _153_745)))
in (

let repr_type = (fun eff_name a wp -> (

let no_reify = (fun l -> (let _153_758 = (let _153_757 = (let _153_756 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _153_755 = (FStar_TypeChecker_Env.get_range env)
in ((_153_756), (_153_755))))
in FStar_Syntax_Syntax.Error (_153_757))
in (Prims.raise _153_758)))
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
(let _153_765 = (let _153_763 = (let _153_762 = (let _153_761 = (FStar_Syntax_Syntax.as_arg a)
in (let _153_760 = (let _153_759 = (FStar_Syntax_Syntax.as_arg wp)
in (_153_759)::[])
in (_153_761)::_153_760))
in ((repr), (_153_762)))
in FStar_Syntax_Syntax.Tm_app (_153_763))
in (let _153_764 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _153_765 None _153_764)))
end)
end)))
in (

let _59_1617 = (match (((sub.FStar_Syntax_Syntax.lift), (sub.FStar_Syntax_Syntax.lift_wp))) with
| (None, None) -> begin
(FStar_All.failwith "Impossible")
end
| (lift, Some (_59_1594, lift_wp)) -> begin
(let _153_766 = (check_and_gen env lift_wp expected_k)
in ((lift), (_153_766)))
end
| (Some (what, lift), None) -> begin
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange))
in (

let _59_1610 = (FStar_TypeChecker_DMFF.star_expr dmff_env lift)
in (match (_59_1610) with
| (_59_1607, lift_wp, lift_elab) -> begin
(

let _59_1611 = (recheck_debug "lift-wp" env lift_wp)
in (

let _59_1613 = (recheck_debug "lift-elab" env lift_elab)
in ((Some ((([]), (lift_elab)))), ((([]), (lift_wp))))))
end)))
end)
in (match (_59_1617) with
| (lift, lift_wp) -> begin
(

let lax = env.FStar_TypeChecker_Env.lax
in (

let env = (

let _59_1619 = env
in {FStar_TypeChecker_Env.solver = _59_1619.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_1619.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_1619.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_1619.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_1619.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_1619.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_1619.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_1619.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_1619.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_1619.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_1619.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_1619.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_1619.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_1619.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_1619.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_1619.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_1619.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_1619.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _59_1619.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_1619.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_1619.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_1619.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_1619.FStar_TypeChecker_Env.qname_and_index})
in (

let lift = (match (lift) with
| None -> begin
None
end
| Some (_59_1624, lift) -> begin
(

let _59_1630 = (let _153_767 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _153_767))
in (match (_59_1630) with
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

let lift_wp_a = (let _153_774 = (let _153_772 = (let _153_771 = (let _153_770 = (FStar_Syntax_Syntax.as_arg a_typ)
in (let _153_769 = (let _153_768 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (_153_768)::[])
in (_153_770)::_153_769))
in ((lift_wp), (_153_771)))
in FStar_Syntax_Syntax.Tm_app (_153_772))
in (let _153_773 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _153_774 None _153_773)))
in (repr_type sub.FStar_Syntax_Syntax.target a_typ lift_wp_a)))
in (

let expected_k = (let _153_781 = (let _153_779 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_778 = (let _153_777 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (let _153_776 = (let _153_775 = (FStar_Syntax_Syntax.null_binder repr_f)
in (_153_775)::[])
in (_153_777)::_153_776))
in (_153_779)::_153_778))
in (let _153_780 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow _153_781 _153_780)))
in (

let _59_1644 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (_59_1644) with
| (expected_k, _59_1641, _59_1643) -> begin
(

let lift = (check_and_gen env lift expected_k)
in Some (lift))
end))))))))
end))
end)
in (

let env = (

let _59_1647 = env
in {FStar_TypeChecker_Env.solver = _59_1647.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_1647.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_1647.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_1647.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_1647.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_1647.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_1647.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_1647.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_1647.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_1647.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_1647.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_1647.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_1647.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_1647.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_1647.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_1647.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_1647.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_1647.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = lax; FStar_TypeChecker_Env.lax_universes = _59_1647.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_1647.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_1647.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_1647.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_1647.FStar_TypeChecker_Env.qname_and_index})
in (

let sub = (

let _59_1650 = sub
in {FStar_Syntax_Syntax.source = _59_1650.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _59_1650.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = Some (lift_wp); FStar_Syntax_Syntax.lift = lift})
in (

let se = FStar_Syntax_Syntax.Sig_sub_effect (((sub), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env)))))))))
end)))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, r) -> begin
(

let _59_1663 = ()
in (

let env0 = env
in (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _59_1669 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_59_1669) with
| (tps, c) -> begin
(

let _59_1673 = (tc_tparams env tps)
in (match (_59_1673) with
| (tps, env, us) -> begin
(

let _59_1677 = (FStar_TypeChecker_TcTerm.tc_comp env c)
in (match (_59_1677) with
| (c, u, g) -> begin
(

let _59_1678 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

let _59_1684 = (let _153_782 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _153_782))
in (match (_59_1684) with
| (uvs, t) -> begin
(

let _59_1703 = (match ((let _153_784 = (let _153_783 = (FStar_Syntax_Subst.compress t)
in _153_783.FStar_Syntax_Syntax.n)
in ((tps), (_153_784)))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_59_1687, c)) -> begin
(([]), (c))
end
| (_59_1693, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
((tps), (c))
end
| _59_1700 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_59_1703) with
| (tps, c) -> begin
(

let _59_1704 = if (((FStar_List.length uvs) <> (Prims.parse_int "1")) && (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid)))) then begin
(let _153_789 = (let _153_788 = (let _153_787 = (let _153_786 = (FStar_Syntax_Print.lid_to_string lid)
in (let _153_785 = (FStar_All.pipe_right (FStar_List.length uvs) FStar_Util.string_of_int)
in (FStar_Util.format2 "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes" _153_786 _153_785)))
in ((_153_787), (r)))
in FStar_Syntax_Syntax.Error (_153_788))
in (Prims.raise _153_789))
end else begin
()
end
in (

let se = FStar_Syntax_Syntax.Sig_effect_abbrev (((lid), (uvs), (tps), (c), (tags), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env0 se)
in (((se)::[]), (env)))))
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

let _59_1716 = ()
in (

let _59_1720 = (let _153_791 = (let _153_790 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _153_790))
in (check_and_gen env t _153_791))
in (match (_59_1720) with
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

let _59_1740 = (FStar_TypeChecker_TcTerm.tc_term env e)
in (match (_59_1740) with
| (e, c, g1) -> begin
(

let _59_1745 = (let _153_795 = (let _153_792 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_153_792))
in (let _153_794 = (let _153_793 = (c.FStar_Syntax_Syntax.comp ())
in ((e), (_153_793)))
in (FStar_TypeChecker_TcTerm.check_expected_effect env _153_795 _153_794)))
in (match (_59_1745) with
| (e, _59_1743, g) -> begin
(

let _59_1746 = (let _153_796 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _153_796))
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
(let _153_808 = (let _153_807 = (let _153_806 = (let _153_805 = (FStar_Syntax_Print.lid_to_string l)
in (let _153_804 = (FStar_Syntax_Print.quals_to_string q)
in (let _153_803 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _153_805 _153_804 _153_803))))
in ((_153_806), (r)))
in FStar_Syntax_Syntax.Error (_153_807))
in (Prims.raise _153_808))
end
end))
in (

let _59_1790 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _59_1767 lb -> (match (_59_1767) with
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _59_1786 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
((gen), (lb), (quals_opt))
end
| Some ((uvs, tval), quals) -> begin
(

let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (

let _59_1781 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _59_1780 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _153_811 = (FStar_Syntax_Syntax.mk_lb ((FStar_Util.Inr (lbname)), (uvs), (FStar_Syntax_Const.effect_ALL_lid), (tval), (lb.FStar_Syntax_Syntax.lbdef)))
in ((false), (_153_811), (quals_opt)))))
end)
in (match (_59_1786) with
| (gen, lb, quals_opt) -> begin
((gen), ((lb)::lbs), (quals_opt))
end)))
end)) ((true), ([]), (if (quals = []) then begin
None
end else begin
Some (quals)
end))))
in (match (_59_1790) with
| (should_generalize, lbs', quals_opt) -> begin
(

let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Visible_default)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _59_8 -> (match (_59_8) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Visible_default) | (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> begin
true
end
| _59_1799 -> begin
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

let e = (let _153_815 = (let _153_814 = (let _153_813 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((((Prims.fst lbs)), (lbs'))), (_153_813)))
in FStar_Syntax_Syntax.Tm_let (_153_814))
in (FStar_Syntax_Syntax.mk _153_815 None r))
in (

let _59_1833 = (match ((FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term (

let _59_1803 = env
in {FStar_TypeChecker_Env.solver = _59_1803.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_1803.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_1803.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_1803.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_1803.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_1803.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_1803.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_1803.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_1803.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_1803.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_1803.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _59_1803.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _59_1803.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_1803.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_1803.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_1803.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_1803.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _59_1803.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_1803.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_1803.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_1803.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_1803.FStar_TypeChecker_Env.qname_and_index}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _59_1810; FStar_Syntax_Syntax.pos = _59_1808; FStar_Syntax_Syntax.vars = _59_1806}, _59_1817, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_59_1821, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _59_1827 -> begin
quals
end)
in ((FStar_Syntax_Syntax.Sig_let (((lbs), (r), (lids), (quals)))), (lbs)))
end
| _59_1830 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_59_1833) with
| (se, lbs) -> begin
(

let _59_1839 = if (log env) then begin
(let _153_823 = (let _153_822 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (match ((let _153_819 = (let _153_818 = (let _153_817 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _153_817.FStar_Syntax_Syntax.fv_name)
in _153_818.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _153_819))) with
| None -> begin
true
end
| _59_1837 -> begin
false
end)
in if should_log then begin
(let _153_821 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _153_820 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _153_821 _153_820)))
end else begin
""
end))))
in (FStar_All.pipe_right _153_822 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _153_823))
end else begin
()
end
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env))))
end)))))
end))))
end))))


let for_export : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident Prims.list) = (fun hidden se -> (

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _59_9 -> (match (_59_9) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _59_1849 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _59_1859 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_59_1861) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _59_1872, r) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _59_1879 -> (match (_59_1879) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _59_1885, _59_1887, quals, r) -> begin
(

let dec = (let _153_837 = (let _153_836 = (let _153_835 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow bs _153_835))
in ((l), (us), (_153_836), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (_153_837))
in (((dec)::out), (hidden)))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _59_1897, _59_1899, _59_1901, _59_1903, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]), (r)))
in (((dec)::out), ((l)::hidden)))
end
| _59_1909 -> begin
((out), (hidden))
end)
end)) ses (([]), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end
| FStar_Syntax_Syntax.Sig_assume (_59_1911, _59_1913, quals, _59_1916) -> begin
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
| _59_1935 -> begin
false
end)))) then begin
(((se)::[]), (hidden))
end else begin
(([]), (hidden))
end
end
end
| FStar_Syntax_Syntax.Sig_main (_59_1937) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _59_1956, _59_1958, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
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
(let _153_844 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _153_843 = (let _153_842 = (let _153_841 = (let _153_840 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _153_840.FStar_Syntax_Syntax.fv_name)
in _153_841.FStar_Syntax_Syntax.v)
in ((_153_842), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (_153_843)))))
in ((_153_844), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let process_one_decl = (fun _59_1979 se -> (match (_59_1979) with
| (ses, exports, env, hidden) -> begin
(

let _59_1981 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_853 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _153_853))
end else begin
()
end
in (

let _59_1985 = (tc_decl env se)
in (match (_59_1985) with
| (ses', env) -> begin
(

let _59_1988 = if ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _153_858 = (FStar_List.fold_left (fun s se -> (let _153_857 = (let _153_856 = (FStar_Syntax_Print.sigelt_to_string se)
in (Prims.strcat _153_856 "\n"))
in (Prims.strcat s _153_857))) "" ses')
in (FStar_Util.print1 "Checked: %s\n" _153_858))
end else begin
()
end
in (

let _59_1991 = (FStar_List.iter (fun se -> (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)) ses')
in (

let _59_2000 = (FStar_List.fold_left (fun _59_1995 se -> (match (_59_1995) with
| (le, lh) -> begin
(

let tup = (for_export hidden se)
in (((FStar_List.rev_append (Prims.fst tup) le)), ((FStar_List.rev_append (Prims.snd tup) lh))))
end)) (([]), ([])) ses')
in (match (_59_2000) with
| (exported, hidden) -> begin
(((FStar_List.rev_append ses' ses)), (((FStar_List.rev_append exported []))::exports), (env), (hidden))
end))))
end)))
end))
in (

let _59_2026 = (FStar_List.fold_left (fun acc se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, r) -> begin
(

let _59_2014 = acc
in (match (_59_2014) with
| (_59_2008, _59_2010, env, _59_2013) -> begin
(

let _59_2017 = (cps_and_elaborate env ne)
in (match (_59_2017) with
| (ses, ne) -> begin
(

let ses = (FStar_List.append ses ((FStar_Syntax_Syntax.Sig_new_effect (((ne), (r))))::[]))
in (FStar_List.fold_left process_one_decl acc ses))
end))
end))
end
| _59_2020 -> begin
(process_one_decl acc se)
end)) (([]), ([]), (env), ([])) ses)
in (match (_59_2026) with
| (ses, exports, env, _59_2025) -> begin
(let _153_864 = (FStar_All.pipe_right (FStar_List.rev_append exports []) FStar_List.flatten)
in (((FStar_List.rev_append ses [])), (_153_864), (env)))
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

let _59_2031 = env
in (let _153_869 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _59_2031.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_2031.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_2031.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_2031.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_2031.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_2031.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_2031.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_2031.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_2031.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_2031.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_2031.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_2031.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_2031.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_2031.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_2031.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_2031.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _153_869; FStar_TypeChecker_Env.lax = _59_2031.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _59_2031.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_2031.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_2031.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_2031.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_2031.FStar_TypeChecker_Env.qname_and_index}))
in (

let _59_2034 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
in (

let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

let _59_2040 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_59_2040) with
| (ses, exports, env) -> begin
(((

let _59_2041 = modul
in {FStar_Syntax_Syntax.name = _59_2041.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _59_2041.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _59_2041.FStar_Syntax_Syntax.is_interface})), (exports), (env))
end))))))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let _59_2049 = (tc_decls env decls)
in (match (_59_2049) with
| (ses, exports, env) -> begin
(

let modul = (

let _59_2050 = modul
in {FStar_Syntax_Syntax.name = _59_2050.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _59_2050.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _59_2050.FStar_Syntax_Syntax.is_interface})
in ((modul), (exports), (env)))
end)))


let check_exports : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env modul exports -> (

let env = (

let _59_2056 = env
in {FStar_TypeChecker_Env.solver = _59_2056.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_2056.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_2056.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_2056.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_2056.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_2056.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_2056.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_2056.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_2056.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_2056.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_2056.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_2056.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_2056.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _59_2056.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_2056.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_2056.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_2056.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = true; FStar_TypeChecker_Env.type_of = _59_2056.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_2056.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_2056.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_2056.FStar_TypeChecker_Env.qname_and_index})
in (

let check_term = (fun lid univs t -> (

let _59_2065 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_59_2065) with
| (univs, t) -> begin
(

let _59_2067 = if (let _153_889 = (let _153_888 = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (FStar_TypeChecker_Env.debug _153_888))
in (FStar_All.pipe_left _153_889 (FStar_Options.Other ("Exports")))) then begin
(let _153_894 = (FStar_Syntax_Print.lid_to_string lid)
in (let _153_893 = (let _153_891 = (FStar_All.pipe_right univs (FStar_List.map (fun x -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (x))))))
in (FStar_All.pipe_right _153_891 (FStar_String.concat ", ")))
in (let _153_892 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print3 "Checking for export %s <%s> : %s\n" _153_894 _153_893 _153_892))))
end else begin
()
end
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env univs)
in (let _153_895 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env t)
in (FStar_All.pipe_right _153_895 Prims.ignore))))
end)))
in (

let check_term = (fun lid univs t -> (

let _59_2074 = (let _153_904 = (let _153_903 = (FStar_Syntax_Print.lid_to_string modul.FStar_Syntax_Syntax.name)
in (let _153_902 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Interface of %s violates its abstraction (add a \'private\' qualifier to \'%s\'?)" _153_903 _153_902)))
in (FStar_TypeChecker_Errors.message_prefix.FStar_TypeChecker_Errors.set_prefix _153_904))
in (

let _59_2076 = (check_term lid univs t)
in (FStar_TypeChecker_Errors.message_prefix.FStar_TypeChecker_Errors.clear_prefix ()))))
in (

let rec check_sigelt = (fun _59_11 -> (match (_59_11) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _59_2083, _59_2085) -> begin
if (not ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private)))) then begin
(FStar_All.pipe_right ses (FStar_List.iter check_sigelt))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_inductive_typ (l, univs, binders, typ, _59_2093, _59_2095, _59_2097, r) -> begin
(

let t = (let _153_909 = (let _153_908 = (let _153_907 = (FStar_Syntax_Syntax.mk_Total typ)
in ((binders), (_153_907)))
in FStar_Syntax_Syntax.Tm_arrow (_153_908))
in (FStar_Syntax_Syntax.mk _153_909 None r))
in (check_term l univs t))
end
| FStar_Syntax_Syntax.Sig_datacon (l, univs, t, _59_2106, _59_2108, _59_2110, _59_2112, _59_2114) -> begin
(check_term l univs t)
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, univs, t, quals, _59_2122) -> begin
if (not ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private)))) then begin
(check_term l univs t)
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_let ((_59_2126, lbs), _59_2130, _59_2132, quals) -> begin
if (not ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private)))) then begin
(FStar_All.pipe_right lbs (FStar_List.iter (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (check_term fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp)))))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, binders, comp, quals, r) -> begin
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

let _59_2168 = modul
in {FStar_Syntax_Syntax.name = _59_2168.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _59_2168.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module env modul)
in (

let _59_2172 = (check_exports env modul exports)
in (

let _59_2174 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (

let _59_2176 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (

let _59_2178 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (

let _59_2180 = (let _153_917 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _153_917 Prims.ignore))
in ((modul), (env))))))))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let _59_2187 = (tc_partial_modul env modul)
in (match (_59_2187) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (

let _59_2190 = if (FStar_Options.debug_any ()) then begin
(let _153_926 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _153_926))
end else begin
()
end
in (

let _59_2194 = (tc_modul env m)
in (match (_59_2194) with
| (m, env) -> begin
(

let _59_2195 = if (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _153_927 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _153_927))
end else begin
()
end
in ((m), (env)))
end))))




