
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

let _59_363 = if ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) || (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reflectable))) then begin
(

let repr = (

let _59_228 = (FStar_Syntax_Util.type_u ())
in (match (_59_228) with
| (t, _59_227) -> begin
(

let expected_k = (let _153_216 = (let _153_214 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_213 = (let _153_212 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_153_212)::[])
in (_153_214)::_153_213))
in (let _153_215 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _153_216 _153_215)))
in (tc_check_trivial_guard env ed.FStar_Syntax_Syntax.repr expected_k))
end))
in (

let mk_repr' = (fun t wp -> (

let repr = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env repr)
in (let _153_226 = (let _153_225 = (let _153_224 = (let _153_223 = (FStar_Syntax_Syntax.as_arg t)
in (let _153_222 = (let _153_221 = (FStar_Syntax_Syntax.as_arg wp)
in (_153_221)::[])
in (_153_223)::_153_222))
in ((repr), (_153_224)))
in FStar_Syntax_Syntax.Tm_app (_153_225))
in (FStar_Syntax_Syntax.mk _153_226 None FStar_Range.dummyRange))))
in (

let mk_repr = (fun a wp -> (let _153_231 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_repr' _153_231 wp)))
in (

let destruct_repr = (fun t -> (match ((let _153_234 = (FStar_Syntax_Subst.compress t)
in _153_234.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_59_241, ((t, _59_248))::((wp, _59_244))::[]) -> begin
((t), (wp))
end
| _59_254 -> begin
(FStar_All.failwith "Unexpected repr type")
end))
in (

let bind_repr = (

let r = (let _153_235 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_0 FStar_Syntax_Syntax.Delta_constant None)
in (FStar_All.pipe_right _153_235 FStar_Syntax_Syntax.fv_to_tm))
in (

let _59_258 = (fresh_effect_signature ())
in (match (_59_258) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _153_239 = (let _153_237 = (let _153_236 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _153_236))
in (_153_237)::[])
in (let _153_238 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _153_239 _153_238)))
in (

let wp_f = (FStar_Syntax_Syntax.gen_bv "wp_f" None wp_a)
in (

let wp_g = (FStar_Syntax_Syntax.gen_bv "wp_g" None a_wp_b)
in (

let x_a = (let _153_240 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _153_240))
in (

let wp_g_x = (let _153_244 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (let _153_243 = (let _153_242 = (let _153_241 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _153_241))
in (_153_242)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _153_244 _153_243 None FStar_Range.dummyRange)))
in (

let res = (

let wp = (let _153_256 = (let _153_245 = (FStar_TypeChecker_Env.inst_tscheme bind_wp)
in (FStar_All.pipe_right _153_245 Prims.snd))
in (let _153_255 = (let _153_254 = (let _153_253 = (let _153_252 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _153_251 = (let _153_250 = (FStar_Syntax_Syntax.bv_to_name b)
in (let _153_249 = (let _153_248 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (let _153_247 = (let _153_246 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (_153_246)::[])
in (_153_248)::_153_247))
in (_153_250)::_153_249))
in (_153_252)::_153_251))
in (r)::_153_253)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _153_254))
in (FStar_Syntax_Syntax.mk_Tm_app _153_256 _153_255 None FStar_Range.dummyRange)))
in (mk_repr b wp))
in (

let expected_k = (let _153_276 = (let _153_274 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_273 = (let _153_272 = (FStar_Syntax_Syntax.mk_binder b)
in (let _153_271 = (let _153_270 = (FStar_Syntax_Syntax.mk_binder wp_f)
in (let _153_269 = (let _153_268 = (let _153_258 = (let _153_257 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (mk_repr a _153_257))
in (FStar_Syntax_Syntax.null_binder _153_258))
in (let _153_267 = (let _153_266 = (FStar_Syntax_Syntax.mk_binder wp_g)
in (let _153_265 = (let _153_264 = (let _153_263 = (let _153_262 = (let _153_259 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_153_259)::[])
in (let _153_261 = (let _153_260 = (mk_repr b wp_g_x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _153_260))
in (FStar_Syntax_Util.arrow _153_262 _153_261)))
in (FStar_Syntax_Syntax.null_binder _153_263))
in (_153_264)::[])
in (_153_266)::_153_265))
in (_153_268)::_153_267))
in (_153_270)::_153_269))
in (_153_272)::_153_271))
in (_153_274)::_153_273))
in (let _153_275 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _153_276 _153_275)))
in (

let _59_272 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (_59_272) with
| (expected_k, _59_269, _59_271) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos)
in (

let env = (

let _59_274 = env
in {FStar_TypeChecker_Env.solver = _59_274.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_274.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_274.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_274.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_274.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_274.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_274.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_274.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_274.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_274.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_274.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_274.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_274.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_274.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_274.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_274.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_274.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_274.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _59_274.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_274.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_274.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_274.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_274.FStar_TypeChecker_Env.qname_and_index})
in (

let br = (check_and_gen' env ed.FStar_Syntax_Syntax.bind_repr expected_k)
in br)))
end)))))))))
end)))
in (

let return_repr = (

let x_a = (let _153_277 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _153_277))
in (

let res = (

let wp = (let _153_284 = (let _153_278 = (FStar_TypeChecker_Env.inst_tscheme return_wp)
in (FStar_All.pipe_right _153_278 Prims.snd))
in (let _153_283 = (let _153_282 = (let _153_281 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _153_280 = (let _153_279 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (_153_279)::[])
in (_153_281)::_153_280))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _153_282))
in (FStar_Syntax_Syntax.mk_Tm_app _153_284 _153_283 None FStar_Range.dummyRange)))
in (mk_repr a wp))
in (

let expected_k = (let _153_289 = (let _153_287 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_286 = (let _153_285 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_153_285)::[])
in (_153_287)::_153_286))
in (let _153_288 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _153_289 _153_288)))
in (

let _59_288 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (_59_288) with
| (expected_k, _59_285, _59_287) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos)
in (

let _59_292 = (check_and_gen' env ed.FStar_Syntax_Syntax.return_repr expected_k)
in (match (_59_292) with
| (univs, repr) -> begin
(match (univs) with
| [] -> begin
(([]), (repr))
end
| _59_295 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected universe-polymorphic return for effect"), (repr.FStar_Syntax_Syntax.pos)))))
end)
end)))
end)))))
in (

let actions = (

let check_action = (fun act -> (

let _59_303 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env act.FStar_Syntax_Syntax.action_typ)
in (match (_59_303) with
| (act_typ, _59_301, g_t) -> begin
(

let env' = (FStar_TypeChecker_Env.set_expected_typ env act_typ)
in (

let _59_305 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _153_293 = (FStar_Syntax_Print.term_to_string act.FStar_Syntax_Syntax.action_defn)
in (let _153_292 = (FStar_Syntax_Print.term_to_string act_typ)
in (FStar_Util.print3 "Checking action %s:\n[definition]: %s\n[cps\'d type]: %s\n" (FStar_Ident.text_of_lid act.FStar_Syntax_Syntax.action_name) _153_293 _153_292)))
end else begin
()
end
in (

let _59_311 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' act.FStar_Syntax_Syntax.action_defn)
in (match (_59_311) with
| (act_defn, _59_309, g_a) -> begin
(

let act_defn = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env act_defn)
in (

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
in (

let _59_334 = (

let act_typ = (FStar_Syntax_Subst.compress act_typ)
in (match (act_typ.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _59_322 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_59_322) with
| (bs, _59_321) -> begin
(

let res = (mk_repr' FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun)
in (

let k = (let _153_294 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs _153_294))
in (

let _59_329 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env k)
in (match (_59_329) with
| (k, _59_327, g) -> begin
((k), (g))
end))))
end))
end
| _59_331 -> begin
(let _153_299 = (let _153_298 = (let _153_297 = (let _153_296 = (FStar_Syntax_Print.term_to_string act_typ)
in (let _153_295 = (FStar_Syntax_Print.tag_of_term act_typ)
in (FStar_Util.format2 "Actions must have function types (not: %s, a.k.a. %s)" _153_296 _153_295)))
in ((_153_297), (act_defn.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_153_298))
in (Prims.raise _153_299))
end))
in (match (_59_334) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env act_typ expected_k)
in (

let _59_336 = (let _153_302 = (let _153_301 = (let _153_300 = (FStar_TypeChecker_Rel.conj_guard g_t g)
in (FStar_TypeChecker_Rel.conj_guard g_k _153_300))
in (FStar_TypeChecker_Rel.conj_guard g_a _153_301))
in (FStar_TypeChecker_Rel.force_trivial_guard env _153_302))
in (

let act_typ = (match ((let _153_303 = (FStar_Syntax_Subst.compress expected_k)
in _153_303.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _59_344 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_59_344) with
| (bs, c) -> begin
(

let _59_347 = (destruct_repr (FStar_Syntax_Util.comp_result c))
in (match (_59_347) with
| (a, wp) -> begin
(

let c = (let _153_307 = (let _153_304 = (env.FStar_TypeChecker_Env.universe_of env a)
in (_153_304)::[])
in (let _153_306 = (let _153_305 = (FStar_Syntax_Syntax.as_arg wp)
in (_153_305)::[])
in {FStar_Syntax_Syntax.comp_univs = _153_307; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a; FStar_Syntax_Syntax.effect_args = _153_306; FStar_Syntax_Syntax.flags = []}))
in (let _153_308 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Util.arrow bs _153_308)))
end))
end))
end
| _59_350 -> begin
(FStar_All.failwith "")
end)
in (

let _59_354 = (FStar_TypeChecker_Util.generalize_universes env act_defn)
in (match (_59_354) with
| (univs, act_defn) -> begin
(

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
in (

let _59_356 = act
in {FStar_Syntax_Syntax.action_name = _59_356.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = act_defn; FStar_Syntax_Syntax.action_typ = act_typ}))
end)))))
end))))
end))))
end)))
in (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.map check_action)))
in ((repr), (bind_repr), (return_repr), (actions)))))))))
end else begin
((ed.FStar_Syntax_Syntax.repr), (ed.FStar_Syntax_Syntax.bind_repr), (ed.FStar_Syntax_Syntax.return_repr), (ed.FStar_Syntax_Syntax.actions))
end
in (match (_59_363) with
| (repr, bind_repr, return_repr, actions) -> begin
(

let t = (let _153_309 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _153_309))
in (

let _59_367 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_59_367) with
| (univs, t) -> begin
(

let signature = (match ((let _153_311 = (let _153_310 = (FStar_Syntax_Subst.compress t)
in _153_310.FStar_Syntax_Syntax.n)
in ((effect_params), (_153_311)))) with
| ([], _59_370) -> begin
t
end
| (_59_373, FStar_Syntax_Syntax.Tm_arrow (_59_375, c)) -> begin
(FStar_Syntax_Util.comp_result c)
end
| _59_381 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let close = (fun n ts -> (

let ts = (let _153_316 = (FStar_Syntax_Subst.close_tscheme effect_params ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _153_316))
in (

let _59_387 = if (((n > (Prims.parse_int "0")) && (not ((FStar_Syntax_Util.is_unknown (Prims.snd ts))))) && ((FStar_List.length (Prims.fst ts)) <> n)) then begin
(let _153_319 = (let _153_318 = (FStar_Util.string_of_int n)
in (let _153_317 = (FStar_Syntax_Print.tscheme_to_string ts)
in (FStar_Util.format2 "The effect combinator is not universe-polymorphic enough (n=%s) (%s)" _153_318 _153_317)))
in (FStar_All.failwith _153_319))
end else begin
()
end
in ts)))
in (

let close_action = (fun act -> (

let _59_393 = (close (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_defn)))
in (match (_59_393) with
| (univs, defn) -> begin
(

let _59_396 = (close (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_typ)))
in (match (_59_396) with
| (univs', typ) -> begin
(

let _59_397 = ()
in (

let _59_399 = act
in {FStar_Syntax_Syntax.action_name = _59_399.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = defn; FStar_Syntax_Syntax.action_typ = typ}))
end))
end)))
in (

let _59_401 = ()
in (

let ed = (

let _59_403 = ed
in (let _153_336 = (close (Prims.parse_int "0") return_wp)
in (let _153_335 = (close (Prims.parse_int "1") bind_wp)
in (let _153_334 = (close (Prims.parse_int "0") if_then_else)
in (let _153_333 = (close (Prims.parse_int "0") ite_wp)
in (let _153_332 = (close (Prims.parse_int "0") stronger)
in (let _153_331 = (close (Prims.parse_int "1") close_wp)
in (let _153_330 = (close (Prims.parse_int "0") assert_p)
in (let _153_329 = (close (Prims.parse_int "0") assume_p)
in (let _153_328 = (close (Prims.parse_int "0") null_wp)
in (let _153_327 = (close (Prims.parse_int "0") trivial_wp)
in (let _153_326 = (let _153_322 = (close (Prims.parse_int "0") (([]), (repr)))
in (Prims.snd _153_322))
in (let _153_325 = (close (Prims.parse_int "0") return_repr)
in (let _153_324 = (close (Prims.parse_int "1") bind_repr)
in (let _153_323 = (FStar_List.map close_action actions)
in {FStar_Syntax_Syntax.qualifiers = _59_403.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _59_403.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _153_336; FStar_Syntax_Syntax.bind_wp = _153_335; FStar_Syntax_Syntax.if_then_else = _153_334; FStar_Syntax_Syntax.ite_wp = _153_333; FStar_Syntax_Syntax.stronger = _153_332; FStar_Syntax_Syntax.close_wp = _153_331; FStar_Syntax_Syntax.assert_p = _153_330; FStar_Syntax_Syntax.assume_p = _153_329; FStar_Syntax_Syntax.null_wp = _153_328; FStar_Syntax_Syntax.trivial = _153_327; FStar_Syntax_Syntax.repr = _153_326; FStar_Syntax_Syntax.return_repr = _153_325; FStar_Syntax_Syntax.bind_repr = _153_324; FStar_Syntax_Syntax.actions = _153_323})))))))))))))))
in (

let _59_406 = if ((FStar_TypeChecker_Env.debug env FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ED")))) then begin
(let _153_337 = (FStar_Syntax_Print.eff_decl_to_string false ed)
in (FStar_Util.print_string _153_337))
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

let _59_412 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_59_412) with
| (effect_binders_un, signature_un) -> begin
(

let _59_417 = (tc_tparams env effect_binders_un)
in (match (_59_417) with
| (effect_binders, env, _59_416) -> begin
(

let _59_421 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (_59_421) with
| (signature, _59_420) -> begin
(

let effect_binders = (FStar_List.map (fun _59_424 -> (match (_59_424) with
| (bv, qual) -> begin
(let _153_342 = (

let _59_425 = bv
in (let _153_341 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _59_425.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_425.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _153_341}))
in ((_153_342), (qual)))
end)) effect_binders)
in (

let _59_440 = (match ((let _153_343 = (FStar_Syntax_Subst.compress signature_un)
in _153_343.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (((a, _59_430))::[], effect_marker) -> begin
((a), (effect_marker))
end
| _59_437 -> begin
(FStar_All.failwith "bad shape for effect-for-free signature")
end)
in (match (_59_440) with
| (a, effect_marker) -> begin
(

let open_and_check = (fun t -> (

let subst = (FStar_Syntax_Subst.opening_of_binders effect_binders)
in (

let t = (FStar_Syntax_Subst.subst subst t)
in (

let _59_449 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (_59_449) with
| (t, comp, _59_448) -> begin
((t), (comp))
end)))))
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None signature.FStar_Syntax_Syntax.pos))
in (

let _59_454 = (open_and_check ed.FStar_Syntax_Syntax.repr)
in (match (_59_454) with
| (repr, _comp) -> begin
(

let _59_455 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _153_348 = (FStar_Syntax_Print.term_to_string repr)
in (FStar_Util.print1 "Representation is: %s\n" _153_348))
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

let wp_a = (let _153_355 = (let _153_354 = (let _153_353 = (let _153_352 = (let _153_351 = (let _153_350 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _153_349 = (FStar_Syntax_Syntax.as_implicit false)
in ((_153_350), (_153_349))))
in (_153_351)::[])
in ((wp_type), (_153_352)))
in FStar_Syntax_Syntax.Tm_app (_153_353))
in (mk _153_354))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _153_355))
in (

let effect_signature = (

let binders = (let _153_360 = (let _153_356 = (FStar_Syntax_Syntax.as_implicit false)
in ((a), (_153_356)))
in (let _153_359 = (let _153_358 = (let _153_357 = (FStar_Syntax_Syntax.gen_bv "dijkstra_wp" None wp_a)
in (FStar_All.pipe_right _153_357 FStar_Syntax_Syntax.mk_binder))
in (_153_358)::[])
in (_153_360)::_153_359))
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

let _59_473 = item
in (match (_59_473) with
| (u_item, item) -> begin
(

let _59_476 = (open_and_check item)
in (match (_59_476) with
| (item, item_comp) -> begin
(

let _59_477 = if (not ((FStar_Syntax_Util.is_total_lcomp item_comp))) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Computation for [item] is not total!")))
end else begin
()
end
in (

let _59_482 = (FStar_TypeChecker_DMFF.star_expr dmff_env item)
in (match (_59_482) with
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

let _59_490 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.bind_repr)
in (match (_59_490) with
| (dmff_env, _59_487, bind_wp, bind_elab) -> begin
(

let _59_496 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.return_repr)
in (match (_59_496) with
| (dmff_env, _59_493, return_wp, return_elab) -> begin
(

let return_wp = (match ((let _153_367 = (FStar_Syntax_Subst.compress return_wp)
in _153_367.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(let _153_368 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs ((b1)::(b2)::[]) _153_368 (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_GTot_lid)))))
end
| _59_507 -> begin
(FStar_All.failwith "unexpected shape for return")
end)
in (

let bind_wp = (match ((let _153_369 = (FStar_Syntax_Subst.compress bind_wp)
in _153_369.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let r = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_lid (FStar_Syntax_Syntax.Delta_unfoldable ((Prims.parse_int "1"))) None)
in (let _153_373 = (let _153_372 = (let _153_371 = (let _153_370 = (mk (FStar_Syntax_Syntax.Tm_fvar (r)))
in (FStar_Syntax_Syntax.null_binder _153_370))
in (_153_371)::[])
in (FStar_List.append _153_372 binders))
in (FStar_Syntax_Util.abs _153_373 body what)))
end
| _59_516 -> begin
(FStar_All.failwith "unexpected shape for bind")
end)
in (

let apply_close = (fun t -> if ((FStar_List.length effect_binders) = (Prims.parse_int "0")) then begin
t
end else begin
(let _153_380 = (let _153_379 = (let _153_378 = (let _153_377 = (let _153_376 = (FStar_Syntax_Util.args_of_binders effect_binders)
in (Prims.snd _153_376))
in ((t), (_153_377)))
in FStar_Syntax_Syntax.Tm_app (_153_378))
in (mk _153_379))
in (FStar_Syntax_Subst.close effect_binders _153_380))
end)
in (

let register = (fun name item -> (

let _59_525 = (let _153_386 = (mk_lid name)
in (let _153_385 = (FStar_Syntax_Util.abs effect_binders item None)
in (FStar_TypeChecker_Util.mk_toplevel_definition env _153_386 _153_385)))
in (match (_59_525) with
| (sigelt, fv) -> begin
(

let _59_526 = (let _153_388 = (let _153_387 = (FStar_ST.read sigelts)
in (sigelt)::_153_387)
in (FStar_ST.op_Colon_Equals sigelts _153_388))
in fv)
end)))
in (

let return_wp = (register "return_wp" return_wp)
in (

let return_elab = (register "return_elab" return_elab)
in (

let bind_wp = (register "bind_wp" bind_wp)
in (

let _59_531 = (let _153_390 = (let _153_389 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true")), (FStar_Range.dummyRange))))::_153_389)
in (FStar_ST.op_Colon_Equals sigelts _153_390))
in (

let bind_elab = (register "bind_elab" bind_elab)
in (

let _59_534 = (let _153_392 = (let _153_391 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false")), (FStar_Range.dummyRange))))::_153_391)
in (FStar_ST.op_Colon_Equals sigelts _153_392))
in (

let _59_553 = (FStar_List.fold_left (fun _59_538 action -> (match (_59_538) with
| (dmff_env, actions) -> begin
(

let _59_544 = (elaborate_and_star dmff_env ((action.FStar_Syntax_Syntax.action_univs), (action.FStar_Syntax_Syntax.action_defn)))
in (match (_59_544) with
| (dmff_env, action_t, action_wp, action_elab) -> begin
(

let name = action.FStar_Syntax_Syntax.action_name.FStar_Ident.ident.FStar_Ident.idText
in (

let action_typ_with_wp = (FStar_TypeChecker_DMFF.trans_F dmff_env action_t action_wp)
in (

let action_elab = (register (Prims.strcat name "_elab") action_elab)
in (

let action_typ_with_wp = (register (Prims.strcat name "_complete_type") action_typ_with_wp)
in (let _153_398 = (let _153_397 = (

let _59_549 = action
in (let _153_396 = (apply_close action_elab)
in (let _153_395 = (apply_close action_typ_with_wp)
in {FStar_Syntax_Syntax.action_name = _59_549.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = _59_549.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _153_396; FStar_Syntax_Syntax.action_typ = _153_395})))
in (_153_397)::actions)
in ((dmff_env), (_153_398)))))))
end))
end)) ((dmff_env), ([])) ed.FStar_Syntax_Syntax.actions)
in (match (_59_553) with
| (dmff_env, actions) -> begin
(

let actions = (FStar_List.rev actions)
in (

let repr = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp_a" None wp_a)
in (

let binders = (let _153_401 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_400 = (let _153_399 = (FStar_Syntax_Syntax.mk_binder wp)
in (_153_399)::[])
in (_153_401)::_153_400))
in (let _153_410 = (let _153_409 = (let _153_407 = (let _153_406 = (let _153_405 = (let _153_404 = (let _153_403 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _153_402 = (FStar_Syntax_Syntax.as_implicit false)
in ((_153_403), (_153_402))))
in (_153_404)::[])
in ((repr), (_153_405)))
in FStar_Syntax_Syntax.Tm_app (_153_406))
in (mk _153_407))
in (let _153_408 = (FStar_Syntax_Syntax.bv_to_name wp)
in (FStar_TypeChecker_DMFF.trans_F dmff_env _153_409 _153_408)))
in (FStar_Syntax_Util.abs binders _153_410 None))))
in (

let repr = (recheck_debug "FC" env repr)
in (

let repr = (register "repr" repr)
in (

let _59_585 = (match ((let _153_411 = (FStar_Syntax_Subst.compress wp_type)
in _153_411.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (effect_param, arrow, _59_563) -> begin
(

let _59_568 = (FStar_Syntax_Subst.open_term effect_param arrow)
in (match (_59_568) with
| (effect_param, arrow) -> begin
(match ((let _153_412 = (FStar_Syntax_Subst.compress arrow)
in _153_412.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (wp_binders, c) -> begin
(

let _59_575 = (FStar_Syntax_Subst.open_comp wp_binders c)
in (match (_59_575) with
| (wp_binders, c) -> begin
(

let _59_578 = (FStar_Util.prefix wp_binders)
in (match (_59_578) with
| (pre_args, post) -> begin
(let _153_414 = (FStar_Syntax_Util.arrow pre_args c)
in (let _153_413 = (FStar_Syntax_Util.abs effect_param (Prims.fst post).FStar_Syntax_Syntax.sort None)
in ((_153_414), (_153_413))))
end))
end))
end
| _59_580 -> begin
(let _153_416 = (let _153_415 = (FStar_Syntax_Print.term_to_string arrow)
in (FStar_Util.format1 "Impossible: pre/post arrow %s" _153_415))
in (FStar_All.failwith _153_416))
end)
end))
end
| _59_582 -> begin
(let _153_418 = (let _153_417 = (FStar_Syntax_Print.term_to_string wp_type)
in (FStar_Util.format1 "Impossible: pre/post abs %s" _153_417))
in (FStar_All.failwith _153_418))
end)
in (match (_59_585) with
| (pre, post) -> begin
(

let _59_586 = (let _153_419 = (register "pre" pre)
in (Prims.ignore _153_419))
in (

let _59_588 = (let _153_420 = (register "post" post)
in (Prims.ignore _153_420))
in (

let _59_590 = (let _153_421 = (register "wp" wp_type)
in (Prims.ignore _153_421))
in (

let ed = (

let _59_592 = ed
in (let _153_432 = (FStar_Syntax_Subst.close_binders effect_binders)
in (let _153_431 = (FStar_Syntax_Subst.close effect_binders effect_signature)
in (let _153_430 = (let _153_422 = (apply_close return_wp)
in (([]), (_153_422)))
in (let _153_429 = (let _153_423 = (apply_close bind_wp)
in (([]), (_153_423)))
in (let _153_428 = (apply_close repr)
in (let _153_427 = (let _153_424 = (apply_close return_elab)
in (([]), (_153_424)))
in (let _153_426 = (let _153_425 = (apply_close bind_elab)
in (([]), (_153_425)))
in {FStar_Syntax_Syntax.qualifiers = _59_592.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _59_592.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _59_592.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _153_432; FStar_Syntax_Syntax.signature = _153_431; FStar_Syntax_Syntax.ret_wp = _153_430; FStar_Syntax_Syntax.bind_wp = _153_429; FStar_Syntax_Syntax.if_then_else = _59_592.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _59_592.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _59_592.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _59_592.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _59_592.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _59_592.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _59_592.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _59_592.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _153_428; FStar_Syntax_Syntax.return_repr = _153_427; FStar_Syntax_Syntax.bind_repr = _153_426; FStar_Syntax_Syntax.actions = actions}))))))))
in (

let _59_597 = (FStar_TypeChecker_DMFF.gen_wps_for_free env effect_binders a wp_a ed)
in (match (_59_597) with
| (sigelts', ed) -> begin
(

let _59_598 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _153_433 = (FStar_Syntax_Print.eff_decl_to_string true ed)
in (FStar_Util.print_string _153_433))
end else begin
()
end
in (let _153_436 = (let _153_435 = (let _153_434 = (FStar_ST.read sigelts)
in (FStar_List.rev _153_434))
in (FStar_List.append _153_435 sigelts'))
in ((_153_436), (ed))))
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

let _59_604 = ()
in (

let _59_612 = ()
in (match (ses) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _59_641, _59_643, [], r))::(FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, _153_441, [], _59_632, r1))::(FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, _153_442, [], _59_621, r2))::[] when (((_153_441 = (Prims.parse_int "0")) && (_153_442 = (Prims.parse_int "0"))) && (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid))) -> begin
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

let lex_top_t = (let _153_446 = (let _153_445 = (let _153_444 = (let _153_443 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1)
in (FStar_Syntax_Syntax.fvar _153_443 FStar_Syntax_Syntax.Delta_constant None))
in ((_153_444), ((FStar_Syntax_Syntax.U_name (utop))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_153_445))
in (FStar_Syntax_Syntax.mk _153_446 None r1))
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

let a = (let _153_447 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _153_447))
in (

let hd = (let _153_448 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _153_448))
in (

let tl = (let _153_453 = (let _153_452 = (let _153_451 = (let _153_450 = (let _153_449 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _153_449 FStar_Syntax_Syntax.Delta_constant None))
in ((_153_450), ((FStar_Syntax_Syntax.U_name (ucons2))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_153_451))
in (FStar_Syntax_Syntax.mk _153_452 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _153_453))
in (

let res = (let _153_457 = (let _153_456 = (let _153_455 = (let _153_454 = (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2)
in (FStar_Syntax_Syntax.fvar _153_454 FStar_Syntax_Syntax.Delta_constant None))
in ((_153_455), ((FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_153_456))
in (FStar_Syntax_Syntax.mk _153_457 None r2))
in (let _153_458 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow ((((a), (Some (FStar_Syntax_Syntax.imp_tag))))::(((hd), (None)))::(((tl), (None)))::[]) _153_458))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon (((lex_cons), ((ucons1)::(ucons2)::[]), (lex_cons_t), (FStar_Syntax_Const.lex_t_lid), ((Prims.parse_int "0")), ([]), ([]), (r2)))
in (let _153_460 = (let _153_459 = (FStar_TypeChecker_Env.get_range env)
in (((tc)::(dc_lextop)::(dc_lexcons)::[]), ([]), (lids), (_153_459)))
in FStar_Syntax_Syntax.Sig_bundle (_153_460)))))))))))))))
end
| _59_667 -> begin
(let _153_462 = (let _153_461 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle (((ses), ([]), (lids), (FStar_Range.dummyRange)))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _153_461))
in (FStar_All.failwith _153_462))
end))))
and tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _59_677 = (FStar_Syntax_Util.type_u ())
in (match (_59_677) with
| (k, _59_676) -> begin
(

let phi = (let _153_468 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _153_468 (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]) env)))
in (

let _59_679 = (FStar_TypeChecker_Util.check_uvars r phi)
in FStar_Syntax_Syntax.Sig_assume (((lid), (phi), (quals), (r)))))
end))))
and tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun env ses quals lids -> (

let warn_positivity = (fun l r -> (let _153_478 = (let _153_477 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _153_477))
in (FStar_TypeChecker_Errors.diag r _153_478)))
in (

let env0 = env
in (

let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(

let _59_702 = ()
in (

let _59_704 = (warn_positivity tc r)
in (

let _59_708 = (FStar_Syntax_Subst.open_term tps k)
in (match (_59_708) with
| (tps, k) -> begin
(

let _59_713 = (FStar_TypeChecker_TcTerm.tc_binders env tps)
in (match (_59_713) with
| (tps, env_tps, guard_params, us) -> begin
(

let _59_716 = (FStar_Syntax_Util.arrow_formals k)
in (match (_59_716) with
| (indices, t) -> begin
(

let _59_721 = (FStar_TypeChecker_TcTerm.tc_binders env_tps indices)
in (match (_59_721) with
| (indices, env', guard_indices, us') -> begin
(

let _59_729 = (

let _59_726 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' t)
in (match (_59_726) with
| (t, _59_724, g) -> begin
(let _153_485 = (let _153_484 = (let _153_483 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params _153_483))
in (FStar_TypeChecker_Rel.discharge_guard env' _153_484))
in ((t), (_153_485)))
end))
in (match (_59_729) with
| (t, guard) -> begin
(

let k = (let _153_486 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _153_486))
in (

let _59_733 = (FStar_Syntax_Util.type_u ())
in (match (_59_733) with
| (t_type, u) -> begin
(

let _59_734 = (let _153_487 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _153_487))
in (

let t_tc = (let _153_488 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _153_488))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _153_489 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) (([]), (t_tc)))
in ((_153_489), (FStar_Syntax_Syntax.Sig_inductive_typ (((tc), ([]), (tps), (k), (mutuals), (data), (quals), (r)))), (u), (guard))))))))
end)))
end))
end))
end))
end))
end))))
end
| _59_741 -> begin
(FStar_All.failwith "impossible")
end))
in (

let positive_if_pure = (fun _59_743 l -> ())
in (

let tc_data = (fun env tcs _59_1 -> (match (_59_1) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let _59_760 = ()
in (

let _59_795 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun _59_764 -> (match (_59_764) with
| (se, u_tc) -> begin
if (let _153_502 = (let _153_501 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _153_501))
in (FStar_Ident.lid_equals tc_lid _153_502)) then begin
(

let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_59_766, _59_768, tps, _59_771, _59_773, _59_775, _59_777, _59_779) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _59_785 -> (match (_59_785) with
| (x, _59_784) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
end
| _59_787 -> begin
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
in (match (_59_795) with
| (tps, u_tc) -> begin
(

let _59_815 = (match ((let _153_504 = (FStar_Syntax_Subst.compress t)
in _153_504.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let _59_803 = (FStar_Util.first_N ntps bs)
in (match (_59_803) with
| (_59_801, bs') -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs'), (res)))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _59_809 -> (match (_59_809) with
| (x, _59_808) -> begin
FStar_Syntax_Syntax.DB ((((ntps - ((Prims.parse_int "1") + i))), (x)))
end))))
in (let _153_507 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _153_507))))
end))
end
| _59_812 -> begin
(([]), (t))
end)
in (match (_59_815) with
| (arguments, result) -> begin
(

let _59_816 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_510 = (FStar_Syntax_Print.lid_to_string c)
in (let _153_509 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _153_508 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _153_510 _153_509 _153_508))))
end else begin
()
end
in (

let _59_821 = (tc_tparams env arguments)
in (match (_59_821) with
| (arguments, env', us) -> begin
(

let _59_825 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env' result)
in (match (_59_825) with
| (result, _59_824) -> begin
(

let _59_829 = (FStar_Syntax_Util.head_and_args result)
in (match (_59_829) with
| (head, _59_828) -> begin
(

let _59_834 = (match ((let _153_511 = (FStar_Syntax_Subst.compress head)
in _153_511.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _59_833 -> begin
(let _153_516 = (let _153_515 = (let _153_514 = (let _153_513 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (let _153_512 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" _153_513 _153_512)))
in ((_153_514), (r)))
in FStar_Syntax_Syntax.Error (_153_515))
in (Prims.raise _153_516))
end)
in (

let g = (FStar_List.fold_left2 (fun g _59_840 u_x -> (match (_59_840) with
| (x, _59_839) -> begin
(

let _59_842 = ()
in (let _153_520 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _153_520)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _153_524 = (let _153_522 = (FStar_All.pipe_right tps (FStar_List.map (fun _59_848 -> (match (_59_848) with
| (x, _59_847) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append _153_522 arguments))
in (let _153_523 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _153_524 _153_523)))
in ((FStar_Syntax_Syntax.Sig_datacon (((c), ([]), (t), (tc_lid), (ntps), (quals), ([]), (r)))), (g)))))
end))
end))
end)))
end))
end)))
end
| _59_851 -> begin
(FStar_All.failwith "impossible")
end))
in (

let generalize_and_inst_within = (fun env g tcs datas -> (

let _59_857 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _59_2 -> (match (_59_2) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_59_861, _59_863, tps, k, _59_867, _59_869, _59_871, _59_873) -> begin
(let _153_535 = (let _153_534 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _153_534))
in (FStar_Syntax_Syntax.null_binder _153_535))
end
| _59_877 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _59_3 -> (match (_59_3) with
| FStar_Syntax_Syntax.Sig_datacon (_59_881, _59_883, t, _59_886, _59_888, _59_890, _59_892, _59_894) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _59_898 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let t = (let _153_537 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _153_537))
in (

let _59_901 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_538 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _153_538))
end else begin
()
end
in (

let _59_905 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_59_905) with
| (uvs, t) -> begin
(

let _59_907 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_542 = (let _153_540 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _153_540 (FStar_String.concat ", ")))
in (let _153_541 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _153_542 _153_541)))
end else begin
()
end
in (

let _59_911 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_59_911) with
| (uvs, t) -> begin
(

let _59_915 = (FStar_Syntax_Util.arrow_formals t)
in (match (_59_915) with
| (args, _59_914) -> begin
(

let _59_918 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_59_918) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun _59_922 se -> (match (_59_922) with
| (x, _59_921) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _59_926, tps, _59_929, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let _59_952 = (match ((let _153_545 = (FStar_Syntax_Subst.compress ty)
in _153_545.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _59_943 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_59_943) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _59_946 -> begin
(let _153_546 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) _153_546 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in ((tps), (t)))
end))
end
| _59_949 -> begin
(([]), (ty))
end)
in (match (_59_952) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs), (tps), (t), (mutuals), (datas), (quals), (r)))
end)))
end
| _59_954 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| _59_958 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _153_547 -> FStar_Syntax_Syntax.U_name (_153_547))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _59_4 -> (match (_59_4) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _59_963, _59_965, _59_967, _59_969, _59_971, _59_973, _59_975) -> begin
((tc), (uvs_universes))
end
| _59_979 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _59_984 d -> (match (_59_984) with
| (t, _59_983) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _59_988, _59_990, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (let _153_551 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _153_551 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon (((l), (uvs), (ty), (tc), (ntps), (quals), (mutuals), (r))))
end
| _59_1000 -> begin
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

let _59_1010 = (FStar_All.pipe_right ses (FStar_List.partition (fun _59_5 -> (match (_59_5) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_59_1004) -> begin
true
end
| _59_1007 -> begin
false
end))))
in (match (_59_1010) with
| (tys, datas) -> begin
(

let _59_1017 = if (FStar_All.pipe_right datas (FStar_Util.for_some (fun _59_6 -> (match (_59_6) with
| FStar_Syntax_Syntax.Sig_datacon (_59_1013) -> begin
false
end
| _59_1016 -> begin
true
end)))) then begin
(let _153_556 = (let _153_555 = (let _153_554 = (FStar_TypeChecker_Env.get_range env)
in (("Mutually defined type contains a non-inductive element"), (_153_554)))
in FStar_Syntax_Syntax.Error (_153_555))
in (Prims.raise _153_556))
end else begin
()
end
in (

let env0 = env
in (

let _59_1036 = (FStar_List.fold_right (fun tc _59_1024 -> (match (_59_1024) with
| (env, all_tcs, g) -> begin
(

let _59_1029 = (tc_tycon env tc)
in (match (_59_1029) with
| (env, tc, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (

let _59_1031 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_559 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _153_559))
end else begin
()
end
in (let _153_561 = (let _153_560 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g _153_560))
in ((env), ((((tc), (tc_u)))::all_tcs), (_153_561)))))
end))
end)) tys ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (_59_1036) with
| (env, tcs, g) -> begin
(

let _59_1046 = (FStar_List.fold_right (fun se _59_1040 -> (match (_59_1040) with
| (datas, g) -> begin
(

let _59_1043 = (tc_data env tcs se)
in (match (_59_1043) with
| (data, g') -> begin
(let _153_564 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((data)::datas), (_153_564)))
end))
end)) datas (([]), (g)))
in (match (_59_1046) with
| (datas, g) -> begin
(

let _59_1049 = (let _153_565 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _153_565 datas))
in (match (_59_1049) with
| (tcs, datas) -> begin
(

let sig_bndle = (let _153_567 = (let _153_566 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_153_566)))
in FStar_Syntax_Syntax.Sig_bundle (_153_567))
in (

let datacon_typ = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (_59_1054, _59_1056, t, _59_1059, _59_1061, _59_1063, _59_1065, _59_1067) -> begin
t
end
| _59_1071 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let dr = FStar_Range.dummyRange
in (

let optimized_haseq_scheme = (fun _59_1074 -> (

let haseq_ty = (fun usubst us acc ty -> (

let _59_1101 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _59_1083, bs, t, _59_1087, d_lids, _59_1090, _59_1092) -> begin
((lid), (bs), (t), (d_lids))
end
| _59_1096 -> begin
(FStar_All.failwith "Impossible!")
end)
in (match (_59_1101) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _153_580 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _153_580 t))
in (

let _59_1106 = (FStar_Syntax_Subst.open_term bs t)
in (match (_59_1106) with
| (bs, t) -> begin
(

let ibs = (match ((let _153_581 = (FStar_Syntax_Subst.compress t)
in _153_581.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _59_1109) -> begin
ibs
end
| _59_1113 -> begin
[]
end)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _153_584 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _153_583 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _153_584 _153_583)))
in (

let ind = (let _153_587 = (FStar_List.map (fun _59_1120 -> (match (_59_1120) with
| (bv, aq) -> begin
(let _153_586 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_153_586), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _153_587 None dr))
in (

let ind = (let _153_590 = (FStar_List.map (fun _59_1124 -> (match (_59_1124) with
| (bv, aq) -> begin
(let _153_589 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_153_589), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _153_590 None dr))
in (

let haseq_ind = (let _153_592 = (let _153_591 = (FStar_Syntax_Syntax.as_arg ind)
in (_153_591)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _153_592 None dr))
in (

let bs' = (FStar_List.filter (fun b -> (

let _59_1135 = acc
in (match (_59_1135) with
| (_59_1129, en, _59_1132, _59_1134) -> begin
(

let opt = (let _153_595 = (let _153_594 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _153_594))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort _153_595 false))
in (match (opt) with
| None -> begin
false
end
| Some (_59_1139) -> begin
true
end))
end))) bs)
in (

let haseq_bs = (FStar_List.fold_left (fun t b -> (let _153_601 = (let _153_600 = (let _153_599 = (let _153_598 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b))
in (FStar_Syntax_Syntax.as_arg _153_598))
in (_153_599)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _153_600 None dr))
in (FStar_Syntax_Util.mk_conj t _153_601))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml = (

let _59_1146 = fml
in (let _153_607 = (let _153_606 = (let _153_605 = (let _153_604 = (let _153_603 = (let _153_602 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_153_602)::[])
in (_153_603)::[])
in FStar_Syntax_Syntax.Meta_pattern (_153_604))
in ((fml), (_153_605)))
in FStar_Syntax_Syntax.Tm_meta (_153_606))
in {FStar_Syntax_Syntax.n = _153_607; FStar_Syntax_Syntax.tk = _59_1146.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _59_1146.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _59_1146.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _153_613 = (let _153_612 = (let _153_611 = (let _153_610 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _153_610 None))
in (FStar_Syntax_Syntax.as_arg _153_611))
in (_153_612)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _153_613 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _153_619 = (let _153_618 = (let _153_617 = (let _153_616 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _153_616 None))
in (FStar_Syntax_Syntax.as_arg _153_617))
in (_153_618)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _153_619 None dr))) bs fml)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let _59_1160 = acc
in (match (_59_1160) with
| (l_axioms, env, guard', cond') -> begin
(

let env = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env = (FStar_TypeChecker_Env.push_binders env ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (_59_1165, _59_1167, _59_1169, t_lid, _59_1172, _59_1174, _59_1176, _59_1178) -> begin
(t_lid = lid)
end
| _59_1182 -> begin
(FStar_All.failwith "Impossible")
end)) datas)
in (

let haseq_data = (fun data -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (match ((let _153_623 = (FStar_Syntax_Subst.compress dt)
in _153_623.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _59_1190) -> begin
(

let dbs = (let _153_624 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _153_624))
in (

let dbs = (let _153_625 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _153_625 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let haseq_b = (let _153_629 = (let _153_628 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_153_628)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _153_629 None dr))
in (

let sort_range = (Prims.fst b).FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos
in (

let haseq_b = (let _153_631 = (let _153_630 = (FStar_Syntax_Print.term_to_string ind)
in (FStar_Util.format1 "Failed to prove that the type \'%s\' supports decidable equality because of this argument; add the \'noeq\' qualifier" _153_630))
in (FStar_TypeChecker_Util.label _153_631 sort_range haseq_b))
in (FStar_Syntax_Util.mk_conj t haseq_b))))) FStar_Syntax_Util.t_true dbs)
in (FStar_List.fold_right (fun b t -> (let _153_637 = (let _153_636 = (let _153_635 = (let _153_634 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _153_634 None))
in (FStar_Syntax_Syntax.as_arg _153_635))
in (_153_636)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _153_637 None dr))) dbs cond)))))
end
| _59_1205 -> begin
FStar_Syntax_Util.t_true
end))))
in (

let cond = (FStar_List.fold_left (fun acc d -> (let _153_640 = (haseq_data d)
in (FStar_Syntax_Util.mk_conj acc _153_640))) FStar_Syntax_Util.t_true t_datas)
in (

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (let _153_642 = (FStar_Syntax_Util.mk_conj guard' guard)
in (let _153_641 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml)))::[]))), (env), (_153_642), (_153_641))))))))))
end)))))))))))))))
end))))
end)))
in (

let us = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_59_1212, us, _59_1215, _59_1217, _59_1219, _59_1221, _59_1223, _59_1225) -> begin
us
end
| _59_1229 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let _59_1233 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (_59_1233) with
| (usubst, us) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (

let _59_1235 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq")
in (

let _59_1237 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle)
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let _59_1244 = (FStar_List.fold_left (haseq_ty usubst us) (([]), (env), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (_59_1244) with
| (axioms, env, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let _59_1249 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env phi)
in (match (_59_1249) with
| (phi, _59_1248) -> begin
(

let _59_1250 = if (FStar_TypeChecker_Env.should_verify env) then begin
(let _153_643 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi)))
in (FStar_TypeChecker_Rel.force_trivial_guard env _153_643))
end else begin
()
end
in (

let ses = (FStar_List.fold_left (fun l _59_1255 -> (match (_59_1255) with
| (lid, fml) -> begin
(

let se = (tc_assume env lid fml [] dr)
in (FStar_List.append l ((se)::[])))
end)) [] axioms)
in (

let _59_1258 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq")
in ses)))
end)))
end))))))
end)))))
in (

let unoptimized_haseq_scheme = (fun _59_1261 -> (

let mutuals = (FStar_List.map (fun ty -> (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _59_1266, _59_1268, _59_1270, _59_1272, _59_1274, _59_1276, _59_1278) -> begin
lid
end
| _59_1282 -> begin
(FStar_All.failwith "Impossible!")
end)) tcs)
in (

let haseq_ty = (fun usubst us acc ty -> (

let _59_1309 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _59_1291, bs, t, _59_1295, d_lids, _59_1298, _59_1300) -> begin
((lid), (bs), (t), (d_lids))
end
| _59_1304 -> begin
(FStar_All.failwith "Impossible!")
end)
in (match (_59_1309) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _153_657 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _153_657 t))
in (

let _59_1314 = (FStar_Syntax_Subst.open_term bs t)
in (match (_59_1314) with
| (bs, t) -> begin
(

let ibs = (match ((let _153_658 = (FStar_Syntax_Subst.compress t)
in _153_658.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _59_1317) -> begin
ibs
end
| _59_1321 -> begin
[]
end)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _153_661 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _153_660 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _153_661 _153_660)))
in (

let ind = (let _153_664 = (FStar_List.map (fun _59_1328 -> (match (_59_1328) with
| (bv, aq) -> begin
(let _153_663 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_153_663), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _153_664 None dr))
in (

let ind = (let _153_667 = (FStar_List.map (fun _59_1332 -> (match (_59_1332) with
| (bv, aq) -> begin
(let _153_666 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_153_666), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _153_667 None dr))
in (

let haseq_ind = (let _153_669 = (let _153_668 = (FStar_Syntax_Syntax.as_arg ind)
in (_153_668)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _153_669 None dr))
in (

let rec is_mutual = (fun t -> (match ((let _153_673 = (FStar_Syntax_Subst.compress t)
in _153_673.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.existsb (fun lid -> (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) mutuals)
end
| FStar_Syntax_Syntax.Tm_uinst (t', _59_1343) -> begin
(is_mutual t')
end
| FStar_Syntax_Syntax.Tm_refine (bv, t') -> begin
(is_mutual bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_app (t', args) -> begin
if (is_mutual t') then begin
true
end else begin
(let _153_675 = (FStar_List.map Prims.fst args)
in (exists_mutual _153_675))
end
end
| FStar_Syntax_Syntax.Tm_meta (t', _59_1356) -> begin
(is_mutual t')
end
| _59_1360 -> begin
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
in (match ((let _153_681 = (FStar_Syntax_Subst.compress dt)
in _153_681.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _59_1373) -> begin
(

let dbs = (let _153_682 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _153_682))
in (

let dbs = (let _153_683 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _153_683 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let sort = (Prims.fst b).FStar_Syntax_Syntax.sort
in (

let haseq_sort = (let _153_687 = (let _153_686 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_153_686)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _153_687 None dr))
in (

let haseq_sort = if (is_mutual sort) then begin
(FStar_Syntax_Util.mk_imp haseq_ind haseq_sort)
end else begin
haseq_sort
end
in (FStar_Syntax_Util.mk_conj t haseq_sort))))) FStar_Syntax_Util.t_true dbs)
in (

let cond = (FStar_List.fold_right (fun b t -> (let _153_693 = (let _153_692 = (let _153_691 = (let _153_690 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _153_690 None))
in (FStar_Syntax_Syntax.as_arg _153_691))
in (_153_692)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _153_693 None dr))) dbs cond)
in (FStar_Syntax_Util.mk_conj acc cond))))))
end
| _59_1389 -> begin
acc
end))))
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (_59_1392, _59_1394, _59_1396, t_lid, _59_1399, _59_1401, _59_1403, _59_1405) -> begin
(t_lid = lid)
end
| _59_1409 -> begin
(FStar_All.failwith "Impossible")
end)) datas)
in (

let data_cond = (FStar_List.fold_left haseq_data FStar_Syntax_Util.t_true t_datas)
in (

let fml = (FStar_Syntax_Util.mk_imp data_cond haseq_ind)
in (

let fml = (

let _59_1413 = fml
in (let _153_700 = (let _153_699 = (let _153_698 = (let _153_697 = (let _153_696 = (let _153_695 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_153_695)::[])
in (_153_696)::[])
in FStar_Syntax_Syntax.Meta_pattern (_153_697))
in ((fml), (_153_698)))
in FStar_Syntax_Syntax.Tm_meta (_153_699))
in {FStar_Syntax_Syntax.n = _153_700; FStar_Syntax_Syntax.tk = _59_1413.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _59_1413.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _59_1413.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _153_706 = (let _153_705 = (let _153_704 = (let _153_703 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _153_703 None))
in (FStar_Syntax_Syntax.as_arg _153_704))
in (_153_705)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _153_706 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _153_712 = (let _153_711 = (let _153_710 = (let _153_709 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _153_709 None))
in (FStar_Syntax_Syntax.as_arg _153_710))
in (_153_711)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _153_712 None dr))) bs fml)
in (FStar_Syntax_Util.mk_conj acc fml)))))))))))))))
end))))
end)))
in (

let _59_1443 = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, _59_1426, _59_1428, _59_1430, _59_1432, _59_1434, _59_1436) -> begin
((lid), (us))
end
| _59_1440 -> begin
(FStar_All.failwith "Impossible!")
end))
in (match (_59_1443) with
| (lid, us) -> begin
(

let _59_1446 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (_59_1446) with
| (usubst, us) -> begin
(

let fml = (FStar_List.fold_left (haseq_ty usubst us) FStar_Syntax_Util.t_true tcs)
in (

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (

let _59_1449 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq")
in (

let _59_1451 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle)
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let se = (let _153_713 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (tc_assume env _153_713 fml [] dr))
in (

let _59_1455 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq")
in (se)::[])))))))
end))
end)))))
in (

let skip_prims_type = (fun _59_1458 -> (

let lid = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _59_1463, _59_1465, _59_1467, _59_1469, _59_1471, _59_1473, _59_1475) -> begin
lid
end
| _59_1479 -> begin
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
in (let _153_721 = (let _153_720 = (let _153_719 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_153_719)))
in FStar_Syntax_Syntax.Sig_bundle (_153_720))
in (_153_721)::ses)))
end)))))))
end))
end))
end))))
end)))))))))
and tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env se -> (

let env = (set_hint_correlator env se)
in (

let _59_1491 = (FStar_TypeChecker_Util.check_sigelt_quals se)
in (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let se = (tc_lex_t env ses quals lids)
in (let _153_724 = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (_153_724)))))
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

let _59_1531 = (set_options FStar_Options.Set o)
in (((se)::[]), (env)))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(

let _59_1535 = (let _153_731 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _153_731 Prims.ignore))
in (

let _59_1540 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (

let _59_1542 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (((se)::[]), (env)))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_59_1545) -> begin
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

let _59_1561 = (FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun _59_1556 a -> (match (_59_1556) with
| (env, ses) -> begin
(

let se_let = (FStar_Syntax_Util.action_as_lb a)
in (let _153_734 = (FStar_TypeChecker_Env.push_sigelt env se_let)
in ((_153_734), ((se_let)::ses))))
end)) ((env), ((se)::[]))))
in (match (_59_1561) with
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

let _59_1570 = (let _153_735 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _153_735))
in (match (_59_1570) with
| (a, wp_a_src) -> begin
(

let _59_1573 = (let _153_736 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _153_736))
in (match (_59_1573) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (let _153_740 = (let _153_739 = (let _153_738 = (let _153_737 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (_153_737)))
in FStar_Syntax_Syntax.NT (_153_738))
in (_153_739)::[])
in (FStar_Syntax_Subst.subst _153_740 wp_b_tgt))
in (

let expected_k = (let _153_745 = (let _153_743 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_742 = (let _153_741 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_153_741)::[])
in (_153_743)::_153_742))
in (let _153_744 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _153_745 _153_744)))
in (

let repr_type = (fun eff_name a wp -> (

let no_reify = (fun l -> (let _153_757 = (let _153_756 = (let _153_755 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _153_754 = (FStar_TypeChecker_Env.get_range env)
in ((_153_755), (_153_754))))
in FStar_Syntax_Syntax.Error (_153_756))
in (Prims.raise _153_757)))
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
(let _153_764 = (let _153_762 = (let _153_761 = (let _153_760 = (FStar_Syntax_Syntax.as_arg a)
in (let _153_759 = (let _153_758 = (FStar_Syntax_Syntax.as_arg wp)
in (_153_758)::[])
in (_153_760)::_153_759))
in ((repr), (_153_761)))
in FStar_Syntax_Syntax.Tm_app (_153_762))
in (let _153_763 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _153_764 None _153_763)))
end)
end)))
in (

let _59_1614 = (match (((sub.FStar_Syntax_Syntax.lift), (sub.FStar_Syntax_Syntax.lift_wp))) with
| (None, None) -> begin
(FStar_All.failwith "Impossible")
end
| (lift, Some (_59_1591, lift_wp)) -> begin
(let _153_765 = (check_and_gen env lift_wp expected_k)
in ((lift), (_153_765)))
end
| (Some (what, lift), None) -> begin
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange))
in (

let _59_1607 = (FStar_TypeChecker_DMFF.star_expr dmff_env lift)
in (match (_59_1607) with
| (_59_1604, lift_wp, lift_elab) -> begin
(

let _59_1608 = (recheck_debug "lift-wp" env lift_wp)
in (

let _59_1610 = (recheck_debug "lift-elab" env lift_elab)
in ((Some ((([]), (lift_elab)))), ((([]), (lift_wp))))))
end)))
end)
in (match (_59_1614) with
| (lift, lift_wp) -> begin
(

let lift = (match (sub.FStar_Syntax_Syntax.lift) with
| None -> begin
None
end
| Some (_59_1617, lift) -> begin
(

let _59_1623 = (let _153_766 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _153_766))
in (match (_59_1623) with
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

let lift_wp_a = (let _153_773 = (let _153_771 = (let _153_770 = (let _153_769 = (FStar_Syntax_Syntax.as_arg a_typ)
in (let _153_768 = (let _153_767 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (_153_767)::[])
in (_153_769)::_153_768))
in (((Prims.snd lift_wp)), (_153_770)))
in FStar_Syntax_Syntax.Tm_app (_153_771))
in (let _153_772 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _153_773 None _153_772)))
in (repr_type sub.FStar_Syntax_Syntax.target a_typ lift_wp_a))
in (

let expected_k = (let _153_780 = (let _153_778 = (FStar_Syntax_Syntax.mk_binder a)
in (let _153_777 = (let _153_776 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (let _153_775 = (let _153_774 = (FStar_Syntax_Syntax.null_binder repr_f)
in (_153_774)::[])
in (_153_776)::_153_775))
in (_153_778)::_153_777))
in (let _153_779 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow _153_780 _153_779)))
in (

let _59_1636 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (_59_1636) with
| (expected_k, _59_1633, _59_1635) -> begin
(

let lift = (check_and_gen env lift expected_k)
in Some (lift))
end))))))))
end))
end)
in (

let sub = (

let _59_1639 = sub
in {FStar_Syntax_Syntax.source = _59_1639.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _59_1639.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = Some (lift_wp); FStar_Syntax_Syntax.lift = lift})
in (

let se = FStar_Syntax_Syntax.Sig_sub_effect (((sub), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (env))))))
end)))))
end))
end))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, tags, r) -> begin
(

let _59_1652 = ()
in (

let env0 = env
in (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _59_1658 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_59_1658) with
| (tps, c) -> begin
(

let _59_1662 = (tc_tparams env tps)
in (match (_59_1662) with
| (tps, env, us) -> begin
(

let _59_1666 = (FStar_TypeChecker_TcTerm.tc_comp env c)
in (match (_59_1666) with
| (c, u, g) -> begin
(

let _59_1667 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

let _59_1673 = (let _153_781 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _153_781))
in (match (_59_1673) with
| (uvs, t) -> begin
(

let _59_1692 = (match ((let _153_783 = (let _153_782 = (FStar_Syntax_Subst.compress t)
in _153_782.FStar_Syntax_Syntax.n)
in ((tps), (_153_783)))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_59_1676, c)) -> begin
(([]), (c))
end
| (_59_1682, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
((tps), (c))
end
| _59_1689 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_59_1692) with
| (tps, c) -> begin
(

let _59_1693 = if (((FStar_List.length uvs) <> (Prims.parse_int "1")) && (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid)))) then begin
(let _153_788 = (let _153_787 = (let _153_786 = (let _153_785 = (FStar_Syntax_Print.lid_to_string lid)
in (let _153_784 = (FStar_All.pipe_right (FStar_List.length uvs) FStar_Util.string_of_int)
in (FStar_Util.format2 "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes" _153_785 _153_784)))
in ((_153_786), (r)))
in FStar_Syntax_Syntax.Error (_153_787))
in (Prims.raise _153_788))
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

let _59_1705 = ()
in (

let _59_1709 = (let _153_790 = (let _153_789 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _153_789))
in (check_and_gen env t _153_790))
in (match (_59_1709) with
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

let _59_1729 = (FStar_TypeChecker_TcTerm.tc_term env e)
in (match (_59_1729) with
| (e, c, g1) -> begin
(

let _59_1734 = (let _153_794 = (let _153_791 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_153_791))
in (let _153_793 = (let _153_792 = (c.FStar_Syntax_Syntax.comp ())
in ((e), (_153_792)))
in (FStar_TypeChecker_TcTerm.check_expected_effect env _153_794 _153_793)))
in (match (_59_1734) with
| (e, _59_1732, g) -> begin
(

let _59_1735 = (let _153_795 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _153_795))
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
(let _153_807 = (let _153_806 = (let _153_805 = (let _153_804 = (FStar_Syntax_Print.lid_to_string l)
in (let _153_803 = (FStar_Syntax_Print.quals_to_string q)
in (let _153_802 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _153_804 _153_803 _153_802))))
in ((_153_805), (r)))
in FStar_Syntax_Syntax.Error (_153_806))
in (Prims.raise _153_807))
end
end))
in (

let _59_1779 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _59_1756 lb -> (match (_59_1756) with
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _59_1775 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
((gen), (lb), (quals_opt))
end
| Some ((uvs, tval), quals) -> begin
(

let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (

let _59_1770 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _59_1769 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _153_810 = (FStar_Syntax_Syntax.mk_lb ((FStar_Util.Inr (lbname)), (uvs), (FStar_Syntax_Const.effect_ALL_lid), (tval), (lb.FStar_Syntax_Syntax.lbdef)))
in ((false), (_153_810), (quals_opt)))))
end)
in (match (_59_1775) with
| (gen, lb, quals_opt) -> begin
((gen), ((lb)::lbs), (quals_opt))
end)))
end)) ((true), ([]), (if (quals = []) then begin
None
end else begin
Some (quals)
end))))
in (match (_59_1779) with
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
| _59_1788 -> begin
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

let e = (let _153_814 = (let _153_813 = (let _153_812 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((((Prims.fst lbs)), (lbs'))), (_153_812)))
in FStar_Syntax_Syntax.Tm_let (_153_813))
in (FStar_Syntax_Syntax.mk _153_814 None r))
in (

let _59_1822 = (match ((FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term (

let _59_1792 = env
in {FStar_TypeChecker_Env.solver = _59_1792.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_1792.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_1792.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_1792.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_1792.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_1792.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_1792.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_1792.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_1792.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_1792.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_1792.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _59_1792.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _59_1792.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_1792.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_1792.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_1792.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_1792.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _59_1792.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_1792.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_1792.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_1792.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_1792.FStar_TypeChecker_Env.qname_and_index}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _59_1799; FStar_Syntax_Syntax.pos = _59_1797; FStar_Syntax_Syntax.vars = _59_1795}, _59_1806, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_59_1810, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _59_1816 -> begin
quals
end)
in ((FStar_Syntax_Syntax.Sig_let (((lbs), (r), (lids), (quals)))), (lbs)))
end
| _59_1819 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_59_1822) with
| (se, lbs) -> begin
(

let _59_1828 = if (log env) then begin
(let _153_822 = (let _153_821 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (match ((let _153_818 = (let _153_817 = (let _153_816 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _153_816.FStar_Syntax_Syntax.fv_name)
in _153_817.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _153_818))) with
| None -> begin
true
end
| _59_1826 -> begin
false
end)
in if should_log then begin
(let _153_820 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _153_819 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _153_820 _153_819)))
end else begin
""
end))))
in (FStar_All.pipe_right _153_821 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _153_822))
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
| _59_1838 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _59_1848 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_59_1850) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _59_1861, r) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _59_1868 -> (match (_59_1868) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _59_1874, _59_1876, quals, r) -> begin
(

let dec = (let _153_836 = (let _153_835 = (let _153_834 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow bs _153_834))
in ((l), (us), (_153_835), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (_153_836))
in (((dec)::out), (hidden)))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _59_1886, _59_1888, _59_1890, _59_1892, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]), (r)))
in (((dec)::out), ((l)::hidden)))
end
| _59_1898 -> begin
((out), (hidden))
end)
end)) ses (([]), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end
| FStar_Syntax_Syntax.Sig_assume (_59_1900, _59_1902, quals, _59_1905) -> begin
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
| _59_1924 -> begin
false
end)))) then begin
(((se)::[]), (hidden))
end else begin
(([]), (hidden))
end
end
end
| FStar_Syntax_Syntax.Sig_main (_59_1926) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _59_1945, _59_1947, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
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
(let _153_843 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _153_842 = (let _153_841 = (let _153_840 = (let _153_839 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _153_839.FStar_Syntax_Syntax.fv_name)
in _153_840.FStar_Syntax_Syntax.v)
in ((_153_841), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (_153_842)))))
in ((_153_843), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let process_one_decl = (fun _59_1968 se -> (match (_59_1968) with
| (ses, exports, env, hidden) -> begin
(

let _59_1970 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_852 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _153_852))
end else begin
()
end
in (

let _59_1974 = (tc_decl env se)
in (match (_59_1974) with
| (ses', env) -> begin
(

let _59_1977 = if ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _153_857 = (FStar_List.fold_left (fun s se -> (let _153_856 = (let _153_855 = (FStar_Syntax_Print.sigelt_to_string se)
in (Prims.strcat _153_855 "\n"))
in (Prims.strcat s _153_856))) "" ses')
in (FStar_Util.print1 "Checked: %s\n" _153_857))
end else begin
()
end
in (

let _59_1980 = (FStar_List.iter (fun se -> (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)) ses')
in (

let _59_1989 = (FStar_List.fold_left (fun _59_1984 se -> (match (_59_1984) with
| (le, lh) -> begin
(

let tup = (for_export hidden se)
in (((FStar_List.rev_append (Prims.fst tup) le)), ((FStar_List.rev_append (Prims.snd tup) lh))))
end)) (([]), ([])) ses')
in (match (_59_1989) with
| (exported, hidden) -> begin
(((FStar_List.rev_append ses' ses)), (((FStar_List.rev_append exported []))::exports), (env), (hidden))
end))))
end)))
end))
in (

let _59_2015 = (FStar_List.fold_left (fun acc se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, r) -> begin
(

let _59_2003 = acc
in (match (_59_2003) with
| (_59_1997, _59_1999, env, _59_2002) -> begin
(

let _59_2006 = (cps_and_elaborate env ne)
in (match (_59_2006) with
| (ses, ne) -> begin
(

let ses = (FStar_List.append ses ((FStar_Syntax_Syntax.Sig_new_effect (((ne), (r))))::[]))
in (FStar_List.fold_left process_one_decl acc ses))
end))
end))
end
| _59_2009 -> begin
(process_one_decl acc se)
end)) (([]), ([]), (env), ([])) ses)
in (match (_59_2015) with
| (ses, exports, env, _59_2014) -> begin
(let _153_863 = (FStar_All.pipe_right (FStar_List.rev_append exports []) FStar_List.flatten)
in (((FStar_List.rev_append ses [])), (_153_863), (env)))
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

let _59_2020 = env
in (let _153_868 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _59_2020.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_2020.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_2020.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_2020.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_2020.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_2020.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_2020.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_2020.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_2020.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_2020.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_2020.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_2020.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_2020.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_2020.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_2020.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_2020.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _153_868; FStar_TypeChecker_Env.lax = _59_2020.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _59_2020.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_2020.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_2020.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_2020.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_2020.FStar_TypeChecker_Env.qname_and_index}))
in (

let _59_2023 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
in (

let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

let _59_2029 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_59_2029) with
| (ses, exports, env) -> begin
(((

let _59_2030 = modul
in {FStar_Syntax_Syntax.name = _59_2030.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _59_2030.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _59_2030.FStar_Syntax_Syntax.is_interface})), (exports), (env))
end))))))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let _59_2038 = (tc_decls env decls)
in (match (_59_2038) with
| (ses, exports, env) -> begin
(

let modul = (

let _59_2039 = modul
in {FStar_Syntax_Syntax.name = _59_2039.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _59_2039.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _59_2039.FStar_Syntax_Syntax.is_interface})
in ((modul), (exports), (env)))
end)))


let check_exports : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env modul exports -> (

let env = (

let _59_2045 = env
in {FStar_TypeChecker_Env.solver = _59_2045.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_2045.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_2045.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_2045.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_2045.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_2045.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_2045.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_2045.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_2045.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_2045.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_2045.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_2045.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_2045.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _59_2045.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_2045.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_2045.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_2045.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = true; FStar_TypeChecker_Env.type_of = _59_2045.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_2045.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_2045.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_2045.FStar_TypeChecker_Env.qname_and_index})
in (

let check_term = (fun lid univs t -> (

let _59_2054 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_59_2054) with
| (univs, t) -> begin
(

let _59_2056 = if (let _153_888 = (let _153_887 = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (FStar_TypeChecker_Env.debug _153_887))
in (FStar_All.pipe_left _153_888 (FStar_Options.Other ("Exports")))) then begin
(let _153_893 = (FStar_Syntax_Print.lid_to_string lid)
in (let _153_892 = (let _153_890 = (FStar_All.pipe_right univs (FStar_List.map (fun x -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (x))))))
in (FStar_All.pipe_right _153_890 (FStar_String.concat ", ")))
in (let _153_891 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print3 "Checking for export %s <%s> : %s\n" _153_893 _153_892 _153_891))))
end else begin
()
end
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env univs)
in (let _153_894 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env t)
in (FStar_All.pipe_right _153_894 Prims.ignore))))
end)))
in (

let check_term = (fun lid univs t -> (

let _59_2063 = (let _153_903 = (let _153_902 = (FStar_Syntax_Print.lid_to_string modul.FStar_Syntax_Syntax.name)
in (let _153_901 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Interface of %s violates its abstraction (add a \'private\' qualifier to \'%s\'?)" _153_902 _153_901)))
in (FStar_TypeChecker_Errors.message_prefix.FStar_TypeChecker_Errors.set_prefix _153_903))
in (

let _59_2065 = (check_term lid univs t)
in (FStar_TypeChecker_Errors.message_prefix.FStar_TypeChecker_Errors.clear_prefix ()))))
in (

let rec check_sigelt = (fun _59_11 -> (match (_59_11) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _59_2072, _59_2074) -> begin
if (not ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private)))) then begin
(FStar_All.pipe_right ses (FStar_List.iter check_sigelt))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_inductive_typ (l, univs, binders, typ, _59_2082, _59_2084, _59_2086, r) -> begin
(

let t = (let _153_908 = (let _153_907 = (let _153_906 = (FStar_Syntax_Syntax.mk_Total typ)
in ((binders), (_153_906)))
in FStar_Syntax_Syntax.Tm_arrow (_153_907))
in (FStar_Syntax_Syntax.mk _153_908 None r))
in (check_term l univs t))
end
| FStar_Syntax_Syntax.Sig_datacon (l, univs, t, _59_2095, _59_2097, _59_2099, _59_2101, _59_2103) -> begin
(check_term l univs t)
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, univs, t, quals, _59_2111) -> begin
if (not ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private)))) then begin
(check_term l univs t)
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_let ((_59_2115, lbs), _59_2119, _59_2121, quals) -> begin
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

let _59_2157 = modul
in {FStar_Syntax_Syntax.name = _59_2157.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _59_2157.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module env modul)
in (

let _59_2161 = (check_exports env modul exports)
in (

let _59_2163 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (

let _59_2165 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (

let _59_2167 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (

let _59_2169 = (let _153_916 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _153_916 Prims.ignore))
in ((modul), (env))))))))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let _59_2176 = (tc_partial_modul env modul)
in (match (_59_2176) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (

let _59_2179 = if (FStar_Options.debug_any ()) then begin
(let _153_925 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _153_925))
end else begin
()
end
in (

let _59_2183 = (tc_modul env m)
in (match (_59_2183) with
| (m, env) -> begin
(

let _59_2184 = if (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _153_926 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _153_926))
end else begin
()
end
in ((m), (env)))
end))))




