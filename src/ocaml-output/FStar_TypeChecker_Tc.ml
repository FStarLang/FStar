
open Prims

let set_hint_correlator : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env = (fun env se -> (match ((FStar_Options.reuse_hint_for ())) with
| Some (l) -> begin
(

let lid = (let _154_5 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_add_suffix _154_5 l))
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
(let _154_8 = (FStar_TypeChecker_Env.current_module env)
in (let _154_7 = (let _154_6 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_right _154_6 FStar_Util.string_of_int))
in (FStar_Ident.lid_add_suffix _154_8 _154_7)))
end
| (l)::_59_23 -> begin
l
end)
in (

let _59_27 = env
in {FStar_TypeChecker_Env.solver = _59_27.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_27.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_27.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_27.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_27.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_27.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_27.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_27.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_27.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_27.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_27.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_27.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_27.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_27.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_27.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_27.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_27.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_27.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_27.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _59_27.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_27.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_27.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_27.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), ((Prims.parse_int "0"))))})))
end))


let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_Options.log_types ()) && (not ((let _154_11 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _154_11))))))


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
(let _154_24 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Term has been %s-transformed to:\n%s\n----------\n" s _154_24))
end else begin
()
end
in (

let _59_51 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (_59_51) with
| (t', _59_48, _59_50) -> begin
(

let _59_52 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _154_25 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print1 "Re-checked; got:\n%s\n----------\n" _154_25))
end else begin
()
end
in t)
end))))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _154_32 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _154_32)))


let check_nogen = (fun env t k -> (

let t = (tc_check_trivial_guard env t k)
in (let _154_36 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (([]), (_154_36)))))


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
(let _154_51 = (let _154_50 = (let _154_49 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env m s)
in ((_154_49), ((FStar_Ident.range_of_lid m))))
in FStar_Syntax_Syntax.Error (_154_50))
in (Prims.raise _154_51))
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
(match ((let _154_58 = (FStar_Syntax_Subst.compress t')
in _154_58.FStar_Syntax_Syntax.n)) with
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
in (let _154_101 = (op ed.FStar_Syntax_Syntax.ret_wp)
in (let _154_100 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _154_99 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _154_98 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _154_97 = (op ed.FStar_Syntax_Syntax.stronger)
in (let _154_96 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _154_95 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _154_94 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _154_93 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _154_92 = (op ed.FStar_Syntax_Syntax.trivial)
in (let _154_91 = (let _154_82 = (op (([]), (ed.FStar_Syntax_Syntax.repr)))
in (Prims.snd _154_82))
in (let _154_90 = (op ed.FStar_Syntax_Syntax.return_repr)
in (let _154_89 = (op ed.FStar_Syntax_Syntax.bind_repr)
in (let _154_88 = (FStar_List.map (fun a -> (

let _59_144 = a
in (let _154_87 = (let _154_84 = (op (([]), (a.FStar_Syntax_Syntax.action_defn)))
in (Prims.snd _154_84))
in (let _154_86 = (let _154_85 = (op (([]), (a.FStar_Syntax_Syntax.action_typ)))
in (Prims.snd _154_85))
in {FStar_Syntax_Syntax.action_name = _59_144.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = _59_144.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = _59_144.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = _154_87; FStar_Syntax_Syntax.action_typ = _154_86})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.qualifiers = _59_141.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _59_141.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _59_141.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _59_141.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _59_141.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _154_101; FStar_Syntax_Syntax.bind_wp = _154_100; FStar_Syntax_Syntax.if_then_else = _154_99; FStar_Syntax_Syntax.ite_wp = _154_98; FStar_Syntax_Syntax.stronger = _154_97; FStar_Syntax_Syntax.close_wp = _154_96; FStar_Syntax_Syntax.assert_p = _154_95; FStar_Syntax_Syntax.assume_p = _154_94; FStar_Syntax_Syntax.null_wp = _154_93; FStar_Syntax_Syntax.trivial = _154_92; FStar_Syntax_Syntax.repr = _154_91; FStar_Syntax_Syntax.return_repr = _154_90; FStar_Syntax_Syntax.bind_repr = _154_89; FStar_Syntax_Syntax.actions = _154_88}))))))))))))))))
end)
in (

let wp_with_fresh_result_type = (fun env mname signature -> (

let fail = (fun t -> (let _154_112 = (let _154_111 = (let _154_110 = (FStar_TypeChecker_Errors.unexpected_signature_for_monad env mname t)
in ((_154_110), ((FStar_Ident.range_of_lid mname))))
in FStar_Syntax_Syntax.Error (_154_111))
in (Prims.raise _154_112)))
in (match ((let _154_113 = (FStar_Syntax_Subst.compress signature)
in _154_113.FStar_Syntax_Syntax.n)) with
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

let env = (let _154_116 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _154_116))
in (

let _59_181 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _154_122 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _154_121 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _154_120 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _154_119 = (let _154_117 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Print.term_to_string _154_117))
in (let _154_118 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.sort)
in (FStar_Util.print5 "Checking effect signature: %s %s : %s\n(a is %s:%s)\n" _154_122 _154_121 _154_120 _154_119 _154_118))))))
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

let expected_k = (let _154_134 = (let _154_132 = (FStar_Syntax_Syntax.mk_binder a)
in (let _154_131 = (let _154_130 = (let _154_129 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _154_129))
in (_154_130)::[])
in (_154_132)::_154_131))
in (let _154_133 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _154_134 _154_133)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret_wp expected_k))
in (

let bind_wp = (

let _59_194 = (fresh_effect_signature ())
in (match (_59_194) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _154_138 = (let _154_136 = (let _154_135 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _154_135))
in (_154_136)::[])
in (let _154_137 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _154_138 _154_137)))
in (

let expected_k = (let _154_149 = (let _154_147 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _154_146 = (let _154_145 = (FStar_Syntax_Syntax.mk_binder a)
in (let _154_144 = (let _154_143 = (FStar_Syntax_Syntax.mk_binder b)
in (let _154_142 = (let _154_141 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _154_140 = (let _154_139 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (_154_139)::[])
in (_154_141)::_154_140))
in (_154_143)::_154_142))
in (_154_145)::_154_144))
in (_154_147)::_154_146))
in (let _154_148 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _154_149 _154_148)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else = (

let p = (let _154_151 = (let _154_150 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _154_150 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _154_151))
in (

let expected_k = (let _154_160 = (let _154_158 = (FStar_Syntax_Syntax.mk_binder a)
in (let _154_157 = (let _154_156 = (FStar_Syntax_Syntax.mk_binder p)
in (let _154_155 = (let _154_154 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _154_153 = (let _154_152 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_154_152)::[])
in (_154_154)::_154_153))
in (_154_156)::_154_155))
in (_154_158)::_154_157))
in (let _154_159 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _154_160 _154_159)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (let _154_165 = (let _154_163 = (FStar_Syntax_Syntax.mk_binder a)
in (let _154_162 = (let _154_161 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_154_161)::[])
in (_154_163)::_154_162))
in (let _154_164 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _154_165 _154_164)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let _59_206 = (FStar_Syntax_Util.type_u ())
in (match (_59_206) with
| (t, _59_205) -> begin
(

let expected_k = (let _154_172 = (let _154_170 = (FStar_Syntax_Syntax.mk_binder a)
in (let _154_169 = (let _154_168 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _154_167 = (let _154_166 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_154_166)::[])
in (_154_168)::_154_167))
in (_154_170)::_154_169))
in (let _154_171 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _154_172 _154_171)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (let _154_174 = (let _154_173 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _154_173 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _154_174))
in (

let b_wp_a = (let _154_178 = (let _154_176 = (let _154_175 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _154_175))
in (_154_176)::[])
in (let _154_177 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _154_178 _154_177)))
in (

let expected_k = (let _154_185 = (let _154_183 = (FStar_Syntax_Syntax.mk_binder a)
in (let _154_182 = (let _154_181 = (FStar_Syntax_Syntax.mk_binder b)
in (let _154_180 = (let _154_179 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_154_179)::[])
in (_154_181)::_154_180))
in (_154_183)::_154_182))
in (let _154_184 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _154_185 _154_184)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (let _154_194 = (let _154_192 = (FStar_Syntax_Syntax.mk_binder a)
in (let _154_191 = (let _154_190 = (let _154_187 = (let _154_186 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _154_186 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _154_187))
in (let _154_189 = (let _154_188 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_154_188)::[])
in (_154_190)::_154_189))
in (_154_192)::_154_191))
in (let _154_193 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _154_194 _154_193)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (let _154_203 = (let _154_201 = (FStar_Syntax_Syntax.mk_binder a)
in (let _154_200 = (let _154_199 = (let _154_196 = (let _154_195 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _154_195 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _154_196))
in (let _154_198 = (let _154_197 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_154_197)::[])
in (_154_199)::_154_198))
in (_154_201)::_154_200))
in (let _154_202 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _154_203 _154_202)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (let _154_206 = (let _154_204 = (FStar_Syntax_Syntax.mk_binder a)
in (_154_204)::[])
in (let _154_205 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _154_206 _154_205)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let _59_222 = (FStar_Syntax_Util.type_u ())
in (match (_59_222) with
| (t, _59_221) -> begin
(

let expected_k = (let _154_211 = (let _154_209 = (FStar_Syntax_Syntax.mk_binder a)
in (let _154_208 = (let _154_207 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_154_207)::[])
in (_154_209)::_154_208))
in (let _154_210 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _154_211 _154_210)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let _59_381 = (match ((let _154_212 = (FStar_Syntax_Subst.compress ed.FStar_Syntax_Syntax.repr)
in _154_212.FStar_Syntax_Syntax.n)) with
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

let expected_k = (let _154_217 = (let _154_215 = (FStar_Syntax_Syntax.mk_binder a)
in (let _154_214 = (let _154_213 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_154_213)::[])
in (_154_215)::_154_214))
in (let _154_216 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _154_217 _154_216)))
in (tc_check_trivial_guard env ed.FStar_Syntax_Syntax.repr expected_k))
end))
in (

let mk_repr' = (fun t wp -> (

let repr = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env repr)
in (let _154_227 = (let _154_226 = (let _154_225 = (let _154_224 = (FStar_Syntax_Syntax.as_arg t)
in (let _154_223 = (let _154_222 = (FStar_Syntax_Syntax.as_arg wp)
in (_154_222)::[])
in (_154_224)::_154_223))
in ((repr), (_154_225)))
in FStar_Syntax_Syntax.Tm_app (_154_226))
in (FStar_Syntax_Syntax.mk _154_227 None FStar_Range.dummyRange))))
in (

let mk_repr = (fun a wp -> (let _154_232 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_repr' _154_232 wp)))
in (

let destruct_repr = (fun t -> (match ((let _154_235 = (FStar_Syntax_Subst.compress t)
in _154_235.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_59_244, ((t, _59_251))::((wp, _59_247))::[]) -> begin
((t), (wp))
end
| _59_257 -> begin
(FStar_All.failwith "Unexpected repr type")
end))
in (

let bind_repr = (

let r = (let _154_236 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_0 FStar_Syntax_Syntax.Delta_constant None)
in (FStar_All.pipe_right _154_236 FStar_Syntax_Syntax.fv_to_tm))
in (

let _59_261 = (fresh_effect_signature ())
in (match (_59_261) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _154_240 = (let _154_238 = (let _154_237 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _154_237))
in (_154_238)::[])
in (let _154_239 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _154_240 _154_239)))
in (

let wp_f = (FStar_Syntax_Syntax.gen_bv "wp_f" None wp_a)
in (

let wp_g = (FStar_Syntax_Syntax.gen_bv "wp_g" None a_wp_b)
in (

let x_a = (let _154_241 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _154_241))
in (

let wp_g_x = (let _154_245 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (let _154_244 = (let _154_243 = (let _154_242 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _154_242))
in (_154_243)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _154_245 _154_244 None FStar_Range.dummyRange)))
in (

let res = (

let wp = (let _154_257 = (let _154_246 = (FStar_TypeChecker_Env.inst_tscheme bind_wp)
in (FStar_All.pipe_right _154_246 Prims.snd))
in (let _154_256 = (let _154_255 = (let _154_254 = (let _154_253 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _154_252 = (let _154_251 = (FStar_Syntax_Syntax.bv_to_name b)
in (let _154_250 = (let _154_249 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (let _154_248 = (let _154_247 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (_154_247)::[])
in (_154_249)::_154_248))
in (_154_251)::_154_250))
in (_154_253)::_154_252))
in (r)::_154_254)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _154_255))
in (FStar_Syntax_Syntax.mk_Tm_app _154_257 _154_256 None FStar_Range.dummyRange)))
in (mk_repr b wp))
in (

let expected_k = (let _154_277 = (let _154_275 = (FStar_Syntax_Syntax.mk_binder a)
in (let _154_274 = (let _154_273 = (FStar_Syntax_Syntax.mk_binder b)
in (let _154_272 = (let _154_271 = (FStar_Syntax_Syntax.mk_binder wp_f)
in (let _154_270 = (let _154_269 = (let _154_259 = (let _154_258 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (mk_repr a _154_258))
in (FStar_Syntax_Syntax.null_binder _154_259))
in (let _154_268 = (let _154_267 = (FStar_Syntax_Syntax.mk_binder wp_g)
in (let _154_266 = (let _154_265 = (let _154_264 = (let _154_263 = (let _154_260 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_154_260)::[])
in (let _154_262 = (let _154_261 = (mk_repr b wp_g_x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _154_261))
in (FStar_Syntax_Util.arrow _154_263 _154_262)))
in (FStar_Syntax_Syntax.null_binder _154_264))
in (_154_265)::[])
in (_154_267)::_154_266))
in (_154_269)::_154_268))
in (_154_271)::_154_270))
in (_154_273)::_154_272))
in (_154_275)::_154_274))
in (let _154_276 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _154_277 _154_276)))
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

let x_a = (let _154_278 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _154_278))
in (

let res = (

let wp = (let _154_285 = (let _154_279 = (FStar_TypeChecker_Env.inst_tscheme return_wp)
in (FStar_All.pipe_right _154_279 Prims.snd))
in (let _154_284 = (let _154_283 = (let _154_282 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _154_281 = (let _154_280 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (_154_280)::[])
in (_154_282)::_154_281))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _154_283))
in (FStar_Syntax_Syntax.mk_Tm_app _154_285 _154_284 None FStar_Range.dummyRange)))
in (mk_repr a wp))
in (

let expected_k = (let _154_290 = (let _154_288 = (FStar_Syntax_Syntax.mk_binder a)
in (let _154_287 = (let _154_286 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_154_286)::[])
in (_154_288)::_154_287))
in (let _154_289 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _154_290 _154_289)))
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

let _59_305 = (FStar_Syntax_Subst.open_term' act.FStar_Syntax_Syntax.action_params act.FStar_Syntax_Syntax.action_typ)
in (match (_59_305) with
| (params_un, act_typ, opening) -> begin
(

let _59_310 = (tc_tparams env params_un)
in (match (_59_310) with
| (params, env, _59_309) -> begin
(

let act_defn = (match (params) with
| [] -> begin
act.FStar_Syntax_Syntax.action_defn
end
| _59_313 -> begin
(FStar_Syntax_Subst.subst opening act.FStar_Syntax_Syntax.action_defn)
end)
in (

let _59_319 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env act_typ)
in (match (_59_319) with
| (act_typ, _59_317, g_t) -> begin
(

let env' = (FStar_TypeChecker_Env.set_expected_typ env act_typ)
in (

let _59_321 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _154_294 = (FStar_Syntax_Print.term_to_string act_defn)
in (let _154_293 = (FStar_Syntax_Print.term_to_string act_typ)
in (FStar_Util.print3 "Checking action %s:\n[definition]: %s\n[cps\'d type]: %s\n" (FStar_Ident.text_of_lid act.FStar_Syntax_Syntax.action_name) _154_294 _154_293)))
end else begin
()
end
in (

let _59_327 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' act_defn)
in (match (_59_327) with
| (act_defn, _59_325, g_a) -> begin
(

let act_defn = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env act_defn)
in (

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
in (

let _59_350 = (

let act_typ = (FStar_Syntax_Subst.compress act_typ)
in (match (act_typ.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _59_338 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_59_338) with
| (bs, _59_337) -> begin
(

let res = (mk_repr' FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun)
in (

let k = (let _154_295 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs _154_295))
in (

let _59_345 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env k)
in (match (_59_345) with
| (k, _59_343, g) -> begin
((k), (g))
end))))
end))
end
| _59_347 -> begin
(let _154_300 = (let _154_299 = (let _154_298 = (let _154_297 = (FStar_Syntax_Print.term_to_string act_typ)
in (let _154_296 = (FStar_Syntax_Print.tag_of_term act_typ)
in (FStar_Util.format2 "Actions must have function types (not: %s, a.k.a. %s)" _154_297 _154_296)))
in ((_154_298), (act_defn.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_154_299))
in (Prims.raise _154_300))
end))
in (match (_59_350) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env act_typ expected_k)
in (

let _59_352 = (let _154_303 = (let _154_302 = (let _154_301 = (FStar_TypeChecker_Rel.conj_guard g_t g)
in (FStar_TypeChecker_Rel.conj_guard g_k _154_301))
in (FStar_TypeChecker_Rel.conj_guard g_a _154_302))
in (FStar_TypeChecker_Rel.force_trivial_guard env _154_303))
in (

let act_typ = (match ((let _154_304 = (FStar_Syntax_Subst.compress expected_k)
in _154_304.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _59_360 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_59_360) with
| (bs, c) -> begin
(

let _59_363 = (destruct_repr (FStar_Syntax_Util.comp_result c))
in (match (_59_363) with
| (a, wp) -> begin
(

let c = (let _154_308 = (let _154_305 = (env.FStar_TypeChecker_Env.universe_of env a)
in (_154_305)::[])
in (let _154_307 = (let _154_306 = (FStar_Syntax_Syntax.as_arg wp)
in (_154_306)::[])
in {FStar_Syntax_Syntax.comp_univs = _154_308; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a; FStar_Syntax_Syntax.effect_args = _154_307; FStar_Syntax_Syntax.flags = []}))
in (let _154_309 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Util.arrow bs _154_309)))
end))
end))
end
| _59_366 -> begin
(FStar_All.failwith "")
end)
in (

let act_defn = (FStar_Syntax_Subst.close params act_defn)
in (

let _59_371 = (FStar_TypeChecker_Util.generalize_universes env act_defn)
in (match (_59_371) with
| (univs, act_defn) -> begin
(

let act_typ = (FStar_Syntax_Subst.close params act_typ)
in (

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
in (

let _59_374 = act
in {FStar_Syntax_Syntax.action_name = _59_374.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_params = params; FStar_Syntax_Syntax.action_defn = act_defn; FStar_Syntax_Syntax.action_typ = act_typ})))
end))))))
end))))
end))))
end)))
end))
end)))
in (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.map check_action)))
in ((repr), (bind_repr), (return_repr), (actions)))))))))
end)
in (match (_59_381) with
| (repr, bind_repr, return_repr, actions) -> begin
(

let t = (let _154_310 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _154_310))
in (

let _59_385 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_59_385) with
| (univs, t) -> begin
(

let signature = (match ((let _154_312 = (let _154_311 = (FStar_Syntax_Subst.compress t)
in _154_311.FStar_Syntax_Syntax.n)
in ((effect_params), (_154_312)))) with
| ([], _59_388) -> begin
t
end
| (_59_391, FStar_Syntax_Syntax.Tm_arrow (_59_393, c)) -> begin
(FStar_Syntax_Util.comp_result c)
end
| _59_399 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let close = (fun n ts -> (

let ts = (let _154_317 = (FStar_Syntax_Subst.close_tscheme effect_params ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _154_317))
in (

let _59_405 = if (((n > (Prims.parse_int "0")) && (not ((FStar_Syntax_Util.is_unknown (Prims.snd ts))))) && ((FStar_List.length (Prims.fst ts)) <> n)) then begin
(let _154_320 = (let _154_319 = (FStar_Util.string_of_int n)
in (let _154_318 = (FStar_Syntax_Print.tscheme_to_string ts)
in (FStar_Util.format2 "The effect combinator is not universe-polymorphic enough (n=%s) (%s)" _154_319 _154_318)))
in (FStar_All.failwith _154_320))
end else begin
()
end
in ts)))
in (

let close_action = (fun act -> (

let _59_411 = (close (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_defn)))
in (match (_59_411) with
| (univs, defn) -> begin
(

let _59_414 = (close (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_typ)))
in (match (_59_414) with
| (univs', typ) -> begin
(

let _59_415 = ()
in (

let _59_417 = act
in {FStar_Syntax_Syntax.action_name = _59_417.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_params = _59_417.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = defn; FStar_Syntax_Syntax.action_typ = typ}))
end))
end)))
in (

let _59_419 = ()
in (

let ed = (

let _59_421 = ed
in (let _154_337 = (close (Prims.parse_int "0") return_wp)
in (let _154_336 = (close (Prims.parse_int "1") bind_wp)
in (let _154_335 = (close (Prims.parse_int "0") if_then_else)
in (let _154_334 = (close (Prims.parse_int "0") ite_wp)
in (let _154_333 = (close (Prims.parse_int "0") stronger)
in (let _154_332 = (close (Prims.parse_int "1") close_wp)
in (let _154_331 = (close (Prims.parse_int "0") assert_p)
in (let _154_330 = (close (Prims.parse_int "0") assume_p)
in (let _154_329 = (close (Prims.parse_int "0") null_wp)
in (let _154_328 = (close (Prims.parse_int "0") trivial_wp)
in (let _154_327 = (let _154_323 = (close (Prims.parse_int "0") (([]), (repr)))
in (Prims.snd _154_323))
in (let _154_326 = (close (Prims.parse_int "0") return_repr)
in (let _154_325 = (close (Prims.parse_int "1") bind_repr)
in (let _154_324 = (FStar_List.map close_action actions)
in {FStar_Syntax_Syntax.qualifiers = _59_421.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _59_421.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _154_337; FStar_Syntax_Syntax.bind_wp = _154_336; FStar_Syntax_Syntax.if_then_else = _154_335; FStar_Syntax_Syntax.ite_wp = _154_334; FStar_Syntax_Syntax.stronger = _154_333; FStar_Syntax_Syntax.close_wp = _154_332; FStar_Syntax_Syntax.assert_p = _154_331; FStar_Syntax_Syntax.assume_p = _154_330; FStar_Syntax_Syntax.null_wp = _154_329; FStar_Syntax_Syntax.trivial = _154_328; FStar_Syntax_Syntax.repr = _154_327; FStar_Syntax_Syntax.return_repr = _154_326; FStar_Syntax_Syntax.bind_repr = _154_325; FStar_Syntax_Syntax.actions = _154_324})))))))))))))))
in (

let _59_424 = if ((FStar_TypeChecker_Env.debug env FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ED")))) then begin
(let _154_338 = (FStar_Syntax_Print.eff_decl_to_string false ed)
in (FStar_Util.print_string _154_338))
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
and cps_and_elaborate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.sigelt Prims.option) = (fun env ed -> (

let _59_430 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_59_430) with
| (effect_binders_un, signature_un) -> begin
(

let _59_435 = (tc_tparams env effect_binders_un)
in (match (_59_435) with
| (effect_binders, env, _59_434) -> begin
(

let _59_439 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (_59_439) with
| (signature, _59_438) -> begin
(

let effect_binders = (FStar_List.map (fun _59_442 -> (match (_59_442) with
| (bv, qual) -> begin
(let _154_343 = (

let _59_443 = bv
in (let _154_342 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _59_443.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_443.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _154_342}))
in ((_154_343), (qual)))
end)) effect_binders)
in (

let _59_458 = (match ((let _154_344 = (FStar_Syntax_Subst.compress signature_un)
in _154_344.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (((a, _59_448))::[], effect_marker) -> begin
((a), (effect_marker))
end
| _59_455 -> begin
(FStar_All.failwith "bad shape for effect-for-free signature")
end)
in (match (_59_458) with
| (a, effect_marker) -> begin
(

let a = if (FStar_Syntax_Syntax.is_null_bv a) then begin
(let _154_346 = (let _154_345 = (FStar_Syntax_Syntax.range_of_bv a)
in Some (_154_345))
in (FStar_Syntax_Syntax.gen_bv "a" _154_346 a.FStar_Syntax_Syntax.sort))
end else begin
a
end
in (

let open_and_check = (fun env other_binders t -> (

let subst = (FStar_Syntax_Subst.opening_of_binders (FStar_List.append effect_binders other_binders))
in (

let t = (FStar_Syntax_Subst.subst subst t)
in (

let _59_470 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (_59_470) with
| (t, comp, _59_469) -> begin
((t), (comp))
end)))))
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None signature.FStar_Syntax_Syntax.pos))
in (

let _59_475 = (open_and_check env [] ed.FStar_Syntax_Syntax.repr)
in (match (_59_475) with
| (repr, _comp) -> begin
(

let _59_476 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _154_355 = (FStar_Syntax_Print.term_to_string repr)
in (FStar_Util.print1 "Representation is: %s\n" _154_355))
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

let wp_a = (let _154_362 = (let _154_361 = (let _154_360 = (let _154_359 = (let _154_358 = (let _154_357 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _154_356 = (FStar_Syntax_Syntax.as_implicit false)
in ((_154_357), (_154_356))))
in (_154_358)::[])
in ((wp_type), (_154_359)))
in FStar_Syntax_Syntax.Tm_app (_154_360))
in (mk _154_361))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _154_362))
in (

let effect_signature = (

let binders = (let _154_367 = (let _154_363 = (FStar_Syntax_Syntax.as_implicit false)
in ((a), (_154_363)))
in (let _154_366 = (let _154_365 = (let _154_364 = (FStar_Syntax_Syntax.gen_bv "dijkstra_wp" None wp_a)
in (FStar_All.pipe_right _154_364 FStar_Syntax_Syntax.mk_binder))
in (_154_365)::[])
in (_154_367)::_154_366))
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

let elaborate_and_star = (fun dmff_env other_binders item -> (

let env = (FStar_TypeChecker_DMFF.get_env dmff_env)
in (

let _59_496 = item
in (match (_59_496) with
| (u_item, item) -> begin
(

let _59_499 = (open_and_check env other_binders item)
in (match (_59_499) with
| (item, item_comp) -> begin
(

let _59_500 = if (not ((FStar_Syntax_Util.is_total_lcomp item_comp))) then begin
(let _154_379 = (let _154_378 = (let _154_377 = (FStar_Syntax_Print.term_to_string item)
in (let _154_376 = (FStar_Syntax_Print.lcomp_to_string item_comp)
in (FStar_Util.format2 "Computation for [%s] is not total : %s !" _154_377 _154_376)))
in FStar_Syntax_Syntax.Err (_154_378))
in (Prims.raise _154_379))
end else begin
()
end
in (

let _59_505 = (FStar_TypeChecker_DMFF.star_expr dmff_env item)
in (match (_59_505) with
| (item_t, item_wp, item_elab) -> begin
(

let item_wp = (recheck_debug "*" env item_wp)
in (

let item_elab = (recheck_debug "_" env item_elab)
in ((dmff_env), (item_t), (item_wp), (item_elab))))
end)))
end))
end))))
in (

let _59_513 = (elaborate_and_star dmff_env [] ed.FStar_Syntax_Syntax.bind_repr)
in (match (_59_513) with
| (dmff_env, _59_510, bind_wp, bind_elab) -> begin
(

let _59_519 = (elaborate_and_star dmff_env [] ed.FStar_Syntax_Syntax.return_repr)
in (match (_59_519) with
| (dmff_env, _59_516, return_wp, return_elab) -> begin
(

let lift_from_pure_wp = (match ((let _154_380 = (FStar_Syntax_Subst.compress return_wp)
in _154_380.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(

let _59_533 = (let _154_381 = (FStar_Syntax_Util.abs bs body None)
in (FStar_Syntax_Subst.open_term ((b1)::(b2)::[]) _154_381))
in (match (_59_533) with
| ((b1)::(b2)::[], body) -> begin
(

let env0 = (FStar_TypeChecker_Env.push_binders (FStar_TypeChecker_DMFF.get_env dmff_env) ((b1)::(b2)::[]))
in (

let wp_b1 = (let _154_388 = (let _154_387 = (let _154_386 = (let _154_385 = (let _154_384 = (let _154_383 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b1))
in (let _154_382 = (FStar_Syntax_Syntax.as_implicit false)
in ((_154_383), (_154_382))))
in (_154_384)::[])
in ((wp_type), (_154_385)))
in FStar_Syntax_Syntax.Tm_app (_154_386))
in (mk _154_387))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env0 _154_388))
in (

let _59_539 = (let _154_390 = (let _154_389 = (FStar_Syntax_Util.unascribe wp_b1)
in (FStar_TypeChecker_Normalize.eta_expand_with_type body _154_389))
in (FStar_All.pipe_left FStar_Syntax_Util.abs_formals _154_390))
in (match (_59_539) with
| (bs, body, what') -> begin
(

let t2 = (Prims.fst b2).FStar_Syntax_Syntax.sort
in (

let pure_wp_type = (FStar_TypeChecker_DMFF.double_star t2)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None pure_wp_type)
in (

let body = (let _154_394 = (FStar_Syntax_Syntax.bv_to_name wp)
in (let _154_393 = (let _154_392 = (let _154_391 = (FStar_Syntax_Util.abs ((b2)::[]) body what')
in ((_154_391), (None)))
in (_154_392)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _154_394 _154_393 None FStar_Range.dummyRange)))
in (let _154_398 = (let _154_396 = (let _154_395 = (FStar_Syntax_Syntax.mk_binder wp)
in (_154_395)::[])
in (b1)::_154_396)
in (let _154_397 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs _154_398 _154_397 (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_GTot_lid))))))))))
end))))
end))
end
| _59_545 -> begin
(FStar_All.failwith "unexpected shape for return")
end)
in (

let return_wp = (match ((let _154_399 = (FStar_Syntax_Subst.compress return_wp)
in _154_399.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(let _154_400 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs ((b1)::(b2)::[]) _154_400 (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_GTot_lid)))))
end
| _59_557 -> begin
(FStar_All.failwith "unexpected shape for return")
end)
in (

let bind_wp = (match ((let _154_401 = (FStar_Syntax_Subst.compress bind_wp)
in _154_401.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let r = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (let _154_405 = (let _154_404 = (let _154_403 = (let _154_402 = (mk (FStar_Syntax_Syntax.Tm_fvar (r)))
in (FStar_Syntax_Syntax.null_binder _154_402))
in (_154_403)::[])
in (FStar_List.append _154_404 binders))
in (FStar_Syntax_Util.abs _154_405 body what)))
end
| _59_566 -> begin
(FStar_All.failwith "unexpected shape for bind")
end)
in (

let apply_close = (fun t -> if ((FStar_List.length effect_binders) = (Prims.parse_int "0")) then begin
t
end else begin
(let _154_412 = (let _154_411 = (let _154_410 = (let _154_409 = (let _154_408 = (FStar_Syntax_Util.args_of_binders effect_binders)
in (Prims.snd _154_408))
in ((t), (_154_409)))
in FStar_Syntax_Syntax.Tm_app (_154_410))
in (mk _154_411))
in (FStar_Syntax_Subst.close effect_binders _154_412))
end)
in (

let register = (fun name item -> (

let _59_575 = (let _154_418 = (mk_lid name)
in (let _154_417 = (FStar_Syntax_Util.abs effect_binders item None)
in (FStar_TypeChecker_Util.mk_toplevel_definition env _154_418 _154_417)))
in (match (_59_575) with
| (sigelt, fv) -> begin
(

let _59_576 = (let _154_420 = (let _154_419 = (FStar_ST.read sigelts)
in (sigelt)::_154_419)
in (FStar_ST.op_Colon_Equals sigelts _154_420))
in fv)
end)))
in (

let lift_from_pure_wp = (register "lift_from_pure" lift_from_pure_wp)
in (

let return_wp = (register "return_wp" return_wp)
in (

let _59_580 = (let _154_422 = (let _154_421 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true")), (FStar_Range.dummyRange))))::_154_421)
in (FStar_ST.op_Colon_Equals sigelts _154_422))
in (

let return_elab = (register "return_elab" return_elab)
in (

let _59_583 = (let _154_424 = (let _154_423 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false")), (FStar_Range.dummyRange))))::_154_423)
in (FStar_ST.op_Colon_Equals sigelts _154_424))
in (

let bind_wp = (register "bind_wp" bind_wp)
in (

let _59_586 = (let _154_426 = (let _154_425 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true")), (FStar_Range.dummyRange))))::_154_425)
in (FStar_ST.op_Colon_Equals sigelts _154_426))
in (

let bind_elab = (register "bind_elab" bind_elab)
in (

let _59_589 = (let _154_428 = (let _154_427 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false")), (FStar_Range.dummyRange))))::_154_427)
in (FStar_ST.op_Colon_Equals sigelts _154_428))
in (

let _59_628 = (FStar_List.fold_left (fun _59_593 action -> (match (_59_593) with
| (dmff_env, actions) -> begin
(

let params_un = (FStar_Syntax_Subst.open_binders action.FStar_Syntax_Syntax.action_params)
in (

let _59_600 = (tc_tparams (FStar_TypeChecker_DMFF.get_env dmff_env) params_un)
in (match (_59_600) with
| (params, env', _59_599) -> begin
(

let params = (FStar_List.map (fun _59_603 -> (match (_59_603) with
| (bv, qual) -> begin
(let _154_433 = (

let _59_604 = bv
in (let _154_432 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _59_604.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_604.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _154_432}))
in ((_154_433), (qual)))
end)) params)
in (

let dmff_env' = (FStar_TypeChecker_DMFF.set_env dmff_env env')
in (

let _59_612 = (elaborate_and_star dmff_env' params ((action.FStar_Syntax_Syntax.action_univs), (action.FStar_Syntax_Syntax.action_defn)))
in (match (_59_612) with
| (dmff_env', action_t, action_wp, action_elab) -> begin
(

let _59_613 = (let _154_435 = (FStar_Syntax_Print.term_to_string action_t)
in (let _154_434 = (FStar_Syntax_Print.term_to_string action_wp)
in (FStar_Util.print2_warning "type %s, wp %s\n" _154_435 _154_434)))
in (

let name = action.FStar_Syntax_Syntax.action_name.FStar_Ident.ident.FStar_Ident.idText
in (

let action_typ_with_wp = (FStar_TypeChecker_DMFF.trans_F dmff_env' action_t action_wp)
in (

let params = (FStar_Syntax_Subst.close_binders params)
in (

let action_elab = (FStar_Syntax_Subst.close params action_elab)
in (

let action_typ_with_wp = (FStar_Syntax_Subst.close params action_typ_with_wp)
in (

let _59_620 = (let _154_437 = (FStar_Syntax_Print.term_to_string action_typ_with_wp)
in (let _154_436 = (FStar_Syntax_Print.term_to_string action_elab)
in (FStar_Util.print2_warning "type %s, term %s\n" _154_437 _154_436)))
in (

let action_elab = (let _154_438 = (FStar_Syntax_Util.abs params action_elab None)
in (register (Prims.strcat name "_elab") _154_438))
in (

let action_typ_with_wp = (let _154_440 = (let _154_439 = (FStar_Syntax_Syntax.mk_Total action_typ_with_wp)
in (FStar_Syntax_Util.arrow params _154_439))
in (FStar_All.pipe_left (register (Prims.strcat name "_complete_type")) _154_440))
in (let _154_444 = (let _154_443 = (

let _59_624 = action
in (let _154_442 = (apply_close action_elab)
in (let _154_441 = (apply_close action_typ_with_wp)
in {FStar_Syntax_Syntax.action_name = _59_624.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_univs = _59_624.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = []; FStar_Syntax_Syntax.action_defn = _154_442; FStar_Syntax_Syntax.action_typ = _154_441})))
in (_154_443)::actions)
in ((dmff_env), (_154_444))))))))))))
end))))
end)))
end)) ((dmff_env), ([])) ed.FStar_Syntax_Syntax.actions)
in (match (_59_628) with
| (dmff_env, actions) -> begin
(

let actions = (FStar_List.rev actions)
in (

let repr = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp_a" None wp_a)
in (

let binders = (let _154_447 = (FStar_Syntax_Syntax.mk_binder a)
in (let _154_446 = (let _154_445 = (FStar_Syntax_Syntax.mk_binder wp)
in (_154_445)::[])
in (_154_447)::_154_446))
in (let _154_456 = (let _154_455 = (let _154_453 = (let _154_452 = (let _154_451 = (let _154_450 = (let _154_449 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _154_448 = (FStar_Syntax_Syntax.as_implicit false)
in ((_154_449), (_154_448))))
in (_154_450)::[])
in ((repr), (_154_451)))
in FStar_Syntax_Syntax.Tm_app (_154_452))
in (mk _154_453))
in (let _154_454 = (FStar_Syntax_Syntax.bv_to_name wp)
in (FStar_TypeChecker_DMFF.trans_F dmff_env _154_455 _154_454)))
in (FStar_Syntax_Util.abs binders _154_456 None))))
in (

let repr = (recheck_debug "FC" env repr)
in (

let repr = (register "repr" repr)
in (

let _59_673 = (match ((let _154_458 = (let _154_457 = (FStar_Syntax_Subst.compress wp_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe _154_457))
in _154_458.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((type_param)::effect_param, arrow, _59_640) -> begin
(

let _59_647 = (FStar_Syntax_Subst.open_term ((type_param)::effect_param) arrow)
in (match (_59_647) with
| ((type_param)::effect_param, arrow) -> begin
(match ((let _154_460 = (let _154_459 = (FStar_Syntax_Subst.compress arrow)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe _154_459))
in _154_460.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (wp_binders, c) -> begin
(

let _59_654 = (FStar_Syntax_Subst.open_comp wp_binders c)
in (match (_59_654) with
| (wp_binders, c) -> begin
(

let _59_661 = (FStar_List.partition (fun _59_658 -> (match (_59_658) with
| (bv, _59_657) -> begin
(let _154_463 = (let _154_462 = (FStar_Syntax_Free.names bv.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _154_462 (FStar_Util.set_mem (Prims.fst type_param))))
in (FStar_All.pipe_right _154_463 Prims.op_Negation))
end)) wp_binders)
in (match (_59_661) with
| (pre_args, post_args) -> begin
(

let post = (match (post_args) with
| (post)::[] -> begin
post
end
| _59_665 -> begin
(let _154_465 = (let _154_464 = (FStar_Syntax_Print.term_to_string arrow)
in (FStar_Util.format1 "Impossible: multiple post candidates %s" _154_464))
in (FStar_All.failwith _154_465))
end)
in (let _154_467 = (FStar_Syntax_Util.arrow pre_args c)
in (let _154_466 = (FStar_Syntax_Util.abs ((type_param)::effect_param) (Prims.fst post).FStar_Syntax_Syntax.sort None)
in ((_154_467), (_154_466)))))
end))
end))
end
| _59_668 -> begin
(let _154_469 = (let _154_468 = (FStar_Syntax_Print.term_to_string arrow)
in (FStar_Util.format1 "Impossible: pre/post arrow %s" _154_468))
in (FStar_All.failwith _154_469))
end)
end))
end
| _59_670 -> begin
(let _154_471 = (let _154_470 = (FStar_Syntax_Print.term_to_string wp_type)
in (FStar_Util.format1 "Impossible: pre/post abs %s" _154_470))
in (FStar_All.failwith _154_471))
end)
in (match (_59_673) with
| (pre, post) -> begin
(

let _59_674 = (let _154_472 = (register "pre" pre)
in (Prims.ignore _154_472))
in (

let _59_676 = (let _154_473 = (register "post" post)
in (Prims.ignore _154_473))
in (

let _59_678 = (let _154_474 = (register "wp" wp_type)
in (Prims.ignore _154_474))
in (

let ed = (

let _59_680 = ed
in (let _154_485 = (FStar_Syntax_Subst.close_binders effect_binders)
in (let _154_484 = (FStar_Syntax_Subst.close effect_binders effect_signature)
in (let _154_483 = (let _154_475 = (apply_close return_wp)
in (([]), (_154_475)))
in (let _154_482 = (let _154_476 = (apply_close bind_wp)
in (([]), (_154_476)))
in (let _154_481 = (apply_close repr)
in (let _154_480 = (let _154_477 = (apply_close return_elab)
in (([]), (_154_477)))
in (let _154_479 = (let _154_478 = (apply_close bind_elab)
in (([]), (_154_478)))
in {FStar_Syntax_Syntax.qualifiers = _59_680.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _59_680.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _59_680.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _154_485; FStar_Syntax_Syntax.signature = _154_484; FStar_Syntax_Syntax.ret_wp = _154_483; FStar_Syntax_Syntax.bind_wp = _154_482; FStar_Syntax_Syntax.if_then_else = _59_680.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _59_680.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _59_680.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _59_680.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _59_680.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _59_680.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _59_680.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _59_680.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _154_481; FStar_Syntax_Syntax.return_repr = _154_480; FStar_Syntax_Syntax.bind_repr = _154_479; FStar_Syntax_Syntax.actions = actions}))))))))
in (

let _59_685 = (FStar_TypeChecker_DMFF.gen_wps_for_free env effect_binders a wp_a ed)
in (match (_59_685) with
| (sigelts', ed) -> begin
(

let _59_686 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _154_486 = (FStar_Syntax_Print.eff_decl_to_string true ed)
in (FStar_Util.print_string _154_486))
end else begin
()
end
in (

let lift_from_pure_opt = if ((FStar_List.length effect_binders) = (Prims.parse_int "0")) then begin
(

let lift_from_pure = (let _154_489 = (let _154_488 = (let _154_487 = (apply_close lift_from_pure_wp)
in (([]), (_154_487)))
in Some (_154_488))
in {FStar_Syntax_Syntax.source = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.target = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.lift_wp = _154_489; FStar_Syntax_Syntax.lift = None})
in Some (FStar_Syntax_Syntax.Sig_sub_effect (((lift_from_pure), (FStar_Range.dummyRange)))))
end else begin
None
end
in (let _154_492 = (let _154_491 = (let _154_490 = (FStar_ST.read sigelts)
in (FStar_List.rev _154_490))
in (FStar_List.append _154_491 sigelts'))
in ((_154_492), (ed), (lift_from_pure_opt)))))
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

let _59_694 = ()
in (

let _59_702 = ()
in (match (ses) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _59_731, _59_733, [], r))::(FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, _154_497, [], _59_722, r1))::(FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, _154_498, [], _59_711, r2))::[] when (((_154_497 = (Prims.parse_int "0")) && (_154_498 = (Prims.parse_int "0"))) && (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid))) -> begin
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

let lex_top_t = (let _154_501 = (let _154_500 = (let _154_499 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1) FStar_Syntax_Syntax.Delta_constant None)
in ((_154_499), ((FStar_Syntax_Syntax.U_name (utop))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_154_500))
in (FStar_Syntax_Syntax.mk _154_501 None r1))
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

let a = (let _154_502 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _154_502))
in (

let hd = (let _154_503 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _154_503))
in (

let tl = (let _154_507 = (let _154_506 = (let _154_505 = (let _154_504 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2) FStar_Syntax_Syntax.Delta_constant None)
in ((_154_504), ((FStar_Syntax_Syntax.U_name (ucons2))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_154_505))
in (FStar_Syntax_Syntax.mk _154_506 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _154_507))
in (

let res = (let _154_510 = (let _154_509 = (let _154_508 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2) FStar_Syntax_Syntax.Delta_constant None)
in ((_154_508), ((FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_154_509))
in (FStar_Syntax_Syntax.mk _154_510 None r2))
in (let _154_511 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow ((((a), (Some (FStar_Syntax_Syntax.imp_tag))))::(((hd), (None)))::(((tl), (None)))::[]) _154_511))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon (((lex_cons), ((ucons1)::(ucons2)::[]), (lex_cons_t), (FStar_Syntax_Const.lex_t_lid), ((Prims.parse_int "0")), ([]), ([]), (r2)))
in (let _154_513 = (let _154_512 = (FStar_TypeChecker_Env.get_range env)
in (((tc)::(dc_lextop)::(dc_lexcons)::[]), ([]), (lids), (_154_512)))
in FStar_Syntax_Syntax.Sig_bundle (_154_513)))))))))))))))
end
| _59_757 -> begin
(let _154_515 = (let _154_514 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle (((ses), ([]), (lids), (FStar_Range.dummyRange)))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _154_514))
in (FStar_All.failwith _154_515))
end))))
and tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _59_767 = (FStar_Syntax_Util.type_u ())
in (match (_59_767) with
| (k, _59_766) -> begin
(

let phi = (let _154_521 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _154_521 (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env)))
in (

let _59_769 = (FStar_TypeChecker_Util.check_uvars r phi)
in FStar_Syntax_Syntax.Sig_assume (((lid), (phi), (quals), (r)))))
end))))
and tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun env ses quals lids -> (

let warn_positivity = (fun l r -> (let _154_531 = (let _154_530 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _154_530))
in (FStar_TypeChecker_Errors.diag r _154_531)))
in (

let env0 = env
in (

let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(

let _59_792 = ()
in (

let _59_794 = (warn_positivity tc r)
in (

let _59_798 = (FStar_Syntax_Subst.open_term tps k)
in (match (_59_798) with
| (tps, k) -> begin
(

let _59_803 = (FStar_TypeChecker_TcTerm.tc_binders env tps)
in (match (_59_803) with
| (tps, env_tps, guard_params, us) -> begin
(

let _59_806 = (FStar_Syntax_Util.arrow_formals k)
in (match (_59_806) with
| (indices, t) -> begin
(

let _59_811 = (FStar_TypeChecker_TcTerm.tc_binders env_tps indices)
in (match (_59_811) with
| (indices, env', guard_indices, us') -> begin
(

let _59_819 = (

let _59_816 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' t)
in (match (_59_816) with
| (t, _59_814, g) -> begin
(let _154_538 = (let _154_537 = (let _154_536 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params _154_536))
in (FStar_TypeChecker_Rel.discharge_guard env' _154_537))
in ((t), (_154_538)))
end))
in (match (_59_819) with
| (t, guard) -> begin
(

let k = (let _154_539 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _154_539))
in (

let _59_823 = (FStar_Syntax_Util.type_u ())
in (match (_59_823) with
| (t_type, u) -> begin
(

let _59_824 = (let _154_540 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _154_540))
in (

let t_tc = (let _154_541 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _154_541))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _154_542 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) (([]), (t_tc)))
in ((_154_542), (FStar_Syntax_Syntax.Sig_inductive_typ (((tc), ([]), (tps), (k), (mutuals), (data), (quals), (r)))), (u), (guard))))))))
end)))
end))
end))
end))
end))
end))))
end
| _59_831 -> begin
(FStar_All.failwith "impossible")
end))
in (

let positive_if_pure = (fun _59_833 l -> ())
in (

let tc_data = (fun env tcs _59_1 -> (match (_59_1) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let _59_850 = ()
in (

let _59_885 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun _59_854 -> (match (_59_854) with
| (se, u_tc) -> begin
if (let _154_555 = (let _154_554 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _154_554))
in (FStar_Ident.lid_equals tc_lid _154_555)) then begin
(

let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_59_856, _59_858, tps, _59_861, _59_863, _59_865, _59_867, _59_869) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _59_875 -> (match (_59_875) with
| (x, _59_874) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
end
| _59_877 -> begin
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
in (match (_59_885) with
| (tps, u_tc) -> begin
(

let _59_905 = (match ((let _154_557 = (FStar_Syntax_Subst.compress t)
in _154_557.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let _59_893 = (FStar_Util.first_N ntps bs)
in (match (_59_893) with
| (_59_891, bs') -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs'), (res)))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _59_899 -> (match (_59_899) with
| (x, _59_898) -> begin
FStar_Syntax_Syntax.DB ((((ntps - ((Prims.parse_int "1") + i))), (x)))
end))))
in (let _154_560 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _154_560))))
end))
end
| _59_902 -> begin
(([]), (t))
end)
in (match (_59_905) with
| (arguments, result) -> begin
(

let _59_906 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _154_563 = (FStar_Syntax_Print.lid_to_string c)
in (let _154_562 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _154_561 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _154_563 _154_562 _154_561))))
end else begin
()
end
in (

let _59_911 = (tc_tparams env arguments)
in (match (_59_911) with
| (arguments, env', us) -> begin
(

let _59_914 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env' result)
in (match (_59_914) with
| (result, res_lcomp) -> begin
(

let _59_919 = (match ((let _154_564 = (FStar_Syntax_Subst.compress res_lcomp.FStar_Syntax_Syntax.res_typ)
in _154_564.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_59_916) -> begin
()
end
| ty -> begin
(let _154_569 = (let _154_568 = (let _154_567 = (let _154_566 = (FStar_Syntax_Print.term_to_string result)
in (let _154_565 = (FStar_Syntax_Print.term_to_string res_lcomp.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "The type of %s is %s, but since this is the result type of a constructor its type should be Type" _154_566 _154_565)))
in ((_154_567), (r)))
in FStar_Syntax_Syntax.Error (_154_568))
in (Prims.raise _154_569))
end)
in (

let _59_924 = (FStar_Syntax_Util.head_and_args result)
in (match (_59_924) with
| (head, _59_923) -> begin
(

let _59_929 = (match ((let _154_570 = (FStar_Syntax_Subst.compress head)
in _154_570.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _59_928 -> begin
(let _154_575 = (let _154_574 = (let _154_573 = (let _154_572 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (let _154_571 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" _154_572 _154_571)))
in ((_154_573), (r)))
in FStar_Syntax_Syntax.Error (_154_574))
in (Prims.raise _154_575))
end)
in (

let g = (FStar_List.fold_left2 (fun g _59_935 u_x -> (match (_59_935) with
| (x, _59_934) -> begin
(

let _59_937 = ()
in (let _154_579 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _154_579)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _154_583 = (let _154_581 = (FStar_All.pipe_right tps (FStar_List.map (fun _59_943 -> (match (_59_943) with
| (x, _59_942) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append _154_581 arguments))
in (let _154_582 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _154_583 _154_582)))
in ((FStar_Syntax_Syntax.Sig_datacon (((c), ([]), (t), (tc_lid), (ntps), (quals), ([]), (r)))), (g)))))
end)))
end))
end)))
end))
end)))
end
| _59_946 -> begin
(FStar_All.failwith "impossible")
end))
in (

let generalize_and_inst_within = (fun env g tcs datas -> (

let _59_952 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _59_2 -> (match (_59_2) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_59_956, _59_958, tps, k, _59_962, _59_964, _59_966, _59_968) -> begin
(let _154_594 = (let _154_593 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _154_593))
in (FStar_Syntax_Syntax.null_binder _154_594))
end
| _59_972 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _59_3 -> (match (_59_3) with
| FStar_Syntax_Syntax.Sig_datacon (_59_976, _59_978, t, _59_981, _59_983, _59_985, _59_987, _59_989) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _59_993 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let t = (let _154_596 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _154_596))
in (

let _59_996 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _154_597 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _154_597))
end else begin
()
end
in (

let _59_1000 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_59_1000) with
| (uvs, t) -> begin
(

let _59_1002 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _154_601 = (let _154_599 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _154_599 (FStar_String.concat ", ")))
in (let _154_600 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _154_601 _154_600)))
end else begin
()
end
in (

let _59_1006 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_59_1006) with
| (uvs, t) -> begin
(

let _59_1010 = (FStar_Syntax_Util.arrow_formals t)
in (match (_59_1010) with
| (args, _59_1009) -> begin
(

let _59_1013 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_59_1013) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun _59_1017 se -> (match (_59_1017) with
| (x, _59_1016) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _59_1021, tps, _59_1024, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let _59_1047 = (match ((let _154_604 = (FStar_Syntax_Subst.compress ty)
in _154_604.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _59_1038 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_59_1038) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _59_1041 -> begin
(let _154_605 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) _154_605 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in ((tps), (t)))
end))
end
| _59_1044 -> begin
(([]), (ty))
end)
in (match (_59_1047) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs), (tps), (t), (mutuals), (datas), (quals), (r)))
end)))
end
| _59_1049 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| _59_1053 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _154_606 -> FStar_Syntax_Syntax.U_name (_154_606))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _59_4 -> (match (_59_4) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _59_1058, _59_1060, _59_1062, _59_1064, _59_1066, _59_1068, _59_1070) -> begin
((tc), (uvs_universes))
end
| _59_1074 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _59_1079 d -> (match (_59_1079) with
| (t, _59_1078) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _59_1083, _59_1085, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (let _154_610 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _154_610 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon (((l), (uvs), (ty), (tc), (ntps), (quals), (mutuals), (r))))
end
| _59_1095 -> begin
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

let _59_1105 = (FStar_All.pipe_right ses (FStar_List.partition (fun _59_5 -> (match (_59_5) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_59_1099) -> begin
true
end
| _59_1102 -> begin
false
end))))
in (match (_59_1105) with
| (tys, datas) -> begin
(

let _59_1112 = if (FStar_All.pipe_right datas (FStar_Util.for_some (fun _59_6 -> (match (_59_6) with
| FStar_Syntax_Syntax.Sig_datacon (_59_1108) -> begin
false
end
| _59_1111 -> begin
true
end)))) then begin
(let _154_615 = (let _154_614 = (let _154_613 = (FStar_TypeChecker_Env.get_range env)
in (("Mutually defined type contains a non-inductive element"), (_154_613)))
in FStar_Syntax_Syntax.Error (_154_614))
in (Prims.raise _154_615))
end else begin
()
end
in (

let env0 = env
in (

let _59_1131 = (FStar_List.fold_right (fun tc _59_1119 -> (match (_59_1119) with
| (env, all_tcs, g) -> begin
(

let _59_1124 = (tc_tycon env tc)
in (match (_59_1124) with
| (env, tc, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (

let _59_1126 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _154_618 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _154_618))
end else begin
()
end
in (let _154_620 = (let _154_619 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g _154_619))
in ((env), ((((tc), (tc_u)))::all_tcs), (_154_620)))))
end))
end)) tys ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (_59_1131) with
| (env, tcs, g) -> begin
(

let _59_1141 = (FStar_List.fold_right (fun se _59_1135 -> (match (_59_1135) with
| (datas, g) -> begin
(

let _59_1138 = (tc_data env tcs se)
in (match (_59_1138) with
| (data, g') -> begin
(let _154_623 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((data)::datas), (_154_623)))
end))
end)) datas (([]), (g)))
in (match (_59_1141) with
| (datas, g) -> begin
(

let _59_1144 = (let _154_624 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _154_624 datas))
in (match (_59_1144) with
| (tcs, datas) -> begin
(

let sig_bndle = (let _154_626 = (let _154_625 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_154_625)))
in FStar_Syntax_Syntax.Sig_bundle (_154_626))
in (

let datacon_typ = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (_59_1149, _59_1151, t, _59_1154, _59_1156, _59_1158, _59_1160, _59_1162) -> begin
t
end
| _59_1166 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let dr = FStar_Range.dummyRange
in (

let optimized_haseq_scheme = (fun _59_1169 -> (

let haseq_ty = (fun usubst us acc ty -> (

let _59_1196 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _59_1178, bs, t, _59_1182, d_lids, _59_1185, _59_1187) -> begin
((lid), (bs), (t), (d_lids))
end
| _59_1191 -> begin
(FStar_All.failwith "Impossible!")
end)
in (match (_59_1196) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _154_639 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _154_639 t))
in (

let _59_1201 = (FStar_Syntax_Subst.open_term bs t)
in (match (_59_1201) with
| (bs, t) -> begin
(

let ibs = (match ((let _154_640 = (FStar_Syntax_Subst.compress t)
in _154_640.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _59_1204) -> begin
ibs
end
| _59_1208 -> begin
[]
end)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _154_643 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _154_642 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _154_643 _154_642)))
in (

let ind = (let _154_646 = (FStar_List.map (fun _59_1215 -> (match (_59_1215) with
| (bv, aq) -> begin
(let _154_645 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_154_645), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _154_646 None dr))
in (

let ind = (let _154_649 = (FStar_List.map (fun _59_1219 -> (match (_59_1219) with
| (bv, aq) -> begin
(let _154_648 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_154_648), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _154_649 None dr))
in (

let haseq_ind = (let _154_651 = (let _154_650 = (FStar_Syntax_Syntax.as_arg ind)
in (_154_650)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _154_651 None dr))
in (

let bs' = (FStar_List.filter (fun b -> (

let _59_1230 = acc
in (match (_59_1230) with
| (_59_1224, en, _59_1227, _59_1229) -> begin
(

let opt = (let _154_654 = (let _154_653 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _154_653))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort _154_654 false))
in (match (opt) with
| None -> begin
false
end
| Some (_59_1234) -> begin
true
end))
end))) bs)
in (

let haseq_bs = (FStar_List.fold_left (fun t b -> (let _154_660 = (let _154_659 = (let _154_658 = (let _154_657 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b))
in (FStar_Syntax_Syntax.as_arg _154_657))
in (_154_658)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _154_659 None dr))
in (FStar_Syntax_Util.mk_conj t _154_660))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml = (

let _59_1241 = fml
in (let _154_666 = (let _154_665 = (let _154_664 = (let _154_663 = (let _154_662 = (let _154_661 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_154_661)::[])
in (_154_662)::[])
in FStar_Syntax_Syntax.Meta_pattern (_154_663))
in ((fml), (_154_664)))
in FStar_Syntax_Syntax.Tm_meta (_154_665))
in {FStar_Syntax_Syntax.n = _154_666; FStar_Syntax_Syntax.tk = _59_1241.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _59_1241.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _59_1241.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _154_672 = (let _154_671 = (let _154_670 = (let _154_669 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _154_669 None))
in (FStar_Syntax_Syntax.as_arg _154_670))
in (_154_671)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _154_672 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _154_678 = (let _154_677 = (let _154_676 = (let _154_675 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _154_675 None))
in (FStar_Syntax_Syntax.as_arg _154_676))
in (_154_677)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _154_678 None dr))) bs fml)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let _59_1255 = acc
in (match (_59_1255) with
| (l_axioms, env, guard', cond') -> begin
(

let env = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env = (FStar_TypeChecker_Env.push_binders env ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (_59_1260, _59_1262, _59_1264, t_lid, _59_1267, _59_1269, _59_1271, _59_1273) -> begin
(t_lid = lid)
end
| _59_1277 -> begin
(FStar_All.failwith "Impossible")
end)) datas)
in (

let haseq_data = (fun data -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (match ((let _154_682 = (FStar_Syntax_Subst.compress dt)
in _154_682.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _59_1285) -> begin
(

let dbs = (let _154_683 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _154_683))
in (

let dbs = (let _154_684 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _154_684 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let haseq_b = (let _154_688 = (let _154_687 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_154_687)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _154_688 None dr))
in (

let sort_range = (Prims.fst b).FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos
in (

let haseq_b = (let _154_690 = (let _154_689 = (FStar_Syntax_Print.term_to_string ind)
in (FStar_Util.format1 "Failed to prove that the type \'%s\' supports decidable equality because of this argument; add the \'noeq\' qualifier" _154_689))
in (FStar_TypeChecker_Util.label _154_690 sort_range haseq_b))
in (FStar_Syntax_Util.mk_conj t haseq_b))))) FStar_Syntax_Util.t_true dbs)
in (FStar_List.fold_right (fun b t -> (let _154_696 = (let _154_695 = (let _154_694 = (let _154_693 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _154_693 None))
in (FStar_Syntax_Syntax.as_arg _154_694))
in (_154_695)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _154_696 None dr))) dbs cond)))))
end
| _59_1300 -> begin
FStar_Syntax_Util.t_true
end))))
in (

let cond = (FStar_List.fold_left (fun acc d -> (let _154_699 = (haseq_data d)
in (FStar_Syntax_Util.mk_conj acc _154_699))) FStar_Syntax_Util.t_true t_datas)
in (

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (let _154_701 = (FStar_Syntax_Util.mk_conj guard' guard)
in (let _154_700 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml)))::[]))), (env), (_154_701), (_154_700))))))))))
end)))))))))))))))
end))))
end)))
in (

let us = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_59_1307, us, _59_1310, _59_1312, _59_1314, _59_1316, _59_1318, _59_1320) -> begin
us
end
| _59_1324 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let _59_1328 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (_59_1328) with
| (usubst, us) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (

let _59_1330 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq")
in (

let _59_1332 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle)
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let _59_1339 = (FStar_List.fold_left (haseq_ty usubst us) (([]), (env), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (_59_1339) with
| (axioms, env, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let _59_1344 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env phi)
in (match (_59_1344) with
| (phi, _59_1343) -> begin
(

let _59_1345 = if (FStar_TypeChecker_Env.should_verify env) then begin
(let _154_702 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi)))
in (FStar_TypeChecker_Rel.force_trivial_guard env _154_702))
end else begin
()
end
in (

let ses = (FStar_List.fold_left (fun l _59_1350 -> (match (_59_1350) with
| (lid, fml) -> begin
(

let se = (tc_assume env lid fml [] dr)
in (FStar_List.append l ((se)::[])))
end)) [] axioms)
in (

let _59_1353 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq")
in ses)))
end)))
end))))))
end)))))
in (

let unoptimized_haseq_scheme = (fun _59_1356 -> (

let mutuals = (FStar_List.map (fun ty -> (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _59_1361, _59_1363, _59_1365, _59_1367, _59_1369, _59_1371, _59_1373) -> begin
lid
end
| _59_1377 -> begin
(FStar_All.failwith "Impossible!")
end)) tcs)
in (

let haseq_ty = (fun usubst us acc ty -> (

let _59_1404 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _59_1386, bs, t, _59_1390, d_lids, _59_1393, _59_1395) -> begin
((lid), (bs), (t), (d_lids))
end
| _59_1399 -> begin
(FStar_All.failwith "Impossible!")
end)
in (match (_59_1404) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _154_716 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _154_716 t))
in (

let _59_1409 = (FStar_Syntax_Subst.open_term bs t)
in (match (_59_1409) with
| (bs, t) -> begin
(

let ibs = (match ((let _154_717 = (FStar_Syntax_Subst.compress t)
in _154_717.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _59_1412) -> begin
ibs
end
| _59_1416 -> begin
[]
end)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _154_720 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _154_719 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _154_720 _154_719)))
in (

let ind = (let _154_723 = (FStar_List.map (fun _59_1423 -> (match (_59_1423) with
| (bv, aq) -> begin
(let _154_722 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_154_722), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _154_723 None dr))
in (

let ind = (let _154_726 = (FStar_List.map (fun _59_1427 -> (match (_59_1427) with
| (bv, aq) -> begin
(let _154_725 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_154_725), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _154_726 None dr))
in (

let haseq_ind = (let _154_728 = (let _154_727 = (FStar_Syntax_Syntax.as_arg ind)
in (_154_727)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _154_728 None dr))
in (

let rec is_mutual = (fun t -> (match ((let _154_732 = (FStar_Syntax_Subst.compress t)
in _154_732.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.existsb (fun lid -> (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) mutuals)
end
| FStar_Syntax_Syntax.Tm_uinst (t', _59_1438) -> begin
(is_mutual t')
end
| FStar_Syntax_Syntax.Tm_refine (bv, t') -> begin
(is_mutual bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_app (t', args) -> begin
if (is_mutual t') then begin
true
end else begin
(let _154_734 = (FStar_List.map Prims.fst args)
in (exists_mutual _154_734))
end
end
| FStar_Syntax_Syntax.Tm_meta (t', _59_1451) -> begin
(is_mutual t')
end
| _59_1455 -> begin
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
in (match ((let _154_740 = (FStar_Syntax_Subst.compress dt)
in _154_740.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _59_1468) -> begin
(

let dbs = (let _154_741 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _154_741))
in (

let dbs = (let _154_742 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _154_742 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let sort = (Prims.fst b).FStar_Syntax_Syntax.sort
in (

let haseq_sort = (let _154_746 = (let _154_745 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_154_745)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _154_746 None dr))
in (

let haseq_sort = if (is_mutual sort) then begin
(FStar_Syntax_Util.mk_imp haseq_ind haseq_sort)
end else begin
haseq_sort
end
in (FStar_Syntax_Util.mk_conj t haseq_sort))))) FStar_Syntax_Util.t_true dbs)
in (

let cond = (FStar_List.fold_right (fun b t -> (let _154_752 = (let _154_751 = (let _154_750 = (let _154_749 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _154_749 None))
in (FStar_Syntax_Syntax.as_arg _154_750))
in (_154_751)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _154_752 None dr))) dbs cond)
in (FStar_Syntax_Util.mk_conj acc cond))))))
end
| _59_1484 -> begin
acc
end))))
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (_59_1487, _59_1489, _59_1491, t_lid, _59_1494, _59_1496, _59_1498, _59_1500) -> begin
(t_lid = lid)
end
| _59_1504 -> begin
(FStar_All.failwith "Impossible")
end)) datas)
in (

let data_cond = (FStar_List.fold_left haseq_data FStar_Syntax_Util.t_true t_datas)
in (

let fml = (FStar_Syntax_Util.mk_imp data_cond haseq_ind)
in (

let fml = (

let _59_1508 = fml
in (let _154_759 = (let _154_758 = (let _154_757 = (let _154_756 = (let _154_755 = (let _154_754 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_154_754)::[])
in (_154_755)::[])
in FStar_Syntax_Syntax.Meta_pattern (_154_756))
in ((fml), (_154_757)))
in FStar_Syntax_Syntax.Tm_meta (_154_758))
in {FStar_Syntax_Syntax.n = _154_759; FStar_Syntax_Syntax.tk = _59_1508.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _59_1508.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _59_1508.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _154_765 = (let _154_764 = (let _154_763 = (let _154_762 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _154_762 None))
in (FStar_Syntax_Syntax.as_arg _154_763))
in (_154_764)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _154_765 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _154_771 = (let _154_770 = (let _154_769 = (let _154_768 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _154_768 None))
in (FStar_Syntax_Syntax.as_arg _154_769))
in (_154_770)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _154_771 None dr))) bs fml)
in (FStar_Syntax_Util.mk_conj acc fml)))))))))))))))
end))))
end)))
in (

let _59_1538 = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, _59_1521, _59_1523, _59_1525, _59_1527, _59_1529, _59_1531) -> begin
((lid), (us))
end
| _59_1535 -> begin
(FStar_All.failwith "Impossible!")
end))
in (match (_59_1538) with
| (lid, us) -> begin
(

let _59_1541 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (_59_1541) with
| (usubst, us) -> begin
(

let fml = (FStar_List.fold_left (haseq_ty usubst us) FStar_Syntax_Util.t_true tcs)
in (

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (

let _59_1544 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq")
in (

let _59_1546 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle)
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let se = (let _154_772 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (tc_assume env _154_772 fml [] dr))
in (

let _59_1550 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq")
in (se)::[])))))))
end))
end)))))
in (

let skip_prims_type = (fun _59_1553 -> (

let lid = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _59_1558, _59_1560, _59_1562, _59_1564, _59_1566, _59_1568, _59_1570) -> begin
lid
end
| _59_1574 -> begin
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
in (let _154_780 = (let _154_779 = (let _154_778 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_154_778)))
in FStar_Syntax_Syntax.Sig_bundle (_154_779))
in (_154_780)::ses)))
end)))))))
end))
end))
end))))
end)))))))))
and tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env se -> (

let env = (set_hint_correlator env se)
in (

let _59_1586 = (FStar_TypeChecker_Util.check_sigelt_quals env se)
in (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let se = (tc_lex_t env ses quals lids)
in (let _154_783 = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (_154_783)))))
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

let _59_1626 = (set_options FStar_Options.Set o)
in (((se)::[]), (env)))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(

let _59_1630 = (let _154_790 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _154_790 Prims.ignore))
in (

let _59_1635 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (

let _59_1637 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (((se)::[]), (env)))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_59_1640) -> begin
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

let _59_1656 = (FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun _59_1651 a -> (match (_59_1651) with
| (env, ses) -> begin
(

let se_let = (FStar_Syntax_Util.action_as_lb a)
in (let _154_793 = (FStar_TypeChecker_Env.push_sigelt env se_let)
in ((_154_793), ((se_let)::ses))))
end)) ((env), ((se)::[]))))
in (match (_59_1656) with
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

let _59_1665 = (let _154_794 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _154_794))
in (match (_59_1665) with
| (a, wp_a_src) -> begin
(

let _59_1668 = (let _154_795 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _154_795))
in (match (_59_1668) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (let _154_799 = (let _154_798 = (let _154_797 = (let _154_796 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (_154_796)))
in FStar_Syntax_Syntax.NT (_154_797))
in (_154_798)::[])
in (FStar_Syntax_Subst.subst _154_799 wp_b_tgt))
in (

let expected_k = (let _154_804 = (let _154_802 = (FStar_Syntax_Syntax.mk_binder a)
in (let _154_801 = (let _154_800 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_154_800)::[])
in (_154_802)::_154_801))
in (let _154_803 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _154_804 _154_803)))
in (

let repr_type = (fun eff_name a wp -> (

let no_reify = (fun l -> (let _154_816 = (let _154_815 = (let _154_814 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _154_813 = (FStar_TypeChecker_Env.get_range env)
in ((_154_814), (_154_813))))
in FStar_Syntax_Syntax.Error (_154_815))
in (Prims.raise _154_816)))
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
(let _154_823 = (let _154_821 = (let _154_820 = (let _154_819 = (FStar_Syntax_Syntax.as_arg a)
in (let _154_818 = (let _154_817 = (FStar_Syntax_Syntax.as_arg wp)
in (_154_817)::[])
in (_154_819)::_154_818))
in ((repr), (_154_820)))
in FStar_Syntax_Syntax.Tm_app (_154_821))
in (let _154_822 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _154_823 None _154_822)))
end)
end)))
in (

let _59_1709 = (match (((sub.FStar_Syntax_Syntax.lift), (sub.FStar_Syntax_Syntax.lift_wp))) with
| (None, None) -> begin
(FStar_All.failwith "Impossible")
end
| (lift, Some (_59_1686, lift_wp)) -> begin
(let _154_824 = (check_and_gen env lift_wp expected_k)
in ((lift), (_154_824)))
end
| (Some (what, lift), None) -> begin
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange))
in (

let _59_1702 = (FStar_TypeChecker_DMFF.star_expr dmff_env lift)
in (match (_59_1702) with
| (_59_1699, lift_wp, lift_elab) -> begin
(

let _59_1703 = (recheck_debug "lift-wp" env lift_wp)
in (

let _59_1705 = (recheck_debug "lift-elab" env lift_elab)
in ((Some ((([]), (lift_elab)))), ((([]), (lift_wp))))))
end)))
end)
in (match (_59_1709) with
| (lift, lift_wp) -> begin
(

let lax = env.FStar_TypeChecker_Env.lax
in (

let env = (

let _59_1711 = env
in {FStar_TypeChecker_Env.solver = _59_1711.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_1711.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_1711.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_1711.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_1711.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_1711.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_1711.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_1711.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_1711.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_1711.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_1711.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_1711.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_1711.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_1711.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_1711.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_1711.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_1711.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_1711.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _59_1711.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_1711.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_1711.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_1711.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_1711.FStar_TypeChecker_Env.qname_and_index})
in (

let lift = (match (lift) with
| None -> begin
None
end
| Some (_59_1716, lift) -> begin
(

let _59_1722 = (let _154_825 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _154_825))
in (match (_59_1722) with
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

let lift_wp_a = (let _154_832 = (let _154_830 = (let _154_829 = (let _154_828 = (FStar_Syntax_Syntax.as_arg a_typ)
in (let _154_827 = (let _154_826 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (_154_826)::[])
in (_154_828)::_154_827))
in ((lift_wp), (_154_829)))
in FStar_Syntax_Syntax.Tm_app (_154_830))
in (let _154_831 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _154_832 None _154_831)))
in (repr_type sub.FStar_Syntax_Syntax.target a_typ lift_wp_a)))
in (

let expected_k = (let _154_839 = (let _154_837 = (FStar_Syntax_Syntax.mk_binder a)
in (let _154_836 = (let _154_835 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (let _154_834 = (let _154_833 = (FStar_Syntax_Syntax.null_binder repr_f)
in (_154_833)::[])
in (_154_835)::_154_834))
in (_154_837)::_154_836))
in (let _154_838 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow _154_839 _154_838)))
in (

let _59_1736 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (_59_1736) with
| (expected_k, _59_1733, _59_1735) -> begin
(

let lift = (check_and_gen env lift expected_k)
in Some (lift))
end))))))))
end))
end)
in (

let env = (

let _59_1739 = env
in {FStar_TypeChecker_Env.solver = _59_1739.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_1739.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_1739.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_1739.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_1739.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_1739.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_1739.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_1739.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_1739.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_1739.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_1739.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_1739.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_1739.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_1739.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_1739.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_1739.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_1739.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_1739.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = lax; FStar_TypeChecker_Env.lax_universes = _59_1739.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_1739.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_1739.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_1739.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_1739.FStar_TypeChecker_Env.qname_and_index})
in (

let sub = (

let _59_1742 = sub
in {FStar_Syntax_Syntax.source = _59_1742.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _59_1742.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = Some (lift_wp); FStar_Syntax_Syntax.lift = lift})
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

let _59_1755 = ()
in (

let env0 = env
in (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _59_1761 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_59_1761) with
| (tps, c) -> begin
(

let _59_1765 = (tc_tparams env tps)
in (match (_59_1765) with
| (tps, env, us) -> begin
(

let _59_1769 = (FStar_TypeChecker_TcTerm.tc_comp env c)
in (match (_59_1769) with
| (c, u, g) -> begin
(

let _59_1770 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

let _59_1776 = (let _154_840 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _154_840))
in (match (_59_1776) with
| (uvs, t) -> begin
(

let _59_1795 = (match ((let _154_842 = (let _154_841 = (FStar_Syntax_Subst.compress t)
in _154_841.FStar_Syntax_Syntax.n)
in ((tps), (_154_842)))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_59_1779, c)) -> begin
(([]), (c))
end
| (_59_1785, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
((tps), (c))
end
| _59_1792 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_59_1795) with
| (tps, c) -> begin
(

let _59_1800 = if (((FStar_List.length uvs) <> (Prims.parse_int "1")) && (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid)))) then begin
(

let _59_1799 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_59_1799) with
| (_59_1797, t) -> begin
(let _154_848 = (let _154_847 = (let _154_846 = (let _154_845 = (FStar_Syntax_Print.lid_to_string lid)
in (let _154_844 = (FStar_All.pipe_right (FStar_List.length uvs) FStar_Util.string_of_int)
in (let _154_843 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)" _154_845 _154_844 _154_843))))
in ((_154_846), (r)))
in FStar_Syntax_Syntax.Error (_154_847))
in (Prims.raise _154_848))
end))
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

let _59_1812 = ()
in (

let _59_1816 = (let _154_850 = (let _154_849 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _154_849))
in (check_and_gen env t _154_850))
in (match (_59_1816) with
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

let _59_1836 = (FStar_TypeChecker_TcTerm.tc_term env e)
in (match (_59_1836) with
| (e, c, g1) -> begin
(

let _59_1841 = (let _154_854 = (let _154_851 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_154_851))
in (let _154_853 = (let _154_852 = (c.FStar_Syntax_Syntax.comp ())
in ((e), (_154_852)))
in (FStar_TypeChecker_TcTerm.check_expected_effect env _154_854 _154_853)))
in (match (_59_1841) with
| (e, _59_1839, g) -> begin
(

let _59_1842 = (let _154_855 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _154_855))
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
(let _154_867 = (let _154_866 = (let _154_865 = (let _154_864 = (FStar_Syntax_Print.lid_to_string l)
in (let _154_863 = (FStar_Syntax_Print.quals_to_string q)
in (let _154_862 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _154_864 _154_863 _154_862))))
in ((_154_865), (r)))
in FStar_Syntax_Syntax.Error (_154_866))
in (Prims.raise _154_867))
end
end))
in (

let _59_1886 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _59_1863 lb -> (match (_59_1863) with
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _59_1882 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
((gen), (lb), (quals_opt))
end
| Some ((uvs, tval), quals) -> begin
(

let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (

let _59_1877 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _59_1876 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _154_870 = (FStar_Syntax_Syntax.mk_lb ((FStar_Util.Inr (lbname)), (uvs), (FStar_Syntax_Const.effect_ALL_lid), (tval), (lb.FStar_Syntax_Syntax.lbdef)))
in ((false), (_154_870), (quals_opt)))))
end)
in (match (_59_1882) with
| (gen, lb, quals_opt) -> begin
((gen), ((lb)::lbs), (quals_opt))
end)))
end)) ((true), ([]), (if (quals = []) then begin
None
end else begin
Some (quals)
end))))
in (match (_59_1886) with
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
| _59_1895 -> begin
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

let e = (let _154_874 = (let _154_873 = (let _154_872 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((((Prims.fst lbs)), (lbs'))), (_154_872)))
in FStar_Syntax_Syntax.Tm_let (_154_873))
in (FStar_Syntax_Syntax.mk _154_874 None r))
in (

let _59_1929 = (match ((FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term (

let _59_1899 = env
in {FStar_TypeChecker_Env.solver = _59_1899.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_1899.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_1899.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_1899.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_1899.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_1899.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_1899.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_1899.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_1899.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_1899.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_1899.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _59_1899.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _59_1899.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_1899.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_1899.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_1899.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_1899.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _59_1899.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_1899.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_1899.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_1899.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_1899.FStar_TypeChecker_Env.qname_and_index}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _59_1906; FStar_Syntax_Syntax.pos = _59_1904; FStar_Syntax_Syntax.vars = _59_1902}, _59_1913, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_59_1917, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _59_1923 -> begin
quals
end)
in ((FStar_Syntax_Syntax.Sig_let (((lbs), (r), (lids), (quals)))), (lbs)))
end
| _59_1926 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_59_1929) with
| (se, lbs) -> begin
(

let _59_1935 = if (log env) then begin
(let _154_882 = (let _154_881 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (match ((let _154_878 = (let _154_877 = (let _154_876 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _154_876.FStar_Syntax_Syntax.fv_name)
in _154_877.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _154_878))) with
| None -> begin
true
end
| _59_1933 -> begin
false
end)
in if should_log then begin
(let _154_880 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _154_879 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _154_880 _154_879)))
end else begin
""
end))))
in (FStar_All.pipe_right _154_881 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _154_882))
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
| _59_1945 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _59_1955 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_59_1957) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _59_1968, r) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _59_1975 -> (match (_59_1975) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _59_1981, _59_1983, quals, r) -> begin
(

let dec = (let _154_896 = (let _154_895 = (let _154_894 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow bs _154_894))
in ((l), (us), (_154_895), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (_154_896))
in (((dec)::out), (hidden)))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _59_1993, _59_1995, _59_1997, _59_1999, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]), (r)))
in (((dec)::out), ((l)::hidden)))
end
| _59_2005 -> begin
((out), (hidden))
end)
end)) ses (([]), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end
| FStar_Syntax_Syntax.Sig_assume (_59_2007, _59_2009, quals, _59_2012) -> begin
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
| _59_2031 -> begin
false
end)))) then begin
(((se)::[]), (hidden))
end else begin
(([]), (hidden))
end
end
end
| FStar_Syntax_Syntax.Sig_main (_59_2033) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _59_2052, _59_2054, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
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
(let _154_903 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _154_902 = (let _154_901 = (let _154_900 = (let _154_899 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _154_899.FStar_Syntax_Syntax.fv_name)
in _154_900.FStar_Syntax_Syntax.v)
in ((_154_901), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (_154_902)))))
in ((_154_903), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let process_one_decl = (fun _59_2075 se -> (match (_59_2075) with
| (ses, exports, env, hidden) -> begin
(

let _59_2077 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _154_912 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _154_912))
end else begin
()
end
in (

let _59_2081 = (tc_decl env se)
in (match (_59_2081) with
| (ses', env) -> begin
(

let _59_2084 = if ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _154_917 = (FStar_List.fold_left (fun s se -> (let _154_916 = (let _154_915 = (FStar_Syntax_Print.sigelt_to_string se)
in (Prims.strcat _154_915 "\n"))
in (Prims.strcat s _154_916))) "" ses')
in (FStar_Util.print1 "Checked: %s\n" _154_917))
end else begin
()
end
in (

let _59_2087 = (FStar_List.iter (fun se -> (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)) ses')
in (

let _59_2096 = (FStar_List.fold_left (fun _59_2091 se -> (match (_59_2091) with
| (le, lh) -> begin
(

let tup = (for_export hidden se)
in (((FStar_List.rev_append (Prims.fst tup) le)), ((FStar_List.rev_append (Prims.snd tup) lh))))
end)) (([]), ([])) ses')
in (match (_59_2096) with
| (exported, hidden) -> begin
(((FStar_List.rev_append ses' ses)), (((FStar_List.rev_append exported []))::exports), (env), (hidden))
end))))
end)))
end))
in (

let _59_2126 = (FStar_List.fold_left (fun acc se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, r) -> begin
(

let _59_2110 = acc
in (match (_59_2110) with
| (_59_2104, _59_2106, env, _59_2109) -> begin
(

let _59_2114 = (cps_and_elaborate env ne)
in (match (_59_2114) with
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
| _59_2120 -> begin
(process_one_decl acc se)
end)) (([]), ([]), (env), ([])) ses)
in (match (_59_2126) with
| (ses, exports, env, _59_2125) -> begin
(let _154_923 = (FStar_All.pipe_right (FStar_List.rev_append exports []) FStar_List.flatten)
in (((FStar_List.rev_append ses [])), (_154_923), (env)))
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

let _59_2131 = env
in (let _154_928 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _59_2131.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_2131.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_2131.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_2131.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_2131.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_2131.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_2131.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_2131.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_2131.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_2131.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_2131.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_2131.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_2131.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_2131.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_2131.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_2131.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _154_928; FStar_TypeChecker_Env.lax = _59_2131.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _59_2131.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_2131.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_2131.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_2131.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_2131.FStar_TypeChecker_Env.qname_and_index}))
in (

let _59_2134 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
in (

let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

let _59_2140 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_59_2140) with
| (ses, exports, env) -> begin
(((

let _59_2141 = modul
in {FStar_Syntax_Syntax.name = _59_2141.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _59_2141.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _59_2141.FStar_Syntax_Syntax.is_interface})), (exports), (env))
end))))))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let _59_2149 = (tc_decls env decls)
in (match (_59_2149) with
| (ses, exports, env) -> begin
(

let modul = (

let _59_2150 = modul
in {FStar_Syntax_Syntax.name = _59_2150.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _59_2150.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _59_2150.FStar_Syntax_Syntax.is_interface})
in ((modul), (exports), (env)))
end)))


let check_exports : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env modul exports -> (

let env = (

let _59_2156 = env
in {FStar_TypeChecker_Env.solver = _59_2156.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_2156.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_2156.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_2156.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_2156.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_2156.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_2156.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_2156.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_2156.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_2156.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_2156.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_2156.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_2156.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _59_2156.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_2156.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_2156.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_2156.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = true; FStar_TypeChecker_Env.type_of = _59_2156.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_2156.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_2156.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_2156.FStar_TypeChecker_Env.qname_and_index})
in (

let check_term = (fun lid univs t -> (

let _59_2165 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_59_2165) with
| (univs, t) -> begin
(

let _59_2167 = if (let _154_948 = (let _154_947 = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (FStar_TypeChecker_Env.debug _154_947))
in (FStar_All.pipe_left _154_948 (FStar_Options.Other ("Exports")))) then begin
(let _154_953 = (FStar_Syntax_Print.lid_to_string lid)
in (let _154_952 = (let _154_950 = (FStar_All.pipe_right univs (FStar_List.map (fun x -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (x))))))
in (FStar_All.pipe_right _154_950 (FStar_String.concat ", ")))
in (let _154_951 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print3 "Checking for export %s <%s> : %s\n" _154_953 _154_952 _154_951))))
end else begin
()
end
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env univs)
in (let _154_954 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env t)
in (FStar_All.pipe_right _154_954 Prims.ignore))))
end)))
in (

let check_term = (fun lid univs t -> (

let _59_2174 = (let _154_963 = (let _154_962 = (FStar_Syntax_Print.lid_to_string modul.FStar_Syntax_Syntax.name)
in (let _154_961 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Interface of %s violates its abstraction (add a \'private\' qualifier to \'%s\'?)" _154_962 _154_961)))
in (FStar_TypeChecker_Errors.message_prefix.FStar_TypeChecker_Errors.set_prefix _154_963))
in (

let _59_2176 = (check_term lid univs t)
in (FStar_TypeChecker_Errors.message_prefix.FStar_TypeChecker_Errors.clear_prefix ()))))
in (

let rec check_sigelt = (fun _59_11 -> (match (_59_11) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _59_2183, _59_2185) -> begin
if (not ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private)))) then begin
(FStar_All.pipe_right ses (FStar_List.iter check_sigelt))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_inductive_typ (l, univs, binders, typ, _59_2193, _59_2195, _59_2197, r) -> begin
(

let t = (let _154_968 = (let _154_967 = (let _154_966 = (FStar_Syntax_Syntax.mk_Total typ)
in ((binders), (_154_966)))
in FStar_Syntax_Syntax.Tm_arrow (_154_967))
in (FStar_Syntax_Syntax.mk _154_968 None r))
in (check_term l univs t))
end
| FStar_Syntax_Syntax.Sig_datacon (l, univs, t, _59_2206, _59_2208, _59_2210, _59_2212, _59_2214) -> begin
(check_term l univs t)
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, univs, t, quals, _59_2222) -> begin
if (not ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private)))) then begin
(check_term l univs t)
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_let ((_59_2226, lbs), _59_2230, _59_2232, quals) -> begin
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

let _59_2268 = modul
in {FStar_Syntax_Syntax.name = _59_2268.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _59_2268.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module env modul)
in (

let _59_2272 = (check_exports env modul exports)
in (

let _59_2274 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (

let _59_2276 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (

let _59_2278 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (

let _59_2280 = (let _154_976 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _154_976 Prims.ignore))
in ((modul), (env))))))))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let _59_2287 = (tc_partial_modul env modul)
in (match (_59_2287) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (

let _59_2290 = if (FStar_Options.debug_any ()) then begin
(let _154_985 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _154_985))
end else begin
()
end
in (

let _59_2294 = (tc_modul env m)
in (match (_59_2294) with
| (m, env) -> begin
(

let _59_2295 = if (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _154_986 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _154_986))
end else begin
()
end
in ((m), (env)))
end))))




