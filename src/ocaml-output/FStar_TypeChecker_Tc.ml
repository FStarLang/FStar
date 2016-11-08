
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
in {FStar_Syntax_Syntax.action_name = _59_144.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = _59_144.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = _59_144.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _154_87; FStar_Syntax_Syntax.action_typ = _154_86})))) ed.FStar_Syntax_Syntax.actions)
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

let _59_366 = (match ((let _154_212 = (FStar_Syntax_Subst.compress ed.FStar_Syntax_Syntax.repr)
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

let _59_306 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env act.FStar_Syntax_Syntax.action_typ)
in (match (_59_306) with
| (act_typ, _59_304, g_t) -> begin
(

let env' = (FStar_TypeChecker_Env.set_expected_typ env act_typ)
in (

let _59_308 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _154_294 = (FStar_Syntax_Print.term_to_string act.FStar_Syntax_Syntax.action_defn)
in (let _154_293 = (FStar_Syntax_Print.term_to_string act_typ)
in (FStar_Util.print3 "Checking action %s:\n[definition]: %s\n[cps\'d type]: %s\n" (FStar_Ident.text_of_lid act.FStar_Syntax_Syntax.action_name) _154_294 _154_293)))
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

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
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

let k = (let _154_295 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs _154_295))
in (

let _59_332 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env k)
in (match (_59_332) with
| (k, _59_330, g) -> begin
((k), (g))
end))))
end))
end
| _59_334 -> begin
(let _154_300 = (let _154_299 = (let _154_298 = (let _154_297 = (FStar_Syntax_Print.term_to_string act_typ)
in (let _154_296 = (FStar_Syntax_Print.tag_of_term act_typ)
in (FStar_Util.format2 "Actions must have function types (not: %s, a.k.a. %s)" _154_297 _154_296)))
in ((_154_298), (act_defn.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_154_299))
in (Prims.raise _154_300))
end))
in (match (_59_337) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env act_typ expected_k)
in (

let _59_339 = (let _154_303 = (let _154_302 = (let _154_301 = (FStar_TypeChecker_Rel.conj_guard g_t g)
in (FStar_TypeChecker_Rel.conj_guard g_k _154_301))
in (FStar_TypeChecker_Rel.conj_guard g_a _154_302))
in (FStar_TypeChecker_Rel.force_trivial_guard env _154_303))
in (

let act_typ = (match ((let _154_304 = (FStar_Syntax_Subst.compress expected_k)
in _154_304.FStar_Syntax_Syntax.n)) with
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
in {FStar_Syntax_Syntax.action_name = _59_359.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = _59_359.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = act_defn; FStar_Syntax_Syntax.action_typ = act_typ}))
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

let t = (let _154_310 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _154_310))
in (

let _59_370 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_59_370) with
| (univs, t) -> begin
(

let signature = (match ((let _154_312 = (let _154_311 = (FStar_Syntax_Subst.compress t)
in _154_311.FStar_Syntax_Syntax.n)
in ((effect_params), (_154_312)))) with
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

let ts = (let _154_317 = (FStar_Syntax_Subst.close_tscheme effect_params ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _154_317))
in (

let _59_390 = if (((n > (Prims.parse_int "0")) && (not ((FStar_Syntax_Util.is_unknown (Prims.snd ts))))) && ((FStar_List.length (Prims.fst ts)) <> n)) then begin
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
in {FStar_Syntax_Syntax.action_name = _59_402.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = _59_402.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = defn; FStar_Syntax_Syntax.action_typ = typ}))
end))
end)))
in (

let _59_404 = ()
in (

let ed = (

let _59_406 = ed
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
in {FStar_Syntax_Syntax.qualifiers = _59_406.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _59_406.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _154_337; FStar_Syntax_Syntax.bind_wp = _154_336; FStar_Syntax_Syntax.if_then_else = _154_335; FStar_Syntax_Syntax.ite_wp = _154_334; FStar_Syntax_Syntax.stronger = _154_333; FStar_Syntax_Syntax.close_wp = _154_332; FStar_Syntax_Syntax.assert_p = _154_331; FStar_Syntax_Syntax.assume_p = _154_330; FStar_Syntax_Syntax.null_wp = _154_329; FStar_Syntax_Syntax.trivial = _154_328; FStar_Syntax_Syntax.repr = _154_327; FStar_Syntax_Syntax.return_repr = _154_326; FStar_Syntax_Syntax.bind_repr = _154_325; FStar_Syntax_Syntax.actions = _154_324})))))))))))))))
in (

let _59_409 = if ((FStar_TypeChecker_Env.debug env FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ED")))) then begin
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
(let _154_343 = (

let _59_428 = bv
in (let _154_342 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _59_428.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_428.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _154_342}))
in ((_154_343), (qual)))
end)) effect_binders)
in (

let _59_443 = (match ((let _154_344 = (FStar_Syntax_Subst.compress signature_un)
in _154_344.FStar_Syntax_Syntax.n)) with
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
(let _154_349 = (FStar_Syntax_Print.term_to_string repr)
in (FStar_Util.print1 "Representation is: %s\n" _154_349))
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

let wp_a = (let _154_356 = (let _154_355 = (let _154_354 = (let _154_353 = (let _154_352 = (let _154_351 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _154_350 = (FStar_Syntax_Syntax.as_implicit false)
in ((_154_351), (_154_350))))
in (_154_352)::[])
in ((wp_type), (_154_353)))
in FStar_Syntax_Syntax.Tm_app (_154_354))
in (mk _154_355))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _154_356))
in (

let effect_signature = (

let binders = (let _154_361 = (let _154_357 = (FStar_Syntax_Syntax.as_implicit false)
in ((a), (_154_357)))
in (let _154_360 = (let _154_359 = (let _154_358 = (FStar_Syntax_Syntax.gen_bv "dijkstra_wp" None wp_a)
in (FStar_All.pipe_right _154_358 FStar_Syntax_Syntax.mk_binder))
in (_154_359)::[])
in (_154_361)::_154_360))
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
(let _154_371 = (let _154_370 = (let _154_369 = (FStar_Syntax_Print.term_to_string item)
in (let _154_368 = (FStar_Syntax_Print.lcomp_to_string item_comp)
in (FStar_Util.format2 "Computation for [%s] is not total : %s !" _154_369 _154_368)))
in FStar_Syntax_Syntax.Err (_154_370))
in (Prims.raise _154_371))
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

let lift_from_pure_wp = (match ((let _154_372 = (FStar_Syntax_Subst.compress return_wp)
in _154_372.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(

let _59_515 = (FStar_Syntax_Subst.open_term ((b1)::(b2)::bs) body)
in (match (_59_515) with
| ((b1)::(b2)::bs, body) -> begin
(

let _59_518 = (FStar_Syntax_Util.abs_formals body)
in (match (_59_518) with
| (bs', body) -> begin
(

let t2 = (Prims.fst b2).FStar_Syntax_Syntax.sort
in (

let pure_wp_type = (let _154_381 = (let _154_379 = (let _154_378 = (let _154_377 = (let _154_376 = (let _154_374 = (let _154_373 = (FStar_Syntax_Syntax.null_bv t2)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _154_373))
in (_154_374)::[])
in (let _154_375 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _154_376 _154_375)))
in (FStar_Syntax_Syntax.null_bv _154_377))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _154_378))
in (_154_379)::[])
in (let _154_380 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _154_381 _154_380)))
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None pure_wp_type)
in (

let body = (let _154_385 = (FStar_Syntax_Syntax.bv_to_name wp)
in (let _154_384 = (let _154_383 = (let _154_382 = (FStar_Syntax_Util.abs ((b2)::[]) body what)
in ((_154_382), (None)))
in (_154_383)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _154_385 _154_384 None FStar_Range.dummyRange)))
in (let _154_389 = (let _154_387 = (let _154_386 = (FStar_Syntax_Syntax.mk_binder wp)
in (_154_386)::[])
in (b1)::_154_387)
in (let _154_388 = (FStar_Syntax_Util.abs (FStar_List.append bs bs') body what)
in (FStar_Syntax_Util.abs _154_389 _154_388 (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_GTot_lid))))))))))
end))
end))
end
| _59_524 -> begin
(FStar_All.failwith "unexpected shape for return")
end)
in (

let return_wp = (match ((let _154_390 = (FStar_Syntax_Subst.compress return_wp)
in _154_390.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(let _154_391 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs ((b1)::(b2)::[]) _154_391 (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_GTot_lid)))))
end
| _59_536 -> begin
(FStar_All.failwith "unexpected shape for return")
end)
in (

let bind_wp = (match ((let _154_392 = (FStar_Syntax_Subst.compress bind_wp)
in _154_392.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let r = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (let _154_396 = (let _154_395 = (let _154_394 = (let _154_393 = (mk (FStar_Syntax_Syntax.Tm_fvar (r)))
in (FStar_Syntax_Syntax.null_binder _154_393))
in (_154_394)::[])
in (FStar_List.append _154_395 binders))
in (FStar_Syntax_Util.abs _154_396 body what)))
end
| _59_545 -> begin
(FStar_All.failwith "unexpected shape for bind")
end)
in (

let apply_close = (fun t -> if ((FStar_List.length effect_binders) = (Prims.parse_int "0")) then begin
t
end else begin
(let _154_403 = (let _154_402 = (let _154_401 = (let _154_400 = (let _154_399 = (FStar_Syntax_Util.args_of_binders effect_binders)
in (Prims.snd _154_399))
in ((t), (_154_400)))
in FStar_Syntax_Syntax.Tm_app (_154_401))
in (mk _154_402))
in (FStar_Syntax_Subst.close effect_binders _154_403))
end)
in (

let register = (fun name item -> (

let _59_554 = (let _154_409 = (mk_lid name)
in (let _154_408 = (FStar_Syntax_Util.abs effect_binders item None)
in (FStar_TypeChecker_Util.mk_toplevel_definition env _154_409 _154_408)))
in (match (_59_554) with
| (sigelt, fv) -> begin
(

let _59_555 = (let _154_411 = (let _154_410 = (FStar_ST.read sigelts)
in (sigelt)::_154_410)
in (FStar_ST.op_Colon_Equals sigelts _154_411))
in fv)
end)))
in (

let lift_from_pure_wp = (register "lift_from_pure" lift_from_pure_wp)
in (

let return_wp = (register "return_wp" return_wp)
in (

let return_elab = (register "return_elab" return_elab)
in (

let bind_wp = (register "bind_wp" bind_wp)
in (

let _59_561 = (let _154_413 = (let _154_412 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true")), (FStar_Range.dummyRange))))::_154_412)
in (FStar_ST.op_Colon_Equals sigelts _154_413))
in (

let bind_elab = (register "bind_elab" bind_elab)
in (

let _59_564 = (let _154_415 = (let _154_414 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false")), (FStar_Range.dummyRange))))::_154_414)
in (FStar_ST.op_Colon_Equals sigelts _154_415))
in (

let _59_583 = (FStar_List.fold_left (fun _59_568 action -> (match (_59_568) with
| (dmff_env, actions) -> begin
(

let _59_574 = (elaborate_and_star dmff_env ((action.FStar_Syntax_Syntax.action_univs), (action.FStar_Syntax_Syntax.action_defn)))
in (match (_59_574) with
| (dmff_env, action_t, action_wp, action_elab) -> begin
(

let name = action.FStar_Syntax_Syntax.action_name.FStar_Ident.ident.FStar_Ident.idText
in (

let action_typ_with_wp = (FStar_TypeChecker_DMFF.trans_F dmff_env action_t action_wp)
in (

let action_elab = (register (Prims.strcat name "_elab") action_elab)
in (

let action_typ_with_wp = (register (Prims.strcat name "_complete_type") action_typ_with_wp)
in (let _154_421 = (let _154_420 = (

let _59_579 = action
in (let _154_419 = (apply_close action_elab)
in (let _154_418 = (apply_close action_typ_with_wp)
in {FStar_Syntax_Syntax.action_name = _59_579.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = _59_579.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = _59_579.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _154_419; FStar_Syntax_Syntax.action_typ = _154_418})))
in (_154_420)::actions)
in ((dmff_env), (_154_421)))))))
end))
end)) ((dmff_env), ([])) ed.FStar_Syntax_Syntax.actions)
in (match (_59_583) with
| (dmff_env, actions) -> begin
(

let actions = (FStar_List.rev actions)
in (

let repr = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp_a" None wp_a)
in (

let binders = (let _154_424 = (FStar_Syntax_Syntax.mk_binder a)
in (let _154_423 = (let _154_422 = (FStar_Syntax_Syntax.mk_binder wp)
in (_154_422)::[])
in (_154_424)::_154_423))
in (let _154_433 = (let _154_432 = (let _154_430 = (let _154_429 = (let _154_428 = (let _154_427 = (let _154_426 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _154_425 = (FStar_Syntax_Syntax.as_implicit false)
in ((_154_426), (_154_425))))
in (_154_427)::[])
in ((repr), (_154_428)))
in FStar_Syntax_Syntax.Tm_app (_154_429))
in (mk _154_430))
in (let _154_431 = (FStar_Syntax_Syntax.bv_to_name wp)
in (FStar_TypeChecker_DMFF.trans_F dmff_env _154_432 _154_431)))
in (FStar_Syntax_Util.abs binders _154_433 None))))
in (

let repr = (recheck_debug "FC" env repr)
in (

let repr = (register "repr" repr)
in (

let _59_615 = (match ((let _154_434 = (FStar_Syntax_Subst.compress wp_type)
in _154_434.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (effect_param, arrow, _59_593) -> begin
(

let _59_598 = (FStar_Syntax_Subst.open_term effect_param arrow)
in (match (_59_598) with
| (effect_param, arrow) -> begin
(match ((let _154_435 = (FStar_Syntax_Subst.compress arrow)
in _154_435.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (wp_binders, c) -> begin
(

let _59_605 = (FStar_Syntax_Subst.open_comp wp_binders c)
in (match (_59_605) with
| (wp_binders, c) -> begin
(

let _59_608 = (FStar_Util.prefix wp_binders)
in (match (_59_608) with
| (pre_args, post) -> begin
(let _154_437 = (FStar_Syntax_Util.arrow pre_args c)
in (let _154_436 = (FStar_Syntax_Util.abs effect_param (Prims.fst post).FStar_Syntax_Syntax.sort None)
in ((_154_437), (_154_436))))
end))
end))
end
| _59_610 -> begin
(let _154_439 = (let _154_438 = (FStar_Syntax_Print.term_to_string arrow)
in (FStar_Util.format1 "Impossible: pre/post arrow %s" _154_438))
in (FStar_All.failwith _154_439))
end)
end))
end
| _59_612 -> begin
(let _154_441 = (let _154_440 = (FStar_Syntax_Print.term_to_string wp_type)
in (FStar_Util.format1 "Impossible: pre/post abs %s" _154_440))
in (FStar_All.failwith _154_441))
end)
in (match (_59_615) with
| (pre, post) -> begin
(

let _59_616 = (let _154_442 = (register "pre" pre)
in (Prims.ignore _154_442))
in (

let _59_618 = (let _154_443 = (register "post" post)
in (Prims.ignore _154_443))
in (

let _59_620 = (let _154_444 = (register "wp" wp_type)
in (Prims.ignore _154_444))
in (

let ed = (

let _59_622 = ed
in (let _154_455 = (FStar_Syntax_Subst.close_binders effect_binders)
in (let _154_454 = (FStar_Syntax_Subst.close effect_binders effect_signature)
in (let _154_453 = (let _154_445 = (apply_close return_wp)
in (([]), (_154_445)))
in (let _154_452 = (let _154_446 = (apply_close bind_wp)
in (([]), (_154_446)))
in (let _154_451 = (apply_close repr)
in (let _154_450 = (let _154_447 = (apply_close return_elab)
in (([]), (_154_447)))
in (let _154_449 = (let _154_448 = (apply_close bind_elab)
in (([]), (_154_448)))
in {FStar_Syntax_Syntax.qualifiers = _59_622.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.mname = _59_622.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _59_622.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _154_455; FStar_Syntax_Syntax.signature = _154_454; FStar_Syntax_Syntax.ret_wp = _154_453; FStar_Syntax_Syntax.bind_wp = _154_452; FStar_Syntax_Syntax.if_then_else = _59_622.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _59_622.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _59_622.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _59_622.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _59_622.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _59_622.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _59_622.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _59_622.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _154_451; FStar_Syntax_Syntax.return_repr = _154_450; FStar_Syntax_Syntax.bind_repr = _154_449; FStar_Syntax_Syntax.actions = actions}))))))))
in (

let _59_627 = (FStar_TypeChecker_DMFF.gen_wps_for_free env effect_binders a wp_a ed)
in (match (_59_627) with
| (sigelts', ed) -> begin
(

let _59_628 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _154_456 = (FStar_Syntax_Print.eff_decl_to_string true ed)
in (FStar_Util.print_string _154_456))
end else begin
()
end
in (

let lift_from_pure_opt = if ((FStar_List.length effect_binders) = (Prims.parse_int "0")) then begin
(

let lift_from_pure = (let _154_459 = (let _154_458 = (let _154_457 = (apply_close lift_from_pure_wp)
in (([]), (_154_457)))
in Some (_154_458))
in {FStar_Syntax_Syntax.source = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.target = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.lift_wp = _154_459; FStar_Syntax_Syntax.lift = None})
in Some (FStar_Syntax_Syntax.Sig_sub_effect (((lift_from_pure), (FStar_Range.dummyRange)))))
end else begin
None
end
in (let _154_462 = (let _154_461 = (let _154_460 = (FStar_ST.read sigelts)
in (FStar_List.rev _154_460))
in (FStar_List.append _154_461 sigelts'))
in ((_154_462), (ed), (lift_from_pure_opt)))))
end))))))
end))))))
end))))))))))))))
end))
end))))))))))))
end))))
end)))
end))
end))
end)))
and tc_lex_t : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt = (fun env ses quals lids -> (

let _59_636 = ()
in (

let _59_644 = ()
in (match (ses) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _59_673, _59_675, [], r))::(FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, _154_467, [], _59_664, r1))::(FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, _154_468, [], _59_653, r2))::[] when (((_154_467 = (Prims.parse_int "0")) && (_154_468 = (Prims.parse_int "0"))) && (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid))) -> begin
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

let lex_top_t = (let _154_471 = (let _154_470 = (let _154_469 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1) FStar_Syntax_Syntax.Delta_constant None)
in ((_154_469), ((FStar_Syntax_Syntax.U_name (utop))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_154_470))
in (FStar_Syntax_Syntax.mk _154_471 None r1))
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

let a = (let _154_472 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _154_472))
in (

let hd = (let _154_473 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _154_473))
in (

let tl = (let _154_477 = (let _154_476 = (let _154_475 = (let _154_474 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2) FStar_Syntax_Syntax.Delta_constant None)
in ((_154_474), ((FStar_Syntax_Syntax.U_name (ucons2))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_154_475))
in (FStar_Syntax_Syntax.mk _154_476 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _154_477))
in (

let res = (let _154_480 = (let _154_479 = (let _154_478 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2) FStar_Syntax_Syntax.Delta_constant None)
in ((_154_478), ((FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_154_479))
in (FStar_Syntax_Syntax.mk _154_480 None r2))
in (let _154_481 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow ((((a), (Some (FStar_Syntax_Syntax.imp_tag))))::(((hd), (None)))::(((tl), (None)))::[]) _154_481))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon (((lex_cons), ((ucons1)::(ucons2)::[]), (lex_cons_t), (FStar_Syntax_Const.lex_t_lid), ((Prims.parse_int "0")), ([]), ([]), (r2)))
in (let _154_483 = (let _154_482 = (FStar_TypeChecker_Env.get_range env)
in (((tc)::(dc_lextop)::(dc_lexcons)::[]), ([]), (lids), (_154_482)))
in FStar_Syntax_Syntax.Sig_bundle (_154_483)))))))))))))))
end
| _59_699 -> begin
(let _154_485 = (let _154_484 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle (((ses), ([]), (lids), (FStar_Range.dummyRange)))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _154_484))
in (FStar_All.failwith _154_485))
end))))
and tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _59_709 = (FStar_Syntax_Util.type_u ())
in (match (_59_709) with
| (k, _59_708) -> begin
(

let phi = (let _154_491 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _154_491 (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env)))
in (

let _59_711 = (FStar_TypeChecker_Util.check_uvars r phi)
in FStar_Syntax_Syntax.Sig_assume (((lid), (phi), (quals), (r)))))
end))))
and tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun env ses quals lids -> (

let warn_positivity = (fun l r -> (let _154_501 = (let _154_500 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _154_500))
in (FStar_TypeChecker_Errors.diag r _154_501)))
in (

let env0 = env
in (

let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(

let _59_734 = ()
in (

let _59_736 = (warn_positivity tc r)
in (

let _59_740 = (FStar_Syntax_Subst.open_term tps k)
in (match (_59_740) with
| (tps, k) -> begin
(

let _59_745 = (FStar_TypeChecker_TcTerm.tc_binders env tps)
in (match (_59_745) with
| (tps, env_tps, guard_params, us) -> begin
(

let _59_748 = (FStar_Syntax_Util.arrow_formals k)
in (match (_59_748) with
| (indices, t) -> begin
(

let _59_753 = (FStar_TypeChecker_TcTerm.tc_binders env_tps indices)
in (match (_59_753) with
| (indices, env', guard_indices, us') -> begin
(

let _59_761 = (

let _59_758 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' t)
in (match (_59_758) with
| (t, _59_756, g) -> begin
(let _154_508 = (let _154_507 = (let _154_506 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params _154_506))
in (FStar_TypeChecker_Rel.discharge_guard env' _154_507))
in ((t), (_154_508)))
end))
in (match (_59_761) with
| (t, guard) -> begin
(

let k = (let _154_509 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _154_509))
in (

let _59_765 = (FStar_Syntax_Util.type_u ())
in (match (_59_765) with
| (t_type, u) -> begin
(

let _59_766 = (let _154_510 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _154_510))
in (

let t_tc = (let _154_511 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _154_511))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _154_512 = (FStar_TypeChecker_Env.push_let_binding env_tps (FStar_Util.Inr (fv_tc)) (([]), (t_tc)))
in ((_154_512), (FStar_Syntax_Syntax.Sig_inductive_typ (((tc), ([]), (tps), (k), (mutuals), (data), (quals), (r)))), (u), (guard))))))))
end)))
end))
end))
end))
end))
end))))
end
| _59_773 -> begin
(FStar_All.failwith "impossible")
end))
in (

let positive_if_pure = (fun _59_775 l -> ())
in (

let tc_data = (fun env tcs _59_1 -> (match (_59_1) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let _59_792 = ()
in (

let _59_827 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun _59_796 -> (match (_59_796) with
| (se, u_tc) -> begin
if (let _154_525 = (let _154_524 = (FStar_Syntax_Util.lid_of_sigelt se)
in (FStar_Util.must _154_524))
in (FStar_Ident.lid_equals tc_lid _154_525)) then begin
(

let tps = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_59_798, _59_800, tps, _59_803, _59_805, _59_807, _59_809, _59_811) -> begin
(FStar_All.pipe_right tps (FStar_List.map (fun _59_817 -> (match (_59_817) with
| (x, _59_816) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
end
| _59_819 -> begin
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
in (match (_59_827) with
| (tps, u_tc) -> begin
(

let _59_847 = (match ((let _154_527 = (FStar_Syntax_Subst.compress t)
in _154_527.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let _59_835 = (FStar_Util.first_N ntps bs)
in (match (_59_835) with
| (_59_833, bs') -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs'), (res)))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _59_841 -> (match (_59_841) with
| (x, _59_840) -> begin
FStar_Syntax_Syntax.DB ((((ntps - ((Prims.parse_int "1") + i))), (x)))
end))))
in (let _154_530 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _154_530))))
end))
end
| _59_844 -> begin
(([]), (t))
end)
in (match (_59_847) with
| (arguments, result) -> begin
(

let _59_848 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _154_533 = (FStar_Syntax_Print.lid_to_string c)
in (let _154_532 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _154_531 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _154_533 _154_532 _154_531))))
end else begin
()
end
in (

let _59_853 = (tc_tparams env arguments)
in (match (_59_853) with
| (arguments, env', us) -> begin
(

let _59_856 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env' result)
in (match (_59_856) with
| (result, res_lcomp) -> begin
(

let _59_861 = (match ((let _154_534 = (FStar_Syntax_Subst.compress res_lcomp.FStar_Syntax_Syntax.res_typ)
in _154_534.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_59_858) -> begin
()
end
| ty -> begin
(let _154_539 = (let _154_538 = (let _154_537 = (let _154_536 = (FStar_Syntax_Print.term_to_string result)
in (let _154_535 = (FStar_Syntax_Print.term_to_string res_lcomp.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "The type of %s is %s, but since this is the result type of a constructor its type should be Type" _154_536 _154_535)))
in ((_154_537), (r)))
in FStar_Syntax_Syntax.Error (_154_538))
in (Prims.raise _154_539))
end)
in (

let _59_866 = (FStar_Syntax_Util.head_and_args result)
in (match (_59_866) with
| (head, _59_865) -> begin
(

let _59_871 = (match ((let _154_540 = (FStar_Syntax_Subst.compress head)
in _154_540.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _59_870 -> begin
(let _154_545 = (let _154_544 = (let _154_543 = (let _154_542 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (let _154_541 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" _154_542 _154_541)))
in ((_154_543), (r)))
in FStar_Syntax_Syntax.Error (_154_544))
in (Prims.raise _154_545))
end)
in (

let g = (FStar_List.fold_left2 (fun g _59_877 u_x -> (match (_59_877) with
| (x, _59_876) -> begin
(

let _59_879 = ()
in (let _154_549 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _154_549)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _154_553 = (let _154_551 = (FStar_All.pipe_right tps (FStar_List.map (fun _59_885 -> (match (_59_885) with
| (x, _59_884) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append _154_551 arguments))
in (let _154_552 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _154_553 _154_552)))
in ((FStar_Syntax_Syntax.Sig_datacon (((c), ([]), (t), (tc_lid), (ntps), (quals), ([]), (r)))), (g)))))
end)))
end))
end)))
end))
end)))
end
| _59_888 -> begin
(FStar_All.failwith "impossible")
end))
in (

let generalize_and_inst_within = (fun env g tcs datas -> (

let _59_894 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _59_2 -> (match (_59_2) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_59_898, _59_900, tps, k, _59_904, _59_906, _59_908, _59_910) -> begin
(let _154_564 = (let _154_563 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _154_563))
in (FStar_Syntax_Syntax.null_binder _154_564))
end
| _59_914 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _59_3 -> (match (_59_3) with
| FStar_Syntax_Syntax.Sig_datacon (_59_918, _59_920, t, _59_923, _59_925, _59_927, _59_929, _59_931) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _59_935 -> begin
(FStar_All.failwith "Impossible")
end))))
in (

let t = (let _154_566 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _154_566))
in (

let _59_938 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _154_567 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _154_567))
end else begin
()
end
in (

let _59_942 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_59_942) with
| (uvs, t) -> begin
(

let _59_944 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _154_571 = (let _154_569 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _154_569 (FStar_String.concat ", ")))
in (let _154_570 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _154_571 _154_570)))
end else begin
()
end
in (

let _59_948 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_59_948) with
| (uvs, t) -> begin
(

let _59_952 = (FStar_Syntax_Util.arrow_formals t)
in (match (_59_952) with
| (args, _59_951) -> begin
(

let _59_955 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_59_955) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun _59_959 se -> (match (_59_959) with
| (x, _59_958) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _59_963, tps, _59_966, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let _59_989 = (match ((let _154_574 = (FStar_Syntax_Subst.compress ty)
in _154_574.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _59_980 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_59_980) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _59_983 -> begin
(let _154_575 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) _154_575 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in ((tps), (t)))
end))
end
| _59_986 -> begin
(([]), (ty))
end)
in (match (_59_989) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs), (tps), (t), (mutuals), (datas), (quals), (r)))
end)))
end
| _59_991 -> begin
(FStar_All.failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| _59_995 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _154_576 -> FStar_Syntax_Syntax.U_name (_154_576))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _59_4 -> (match (_59_4) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _59_1000, _59_1002, _59_1004, _59_1006, _59_1008, _59_1010, _59_1012) -> begin
((tc), (uvs_universes))
end
| _59_1016 -> begin
(FStar_All.failwith "Impossible")
end))))
in (FStar_List.map2 (fun _59_1021 d -> (match (_59_1021) with
| (t, _59_1020) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _59_1025, _59_1027, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (let _154_580 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _154_580 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon (((l), (uvs), (ty), (tc), (ntps), (quals), (mutuals), (r))))
end
| _59_1037 -> begin
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

let _59_1047 = (FStar_All.pipe_right ses (FStar_List.partition (fun _59_5 -> (match (_59_5) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_59_1041) -> begin
true
end
| _59_1044 -> begin
false
end))))
in (match (_59_1047) with
| (tys, datas) -> begin
(

let _59_1054 = if (FStar_All.pipe_right datas (FStar_Util.for_some (fun _59_6 -> (match (_59_6) with
| FStar_Syntax_Syntax.Sig_datacon (_59_1050) -> begin
false
end
| _59_1053 -> begin
true
end)))) then begin
(let _154_585 = (let _154_584 = (let _154_583 = (FStar_TypeChecker_Env.get_range env)
in (("Mutually defined type contains a non-inductive element"), (_154_583)))
in FStar_Syntax_Syntax.Error (_154_584))
in (Prims.raise _154_585))
end else begin
()
end
in (

let env0 = env
in (

let _59_1073 = (FStar_List.fold_right (fun tc _59_1061 -> (match (_59_1061) with
| (env, all_tcs, g) -> begin
(

let _59_1066 = (tc_tycon env tc)
in (match (_59_1066) with
| (env, tc, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (

let _59_1068 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _154_588 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _154_588))
end else begin
()
end
in (let _154_590 = (let _154_589 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g _154_589))
in ((env), ((((tc), (tc_u)))::all_tcs), (_154_590)))))
end))
end)) tys ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (_59_1073) with
| (env, tcs, g) -> begin
(

let _59_1083 = (FStar_List.fold_right (fun se _59_1077 -> (match (_59_1077) with
| (datas, g) -> begin
(

let _59_1080 = (tc_data env tcs se)
in (match (_59_1080) with
| (data, g') -> begin
(let _154_593 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((data)::datas), (_154_593)))
end))
end)) datas (([]), (g)))
in (match (_59_1083) with
| (datas, g) -> begin
(

let _59_1086 = (let _154_594 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _154_594 datas))
in (match (_59_1086) with
| (tcs, datas) -> begin
(

let sig_bndle = (let _154_596 = (let _154_595 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_154_595)))
in FStar_Syntax_Syntax.Sig_bundle (_154_596))
in (

let datacon_typ = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (_59_1091, _59_1093, t, _59_1096, _59_1098, _59_1100, _59_1102, _59_1104) -> begin
t
end
| _59_1108 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let dr = FStar_Range.dummyRange
in (

let optimized_haseq_scheme = (fun _59_1111 -> (

let haseq_ty = (fun usubst us acc ty -> (

let _59_1138 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _59_1120, bs, t, _59_1124, d_lids, _59_1127, _59_1129) -> begin
((lid), (bs), (t), (d_lids))
end
| _59_1133 -> begin
(FStar_All.failwith "Impossible!")
end)
in (match (_59_1138) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _154_609 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _154_609 t))
in (

let _59_1143 = (FStar_Syntax_Subst.open_term bs t)
in (match (_59_1143) with
| (bs, t) -> begin
(

let ibs = (match ((let _154_610 = (FStar_Syntax_Subst.compress t)
in _154_610.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _59_1146) -> begin
ibs
end
| _59_1150 -> begin
[]
end)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _154_613 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _154_612 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _154_613 _154_612)))
in (

let ind = (let _154_616 = (FStar_List.map (fun _59_1157 -> (match (_59_1157) with
| (bv, aq) -> begin
(let _154_615 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_154_615), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _154_616 None dr))
in (

let ind = (let _154_619 = (FStar_List.map (fun _59_1161 -> (match (_59_1161) with
| (bv, aq) -> begin
(let _154_618 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_154_618), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _154_619 None dr))
in (

let haseq_ind = (let _154_621 = (let _154_620 = (FStar_Syntax_Syntax.as_arg ind)
in (_154_620)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _154_621 None dr))
in (

let bs' = (FStar_List.filter (fun b -> (

let _59_1172 = acc
in (match (_59_1172) with
| (_59_1166, en, _59_1169, _59_1171) -> begin
(

let opt = (let _154_624 = (let _154_623 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _154_623))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort _154_624 false))
in (match (opt) with
| None -> begin
false
end
| Some (_59_1176) -> begin
true
end))
end))) bs)
in (

let haseq_bs = (FStar_List.fold_left (fun t b -> (let _154_630 = (let _154_629 = (let _154_628 = (let _154_627 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b))
in (FStar_Syntax_Syntax.as_arg _154_627))
in (_154_628)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _154_629 None dr))
in (FStar_Syntax_Util.mk_conj t _154_630))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml = (

let _59_1183 = fml
in (let _154_636 = (let _154_635 = (let _154_634 = (let _154_633 = (let _154_632 = (let _154_631 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_154_631)::[])
in (_154_632)::[])
in FStar_Syntax_Syntax.Meta_pattern (_154_633))
in ((fml), (_154_634)))
in FStar_Syntax_Syntax.Tm_meta (_154_635))
in {FStar_Syntax_Syntax.n = _154_636; FStar_Syntax_Syntax.tk = _59_1183.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _59_1183.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _59_1183.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _154_642 = (let _154_641 = (let _154_640 = (let _154_639 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _154_639 None))
in (FStar_Syntax_Syntax.as_arg _154_640))
in (_154_641)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _154_642 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _154_648 = (let _154_647 = (let _154_646 = (let _154_645 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _154_645 None))
in (FStar_Syntax_Syntax.as_arg _154_646))
in (_154_647)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _154_648 None dr))) bs fml)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let _59_1197 = acc
in (match (_59_1197) with
| (l_axioms, env, guard', cond') -> begin
(

let env = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env = (FStar_TypeChecker_Env.push_binders env ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (_59_1202, _59_1204, _59_1206, t_lid, _59_1209, _59_1211, _59_1213, _59_1215) -> begin
(t_lid = lid)
end
| _59_1219 -> begin
(FStar_All.failwith "Impossible")
end)) datas)
in (

let haseq_data = (fun data -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (match ((let _154_652 = (FStar_Syntax_Subst.compress dt)
in _154_652.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _59_1227) -> begin
(

let dbs = (let _154_653 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _154_653))
in (

let dbs = (let _154_654 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _154_654 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let haseq_b = (let _154_658 = (let _154_657 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_154_657)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _154_658 None dr))
in (

let sort_range = (Prims.fst b).FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos
in (

let haseq_b = (let _154_660 = (let _154_659 = (FStar_Syntax_Print.term_to_string ind)
in (FStar_Util.format1 "Failed to prove that the type \'%s\' supports decidable equality because of this argument; add the \'noeq\' qualifier" _154_659))
in (FStar_TypeChecker_Util.label _154_660 sort_range haseq_b))
in (FStar_Syntax_Util.mk_conj t haseq_b))))) FStar_Syntax_Util.t_true dbs)
in (FStar_List.fold_right (fun b t -> (let _154_666 = (let _154_665 = (let _154_664 = (let _154_663 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _154_663 None))
in (FStar_Syntax_Syntax.as_arg _154_664))
in (_154_665)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _154_666 None dr))) dbs cond)))))
end
| _59_1242 -> begin
FStar_Syntax_Util.t_true
end))))
in (

let cond = (FStar_List.fold_left (fun acc d -> (let _154_669 = (haseq_data d)
in (FStar_Syntax_Util.mk_conj acc _154_669))) FStar_Syntax_Util.t_true t_datas)
in (

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (let _154_671 = (FStar_Syntax_Util.mk_conj guard' guard)
in (let _154_670 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml)))::[]))), (env), (_154_671), (_154_670))))))))))
end)))))))))))))))
end))))
end)))
in (

let us = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_59_1249, us, _59_1252, _59_1254, _59_1256, _59_1258, _59_1260, _59_1262) -> begin
us
end
| _59_1266 -> begin
(FStar_All.failwith "Impossible!")
end))
in (

let _59_1270 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (_59_1270) with
| (usubst, us) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (

let _59_1272 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq")
in (

let _59_1274 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle)
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let _59_1281 = (FStar_List.fold_left (haseq_ty usubst us) (([]), (env), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (_59_1281) with
| (axioms, env, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let _59_1286 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env phi)
in (match (_59_1286) with
| (phi, _59_1285) -> begin
(

let _59_1287 = if (FStar_TypeChecker_Env.should_verify env) then begin
(let _154_672 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi)))
in (FStar_TypeChecker_Rel.force_trivial_guard env _154_672))
end else begin
()
end
in (

let ses = (FStar_List.fold_left (fun l _59_1292 -> (match (_59_1292) with
| (lid, fml) -> begin
(

let se = (tc_assume env lid fml [] dr)
in (FStar_List.append l ((se)::[])))
end)) [] axioms)
in (

let _59_1295 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq")
in ses)))
end)))
end))))))
end)))))
in (

let unoptimized_haseq_scheme = (fun _59_1298 -> (

let mutuals = (FStar_List.map (fun ty -> (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _59_1303, _59_1305, _59_1307, _59_1309, _59_1311, _59_1313, _59_1315) -> begin
lid
end
| _59_1319 -> begin
(FStar_All.failwith "Impossible!")
end)) tcs)
in (

let haseq_ty = (fun usubst us acc ty -> (

let _59_1346 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _59_1328, bs, t, _59_1332, d_lids, _59_1335, _59_1337) -> begin
((lid), (bs), (t), (d_lids))
end
| _59_1341 -> begin
(FStar_All.failwith "Impossible!")
end)
in (match (_59_1346) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _154_686 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _154_686 t))
in (

let _59_1351 = (FStar_Syntax_Subst.open_term bs t)
in (match (_59_1351) with
| (bs, t) -> begin
(

let ibs = (match ((let _154_687 = (FStar_Syntax_Subst.compress t)
in _154_687.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _59_1354) -> begin
ibs
end
| _59_1358 -> begin
[]
end)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _154_690 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _154_689 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _154_690 _154_689)))
in (

let ind = (let _154_693 = (FStar_List.map (fun _59_1365 -> (match (_59_1365) with
| (bv, aq) -> begin
(let _154_692 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_154_692), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _154_693 None dr))
in (

let ind = (let _154_696 = (FStar_List.map (fun _59_1369 -> (match (_59_1369) with
| (bv, aq) -> begin
(let _154_695 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_154_695), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _154_696 None dr))
in (

let haseq_ind = (let _154_698 = (let _154_697 = (FStar_Syntax_Syntax.as_arg ind)
in (_154_697)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _154_698 None dr))
in (

let rec is_mutual = (fun t -> (match ((let _154_702 = (FStar_Syntax_Subst.compress t)
in _154_702.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.existsb (fun lid -> (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) mutuals)
end
| FStar_Syntax_Syntax.Tm_uinst (t', _59_1380) -> begin
(is_mutual t')
end
| FStar_Syntax_Syntax.Tm_refine (bv, t') -> begin
(is_mutual bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_app (t', args) -> begin
if (is_mutual t') then begin
true
end else begin
(let _154_704 = (FStar_List.map Prims.fst args)
in (exists_mutual _154_704))
end
end
| FStar_Syntax_Syntax.Tm_meta (t', _59_1393) -> begin
(is_mutual t')
end
| _59_1397 -> begin
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
in (match ((let _154_710 = (FStar_Syntax_Subst.compress dt)
in _154_710.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _59_1410) -> begin
(

let dbs = (let _154_711 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _154_711))
in (

let dbs = (let _154_712 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _154_712 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let sort = (Prims.fst b).FStar_Syntax_Syntax.sort
in (

let haseq_sort = (let _154_716 = (let _154_715 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_154_715)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _154_716 None dr))
in (

let haseq_sort = if (is_mutual sort) then begin
(FStar_Syntax_Util.mk_imp haseq_ind haseq_sort)
end else begin
haseq_sort
end
in (FStar_Syntax_Util.mk_conj t haseq_sort))))) FStar_Syntax_Util.t_true dbs)
in (

let cond = (FStar_List.fold_right (fun b t -> (let _154_722 = (let _154_721 = (let _154_720 = (let _154_719 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _154_719 None))
in (FStar_Syntax_Syntax.as_arg _154_720))
in (_154_721)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _154_722 None dr))) dbs cond)
in (FStar_Syntax_Util.mk_conj acc cond))))))
end
| _59_1426 -> begin
acc
end))))
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (_59_1429, _59_1431, _59_1433, t_lid, _59_1436, _59_1438, _59_1440, _59_1442) -> begin
(t_lid = lid)
end
| _59_1446 -> begin
(FStar_All.failwith "Impossible")
end)) datas)
in (

let data_cond = (FStar_List.fold_left haseq_data FStar_Syntax_Util.t_true t_datas)
in (

let fml = (FStar_Syntax_Util.mk_imp data_cond haseq_ind)
in (

let fml = (

let _59_1450 = fml
in (let _154_729 = (let _154_728 = (let _154_727 = (let _154_726 = (let _154_725 = (let _154_724 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_154_724)::[])
in (_154_725)::[])
in FStar_Syntax_Syntax.Meta_pattern (_154_726))
in ((fml), (_154_727)))
in FStar_Syntax_Syntax.Tm_meta (_154_728))
in {FStar_Syntax_Syntax.n = _154_729; FStar_Syntax_Syntax.tk = _59_1450.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _59_1450.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _59_1450.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _154_735 = (let _154_734 = (let _154_733 = (let _154_732 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _154_732 None))
in (FStar_Syntax_Syntax.as_arg _154_733))
in (_154_734)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _154_735 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _154_741 = (let _154_740 = (let _154_739 = (let _154_738 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _154_738 None))
in (FStar_Syntax_Syntax.as_arg _154_739))
in (_154_740)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _154_741 None dr))) bs fml)
in (FStar_Syntax_Util.mk_conj acc fml)))))))))))))))
end))))
end)))
in (

let _59_1480 = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, _59_1463, _59_1465, _59_1467, _59_1469, _59_1471, _59_1473) -> begin
((lid), (us))
end
| _59_1477 -> begin
(FStar_All.failwith "Impossible!")
end))
in (match (_59_1480) with
| (lid, us) -> begin
(

let _59_1483 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (_59_1483) with
| (usubst, us) -> begin
(

let fml = (FStar_List.fold_left (haseq_ty usubst us) FStar_Syntax_Util.t_true tcs)
in (

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (

let _59_1486 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq")
in (

let _59_1488 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle)
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let se = (let _154_742 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (tc_assume env _154_742 fml [] dr))
in (

let _59_1492 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq")
in (se)::[])))))))
end))
end)))))
in (

let skip_prims_type = (fun _59_1495 -> (

let lid = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _59_1500, _59_1502, _59_1504, _59_1506, _59_1508, _59_1510, _59_1512) -> begin
lid
end
| _59_1516 -> begin
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
in (let _154_750 = (let _154_749 = (let _154_748 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_154_748)))
in FStar_Syntax_Syntax.Sig_bundle (_154_749))
in (_154_750)::ses)))
end)))))))
end))
end))
end))))
end)))))))))
and tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env se -> (

let env = (set_hint_correlator env se)
in (

let _59_1528 = (FStar_TypeChecker_Util.check_sigelt_quals env se)
in (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let se = (tc_lex_t env ses quals lids)
in (let _154_753 = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (_154_753)))))
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

let _59_1568 = (set_options FStar_Options.Set o)
in (((se)::[]), (env)))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(

let _59_1572 = (let _154_760 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _154_760 Prims.ignore))
in (

let _59_1577 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (

let _59_1579 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (((se)::[]), (env)))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_59_1582) -> begin
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

let _59_1598 = (FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun _59_1593 a -> (match (_59_1593) with
| (env, ses) -> begin
(

let se_let = (FStar_Syntax_Util.action_as_lb a)
in (let _154_763 = (FStar_TypeChecker_Env.push_sigelt env se_let)
in ((_154_763), ((se_let)::ses))))
end)) ((env), ((se)::[]))))
in (match (_59_1598) with
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

let _59_1607 = (let _154_764 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _154_764))
in (match (_59_1607) with
| (a, wp_a_src) -> begin
(

let _59_1610 = (let _154_765 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _154_765))
in (match (_59_1610) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (let _154_769 = (let _154_768 = (let _154_767 = (let _154_766 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (_154_766)))
in FStar_Syntax_Syntax.NT (_154_767))
in (_154_768)::[])
in (FStar_Syntax_Subst.subst _154_769 wp_b_tgt))
in (

let expected_k = (let _154_774 = (let _154_772 = (FStar_Syntax_Syntax.mk_binder a)
in (let _154_771 = (let _154_770 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_154_770)::[])
in (_154_772)::_154_771))
in (let _154_773 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _154_774 _154_773)))
in (

let repr_type = (fun eff_name a wp -> (

let no_reify = (fun l -> (let _154_786 = (let _154_785 = (let _154_784 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _154_783 = (FStar_TypeChecker_Env.get_range env)
in ((_154_784), (_154_783))))
in FStar_Syntax_Syntax.Error (_154_785))
in (Prims.raise _154_786)))
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
(let _154_793 = (let _154_791 = (let _154_790 = (let _154_789 = (FStar_Syntax_Syntax.as_arg a)
in (let _154_788 = (let _154_787 = (FStar_Syntax_Syntax.as_arg wp)
in (_154_787)::[])
in (_154_789)::_154_788))
in ((repr), (_154_790)))
in FStar_Syntax_Syntax.Tm_app (_154_791))
in (let _154_792 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _154_793 None _154_792)))
end)
end)))
in (

let _59_1651 = (match (((sub.FStar_Syntax_Syntax.lift), (sub.FStar_Syntax_Syntax.lift_wp))) with
| (None, None) -> begin
(FStar_All.failwith "Impossible")
end
| (lift, Some (_59_1628, lift_wp)) -> begin
(let _154_794 = (check_and_gen env lift_wp expected_k)
in ((lift), (_154_794)))
end
| (Some (what, lift), None) -> begin
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange))
in (

let _59_1644 = (FStar_TypeChecker_DMFF.star_expr dmff_env lift)
in (match (_59_1644) with
| (_59_1641, lift_wp, lift_elab) -> begin
(

let _59_1645 = (recheck_debug "lift-wp" env lift_wp)
in (

let _59_1647 = (recheck_debug "lift-elab" env lift_elab)
in ((Some ((([]), (lift_elab)))), ((([]), (lift_wp))))))
end)))
end)
in (match (_59_1651) with
| (lift, lift_wp) -> begin
(

let lax = env.FStar_TypeChecker_Env.lax
in (

let env = (

let _59_1653 = env
in {FStar_TypeChecker_Env.solver = _59_1653.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_1653.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_1653.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_1653.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_1653.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_1653.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_1653.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_1653.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_1653.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_1653.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_1653.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_1653.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_1653.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_1653.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_1653.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_1653.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_1653.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_1653.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _59_1653.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_1653.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_1653.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_1653.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_1653.FStar_TypeChecker_Env.qname_and_index})
in (

let lift = (match (lift) with
| None -> begin
None
end
| Some (_59_1658, lift) -> begin
(

let _59_1664 = (let _154_795 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _154_795))
in (match (_59_1664) with
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

let lift_wp_a = (let _154_802 = (let _154_800 = (let _154_799 = (let _154_798 = (FStar_Syntax_Syntax.as_arg a_typ)
in (let _154_797 = (let _154_796 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (_154_796)::[])
in (_154_798)::_154_797))
in ((lift_wp), (_154_799)))
in FStar_Syntax_Syntax.Tm_app (_154_800))
in (let _154_801 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _154_802 None _154_801)))
in (repr_type sub.FStar_Syntax_Syntax.target a_typ lift_wp_a)))
in (

let expected_k = (let _154_809 = (let _154_807 = (FStar_Syntax_Syntax.mk_binder a)
in (let _154_806 = (let _154_805 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (let _154_804 = (let _154_803 = (FStar_Syntax_Syntax.null_binder repr_f)
in (_154_803)::[])
in (_154_805)::_154_804))
in (_154_807)::_154_806))
in (let _154_808 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow _154_809 _154_808)))
in (

let _59_1678 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (_59_1678) with
| (expected_k, _59_1675, _59_1677) -> begin
(

let lift = (check_and_gen env lift expected_k)
in Some (lift))
end))))))))
end))
end)
in (

let env = (

let _59_1681 = env
in {FStar_TypeChecker_Env.solver = _59_1681.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_1681.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_1681.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_1681.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_1681.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_1681.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_1681.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_1681.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_1681.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_1681.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_1681.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_1681.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_1681.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_1681.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_1681.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_1681.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_1681.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_1681.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = lax; FStar_TypeChecker_Env.lax_universes = _59_1681.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_1681.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_1681.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_1681.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_1681.FStar_TypeChecker_Env.qname_and_index})
in (

let sub = (

let _59_1684 = sub
in {FStar_Syntax_Syntax.source = _59_1684.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _59_1684.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = Some (lift_wp); FStar_Syntax_Syntax.lift = lift})
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

let _59_1697 = ()
in (

let env0 = env
in (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _59_1703 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_59_1703) with
| (tps, c) -> begin
(

let _59_1707 = (tc_tparams env tps)
in (match (_59_1707) with
| (tps, env, us) -> begin
(

let _59_1711 = (FStar_TypeChecker_TcTerm.tc_comp env c)
in (match (_59_1711) with
| (c, u, g) -> begin
(

let _59_1712 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

let _59_1718 = (let _154_810 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _154_810))
in (match (_59_1718) with
| (uvs, t) -> begin
(

let _59_1737 = (match ((let _154_812 = (let _154_811 = (FStar_Syntax_Subst.compress t)
in _154_811.FStar_Syntax_Syntax.n)
in ((tps), (_154_812)))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_59_1721, c)) -> begin
(([]), (c))
end
| (_59_1727, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
((tps), (c))
end
| _59_1734 -> begin
(FStar_All.failwith "Impossible")
end)
in (match (_59_1737) with
| (tps, c) -> begin
(

let _59_1742 = if (((FStar_List.length uvs) <> (Prims.parse_int "1")) && (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid)))) then begin
(

let _59_1741 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_59_1741) with
| (_59_1739, t) -> begin
(let _154_818 = (let _154_817 = (let _154_816 = (let _154_815 = (FStar_Syntax_Print.lid_to_string lid)
in (let _154_814 = (FStar_All.pipe_right (FStar_List.length uvs) FStar_Util.string_of_int)
in (let _154_813 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)" _154_815 _154_814 _154_813))))
in ((_154_816), (r)))
in FStar_Syntax_Syntax.Error (_154_817))
in (Prims.raise _154_818))
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

let _59_1754 = ()
in (

let _59_1758 = (let _154_820 = (let _154_819 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _154_819))
in (check_and_gen env t _154_820))
in (match (_59_1758) with
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

let _59_1778 = (FStar_TypeChecker_TcTerm.tc_term env e)
in (match (_59_1778) with
| (e, c, g1) -> begin
(

let _59_1783 = (let _154_824 = (let _154_821 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_154_821))
in (let _154_823 = (let _154_822 = (c.FStar_Syntax_Syntax.comp ())
in ((e), (_154_822)))
in (FStar_TypeChecker_TcTerm.check_expected_effect env _154_824 _154_823)))
in (match (_59_1783) with
| (e, _59_1781, g) -> begin
(

let _59_1784 = (let _154_825 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _154_825))
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
(let _154_837 = (let _154_836 = (let _154_835 = (let _154_834 = (FStar_Syntax_Print.lid_to_string l)
in (let _154_833 = (FStar_Syntax_Print.quals_to_string q)
in (let _154_832 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _154_834 _154_833 _154_832))))
in ((_154_835), (r)))
in FStar_Syntax_Syntax.Error (_154_836))
in (Prims.raise _154_837))
end
end))
in (

let _59_1828 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _59_1805 lb -> (match (_59_1805) with
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _59_1824 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
((gen), (lb), (quals_opt))
end
| Some ((uvs, tval), quals) -> begin
(

let quals_opt = (check_quals_eq lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v quals_opt quals)
in (

let _59_1819 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _59_1818 -> begin
(FStar_TypeChecker_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (let _154_840 = (FStar_Syntax_Syntax.mk_lb ((FStar_Util.Inr (lbname)), (uvs), (FStar_Syntax_Const.effect_ALL_lid), (tval), (lb.FStar_Syntax_Syntax.lbdef)))
in ((false), (_154_840), (quals_opt)))))
end)
in (match (_59_1824) with
| (gen, lb, quals_opt) -> begin
((gen), ((lb)::lbs), (quals_opt))
end)))
end)) ((true), ([]), (if (quals = []) then begin
None
end else begin
Some (quals)
end))))
in (match (_59_1828) with
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
| _59_1837 -> begin
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

let e = (let _154_844 = (let _154_843 = (let _154_842 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((((Prims.fst lbs)), (lbs'))), (_154_842)))
in FStar_Syntax_Syntax.Tm_let (_154_843))
in (FStar_Syntax_Syntax.mk _154_844 None r))
in (

let _59_1871 = (match ((FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term (

let _59_1841 = env
in {FStar_TypeChecker_Env.solver = _59_1841.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_1841.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_1841.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_1841.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_1841.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_1841.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_1841.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_1841.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_1841.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_1841.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_1841.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _59_1841.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _59_1841.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_1841.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_1841.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_1841.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_1841.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _59_1841.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_1841.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_1841.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_1841.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_1841.FStar_TypeChecker_Env.qname_and_index}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _59_1848; FStar_Syntax_Syntax.pos = _59_1846; FStar_Syntax_Syntax.vars = _59_1844}, _59_1855, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_59_1859, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _59_1865 -> begin
quals
end)
in ((FStar_Syntax_Syntax.Sig_let (((lbs), (r), (lids), (quals)))), (lbs)))
end
| _59_1868 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_59_1871) with
| (se, lbs) -> begin
(

let _59_1877 = if (log env) then begin
(let _154_852 = (let _154_851 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (match ((let _154_848 = (let _154_847 = (let _154_846 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _154_846.FStar_Syntax_Syntax.fv_name)
in _154_847.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _154_848))) with
| None -> begin
true
end
| _59_1875 -> begin
false
end)
in if should_log then begin
(let _154_850 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _154_849 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _154_850 _154_849)))
end else begin
""
end))))
in (FStar_All.pipe_right _154_851 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _154_852))
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
| _59_1887 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _59_1897 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_59_1899) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _59_1910, r) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _59_1917 -> (match (_59_1917) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _59_1923, _59_1925, quals, r) -> begin
(

let dec = (let _154_866 = (let _154_865 = (let _154_864 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow bs _154_864))
in ((l), (us), (_154_865), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (_154_866))
in (((dec)::out), (hidden)))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _59_1935, _59_1937, _59_1939, _59_1941, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]), (r)))
in (((dec)::out), ((l)::hidden)))
end
| _59_1947 -> begin
((out), (hidden))
end)
end)) ses (([]), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end
| FStar_Syntax_Syntax.Sig_assume (_59_1949, _59_1951, quals, _59_1954) -> begin
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
| _59_1973 -> begin
false
end)))) then begin
(((se)::[]), (hidden))
end else begin
(([]), (hidden))
end
end
end
| FStar_Syntax_Syntax.Sig_main (_59_1975) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _59_1994, _59_1996, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
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
(let _154_873 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _154_872 = (let _154_871 = (let _154_870 = (let _154_869 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _154_869.FStar_Syntax_Syntax.fv_name)
in _154_870.FStar_Syntax_Syntax.v)
in ((_154_871), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (_154_872)))))
in ((_154_873), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let process_one_decl = (fun _59_2017 se -> (match (_59_2017) with
| (ses, exports, env, hidden) -> begin
(

let _59_2019 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _154_882 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _154_882))
end else begin
()
end
in (

let _59_2023 = (tc_decl env se)
in (match (_59_2023) with
| (ses', env) -> begin
(

let _59_2026 = if ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _154_887 = (FStar_List.fold_left (fun s se -> (let _154_886 = (let _154_885 = (FStar_Syntax_Print.sigelt_to_string se)
in (Prims.strcat _154_885 "\n"))
in (Prims.strcat s _154_886))) "" ses')
in (FStar_Util.print1 "Checked: %s\n" _154_887))
end else begin
()
end
in (

let _59_2029 = (FStar_List.iter (fun se -> (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)) ses')
in (

let _59_2038 = (FStar_List.fold_left (fun _59_2033 se -> (match (_59_2033) with
| (le, lh) -> begin
(

let tup = (for_export hidden se)
in (((FStar_List.rev_append (Prims.fst tup) le)), ((FStar_List.rev_append (Prims.snd tup) lh))))
end)) (([]), ([])) ses')
in (match (_59_2038) with
| (exported, hidden) -> begin
(((FStar_List.rev_append ses' ses)), (((FStar_List.rev_append exported []))::exports), (env), (hidden))
end))))
end)))
end))
in (

let _59_2068 = (FStar_List.fold_left (fun acc se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, r) -> begin
(

let _59_2052 = acc
in (match (_59_2052) with
| (_59_2046, _59_2048, env, _59_2051) -> begin
(

let _59_2056 = (cps_and_elaborate env ne)
in (match (_59_2056) with
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
| _59_2062 -> begin
(process_one_decl acc se)
end)) (([]), ([]), (env), ([])) ses)
in (match (_59_2068) with
| (ses, exports, env, _59_2067) -> begin
(let _154_893 = (FStar_All.pipe_right (FStar_List.rev_append exports []) FStar_List.flatten)
in (((FStar_List.rev_append ses [])), (_154_893), (env)))
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

let _59_2073 = env
in (let _154_898 = (not ((FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _59_2073.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_2073.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_2073.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_2073.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_2073.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_2073.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_2073.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_2073.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_2073.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_2073.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_2073.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_2073.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_2073.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_2073.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_2073.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_2073.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = _154_898; FStar_TypeChecker_Env.lax = _59_2073.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _59_2073.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_2073.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_2073.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_2073.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_2073.FStar_TypeChecker_Env.qname_and_index}))
in (

let _59_2076 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
in (

let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

let _59_2082 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_59_2082) with
| (ses, exports, env) -> begin
(((

let _59_2083 = modul
in {FStar_Syntax_Syntax.name = _59_2083.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _59_2083.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _59_2083.FStar_Syntax_Syntax.is_interface})), (exports), (env))
end))))))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let _59_2091 = (tc_decls env decls)
in (match (_59_2091) with
| (ses, exports, env) -> begin
(

let modul = (

let _59_2092 = modul
in {FStar_Syntax_Syntax.name = _59_2092.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _59_2092.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _59_2092.FStar_Syntax_Syntax.is_interface})
in ((modul), (exports), (env)))
end)))


let check_exports : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env modul exports -> (

let env = (

let _59_2098 = env
in {FStar_TypeChecker_Env.solver = _59_2098.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_2098.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_2098.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_2098.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_2098.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_2098.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_2098.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_2098.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_2098.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_2098.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_2098.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_2098.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_2098.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _59_2098.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_2098.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_2098.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_2098.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = true; FStar_TypeChecker_Env.type_of = _59_2098.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_2098.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_2098.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_2098.FStar_TypeChecker_Env.qname_and_index})
in (

let check_term = (fun lid univs t -> (

let _59_2107 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_59_2107) with
| (univs, t) -> begin
(

let _59_2109 = if (let _154_918 = (let _154_917 = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (FStar_TypeChecker_Env.debug _154_917))
in (FStar_All.pipe_left _154_918 (FStar_Options.Other ("Exports")))) then begin
(let _154_923 = (FStar_Syntax_Print.lid_to_string lid)
in (let _154_922 = (let _154_920 = (FStar_All.pipe_right univs (FStar_List.map (fun x -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (x))))))
in (FStar_All.pipe_right _154_920 (FStar_String.concat ", ")))
in (let _154_921 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print3 "Checking for export %s <%s> : %s\n" _154_923 _154_922 _154_921))))
end else begin
()
end
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env univs)
in (let _154_924 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env t)
in (FStar_All.pipe_right _154_924 Prims.ignore))))
end)))
in (

let check_term = (fun lid univs t -> (

let _59_2116 = (let _154_933 = (let _154_932 = (FStar_Syntax_Print.lid_to_string modul.FStar_Syntax_Syntax.name)
in (let _154_931 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Interface of %s violates its abstraction (add a \'private\' qualifier to \'%s\'?)" _154_932 _154_931)))
in (FStar_TypeChecker_Errors.message_prefix.FStar_TypeChecker_Errors.set_prefix _154_933))
in (

let _59_2118 = (check_term lid univs t)
in (FStar_TypeChecker_Errors.message_prefix.FStar_TypeChecker_Errors.clear_prefix ()))))
in (

let rec check_sigelt = (fun _59_11 -> (match (_59_11) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _59_2125, _59_2127) -> begin
if (not ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private)))) then begin
(FStar_All.pipe_right ses (FStar_List.iter check_sigelt))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_inductive_typ (l, univs, binders, typ, _59_2135, _59_2137, _59_2139, r) -> begin
(

let t = (let _154_938 = (let _154_937 = (let _154_936 = (FStar_Syntax_Syntax.mk_Total typ)
in ((binders), (_154_936)))
in FStar_Syntax_Syntax.Tm_arrow (_154_937))
in (FStar_Syntax_Syntax.mk _154_938 None r))
in (check_term l univs t))
end
| FStar_Syntax_Syntax.Sig_datacon (l, univs, t, _59_2148, _59_2150, _59_2152, _59_2154, _59_2156) -> begin
(check_term l univs t)
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, univs, t, quals, _59_2164) -> begin
if (not ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private)))) then begin
(check_term l univs t)
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_let ((_59_2168, lbs), _59_2172, _59_2174, quals) -> begin
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

let _59_2210 = modul
in {FStar_Syntax_Syntax.name = _59_2210.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _59_2210.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module env modul)
in (

let _59_2214 = (check_exports env modul exports)
in (

let _59_2216 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (

let _59_2218 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (

let _59_2220 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (

let _59_2222 = (let _154_946 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _154_946 Prims.ignore))
in ((modul), (env))))))))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let _59_2229 = (tc_partial_modul env modul)
in (match (_59_2229) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (

let _59_2232 = if (FStar_Options.debug_any ()) then begin
(let _154_955 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _154_955))
end else begin
()
end
in (

let _59_2236 = (tc_modul env m)
in (match (_59_2236) with
| (m, env) -> begin
(

let _59_2237 = if (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _154_956 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _154_956))
end else begin
()
end
in ((m), (env)))
end))))




