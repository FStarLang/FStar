
open Prims

let set_hint_correlator : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_TypeChecker_Env.env = (fun env se -> (match ((FStar_Options.reuse_hint_for ())) with
| Some (l) -> begin
(

let lid = (let _163_5 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_add_suffix _163_5 l))
in (

let _62_19 = env
in {FStar_TypeChecker_Env.solver = _62_19.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _62_19.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _62_19.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _62_19.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _62_19.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _62_19.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _62_19.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _62_19.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _62_19.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _62_19.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _62_19.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _62_19.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _62_19.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _62_19.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _62_19.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _62_19.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _62_19.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _62_19.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _62_19.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _62_19.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _62_19.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _62_19.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _62_19.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), ((Prims.parse_int "0"))))}))
end
| None -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in (

let lid = (match (lids) with
| [] -> begin
(let _163_8 = (FStar_TypeChecker_Env.current_module env)
in (let _163_7 = (let _163_6 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_right _163_6 FStar_Util.string_of_int))
in (FStar_Ident.lid_add_suffix _163_8 _163_7)))
end
| (l)::_62_25 -> begin
l
end)
in (

let _62_29 = env
in {FStar_TypeChecker_Env.solver = _62_29.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _62_29.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _62_29.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _62_29.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _62_29.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _62_29.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _62_29.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _62_29.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _62_29.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _62_29.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _62_29.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _62_29.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _62_29.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _62_29.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _62_29.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _62_29.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _62_29.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _62_29.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _62_29.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _62_29.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _62_29.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _62_29.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _62_29.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = Some (((lid), ((Prims.parse_int "0"))))})))
end))


let log : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> ((FStar_Options.log_types ()) && (not ((let _163_11 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _163_11))))))


let tc_check_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env t k -> (

let _62_38 = (FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k)
in (match (_62_38) with
| (t, c, g) -> begin
(

let _62_39 = (FStar_ST.op_Colon_Equals t.FStar_Syntax_Syntax.tk (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)))
in (

let _62_41 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in t))
end)))


let recheck_debug : Prims.string  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s env t -> (

let _62_46 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _163_24 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Term has been %s-transformed to:\n%s\n----------\n" s _163_24))
end else begin
()
end
in (

let _62_53 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (_62_53) with
| (t', _62_50, _62_52) -> begin
(

let _62_54 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _163_25 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print1 "Re-checked; got:\n%s\n----------\n" _163_25))
end else begin
()
end
in t)
end))))


let check_and_gen : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.tscheme = (fun env t k -> (let _163_32 = (tc_check_trivial_guard env t k)
in (FStar_TypeChecker_Util.generalize_universes env _163_32)))


let check_nogen = (fun env t k -> (

let t = (tc_check_trivial_guard env t k)
in (let _163_36 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (([]), (_163_36)))))


let tc_tparams : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.universes) = (fun env tps -> (

let _62_69 = (FStar_TypeChecker_TcTerm.tc_binders env tps)
in (match (_62_69) with
| (tps, env, g, us) -> begin
(

let _62_70 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in ((tps), (env), (us)))
end)))


let monad_signature : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m s -> (

let fail = (fun _62_76 -> (match (()) with
| () -> begin
(let _163_51 = (let _163_50 = (let _163_49 = (FStar_TypeChecker_Err.unexpected_signature_for_monad env m s)
in ((_163_49), ((FStar_Ident.range_of_lid m))))
in FStar_Errors.Error (_163_50))
in (Prims.raise _163_51))
end))
in (

let s = (FStar_Syntax_Subst.compress s)
in (match (s.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _62_89))::((wp, _62_85))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _62_93 -> begin
(fail ())
end))
end
| _62_95 -> begin
(fail ())
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let _62_102 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_62_102) with
| (uvs, c) -> begin
((uvs), ([]), (c))
end))
end
| _62_104 -> begin
(

let t' = (FStar_Syntax_Util.arrow binders c)
in (

let _62_108 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_62_108) with
| (uvs, t') -> begin
(match ((let _163_58 = (FStar_Syntax_Subst.compress t')
in _163_58.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
((uvs), (binders), (c))
end
| _62_114 -> begin
(failwith "Impossible")
end)
end)))
end))


let rec tc_eff_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.eff_decl = (fun env0 ed -> (

let _62_117 = ()
in (

let _62_122 = (FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_62_122) with
| (effect_params_un, signature_un, opening) -> begin
(

let _62_127 = (tc_tparams env0 effect_params_un)
in (match (_62_127) with
| (effect_params, env, _62_126) -> begin
(

let _62_131 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (_62_131) with
| (signature, _62_130) -> begin
(

let ed = (

let _62_132 = ed
in {FStar_Syntax_Syntax.qualifiers = _62_132.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = _62_132.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = _62_132.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _62_132.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _62_132.FStar_Syntax_Syntax.ret_wp; FStar_Syntax_Syntax.bind_wp = _62_132.FStar_Syntax_Syntax.bind_wp; FStar_Syntax_Syntax.if_then_else = _62_132.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _62_132.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _62_132.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _62_132.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _62_132.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _62_132.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _62_132.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _62_132.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _62_132.FStar_Syntax_Syntax.repr; FStar_Syntax_Syntax.return_repr = _62_132.FStar_Syntax_Syntax.return_repr; FStar_Syntax_Syntax.bind_repr = _62_132.FStar_Syntax_Syntax.bind_repr; FStar_Syntax_Syntax.actions = _62_132.FStar_Syntax_Syntax.actions})
in (

let ed = (match (effect_params) with
| [] -> begin
ed
end
| _62_137 -> begin
(

let op = (fun ts -> (

let _62_140 = ()
in (

let t1 = (FStar_Syntax_Subst.subst opening (Prims.snd ts))
in (([]), (t1)))))
in (

let _62_143 = ed
in (let _163_101 = (op ed.FStar_Syntax_Syntax.ret_wp)
in (let _163_100 = (op ed.FStar_Syntax_Syntax.bind_wp)
in (let _163_99 = (op ed.FStar_Syntax_Syntax.if_then_else)
in (let _163_98 = (op ed.FStar_Syntax_Syntax.ite_wp)
in (let _163_97 = (op ed.FStar_Syntax_Syntax.stronger)
in (let _163_96 = (op ed.FStar_Syntax_Syntax.close_wp)
in (let _163_95 = (op ed.FStar_Syntax_Syntax.assert_p)
in (let _163_94 = (op ed.FStar_Syntax_Syntax.assume_p)
in (let _163_93 = (op ed.FStar_Syntax_Syntax.null_wp)
in (let _163_92 = (op ed.FStar_Syntax_Syntax.trivial)
in (let _163_91 = (let _163_82 = (op (([]), (ed.FStar_Syntax_Syntax.repr)))
in (Prims.snd _163_82))
in (let _163_90 = (op ed.FStar_Syntax_Syntax.return_repr)
in (let _163_89 = (op ed.FStar_Syntax_Syntax.bind_repr)
in (let _163_88 = (FStar_List.map (fun a -> (

let _62_146 = a
in (let _163_87 = (let _163_84 = (op (([]), (a.FStar_Syntax_Syntax.action_defn)))
in (Prims.snd _163_84))
in (let _163_86 = (let _163_85 = (op (([]), (a.FStar_Syntax_Syntax.action_typ)))
in (Prims.snd _163_85))
in {FStar_Syntax_Syntax.action_name = _62_146.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = _62_146.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = _62_146.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _163_87; FStar_Syntax_Syntax.action_typ = _163_86})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.qualifiers = _62_143.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = _62_143.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = _62_143.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _62_143.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _62_143.FStar_Syntax_Syntax.binders; FStar_Syntax_Syntax.signature = _62_143.FStar_Syntax_Syntax.signature; FStar_Syntax_Syntax.ret_wp = _163_101; FStar_Syntax_Syntax.bind_wp = _163_100; FStar_Syntax_Syntax.if_then_else = _163_99; FStar_Syntax_Syntax.ite_wp = _163_98; FStar_Syntax_Syntax.stronger = _163_97; FStar_Syntax_Syntax.close_wp = _163_96; FStar_Syntax_Syntax.assert_p = _163_95; FStar_Syntax_Syntax.assume_p = _163_94; FStar_Syntax_Syntax.null_wp = _163_93; FStar_Syntax_Syntax.trivial = _163_92; FStar_Syntax_Syntax.repr = _163_91; FStar_Syntax_Syntax.return_repr = _163_90; FStar_Syntax_Syntax.bind_repr = _163_89; FStar_Syntax_Syntax.actions = _163_88}))))))))))))))))
end)
in (

let wp_with_fresh_result_type = (fun env mname signature -> (

let fail = (fun t -> (let _163_112 = (let _163_111 = (let _163_110 = (FStar_TypeChecker_Err.unexpected_signature_for_monad env mname t)
in ((_163_110), ((FStar_Ident.range_of_lid mname))))
in FStar_Errors.Error (_163_111))
in (Prims.raise _163_112)))
in (match ((let _163_113 = (FStar_Syntax_Subst.compress signature)
in _163_113.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let bs = (FStar_Syntax_Subst.open_binders bs)
in (match (bs) with
| ((a, _62_166))::((wp, _62_162))::[] -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| _62_170 -> begin
(fail signature)
end))
end
| _62_172 -> begin
(fail signature)
end)))
in (

let _62_175 = (wp_with_fresh_result_type env ed.FStar_Syntax_Syntax.mname ed.FStar_Syntax_Syntax.signature)
in (match (_62_175) with
| (a, wp_a) -> begin
(

let fresh_effect_signature = (fun _62_177 -> (match (()) with
| () -> begin
(

let _62_181 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (_62_181) with
| (signature, _62_180) -> begin
(wp_with_fresh_result_type env ed.FStar_Syntax_Syntax.mname signature)
end))
end))
in (

let env = (let _163_116 = (FStar_Syntax_Syntax.new_bv None ed.FStar_Syntax_Syntax.signature)
in (FStar_TypeChecker_Env.push_bv env _163_116))
in (

let _62_183 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0) (FStar_Options.Other ("ED"))) then begin
(let _163_122 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (let _163_121 = (FStar_Syntax_Print.binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (let _163_120 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.signature)
in (let _163_119 = (let _163_117 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Print.term_to_string _163_117))
in (let _163_118 = (FStar_Syntax_Print.term_to_string a.FStar_Syntax_Syntax.sort)
in (FStar_Util.print5 "Checking effect signature: %s %s : %s\n(a is %s:%s)\n" _163_122 _163_121 _163_120 _163_119 _163_118))))))
end else begin
()
end
in (

let check_and_gen' = (fun env _62_190 k -> (match (_62_190) with
| (_62_188, t) -> begin
(check_and_gen env t k)
end))
in (

let return_wp = (

let expected_k = (let _163_134 = (let _163_132 = (FStar_Syntax_Syntax.mk_binder a)
in (let _163_131 = (let _163_130 = (let _163_129 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _163_129))
in (_163_130)::[])
in (_163_132)::_163_131))
in (let _163_133 = (FStar_Syntax_Syntax.mk_GTotal wp_a)
in (FStar_Syntax_Util.arrow _163_134 _163_133)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ret_wp expected_k))
in (

let bind_wp = (

let _62_196 = (fresh_effect_signature ())
in (match (_62_196) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _163_138 = (let _163_136 = (let _163_135 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _163_135))
in (_163_136)::[])
in (let _163_137 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _163_138 _163_137)))
in (

let expected_k = (let _163_149 = (let _163_147 = (FStar_Syntax_Syntax.null_binder FStar_TypeChecker_Common.t_range)
in (let _163_146 = (let _163_145 = (FStar_Syntax_Syntax.mk_binder a)
in (let _163_144 = (let _163_143 = (FStar_Syntax_Syntax.mk_binder b)
in (let _163_142 = (let _163_141 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _163_140 = (let _163_139 = (FStar_Syntax_Syntax.null_binder a_wp_b)
in (_163_139)::[])
in (_163_141)::_163_140))
in (_163_143)::_163_142))
in (_163_145)::_163_144))
in (_163_147)::_163_146))
in (let _163_148 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _163_149 _163_148)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.bind_wp expected_k)))
end))
in (

let if_then_else = (

let p = (let _163_151 = (let _163_150 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _163_150 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _163_151))
in (

let expected_k = (let _163_160 = (let _163_158 = (FStar_Syntax_Syntax.mk_binder a)
in (let _163_157 = (let _163_156 = (FStar_Syntax_Syntax.mk_binder p)
in (let _163_155 = (let _163_154 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _163_153 = (let _163_152 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_163_152)::[])
in (_163_154)::_163_153))
in (_163_156)::_163_155))
in (_163_158)::_163_157))
in (let _163_159 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _163_160 _163_159)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.if_then_else expected_k)))
in (

let ite_wp = (

let expected_k = (let _163_165 = (let _163_163 = (FStar_Syntax_Syntax.mk_binder a)
in (let _163_162 = (let _163_161 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_163_161)::[])
in (_163_163)::_163_162))
in (let _163_164 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _163_165 _163_164)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.ite_wp expected_k))
in (

let stronger = (

let _62_208 = (FStar_Syntax_Util.type_u ())
in (match (_62_208) with
| (t, _62_207) -> begin
(

let expected_k = (let _163_172 = (let _163_170 = (FStar_Syntax_Syntax.mk_binder a)
in (let _163_169 = (let _163_168 = (FStar_Syntax_Syntax.null_binder wp_a)
in (let _163_167 = (let _163_166 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_163_166)::[])
in (_163_168)::_163_167))
in (_163_170)::_163_169))
in (let _163_171 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow _163_172 _163_171)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.stronger expected_k))
end))
in (

let close_wp = (

let b = (let _163_174 = (let _163_173 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _163_173 Prims.fst))
in (FStar_Syntax_Syntax.new_bv (Some ((FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname))) _163_174))
in (

let b_wp_a = (let _163_178 = (let _163_176 = (let _163_175 = (FStar_Syntax_Syntax.bv_to_name b)
in (FStar_Syntax_Syntax.null_binder _163_175))
in (_163_176)::[])
in (let _163_177 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _163_178 _163_177)))
in (

let expected_k = (let _163_185 = (let _163_183 = (FStar_Syntax_Syntax.mk_binder a)
in (let _163_182 = (let _163_181 = (FStar_Syntax_Syntax.mk_binder b)
in (let _163_180 = (let _163_179 = (FStar_Syntax_Syntax.null_binder b_wp_a)
in (_163_179)::[])
in (_163_181)::_163_180))
in (_163_183)::_163_182))
in (let _163_184 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _163_185 _163_184)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.close_wp expected_k))))
in (

let assert_p = (

let expected_k = (let _163_194 = (let _163_192 = (FStar_Syntax_Syntax.mk_binder a)
in (let _163_191 = (let _163_190 = (let _163_187 = (let _163_186 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _163_186 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _163_187))
in (let _163_189 = (let _163_188 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_163_188)::[])
in (_163_190)::_163_189))
in (_163_192)::_163_191))
in (let _163_193 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _163_194 _163_193)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assert_p expected_k))
in (

let assume_p = (

let expected_k = (let _163_203 = (let _163_201 = (FStar_Syntax_Syntax.mk_binder a)
in (let _163_200 = (let _163_199 = (let _163_196 = (let _163_195 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _163_195 Prims.fst))
in (FStar_Syntax_Syntax.null_binder _163_196))
in (let _163_198 = (let _163_197 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_163_197)::[])
in (_163_199)::_163_198))
in (_163_201)::_163_200))
in (let _163_202 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _163_203 _163_202)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.assume_p expected_k))
in (

let null_wp = (

let expected_k = (let _163_206 = (let _163_204 = (FStar_Syntax_Syntax.mk_binder a)
in (_163_204)::[])
in (let _163_205 = (FStar_Syntax_Syntax.mk_Total wp_a)
in (FStar_Syntax_Util.arrow _163_206 _163_205)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.null_wp expected_k))
in (

let trivial_wp = (

let _62_224 = (FStar_Syntax_Util.type_u ())
in (match (_62_224) with
| (t, _62_223) -> begin
(

let expected_k = (let _163_211 = (let _163_209 = (FStar_Syntax_Syntax.mk_binder a)
in (let _163_208 = (let _163_207 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_163_207)::[])
in (_163_209)::_163_208))
in (let _163_210 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _163_211 _163_210)))
in (check_and_gen' env ed.FStar_Syntax_Syntax.trivial expected_k))
end))
in (

let _62_368 = (match ((let _163_212 = (FStar_Syntax_Subst.compress ed.FStar_Syntax_Syntax.repr)
in _163_212.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((ed.FStar_Syntax_Syntax.repr), (ed.FStar_Syntax_Syntax.bind_repr), (ed.FStar_Syntax_Syntax.return_repr), (ed.FStar_Syntax_Syntax.actions))
end
| _62_229 -> begin
(

let repr = (

let _62_233 = (FStar_Syntax_Util.type_u ())
in (match (_62_233) with
| (t, _62_232) -> begin
(

let expected_k = (let _163_217 = (let _163_215 = (FStar_Syntax_Syntax.mk_binder a)
in (let _163_214 = (let _163_213 = (FStar_Syntax_Syntax.null_binder wp_a)
in (_163_213)::[])
in (_163_215)::_163_214))
in (let _163_216 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.arrow _163_217 _163_216)))
in (tc_check_trivial_guard env ed.FStar_Syntax_Syntax.repr expected_k))
end))
in (

let mk_repr' = (fun t wp -> (

let repr = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env repr)
in (let _163_227 = (let _163_226 = (let _163_225 = (let _163_224 = (FStar_Syntax_Syntax.as_arg t)
in (let _163_223 = (let _163_222 = (FStar_Syntax_Syntax.as_arg wp)
in (_163_222)::[])
in (_163_224)::_163_223))
in ((repr), (_163_225)))
in FStar_Syntax_Syntax.Tm_app (_163_226))
in (FStar_Syntax_Syntax.mk _163_227 None FStar_Range.dummyRange))))
in (

let mk_repr = (fun a wp -> (let _163_232 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_repr' _163_232 wp)))
in (

let destruct_repr = (fun t -> (match ((let _163_235 = (FStar_Syntax_Subst.compress t)
in _163_235.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_62_246, ((t, _62_253))::((wp, _62_249))::[]) -> begin
((t), (wp))
end
| _62_259 -> begin
(failwith "Unexpected repr type")
end))
in (

let bind_repr = (

let r = (let _163_236 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_0 FStar_Syntax_Syntax.Delta_constant None)
in (FStar_All.pipe_right _163_236 FStar_Syntax_Syntax.fv_to_tm))
in (

let _62_263 = (fresh_effect_signature ())
in (match (_62_263) with
| (b, wp_b) -> begin
(

let a_wp_b = (let _163_240 = (let _163_238 = (let _163_237 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.null_binder _163_237))
in (_163_238)::[])
in (let _163_239 = (FStar_Syntax_Syntax.mk_Total wp_b)
in (FStar_Syntax_Util.arrow _163_240 _163_239)))
in (

let wp_f = (FStar_Syntax_Syntax.gen_bv "wp_f" None wp_a)
in (

let wp_g = (FStar_Syntax_Syntax.gen_bv "wp_g" None a_wp_b)
in (

let x_a = (let _163_241 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _163_241))
in (

let wp_g_x = (let _163_245 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (let _163_244 = (let _163_243 = (let _163_242 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _163_242))
in (_163_243)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _163_245 _163_244 None FStar_Range.dummyRange)))
in (

let res = (

let wp = (let _163_257 = (let _163_246 = (FStar_TypeChecker_Env.inst_tscheme bind_wp)
in (FStar_All.pipe_right _163_246 Prims.snd))
in (let _163_256 = (let _163_255 = (let _163_254 = (let _163_253 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _163_252 = (let _163_251 = (FStar_Syntax_Syntax.bv_to_name b)
in (let _163_250 = (let _163_249 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (let _163_248 = (let _163_247 = (FStar_Syntax_Syntax.bv_to_name wp_g)
in (_163_247)::[])
in (_163_249)::_163_248))
in (_163_251)::_163_250))
in (_163_253)::_163_252))
in (r)::_163_254)
in (FStar_List.map FStar_Syntax_Syntax.as_arg _163_255))
in (FStar_Syntax_Syntax.mk_Tm_app _163_257 _163_256 None FStar_Range.dummyRange)))
in (mk_repr b wp))
in (

let expected_k = (let _163_277 = (let _163_275 = (FStar_Syntax_Syntax.mk_binder a)
in (let _163_274 = (let _163_273 = (FStar_Syntax_Syntax.mk_binder b)
in (let _163_272 = (let _163_271 = (FStar_Syntax_Syntax.mk_binder wp_f)
in (let _163_270 = (let _163_269 = (let _163_259 = (let _163_258 = (FStar_Syntax_Syntax.bv_to_name wp_f)
in (mk_repr a _163_258))
in (FStar_Syntax_Syntax.null_binder _163_259))
in (let _163_268 = (let _163_267 = (FStar_Syntax_Syntax.mk_binder wp_g)
in (let _163_266 = (let _163_265 = (let _163_264 = (let _163_263 = (let _163_260 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_163_260)::[])
in (let _163_262 = (let _163_261 = (mk_repr b wp_g_x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _163_261))
in (FStar_Syntax_Util.arrow _163_263 _163_262)))
in (FStar_Syntax_Syntax.null_binder _163_264))
in (_163_265)::[])
in (_163_267)::_163_266))
in (_163_269)::_163_268))
in (_163_271)::_163_270))
in (_163_273)::_163_272))
in (_163_275)::_163_274))
in (let _163_276 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _163_277 _163_276)))
in (

let _62_277 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (_62_277) with
| (expected_k, _62_274, _62_276) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos)
in (

let env = (

let _62_279 = env
in {FStar_TypeChecker_Env.solver = _62_279.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _62_279.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _62_279.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _62_279.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _62_279.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _62_279.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _62_279.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _62_279.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _62_279.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _62_279.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _62_279.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _62_279.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _62_279.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _62_279.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _62_279.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _62_279.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _62_279.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _62_279.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _62_279.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _62_279.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _62_279.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _62_279.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _62_279.FStar_TypeChecker_Env.qname_and_index})
in (

let br = (check_and_gen' env ed.FStar_Syntax_Syntax.bind_repr expected_k)
in br)))
end)))))))))
end)))
in (

let return_repr = (

let x_a = (let _163_278 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.gen_bv "x_a" None _163_278))
in (

let res = (

let wp = (let _163_285 = (let _163_279 = (FStar_TypeChecker_Env.inst_tscheme return_wp)
in (FStar_All.pipe_right _163_279 Prims.snd))
in (let _163_284 = (let _163_283 = (let _163_282 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _163_281 = (let _163_280 = (FStar_Syntax_Syntax.bv_to_name x_a)
in (_163_280)::[])
in (_163_282)::_163_281))
in (FStar_List.map FStar_Syntax_Syntax.as_arg _163_283))
in (FStar_Syntax_Syntax.mk_Tm_app _163_285 _163_284 None FStar_Range.dummyRange)))
in (mk_repr a wp))
in (

let expected_k = (let _163_290 = (let _163_288 = (FStar_Syntax_Syntax.mk_binder a)
in (let _163_287 = (let _163_286 = (FStar_Syntax_Syntax.mk_binder x_a)
in (_163_286)::[])
in (_163_288)::_163_287))
in (let _163_289 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow _163_290 _163_289)))
in (

let _62_293 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (_62_293) with
| (expected_k, _62_290, _62_292) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env (Prims.snd ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos)
in (

let _62_297 = (check_and_gen' env ed.FStar_Syntax_Syntax.return_repr expected_k)
in (match (_62_297) with
| (univs, repr) -> begin
(match (univs) with
| [] -> begin
(([]), (repr))
end
| _62_300 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected universe-polymorphic return for effect"), (repr.FStar_Syntax_Syntax.pos)))))
end)
end)))
end)))))
in (

let actions = (

let check_action = (fun act -> (

let _62_308 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env act.FStar_Syntax_Syntax.action_typ)
in (match (_62_308) with
| (act_typ, _62_306, g_t) -> begin
(

let env' = (FStar_TypeChecker_Env.set_expected_typ env act_typ)
in (

let _62_310 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _163_294 = (FStar_Syntax_Print.term_to_string act.FStar_Syntax_Syntax.action_defn)
in (let _163_293 = (FStar_Syntax_Print.term_to_string act_typ)
in (FStar_Util.print3 "Checking action %s:\n[definition]: %s\n[cps\'d type]: %s\n" (FStar_Ident.text_of_lid act.FStar_Syntax_Syntax.action_name) _163_294 _163_293)))
end else begin
()
end
in (

let _62_316 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' act.FStar_Syntax_Syntax.action_defn)
in (match (_62_316) with
| (act_defn, _62_314, g_a) -> begin
(

let act_defn = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env act_defn)
in (

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
in (

let _62_339 = (

let act_typ = (FStar_Syntax_Subst.compress act_typ)
in (match (act_typ.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _62_327 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_62_327) with
| (bs, _62_326) -> begin
(

let res = (mk_repr' FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun)
in (

let k = (let _163_295 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow bs _163_295))
in (

let _62_334 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env k)
in (match (_62_334) with
| (k, _62_332, g) -> begin
((k), (g))
end))))
end))
end
| _62_336 -> begin
(let _163_300 = (let _163_299 = (let _163_298 = (let _163_297 = (FStar_Syntax_Print.term_to_string act_typ)
in (let _163_296 = (FStar_Syntax_Print.tag_of_term act_typ)
in (FStar_Util.format2 "Actions must have function types (not: %s, a.k.a. %s)" _163_297 _163_296)))
in ((_163_298), (act_defn.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (_163_299))
in (Prims.raise _163_300))
end))
in (match (_62_339) with
| (expected_k, g_k) -> begin
(

let g = (FStar_TypeChecker_Rel.teq env act_typ expected_k)
in (

let _62_341 = (let _163_303 = (let _163_302 = (let _163_301 = (FStar_TypeChecker_Rel.conj_guard g_t g)
in (FStar_TypeChecker_Rel.conj_guard g_k _163_301))
in (FStar_TypeChecker_Rel.conj_guard g_a _163_302))
in (FStar_TypeChecker_Rel.force_trivial_guard env _163_303))
in (

let act_typ = (match ((let _163_304 = (FStar_Syntax_Subst.compress expected_k)
in _163_304.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _62_349 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_62_349) with
| (bs, c) -> begin
(

let _62_352 = (destruct_repr (FStar_Syntax_Util.comp_result c))
in (match (_62_352) with
| (a, wp) -> begin
(

let c = (let _163_308 = (let _163_305 = (env.FStar_TypeChecker_Env.universe_of env a)
in (_163_305)::[])
in (let _163_307 = (let _163_306 = (FStar_Syntax_Syntax.as_arg wp)
in (_163_306)::[])
in {FStar_Syntax_Syntax.comp_univs = _163_308; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = a; FStar_Syntax_Syntax.effect_args = _163_307; FStar_Syntax_Syntax.flags = []}))
in (let _163_309 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Util.arrow bs _163_309)))
end))
end))
end
| _62_355 -> begin
(failwith "")
end)
in (

let _62_359 = (FStar_TypeChecker_Util.generalize_universes env act_defn)
in (match (_62_359) with
| (univs, act_defn) -> begin
(

let act_typ = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env act_typ)
in (

let _62_361 = act
in {FStar_Syntax_Syntax.action_name = _62_361.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = _62_361.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = act_defn; FStar_Syntax_Syntax.action_typ = act_typ}))
end)))))
end))))
end))))
end)))
in (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.map check_action)))
in ((repr), (bind_repr), (return_repr), (actions)))))))))
end)
in (match (_62_368) with
| (repr, bind_repr, return_repr, actions) -> begin
(

let t = (let _163_310 = (FStar_Syntax_Syntax.mk_Total ed.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ed.FStar_Syntax_Syntax.binders _163_310))
in (

let _62_372 = (FStar_TypeChecker_Util.generalize_universes env0 t)
in (match (_62_372) with
| (univs, t) -> begin
(

let signature = (match ((let _163_312 = (let _163_311 = (FStar_Syntax_Subst.compress t)
in _163_311.FStar_Syntax_Syntax.n)
in ((effect_params), (_163_312)))) with
| ([], _62_375) -> begin
t
end
| (_62_378, FStar_Syntax_Syntax.Tm_arrow (_62_380, c)) -> begin
(FStar_Syntax_Util.comp_result c)
end
| _62_386 -> begin
(failwith "Impossible")
end)
in (

let close = (fun n ts -> (

let ts = (let _163_317 = (FStar_Syntax_Subst.close_tscheme effect_params ts)
in (FStar_Syntax_Subst.close_univ_vars_tscheme univs _163_317))
in (

let m = (FStar_List.length (Prims.fst ts))
in (

let _62_394 = if (((n >= (Prims.parse_int "0")) && (not ((FStar_Syntax_Util.is_unknown (Prims.snd ts))))) && (m <> n)) then begin
(

let error = if (m < n) then begin
"not universe-polymorphic enough"
end else begin
"too universe-polymorphic"
end
in (let _163_320 = (let _163_319 = (FStar_Util.string_of_int n)
in (let _163_318 = (FStar_Syntax_Print.tscheme_to_string ts)
in (FStar_Util.format3 "The effect combinator is %s (n=%s) (%s)" error _163_319 _163_318)))
in (failwith _163_320)))
end else begin
()
end
in ts))))
in (

let close_action = (fun act -> (

let _62_400 = (close (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_defn)))
in (match (_62_400) with
| (univs, defn) -> begin
(

let _62_403 = (close (~- ((Prims.parse_int "1"))) ((act.FStar_Syntax_Syntax.action_univs), (act.FStar_Syntax_Syntax.action_typ)))
in (match (_62_403) with
| (univs', typ) -> begin
(

let _62_404 = ()
in (

let _62_406 = act
in {FStar_Syntax_Syntax.action_name = _62_406.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = _62_406.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = univs; FStar_Syntax_Syntax.action_defn = defn; FStar_Syntax_Syntax.action_typ = typ}))
end))
end)))
in (

let nunivs = (FStar_List.length univs)
in (

let _62_409 = ()
in (

let ed = (

let _62_411 = ed
in (let _163_337 = (close (Prims.parse_int "0") return_wp)
in (let _163_336 = (close (Prims.parse_int "1") bind_wp)
in (let _163_335 = (close (Prims.parse_int "0") if_then_else)
in (let _163_334 = (close (Prims.parse_int "0") ite_wp)
in (let _163_333 = (close (Prims.parse_int "0") stronger)
in (let _163_332 = (close (Prims.parse_int "1") close_wp)
in (let _163_331 = (close (Prims.parse_int "0") assert_p)
in (let _163_330 = (close (Prims.parse_int "0") assume_p)
in (let _163_329 = (close (Prims.parse_int "0") null_wp)
in (let _163_328 = (close (Prims.parse_int "0") trivial_wp)
in (let _163_327 = (let _163_323 = (close (Prims.parse_int "0") (([]), (repr)))
in (Prims.snd _163_323))
in (let _163_326 = (close (Prims.parse_int "0") return_repr)
in (let _163_325 = (close (Prims.parse_int "1") bind_repr)
in (let _163_324 = (FStar_List.map close_action actions)
in {FStar_Syntax_Syntax.qualifiers = _62_411.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = _62_411.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = _62_411.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = univs; FStar_Syntax_Syntax.binders = effect_params; FStar_Syntax_Syntax.signature = signature; FStar_Syntax_Syntax.ret_wp = _163_337; FStar_Syntax_Syntax.bind_wp = _163_336; FStar_Syntax_Syntax.if_then_else = _163_335; FStar_Syntax_Syntax.ite_wp = _163_334; FStar_Syntax_Syntax.stronger = _163_333; FStar_Syntax_Syntax.close_wp = _163_332; FStar_Syntax_Syntax.assert_p = _163_331; FStar_Syntax_Syntax.assume_p = _163_330; FStar_Syntax_Syntax.null_wp = _163_329; FStar_Syntax_Syntax.trivial = _163_328; FStar_Syntax_Syntax.repr = _163_327; FStar_Syntax_Syntax.return_repr = _163_326; FStar_Syntax_Syntax.bind_repr = _163_325; FStar_Syntax_Syntax.actions = _163_324})))))))))))))))
in (

let _62_414 = if ((FStar_TypeChecker_Env.debug env FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ED")))) then begin
(let _163_338 = (FStar_Syntax_Print.eff_decl_to_string false ed)
in (FStar_Util.print_string _163_338))
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

let _62_420 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (_62_420) with
| (effect_binders_un, signature_un) -> begin
(

let _62_425 = (tc_tparams env effect_binders_un)
in (match (_62_425) with
| (effect_binders, env, _62_424) -> begin
(

let _62_429 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un)
in (match (_62_429) with
| (signature, _62_428) -> begin
(

let effect_binders = (FStar_List.map (fun _62_432 -> (match (_62_432) with
| (bv, qual) -> begin
(let _163_343 = (

let _62_433 = bv
in (let _163_342 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env bv.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _62_433.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _62_433.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _163_342}))
in ((_163_343), (qual)))
end)) effect_binders)
in (

let _62_448 = (match ((let _163_344 = (FStar_Syntax_Subst.compress signature_un)
in _163_344.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (((a, _62_438))::[], effect_marker) -> begin
((a), (effect_marker))
end
| _62_445 -> begin
(failwith "bad shape for effect-for-free signature")
end)
in (match (_62_448) with
| (a, effect_marker) -> begin
(

let a = if (FStar_Syntax_Syntax.is_null_bv a) then begin
(let _163_346 = (let _163_345 = (FStar_Syntax_Syntax.range_of_bv a)
in Some (_163_345))
in (FStar_Syntax_Syntax.gen_bv "a" _163_346 a.FStar_Syntax_Syntax.sort))
end else begin
a
end
in (

let open_and_check = (fun t -> (

let subst = (FStar_Syntax_Subst.opening_of_binders effect_binders)
in (

let t = (FStar_Syntax_Subst.subst subst t)
in (

let _62_458 = (FStar_TypeChecker_TcTerm.tc_term env t)
in (match (_62_458) with
| (t, comp, _62_457) -> begin
((t), (comp))
end)))))
in (

let mk = (fun x -> (FStar_Syntax_Syntax.mk x None signature.FStar_Syntax_Syntax.pos))
in (

let _62_463 = (open_and_check ed.FStar_Syntax_Syntax.repr)
in (match (_62_463) with
| (repr, _comp) -> begin
(

let _62_464 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _163_351 = (FStar_Syntax_Print.term_to_string repr)
in (FStar_Util.print1 "Representation is: %s\n" _163_351))
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

let wp_a = (let _163_358 = (let _163_357 = (let _163_356 = (let _163_355 = (let _163_354 = (let _163_353 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _163_352 = (FStar_Syntax_Syntax.as_implicit false)
in ((_163_353), (_163_352))))
in (_163_354)::[])
in ((wp_type), (_163_355)))
in FStar_Syntax_Syntax.Tm_app (_163_356))
in (mk _163_357))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _163_358))
in (

let effect_signature = (

let binders = (let _163_363 = (let _163_359 = (FStar_Syntax_Syntax.as_implicit false)
in ((a), (_163_359)))
in (let _163_362 = (let _163_361 = (let _163_360 = (FStar_Syntax_Syntax.gen_bv "dijkstra_wp" None wp_a)
in (FStar_All.pipe_right _163_360 FStar_Syntax_Syntax.mk_binder))
in (_163_361)::[])
in (_163_363)::_163_362))
in (

let binders = (FStar_Syntax_Subst.close_binders binders)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((binders), (effect_marker)))))))
in (

let effect_signature = (recheck_debug "turned into the effect signature" env effect_signature)
in (

let sigelts = (FStar_Util.mk_ref [])
in (

let mk_lid = (fun name -> (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" name))) FStar_Range.dummyRange))
in (

let elaborate_and_star = (fun dmff_env item -> (

let _62_482 = item
in (match (_62_482) with
| (u_item, item) -> begin
(

let _62_485 = (open_and_check item)
in (match (_62_485) with
| (item, item_comp) -> begin
(

let _62_486 = if (not ((FStar_Syntax_Util.is_total_lcomp item_comp))) then begin
(let _163_373 = (let _163_372 = (let _163_371 = (FStar_Syntax_Print.term_to_string item)
in (let _163_370 = (FStar_Syntax_Print.lcomp_to_string item_comp)
in (FStar_Util.format2 "Computation for [%s] is not total : %s !" _163_371 _163_370)))
in FStar_Errors.Err (_163_372))
in (Prims.raise _163_373))
end else begin
()
end
in (

let _62_491 = (FStar_TypeChecker_DMFF.star_expr dmff_env item)
in (match (_62_491) with
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

let _62_499 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.bind_repr)
in (match (_62_499) with
| (dmff_env, _62_496, bind_wp, bind_elab) -> begin
(

let _62_505 = (elaborate_and_star dmff_env ed.FStar_Syntax_Syntax.return_repr)
in (match (_62_505) with
| (dmff_env, _62_502, return_wp, return_elab) -> begin
(

let lift_from_pure_wp = (match ((let _163_374 = (FStar_Syntax_Subst.compress return_wp)
in _163_374.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(

let _62_525 = (match ((let _163_375 = (FStar_Syntax_Util.abs bs body None)
in (FStar_Syntax_Subst.open_term ((b1)::(b2)::[]) _163_375))) with
| ((b1)::(b2)::[], body) -> begin
((b1), (b2), (body))
end
| _62_521 -> begin
(failwith "Impossible : open_term not preserving binders arity")
end)
in (match (_62_525) with
| (b1, b2, body) -> begin
(

let env0 = (let _163_376 = (FStar_TypeChecker_DMFF.get_env dmff_env)
in (FStar_TypeChecker_Env.push_binders _163_376 ((b1)::(b2)::[])))
in (

let wp_b1 = (let _163_383 = (let _163_382 = (let _163_381 = (let _163_380 = (let _163_379 = (let _163_378 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b1))
in (let _163_377 = (FStar_Syntax_Syntax.as_implicit false)
in ((_163_378), (_163_377))))
in (_163_379)::[])
in ((wp_type), (_163_380)))
in FStar_Syntax_Syntax.Tm_app (_163_381))
in (mk _163_382))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env0 _163_383))
in (

let _62_531 = (let _163_385 = (let _163_384 = (FStar_Syntax_Util.unascribe wp_b1)
in (FStar_TypeChecker_Normalize.eta_expand_with_type body _163_384))
in (FStar_All.pipe_left FStar_Syntax_Util.abs_formals _163_385))
in (match (_62_531) with
| (bs, body, what') -> begin
(

let t2 = (Prims.fst b2).FStar_Syntax_Syntax.sort
in (

let pure_wp_type = (FStar_TypeChecker_DMFF.double_star t2)
in (

let wp = (FStar_Syntax_Syntax.gen_bv "wp" None pure_wp_type)
in (

let body = (let _163_389 = (FStar_Syntax_Syntax.bv_to_name wp)
in (let _163_388 = (let _163_387 = (let _163_386 = (FStar_Syntax_Util.abs ((b2)::[]) body what')
in ((_163_386), (None)))
in (_163_387)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _163_389 _163_388 None FStar_Range.dummyRange)))
in (let _163_393 = (let _163_391 = (let _163_390 = (FStar_Syntax_Syntax.mk_binder wp)
in (_163_390)::[])
in (b1)::_163_391)
in (let _163_392 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs _163_393 _163_392 (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_GTot_lid), ([]))))))))))))
end))))
end))
end
| _62_537 -> begin
(failwith "unexpected shape for return")
end)
in (

let return_wp = (match ((let _163_394 = (FStar_Syntax_Subst.compress return_wp)
in _163_394.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((b1)::(b2)::bs, body, what) -> begin
(let _163_395 = (FStar_Syntax_Util.abs bs body what)
in (FStar_Syntax_Util.abs ((b1)::(b2)::[]) _163_395 (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_GTot_lid), ([])))))))
end
| _62_549 -> begin
(failwith "unexpected shape for return")
end)
in (

let bind_wp = (match ((let _163_396 = (FStar_Syntax_Subst.compress bind_wp)
in _163_396.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, what) -> begin
(

let r = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.range_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (let _163_400 = (let _163_399 = (let _163_398 = (let _163_397 = (mk (FStar_Syntax_Syntax.Tm_fvar (r)))
in (FStar_Syntax_Syntax.null_binder _163_397))
in (_163_398)::[])
in (FStar_List.append _163_399 binders))
in (FStar_Syntax_Util.abs _163_400 body what)))
end
| _62_558 -> begin
(failwith "unexpected shape for bind")
end)
in (

let apply_close = (fun t -> if ((FStar_List.length effect_binders) = (Prims.parse_int "0")) then begin
t
end else begin
(let _163_407 = (let _163_406 = (let _163_405 = (let _163_404 = (let _163_403 = (FStar_Syntax_Util.args_of_binders effect_binders)
in (Prims.snd _163_403))
in ((t), (_163_404)))
in FStar_Syntax_Syntax.Tm_app (_163_405))
in (mk _163_406))
in (FStar_Syntax_Subst.close effect_binders _163_407))
end)
in (

let register = (fun name item -> (

let _62_567 = (let _163_413 = (mk_lid name)
in (let _163_412 = (FStar_Syntax_Util.abs effect_binders item None)
in (FStar_TypeChecker_Util.mk_toplevel_definition env _163_413 _163_412)))
in (match (_62_567) with
| (sigelt, fv) -> begin
(

let _62_568 = (let _163_415 = (let _163_414 = (FStar_ST.read sigelts)
in (sigelt)::_163_414)
in (FStar_ST.op_Colon_Equals sigelts _163_415))
in fv)
end)))
in (

let lift_from_pure_wp = (register "lift_from_pure" lift_from_pure_wp)
in (

let return_wp = (register "return_wp" return_wp)
in (

let _62_572 = (let _163_417 = (let _163_416 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true")), (FStar_Range.dummyRange))))::_163_416)
in (FStar_ST.op_Colon_Equals sigelts _163_417))
in (

let return_elab = (register "return_elab" return_elab)
in (

let _62_575 = (let _163_419 = (let _163_418 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false")), (FStar_Range.dummyRange))))::_163_418)
in (FStar_ST.op_Colon_Equals sigelts _163_419))
in (

let bind_wp = (register "bind_wp" bind_wp)
in (

let _62_578 = (let _163_421 = (let _163_420 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries true")), (FStar_Range.dummyRange))))::_163_420)
in (FStar_ST.op_Colon_Equals sigelts _163_421))
in (

let bind_elab = (register "bind_elab" bind_elab)
in (

let _62_581 = (let _163_423 = (let _163_422 = (FStar_ST.read sigelts)
in (FStar_Syntax_Syntax.Sig_pragma (((FStar_Syntax_Syntax.SetOptions ("--admit_smt_queries false")), (FStar_Range.dummyRange))))::_163_422)
in (FStar_ST.op_Colon_Equals sigelts _163_423))
in (

let _62_600 = (FStar_List.fold_left (fun _62_585 action -> (match (_62_585) with
| (dmff_env, actions) -> begin
(

let _62_591 = (elaborate_and_star dmff_env ((action.FStar_Syntax_Syntax.action_univs), (action.FStar_Syntax_Syntax.action_defn)))
in (match (_62_591) with
| (dmff_env, action_t, action_wp, action_elab) -> begin
(

let name = action.FStar_Syntax_Syntax.action_name.FStar_Ident.ident.FStar_Ident.idText
in (

let action_typ_with_wp = (FStar_TypeChecker_DMFF.trans_F dmff_env action_t action_wp)
in (

let action_elab = (register (Prims.strcat name "_elab") action_elab)
in (

let action_typ_with_wp = (register (Prims.strcat name "_complete_type") action_typ_with_wp)
in (let _163_429 = (let _163_428 = (

let _62_596 = action
in (let _163_427 = (apply_close action_elab)
in (let _163_426 = (apply_close action_typ_with_wp)
in {FStar_Syntax_Syntax.action_name = _62_596.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = _62_596.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = _62_596.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _163_427; FStar_Syntax_Syntax.action_typ = _163_426})))
in (_163_428)::actions)
in ((dmff_env), (_163_429)))))))
end))
end)) ((dmff_env), ([])) ed.FStar_Syntax_Syntax.actions)
in (match (_62_600) with
| (dmff_env, actions) -> begin
(

let actions = (FStar_List.rev actions)
in (

let repr = (

let wp = (FStar_Syntax_Syntax.gen_bv "wp_a" None wp_a)
in (

let binders = (let _163_432 = (FStar_Syntax_Syntax.mk_binder a)
in (let _163_431 = (let _163_430 = (FStar_Syntax_Syntax.mk_binder wp)
in (_163_430)::[])
in (_163_432)::_163_431))
in (let _163_441 = (let _163_440 = (let _163_438 = (let _163_437 = (let _163_436 = (let _163_435 = (let _163_434 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _163_433 = (FStar_Syntax_Syntax.as_implicit false)
in ((_163_434), (_163_433))))
in (_163_435)::[])
in ((repr), (_163_436)))
in FStar_Syntax_Syntax.Tm_app (_163_437))
in (mk _163_438))
in (let _163_439 = (FStar_Syntax_Syntax.bv_to_name wp)
in (FStar_TypeChecker_DMFF.trans_F dmff_env _163_440 _163_439)))
in (FStar_Syntax_Util.abs binders _163_441 None))))
in (

let repr = (recheck_debug "FC" env repr)
in (

let repr = (register "repr" repr)
in (

let _62_651 = (match ((let _163_443 = (let _163_442 = (FStar_Syntax_Subst.compress wp_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe _163_442))
in _163_443.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((type_param)::effect_param, arrow, _62_612) -> begin
(

let _62_625 = (match ((FStar_Syntax_Subst.open_term ((type_param)::effect_param) arrow)) with
| ((b)::bs, body) -> begin
((b), (bs), (body))
end
| _62_621 -> begin
(failwith "Impossible : open_term nt preserving binders arity")
end)
in (match (_62_625) with
| (type_param, effect_param, arrow) -> begin
(match ((let _163_445 = (let _163_444 = (FStar_Syntax_Subst.compress arrow)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe _163_444))
in _163_445.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (wp_binders, c) -> begin
(

let _62_632 = (FStar_Syntax_Subst.open_comp wp_binders c)
in (match (_62_632) with
| (wp_binders, c) -> begin
(

let _62_639 = (FStar_List.partition (fun _62_636 -> (match (_62_636) with
| (bv, _62_635) -> begin
(let _163_448 = (let _163_447 = (FStar_Syntax_Free.names bv.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _163_447 (FStar_Util.set_mem (Prims.fst type_param))))
in (FStar_All.pipe_right _163_448 Prims.op_Negation))
end)) wp_binders)
in (match (_62_639) with
| (pre_args, post_args) -> begin
(

let post = (match (post_args) with
| (post)::[] -> begin
post
end
| _62_643 -> begin
(let _163_450 = (let _163_449 = (FStar_Syntax_Print.term_to_string arrow)
in (FStar_Util.format1 "Impossible: multiple post candidates %s" _163_449))
in (failwith _163_450))
end)
in (let _163_452 = (FStar_Syntax_Util.arrow pre_args c)
in (let _163_451 = (FStar_Syntax_Util.abs ((type_param)::effect_param) (Prims.fst post).FStar_Syntax_Syntax.sort None)
in ((_163_452), (_163_451)))))
end))
end))
end
| _62_646 -> begin
(let _163_454 = (let _163_453 = (FStar_Syntax_Print.term_to_string arrow)
in (FStar_Util.format1 "Impossible: pre/post arrow %s" _163_453))
in (failwith _163_454))
end)
end))
end
| _62_648 -> begin
(let _163_456 = (let _163_455 = (FStar_Syntax_Print.term_to_string wp_type)
in (FStar_Util.format1 "Impossible: pre/post abs %s" _163_455))
in (failwith _163_456))
end)
in (match (_62_651) with
| (pre, post) -> begin
(

let _62_652 = (let _163_457 = (register "pre" pre)
in (Prims.ignore _163_457))
in (

let _62_654 = (let _163_458 = (register "post" post)
in (Prims.ignore _163_458))
in (

let _62_656 = (let _163_459 = (register "wp" wp_type)
in (Prims.ignore _163_459))
in (

let ed = (

let _62_658 = ed
in (let _163_470 = (FStar_Syntax_Subst.close_binders effect_binders)
in (let _163_469 = (FStar_Syntax_Subst.close effect_binders effect_signature)
in (let _163_468 = (let _163_460 = (apply_close return_wp)
in (([]), (_163_460)))
in (let _163_467 = (let _163_461 = (apply_close bind_wp)
in (([]), (_163_461)))
in (let _163_466 = (apply_close repr)
in (let _163_465 = (let _163_462 = (apply_close return_elab)
in (([]), (_163_462)))
in (let _163_464 = (let _163_463 = (apply_close bind_elab)
in (([]), (_163_463)))
in {FStar_Syntax_Syntax.qualifiers = _62_658.FStar_Syntax_Syntax.qualifiers; FStar_Syntax_Syntax.cattributes = _62_658.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = _62_658.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = _62_658.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = _163_470; FStar_Syntax_Syntax.signature = _163_469; FStar_Syntax_Syntax.ret_wp = _163_468; FStar_Syntax_Syntax.bind_wp = _163_467; FStar_Syntax_Syntax.if_then_else = _62_658.FStar_Syntax_Syntax.if_then_else; FStar_Syntax_Syntax.ite_wp = _62_658.FStar_Syntax_Syntax.ite_wp; FStar_Syntax_Syntax.stronger = _62_658.FStar_Syntax_Syntax.stronger; FStar_Syntax_Syntax.close_wp = _62_658.FStar_Syntax_Syntax.close_wp; FStar_Syntax_Syntax.assert_p = _62_658.FStar_Syntax_Syntax.assert_p; FStar_Syntax_Syntax.assume_p = _62_658.FStar_Syntax_Syntax.assume_p; FStar_Syntax_Syntax.null_wp = _62_658.FStar_Syntax_Syntax.null_wp; FStar_Syntax_Syntax.trivial = _62_658.FStar_Syntax_Syntax.trivial; FStar_Syntax_Syntax.repr = _163_466; FStar_Syntax_Syntax.return_repr = _163_465; FStar_Syntax_Syntax.bind_repr = _163_464; FStar_Syntax_Syntax.actions = actions}))))))))
in (

let _62_663 = (FStar_TypeChecker_DMFF.gen_wps_for_free env effect_binders a wp_a ed)
in (match (_62_663) with
| (sigelts', ed) -> begin
(

let _62_664 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(let _163_471 = (FStar_Syntax_Print.eff_decl_to_string true ed)
in (FStar_Util.print_string _163_471))
end else begin
()
end
in (

let lift_from_pure_opt = if ((FStar_List.length effect_binders) = (Prims.parse_int "0")) then begin
(

let lift_from_pure = (let _163_474 = (let _163_473 = (let _163_472 = (apply_close lift_from_pure_wp)
in (([]), (_163_472)))
in Some (_163_473))
in {FStar_Syntax_Syntax.source = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.target = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.lift_wp = _163_474; FStar_Syntax_Syntax.lift = None})
in Some (FStar_Syntax_Syntax.Sig_sub_effect (((lift_from_pure), (FStar_Range.dummyRange)))))
end else begin
None
end
in (let _163_477 = (let _163_476 = (let _163_475 = (FStar_ST.read sigelts)
in (FStar_List.rev _163_475))
in (FStar_List.append _163_476 sigelts'))
in ((_163_477), (ed), (lift_from_pure_opt)))))
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

let _62_672 = ()
in (

let _62_680 = ()
in (match (ses) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (lex_t, [], [], t, _62_709, _62_711, [], r))::(FStar_Syntax_Syntax.Sig_datacon (lex_top, [], _t_top, _lex_t_top, _163_482, [], _62_700, r1))::(FStar_Syntax_Syntax.Sig_datacon (lex_cons, [], _t_cons, _lex_t_cons, _163_483, [], _62_689, r2))::[] when (((_163_482 = (Prims.parse_int "0")) && (_163_483 = (Prims.parse_int "0"))) && (((FStar_Ident.lid_equals lex_t FStar_Syntax_Const.lex_t_lid) && (FStar_Ident.lid_equals lex_top FStar_Syntax_Const.lextop_lid)) && (FStar_Ident.lid_equals lex_cons FStar_Syntax_Const.lexcons_lid))) -> begin
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

let lex_top_t = (let _163_486 = (let _163_485 = (let _163_484 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r1) FStar_Syntax_Syntax.Delta_constant None)
in ((_163_484), ((FStar_Syntax_Syntax.U_name (utop))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_163_485))
in (FStar_Syntax_Syntax.mk _163_486 None r1))
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

let a = (let _163_487 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_name (ucons1))) None r2)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _163_487))
in (

let hd = (let _163_488 = (FStar_Syntax_Syntax.bv_to_name a)
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _163_488))
in (

let tl = (let _163_492 = (let _163_491 = (let _163_490 = (let _163_489 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2) FStar_Syntax_Syntax.Delta_constant None)
in ((_163_489), ((FStar_Syntax_Syntax.U_name (ucons2))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_163_490))
in (FStar_Syntax_Syntax.mk _163_491 None r2))
in (FStar_Syntax_Syntax.new_bv (Some (r2)) _163_492))
in (

let res = (let _163_495 = (let _163_494 = (let _163_493 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.lex_t_lid r2) FStar_Syntax_Syntax.Delta_constant None)
in ((_163_493), ((FStar_Syntax_Syntax.U_max ((FStar_Syntax_Syntax.U_name (ucons1))::(FStar_Syntax_Syntax.U_name (ucons2))::[]))::[])))
in FStar_Syntax_Syntax.Tm_uinst (_163_494))
in (FStar_Syntax_Syntax.mk _163_495 None r2))
in (let _163_496 = (FStar_Syntax_Syntax.mk_Total res)
in (FStar_Syntax_Util.arrow ((((a), (Some (FStar_Syntax_Syntax.imp_tag))))::(((hd), (None)))::(((tl), (None)))::[]) _163_496))))))
in (

let lex_cons_t = (FStar_Syntax_Subst.close_univ_vars ((ucons1)::(ucons2)::[]) lex_cons_t)
in (

let dc_lexcons = FStar_Syntax_Syntax.Sig_datacon (((lex_cons), ((ucons1)::(ucons2)::[]), (lex_cons_t), (FStar_Syntax_Const.lex_t_lid), ((Prims.parse_int "0")), ([]), ([]), (r2)))
in (let _163_498 = (let _163_497 = (FStar_TypeChecker_Env.get_range env)
in (((tc)::(dc_lextop)::(dc_lexcons)::[]), ([]), (lids), (_163_497)))
in FStar_Syntax_Syntax.Sig_bundle (_163_498)))))))))))))))
end
| _62_735 -> begin
(let _163_500 = (let _163_499 = (FStar_Syntax_Print.sigelt_to_string (FStar_Syntax_Syntax.Sig_bundle (((ses), ([]), (lids), (FStar_Range.dummyRange)))))
in (FStar_Util.format1 "Unexpected lex_t: %s\n" _163_499))
in (failwith _163_500))
end))))
and tc_assume : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env lid phi quals r -> (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _62_745 = (FStar_Syntax_Util.type_u ())
in (match (_62_745) with
| (k, _62_744) -> begin
(

let phi = (let _163_506 = (tc_check_trivial_guard env phi k)
in (FStar_All.pipe_right _163_506 (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env)))
in (

let _62_747 = (FStar_TypeChecker_Util.check_uvars r phi)
in FStar_Syntax_Syntax.Sig_assume (((lid), (phi), (quals), (r)))))
end))))
and tc_inductive : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lident Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env ses quals lids -> (

let warn_positivity = (fun l r -> (let _163_516 = (let _163_515 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Positivity check is not yet implemented (%s)" _163_515))
in (FStar_Errors.diag r _163_516)))
in (

let env0 = env
in (

let tc_tycon = (fun env s -> (match (s) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals, r) -> begin
(

let _62_770 = ()
in (

let _62_772 = (warn_positivity tc r)
in (

let _62_776 = (FStar_Syntax_Subst.open_term tps k)
in (match (_62_776) with
| (tps, k) -> begin
(

let _62_781 = (FStar_TypeChecker_TcTerm.tc_binders env tps)
in (match (_62_781) with
| (tps, env_tps, guard_params, us) -> begin
(

let _62_784 = (FStar_Syntax_Util.arrow_formals k)
in (match (_62_784) with
| (indices, t) -> begin
(

let _62_789 = (FStar_TypeChecker_TcTerm.tc_binders env_tps indices)
in (match (_62_789) with
| (indices, env', guard_indices, us') -> begin
(

let _62_797 = (

let _62_794 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env' t)
in (match (_62_794) with
| (t, _62_792, g) -> begin
(let _163_523 = (let _163_522 = (let _163_521 = (FStar_TypeChecker_Rel.conj_guard guard_indices g)
in (FStar_TypeChecker_Rel.conj_guard guard_params _163_521))
in (FStar_TypeChecker_Rel.discharge_guard env' _163_522))
in ((t), (_163_523)))
end))
in (match (_62_797) with
| (t, guard) -> begin
(

let k = (let _163_524 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow indices _163_524))
in (

let _62_801 = (FStar_Syntax_Util.type_u ())
in (match (_62_801) with
| (t_type, u) -> begin
(

let _62_802 = (let _163_525 = (FStar_TypeChecker_Rel.teq env' t t_type)
in (FStar_TypeChecker_Rel.force_trivial_guard env' _163_525))
in (

let t_tc = (let _163_526 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow (FStar_List.append tps indices) _163_526))
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let k = (FStar_Syntax_Subst.close tps k)
in (

let fv_tc = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (let _163_527 = (FStar_TypeChecker_Env.push_let_binding env (FStar_Util.Inr (fv_tc)) (([]), (t_tc)))
in ((_163_527), (FStar_Syntax_Syntax.Sig_inductive_typ (((tc), ([]), (tps), (k), (mutuals), (data), (quals), (r)))), (u), (guard))))))))
end)))
end))
end))
end))
end))
end))))
end
| _62_809 -> begin
(failwith "impossible")
end))
in (

let positive_if_pure = (fun _62_811 l -> ())
in (

let tc_data = (fun env tcs _62_1 -> (match (_62_1) with
| FStar_Syntax_Syntax.Sig_datacon (c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs, r) -> begin
(

let _62_828 = ()
in (

let _62_865 = (

let tps_u_opt = (FStar_Util.find_map tcs (fun _62_832 -> (match (_62_832) with
| (se, u_tc) -> begin
if (let _163_539 = (FStar_Util.must (FStar_Syntax_Util.lid_of_sigelt se))
in (FStar_Ident.lid_equals tc_lid _163_539)) then begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_62_834, _62_836, tps, _62_839, _62_841, _62_843, _62_845, _62_847) -> begin
(

let tps = (FStar_All.pipe_right tps (FStar_List.map (fun _62_853 -> (match (_62_853) with
| (x, _62_852) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let tps = (FStar_Syntax_Subst.open_binders tps)
in (let _163_542 = (let _163_541 = (FStar_TypeChecker_Env.push_binders env tps)
in ((_163_541), (tps), (u_tc)))
in Some (_163_542))))
end
| _62_857 -> begin
(failwith "Impossible")
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
(Prims.raise (FStar_Errors.Error ((("Unexpected data constructor"), (r)))))
end
end))
in (match (_62_865) with
| (env, tps, u_tc) -> begin
(

let _62_885 = (match ((let _163_543 = (FStar_Syntax_Subst.compress t)
in _163_543.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, res) -> begin
(

let _62_873 = (FStar_Util.first_N ntps bs)
in (match (_62_873) with
| (_62_871, bs') -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs'), (res)))) None t.FStar_Syntax_Syntax.pos)
in (

let subst = (FStar_All.pipe_right tps (FStar_List.mapi (fun i _62_879 -> (match (_62_879) with
| (x, _62_878) -> begin
FStar_Syntax_Syntax.DB ((((ntps - ((Prims.parse_int "1") + i))), (x)))
end))))
in (let _163_546 = (FStar_Syntax_Subst.subst subst t)
in (FStar_Syntax_Util.arrow_formals _163_546))))
end))
end
| _62_882 -> begin
(([]), (t))
end)
in (match (_62_885) with
| (arguments, result) -> begin
(

let _62_886 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _163_549 = (FStar_Syntax_Print.lid_to_string c)
in (let _163_548 = (FStar_Syntax_Print.binders_to_string "->" arguments)
in (let _163_547 = (FStar_Syntax_Print.term_to_string result)
in (FStar_Util.print3 "Checking datacon  %s : %s -> %s \n" _163_549 _163_548 _163_547))))
end else begin
()
end
in (

let _62_891 = (tc_tparams env arguments)
in (match (_62_891) with
| (arguments, env', us) -> begin
(

let _62_894 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env' result)
in (match (_62_894) with
| (result, res_lcomp) -> begin
(

let _62_899 = (match ((let _163_550 = (FStar_Syntax_Subst.compress res_lcomp.FStar_Syntax_Syntax.res_typ)
in _163_550.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_62_896) -> begin
()
end
| ty -> begin
(let _163_555 = (let _163_554 = (let _163_553 = (let _163_552 = (FStar_Syntax_Print.term_to_string result)
in (let _163_551 = (FStar_Syntax_Print.term_to_string res_lcomp.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "The type of %s is %s, but since this is the result type of a constructor its type should be Type" _163_552 _163_551)))
in ((_163_553), (r)))
in FStar_Errors.Error (_163_554))
in (Prims.raise _163_555))
end)
in (

let _62_904 = (FStar_Syntax_Util.head_and_args result)
in (match (_62_904) with
| (head, _62_903) -> begin
(

let _62_909 = (match ((let _163_556 = (FStar_Syntax_Subst.compress head)
in _163_556.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv tc_lid) -> begin
()
end
| _62_908 -> begin
(let _163_561 = (let _163_560 = (let _163_559 = (let _163_558 = (FStar_Syntax_Print.lid_to_string tc_lid)
in (let _163_557 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Expected a constructor of type %s; got %s" _163_558 _163_557)))
in ((_163_559), (r)))
in FStar_Errors.Error (_163_560))
in (Prims.raise _163_561))
end)
in (

let g = (FStar_List.fold_left2 (fun g _62_915 u_x -> (match (_62_915) with
| (x, _62_914) -> begin
(

let _62_917 = ()
in (let _163_565 = (FStar_TypeChecker_Rel.universe_inequality u_x u_tc)
in (FStar_TypeChecker_Rel.conj_guard g _163_565)))
end)) FStar_TypeChecker_Rel.trivial_guard arguments us)
in (

let t = (let _163_569 = (let _163_567 = (FStar_All.pipe_right tps (FStar_List.map (fun _62_923 -> (match (_62_923) with
| (x, _62_922) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end))))
in (FStar_List.append _163_567 arguments))
in (let _163_568 = (FStar_Syntax_Syntax.mk_Total result)
in (FStar_Syntax_Util.arrow _163_569 _163_568)))
in ((FStar_Syntax_Syntax.Sig_datacon (((c), ([]), (t), (tc_lid), (ntps), (quals), ([]), (r)))), (g)))))
end)))
end))
end)))
end))
end)))
end
| _62_926 -> begin
(failwith "impossible")
end))
in (

let generalize_and_inst_within = (fun env g tcs datas -> (

let _62_932 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let binders = (FStar_All.pipe_right tcs (FStar_List.map (fun _62_2 -> (match (_62_2) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_62_936, _62_938, tps, k, _62_942, _62_944, _62_946, _62_948) -> begin
(let _163_580 = (let _163_579 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_All.pipe_left (FStar_Syntax_Util.arrow tps) _163_579))
in (FStar_Syntax_Syntax.null_binder _163_580))
end
| _62_952 -> begin
(failwith "Impossible")
end))))
in (

let binders' = (FStar_All.pipe_right datas (FStar_List.map (fun _62_3 -> (match (_62_3) with
| FStar_Syntax_Syntax.Sig_datacon (_62_956, _62_958, t, _62_961, _62_963, _62_965, _62_967, _62_969) -> begin
(FStar_Syntax_Syntax.null_binder t)
end
| _62_973 -> begin
(failwith "Impossible")
end))))
in (

let t = (let _163_582 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_Syntax_Util.arrow (FStar_List.append binders binders') _163_582))
in (

let _62_976 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _163_583 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.print1 "@@@@@@Trying to generalize universes in %s\n" _163_583))
end else begin
()
end
in (

let _62_980 = (FStar_TypeChecker_Util.generalize_universes env t)
in (match (_62_980) with
| (uvs, t) -> begin
(

let _62_982 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _163_587 = (let _163_585 = (FStar_All.pipe_right uvs (FStar_List.map (fun u -> u.FStar_Ident.idText)))
in (FStar_All.pipe_right _163_585 (FStar_String.concat ", ")))
in (let _163_586 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "@@@@@@Generalized to (%s, %s)\n" _163_587 _163_586)))
end else begin
()
end
in (

let _62_986 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_62_986) with
| (uvs, t) -> begin
(

let _62_990 = (FStar_Syntax_Util.arrow_formals t)
in (match (_62_990) with
| (args, _62_989) -> begin
(

let _62_993 = (FStar_Util.first_N (FStar_List.length binders) args)
in (match (_62_993) with
| (tc_types, data_types) -> begin
(

let tcs = (FStar_List.map2 (fun _62_997 se -> (match (_62_997) with
| (x, _62_996) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _62_1001, tps, _62_1004, mutuals, datas, quals, r) -> begin
(

let ty = (FStar_Syntax_Subst.close_univ_vars uvs x.FStar_Syntax_Syntax.sort)
in (

let _62_1027 = (match ((let _163_590 = (FStar_Syntax_Subst.compress ty)
in _163_590.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _62_1018 = (FStar_Util.first_N (FStar_List.length tps) binders)
in (match (_62_1018) with
| (tps, rest) -> begin
(

let t = (match (rest) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _62_1021 -> begin
(let _163_591 = (FStar_ST.read x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) _163_591 x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos))
end)
in ((tps), (t)))
end))
end
| _62_1024 -> begin
(([]), (ty))
end)
in (match (_62_1027) with
| (tps, t) -> begin
FStar_Syntax_Syntax.Sig_inductive_typ (((tc), (uvs), (tps), (t), (mutuals), (datas), (quals), (r)))
end)))
end
| _62_1029 -> begin
(failwith "Impossible")
end)
end)) tc_types tcs)
in (

let datas = (match (uvs) with
| [] -> begin
datas
end
| _62_1033 -> begin
(

let uvs_universes = (FStar_All.pipe_right uvs (FStar_List.map (fun _163_592 -> FStar_Syntax_Syntax.U_name (_163_592))))
in (

let tc_insts = (FStar_All.pipe_right tcs (FStar_List.map (fun _62_4 -> (match (_62_4) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tc, _62_1038, _62_1040, _62_1042, _62_1044, _62_1046, _62_1048, _62_1050) -> begin
((tc), (uvs_universes))
end
| _62_1054 -> begin
(failwith "Impossible")
end))))
in (FStar_List.map2 (fun _62_1059 d -> (match (_62_1059) with
| (t, _62_1058) -> begin
(match (d) with
| FStar_Syntax_Syntax.Sig_datacon (l, _62_1063, _62_1065, tc, ntps, quals, mutuals, r) -> begin
(

let ty = (let _163_596 = (FStar_Syntax_InstFV.instantiate tc_insts t.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _163_596 (FStar_Syntax_Subst.close_univ_vars uvs)))
in FStar_Syntax_Syntax.Sig_datacon (((l), (uvs), (ty), (tc), (ntps), (quals), (mutuals), (r))))
end
| _62_1075 -> begin
(failwith "Impossible")
end)
end)) data_types datas)))
end)
in ((tcs), (datas))))
end))
end))
end)))
end))))))))
in (

let _62_1085 = (FStar_All.pipe_right ses (FStar_List.partition (fun _62_5 -> (match (_62_5) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_62_1079) -> begin
true
end
| _62_1082 -> begin
false
end))))
in (match (_62_1085) with
| (tys, datas) -> begin
(

let _62_1092 = if (FStar_All.pipe_right datas (FStar_Util.for_some (fun _62_6 -> (match (_62_6) with
| FStar_Syntax_Syntax.Sig_datacon (_62_1088) -> begin
false
end
| _62_1091 -> begin
true
end)))) then begin
(let _163_601 = (let _163_600 = (let _163_599 = (FStar_TypeChecker_Env.get_range env)
in (("Mutually defined type contains a non-inductive element"), (_163_599)))
in FStar_Errors.Error (_163_600))
in (Prims.raise _163_601))
end else begin
()
end
in (

let env0 = env
in (

let _62_1111 = (FStar_List.fold_right (fun tc _62_1099 -> (match (_62_1099) with
| (env, all_tcs, g) -> begin
(

let _62_1104 = (tc_tycon env tc)
in (match (_62_1104) with
| (env, tc, tc_u, guard) -> begin
(

let g' = (FStar_TypeChecker_Rel.universe_inequality FStar_Syntax_Syntax.U_zero tc_u)
in (

let _62_1106 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _163_604 = (FStar_Syntax_Print.sigelt_to_string tc)
in (FStar_Util.print1 "Checked inductive: %s\n" _163_604))
end else begin
()
end
in (let _163_606 = (let _163_605 = (FStar_TypeChecker_Rel.conj_guard guard g')
in (FStar_TypeChecker_Rel.conj_guard g _163_605))
in ((env), ((((tc), (tc_u)))::all_tcs), (_163_606)))))
end))
end)) tys ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (_62_1111) with
| (env, tcs, g) -> begin
(

let _62_1121 = (FStar_List.fold_right (fun se _62_1115 -> (match (_62_1115) with
| (datas, g) -> begin
(

let _62_1118 = (tc_data env tcs se)
in (match (_62_1118) with
| (data, g') -> begin
(let _163_609 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((data)::datas), (_163_609)))
end))
end)) datas (([]), (g)))
in (match (_62_1121) with
| (datas, g) -> begin
(

let _62_1124 = (let _163_610 = (FStar_List.map Prims.fst tcs)
in (generalize_and_inst_within env0 g _163_610 datas))
in (match (_62_1124) with
| (tcs, datas) -> begin
(

let sig_bndle = (let _163_612 = (let _163_611 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_163_611)))
in FStar_Syntax_Syntax.Sig_bundle (_163_612))
in (

let data_ops_ses = (let _163_613 = (FStar_List.map (FStar_TypeChecker_Util.mk_data_operations quals env tcs) datas)
in (FStar_All.pipe_right _163_613 FStar_List.flatten))
in (

let datacon_typ = (fun data -> (match (data) with
| FStar_Syntax_Syntax.Sig_datacon (_62_1130, _62_1132, t, _62_1135, _62_1137, _62_1139, _62_1141, _62_1143) -> begin
t
end
| _62_1147 -> begin
(failwith "Impossible!")
end))
in (

let dr = FStar_Range.dummyRange
in (

let optimized_haseq_scheme = (fun _62_1150 -> (

let haseq_ty = (fun usubst us acc ty -> (

let _62_1177 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _62_1159, bs, t, _62_1163, d_lids, _62_1166, _62_1168) -> begin
((lid), (bs), (t), (d_lids))
end
| _62_1172 -> begin
(failwith "Impossible!")
end)
in (match (_62_1177) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _163_626 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _163_626 t))
in (

let _62_1182 = (FStar_Syntax_Subst.open_term bs t)
in (match (_62_1182) with
| (bs, t) -> begin
(

let ibs = (match ((let _163_627 = (FStar_Syntax_Subst.compress t)
in _163_627.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _62_1185) -> begin
ibs
end
| _62_1189 -> begin
[]
end)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _163_630 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _163_629 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _163_630 _163_629)))
in (

let ind = (let _163_633 = (FStar_List.map (fun _62_1196 -> (match (_62_1196) with
| (bv, aq) -> begin
(let _163_632 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_163_632), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _163_633 None dr))
in (

let ind = (let _163_636 = (FStar_List.map (fun _62_1200 -> (match (_62_1200) with
| (bv, aq) -> begin
(let _163_635 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_163_635), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _163_636 None dr))
in (

let haseq_ind = (let _163_638 = (let _163_637 = (FStar_Syntax_Syntax.as_arg ind)
in (_163_637)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _163_638 None dr))
in (

let bs' = (FStar_List.filter (fun b -> (

let _62_1211 = acc
in (match (_62_1211) with
| (_62_1205, en, _62_1208, _62_1210) -> begin
(

let opt = (let _163_641 = (let _163_640 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _163_640))
in (FStar_TypeChecker_Rel.try_subtype' en (Prims.fst b).FStar_Syntax_Syntax.sort _163_641 false))
in (match (opt) with
| None -> begin
false
end
| Some (_62_1215) -> begin
true
end))
end))) bs)
in (

let haseq_bs = (FStar_List.fold_left (fun t b -> (let _163_647 = (let _163_646 = (let _163_645 = (let _163_644 = (FStar_Syntax_Syntax.bv_to_name (Prims.fst b))
in (FStar_Syntax_Syntax.as_arg _163_644))
in (_163_645)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _163_646 None dr))
in (FStar_Syntax_Util.mk_conj t _163_647))) FStar_Syntax_Util.t_true bs')
in (

let fml = (FStar_Syntax_Util.mk_imp haseq_bs haseq_ind)
in (

let fml = (

let _62_1222 = fml
in (let _163_653 = (let _163_652 = (let _163_651 = (let _163_650 = (let _163_649 = (let _163_648 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_163_648)::[])
in (_163_649)::[])
in FStar_Syntax_Syntax.Meta_pattern (_163_650))
in ((fml), (_163_651)))
in FStar_Syntax_Syntax.Tm_meta (_163_652))
in {FStar_Syntax_Syntax.n = _163_653; FStar_Syntax_Syntax.tk = _62_1222.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _62_1222.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _62_1222.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _163_659 = (let _163_658 = (let _163_657 = (let _163_656 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _163_656 None))
in (FStar_Syntax_Syntax.as_arg _163_657))
in (_163_658)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _163_659 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _163_665 = (let _163_664 = (let _163_663 = (let _163_662 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _163_662 None))
in (FStar_Syntax_Syntax.as_arg _163_663))
in (_163_664)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _163_665 None dr))) bs fml)
in (

let guard = (FStar_Syntax_Util.mk_conj haseq_bs fml)
in (

let _62_1236 = acc
in (match (_62_1236) with
| (l_axioms, env, guard', cond') -> begin
(

let env = (FStar_TypeChecker_Env.push_binders env bs)
in (

let env = (FStar_TypeChecker_Env.push_binders env ibs)
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (_62_1241, _62_1243, _62_1245, t_lid, _62_1248, _62_1250, _62_1252, _62_1254) -> begin
(t_lid = lid)
end
| _62_1258 -> begin
(failwith "Impossible")
end)) datas)
in (

let haseq_data = (fun data -> (

let dt = (datacon_typ data)
in (

let dt = (FStar_Syntax_Subst.subst usubst dt)
in (match ((let _163_669 = (FStar_Syntax_Subst.compress dt)
in _163_669.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _62_1266) -> begin
(

let dbs = (let _163_670 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _163_670))
in (

let dbs = (let _163_671 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _163_671 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let haseq_b = (let _163_675 = (let _163_674 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_163_674)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _163_675 None dr))
in (

let sort_range = (Prims.fst b).FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.pos
in (

let haseq_b = (let _163_677 = (let _163_676 = (FStar_Syntax_Print.term_to_string ind)
in (FStar_Util.format1 "Failed to prove that the type \'%s\' supports decidable equality because of this argument; add the \'noeq\' qualifier" _163_676))
in (FStar_TypeChecker_Util.label _163_677 sort_range haseq_b))
in (FStar_Syntax_Util.mk_conj t haseq_b))))) FStar_Syntax_Util.t_true dbs)
in (FStar_List.fold_right (fun b t -> (let _163_683 = (let _163_682 = (let _163_681 = (let _163_680 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _163_680 None))
in (FStar_Syntax_Syntax.as_arg _163_681))
in (_163_682)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _163_683 None dr))) dbs cond)))))
end
| _62_1281 -> begin
FStar_Syntax_Util.t_true
end))))
in (

let cond = (FStar_List.fold_left (fun acc d -> (let _163_686 = (haseq_data d)
in (FStar_Syntax_Util.mk_conj acc _163_686))) FStar_Syntax_Util.t_true t_datas)
in (

let axiom_lid = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (let _163_688 = (FStar_Syntax_Util.mk_conj guard' guard)
in (let _163_687 = (FStar_Syntax_Util.mk_conj cond' cond)
in (((FStar_List.append l_axioms ((((axiom_lid), (fml)))::[]))), (env), (_163_688), (_163_687))))))))))
end)))))))))))))))
end))))
end)))
in (

let us = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_62_1288, us, _62_1291, _62_1293, _62_1295, _62_1297, _62_1299, _62_1301) -> begin
us
end
| _62_1305 -> begin
(failwith "Impossible!")
end))
in (

let _62_1309 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (_62_1309) with
| (usubst, us) -> begin
(

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (

let _62_1311 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq")
in (

let _62_1313 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle)
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let _62_1320 = (FStar_List.fold_left (haseq_ty usubst us) (([]), (env), (FStar_Syntax_Util.t_true), (FStar_Syntax_Util.t_true)) tcs)
in (match (_62_1320) with
| (axioms, env, guard, cond) -> begin
(

let phi = (FStar_Syntax_Util.mk_imp guard cond)
in (

let _62_1325 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env phi)
in (match (_62_1325) with
| (phi, _62_1324) -> begin
(

let _62_1326 = if (FStar_TypeChecker_Env.should_verify env) then begin
(let _163_689 = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (phi)))
in (FStar_TypeChecker_Rel.force_trivial_guard env _163_689))
end else begin
()
end
in (

let ses = (FStar_List.fold_left (fun l _62_1331 -> (match (_62_1331) with
| (lid, fml) -> begin
(

let se = (tc_assume env lid fml [] dr)
in (FStar_List.append l ((se)::[])))
end)) [] axioms)
in (

let _62_1334 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq")
in ses)))
end)))
end))))))
end)))))
in (

let unoptimized_haseq_scheme = (fun _62_1337 -> (

let mutuals = (FStar_List.map (fun ty -> (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _62_1342, _62_1344, _62_1346, _62_1348, _62_1350, _62_1352, _62_1354) -> begin
lid
end
| _62_1358 -> begin
(failwith "Impossible!")
end)) tcs)
in (

let haseq_ty = (fun usubst us acc ty -> (

let _62_1385 = (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _62_1367, bs, t, _62_1371, d_lids, _62_1374, _62_1376) -> begin
((lid), (bs), (t), (d_lids))
end
| _62_1380 -> begin
(failwith "Impossible!")
end)
in (match (_62_1385) with
| (lid, bs, t, d_lids) -> begin
(

let bs = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let t = (let _163_703 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst _163_703 t))
in (

let _62_1390 = (FStar_Syntax_Subst.open_term bs t)
in (match (_62_1390) with
| (bs, t) -> begin
(

let ibs = (match ((let _163_704 = (FStar_Syntax_Subst.compress t)
in _163_704.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (ibs, _62_1393) -> begin
ibs
end
| _62_1397 -> begin
[]
end)
in (

let ibs = (FStar_Syntax_Subst.open_binders ibs)
in (

let ind = (let _163_707 = (FStar_Syntax_Syntax.fvar lid FStar_Syntax_Syntax.Delta_constant None)
in (let _163_706 = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst _163_707 _163_706)))
in (

let ind = (let _163_710 = (FStar_List.map (fun _62_1404 -> (match (_62_1404) with
| (bv, aq) -> begin
(let _163_709 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_163_709), (aq)))
end)) bs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _163_710 None dr))
in (

let ind = (let _163_713 = (FStar_List.map (fun _62_1408 -> (match (_62_1408) with
| (bv, aq) -> begin
(let _163_712 = (FStar_Syntax_Syntax.bv_to_name bv)
in ((_163_712), (aq)))
end)) ibs)
in (FStar_Syntax_Syntax.mk_Tm_app ind _163_713 None dr))
in (

let haseq_ind = (let _163_715 = (let _163_714 = (FStar_Syntax_Syntax.as_arg ind)
in (_163_714)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _163_715 None dr))
in (

let rec is_mutual = (fun t -> (match ((let _163_719 = (FStar_Syntax_Subst.compress t)
in _163_719.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.existsb (fun lid -> (FStar_Ident.lid_equals lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) mutuals)
end
| FStar_Syntax_Syntax.Tm_uinst (t', _62_1419) -> begin
(is_mutual t')
end
| FStar_Syntax_Syntax.Tm_refine (bv, t') -> begin
(is_mutual bv.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_app (t', args) -> begin
if (is_mutual t') then begin
true
end else begin
(let _163_721 = (FStar_List.map Prims.fst args)
in (exists_mutual _163_721))
end
end
| FStar_Syntax_Syntax.Tm_meta (t', _62_1432) -> begin
(is_mutual t')
end
| _62_1436 -> begin
false
end))
and exists_mutual = (fun _62_7 -> (match (_62_7) with
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
in (match ((let _163_727 = (FStar_Syntax_Subst.compress dt)
in _163_727.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (dbs, _62_1449) -> begin
(

let dbs = (let _163_728 = (FStar_List.splitAt (FStar_List.length bs) dbs)
in (Prims.snd _163_728))
in (

let dbs = (let _163_729 = (FStar_Syntax_Subst.opening_of_binders bs)
in (FStar_Syntax_Subst.subst_binders _163_729 dbs))
in (

let dbs = (FStar_Syntax_Subst.open_binders dbs)
in (

let cond = (FStar_List.fold_left (fun t b -> (

let sort = (Prims.fst b).FStar_Syntax_Syntax.sort
in (

let haseq_sort = (let _163_733 = (let _163_732 = (FStar_Syntax_Syntax.as_arg (Prims.fst b).FStar_Syntax_Syntax.sort)
in (_163_732)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.t_haseq _163_733 None dr))
in (

let haseq_sort = if (is_mutual sort) then begin
(FStar_Syntax_Util.mk_imp haseq_ind haseq_sort)
end else begin
haseq_sort
end
in (FStar_Syntax_Util.mk_conj t haseq_sort))))) FStar_Syntax_Util.t_true dbs)
in (

let cond = (FStar_List.fold_right (fun b t -> (let _163_739 = (let _163_738 = (let _163_737 = (let _163_736 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _163_736 None))
in (FStar_Syntax_Syntax.as_arg _163_737))
in (_163_738)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _163_739 None dr))) dbs cond)
in (FStar_Syntax_Util.mk_conj acc cond))))))
end
| _62_1465 -> begin
acc
end))))
in (

let t_datas = (FStar_List.filter (fun s -> (match (s) with
| FStar_Syntax_Syntax.Sig_datacon (_62_1468, _62_1470, _62_1472, t_lid, _62_1475, _62_1477, _62_1479, _62_1481) -> begin
(t_lid = lid)
end
| _62_1485 -> begin
(failwith "Impossible")
end)) datas)
in (

let data_cond = (FStar_List.fold_left haseq_data FStar_Syntax_Util.t_true t_datas)
in (

let fml = (FStar_Syntax_Util.mk_imp data_cond haseq_ind)
in (

let fml = (

let _62_1489 = fml
in (let _163_746 = (let _163_745 = (let _163_744 = (let _163_743 = (let _163_742 = (let _163_741 = (FStar_Syntax_Syntax.as_arg haseq_ind)
in (_163_741)::[])
in (_163_742)::[])
in FStar_Syntax_Syntax.Meta_pattern (_163_743))
in ((fml), (_163_744)))
in FStar_Syntax_Syntax.Tm_meta (_163_745))
in {FStar_Syntax_Syntax.n = _163_746; FStar_Syntax_Syntax.tk = _62_1489.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _62_1489.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _62_1489.FStar_Syntax_Syntax.vars}))
in (

let fml = (FStar_List.fold_right (fun b t -> (let _163_752 = (let _163_751 = (let _163_750 = (let _163_749 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _163_749 None))
in (FStar_Syntax_Syntax.as_arg _163_750))
in (_163_751)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _163_752 None dr))) ibs fml)
in (

let fml = (FStar_List.fold_right (fun b t -> (let _163_758 = (let _163_757 = (let _163_756 = (let _163_755 = (FStar_Syntax_Subst.close ((b)::[]) t)
in (FStar_Syntax_Util.abs (((((Prims.fst b)), (None)))::[]) _163_755 None))
in (FStar_Syntax_Syntax.as_arg _163_756))
in (_163_757)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.tforall _163_758 None dr))) bs fml)
in (FStar_Syntax_Util.mk_conj acc fml)))))))))))))))
end))))
end)))
in (

let _62_1519 = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, _62_1502, _62_1504, _62_1506, _62_1508, _62_1510, _62_1512) -> begin
((lid), (us))
end
| _62_1516 -> begin
(failwith "Impossible!")
end))
in (match (_62_1519) with
| (lid, us) -> begin
(

let _62_1522 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (_62_1522) with
| (usubst, us) -> begin
(

let fml = (FStar_List.fold_left (haseq_ty usubst us) FStar_Syntax_Util.t_true tcs)
in (

let env = (FStar_TypeChecker_Env.push_sigelt env0 sig_bndle)
in (

let _62_1525 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push "haseq")
in (

let _62_1527 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env sig_bndle)
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env us)
in (

let se = (let _163_759 = (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.id_of_text (Prims.strcat lid.FStar_Ident.ident.FStar_Ident.idText "_haseq")))::[])))
in (tc_assume env _163_759 fml [] dr))
in (

let _62_1531 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop "haseq")
in (se)::[])))))))
end))
end)))))
in (

let skip_prims_type = (fun _62_1534 -> (

let lid = (

let ty = (FStar_List.hd tcs)
in (match (ty) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, _62_1539, _62_1541, _62_1543, _62_1545, _62_1547, _62_1549, _62_1551) -> begin
lid
end
| _62_1555 -> begin
(failwith "Impossible")
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
in (let _163_768 = (let _163_767 = (let _163_766 = (let _163_765 = (FStar_TypeChecker_Env.get_range env0)
in (((FStar_List.append tcs datas)), (quals), (lids), (_163_765)))
in FStar_Syntax_Syntax.Sig_bundle (_163_766))
in (_163_767)::ses)
in ((_163_768), (data_ops_ses)))))
end))))))))
end))
end))
end))))
end)))))))))
and tc_decl : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env se -> (

let env = (set_hint_correlator env se)
in (

let _62_1567 = (FStar_TypeChecker_Util.check_sigelt_quals env se)
in (match (se) with
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(failwith "Impossible bare data-constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) when (FStar_All.pipe_right lids (FStar_Util.for_some (FStar_Ident.lid_equals FStar_Syntax_Const.lex_t_lid))) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let se = (tc_lex_t env ses quals lids)
in (let _163_771 = (FStar_TypeChecker_Env.push_sigelt env se)
in (((se)::[]), (_163_771), ([])))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, lids, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _62_1592 = (tc_inductive env ses quals lids)
in (match (_62_1592) with
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
(Prims.raise (FStar_Errors.Error ((("Failed to process pragma: use \'fstar --help\' to see which options are available"), (r)))))
end
| FStar_Getopt.Error (s) -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Failed to process pragma: " s)), (r)))))
end))
in (match (p) with
| FStar_Syntax_Syntax.SetOptions (o) -> begin
(

let _62_1609 = (set_options FStar_Options.Set o)
in (((se)::[]), (env), ([])))
end
| FStar_Syntax_Syntax.ResetOptions (sopt) -> begin
(

let _62_1613 = (let _163_778 = (FStar_Options.restore_cmd_line_options false)
in (FStar_All.pipe_right _163_778 Prims.ignore))
in (

let _62_1618 = (match (sopt) with
| None -> begin
()
end
| Some (s) -> begin
(set_options FStar_Options.Reset s)
end)
in (

let _62_1620 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (((se)::[]), (env), ([])))))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_62_1623) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Sig_new_effect (ne, r) -> begin
(

let ne = (tc_eff_decl env ne)
in (

let se = FStar_Syntax_Syntax.Sig_new_effect (((ne), (r)))
in (

let env = (FStar_TypeChecker_Env.push_sigelt env se)
in (

let _62_1639 = (FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun _62_1634 a -> (match (_62_1634) with
| (env, ses) -> begin
(

let se_let = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a)
in (let _163_781 = (FStar_TypeChecker_Env.push_sigelt env se_let)
in ((_163_781), ((se_let)::ses))))
end)) ((env), ((se)::[]))))
in (match (_62_1639) with
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

let _62_1648 = (let _163_782 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _163_782))
in (match (_62_1648) with
| (a, wp_a_src) -> begin
(

let _62_1651 = (let _163_783 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.target)
in (monad_signature env sub.FStar_Syntax_Syntax.target _163_783))
in (match (_62_1651) with
| (b, wp_b_tgt) -> begin
(

let wp_a_tgt = (let _163_787 = (let _163_786 = (let _163_785 = (let _163_784 = (FStar_Syntax_Syntax.bv_to_name a)
in ((b), (_163_784)))
in FStar_Syntax_Syntax.NT (_163_785))
in (_163_786)::[])
in (FStar_Syntax_Subst.subst _163_787 wp_b_tgt))
in (

let expected_k = (let _163_792 = (let _163_790 = (FStar_Syntax_Syntax.mk_binder a)
in (let _163_789 = (let _163_788 = (FStar_Syntax_Syntax.null_binder wp_a_src)
in (_163_788)::[])
in (_163_790)::_163_789))
in (let _163_791 = (FStar_Syntax_Syntax.mk_Total wp_a_tgt)
in (FStar_Syntax_Util.arrow _163_792 _163_791)))
in (

let repr_type = (fun eff_name a wp -> (

let no_reify = (fun l -> (let _163_804 = (let _163_803 = (let _163_802 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _163_801 = (FStar_TypeChecker_Env.get_range env)
in ((_163_802), (_163_801))))
in FStar_Errors.Error (_163_803))
in (Prims.raise _163_804)))
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
(let _163_811 = (let _163_809 = (let _163_808 = (let _163_807 = (FStar_Syntax_Syntax.as_arg a)
in (let _163_806 = (let _163_805 = (FStar_Syntax_Syntax.as_arg wp)
in (_163_805)::[])
in (_163_807)::_163_806))
in ((repr), (_163_808)))
in FStar_Syntax_Syntax.Tm_app (_163_809))
in (let _163_810 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _163_811 None _163_810)))
end)
end)))
in (

let _62_1692 = (match (((sub.FStar_Syntax_Syntax.lift), (sub.FStar_Syntax_Syntax.lift_wp))) with
| (None, None) -> begin
(failwith "Impossible")
end
| (lift, Some (_62_1669, lift_wp)) -> begin
(let _163_812 = (check_and_gen env lift_wp expected_k)
in ((lift), (_163_812)))
end
| (Some (what, lift), None) -> begin
(

let dmff_env = (FStar_TypeChecker_DMFF.empty env (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange))
in (

let _62_1685 = (FStar_TypeChecker_DMFF.star_expr dmff_env lift)
in (match (_62_1685) with
| (_62_1682, lift_wp, lift_elab) -> begin
(

let _62_1686 = (recheck_debug "lift-wp" env lift_wp)
in (

let _62_1688 = (recheck_debug "lift-elab" env lift_elab)
in ((Some ((([]), (lift_elab)))), ((([]), (lift_wp))))))
end)))
end)
in (match (_62_1692) with
| (lift, lift_wp) -> begin
(

let lax = env.FStar_TypeChecker_Env.lax
in (

let env = (

let _62_1694 = env
in {FStar_TypeChecker_Env.solver = _62_1694.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _62_1694.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _62_1694.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _62_1694.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _62_1694.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _62_1694.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _62_1694.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _62_1694.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _62_1694.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _62_1694.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _62_1694.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _62_1694.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _62_1694.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _62_1694.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _62_1694.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _62_1694.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _62_1694.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _62_1694.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _62_1694.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _62_1694.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _62_1694.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _62_1694.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _62_1694.FStar_TypeChecker_Env.qname_and_index})
in (

let lift = (match (lift) with
| None -> begin
None
end
| Some (_62_1699, lift) -> begin
(

let _62_1705 = (let _163_813 = (FStar_TypeChecker_Env.lookup_effect_lid env sub.FStar_Syntax_Syntax.source)
in (monad_signature env sub.FStar_Syntax_Syntax.source _163_813))
in (match (_62_1705) with
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

let lift_wp_a = (let _163_820 = (let _163_818 = (let _163_817 = (let _163_816 = (FStar_Syntax_Syntax.as_arg a_typ)
in (let _163_815 = (let _163_814 = (FStar_Syntax_Syntax.as_arg wp_a_typ)
in (_163_814)::[])
in (_163_816)::_163_815))
in ((lift_wp), (_163_817)))
in FStar_Syntax_Syntax.Tm_app (_163_818))
in (let _163_819 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _163_820 None _163_819)))
in (repr_type sub.FStar_Syntax_Syntax.target a_typ lift_wp_a)))
in (

let expected_k = (let _163_827 = (let _163_825 = (FStar_Syntax_Syntax.mk_binder a)
in (let _163_824 = (let _163_823 = (FStar_Syntax_Syntax.mk_binder wp_a)
in (let _163_822 = (let _163_821 = (FStar_Syntax_Syntax.null_binder repr_f)
in (_163_821)::[])
in (_163_823)::_163_822))
in (_163_825)::_163_824))
in (let _163_826 = (FStar_Syntax_Syntax.mk_Total repr_result)
in (FStar_Syntax_Util.arrow _163_827 _163_826)))
in (

let _62_1719 = (FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env expected_k)
in (match (_62_1719) with
| (expected_k, _62_1716, _62_1718) -> begin
(

let lift = (check_and_gen env lift expected_k)
in Some (lift))
end))))))))
end))
end)
in (

let env = (

let _62_1722 = env
in {FStar_TypeChecker_Env.solver = _62_1722.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _62_1722.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _62_1722.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _62_1722.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _62_1722.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _62_1722.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _62_1722.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _62_1722.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _62_1722.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _62_1722.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _62_1722.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _62_1722.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _62_1722.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _62_1722.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _62_1722.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _62_1722.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _62_1722.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _62_1722.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = lax; FStar_TypeChecker_Env.lax_universes = _62_1722.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _62_1722.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _62_1722.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _62_1722.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _62_1722.FStar_TypeChecker_Env.qname_and_index})
in (

let sub = (

let _62_1725 = sub
in {FStar_Syntax_Syntax.source = _62_1725.FStar_Syntax_Syntax.source; FStar_Syntax_Syntax.target = _62_1725.FStar_Syntax_Syntax.target; FStar_Syntax_Syntax.lift_wp = Some (lift_wp); FStar_Syntax_Syntax.lift = lift})
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

let _62_1739 = ()
in (

let env0 = env
in (

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _62_1745 = (FStar_Syntax_Subst.open_comp tps c)
in (match (_62_1745) with
| (tps, c) -> begin
(

let _62_1749 = (tc_tparams env tps)
in (match (_62_1749) with
| (tps, env, us) -> begin
(

let _62_1753 = (FStar_TypeChecker_TcTerm.tc_comp env c)
in (match (_62_1753) with
| (c, u, g) -> begin
(

let _62_1754 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (

let tps = (FStar_Syntax_Subst.close_binders tps)
in (

let c = (FStar_Syntax_Subst.close_comp tps c)
in (

let _62_1760 = (let _163_828 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) None r)
in (FStar_TypeChecker_Util.generalize_universes env0 _163_828))
in (match (_62_1760) with
| (uvs, t) -> begin
(

let _62_1779 = (match ((let _163_830 = (let _163_829 = (FStar_Syntax_Subst.compress t)
in _163_829.FStar_Syntax_Syntax.n)
in ((tps), (_163_830)))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (_62_1763, c)) -> begin
(([]), (c))
end
| (_62_1769, FStar_Syntax_Syntax.Tm_arrow (tps, c)) -> begin
((tps), (c))
end
| _62_1776 -> begin
(failwith "Impossible")
end)
in (match (_62_1779) with
| (tps, c) -> begin
(

let _62_1784 = if (((FStar_List.length uvs) <> (Prims.parse_int "1")) && (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.effect_Lemma_lid)))) then begin
(

let _62_1783 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_62_1783) with
| (_62_1781, t) -> begin
(let _163_836 = (let _163_835 = (let _163_834 = (let _163_833 = (FStar_Syntax_Print.lid_to_string lid)
in (let _163_832 = (FStar_All.pipe_right (FStar_List.length uvs) FStar_Util.string_of_int)
in (let _163_831 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)" _163_833 _163_832 _163_831))))
in ((_163_834), (r)))
in FStar_Errors.Error (_163_835))
in (Prims.raise _163_836))
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
| (FStar_Syntax_Syntax.Sig_declare_typ (_, _, _, quals, _)) | (FStar_Syntax_Syntax.Sig_let (_, _, _, quals, _)) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _62_8 -> (match (_62_8) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| _62_1812 -> begin
false
end)))) -> begin
(([]), (env), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t, quals, r) -> begin
(

let env = (FStar_TypeChecker_Env.set_range env r)
in (

let _62_1826 = if (uvs = []) then begin
(let _163_839 = (let _163_838 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _163_838))
in (check_and_gen env t _163_839))
end else begin
(

let _62_1823 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (_62_1823) with
| (uvs, t) -> begin
(let _163_843 = (let _163_842 = (let _163_841 = (let _163_840 = (FStar_Syntax_Util.type_u ())
in (Prims.fst _163_840))
in (tc_check_trivial_guard env t _163_841))
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) _163_842))
in ((uvs), (_163_843)))
end))
end
in (match (_62_1826) with
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

let _62_1846 = (FStar_TypeChecker_TcTerm.tc_term env e)
in (match (_62_1846) with
| (e, c, g1) -> begin
(

let _62_1851 = (let _163_847 = (let _163_844 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit r)
in Some (_163_844))
in (let _163_846 = (let _163_845 = (c.FStar_Syntax_Syntax.comp ())
in ((e), (_163_845)))
in (FStar_TypeChecker_TcTerm.check_expected_effect env _163_847 _163_846)))
in (match (_62_1851) with
| (e, _62_1849, g) -> begin
(

let _62_1852 = (let _163_848 = (FStar_TypeChecker_Rel.conj_guard g1 g)
in (FStar_TypeChecker_Rel.force_trivial_guard env _163_848))
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
(let _163_860 = (let _163_859 = (let _163_858 = (let _163_857 = (FStar_Syntax_Print.lid_to_string l)
in (let _163_856 = (FStar_Syntax_Print.quals_to_string q)
in (let _163_855 = (FStar_Syntax_Print.quals_to_string q')
in (FStar_Util.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}" _163_857 _163_856 _163_855))))
in ((_163_858), (r)))
in FStar_Errors.Error (_163_859))
in (Prims.raise _163_860))
end
end))
in (

let _62_1899 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.fold_left (fun _62_1874 lb -> (match (_62_1874) with
| (gen, lbs, quals_opt) -> begin
(

let lbname = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _62_1895 = (match ((FStar_TypeChecker_Env.try_lookup_val_decl env lbname.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
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

let _62_1888 = (match (lb.FStar_Syntax_Syntax.lbtyp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
()
end
| _62_1887 -> begin
(FStar_Errors.warn r "Annotation from val declaration overrides inline type annotation")
end)
in (

let _62_1890 = if ((lb.FStar_Syntax_Syntax.lbunivs <> []) && ((FStar_List.length lb.FStar_Syntax_Syntax.lbunivs) <> (FStar_List.length uvs))) then begin
(Prims.raise (FStar_Errors.Error ((("Inline universes are incoherent with annotation from val declaration"), (r)))))
end else begin
()
end
in (let _163_863 = (FStar_Syntax_Syntax.mk_lb ((FStar_Util.Inr (lbname)), (uvs), (FStar_Syntax_Const.effect_ALL_lid), (tval), (lb.FStar_Syntax_Syntax.lbdef)))
in ((false), (_163_863), (quals_opt))))))
end)
in (match (_62_1895) with
| (gen, lb, quals_opt) -> begin
((gen), ((lb)::lbs), (quals_opt))
end)))
end)) ((true), ([]), (if (quals = []) then begin
None
end else begin
Some (quals)
end))))
in (match (_62_1899) with
| (should_generalize, lbs', quals_opt) -> begin
(

let quals = (match (quals_opt) with
| None -> begin
(FStar_Syntax_Syntax.Visible_default)::[]
end
| Some (q) -> begin
if (FStar_All.pipe_right q (FStar_Util.for_some (fun _62_9 -> (match (_62_9) with
| (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Visible_default) | (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> begin
true
end
| _62_1908 -> begin
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

let e = (let _163_867 = (let _163_866 = (let _163_865 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) None r)
in (((((Prims.fst lbs)), (lbs'))), (_163_865)))
in FStar_Syntax_Syntax.Tm_let (_163_866))
in (FStar_Syntax_Syntax.mk _163_867 None r))
in (

let _62_1942 = (match ((FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term (

let _62_1912 = env
in {FStar_TypeChecker_Env.solver = _62_1912.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _62_1912.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _62_1912.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _62_1912.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _62_1912.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _62_1912.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _62_1912.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _62_1912.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _62_1912.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _62_1912.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _62_1912.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = should_generalize; FStar_TypeChecker_Env.letrecs = _62_1912.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _62_1912.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _62_1912.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _62_1912.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _62_1912.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _62_1912.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _62_1912.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _62_1912.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _62_1912.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _62_1912.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _62_1912.FStar_TypeChecker_Env.qname_and_index}) e)) with
| ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let (lbs, e); FStar_Syntax_Syntax.tk = _62_1919; FStar_Syntax_Syntax.pos = _62_1917; FStar_Syntax_Syntax.vars = _62_1915}, _62_1926, g) when (FStar_TypeChecker_Rel.is_trivial g) -> begin
(

let quals = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (_62_1930, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect)) -> begin
(FStar_Syntax_Syntax.HasMaskedEffect)::quals
end
| _62_1936 -> begin
quals
end)
in ((FStar_Syntax_Syntax.Sig_let (((lbs), (r), (lids), (quals), (attrs)))), (lbs)))
end
| _62_1939 -> begin
(failwith "impossible")
end)
in (match (_62_1942) with
| (se, lbs) -> begin
(

let _62_1948 = if (log env) then begin
(let _163_875 = (let _163_874 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let should_log = (match ((let _163_871 = (let _163_870 = (let _163_869 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _163_869.FStar_Syntax_Syntax.fv_name)
in _163_870.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.try_lookup_val_decl env _163_871))) with
| None -> begin
true
end
| _62_1946 -> begin
false
end)
in if should_log then begin
(let _163_873 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _163_872 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_Util.format2 "let %s : %s" _163_873 _163_872)))
end else begin
""
end))))
in (FStar_All.pipe_right _163_874 (FStar_String.concat "\n")))
in (FStar_Util.print1 "%s\n" _163_875))
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

let is_abstract = (fun quals -> (FStar_All.pipe_right quals (FStar_Util.for_some (fun _62_10 -> (match (_62_10) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| _62_1958 -> begin
false
end)))))
in (

let is_hidden_proj_or_disc = (fun q -> (match (q) with
| (FStar_Syntax_Syntax.Projector (l, _)) | (FStar_Syntax_Syntax.Discriminator (l)) -> begin
(FStar_All.pipe_right hidden (FStar_Util.for_some (FStar_Ident.lid_equals l)))
end
| _62_1968 -> begin
false
end))
in (match (se) with
| FStar_Syntax_Syntax.Sig_pragma (_62_1970) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _62_1981, r) -> begin
if (is_abstract quals) then begin
(FStar_List.fold_right (fun se _62_1988 -> (match (_62_1988) with
| (out, hidden) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, us, bs, t, _62_1994, _62_1996, quals, r) -> begin
(

let dec = (let _163_889 = (let _163_888 = (let _163_887 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow bs _163_887))
in ((l), (us), (_163_888), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (_163_889))
in (((dec)::out), (hidden)))
end
| FStar_Syntax_Syntax.Sig_datacon (l, us, t, _62_2006, _62_2008, _62_2010, _62_2012, r) -> begin
(

let dec = FStar_Syntax_Syntax.Sig_declare_typ (((l), (us), (t), ((FStar_Syntax_Syntax.Assumption)::[]), (r)))
in (((dec)::out), ((l)::hidden)))
end
| _62_2018 -> begin
((out), (hidden))
end)
end)) ses (([]), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end
| FStar_Syntax_Syntax.Sig_assume (_62_2020, _62_2022, quals, _62_2025) -> begin
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
if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _62_11 -> (match (_62_11) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _62_2044 -> begin
false
end)))) then begin
(((se)::[]), (hidden))
end else begin
(([]), (hidden))
end
end
end
| FStar_Syntax_Syntax.Sig_main (_62_2046) -> begin
(([]), (hidden))
end
| (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) -> begin
(((se)::[]), (hidden))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _62_2065, _62_2067, quals, _62_2070) when (FStar_All.pipe_right quals (FStar_Util.for_some is_hidden_proj_or_disc)) -> begin
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
| FStar_Syntax_Syntax.Sig_let (lbs, r, l, quals, _62_2081) -> begin
if (is_abstract quals) then begin
(let _163_896 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (let _163_895 = (let _163_894 = (let _163_893 = (let _163_892 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _163_892.FStar_Syntax_Syntax.fv_name)
in _163_893.FStar_Syntax_Syntax.v)
in ((_163_894), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), ((FStar_Syntax_Syntax.Assumption)::quals), (r)))
in FStar_Syntax_Syntax.Sig_declare_typ (_163_895)))))
in ((_163_896), (hidden)))
end else begin
(((se)::[]), (hidden))
end
end))))


let tc_decls : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env ses -> (

let rec process_one_decl = (fun _62_2092 se -> (match (_62_2092) with
| (ses, exports, env, hidden) -> begin
(

let _62_2094 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _163_905 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 ">>>>>>>>>>>>>>Checking top-level decl %s\n" _163_905))
end else begin
()
end
in (

let _62_2099 = (tc_decl env se)
in (match (_62_2099) with
| (ses', env, ses_elaborated) -> begin
(

let _62_2102 = if ((FStar_Options.log_types ()) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("LogTypes")))) then begin
(let _163_910 = (FStar_List.fold_left (fun s se -> (let _163_909 = (let _163_908 = (FStar_Syntax_Print.sigelt_to_string se)
in (Prims.strcat _163_908 "\n"))
in (Prims.strcat s _163_909))) "" ses')
in (FStar_Util.print1 "Checked: %s\n" _163_910))
end else begin
()
end
in (

let _62_2105 = (FStar_List.iter (fun se -> (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_sig env se)) ses')
in (

let _62_2114 = (FStar_List.fold_left (fun _62_2109 se -> (match (_62_2109) with
| (le, lh) -> begin
(

let tup = (for_export hidden se)
in (((FStar_List.rev_append (Prims.fst tup) le)), ((FStar_List.rev_append (Prims.snd tup) lh))))
end)) (([]), ([])) ses')
in (match (_62_2114) with
| (exported, hidden) -> begin
(FStar_List.fold_left process_one_decl (((FStar_List.rev_append ses' ses)), (((FStar_List.rev_append exported []))::exports), (env), (hidden)) ses_elaborated)
end))))
end)))
end))
in (

let _62_2144 = (FStar_List.fold_left (fun acc se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ne, r) -> begin
(

let _62_2128 = acc
in (match (_62_2128) with
| (_62_2122, _62_2124, env, _62_2127) -> begin
(

let _62_2132 = (cps_and_elaborate env ne)
in (match (_62_2132) with
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
| _62_2138 -> begin
(process_one_decl acc se)
end)) (([]), ([]), (env), ([])) ses)
in (match (_62_2144) with
| (ses, exports, env, _62_2143) -> begin
(let _163_916 = (FStar_All.pipe_right (FStar_List.rev_append exports []) FStar_List.flatten)
in (((FStar_List.rev_append ses [])), (_163_916), (env)))
end))))


let tc_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul -> (

let verify = (FStar_Options.should_verify modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let action = if verify then begin
"Verifying"
end else begin
"Lax-checking"
end
in (

let label = if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"implementation"
end
in (

let _62_2150 = if (FStar_Options.debug_any ()) then begin
(FStar_Util.print3 "%s %s of %s\n" action label modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
end else begin
()
end
in (

let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let msg = (Prims.strcat "Internals for " name)
in (

let env = (

let _62_2154 = env
in {FStar_TypeChecker_Env.solver = _62_2154.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _62_2154.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _62_2154.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _62_2154.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _62_2154.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _62_2154.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _62_2154.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _62_2154.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _62_2154.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _62_2154.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _62_2154.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _62_2154.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _62_2154.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _62_2154.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _62_2154.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _62_2154.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = modul.FStar_Syntax_Syntax.is_interface; FStar_TypeChecker_Env.admit = (not (verify)); FStar_TypeChecker_Env.lax = _62_2154.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _62_2154.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _62_2154.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _62_2154.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _62_2154.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _62_2154.FStar_TypeChecker_Env.qname_and_index})
in (

let _62_2157 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.push msg)
in (

let env = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (

let _62_2163 = (tc_decls env modul.FStar_Syntax_Syntax.declarations)
in (match (_62_2163) with
| (ses, exports, env) -> begin
(((

let _62_2164 = modul
in {FStar_Syntax_Syntax.name = _62_2164.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = ses; FStar_Syntax_Syntax.exports = _62_2164.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _62_2164.FStar_Syntax_Syntax.is_interface})), (exports), (env))
end))))))))))))


let tc_more_partial_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env) = (fun env modul decls -> (

let _62_2172 = (tc_decls env decls)
in (match (_62_2172) with
| (ses, exports, env) -> begin
(

let modul = (

let _62_2173 = modul
in {FStar_Syntax_Syntax.name = _62_2173.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = (FStar_List.append modul.FStar_Syntax_Syntax.declarations ses); FStar_Syntax_Syntax.exports = _62_2173.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _62_2173.FStar_Syntax_Syntax.is_interface})
in ((modul), (exports), (env)))
end)))


let check_exports : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env modul exports -> (

let env = (

let _62_2179 = env
in {FStar_TypeChecker_Env.solver = _62_2179.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _62_2179.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _62_2179.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _62_2179.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _62_2179.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _62_2179.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _62_2179.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _62_2179.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _62_2179.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _62_2179.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _62_2179.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _62_2179.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _62_2179.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = true; FStar_TypeChecker_Env.check_uvars = _62_2179.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _62_2179.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _62_2179.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _62_2179.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = true; FStar_TypeChecker_Env.type_of = _62_2179.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _62_2179.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _62_2179.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _62_2179.FStar_TypeChecker_Env.qname_and_index})
in (

let check_term = (fun lid univs t -> (

let _62_2188 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (_62_2188) with
| (univs, t) -> begin
(

let _62_2190 = if (let _163_940 = (let _163_939 = (FStar_TypeChecker_Env.set_current_module env modul.FStar_Syntax_Syntax.name)
in (FStar_TypeChecker_Env.debug _163_939))
in (FStar_All.pipe_left _163_940 (FStar_Options.Other ("Exports")))) then begin
(let _163_945 = (FStar_Syntax_Print.lid_to_string lid)
in (let _163_944 = (let _163_942 = (FStar_All.pipe_right univs (FStar_List.map (fun x -> (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (x))))))
in (FStar_All.pipe_right _163_942 (FStar_String.concat ", ")))
in (let _163_943 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print3 "Checking for export %s <%s> : %s\n" _163_945 _163_944 _163_943))))
end else begin
()
end
in (

let env = (FStar_TypeChecker_Env.push_univ_vars env univs)
in (let _163_946 = (FStar_TypeChecker_TcTerm.tc_trivial_guard env t)
in (FStar_All.pipe_right _163_946 Prims.ignore))))
end)))
in (

let check_term = (fun lid univs t -> (

let _62_2197 = (let _163_955 = (let _163_954 = (FStar_Syntax_Print.lid_to_string modul.FStar_Syntax_Syntax.name)
in (let _163_953 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Interface of %s violates its abstraction (add a \'private\' qualifier to \'%s\'?)" _163_954 _163_953)))
in (FStar_Errors.message_prefix.FStar_Errors.set_prefix _163_955))
in (

let _62_2199 = (check_term lid univs t)
in (FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()))))
in (

let rec check_sigelt = (fun _62_12 -> (match (_62_12) with
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _62_2206, _62_2208) -> begin
if (not ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private)))) then begin
(FStar_All.pipe_right ses (FStar_List.iter check_sigelt))
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_inductive_typ (l, univs, binders, typ, _62_2216, _62_2218, _62_2220, r) -> begin
(

let t = (let _163_960 = (let _163_959 = (let _163_958 = (FStar_Syntax_Syntax.mk_Total typ)
in ((binders), (_163_958)))
in FStar_Syntax_Syntax.Tm_arrow (_163_959))
in (FStar_Syntax_Syntax.mk _163_960 None r))
in (check_term l univs t))
end
| FStar_Syntax_Syntax.Sig_datacon (l, univs, t, _62_2229, _62_2231, _62_2233, _62_2235, _62_2237) -> begin
(check_term l univs t)
end
| FStar_Syntax_Syntax.Sig_declare_typ (l, univs, t, quals, _62_2245) -> begin
if (not ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Private)))) then begin
(check_term l univs t)
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_let ((_62_2249, lbs), _62_2253, _62_2255, quals, _62_2258) -> begin
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

let _62_2294 = modul
in {FStar_Syntax_Syntax.name = _62_2294.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _62_2294.FStar_Syntax_Syntax.declarations; FStar_Syntax_Syntax.exports = exports; FStar_Syntax_Syntax.is_interface = modul.FStar_Syntax_Syntax.is_interface})
in (

let env = (FStar_TypeChecker_Env.finish_module env modul)
in (

let _62_2298 = if (not ((FStar_Options.lax ()))) then begin
(check_exports env modul exports)
end else begin
()
end
in (

let _62_2300 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.pop (Prims.strcat "Ending modul " modul.FStar_Syntax_Syntax.name.FStar_Ident.str))
in (

let _62_2302 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.encode_modul env modul)
in (

let _62_2304 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
in (

let _62_2306 = if (not ((FStar_Options.interactive ()))) then begin
(let _163_968 = (FStar_Options.restore_cmd_line_options true)
in (FStar_All.pipe_right _163_968 Prims.ignore))
end else begin
()
end
in ((modul), (env))))))))))


let tc_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env modul -> (

let _62_2313 = (tc_partial_modul env modul)
in (match (_62_2313) with
| (modul, non_private_decls, env) -> begin
(finish_partial_modul env modul non_private_decls)
end)))


let check_module : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env) = (fun env m -> (

let _62_2316 = if (FStar_Options.debug_any ()) then begin
(let _163_977 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print2 "Checking %s: %s\n" (if m.FStar_Syntax_Syntax.is_interface then begin
"i\'face"
end else begin
"module"
end) _163_977))
end else begin
()
end
in (

let env = (

let _62_2318 = env
in (let _163_978 = (not ((FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str)))
in {FStar_TypeChecker_Env.solver = _62_2318.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _62_2318.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _62_2318.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _62_2318.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _62_2318.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _62_2318.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _62_2318.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _62_2318.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _62_2318.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _62_2318.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _62_2318.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _62_2318.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _62_2318.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _62_2318.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _62_2318.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _62_2318.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _62_2318.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _62_2318.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _163_978; FStar_TypeChecker_Env.lax_universes = _62_2318.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _62_2318.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _62_2318.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _62_2318.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _62_2318.FStar_TypeChecker_Env.qname_and_index}))
in (

let _62_2323 = (tc_modul env m)
in (match (_62_2323) with
| (m, env) -> begin
(

let _62_2324 = if (FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _163_979 = (FStar_Syntax_Print.modul_to_string m)
in (FStar_Util.print1 "%s\n" _163_979))
end else begin
()
end
in (

let _62_2349 = if ((FStar_Options.dump_module m.FStar_Syntax_Syntax.name.FStar_Ident.str) && (FStar_Options.debug_at_level m.FStar_Syntax_Syntax.name.FStar_Ident.str (FStar_Options.Other ("Normalize")))) then begin
(

let normalize_toplevel_lets = (fun _62_13 -> (match (_62_13) with
| FStar_Syntax_Syntax.Sig_let ((b, lbs), r, ids, qs, attrs) -> begin
(

let n = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]))
in (

let update = (fun lb -> (

let _62_2341 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbdef)
in (match (_62_2341) with
| (univnames, e) -> begin
(

let _62_2342 = lb
in (let _163_987 = (let _163_986 = (FStar_TypeChecker_Env.push_univ_vars env univnames)
in (n _163_986 e))
in {FStar_Syntax_Syntax.lbname = _62_2342.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _62_2342.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _62_2342.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _62_2342.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _163_987}))
end)))
in (let _163_990 = (let _163_989 = (let _163_988 = (FStar_List.map update lbs)
in ((b), (_163_988)))
in ((_163_989), (r), (ids), (qs), (attrs)))
in FStar_Syntax_Syntax.Sig_let (_163_990))))
end
| se -> begin
se
end))
in (

let normalized_module = (

let _62_2346 = m
in (let _163_991 = (FStar_List.map normalize_toplevel_lets m.FStar_Syntax_Syntax.declarations)
in {FStar_Syntax_Syntax.name = _62_2346.FStar_Syntax_Syntax.name; FStar_Syntax_Syntax.declarations = _163_991; FStar_Syntax_Syntax.exports = _62_2346.FStar_Syntax_Syntax.exports; FStar_Syntax_Syntax.is_interface = _62_2346.FStar_Syntax_Syntax.is_interface}))
in (let _163_992 = (FStar_Syntax_Print.modul_to_string normalized_module)
in (FStar_Util.print1 "%s\n" _163_992))))
end else begin
()
end
in ((m), (env))))
end)))))




