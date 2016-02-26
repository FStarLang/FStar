
open Prims
# 31 "FStar.TypeChecker.Util.fst"
type lcomp_with_binder =
(FStar_Syntax_Syntax.bv Prims.option * FStar_Syntax_Syntax.lcomp)

# 77 "FStar.TypeChecker.Util.fst"
let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _152_6 = (FStar_TypeChecker_Env.get_range env)
in (let _152_5 = (FStar_TypeChecker_Errors.failed_to_prove_specification errs)
in (FStar_TypeChecker_Errors.report _152_6 _152_5))))

# 84 "FStar.TypeChecker.Util.fst"
let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _152_9 = (FStar_Syntax_Subst.compress t)
in _152_9.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_70_12) -> begin
true
end
| _70_15 -> begin
false
end))

# 88 "FStar.TypeChecker.Util.fst"
let t_binders : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env -> (let _152_13 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right _152_13 (FStar_List.filter (fun _70_20 -> (match (_70_20) with
| (x, _70_19) -> begin
(is_type x.FStar_Syntax_Syntax.sort)
end))))))

# 92 "FStar.TypeChecker.Util.fst"
let new_uvar_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun env k -> (
# 93 "FStar.TypeChecker.Util.fst"
let bs = if (FStar_ST.read FStar_Options.full_context_dependency) then begin
(FStar_TypeChecker_Env.all_binders env)
end else begin
(t_binders env)
end
in (let _152_18 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Rel.new_uvar _152_18 bs k))))

# 98 "FStar.TypeChecker.Util.fst"
let new_uvar : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env k -> (let _152_23 = (new_uvar_aux env k)
in (Prims.fst _152_23)))

# 100 "FStar.TypeChecker.Util.fst"
let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun _70_1 -> (match (_70_1) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, _70_35); FStar_Syntax_Syntax.tk = _70_32; FStar_Syntax_Syntax.pos = _70_30; FStar_Syntax_Syntax.vars = _70_28} -> begin
uv
end
| _70_40 -> begin
(FStar_All.failwith "Impossible")
end))

# 104 "FStar.TypeChecker.Util.fst"
let new_implicit_var : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.uvar * FStar_Range.range) * FStar_TypeChecker_Env.guard_t) = (fun env k -> (
# 105 "FStar.TypeChecker.Util.fst"
let _70_45 = (new_uvar_aux env k)
in (match (_70_45) with
| (t, u) -> begin
(
# 106 "FStar.TypeChecker.Util.fst"
let g = (
# 106 "FStar.TypeChecker.Util.fst"
let _70_46 = FStar_TypeChecker_Rel.trivial_guard
in (let _152_32 = (let _152_31 = (let _152_30 = (as_uvar u)
in (env, _152_30, t, k, u.FStar_Syntax_Syntax.pos))
in (_152_31)::[])
in {FStar_TypeChecker_Env.guard_f = _70_46.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _70_46.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _70_46.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _152_32}))
in (let _152_34 = (let _152_33 = (as_uvar u)
in (_152_33, u.FStar_Syntax_Syntax.pos))
in (t, _152_34, g)))
end)))

# 109 "FStar.TypeChecker.Util.fst"
let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun r t -> (
# 110 "FStar.TypeChecker.Util.fst"
let uvs = (FStar_Syntax_Free.uvars t)
in if (not ((FStar_Util.set_is_empty uvs))) then begin
(
# 113 "FStar.TypeChecker.Util.fst"
let us = (let _152_41 = (let _152_40 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun _70_55 -> (match (_70_55) with
| (x, _70_54) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) _152_40))
in (FStar_All.pipe_right _152_41 (FStar_String.concat ", ")))
in (
# 115 "FStar.TypeChecker.Util.fst"
let hide_uvar_nums_saved = (FStar_ST.read FStar_Options.hide_uvar_nums)
in (
# 116 "FStar.TypeChecker.Util.fst"
let print_implicits_saved = (FStar_ST.read FStar_Options.print_implicits)
in (
# 117 "FStar.TypeChecker.Util.fst"
let _70_59 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums false)
in (
# 118 "FStar.TypeChecker.Util.fst"
let _70_61 = (FStar_ST.op_Colon_Equals FStar_Options.print_implicits true)
in (
# 119 "FStar.TypeChecker.Util.fst"
let _70_63 = (let _152_43 = (let _152_42 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us _152_42))
in (FStar_TypeChecker_Errors.report r _152_43))
in (
# 122 "FStar.TypeChecker.Util.fst"
let _70_65 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums hide_uvar_nums_saved)
in (FStar_ST.op_Colon_Equals FStar_Options.print_implicits print_implicits_saved))))))))
end else begin
()
end))

# 129 "FStar.TypeChecker.Util.fst"
let force_sort' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' = (fun s -> (match ((FStar_ST.read s.FStar_Syntax_Syntax.tk)) with
| None -> begin
(let _152_48 = (let _152_47 = (FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos)
in (let _152_46 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s" _152_47 _152_46)))
in (FStar_All.failwith _152_48))
end
| Some (tk) -> begin
tk
end))

# 133 "FStar.TypeChecker.Util.fst"
let force_sort = (fun s -> (let _152_50 = (force_sort' s)
in (FStar_Syntax_Syntax.mk _152_50 None s.FStar_Syntax_Syntax.pos)))

# 135 "FStar.TypeChecker.Util.fst"
let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env _70_80 -> (match (_70_80) with
| {FStar_Syntax_Syntax.lbname = _70_79; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _70_75; FStar_Syntax_Syntax.lbdef = e} -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 138 "FStar.TypeChecker.Util.fst"
let _70_82 = if (univ_vars <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (
# 139 "FStar.TypeChecker.Util.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 140 "FStar.TypeChecker.Util.fst"
let mk_binder = (fun scope a -> (match (a.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 142 "FStar.TypeChecker.Util.fst"
let _70_92 = (FStar_Syntax_Util.type_u ())
in (match (_70_92) with
| (k, _70_91) -> begin
(
# 143 "FStar.TypeChecker.Util.fst"
let t = (let _152_59 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right _152_59 Prims.fst))
in ((
# 144 "FStar.TypeChecker.Util.fst"
let _70_94 = a
in {FStar_Syntax_Syntax.ppname = _70_94.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_94.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), false))
end))
end
| _70_97 -> begin
(a, true)
end))
in (
# 147 "FStar.TypeChecker.Util.fst"
let rec aux = (fun vars e -> (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, _70_103) -> begin
(aux vars e)
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _70_109) -> begin
(t, true)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _70_115) -> begin
(
# 153 "FStar.TypeChecker.Util.fst"
let _70_134 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _70_121 _70_124 -> (match ((_70_121, _70_124)) with
| ((scope, bs, check), (a, imp)) -> begin
(
# 154 "FStar.TypeChecker.Util.fst"
let _70_127 = (mk_binder scope a)
in (match (_70_127) with
| (tb, c) -> begin
(
# 155 "FStar.TypeChecker.Util.fst"
let b = (tb, imp)
in (
# 156 "FStar.TypeChecker.Util.fst"
let bs = (FStar_List.append bs ((b)::[]))
in (
# 157 "FStar.TypeChecker.Util.fst"
let scope = (FStar_List.append scope ((b)::[]))
in (scope, bs, (c || check)))))
end))
end)) (vars, [], false)))
in (match (_70_134) with
| (scope, bs, check) -> begin
(
# 161 "FStar.TypeChecker.Util.fst"
let _70_137 = (aux scope body)
in (match (_70_137) with
| (res, check_res) -> begin
(
# 162 "FStar.TypeChecker.Util.fst"
let c = (FStar_Syntax_Util.ml_comp res r)
in (
# 163 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Util.arrow bs c)
in (
# 164 "FStar.TypeChecker.Util.fst"
let _70_140 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _152_67 = (FStar_Range.string_of_range r)
in (let _152_66 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _152_67 _152_66)))
end else begin
()
end
in (t, (check_res || check)))))
end))
end))
end
| _70_143 -> begin
(let _152_69 = (let _152_68 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _152_68 Prims.fst))
in (_152_69, false))
end))
in (
# 169 "FStar.TypeChecker.Util.fst"
let _70_146 = (let _152_70 = (t_binders env)
in (aux _152_70 e))
in (match (_70_146) with
| (t, b) -> begin
([], t, b)
end))))))
end
| _70_148 -> begin
(
# 173 "FStar.TypeChecker.Util.fst"
let _70_151 = (FStar_Syntax_Subst.open_univ_vars univ_vars t)
in (match (_70_151) with
| (univ_vars, t) -> begin
(univ_vars, t, false)
end))
end)
end))

# 184 "FStar.TypeChecker.Util.fst"
let pat_as_exps : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term Prims.list * FStar_Syntax_Syntax.pat) = (fun allow_implicits env p -> (
# 189 "FStar.TypeChecker.Util.fst"
let rec pat_as_arg_with_env = (fun allow_wc_dependence env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(
# 198 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) None p.FStar_Syntax_Syntax.p)
in ([], [], [], env, e, p))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _70_164) -> begin
(
# 202 "FStar.TypeChecker.Util.fst"
let _70_170 = (FStar_Syntax_Util.type_u ())
in (match (_70_170) with
| (k, _70_169) -> begin
(
# 203 "FStar.TypeChecker.Util.fst"
let t = (new_uvar env k)
in (
# 204 "FStar.TypeChecker.Util.fst"
let x = (
# 204 "FStar.TypeChecker.Util.fst"
let _70_172 = x
in {FStar_Syntax_Syntax.ppname = _70_172.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_172.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (
# 205 "FStar.TypeChecker.Util.fst"
let _70_177 = (let _152_83 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _152_83 t))
in (match (_70_177) with
| (e, u) -> begin
(
# 206 "FStar.TypeChecker.Util.fst"
let p = (
# 206 "FStar.TypeChecker.Util.fst"
let _70_178 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, e)); FStar_Syntax_Syntax.ty = _70_178.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _70_178.FStar_Syntax_Syntax.p})
in ([], [], [], env, e, p))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 210 "FStar.TypeChecker.Util.fst"
let _70_186 = (FStar_Syntax_Util.type_u ())
in (match (_70_186) with
| (t, _70_185) -> begin
(
# 211 "FStar.TypeChecker.Util.fst"
let x = (
# 211 "FStar.TypeChecker.Util.fst"
let _70_187 = x
in (let _152_84 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _70_187.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_187.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _152_84}))
in (
# 212 "FStar.TypeChecker.Util.fst"
let env = if allow_wc_dependence then begin
(FStar_TypeChecker_Env.push_bv env x)
end else begin
env
end
in (
# 213 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in ((x)::[], [], (x)::[], env, e, p))))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 217 "FStar.TypeChecker.Util.fst"
let _70_197 = (FStar_Syntax_Util.type_u ())
in (match (_70_197) with
| (t, _70_196) -> begin
(
# 218 "FStar.TypeChecker.Util.fst"
let x = (
# 218 "FStar.TypeChecker.Util.fst"
let _70_198 = x
in (let _152_85 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _70_198.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_198.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _152_85}))
in (
# 219 "FStar.TypeChecker.Util.fst"
let env = (FStar_TypeChecker_Env.push_bv env x)
in (
# 220 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in ((x)::[], (x)::[], [], env, e, p))))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 224 "FStar.TypeChecker.Util.fst"
let _70_231 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _70_213 _70_216 -> (match ((_70_213, _70_216)) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(
# 225 "FStar.TypeChecker.Util.fst"
let _70_223 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_70_223) with
| (b', a', w', env, te, pat) -> begin
(
# 226 "FStar.TypeChecker.Util.fst"
let arg = if imp then begin
(FStar_Syntax_Syntax.iarg te)
end else begin
(FStar_Syntax_Syntax.as_arg te)
end
in ((b')::b, (a')::a, (w')::w, env, (arg)::args, ((pat, imp))::pats))
end))
end)) ([], [], [], env, [], [])))
in (match (_70_231) with
| (b, a, w, env, args, pats) -> begin
(
# 229 "FStar.TypeChecker.Util.fst"
let e = (let _152_92 = (let _152_91 = (let _152_90 = (let _152_89 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (let _152_88 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app _152_89 _152_88 None p.FStar_Syntax_Syntax.p)))
in (_152_90, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))
in FStar_Syntax_Syntax.Tm_meta (_152_91))
in (FStar_Syntax_Syntax.mk _152_92 None p.FStar_Syntax_Syntax.p))
in (let _152_95 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _152_94 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _152_93 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in (_152_95, _152_94, _152_93, env, e, (
# 235 "FStar.TypeChecker.Util.fst"
let _70_233 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _70_233.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _70_233.FStar_Syntax_Syntax.p}))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (_70_236) -> begin
(FStar_All.failwith "impossible")
end))
in (
# 239 "FStar.TypeChecker.Util.fst"
let rec elaborate_pat = (fun env p -> (
# 240 "FStar.TypeChecker.Util.fst"
let maybe_dot = (fun inaccessible a r -> if (allow_implicits && inaccessible) then begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term ((a, FStar_Syntax_Syntax.tun))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end else begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var (a)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end)
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 246 "FStar.TypeChecker.Util.fst"
let pats = (FStar_List.map (fun _70_251 -> (match (_70_251) with
| (p, imp) -> begin
(let _152_107 = (elaborate_pat env p)
in (_152_107, imp))
end)) pats)
in (
# 247 "FStar.TypeChecker.Util.fst"
let _70_256 = (FStar_TypeChecker_Env.lookup_datacon env (Prims.fst fv).FStar_Syntax_Syntax.v)
in (match (_70_256) with
| (_70_254, t) -> begin
(
# 248 "FStar.TypeChecker.Util.fst"
let _70_260 = (FStar_Syntax_Util.arrow_formals t)
in (match (_70_260) with
| (f, _70_259) -> begin
(
# 249 "FStar.TypeChecker.Util.fst"
let rec aux = (fun formals pats -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _70_271::_70_269) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v)))))
end
| (_70_277::_70_275, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun _70_283 -> (match (_70_283) with
| (t, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(
# 255 "FStar.TypeChecker.Util.fst"
let a = (let _152_114 = (let _152_113 = (FStar_Syntax_Syntax.range_of_bv t)
in Some (_152_113))
in (FStar_Syntax_Syntax.new_bv _152_114 FStar_Syntax_Syntax.tun))
in (
# 256 "FStar.TypeChecker.Util.fst"
let r = (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v)
in (let _152_115 = (maybe_dot inaccessible a r)
in (_152_115, true))))
end
| _70_290 -> begin
(let _152_119 = (let _152_118 = (let _152_117 = (let _152_116 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _152_116))
in (_152_117, (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v)))
in FStar_Syntax_Syntax.Error (_152_118))
in (Prims.raise _152_119))
end)
end))))
end
| (f::formals', (p, p_imp)::pats') -> begin
(match (f) with
| (_70_301, Some (FStar_Syntax_Syntax.Implicit (_70_303))) when p_imp -> begin
(let _152_120 = (aux formals' pats')
in ((p, true))::_152_120)
end
| (_70_308, Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(
# 268 "FStar.TypeChecker.Util.fst"
let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (
# 269 "FStar.TypeChecker.Util.fst"
let p = (maybe_dot inaccessible a (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v))
in (let _152_121 = (aux formals' pats)
in ((p, true))::_152_121)))
end
| (_70_316, imp) -> begin
(let _152_124 = (let _152_122 = (FStar_Syntax_Syntax.is_implicit imp)
in (p, _152_122))
in (let _152_123 = (aux formals' pats')
in (_152_124)::_152_123))
end)
end))
in (
# 275 "FStar.TypeChecker.Util.fst"
let _70_319 = p
in (let _152_127 = (let _152_126 = (let _152_125 = (aux f pats)
in (fv, _152_125))
in FStar_Syntax_Syntax.Pat_cons (_152_126))
in {FStar_Syntax_Syntax.v = _152_127; FStar_Syntax_Syntax.ty = _70_319.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _70_319.FStar_Syntax_Syntax.p})))
end))
end)))
end
| _70_322 -> begin
p
end)))
in (
# 279 "FStar.TypeChecker.Util.fst"
let one_pat = (fun allow_wc_dependence env p -> (
# 280 "FStar.TypeChecker.Util.fst"
let p = (elaborate_pat env p)
in (
# 281 "FStar.TypeChecker.Util.fst"
let _70_334 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_70_334) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))) with
| Some (x) -> begin
(let _152_136 = (let _152_135 = (let _152_134 = (FStar_TypeChecker_Errors.nonlinear_pattern_variable x)
in (_152_134, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_152_135))
in (Prims.raise _152_136))
end
| _70_338 -> begin
(b, a, w, arg, p)
end)
end))))
in (
# 286 "FStar.TypeChecker.Util.fst"
let top_level_pat_as_args = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_disj (q::pats) -> begin
(
# 293 "FStar.TypeChecker.Util.fst"
let _70_354 = (one_pat false env q)
in (match (_70_354) with
| (b, a, _70_351, te, q) -> begin
(
# 294 "FStar.TypeChecker.Util.fst"
let _70_369 = (FStar_List.fold_right (fun p _70_359 -> (match (_70_359) with
| (w, args, pats) -> begin
(
# 295 "FStar.TypeChecker.Util.fst"
let _70_365 = (one_pat false env p)
in (match (_70_365) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv FStar_Syntax_Syntax.bv_eq a a'))) then begin
(let _152_146 = (let _152_145 = (let _152_144 = (FStar_TypeChecker_Errors.disjunctive_pattern_vars a a')
in (let _152_143 = (FStar_TypeChecker_Env.get_range env)
in (_152_144, _152_143)))
in FStar_Syntax_Syntax.Error (_152_145))
in (Prims.raise _152_146))
end else begin
(let _152_148 = (let _152_147 = (FStar_Syntax_Syntax.as_arg arg)
in (_152_147)::args)
in ((FStar_List.append w' w), _152_148, (p)::pats))
end
end))
end)) pats ([], [], []))
in (match (_70_369) with
| (w, args, pats) -> begin
(let _152_150 = (let _152_149 = (FStar_Syntax_Syntax.as_arg te)
in (_152_149)::args)
in ((FStar_List.append b w), _152_150, (
# 300 "FStar.TypeChecker.Util.fst"
let _70_370 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((q)::pats); FStar_Syntax_Syntax.ty = _70_370.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _70_370.FStar_Syntax_Syntax.p})))
end))
end))
end
| _70_373 -> begin
(
# 303 "FStar.TypeChecker.Util.fst"
let _70_381 = (one_pat true env p)
in (match (_70_381) with
| (b, _70_376, _70_378, arg, p) -> begin
(let _152_152 = (let _152_151 = (FStar_Syntax_Syntax.as_arg arg)
in (_152_151)::[])
in (b, _152_152, p))
end))
end))
in (
# 306 "FStar.TypeChecker.Util.fst"
let _70_385 = (top_level_pat_as_args env p)
in (match (_70_385) with
| (b, args, p) -> begin
(
# 307 "FStar.TypeChecker.Util.fst"
let exps = (FStar_All.pipe_right args (FStar_List.map Prims.fst))
in (b, exps, p))
end)))))))

# 310 "FStar.TypeChecker.Util.fst"
let decorate_pattern : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.pat = (fun env p exps -> (
# 311 "FStar.TypeChecker.Util.fst"
let qq = p
in (
# 312 "FStar.TypeChecker.Util.fst"
let rec aux = (fun p e -> (
# 313 "FStar.TypeChecker.Util.fst"
let pkg = (fun q t -> (FStar_Syntax_Syntax.withinfo q t p.FStar_Syntax_Syntax.p))
in (
# 314 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Util.unmeta e)
in (match ((p.FStar_Syntax_Syntax.v, e.FStar_Syntax_Syntax.n)) with
| (_70_399, FStar_Syntax_Syntax.Tm_uinst (e, _70_402)) -> begin
(aux p e)
end
| (FStar_Syntax_Syntax.Pat_constant (_70_407), FStar_Syntax_Syntax.Tm_constant (_70_410)) -> begin
(let _152_167 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v _152_167))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(
# 322 "FStar.TypeChecker.Util.fst"
let _70_418 = if (not ((FStar_Syntax_Syntax.bv_eq x y))) then begin
(let _152_170 = (let _152_169 = (FStar_Syntax_Print.bv_to_string x)
in (let _152_168 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _152_169 _152_168)))
in (FStar_All.failwith _152_170))
end else begin
()
end
in (
# 324 "FStar.TypeChecker.Util.fst"
let _70_420 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _152_172 = (FStar_Syntax_Print.bv_to_string x)
in (let _152_171 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _152_172 _152_171)))
end else begin
()
end
in (
# 326 "FStar.TypeChecker.Util.fst"
let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (
# 327 "FStar.TypeChecker.Util.fst"
let x = (
# 327 "FStar.TypeChecker.Util.fst"
let _70_423 = x
in {FStar_Syntax_Syntax.ppname = _70_423.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_423.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x)) s.FStar_Syntax_Syntax.n)))))
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(
# 331 "FStar.TypeChecker.Util.fst"
let _70_431 = if (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation) then begin
(let _152_175 = (let _152_174 = (FStar_Syntax_Print.bv_to_string x)
in (let _152_173 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _152_174 _152_173)))
in (FStar_All.failwith _152_175))
end else begin
()
end
in (
# 333 "FStar.TypeChecker.Util.fst"
let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (
# 334 "FStar.TypeChecker.Util.fst"
let x = (
# 334 "FStar.TypeChecker.Util.fst"
let _70_434 = x
in {FStar_Syntax_Syntax.ppname = _70_434.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_434.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x)) s.FStar_Syntax_Syntax.n))))
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _70_439), _70_443) -> begin
(
# 338 "FStar.TypeChecker.Util.fst"
let s = (force_sort e)
in (
# 339 "FStar.TypeChecker.Util.fst"
let x = (
# 339 "FStar.TypeChecker.Util.fst"
let _70_446 = x
in {FStar_Syntax_Syntax.ppname = _70_446.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_446.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
(
# 343 "FStar.TypeChecker.Util.fst"
let _70_456 = if (not ((FStar_Syntax_Syntax.fv_eq fv fv'))) then begin
(let _152_176 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" (Prims.fst fv).FStar_Syntax_Syntax.v.FStar_Ident.str (Prims.fst fv').FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _152_176))
end else begin
()
end
in (let _152_177 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv', []))) _152_177)))
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
(
# 350 "FStar.TypeChecker.Util.fst"
let _70_499 = if (let _152_178 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right _152_178 Prims.op_Negation)) then begin
(let _152_179 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" (Prims.fst fv).FStar_Syntax_Syntax.v.FStar_Ident.str (Prims.fst fv').FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _152_179))
end else begin
()
end
in (
# 353 "FStar.TypeChecker.Util.fst"
let fv = fv'
in (
# 354 "FStar.TypeChecker.Util.fst"
let rec match_args = (fun matched_pats args argpats -> (match ((args, argpats)) with
| ([], []) -> begin
(let _152_186 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev matched_pats)))) _152_186))
end
| (arg::args, (argpat, _70_515)::argpats) -> begin
(match ((arg, argpat.FStar_Syntax_Syntax.v)) with
| ((e, Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (_70_525)) -> begin
(
# 359 "FStar.TypeChecker.Util.fst"
let x = (let _152_187 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _152_187))
in (
# 360 "FStar.TypeChecker.Util.fst"
let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((e, imp), _70_534) -> begin
(
# 364 "FStar.TypeChecker.Util.fst"
let pat = (let _152_189 = (aux argpat e)
in (let _152_188 = (FStar_Syntax_Syntax.is_implicit imp)
in (_152_189, _152_188)))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _70_538 -> begin
(let _152_192 = (let _152_191 = (FStar_Syntax_Print.pat_to_string p)
in (let _152_190 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _152_191 _152_190)))
in (FStar_All.failwith _152_192))
end))
in (match_args [] args argpats))))
end
| _70_540 -> begin
(let _152_197 = (let _152_196 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (let _152_195 = (FStar_Syntax_Print.pat_to_string qq)
in (let _152_194 = (let _152_193 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right _152_193 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _152_196 _152_195 _152_194))))
in (FStar_All.failwith _152_197))
end))))
in (match ((p.FStar_Syntax_Syntax.v, exps)) with
| (FStar_Syntax_Syntax.Pat_disj (ps), _70_544) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(
# 377 "FStar.TypeChecker.Util.fst"
let ps = (FStar_List.map2 aux ps exps)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj (ps)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p))
end
| (_70_548, e::[]) -> begin
(aux p e)
end
| _70_553 -> begin
(FStar_All.failwith "Unexpected number of patterns")
end))))

# 385 "FStar.TypeChecker.Util.fst"
let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (
# 386 "FStar.TypeChecker.Util.fst"
let topt = Some (pat.FStar_Syntax_Syntax.ty)
in (
# 387 "FStar.TypeChecker.Util.fst"
let mk = (fun f -> (FStar_Syntax_Syntax.mk f topt pat.FStar_Syntax_Syntax.p))
in (
# 389 "FStar.TypeChecker.Util.fst"
let pat_as_arg = (fun _70_561 -> (match (_70_561) with
| (p, i) -> begin
(
# 390 "FStar.TypeChecker.Util.fst"
let _70_564 = (decorated_pattern_as_term p)
in (match (_70_564) with
| (vars, te) -> begin
(let _152_205 = (let _152_204 = (FStar_Syntax_Syntax.as_implicit i)
in (te, _152_204))
in (vars, _152_205))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_70_566) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _152_206 = (mk (FStar_Syntax_Syntax.Tm_constant (c)))
in ([], _152_206))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(let _152_207 = (mk (FStar_Syntax_Syntax.Tm_name (x)))
in ((x)::[], _152_207))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 404 "FStar.TypeChecker.Util.fst"
let _70_579 = (let _152_208 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _152_208 FStar_List.unzip))
in (match (_70_579) with
| (vars, args) -> begin
(
# 405 "FStar.TypeChecker.Util.fst"
let vars = (FStar_List.flatten vars)
in (let _152_212 = (let _152_211 = (let _152_210 = (let _152_209 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (_152_209, args))
in FStar_Syntax_Syntax.Tm_app (_152_210))
in (mk _152_211))
in (vars, _152_212)))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
([], e)
end)))))

# 415 "FStar.TypeChecker.Util.fst"
let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (
# 416 "FStar.TypeChecker.Util.fst"
let _70_603 = (match (c.FStar_Syntax_Syntax.effect_args) with
| (wp, _70_592)::(wlp, _70_588)::[] -> begin
(wp, wlp)
end
| _70_596 -> begin
(let _152_218 = (let _152_217 = (let _152_216 = (FStar_List.map (fun _70_600 -> (match (_70_600) with
| (x, _70_599) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right _152_216 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str _152_217))
in (FStar_All.failwith _152_218))
end)
in (match (_70_603) with
| (wp, wlp) -> begin
(c.FStar_Syntax_Syntax.result_typ, wp, wlp)
end)))

# 422 "FStar.TypeChecker.Util.fst"
let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (
# 423 "FStar.TypeChecker.Util.fst"
let _70_611 = (destruct_comp c)
in (match (_70_611) with
| (_70_608, wp, wlp) -> begin
(let _152_240 = (let _152_239 = (let _152_235 = (lift c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _152_235))
in (let _152_238 = (let _152_237 = (let _152_236 = (lift c.FStar_Syntax_Syntax.result_typ wlp)
in (FStar_Syntax_Syntax.as_arg _152_236))
in (_152_237)::[])
in (_152_239)::_152_238))
in {FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _152_240; FStar_Syntax_Syntax.flags = []})
end)))

# 429 "FStar.TypeChecker.Util.fst"
let norm_eff_name : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (
# 430 "FStar.TypeChecker.Util.fst"
let cache = (FStar_Util.smap_create 20)
in (fun env l -> (
# 432 "FStar.TypeChecker.Util.fst"
let rec find = (fun l -> (match ((FStar_TypeChecker_Env.lookup_effect_abbrev env FStar_Syntax_Syntax.U_unknown l)) with
| None -> begin
None
end
| Some (_70_619, c) -> begin
(
# 436 "FStar.TypeChecker.Util.fst"
let l = (FStar_Syntax_Util.comp_to_comp_typ c).FStar_Syntax_Syntax.effect_name
in (match ((find l)) with
| None -> begin
Some (l)
end
| Some (l') -> begin
Some (l')
end))
end))
in (
# 440 "FStar.TypeChecker.Util.fst"
let res = (match ((FStar_Util.smap_try_find cache l.FStar_Ident.str)) with
| Some (l) -> begin
l
end
| None -> begin
(match ((find l)) with
| None -> begin
l
end
| Some (m) -> begin
(
# 445 "FStar.TypeChecker.Util.fst"
let _70_633 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))

# 451 "FStar.TypeChecker.Util.fst"
let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (
# 452 "FStar.TypeChecker.Util.fst"
let _70_644 = (let _152_254 = (norm_eff_name env l1)
in (let _152_253 = (norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _152_254 _152_253)))
in (match (_70_644) with
| (m, _70_641, _70_643) -> begin
m
end)))

# 455 "FStar.TypeChecker.Util.fst"
let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> if ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2)) then begin
FStar_Syntax_Const.effect_Tot_lid
end else begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)

# 461 "FStar.TypeChecker.Util.fst"
let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)) = (fun env c1 c2 -> (
# 462 "FStar.TypeChecker.Util.fst"
let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (
# 463 "FStar.TypeChecker.Util.fst"
let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (
# 464 "FStar.TypeChecker.Util.fst"
let _70_656 = (FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (_70_656) with
| (m, lift1, lift2) -> begin
(
# 465 "FStar.TypeChecker.Util.fst"
let m1 = (lift_comp c1 m lift1)
in (
# 466 "FStar.TypeChecker.Util.fst"
let m2 = (lift_comp c2 m lift2)
in (
# 467 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (
# 468 "FStar.TypeChecker.Util.fst"
let _70_662 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (_70_662) with
| (a, kwp) -> begin
(let _152_268 = (destruct_comp m1)
in (let _152_267 = (destruct_comp m2)
in ((md, a, kwp), _152_268, _152_267)))
end)))))
end)))))

# 471 "FStar.TypeChecker.Util.fst"
let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (
# 472 "FStar.TypeChecker.Util.fst"
let l = (norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)))

# 475 "FStar.TypeChecker.Util.fst"
let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (
# 476 "FStar.TypeChecker.Util.fst"
let l = (norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid))))

# 480 "FStar.TypeChecker.Util.fst"
let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md result wp wlp flags -> (let _152_291 = (let _152_290 = (let _152_289 = (FStar_Syntax_Syntax.as_arg wp)
in (let _152_288 = (let _152_287 = (FStar_Syntax_Syntax.as_arg wlp)
in (_152_287)::[])
in (_152_289)::_152_288))
in {FStar_Syntax_Syntax.effect_name = md.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = _152_290; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp _152_291)))

# 486 "FStar.TypeChecker.Util.fst"
let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (
# 487 "FStar.TypeChecker.Util.fst"
let _70_676 = lc
in (let _152_298 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _70_676.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _152_298; FStar_Syntax_Syntax.cflags = _70_676.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _70_678 -> (match (()) with
| () -> begin
(let _152_297 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _152_297))
end))})))

# 490 "FStar.TypeChecker.Util.fst"
let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _152_301 = (FStar_Syntax_Subst.compress t)
in _152_301.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_70_681) -> begin
true
end
| _70_684 -> begin
false
end))

# 494 "FStar.TypeChecker.Util.fst"
let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v -> (
# 496 "FStar.TypeChecker.Util.fst"
let c = if (let _152_308 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation _152_308)) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(
# 499 "FStar.TypeChecker.Util.fst"
let m = (let _152_309 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must _152_309))
in (
# 500 "FStar.TypeChecker.Util.fst"
let _70_691 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_70_691) with
| (a, kwp) -> begin
(
# 501 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 502 "FStar.TypeChecker.Util.fst"
let wp = (let _152_317 = (let _152_316 = (let _152_311 = (let _152_310 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_152_310)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _152_311 env m m.FStar_Syntax_Syntax.ret))
in (let _152_315 = (let _152_314 = (FStar_Syntax_Syntax.as_arg t)
in (let _152_313 = (let _152_312 = (FStar_Syntax_Syntax.as_arg v)
in (_152_312)::[])
in (_152_314)::_152_313))
in (FStar_Syntax_Syntax.mk_Tm_app _152_316 _152_315 (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _152_317))
in (
# 503 "FStar.TypeChecker.Util.fst"
let wlp = wp
in (mk_comp m t wp wlp ((FStar_Syntax_Syntax.RETURN)::[])))))
end)))
end
in (
# 505 "FStar.TypeChecker.Util.fst"
let _70_696 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return"))) then begin
(let _152_320 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _152_319 = (FStar_Syntax_Print.term_to_string v)
in (let _152_318 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _152_320 _152_319 _152_318))))
end else begin
()
end
in c)))

# 510 "FStar.TypeChecker.Util.fst"
let bind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun env e1opt lc1 _70_703 -> (match (_70_703) with
| (b, lc2) -> begin
(
# 511 "FStar.TypeChecker.Util.fst"
let _70_711 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(
# 513 "FStar.TypeChecker.Util.fst"
let bstr = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _152_331 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (let _152_330 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _152_329 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" _152_331 _152_330 bstr _152_329)))))
end else begin
()
end
in (
# 519 "FStar.TypeChecker.Util.fst"
let bind_it = (fun _70_714 -> (match (()) with
| () -> begin
(
# 520 "FStar.TypeChecker.Util.fst"
let c1 = (lc1.FStar_Syntax_Syntax.comp ())
in (
# 521 "FStar.TypeChecker.Util.fst"
let c2 = (lc2.FStar_Syntax_Syntax.comp ())
in (
# 522 "FStar.TypeChecker.Util.fst"
let _70_720 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _152_338 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _152_337 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _152_336 = (FStar_Syntax_Print.comp_to_string c1)
in (let _152_335 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (let _152_334 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" _152_338 _152_337 _152_336 _152_335 _152_334))))))
end else begin
()
end
in (
# 531 "FStar.TypeChecker.Util.fst"
let try_simplify = (fun _70_723 -> (match (()) with
| () -> begin
(
# 532 "FStar.TypeChecker.Util.fst"
let aux = (fun _70_725 -> (match (()) with
| () -> begin
if (FStar_Syntax_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some ((c2, "trivial no binder"))
end
| Some (_70_728) -> begin
if (FStar_Syntax_Util.is_ml_comp c2) then begin
Some ((c2, "trivial ml"))
end else begin
None
end
end)
end else begin
if ((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) then begin
Some ((c2, "both ml"))
end else begin
None
end
end
end))
in if ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2)) then begin
Some ((c2, "both total"))
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2)) then begin
(let _152_344 = (let _152_343 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in (_152_343, "both gtot"))
in Some (_152_344))
end else begin
(match ((e1opt, b)) with
| (Some (e), Some (x)) -> begin
if ((FStar_Syntax_Util.is_total_comp c1) && (not ((FStar_Syntax_Syntax.is_null_bv x)))) then begin
(let _152_346 = (let _152_345 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT ((x, e)))::[]) c2)
in (_152_345, "substituted e"))
in Some (_152_346))
end else begin
(aux ())
end
end
| _70_736 -> begin
(aux ())
end)
end
end)
end))
in (match ((try_simplify ())) with
| Some (c, reason) -> begin
c
end
| None -> begin
(
# 559 "FStar.TypeChecker.Util.fst"
let _70_754 = (lift_and_destruct env c1 c2)
in (match (_70_754) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(
# 560 "FStar.TypeChecker.Util.fst"
let bs = (match (b) with
| None -> begin
(let _152_347 = (FStar_Syntax_Syntax.null_binder t1)
in (_152_347)::[])
end
| Some (x) -> begin
(let _152_348 = (FStar_Syntax_Syntax.mk_binder x)
in (_152_348)::[])
end)
in (
# 563 "FStar.TypeChecker.Util.fst"
let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp None))
in (
# 564 "FStar.TypeChecker.Util.fst"
let wp_args = (let _152_363 = (FStar_Syntax_Syntax.as_arg t1)
in (let _152_362 = (let _152_361 = (FStar_Syntax_Syntax.as_arg t2)
in (let _152_360 = (let _152_359 = (FStar_Syntax_Syntax.as_arg wp1)
in (let _152_358 = (let _152_357 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _152_356 = (let _152_355 = (let _152_351 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg _152_351))
in (let _152_354 = (let _152_353 = (let _152_352 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _152_352))
in (_152_353)::[])
in (_152_355)::_152_354))
in (_152_357)::_152_356))
in (_152_359)::_152_358))
in (_152_361)::_152_360))
in (_152_363)::_152_362))
in (
# 565 "FStar.TypeChecker.Util.fst"
let wlp_args = (let _152_371 = (FStar_Syntax_Syntax.as_arg t1)
in (let _152_370 = (let _152_369 = (FStar_Syntax_Syntax.as_arg t2)
in (let _152_368 = (let _152_367 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _152_366 = (let _152_365 = (let _152_364 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _152_364))
in (_152_365)::[])
in (_152_367)::_152_366))
in (_152_369)::_152_368))
in (_152_371)::_152_370))
in (
# 566 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t2)))::[]) kwp)
in (
# 567 "FStar.TypeChecker.Util.fst"
let us = (let _152_374 = (env.FStar_TypeChecker_Env.universe_of env t1)
in (let _152_373 = (let _152_372 = (env.FStar_TypeChecker_Env.universe_of env t2)
in (_152_372)::[])
in (_152_374)::_152_373))
in (
# 568 "FStar.TypeChecker.Util.fst"
let wp = (let _152_375 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _152_375 wp_args None t2.FStar_Syntax_Syntax.pos))
in (
# 569 "FStar.TypeChecker.Util.fst"
let wlp = (let _152_376 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wlp)
in (FStar_Syntax_Syntax.mk_Tm_app _152_376 wlp_args None t2.FStar_Syntax_Syntax.pos))
in (
# 570 "FStar.TypeChecker.Util.fst"
let c = (mk_comp md t2 wp wlp [])
in c)))))))))
end))
end)))))
end))
in (let _152_377 = (join_lcomp env lc1 lc2)
in {FStar_Syntax_Syntax.eff_name = _152_377; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it})))
end))

# 577 "FStar.TypeChecker.Util.fst"
let lift_formula : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t mk_wp mk_wlp f -> (
# 578 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 579 "FStar.TypeChecker.Util.fst"
let _70_776 = (FStar_TypeChecker_Env.wp_signature env md_pure.FStar_Syntax_Syntax.mname)
in (match (_70_776) with
| (a, kwp) -> begin
(
# 580 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 581 "FStar.TypeChecker.Util.fst"
let wp = (let _152_391 = (let _152_390 = (FStar_Syntax_Syntax.as_arg t)
in (let _152_389 = (let _152_388 = (FStar_Syntax_Syntax.as_arg f)
in (_152_388)::[])
in (_152_390)::_152_389))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wp _152_391 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (
# 582 "FStar.TypeChecker.Util.fst"
let wlp = (let _152_395 = (let _152_394 = (FStar_Syntax_Syntax.as_arg t)
in (let _152_393 = (let _152_392 = (FStar_Syntax_Syntax.as_arg f)
in (_152_392)::[])
in (_152_394)::_152_393))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wlp _152_395 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (mk_comp md_pure FStar_TypeChecker_Recheck.t_unit wp wlp []))))
end))))

# 585 "FStar.TypeChecker.Util.fst"
let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((f, FStar_Syntax_Syntax.Meta_labeled ((reason, r, false))))) None f.FStar_Syntax_Syntax.pos))

# 588 "FStar.TypeChecker.Util.fst"
let label_opt : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _152_419 = (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)
in (FStar_All.pipe_left Prims.op_Negation _152_419)) then begin
f
end else begin
(let _152_420 = (reason ())
in (label _152_420 r f))
end
end))

# 595 "FStar.TypeChecker.Util.fst"
let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 597 "FStar.TypeChecker.Util.fst"
let _70_796 = g
in (let _152_428 = (let _152_427 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_152_427))
in {FStar_TypeChecker_Env.guard_f = _152_428; FStar_TypeChecker_Env.deferred = _70_796.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _70_796.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _70_796.FStar_TypeChecker_Env.implicits}))
end))

# 599 "FStar.TypeChecker.Util.fst"
let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(
# 601 "FStar.TypeChecker.Util.fst"
let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| _70_807 -> begin
g2
end))

# 605 "FStar.TypeChecker.Util.fst"
let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (
# 606 "FStar.TypeChecker.Util.fst"
let weaken = (fun _70_812 -> (match (()) with
| () -> begin
(
# 607 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (match (f) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
if (FStar_Syntax_Util.is_ml_comp c) then begin
c
end else begin
(
# 613 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 614 "FStar.TypeChecker.Util.fst"
let _70_821 = (destruct_comp c)
in (match (_70_821) with
| (res_t, wp, wlp) -> begin
(
# 615 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 616 "FStar.TypeChecker.Util.fst"
let us = (let _152_441 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_152_441)::[])
in (
# 617 "FStar.TypeChecker.Util.fst"
let wp = (let _152_448 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _152_447 = (let _152_446 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _152_445 = (let _152_444 = (FStar_Syntax_Syntax.as_arg f)
in (let _152_443 = (let _152_442 = (FStar_Syntax_Syntax.as_arg wp)
in (_152_442)::[])
in (_152_444)::_152_443))
in (_152_446)::_152_445))
in (FStar_Syntax_Syntax.mk_Tm_app _152_448 _152_447 None wp.FStar_Syntax_Syntax.pos)))
in (
# 618 "FStar.TypeChecker.Util.fst"
let wlp = (let _152_455 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _152_454 = (let _152_453 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _152_452 = (let _152_451 = (FStar_Syntax_Syntax.as_arg f)
in (let _152_450 = (let _152_449 = (FStar_Syntax_Syntax.as_arg wlp)
in (_152_449)::[])
in (_152_451)::_152_450))
in (_152_453)::_152_452))
in (FStar_Syntax_Syntax.mk_Tm_app _152_455 _152_454 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp c.FStar_Syntax_Syntax.flags)))))
end)))
end
end))
end))
in (
# 620 "FStar.TypeChecker.Util.fst"
let _70_826 = lc
in {FStar_Syntax_Syntax.eff_name = _70_826.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _70_826.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _70_826.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))

# 622 "FStar.TypeChecker.Util.fst"
let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> if (FStar_TypeChecker_Rel.is_trivial g0) then begin
(lc, g0)
end else begin
(
# 626 "FStar.TypeChecker.Util.fst"
let _70_833 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _152_475 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _152_474 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _152_475 _152_474)))
end else begin
()
end
in (
# 630 "FStar.TypeChecker.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _70_2 -> (match (_70_2) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _70_839 -> begin
[]
end))))
in (
# 631 "FStar.TypeChecker.Util.fst"
let strengthen = (fun _70_842 -> (match (()) with
| () -> begin
(
# 632 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 633 "FStar.TypeChecker.Util.fst"
let g0 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (match ((FStar_TypeChecker_Rel.guard_form g0)) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 637 "FStar.TypeChecker.Util.fst"
let c = if (true || (((FStar_Syntax_Util.is_pure_or_ghost_comp c) && (not ((is_function (FStar_Syntax_Util.comp_result c))))) && (not ((FStar_Syntax_Util.is_partial_return c))))) then begin
(
# 642 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.gen_bv "strengthen_pre_x" None (FStar_Syntax_Util.comp_result c))
in (
# 643 "FStar.TypeChecker.Util.fst"
let xret = (let _152_480 = (let _152_479 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _152_479))
in (FStar_Syntax_Util.comp_set_flags _152_480 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (
# 644 "FStar.TypeChecker.Util.fst"
let lc = (bind env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), (FStar_Syntax_Util.lcomp_of_comp xret)))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (
# 648 "FStar.TypeChecker.Util.fst"
let _70_852 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _152_482 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _152_481 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _152_482 _152_481)))
end else begin
()
end
in (
# 653 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 654 "FStar.TypeChecker.Util.fst"
let _70_858 = (destruct_comp c)
in (match (_70_858) with
| (res_t, wp, wlp) -> begin
(
# 655 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 656 "FStar.TypeChecker.Util.fst"
let us = (let _152_483 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_152_483)::[])
in (
# 657 "FStar.TypeChecker.Util.fst"
let wp = (let _152_492 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assert_p)
in (let _152_491 = (let _152_490 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _152_489 = (let _152_488 = (let _152_485 = (let _152_484 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason _152_484 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _152_485))
in (let _152_487 = (let _152_486 = (FStar_Syntax_Syntax.as_arg wp)
in (_152_486)::[])
in (_152_488)::_152_487))
in (_152_490)::_152_489))
in (FStar_Syntax_Syntax.mk_Tm_app _152_492 _152_491 None wp.FStar_Syntax_Syntax.pos)))
in (
# 658 "FStar.TypeChecker.Util.fst"
let wlp = (let _152_499 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _152_498 = (let _152_497 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _152_496 = (let _152_495 = (FStar_Syntax_Syntax.as_arg f)
in (let _152_494 = (let _152_493 = (FStar_Syntax_Syntax.as_arg wlp)
in (_152_493)::[])
in (_152_495)::_152_494))
in (_152_497)::_152_496))
in (FStar_Syntax_Syntax.mk_Tm_app _152_499 _152_498 None wlp.FStar_Syntax_Syntax.pos)))
in (
# 660 "FStar.TypeChecker.Util.fst"
let _70_863 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _152_500 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _152_500))
end else begin
()
end
in (
# 664 "FStar.TypeChecker.Util.fst"
let c2 = (mk_comp md res_t wp wlp flags)
in c2))))))
end)))))
end)))
end))
in (let _152_504 = (
# 666 "FStar.TypeChecker.Util.fst"
let _70_866 = lc
in (let _152_503 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _152_502 = if ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _152_501 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _152_501))) then begin
flags
end else begin
[]
end
in {FStar_Syntax_Syntax.eff_name = _152_503; FStar_Syntax_Syntax.res_typ = _70_866.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _152_502; FStar_Syntax_Syntax.comp = strengthen})))
in (_152_504, (
# 669 "FStar.TypeChecker.Util.fst"
let _70_868 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _70_868.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _70_868.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _70_868.FStar_TypeChecker_Env.implicits}))))))
end)

# 671 "FStar.TypeChecker.Util.fst"
let record_application_site : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (
# 672 "FStar.TypeChecker.Util.fst"
let comp = (fun _70_874 -> (match (()) with
| () -> begin
(
# 673 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 674 "FStar.TypeChecker.Util.fst"
let res_t = (FStar_Syntax_Util.comp_result c)
in if (((FStar_Syntax_Util.is_trivial_wp c) || (let _152_513 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals _152_513 FStar_Syntax_Const.prims_lid))) || (FStar_Syntax_Syntax.is_teff res_t)) then begin
c
end else begin
(
# 679 "FStar.TypeChecker.Util.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (FStar_TypeChecker_Recheck.t_unit)))
in (
# 680 "FStar.TypeChecker.Util.fst"
let _70_882 = (strengthen_precondition (Some ((fun _70_878 -> (match (()) with
| () -> begin
"push"
end)))) env e (FStar_Syntax_Util.lcomp_of_comp c) g)
in (match (_70_882) with
| (c, _70_881) -> begin
(
# 681 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 682 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 683 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 684 "FStar.TypeChecker.Util.fst"
let us = (let _152_517 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_152_517)::[])
in (
# 685 "FStar.TypeChecker.Util.fst"
let xret = (let _152_522 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _152_521 = (let _152_520 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _152_519 = (let _152_518 = (FStar_Syntax_Syntax.as_arg xexp)
in (_152_518)::[])
in (_152_520)::_152_519))
in (FStar_Syntax_Syntax.mk_Tm_app _152_522 _152_521 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 686 "FStar.TypeChecker.Util.fst"
let xret_comp = (let _152_523 = (mk_comp md_pure res_t xret xret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_523))
in (
# 687 "FStar.TypeChecker.Util.fst"
let lc = (let _152_529 = (let _152_528 = (let _152_527 = (strengthen_precondition (Some ((fun _70_889 -> (match (()) with
| () -> begin
"pop"
end)))) env xexp xret_comp g)
in (FStar_All.pipe_left Prims.fst _152_527))
in (Some (x), _152_528))
in (bind env None c _152_529))
in (lc.FStar_Syntax_Syntax.comp ()))))))))
end)))
end))
end))
in (
# 689 "FStar.TypeChecker.Util.fst"
let _70_891 = lc
in {FStar_Syntax_Syntax.eff_name = _70_891.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _70_891.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _70_891.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = comp})))

# 691 "FStar.TypeChecker.Util.fst"
let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env comp res_t -> (
# 692 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 693 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 694 "FStar.TypeChecker.Util.fst"
let y = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 695 "FStar.TypeChecker.Util.fst"
let _70_901 = (let _152_537 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _152_536 = (FStar_Syntax_Syntax.bv_to_name y)
in (_152_537, _152_536)))
in (match (_70_901) with
| (xexp, yexp) -> begin
(
# 696 "FStar.TypeChecker.Util.fst"
let us = (let _152_538 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_152_538)::[])
in (
# 697 "FStar.TypeChecker.Util.fst"
let yret = (let _152_543 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _152_542 = (let _152_541 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _152_540 = (let _152_539 = (FStar_Syntax_Syntax.as_arg yexp)
in (_152_539)::[])
in (_152_541)::_152_540))
in (FStar_Syntax_Syntax.mk_Tm_app _152_543 _152_542 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 698 "FStar.TypeChecker.Util.fst"
let x_eq_y_yret = (let _152_551 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _152_550 = (let _152_549 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _152_548 = (let _152_547 = (let _152_544 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _152_544))
in (let _152_546 = (let _152_545 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_152_545)::[])
in (_152_547)::_152_546))
in (_152_549)::_152_548))
in (FStar_Syntax_Syntax.mk_Tm_app _152_551 _152_550 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 699 "FStar.TypeChecker.Util.fst"
let forall_y_x_eq_y_yret = (let _152_561 = (FStar_TypeChecker_Env.inst_effect_fun_with (FStar_List.append us us) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _152_560 = (let _152_559 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _152_558 = (let _152_557 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _152_556 = (let _152_555 = (let _152_554 = (let _152_553 = (let _152_552 = (FStar_Syntax_Syntax.mk_binder y)
in (_152_552)::[])
in (FStar_Syntax_Util.abs _152_553 x_eq_y_yret None))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _152_554))
in (_152_555)::[])
in (_152_557)::_152_556))
in (_152_559)::_152_558))
in (FStar_Syntax_Syntax.mk_Tm_app _152_561 _152_560 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 700 "FStar.TypeChecker.Util.fst"
let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (
# 701 "FStar.TypeChecker.Util.fst"
let lc = (bind env None (FStar_Syntax_Util.lcomp_of_comp comp) (Some (x), (FStar_Syntax_Util.lcomp_of_comp lc2)))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))

# 704 "FStar.TypeChecker.Util.fst"
let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (
# 705 "FStar.TypeChecker.Util.fst"
let comp = (fun _70_913 -> (match (()) with
| () -> begin
(
# 706 "FStar.TypeChecker.Util.fst"
let _70_929 = (let _152_573 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _152_572 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _152_573 _152_572)))
in (match (_70_929) with
| ((md, _70_916, _70_918), (res_t, wp_then, wlp_then), (_70_925, wp_else, wlp_else)) -> begin
(
# 707 "FStar.TypeChecker.Util.fst"
let us = (let _152_574 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_152_574)::[])
in (
# 708 "FStar.TypeChecker.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _152_594 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _152_593 = (let _152_591 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _152_590 = (let _152_589 = (FStar_Syntax_Syntax.as_arg g)
in (let _152_588 = (let _152_587 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _152_586 = (let _152_585 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_152_585)::[])
in (_152_587)::_152_586))
in (_152_589)::_152_588))
in (_152_591)::_152_590))
in (let _152_592 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _152_594 _152_593 None _152_592)))))
in (
# 709 "FStar.TypeChecker.Util.fst"
let wp = (ifthenelse md res_t guard wp_then wp_else)
in (
# 710 "FStar.TypeChecker.Util.fst"
let wlp = (ifthenelse md res_t guard wlp_then wlp_else)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(
# 712 "FStar.TypeChecker.Util.fst"
let comp = (mk_comp md res_t wp wlp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(
# 714 "FStar.TypeChecker.Util.fst"
let wp = (let _152_601 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _152_600 = (let _152_599 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _152_598 = (let _152_597 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _152_596 = (let _152_595 = (FStar_Syntax_Syntax.as_arg wp)
in (_152_595)::[])
in (_152_597)::_152_596))
in (_152_599)::_152_598))
in (FStar_Syntax_Syntax.mk_Tm_app _152_601 _152_600 None wp.FStar_Syntax_Syntax.pos)))
in (
# 715 "FStar.TypeChecker.Util.fst"
let wlp = (let _152_606 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _152_605 = (let _152_604 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _152_603 = (let _152_602 = (FStar_Syntax_Syntax.as_arg wlp)
in (_152_602)::[])
in (_152_604)::_152_603))
in (FStar_Syntax_Syntax.mk_Tm_app _152_606 _152_605 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end))))
end))
end))
in (let _152_607 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _152_607; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp})))

# 722 "FStar.TypeChecker.Util.fst"
let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (
# 723 "FStar.TypeChecker.Util.fst"
let eff = (FStar_List.fold_left (fun eff _70_949 -> (match (_70_949) with
| (_70_947, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (
# 724 "FStar.TypeChecker.Util.fst"
let bind_cases = (fun _70_952 -> (match (()) with
| () -> begin
(
# 725 "FStar.TypeChecker.Util.fst"
let us = (let _152_618 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_152_618)::[])
in (
# 726 "FStar.TypeChecker.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _152_638 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _152_637 = (let _152_635 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _152_634 = (let _152_633 = (FStar_Syntax_Syntax.as_arg g)
in (let _152_632 = (let _152_631 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _152_630 = (let _152_629 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_152_629)::[])
in (_152_631)::_152_630))
in (_152_633)::_152_632))
in (_152_635)::_152_634))
in (let _152_636 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _152_638 _152_637 None _152_636)))))
in (
# 728 "FStar.TypeChecker.Util.fst"
let default_case = (
# 729 "FStar.TypeChecker.Util.fst"
let post_k = (let _152_641 = (let _152_639 = (FStar_Syntax_Syntax.null_binder res_t)
in (_152_639)::[])
in (let _152_640 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _152_641 _152_640)))
in (
# 730 "FStar.TypeChecker.Util.fst"
let kwp = (let _152_644 = (let _152_642 = (FStar_Syntax_Syntax.null_binder post_k)
in (_152_642)::[])
in (let _152_643 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _152_644 _152_643)))
in (
# 731 "FStar.TypeChecker.Util.fst"
let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (
# 732 "FStar.TypeChecker.Util.fst"
let wp = (let _152_651 = (let _152_645 = (FStar_Syntax_Syntax.mk_binder post)
in (_152_645)::[])
in (let _152_650 = (let _152_649 = (let _152_646 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Errors.exhaustiveness_check _152_646))
in (let _152_648 = (let _152_647 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.false_lid _152_647))
in (FStar_All.pipe_left _152_649 _152_648)))
in (FStar_Syntax_Util.abs _152_651 _152_650 None)))
in (
# 733 "FStar.TypeChecker.Util.fst"
let wlp = (let _152_655 = (let _152_652 = (FStar_Syntax_Syntax.mk_binder post)
in (_152_652)::[])
in (let _152_654 = (let _152_653 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid _152_653))
in (FStar_Syntax_Util.abs _152_655 _152_654 None)))
in (
# 734 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (
# 736 "FStar.TypeChecker.Util.fst"
let comp = (FStar_List.fold_right (fun _70_969 celse -> (match (_70_969) with
| (g, cthen) -> begin
(
# 737 "FStar.TypeChecker.Util.fst"
let _70_987 = (let _152_658 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _152_658 celse))
in (match (_70_987) with
| ((md, _70_973, _70_975), (_70_978, wp_then, wlp_then), (_70_983, wp_else, wlp_else)) -> begin
(let _152_660 = (ifthenelse md res_t g wp_then wp_else)
in (let _152_659 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _152_660 _152_659 [])))
end))
end)) lcases default_case)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(add_equality_to_post_condition env comp res_t)
end else begin
(
# 741 "FStar.TypeChecker.Util.fst"
let comp = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (
# 742 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env comp.FStar_Syntax_Syntax.effect_name)
in (
# 743 "FStar.TypeChecker.Util.fst"
let _70_995 = (destruct_comp comp)
in (match (_70_995) with
| (_70_992, wp, wlp) -> begin
(
# 744 "FStar.TypeChecker.Util.fst"
let wp = (let _152_667 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _152_666 = (let _152_665 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _152_664 = (let _152_663 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _152_662 = (let _152_661 = (FStar_Syntax_Syntax.as_arg wp)
in (_152_661)::[])
in (_152_663)::_152_662))
in (_152_665)::_152_664))
in (FStar_Syntax_Syntax.mk_Tm_app _152_667 _152_666 None wp.FStar_Syntax_Syntax.pos)))
in (
# 745 "FStar.TypeChecker.Util.fst"
let wlp = (let _152_672 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _152_671 = (let _152_670 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _152_669 = (let _152_668 = (FStar_Syntax_Syntax.as_arg wlp)
in (_152_668)::[])
in (_152_670)::_152_669))
in (FStar_Syntax_Syntax.mk_Tm_app _152_672 _152_671 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end))))
end))))
end))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))

# 752 "FStar.TypeChecker.Util.fst"
let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (
# 753 "FStar.TypeChecker.Util.fst"
let close = (fun _70_1002 -> (match (()) with
| () -> begin
(
# 754 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in if (FStar_Syntax_Util.is_ml_comp c) then begin
c
end else begin
(
# 757 "FStar.TypeChecker.Util.fst"
let close_wp = (fun u_res md res_t bvs wp0 -> (FStar_List.fold_right (fun x wp -> (
# 759 "FStar.TypeChecker.Util.fst"
let bs = (let _152_693 = (FStar_Syntax_Syntax.mk_binder x)
in (_152_693)::[])
in (
# 760 "FStar.TypeChecker.Util.fst"
let us = (let _152_695 = (let _152_694 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (_152_694)::[])
in (u_res)::_152_695)
in (
# 761 "FStar.TypeChecker.Util.fst"
let wp = (FStar_Syntax_Util.abs bs wp None)
in (let _152_702 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (let _152_701 = (let _152_700 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _152_699 = (let _152_698 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _152_697 = (let _152_696 = (FStar_Syntax_Syntax.as_arg wp)
in (_152_696)::[])
in (_152_698)::_152_697))
in (_152_700)::_152_699))
in (FStar_Syntax_Syntax.mk_Tm_app _152_702 _152_701 None wp0.FStar_Syntax_Syntax.pos))))))) bvs wp0))
in (
# 764 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 765 "FStar.TypeChecker.Util.fst"
let _70_1019 = (destruct_comp c)
in (match (_70_1019) with
| (t, wp, wlp) -> begin
(
# 766 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 767 "FStar.TypeChecker.Util.fst"
let u_res = (env.FStar_TypeChecker_Env.universe_of env c.FStar_Syntax_Syntax.result_typ)
in (
# 768 "FStar.TypeChecker.Util.fst"
let wp = (close_wp u_res md c.FStar_Syntax_Syntax.result_typ bvs wp)
in (
# 769 "FStar.TypeChecker.Util.fst"
let wlp = (close_wp u_res md c.FStar_Syntax_Syntax.result_typ bvs wlp)
in (mk_comp md c.FStar_Syntax_Syntax.result_typ wp wlp c.FStar_Syntax_Syntax.flags)))))
end))))
end)
end))
in (
# 771 "FStar.TypeChecker.Util.fst"
let _70_1024 = lc
in {FStar_Syntax_Syntax.eff_name = _70_1024.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _70_1024.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _70_1024.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))

# 773 "FStar.TypeChecker.Util.fst"
let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (
# 774 "FStar.TypeChecker.Util.fst"
let refine = (fun _70_1030 -> (match (()) with
| () -> begin
(
# 775 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in if (not ((is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name))) then begin
c
end else begin
if (FStar_Syntax_Util.is_partial_return c) then begin
c
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c) && (not ((FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)))) then begin
(let _152_713 = (let _152_712 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _152_711 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _152_712 _152_711)))
in (FStar_All.failwith _152_713))
end else begin
(
# 783 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 784 "FStar.TypeChecker.Util.fst"
let t = c.FStar_Syntax_Syntax.result_typ
in (
# 785 "FStar.TypeChecker.Util.fst"
let c = (FStar_Syntax_Syntax.mk_Comp c)
in (
# 786 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (
# 787 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 788 "FStar.TypeChecker.Util.fst"
let ret = (let _152_715 = (let _152_714 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _152_714 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_715))
in (
# 789 "FStar.TypeChecker.Util.fst"
let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (
# 790 "FStar.TypeChecker.Util.fst"
let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (
# 792 "FStar.TypeChecker.Util.fst"
let c = (let _152_717 = (let _152_716 = (bind env None (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), eq_ret))
in (_152_716.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _152_717 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
in c)))))))))
end
end
end)
end))
in (
# 795 "FStar.TypeChecker.Util.fst"
let flags = if (((not ((FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)) && (not ((FStar_Syntax_Util.is_lcomp_partial_return lc)))) then begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_Syntax_Syntax.cflags
end else begin
lc.FStar_Syntax_Syntax.cflags
end
in (
# 801 "FStar.TypeChecker.Util.fst"
let _70_1042 = lc
in {FStar_Syntax_Syntax.eff_name = _70_1042.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _70_1042.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))

# 803 "FStar.TypeChecker.Util.fst"
let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (match ((FStar_TypeChecker_Rel.sub_comp env c c')) with
| None -> begin
(let _152_729 = (let _152_728 = (let _152_727 = (FStar_TypeChecker_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _152_726 = (FStar_TypeChecker_Env.get_range env)
in (_152_727, _152_726)))
in FStar_Syntax_Syntax.Error (_152_728))
in (Prims.raise _152_729))
end
| Some (g) -> begin
(e, c', g)
end))

# 809 "FStar.TypeChecker.Util.fst"
let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match ((let _152_738 = (FStar_Syntax_Subst.compress t)
in _152_738.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_70_1056) -> begin
(match ((let _152_739 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _152_739.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _70_1060) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.bool_lid) -> begin
(
# 814 "FStar.TypeChecker.Util.fst"
let _70_1063 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (
# 815 "FStar.TypeChecker.Util.fst"
let b2t = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos)
in (
# 816 "FStar.TypeChecker.Util.fst"
let lc = (let _152_742 = (let _152_741 = (let _152_740 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_740))
in (None, _152_741))
in (bind env (Some (e)) lc _152_742))
in (
# 817 "FStar.TypeChecker.Util.fst"
let e = (let _152_744 = (let _152_743 = (FStar_Syntax_Syntax.as_arg e)
in (_152_743)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _152_744 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (e, lc)))))
end
| _70_1069 -> begin
(e, lc)
end)
end
| _70_1071 -> begin
(e, lc)
end))

# 824 "FStar.TypeChecker.Util.fst"
let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (
# 825 "FStar.TypeChecker.Util.fst"
let gopt = if env.FStar_TypeChecker_Env.use_eq then begin
(let _152_753 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in (_152_753, false))
end else begin
(let _152_754 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in (_152_754, true))
end
in (match (gopt) with
| (None, _70_1079) -> begin
(FStar_TypeChecker_Rel.subtype_fail env lc.FStar_Syntax_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(match ((FStar_TypeChecker_Rel.guard_form g)) with
| FStar_TypeChecker_Common.Trivial -> begin
(
# 833 "FStar.TypeChecker.Util.fst"
let lc = (
# 833 "FStar.TypeChecker.Util.fst"
let _70_1086 = lc
in {FStar_Syntax_Syntax.eff_name = _70_1086.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _70_1086.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _70_1086.FStar_Syntax_Syntax.comp})
in (e, lc, g))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 837 "FStar.TypeChecker.Util.fst"
let g = (
# 837 "FStar.TypeChecker.Util.fst"
let _70_1091 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _70_1091.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _70_1091.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _70_1091.FStar_TypeChecker_Env.implicits})
in (
# 838 "FStar.TypeChecker.Util.fst"
let strengthen = (fun _70_1095 -> (match (()) with
| () -> begin
(
# 840 "FStar.TypeChecker.Util.fst"
let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (match ((let _152_757 = (FStar_Syntax_Subst.compress f)
in _152_757.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_70_1098, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _70_1107); FStar_Syntax_Syntax.tk = _70_1104; FStar_Syntax_Syntax.pos = _70_1102; FStar_Syntax_Syntax.vars = _70_1100}, _70_1112) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) -> begin
(
# 844 "FStar.TypeChecker.Util.fst"
let lc = (
# 844 "FStar.TypeChecker.Util.fst"
let _70_1115 = lc
in {FStar_Syntax_Syntax.eff_name = _70_1115.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _70_1115.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _70_1115.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| _70_1119 -> begin
(
# 848 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 849 "FStar.TypeChecker.Util.fst"
let _70_1121 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _152_761 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _152_760 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _152_759 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _152_758 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _152_761 _152_760 _152_759 _152_758)))))
end else begin
()
end
in (
# 856 "FStar.TypeChecker.Util.fst"
let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 857 "FStar.TypeChecker.Util.fst"
let _70_1126 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_70_1126) with
| (a, kwp) -> begin
(
# 858 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 859 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env ct.FStar_Syntax_Syntax.effect_name)
in (
# 860 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (
# 861 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 862 "FStar.TypeChecker.Util.fst"
let us = (let _152_762 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_152_762)::[])
in (
# 863 "FStar.TypeChecker.Util.fst"
let wp = (let _152_767 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ret)
in (let _152_766 = (let _152_765 = (FStar_Syntax_Syntax.as_arg t)
in (let _152_764 = (let _152_763 = (FStar_Syntax_Syntax.as_arg xexp)
in (_152_763)::[])
in (_152_765)::_152_764))
in (FStar_Syntax_Syntax.mk_Tm_app _152_767 _152_766 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)))
in (
# 864 "FStar.TypeChecker.Util.fst"
let cret = (let _152_768 = (mk_comp md t wp wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_768))
in (
# 865 "FStar.TypeChecker.Util.fst"
let guard = if apply_guard then begin
(let _152_770 = (let _152_769 = (FStar_Syntax_Syntax.as_arg xexp)
in (_152_769)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _152_770 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end else begin
f
end
in (
# 866 "FStar.TypeChecker.Util.fst"
let _70_1137 = (let _152_778 = (FStar_All.pipe_left (fun _152_775 -> Some (_152_775)) (FStar_TypeChecker_Errors.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _152_777 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _152_776 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _152_778 _152_777 e cret _152_776))))
in (match (_70_1137) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(
# 870 "FStar.TypeChecker.Util.fst"
let x = (
# 870 "FStar.TypeChecker.Util.fst"
let _70_1138 = x
in {FStar_Syntax_Syntax.ppname = _70_1138.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_1138.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (
# 871 "FStar.TypeChecker.Util.fst"
let c = (let _152_780 = (let _152_779 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_779))
in (bind env (Some (e)) _152_780 (Some (x), eq_ret)))
in (
# 872 "FStar.TypeChecker.Util.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 873 "FStar.TypeChecker.Util.fst"
let _70_1143 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _152_781 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _152_781))
end else begin
()
end
in c))))
end))))))))))
end)))))
end))
end))
in (
# 876 "FStar.TypeChecker.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _70_3 -> (match (_70_3) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _70_1149 -> begin
[]
end))))
in (
# 877 "FStar.TypeChecker.Util.fst"
let lc = (
# 877 "FStar.TypeChecker.Util.fst"
let _70_1151 = lc
in (let _152_783 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _152_783; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (
# 878 "FStar.TypeChecker.Util.fst"
let g = (
# 878 "FStar.TypeChecker.Util.fst"
let _70_1154 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _70_1154.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _70_1154.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _70_1154.FStar_TypeChecker_Env.implicits})
in (e, lc, g))))))
end)
end)))

# 881 "FStar.TypeChecker.Util.fst"
let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (
# 882 "FStar.TypeChecker.Util.fst"
let mk_post_type = (fun res_t ens -> (
# 883 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _152_795 = (let _152_794 = (let _152_793 = (let _152_792 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _152_792))
in (_152_793)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _152_794 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _152_795))))
in (
# 885 "FStar.TypeChecker.Util.fst"
let norm = (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Unlabel)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env t))
in if (FStar_Syntax_Util.is_tot_or_gtot_comp comp) then begin
(None, (FStar_Syntax_Util.comp_result comp))
end else begin
(match (comp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.GTotal (_)) | (FStar_Syntax_Syntax.Total (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
if ((FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Ghost_lid)) then begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| (req, _70_1182)::(ens, _70_1177)::_70_1174 -> begin
(let _152_801 = (let _152_798 = (norm req)
in Some (_152_798))
in (let _152_800 = (let _152_799 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _152_799))
in (_152_801, _152_800)))
end
| _70_1186 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 899 "FStar.TypeChecker.Util.fst"
let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (wp, _70_1197)::(wlp, _70_1192)::_70_1189 -> begin
(
# 902 "FStar.TypeChecker.Util.fst"
let _70_1203 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (_70_1203) with
| (us_r, _70_1202) -> begin
(
# 903 "FStar.TypeChecker.Util.fst"
let _70_1207 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (_70_1207) with
| (us_e, _70_1206) -> begin
(
# 904 "FStar.TypeChecker.Util.fst"
let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (
# 905 "FStar.TypeChecker.Util.fst"
let as_req = (let _152_802 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.as_requires r)
in (FStar_Syntax_Syntax.mk_Tm_uinst _152_802 us_r))
in (
# 906 "FStar.TypeChecker.Util.fst"
let as_ens = (let _152_803 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.as_ensures r)
in (FStar_Syntax_Syntax.mk_Tm_uinst _152_803 us_e))
in (
# 907 "FStar.TypeChecker.Util.fst"
let req = (let _152_806 = (let _152_805 = (let _152_804 = (FStar_Syntax_Syntax.as_arg wp)
in (_152_804)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.imp_tag)))::_152_805)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _152_806 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 908 "FStar.TypeChecker.Util.fst"
let ens = (let _152_809 = (let _152_808 = (let _152_807 = (FStar_Syntax_Syntax.as_arg wlp)
in (_152_807)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.imp_tag)))::_152_808)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _152_809 None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _152_813 = (let _152_810 = (norm req)
in Some (_152_810))
in (let _152_812 = (let _152_811 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm _152_811))
in (_152_813, _152_812))))))))
end))
end))
end
| _70_1214 -> begin
(FStar_All.failwith "Impossible")
end))
end
end)
end)))

# 918 "FStar.TypeChecker.Util.fst"
let maybe_instantiate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (
# 919 "FStar.TypeChecker.Util.fst"
let torig = (FStar_Syntax_Subst.compress t)
in if (not (env.FStar_TypeChecker_Env.instantiate_imp)) then begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end else begin
(match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 924 "FStar.TypeChecker.Util.fst"
let _70_1225 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_70_1225) with
| (bs, c) -> begin
(
# 925 "FStar.TypeChecker.Util.fst"
let rec aux = (fun subst _70_4 -> (match (_70_4) with
| (x, Some (FStar_Syntax_Syntax.Implicit (dot)))::rest -> begin
(
# 927 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 928 "FStar.TypeChecker.Util.fst"
let _70_1240 = (new_implicit_var env t)
in (match (_70_1240) with
| (v, u, g) -> begin
(
# 929 "FStar.TypeChecker.Util.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, v)))::subst
in (
# 930 "FStar.TypeChecker.Util.fst"
let _70_1246 = (aux subst rest)
in (match (_70_1246) with
| (args, bs, subst, g') -> begin
(let _152_824 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((v, Some (FStar_Syntax_Syntax.Implicit (dot))))::args, bs, subst, _152_824))
end)))
end)))
end
| bs -> begin
([], bs, subst, FStar_TypeChecker_Rel.trivial_guard)
end))
in (
# 934 "FStar.TypeChecker.Util.fst"
let _70_1252 = (aux [] bs)
in (match (_70_1252) with
| (args, bs, subst, guard) -> begin
(match ((args, bs)) with
| ([], _70_1255) -> begin
(e, torig, guard)
end
| (_70_1258, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end
| _70_1262 -> begin
(
# 945 "FStar.TypeChecker.Util.fst"
let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _70_1265 -> begin
(FStar_Syntax_Util.arrow bs c)
end)
in (
# 948 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.subst subst t)
in (
# 949 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk_Tm_app e args (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (e, t, guard))))
end)
end)))
end))
end
| _70_1270 -> begin
(e, t, FStar_TypeChecker_Rel.trivial_guard)
end)
end))

# 959 "FStar.TypeChecker.Util.fst"
let gen_univs : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe_uvar Prims.list * (FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  Prims.bool))  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(
# 961 "FStar.TypeChecker.Util.fst"
let s = (let _152_836 = (let _152_835 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _152_835))
in (FStar_All.pipe_right _152_836 FStar_Util.set_elements))
in (
# 962 "FStar.TypeChecker.Util.fst"
let r = (let _152_837 = (FStar_TypeChecker_Env.get_range env)
in Some (_152_837))
in (
# 963 "FStar.TypeChecker.Util.fst"
let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (
# 964 "FStar.TypeChecker.Util.fst"
let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (
# 965 "FStar.TypeChecker.Util.fst"
let _70_1277 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _152_842 = (let _152_839 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _152_839))
in (let _152_841 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _152_840 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _152_842 _152_841 _152_840))))
end else begin
()
end
in (
# 967 "FStar.TypeChecker.Util.fst"
let _70_1279 = (FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))))
in u_name))))))
in u_names)))
end)

# 971 "FStar.TypeChecker.Util.fst"
let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t -> (
# 972 "FStar.TypeChecker.Util.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (
# 973 "FStar.TypeChecker.Util.fst"
let univs = (FStar_Syntax_Free.univs t)
in (
# 974 "FStar.TypeChecker.Util.fst"
let _70_1287 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _152_851 = (let _152_850 = (let _152_849 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _152_849 (FStar_List.map (fun u -> (let _152_848 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _152_848 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _152_850 (FStar_String.concat ", ")))
in (FStar_Util.print1 "univs to gen : %s\n" _152_851))
end else begin
()
end
in (
# 978 "FStar.TypeChecker.Util.fst"
let gen = (gen_univs env univs)
in (
# 979 "FStar.TypeChecker.Util.fst"
let _70_1290 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _152_852 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _152_852))
end else begin
()
end
in (
# 981 "FStar.TypeChecker.Util.fst"
let ts = (FStar_Syntax_Subst.close_univ_vars gen t)
in (gen, ts))))))))

# 984 "FStar.TypeChecker.Util.fst"
let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> if (let _152_858 = (FStar_Util.for_all (fun _70_1298 -> (match (_70_1298) with
| (_70_1296, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _152_858)) then begin
None
end else begin
(
# 988 "FStar.TypeChecker.Util.fst"
let norm = (fun c -> (
# 989 "FStar.TypeChecker.Util.fst"
let _70_1301 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _152_861 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _152_861))
end else begin
()
end
in (
# 991 "FStar.TypeChecker.Util.fst"
let c = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.Eta)::[]) env c)
end else begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env c)
end
in (
# 994 "FStar.TypeChecker.Util.fst"
let _70_1304 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _152_862 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _152_862))
end else begin
()
end
in c))))
in (
# 997 "FStar.TypeChecker.Util.fst"
let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (
# 998 "FStar.TypeChecker.Util.fst"
let gen_uvars = (fun uvs -> (let _152_865 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _152_865 FStar_Util.set_elements)))
in (
# 999 "FStar.TypeChecker.Util.fst"
let _70_1321 = (let _152_867 = (FStar_All.pipe_right ecs (FStar_List.map (fun _70_1311 -> (match (_70_1311) with
| (e, c) -> begin
(
# 1000 "FStar.TypeChecker.Util.fst"
let t = (FStar_All.pipe_right (FStar_Syntax_Util.comp_result c) FStar_Syntax_Subst.compress)
in (
# 1001 "FStar.TypeChecker.Util.fst"
let c = (norm c)
in (
# 1002 "FStar.TypeChecker.Util.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (
# 1003 "FStar.TypeChecker.Util.fst"
let t = ct.FStar_Syntax_Syntax.result_typ
in (
# 1004 "FStar.TypeChecker.Util.fst"
let univs = (FStar_Syntax_Free.univs t)
in (
# 1005 "FStar.TypeChecker.Util.fst"
let uvt = (FStar_Syntax_Free.uvars t)
in (
# 1006 "FStar.TypeChecker.Util.fst"
let uvs = (gen_uvars uvt)
in (univs, (uvs, e, c)))))))))
end))))
in (FStar_All.pipe_right _152_867 FStar_List.unzip))
in (match (_70_1321) with
| (univs, uvars) -> begin
(
# 1009 "FStar.TypeChecker.Util.fst"
let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (
# 1010 "FStar.TypeChecker.Util.fst"
let gen_univs = (gen_univs env univs)
in (
# 1011 "FStar.TypeChecker.Util.fst"
let _70_1325 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end else begin
()
end
in (
# 1013 "FStar.TypeChecker.Util.fst"
let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _70_1330 -> (match (_70_1330) with
| (uvs, e, c) -> begin
(
# 1014 "FStar.TypeChecker.Util.fst"
let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _70_1333 -> (match (_70_1333) with
| (u, k) -> begin
(match ((FStar_Unionfind.find u)) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(a, Some (FStar_Syntax_Syntax.imp_tag))
end
| FStar_Syntax_Syntax.Fixed (_70_1367) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _70_1370 -> begin
(
# 1020 "FStar.TypeChecker.Util.fst"
let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (
# 1021 "FStar.TypeChecker.Util.fst"
let _70_1374 = (FStar_Syntax_Util.arrow_formals k)
in (match (_70_1374) with
| (bs, kres) -> begin
(
# 1022 "FStar.TypeChecker.Util.fst"
let a = (let _152_873 = (let _152_872 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _152_871 -> Some (_152_871)) _152_872))
in (FStar_Syntax_Syntax.new_bv _152_873 kres))
in (
# 1023 "FStar.TypeChecker.Util.fst"
let t = (let _152_877 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _152_876 = (let _152_875 = (let _152_874 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _152_874))
in Some (_152_875))
in (FStar_Syntax_Util.abs bs _152_877 _152_876)))
in (
# 1024 "FStar.TypeChecker.Util.fst"
let _70_1377 = (FStar_Syntax_Util.set_uvar u t)
in (a, Some (FStar_Syntax_Syntax.imp_tag)))))
end)))
end)
end))))
in (
# 1028 "FStar.TypeChecker.Util.fst"
let _70_1398 = (match (tvars) with
| [] -> begin
(e, c)
end
| _70_1382 -> begin
(
# 1034 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]) env c)
in (
# 1035 "FStar.TypeChecker.Util.fst"
let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]) env e)
in (
# 1037 "FStar.TypeChecker.Util.fst"
let t = (match ((let _152_878 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _152_878.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(
# 1039 "FStar.TypeChecker.Util.fst"
let _70_1391 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (_70_1391) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| _70_1393 -> begin
(FStar_Syntax_Util.arrow tvars c)
end)
in (
# 1044 "FStar.TypeChecker.Util.fst"
let e' = (FStar_Syntax_Util.abs tvars e None)
in (let _152_879 = (FStar_Syntax_Syntax.mk_Total t)
in (e', _152_879))))))
end)
in (match (_70_1398) with
| (e, c) -> begin
(gen_univs, e, c)
end)))
end))))
in Some (ecs)))))
end)))))
end)

# 1049 "FStar.TypeChecker.Util.fst"
let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> (
# 1050 "FStar.TypeChecker.Util.fst"
let _70_1408 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _152_886 = (let _152_885 = (FStar_List.map (fun _70_1407 -> (match (_70_1407) with
| (lb, _70_1404, _70_1406) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _152_885 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _152_886))
end else begin
()
end
in (match ((let _152_888 = (FStar_All.pipe_right lecs (FStar_List.map (fun _70_1414 -> (match (_70_1414) with
| (_70_1411, e, c) -> begin
(e, c)
end))))
in (gen env _152_888))) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun _70_1419 -> (match (_70_1419) with
| (l, t, c) -> begin
(l, [], t, c)
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _70_1427 _70_1431 -> (match ((_70_1427, _70_1431)) with
| ((l, _70_1424, _70_1426), (us, e, c)) -> begin
(
# 1057 "FStar.TypeChecker.Util.fst"
let _70_1432 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _152_894 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _152_893 = (FStar_Syntax_Print.lbname_to_string l)
in (let _152_892 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.print3 "(%s) Generalized %s to %s\n" _152_894 _152_893 _152_892))))
end else begin
()
end
in (l, us, e, c))
end)) lecs ecs)
end)))

# 1070 "FStar.TypeChecker.Util.fst"
let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (
# 1071 "FStar.TypeChecker.Util.fst"
let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (
# 1072 "FStar.TypeChecker.Util.fst"
let check = (fun env t1 t2 -> if env.FStar_TypeChecker_Env.use_eq then begin
(FStar_TypeChecker_Rel.try_teq env t1 t2)
end else begin
(match ((FStar_TypeChecker_Rel.try_subtype env t1 t2)) with
| None -> begin
None
end
| Some (f) -> begin
(let _152_910 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _152_909 -> Some (_152_909)) _152_910))
end)
end)
in (
# 1078 "FStar.TypeChecker.Util.fst"
let is_var = (fun e -> (match ((let _152_913 = (FStar_Syntax_Subst.compress e)
in _152_913.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (_70_1449) -> begin
true
end
| _70_1452 -> begin
false
end))
in (
# 1081 "FStar.TypeChecker.Util.fst"
let decorate = (fun e t -> (
# 1082 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((
# 1084 "FStar.TypeChecker.Util.fst"
let _70_1459 = x
in {FStar_Syntax_Syntax.ppname = _70_1459.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _70_1459.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| _70_1462 -> begin
(
# 1085 "FStar.TypeChecker.Util.fst"
let _70_1463 = e
in (let _152_918 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _70_1463.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _152_918; FStar_Syntax_Syntax.pos = _70_1463.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _70_1463.FStar_Syntax_Syntax.vars}))
end)))
in (
# 1086 "FStar.TypeChecker.Util.fst"
let env = (
# 1086 "FStar.TypeChecker.Util.fst"
let _70_1465 = env
in (let _152_919 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _70_1465.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _70_1465.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _70_1465.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _70_1465.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _70_1465.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _70_1465.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _70_1465.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _70_1465.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _70_1465.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _70_1465.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _70_1465.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _70_1465.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _70_1465.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _70_1465.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _70_1465.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _152_919; FStar_TypeChecker_Env.is_iface = _70_1465.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _70_1465.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _70_1465.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _70_1465.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _70_1465.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _70_1465.FStar_TypeChecker_Env.use_bv_sorts}))
in (match ((check env t1 t2)) with
| None -> begin
(let _152_923 = (let _152_922 = (let _152_921 = (FStar_TypeChecker_Errors.expected_expression_of_type env t2 e t1)
in (let _152_920 = (FStar_TypeChecker_Env.get_range env)
in (_152_921, _152_920)))
in FStar_Syntax_Syntax.Error (_152_922))
in (Prims.raise _152_923))
end
| Some (g) -> begin
(
# 1090 "FStar.TypeChecker.Util.fst"
let _70_1471 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _152_924 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _152_924))
end else begin
()
end
in (let _152_925 = (decorate e t2)
in (_152_925, g)))
end)))))))

# 1095 "FStar.TypeChecker.Util.fst"
let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (
# 1096 "FStar.TypeChecker.Util.fst"
let discharge = (fun g -> (
# 1097 "FStar.TypeChecker.Util.fst"
let _70_1478 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (
# 1099 "FStar.TypeChecker.Util.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _152_935 = (discharge g)
in (let _152_934 = (lc.FStar_Syntax_Syntax.comp ())
in (_152_935, _152_934)))
end else begin
(
# 1102 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 1103 "FStar.TypeChecker.Util.fst"
let steps = (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.DeltaComp)::[]
in (
# 1104 "FStar.TypeChecker.Util.fst"
let c = (let _152_936 = (FStar_TypeChecker_Normalize.normalize_comp steps env c)
in (FStar_All.pipe_right _152_936 FStar_Syntax_Util.comp_to_comp_typ))
in (
# 1105 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 1106 "FStar.TypeChecker.Util.fst"
let _70_1489 = (destruct_comp c)
in (match (_70_1489) with
| (t, wp, _70_1488) -> begin
(
# 1107 "FStar.TypeChecker.Util.fst"
let vc = (let _152_944 = (let _152_938 = (let _152_937 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_152_937)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _152_938 env md md.FStar_Syntax_Syntax.trivial))
in (let _152_943 = (let _152_941 = (FStar_Syntax_Syntax.as_arg t)
in (let _152_940 = (let _152_939 = (FStar_Syntax_Syntax.as_arg wp)
in (_152_939)::[])
in (_152_941)::_152_940))
in (let _152_942 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk_Tm_app _152_944 _152_943 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _152_942))))
in (
# 1108 "FStar.TypeChecker.Util.fst"
let _70_1491 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _152_945 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _152_945))
end else begin
()
end
in (
# 1110 "FStar.TypeChecker.Util.fst"
let g = (let _152_946 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _152_946))
in (let _152_948 = (discharge g)
in (let _152_947 = (FStar_Syntax_Syntax.mk_Comp c)
in (_152_948, _152_947))))))
end))))))
end)))

# 1116 "FStar.TypeChecker.Util.fst"
let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (
# 1117 "FStar.TypeChecker.Util.fst"
let short_bin_op = (fun f _70_5 -> (match (_70_5) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (fst, _70_1502)::[] -> begin
(f fst)
end
| _70_1506 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (
# 1122 "FStar.TypeChecker.Util.fst"
let op_and_e = (fun e -> (let _152_969 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _152_969 (fun _152_968 -> FStar_TypeChecker_Common.NonTrivial (_152_968)))))
in (
# 1123 "FStar.TypeChecker.Util.fst"
let op_or_e = (fun e -> (let _152_974 = (let _152_972 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _152_972))
in (FStar_All.pipe_right _152_974 (fun _152_973 -> FStar_TypeChecker_Common.NonTrivial (_152_973)))))
in (
# 1124 "FStar.TypeChecker.Util.fst"
let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _152_977 -> FStar_TypeChecker_Common.NonTrivial (_152_977))))
in (
# 1125 "FStar.TypeChecker.Util.fst"
let op_or_t = (fun t -> (let _152_981 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _152_981 (fun _152_980 -> FStar_TypeChecker_Common.NonTrivial (_152_980)))))
in (
# 1126 "FStar.TypeChecker.Util.fst"
let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _152_984 -> FStar_TypeChecker_Common.NonTrivial (_152_984))))
in (
# 1128 "FStar.TypeChecker.Util.fst"
let short_op_ite = (fun _70_6 -> (match (_70_6) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (guard, _70_1521)::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| _then::(guard, _70_1526)::[] -> begin
(let _152_988 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _152_988 (fun _152_987 -> FStar_TypeChecker_Common.NonTrivial (_152_987))))
end
| _70_1531 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (
# 1133 "FStar.TypeChecker.Util.fst"
let table = ((FStar_Syntax_Const.op_And, (short_bin_op op_and_e)))::((FStar_Syntax_Const.op_Or, (short_bin_op op_or_e)))::((FStar_Syntax_Const.and_lid, (short_bin_op op_and_t)))::((FStar_Syntax_Const.or_lid, (short_bin_op op_or_t)))::((FStar_Syntax_Const.imp_lid, (short_bin_op op_imp_t)))::((FStar_Syntax_Const.ite_lid, short_op_ite))::[]
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _70_1536) -> begin
(
# 1143 "FStar.TypeChecker.Util.fst"
let lid = fv.FStar_Syntax_Syntax.v
in (match ((FStar_Util.find_map table (fun _70_1542 -> (match (_70_1542) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _152_1021 = (mk seen_args)
in Some (_152_1021))
end else begin
None
end
end)))) with
| None -> begin
FStar_TypeChecker_Common.Trivial
end
| Some (g) -> begin
g
end))
end
| _70_1547 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))

# 1150 "FStar.TypeChecker.Util.fst"
let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (match ((let _152_1024 = (FStar_Syntax_Subst.compress l)
in _152_1024.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (v, _70_1551) -> begin
(FStar_Util.for_some (FStar_Ident.lid_equals v.FStar_Syntax_Syntax.v) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| _70_1555 -> begin
false
end))

# 1171 "FStar.TypeChecker.Util.fst"
let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (
# 1172 "FStar.TypeChecker.Util.fst"
let pos = (fun bs -> (match (bs) with
| (hd, _70_1564)::_70_1561 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| _70_1568 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| (_70_1572, Some (FStar_Syntax_Syntax.Implicit (_70_1574)))::_70_1570 -> begin
bs
end
| _70_1580 -> begin
(match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
bs
end
| Some (t) -> begin
(match ((let _152_1031 = (FStar_Syntax_Subst.compress t)
in _152_1031.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', _70_1586) -> begin
(match ((FStar_Util.prefix_until (fun _70_7 -> (match (_70_7) with
| (_70_1591, Some (FStar_Syntax_Syntax.Implicit (_70_1593))) -> begin
false
end
| _70_1598 -> begin
true
end)) bs')) with
| None -> begin
bs
end
| Some ([], _70_1602, _70_1604) -> begin
bs
end
| Some (imps, _70_1609, _70_1611) -> begin
if (FStar_All.pipe_right imps (FStar_Util.for_all (fun _70_1617 -> (match (_70_1617) with
| (x, _70_1616) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end)))) then begin
(
# 1188 "FStar.TypeChecker.Util.fst"
let r = (pos bs)
in (
# 1189 "FStar.TypeChecker.Util.fst"
let imps = (FStar_All.pipe_right imps (FStar_List.map (fun _70_1621 -> (match (_70_1621) with
| (x, i) -> begin
(let _152_1035 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in (_152_1035, i))
end))))
in (FStar_List.append imps bs)))
end else begin
bs
end
end)
end
| _70_1624 -> begin
bs
end)
end)
end)))




