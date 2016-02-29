
open Prims
# 31 "FStar.TypeChecker.Util.fst"
type lcomp_with_binder =
(FStar_Syntax_Syntax.bv Prims.option * FStar_Syntax_Syntax.lcomp)

# 77 "FStar.TypeChecker.Util.fst"
let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _150_6 = (FStar_TypeChecker_Env.get_range env)
in (let _150_5 = (FStar_TypeChecker_Errors.failed_to_prove_specification errs)
in (FStar_TypeChecker_Errors.report _150_6 _150_5))))

# 84 "FStar.TypeChecker.Util.fst"
let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _150_9 = (FStar_Syntax_Subst.compress t)
in _150_9.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_69_12) -> begin
true
end
| _69_15 -> begin
false
end))

# 88 "FStar.TypeChecker.Util.fst"
let t_binders : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env -> (let _150_13 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right _150_13 (FStar_List.filter (fun _69_20 -> (match (_69_20) with
| (x, _69_19) -> begin
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
in (let _150_18 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Rel.new_uvar _150_18 bs k))))

# 98 "FStar.TypeChecker.Util.fst"
let new_uvar : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env k -> (let _150_23 = (new_uvar_aux env k)
in (Prims.fst _150_23)))

# 100 "FStar.TypeChecker.Util.fst"
let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun _69_1 -> (match (_69_1) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, _69_35); FStar_Syntax_Syntax.tk = _69_32; FStar_Syntax_Syntax.pos = _69_30; FStar_Syntax_Syntax.vars = _69_28} -> begin
uv
end
| _69_40 -> begin
(FStar_All.failwith "Impossible")
end))

# 104 "FStar.TypeChecker.Util.fst"
let new_implicit_var : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.uvar * FStar_Range.range) * FStar_TypeChecker_Env.guard_t) = (fun env k -> (
# 105 "FStar.TypeChecker.Util.fst"
let _69_45 = (new_uvar_aux env k)
in (match (_69_45) with
| (t, u) -> begin
(
# 106 "FStar.TypeChecker.Util.fst"
let g = (
# 106 "FStar.TypeChecker.Util.fst"
let _69_46 = FStar_TypeChecker_Rel.trivial_guard
in (let _150_32 = (let _150_31 = (let _150_30 = (as_uvar u)
in (env, _150_30, t, k, u.FStar_Syntax_Syntax.pos))
in (_150_31)::[])
in {FStar_TypeChecker_Env.guard_f = _69_46.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _69_46.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _69_46.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _150_32}))
in (let _150_34 = (let _150_33 = (as_uvar u)
in (_150_33, u.FStar_Syntax_Syntax.pos))
in (t, _150_34, g)))
end)))

# 109 "FStar.TypeChecker.Util.fst"
let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun r t -> (
# 110 "FStar.TypeChecker.Util.fst"
let uvs = (FStar_Syntax_Free.uvars t)
in if (not ((FStar_Util.set_is_empty uvs))) then begin
(
# 113 "FStar.TypeChecker.Util.fst"
let us = (let _150_41 = (let _150_40 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun _69_55 -> (match (_69_55) with
| (x, _69_54) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) _150_40))
in (FStar_All.pipe_right _150_41 (FStar_String.concat ", ")))
in (
# 115 "FStar.TypeChecker.Util.fst"
let hide_uvar_nums_saved = (FStar_ST.read FStar_Options.hide_uvar_nums)
in (
# 116 "FStar.TypeChecker.Util.fst"
let print_implicits_saved = (FStar_ST.read FStar_Options.print_implicits)
in (
# 117 "FStar.TypeChecker.Util.fst"
let _69_59 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums false)
in (
# 118 "FStar.TypeChecker.Util.fst"
let _69_61 = (FStar_ST.op_Colon_Equals FStar_Options.print_implicits true)
in (
# 119 "FStar.TypeChecker.Util.fst"
let _69_63 = (let _150_43 = (let _150_42 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us _150_42))
in (FStar_TypeChecker_Errors.report r _150_43))
in (
# 122 "FStar.TypeChecker.Util.fst"
let _69_65 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums hide_uvar_nums_saved)
in (FStar_ST.op_Colon_Equals FStar_Options.print_implicits print_implicits_saved))))))))
end else begin
()
end))

# 129 "FStar.TypeChecker.Util.fst"
let force_sort' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' = (fun s -> (match ((FStar_ST.read s.FStar_Syntax_Syntax.tk)) with
| None -> begin
(let _150_48 = (let _150_47 = (FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos)
in (let _150_46 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s" _150_47 _150_46)))
in (FStar_All.failwith _150_48))
end
| Some (tk) -> begin
tk
end))

# 133 "FStar.TypeChecker.Util.fst"
let force_sort = (fun s -> (let _150_50 = (force_sort' s)
in (FStar_Syntax_Syntax.mk _150_50 None s.FStar_Syntax_Syntax.pos)))

# 135 "FStar.TypeChecker.Util.fst"
let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env _69_80 -> (match (_69_80) with
| {FStar_Syntax_Syntax.lbname = _69_79; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _69_75; FStar_Syntax_Syntax.lbdef = e} -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 138 "FStar.TypeChecker.Util.fst"
let _69_82 = if (univ_vars <> []) then begin
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
let _69_92 = (FStar_Syntax_Util.type_u ())
in (match (_69_92) with
| (k, _69_91) -> begin
(
# 143 "FStar.TypeChecker.Util.fst"
let t = (let _150_59 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right _150_59 Prims.fst))
in ((
# 144 "FStar.TypeChecker.Util.fst"
let _69_94 = a
in {FStar_Syntax_Syntax.ppname = _69_94.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_94.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), false))
end))
end
| _69_97 -> begin
(a, true)
end))
in (
# 147 "FStar.TypeChecker.Util.fst"
let rec aux = (fun vars e -> (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, _69_103) -> begin
(aux vars e)
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _69_109) -> begin
(t, true)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _69_115) -> begin
(
# 153 "FStar.TypeChecker.Util.fst"
let _69_134 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _69_121 _69_124 -> (match ((_69_121, _69_124)) with
| ((scope, bs, check), (a, imp)) -> begin
(
# 154 "FStar.TypeChecker.Util.fst"
let _69_127 = (mk_binder scope a)
in (match (_69_127) with
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
in (match (_69_134) with
| (scope, bs, check) -> begin
(
# 161 "FStar.TypeChecker.Util.fst"
let _69_137 = (aux scope body)
in (match (_69_137) with
| (res, check_res) -> begin
(
# 162 "FStar.TypeChecker.Util.fst"
let c = (FStar_Syntax_Util.ml_comp res r)
in (
# 163 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Util.arrow bs c)
in (
# 164 "FStar.TypeChecker.Util.fst"
let _69_140 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_67 = (FStar_Range.string_of_range r)
in (let _150_66 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _150_67 _150_66)))
end else begin
()
end
in (t, (check_res || check)))))
end))
end))
end
| _69_143 -> begin
(let _150_69 = (let _150_68 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _150_68 Prims.fst))
in (_150_69, false))
end))
in (
# 169 "FStar.TypeChecker.Util.fst"
let _69_146 = (let _150_70 = (t_binders env)
in (aux _150_70 e))
in (match (_69_146) with
| (t, b) -> begin
([], t, b)
end))))))
end
| _69_148 -> begin
(
# 173 "FStar.TypeChecker.Util.fst"
let _69_151 = (FStar_Syntax_Subst.open_univ_vars univ_vars t)
in (match (_69_151) with
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
| FStar_Syntax_Syntax.Pat_dot_term (x, _69_164) -> begin
(
# 202 "FStar.TypeChecker.Util.fst"
let _69_170 = (FStar_Syntax_Util.type_u ())
in (match (_69_170) with
| (k, _69_169) -> begin
(
# 203 "FStar.TypeChecker.Util.fst"
let t = (new_uvar env k)
in (
# 204 "FStar.TypeChecker.Util.fst"
let x = (
# 204 "FStar.TypeChecker.Util.fst"
let _69_172 = x
in {FStar_Syntax_Syntax.ppname = _69_172.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_172.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (
# 205 "FStar.TypeChecker.Util.fst"
let _69_177 = (let _150_83 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _150_83 t))
in (match (_69_177) with
| (e, u) -> begin
(
# 206 "FStar.TypeChecker.Util.fst"
let p = (
# 206 "FStar.TypeChecker.Util.fst"
let _69_178 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, e)); FStar_Syntax_Syntax.ty = _69_178.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _69_178.FStar_Syntax_Syntax.p})
in ([], [], [], env, e, p))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 210 "FStar.TypeChecker.Util.fst"
let _69_186 = (FStar_Syntax_Util.type_u ())
in (match (_69_186) with
| (t, _69_185) -> begin
(
# 211 "FStar.TypeChecker.Util.fst"
let x = (
# 211 "FStar.TypeChecker.Util.fst"
let _69_187 = x
in (let _150_84 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _69_187.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_187.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_84}))
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
let _69_197 = (FStar_Syntax_Util.type_u ())
in (match (_69_197) with
| (t, _69_196) -> begin
(
# 218 "FStar.TypeChecker.Util.fst"
let x = (
# 218 "FStar.TypeChecker.Util.fst"
let _69_198 = x
in (let _150_85 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _69_198.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_198.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_85}))
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
let _69_231 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _69_213 _69_216 -> (match ((_69_213, _69_216)) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(
# 225 "FStar.TypeChecker.Util.fst"
let _69_223 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_69_223) with
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
in (match (_69_231) with
| (b, a, w, env, args, pats) -> begin
(
# 229 "FStar.TypeChecker.Util.fst"
let e = (let _150_92 = (let _150_91 = (let _150_90 = (let _150_89 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (let _150_88 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app _150_89 _150_88 None p.FStar_Syntax_Syntax.p)))
in (_150_90, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))
in FStar_Syntax_Syntax.Tm_meta (_150_91))
in (FStar_Syntax_Syntax.mk _150_92 None p.FStar_Syntax_Syntax.p))
in (let _150_95 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _150_94 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _150_93 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in (_150_95, _150_94, _150_93, env, e, (
# 235 "FStar.TypeChecker.Util.fst"
let _69_233 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _69_233.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _69_233.FStar_Syntax_Syntax.p}))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (_69_236) -> begin
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
let pats = (FStar_List.map (fun _69_251 -> (match (_69_251) with
| (p, imp) -> begin
(let _150_107 = (elaborate_pat env p)
in (_150_107, imp))
end)) pats)
in (
# 247 "FStar.TypeChecker.Util.fst"
let _69_256 = (FStar_TypeChecker_Env.lookup_datacon env (Prims.fst fv).FStar_Syntax_Syntax.v)
in (match (_69_256) with
| (_69_254, t) -> begin
(
# 248 "FStar.TypeChecker.Util.fst"
let _69_260 = (FStar_Syntax_Util.arrow_formals t)
in (match (_69_260) with
| (f, _69_259) -> begin
(
# 249 "FStar.TypeChecker.Util.fst"
let rec aux = (fun formals pats -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _69_271::_69_269) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v)))))
end
| (_69_277::_69_275, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun _69_283 -> (match (_69_283) with
| (t, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(
# 255 "FStar.TypeChecker.Util.fst"
let a = (let _150_114 = (let _150_113 = (FStar_Syntax_Syntax.range_of_bv t)
in Some (_150_113))
in (FStar_Syntax_Syntax.new_bv _150_114 FStar_Syntax_Syntax.tun))
in (
# 256 "FStar.TypeChecker.Util.fst"
let r = (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v)
in (let _150_115 = (maybe_dot inaccessible a r)
in (_150_115, true))))
end
| _69_290 -> begin
(let _150_119 = (let _150_118 = (let _150_117 = (let _150_116 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _150_116))
in (_150_117, (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v)))
in FStar_Syntax_Syntax.Error (_150_118))
in (Prims.raise _150_119))
end)
end))))
end
| (f::formals', (p, p_imp)::pats') -> begin
(match (f) with
| (_69_301, Some (FStar_Syntax_Syntax.Implicit (_69_303))) when p_imp -> begin
(let _150_120 = (aux formals' pats')
in ((p, true))::_150_120)
end
| (_69_308, Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(
# 268 "FStar.TypeChecker.Util.fst"
let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (
# 269 "FStar.TypeChecker.Util.fst"
let p = (maybe_dot inaccessible a (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v))
in (let _150_121 = (aux formals' pats)
in ((p, true))::_150_121)))
end
| (_69_316, imp) -> begin
(let _150_124 = (let _150_122 = (FStar_Syntax_Syntax.is_implicit imp)
in (p, _150_122))
in (let _150_123 = (aux formals' pats')
in (_150_124)::_150_123))
end)
end))
in (
# 275 "FStar.TypeChecker.Util.fst"
let _69_319 = p
in (let _150_127 = (let _150_126 = (let _150_125 = (aux f pats)
in (fv, _150_125))
in FStar_Syntax_Syntax.Pat_cons (_150_126))
in {FStar_Syntax_Syntax.v = _150_127; FStar_Syntax_Syntax.ty = _69_319.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _69_319.FStar_Syntax_Syntax.p})))
end))
end)))
end
| _69_322 -> begin
p
end)))
in (
# 279 "FStar.TypeChecker.Util.fst"
let one_pat = (fun allow_wc_dependence env p -> (
# 280 "FStar.TypeChecker.Util.fst"
let p = (elaborate_pat env p)
in (
# 281 "FStar.TypeChecker.Util.fst"
let _69_334 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_69_334) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))) with
| Some (x) -> begin
(let _150_136 = (let _150_135 = (let _150_134 = (FStar_TypeChecker_Errors.nonlinear_pattern_variable x)
in (_150_134, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_150_135))
in (Prims.raise _150_136))
end
| _69_338 -> begin
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
let _69_354 = (one_pat false env q)
in (match (_69_354) with
| (b, a, _69_351, te, q) -> begin
(
# 294 "FStar.TypeChecker.Util.fst"
let _69_369 = (FStar_List.fold_right (fun p _69_359 -> (match (_69_359) with
| (w, args, pats) -> begin
(
# 295 "FStar.TypeChecker.Util.fst"
let _69_365 = (one_pat false env p)
in (match (_69_365) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv FStar_Syntax_Syntax.bv_eq a a'))) then begin
(let _150_146 = (let _150_145 = (let _150_144 = (FStar_TypeChecker_Errors.disjunctive_pattern_vars a a')
in (let _150_143 = (FStar_TypeChecker_Env.get_range env)
in (_150_144, _150_143)))
in FStar_Syntax_Syntax.Error (_150_145))
in (Prims.raise _150_146))
end else begin
(let _150_148 = (let _150_147 = (FStar_Syntax_Syntax.as_arg arg)
in (_150_147)::args)
in ((FStar_List.append w' w), _150_148, (p)::pats))
end
end))
end)) pats ([], [], []))
in (match (_69_369) with
| (w, args, pats) -> begin
(let _150_150 = (let _150_149 = (FStar_Syntax_Syntax.as_arg te)
in (_150_149)::args)
in ((FStar_List.append b w), _150_150, (
# 300 "FStar.TypeChecker.Util.fst"
let _69_370 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((q)::pats); FStar_Syntax_Syntax.ty = _69_370.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _69_370.FStar_Syntax_Syntax.p})))
end))
end))
end
| _69_373 -> begin
(
# 303 "FStar.TypeChecker.Util.fst"
let _69_381 = (one_pat true env p)
in (match (_69_381) with
| (b, _69_376, _69_378, arg, p) -> begin
(let _150_152 = (let _150_151 = (FStar_Syntax_Syntax.as_arg arg)
in (_150_151)::[])
in (b, _150_152, p))
end))
end))
in (
# 306 "FStar.TypeChecker.Util.fst"
let _69_385 = (top_level_pat_as_args env p)
in (match (_69_385) with
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
| (_69_399, FStar_Syntax_Syntax.Tm_uinst (e, _69_402)) -> begin
(aux p e)
end
| (FStar_Syntax_Syntax.Pat_constant (_69_407), FStar_Syntax_Syntax.Tm_constant (_69_410)) -> begin
(let _150_167 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v _150_167))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(
# 322 "FStar.TypeChecker.Util.fst"
let _69_418 = if (not ((FStar_Syntax_Syntax.bv_eq x y))) then begin
(let _150_170 = (let _150_169 = (FStar_Syntax_Print.bv_to_string x)
in (let _150_168 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _150_169 _150_168)))
in (FStar_All.failwith _150_170))
end else begin
()
end
in (
# 324 "FStar.TypeChecker.Util.fst"
let _69_420 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _150_172 = (FStar_Syntax_Print.bv_to_string x)
in (let _150_171 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _150_172 _150_171)))
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
let _69_423 = x
in {FStar_Syntax_Syntax.ppname = _69_423.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_423.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x)) s.FStar_Syntax_Syntax.n)))))
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(
# 331 "FStar.TypeChecker.Util.fst"
let _69_431 = if (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation) then begin
(let _150_175 = (let _150_174 = (FStar_Syntax_Print.bv_to_string x)
in (let _150_173 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _150_174 _150_173)))
in (FStar_All.failwith _150_175))
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
let _69_434 = x
in {FStar_Syntax_Syntax.ppname = _69_434.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_434.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x)) s.FStar_Syntax_Syntax.n))))
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _69_439), _69_443) -> begin
(
# 338 "FStar.TypeChecker.Util.fst"
let s = (force_sort e)
in (
# 339 "FStar.TypeChecker.Util.fst"
let x = (
# 339 "FStar.TypeChecker.Util.fst"
let _69_446 = x
in {FStar_Syntax_Syntax.ppname = _69_446.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_446.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
(
# 343 "FStar.TypeChecker.Util.fst"
let _69_456 = if (not ((FStar_Syntax_Syntax.fv_eq fv fv'))) then begin
(let _150_176 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" (Prims.fst fv).FStar_Syntax_Syntax.v.FStar_Ident.str (Prims.fst fv').FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _150_176))
end else begin
()
end
in (let _150_177 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv', []))) _150_177)))
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
(
# 350 "FStar.TypeChecker.Util.fst"
let _69_499 = if (let _150_178 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right _150_178 Prims.op_Negation)) then begin
(let _150_179 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" (Prims.fst fv).FStar_Syntax_Syntax.v.FStar_Ident.str (Prims.fst fv').FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _150_179))
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
(let _150_186 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev matched_pats)))) _150_186))
end
| (arg::args, (argpat, _69_515)::argpats) -> begin
(match ((arg, argpat.FStar_Syntax_Syntax.v)) with
| ((e, Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (_69_525)) -> begin
(
# 359 "FStar.TypeChecker.Util.fst"
let x = (let _150_187 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _150_187))
in (
# 360 "FStar.TypeChecker.Util.fst"
let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((e, imp), _69_534) -> begin
(
# 364 "FStar.TypeChecker.Util.fst"
let pat = (let _150_189 = (aux argpat e)
in (let _150_188 = (FStar_Syntax_Syntax.is_implicit imp)
in (_150_189, _150_188)))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _69_538 -> begin
(let _150_192 = (let _150_191 = (FStar_Syntax_Print.pat_to_string p)
in (let _150_190 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _150_191 _150_190)))
in (FStar_All.failwith _150_192))
end))
in (match_args [] args argpats))))
end
| _69_540 -> begin
(let _150_197 = (let _150_196 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (let _150_195 = (FStar_Syntax_Print.pat_to_string qq)
in (let _150_194 = (let _150_193 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right _150_193 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _150_196 _150_195 _150_194))))
in (FStar_All.failwith _150_197))
end))))
in (match ((p.FStar_Syntax_Syntax.v, exps)) with
| (FStar_Syntax_Syntax.Pat_disj (ps), _69_544) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(
# 377 "FStar.TypeChecker.Util.fst"
let ps = (FStar_List.map2 aux ps exps)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj (ps)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p))
end
| (_69_548, e::[]) -> begin
(aux p e)
end
| _69_553 -> begin
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
let pat_as_arg = (fun _69_561 -> (match (_69_561) with
| (p, i) -> begin
(
# 390 "FStar.TypeChecker.Util.fst"
let _69_564 = (decorated_pattern_as_term p)
in (match (_69_564) with
| (vars, te) -> begin
(let _150_205 = (let _150_204 = (FStar_Syntax_Syntax.as_implicit i)
in (te, _150_204))
in (vars, _150_205))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_69_566) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _150_206 = (mk (FStar_Syntax_Syntax.Tm_constant (c)))
in ([], _150_206))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(let _150_207 = (mk (FStar_Syntax_Syntax.Tm_name (x)))
in ((x)::[], _150_207))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 404 "FStar.TypeChecker.Util.fst"
let _69_579 = (let _150_208 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _150_208 FStar_List.unzip))
in (match (_69_579) with
| (vars, args) -> begin
(
# 405 "FStar.TypeChecker.Util.fst"
let vars = (FStar_List.flatten vars)
in (let _150_212 = (let _150_211 = (let _150_210 = (let _150_209 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (_150_209, args))
in FStar_Syntax_Syntax.Tm_app (_150_210))
in (mk _150_211))
in (vars, _150_212)))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
([], e)
end)))))

# 415 "FStar.TypeChecker.Util.fst"
let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (
# 416 "FStar.TypeChecker.Util.fst"
let _69_603 = (match (c.FStar_Syntax_Syntax.effect_args) with
| (wp, _69_592)::(wlp, _69_588)::[] -> begin
(wp, wlp)
end
| _69_596 -> begin
(let _150_218 = (let _150_217 = (let _150_216 = (FStar_List.map (fun _69_600 -> (match (_69_600) with
| (x, _69_599) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right _150_216 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str _150_217))
in (FStar_All.failwith _150_218))
end)
in (match (_69_603) with
| (wp, wlp) -> begin
(c.FStar_Syntax_Syntax.result_typ, wp, wlp)
end)))

# 422 "FStar.TypeChecker.Util.fst"
let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (
# 423 "FStar.TypeChecker.Util.fst"
let _69_611 = (destruct_comp c)
in (match (_69_611) with
| (_69_608, wp, wlp) -> begin
(let _150_240 = (let _150_239 = (let _150_235 = (lift c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _150_235))
in (let _150_238 = (let _150_237 = (let _150_236 = (lift c.FStar_Syntax_Syntax.result_typ wlp)
in (FStar_Syntax_Syntax.as_arg _150_236))
in (_150_237)::[])
in (_150_239)::_150_238))
in {FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _150_240; FStar_Syntax_Syntax.flags = []})
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
| Some (_69_619, c) -> begin
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
let _69_633 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))

# 451 "FStar.TypeChecker.Util.fst"
let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (
# 452 "FStar.TypeChecker.Util.fst"
let _69_644 = (let _150_254 = (norm_eff_name env l1)
in (let _150_253 = (norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _150_254 _150_253)))
in (match (_69_644) with
| (m, _69_641, _69_643) -> begin
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
let _69_656 = (FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (_69_656) with
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
let _69_662 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (_69_662) with
| (a, kwp) -> begin
(let _150_268 = (destruct_comp m1)
in (let _150_267 = (destruct_comp m2)
in ((md, a, kwp), _150_268, _150_267)))
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
let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md result wp wlp flags -> (let _150_291 = (let _150_290 = (let _150_289 = (FStar_Syntax_Syntax.as_arg wp)
in (let _150_288 = (let _150_287 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_287)::[])
in (_150_289)::_150_288))
in {FStar_Syntax_Syntax.effect_name = md.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = _150_290; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp _150_291)))

# 486 "FStar.TypeChecker.Util.fst"
let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (
# 487 "FStar.TypeChecker.Util.fst"
let _69_676 = lc
in (let _150_298 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _69_676.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _150_298; FStar_Syntax_Syntax.cflags = _69_676.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _69_678 -> (match (()) with
| () -> begin
(let _150_297 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _150_297))
end))})))

# 490 "FStar.TypeChecker.Util.fst"
let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _150_301 = (FStar_Syntax_Subst.compress t)
in _150_301.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_69_681) -> begin
true
end
| _69_684 -> begin
false
end))

# 494 "FStar.TypeChecker.Util.fst"
let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v -> (
# 496 "FStar.TypeChecker.Util.fst"
let c = if (let _150_308 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation _150_308)) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(
# 499 "FStar.TypeChecker.Util.fst"
let m = (let _150_309 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must _150_309))
in (
# 500 "FStar.TypeChecker.Util.fst"
let _69_691 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_69_691) with
| (a, kwp) -> begin
(
# 501 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 502 "FStar.TypeChecker.Util.fst"
let wp = (let _150_317 = (let _150_316 = (let _150_311 = (let _150_310 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_150_310)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _150_311 env m m.FStar_Syntax_Syntax.ret))
in (let _150_315 = (let _150_314 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_313 = (let _150_312 = (FStar_Syntax_Syntax.as_arg v)
in (_150_312)::[])
in (_150_314)::_150_313))
in (FStar_Syntax_Syntax.mk_Tm_app _150_316 _150_315 (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _150_317))
in (
# 503 "FStar.TypeChecker.Util.fst"
let wlp = wp
in (mk_comp m t wp wlp ((FStar_Syntax_Syntax.RETURN)::[])))))
end)))
end
in (
# 505 "FStar.TypeChecker.Util.fst"
let _69_696 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return"))) then begin
(let _150_320 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _150_319 = (FStar_Syntax_Print.term_to_string v)
in (let _150_318 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _150_320 _150_319 _150_318))))
end else begin
()
end
in c)))

# 510 "FStar.TypeChecker.Util.fst"
let bind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun env e1opt lc1 _69_703 -> (match (_69_703) with
| (b, lc2) -> begin
(
# 511 "FStar.TypeChecker.Util.fst"
let _69_711 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(
# 513 "FStar.TypeChecker.Util.fst"
let bstr = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _150_331 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (let _150_330 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _150_329 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" _150_331 _150_330 bstr _150_329)))))
end else begin
()
end
in (
# 519 "FStar.TypeChecker.Util.fst"
let bind_it = (fun _69_714 -> (match (()) with
| () -> begin
(
# 520 "FStar.TypeChecker.Util.fst"
let c1 = (lc1.FStar_Syntax_Syntax.comp ())
in (
# 521 "FStar.TypeChecker.Util.fst"
let c2 = (lc2.FStar_Syntax_Syntax.comp ())
in (
# 522 "FStar.TypeChecker.Util.fst"
let _69_720 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_338 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _150_337 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _150_336 = (FStar_Syntax_Print.comp_to_string c1)
in (let _150_335 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (let _150_334 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" _150_338 _150_337 _150_336 _150_335 _150_334))))))
end else begin
()
end
in (
# 531 "FStar.TypeChecker.Util.fst"
let try_simplify = (fun _69_723 -> (match (()) with
| () -> begin
(
# 532 "FStar.TypeChecker.Util.fst"
let aux = (fun _69_725 -> (match (()) with
| () -> begin
if (FStar_Syntax_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some ((c2, "trivial no binder"))
end
| Some (_69_728) -> begin
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
(let _150_344 = (let _150_343 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in (_150_343, "both gtot"))
in Some (_150_344))
end else begin
(match ((e1opt, b)) with
| (Some (e), Some (x)) -> begin
if ((FStar_Syntax_Util.is_total_comp c1) && (not ((FStar_Syntax_Syntax.is_null_bv x)))) then begin
(let _150_346 = (let _150_345 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT ((x, e)))::[]) c2)
in (_150_345, "substituted e"))
in Some (_150_346))
end else begin
(aux ())
end
end
| _69_736 -> begin
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
let _69_754 = (lift_and_destruct env c1 c2)
in (match (_69_754) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(
# 560 "FStar.TypeChecker.Util.fst"
let bs = (match (b) with
| None -> begin
(let _150_347 = (FStar_Syntax_Syntax.null_binder t1)
in (_150_347)::[])
end
| Some (x) -> begin
(let _150_348 = (FStar_Syntax_Syntax.mk_binder x)
in (_150_348)::[])
end)
in (
# 563 "FStar.TypeChecker.Util.fst"
let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp None))
in (
# 564 "FStar.TypeChecker.Util.fst"
let wp_args = (let _150_363 = (FStar_Syntax_Syntax.as_arg t1)
in (let _150_362 = (let _150_361 = (FStar_Syntax_Syntax.as_arg t2)
in (let _150_360 = (let _150_359 = (FStar_Syntax_Syntax.as_arg wp1)
in (let _150_358 = (let _150_357 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _150_356 = (let _150_355 = (let _150_351 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg _150_351))
in (let _150_354 = (let _150_353 = (let _150_352 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _150_352))
in (_150_353)::[])
in (_150_355)::_150_354))
in (_150_357)::_150_356))
in (_150_359)::_150_358))
in (_150_361)::_150_360))
in (_150_363)::_150_362))
in (
# 565 "FStar.TypeChecker.Util.fst"
let wlp_args = (let _150_371 = (FStar_Syntax_Syntax.as_arg t1)
in (let _150_370 = (let _150_369 = (FStar_Syntax_Syntax.as_arg t2)
in (let _150_368 = (let _150_367 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _150_366 = (let _150_365 = (let _150_364 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _150_364))
in (_150_365)::[])
in (_150_367)::_150_366))
in (_150_369)::_150_368))
in (_150_371)::_150_370))
in (
# 566 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t2)))::[]) kwp)
in (
# 567 "FStar.TypeChecker.Util.fst"
let us = (let _150_374 = (env.FStar_TypeChecker_Env.universe_of env t1)
in (let _150_373 = (let _150_372 = (env.FStar_TypeChecker_Env.universe_of env t2)
in (_150_372)::[])
in (_150_374)::_150_373))
in (
# 568 "FStar.TypeChecker.Util.fst"
let wp = (let _150_375 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _150_375 wp_args None t2.FStar_Syntax_Syntax.pos))
in (
# 569 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_376 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wlp)
in (FStar_Syntax_Syntax.mk_Tm_app _150_376 wlp_args None t2.FStar_Syntax_Syntax.pos))
in (
# 570 "FStar.TypeChecker.Util.fst"
let c = (mk_comp md t2 wp wlp [])
in c)))))))))
end))
end)))))
end))
in (let _150_377 = (join_lcomp env lc1 lc2)
in {FStar_Syntax_Syntax.eff_name = _150_377; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it})))
end))

# 577 "FStar.TypeChecker.Util.fst"
let lift_formula : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t mk_wp mk_wlp f -> (
# 578 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 579 "FStar.TypeChecker.Util.fst"
let _69_776 = (FStar_TypeChecker_Env.wp_signature env md_pure.FStar_Syntax_Syntax.mname)
in (match (_69_776) with
| (a, kwp) -> begin
(
# 580 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 581 "FStar.TypeChecker.Util.fst"
let wp = (let _150_391 = (let _150_390 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_389 = (let _150_388 = (FStar_Syntax_Syntax.as_arg f)
in (_150_388)::[])
in (_150_390)::_150_389))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wp _150_391 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (
# 582 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_395 = (let _150_394 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_393 = (let _150_392 = (FStar_Syntax_Syntax.as_arg f)
in (_150_392)::[])
in (_150_394)::_150_393))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wlp _150_395 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (mk_comp md_pure FStar_TypeChecker_Common.t_unit wp wlp []))))
end))))

# 585 "FStar.TypeChecker.Util.fst"
let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((f, FStar_Syntax_Syntax.Meta_labeled ((reason, r, false))))) None f.FStar_Syntax_Syntax.pos))

# 588 "FStar.TypeChecker.Util.fst"
let label_opt : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _150_419 = (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)
in (FStar_All.pipe_left Prims.op_Negation _150_419)) then begin
f
end else begin
(let _150_420 = (reason ())
in (label _150_420 r f))
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
let _69_796 = g
in (let _150_428 = (let _150_427 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_150_427))
in {FStar_TypeChecker_Env.guard_f = _150_428; FStar_TypeChecker_Env.deferred = _69_796.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _69_796.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _69_796.FStar_TypeChecker_Env.implicits}))
end))

# 599 "FStar.TypeChecker.Util.fst"
let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(
# 601 "FStar.TypeChecker.Util.fst"
let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| _69_807 -> begin
g2
end))

# 605 "FStar.TypeChecker.Util.fst"
let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (
# 606 "FStar.TypeChecker.Util.fst"
let weaken = (fun _69_812 -> (match (()) with
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
let _69_821 = (destruct_comp c)
in (match (_69_821) with
| (res_t, wp, wlp) -> begin
(
# 615 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 616 "FStar.TypeChecker.Util.fst"
let us = (let _150_441 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_441)::[])
in (
# 617 "FStar.TypeChecker.Util.fst"
let wp = (let _150_448 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _150_447 = (let _150_446 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_445 = (let _150_444 = (FStar_Syntax_Syntax.as_arg f)
in (let _150_443 = (let _150_442 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_442)::[])
in (_150_444)::_150_443))
in (_150_446)::_150_445))
in (FStar_Syntax_Syntax.mk_Tm_app _150_448 _150_447 None wp.FStar_Syntax_Syntax.pos)))
in (
# 618 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_455 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _150_454 = (let _150_453 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_452 = (let _150_451 = (FStar_Syntax_Syntax.as_arg f)
in (let _150_450 = (let _150_449 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_449)::[])
in (_150_451)::_150_450))
in (_150_453)::_150_452))
in (FStar_Syntax_Syntax.mk_Tm_app _150_455 _150_454 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp c.FStar_Syntax_Syntax.flags)))))
end)))
end
end))
end))
in (
# 620 "FStar.TypeChecker.Util.fst"
let _69_826 = lc
in {FStar_Syntax_Syntax.eff_name = _69_826.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _69_826.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _69_826.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))

# 622 "FStar.TypeChecker.Util.fst"
let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> if (FStar_TypeChecker_Rel.is_trivial g0) then begin
(lc, g0)
end else begin
(
# 626 "FStar.TypeChecker.Util.fst"
let _69_833 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_475 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _150_474 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _150_475 _150_474)))
end else begin
()
end
in (
# 630 "FStar.TypeChecker.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _69_2 -> (match (_69_2) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _69_839 -> begin
[]
end))))
in (
# 631 "FStar.TypeChecker.Util.fst"
let strengthen = (fun _69_842 -> (match (()) with
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
let xret = (let _150_480 = (let _150_479 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _150_479))
in (FStar_Syntax_Util.comp_set_flags _150_480 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (
# 644 "FStar.TypeChecker.Util.fst"
let lc = (bind env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), (FStar_Syntax_Util.lcomp_of_comp xret)))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (
# 648 "FStar.TypeChecker.Util.fst"
let _69_852 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_482 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _150_481 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _150_482 _150_481)))
end else begin
()
end
in (
# 653 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 654 "FStar.TypeChecker.Util.fst"
let _69_858 = (destruct_comp c)
in (match (_69_858) with
| (res_t, wp, wlp) -> begin
(
# 655 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 656 "FStar.TypeChecker.Util.fst"
let us = (let _150_483 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_483)::[])
in (
# 657 "FStar.TypeChecker.Util.fst"
let wp = (let _150_492 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assert_p)
in (let _150_491 = (let _150_490 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_489 = (let _150_488 = (let _150_485 = (let _150_484 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason _150_484 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _150_485))
in (let _150_487 = (let _150_486 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_486)::[])
in (_150_488)::_150_487))
in (_150_490)::_150_489))
in (FStar_Syntax_Syntax.mk_Tm_app _150_492 _150_491 None wp.FStar_Syntax_Syntax.pos)))
in (
# 658 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_499 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _150_498 = (let _150_497 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_496 = (let _150_495 = (FStar_Syntax_Syntax.as_arg f)
in (let _150_494 = (let _150_493 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_493)::[])
in (_150_495)::_150_494))
in (_150_497)::_150_496))
in (FStar_Syntax_Syntax.mk_Tm_app _150_499 _150_498 None wlp.FStar_Syntax_Syntax.pos)))
in (
# 660 "FStar.TypeChecker.Util.fst"
let _69_863 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_500 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _150_500))
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
in (let _150_504 = (
# 666 "FStar.TypeChecker.Util.fst"
let _69_866 = lc
in (let _150_503 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _150_502 = if ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _150_501 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _150_501))) then begin
flags
end else begin
[]
end
in {FStar_Syntax_Syntax.eff_name = _150_503; FStar_Syntax_Syntax.res_typ = _69_866.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _150_502; FStar_Syntax_Syntax.comp = strengthen})))
in (_150_504, (
# 669 "FStar.TypeChecker.Util.fst"
let _69_868 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _69_868.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _69_868.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _69_868.FStar_TypeChecker_Env.implicits}))))))
end)

# 671 "FStar.TypeChecker.Util.fst"
let record_application_site : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (
# 672 "FStar.TypeChecker.Util.fst"
let comp = (fun _69_874 -> (match (()) with
| () -> begin
(
# 673 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 674 "FStar.TypeChecker.Util.fst"
let res_t = (FStar_Syntax_Util.comp_result c)
in if (((FStar_Syntax_Util.is_trivial_wp c) || (let _150_513 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals _150_513 FStar_Syntax_Const.prims_lid))) || (FStar_Syntax_Syntax.is_teff res_t)) then begin
c
end else begin
(
# 679 "FStar.TypeChecker.Util.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (FStar_TypeChecker_Common.t_unit)))
in (
# 680 "FStar.TypeChecker.Util.fst"
let _69_882 = (strengthen_precondition (Some ((fun _69_878 -> (match (()) with
| () -> begin
"push"
end)))) env e (FStar_Syntax_Util.lcomp_of_comp c) g)
in (match (_69_882) with
| (c, _69_881) -> begin
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
let us = (let _150_517 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_517)::[])
in (
# 685 "FStar.TypeChecker.Util.fst"
let xret = (let _150_522 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _150_521 = (let _150_520 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_519 = (let _150_518 = (FStar_Syntax_Syntax.as_arg xexp)
in (_150_518)::[])
in (_150_520)::_150_519))
in (FStar_Syntax_Syntax.mk_Tm_app _150_522 _150_521 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 686 "FStar.TypeChecker.Util.fst"
let xret_comp = (let _150_523 = (mk_comp md_pure res_t xret xret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_523))
in (
# 687 "FStar.TypeChecker.Util.fst"
let lc = (let _150_529 = (let _150_528 = (let _150_527 = (strengthen_precondition (Some ((fun _69_889 -> (match (()) with
| () -> begin
"pop"
end)))) env xexp xret_comp g)
in (FStar_All.pipe_left Prims.fst _150_527))
in (Some (x), _150_528))
in (bind env None c _150_529))
in (lc.FStar_Syntax_Syntax.comp ()))))))))
end)))
end))
end))
in (
# 689 "FStar.TypeChecker.Util.fst"
let _69_891 = lc
in {FStar_Syntax_Syntax.eff_name = _69_891.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _69_891.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _69_891.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = comp})))

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
let _69_901 = (let _150_537 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _150_536 = (FStar_Syntax_Syntax.bv_to_name y)
in (_150_537, _150_536)))
in (match (_69_901) with
| (xexp, yexp) -> begin
(
# 696 "FStar.TypeChecker.Util.fst"
let us = (let _150_538 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_538)::[])
in (
# 697 "FStar.TypeChecker.Util.fst"
let yret = (let _150_543 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _150_542 = (let _150_541 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_540 = (let _150_539 = (FStar_Syntax_Syntax.as_arg yexp)
in (_150_539)::[])
in (_150_541)::_150_540))
in (FStar_Syntax_Syntax.mk_Tm_app _150_543 _150_542 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 698 "FStar.TypeChecker.Util.fst"
let x_eq_y_yret = (let _150_551 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _150_550 = (let _150_549 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_548 = (let _150_547 = (let _150_544 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _150_544))
in (let _150_546 = (let _150_545 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_150_545)::[])
in (_150_547)::_150_546))
in (_150_549)::_150_548))
in (FStar_Syntax_Syntax.mk_Tm_app _150_551 _150_550 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 699 "FStar.TypeChecker.Util.fst"
let forall_y_x_eq_y_yret = (let _150_561 = (FStar_TypeChecker_Env.inst_effect_fun_with (FStar_List.append us us) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _150_560 = (let _150_559 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_558 = (let _150_557 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_556 = (let _150_555 = (let _150_554 = (let _150_553 = (let _150_552 = (FStar_Syntax_Syntax.mk_binder y)
in (_150_552)::[])
in (FStar_Syntax_Util.abs _150_553 x_eq_y_yret None))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _150_554))
in (_150_555)::[])
in (_150_557)::_150_556))
in (_150_559)::_150_558))
in (FStar_Syntax_Syntax.mk_Tm_app _150_561 _150_560 None res_t.FStar_Syntax_Syntax.pos)))
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
let comp = (fun _69_913 -> (match (()) with
| () -> begin
(
# 706 "FStar.TypeChecker.Util.fst"
let _69_929 = (let _150_573 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _150_572 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _150_573 _150_572)))
in (match (_69_929) with
| ((md, _69_916, _69_918), (res_t, wp_then, wlp_then), (_69_925, wp_else, wlp_else)) -> begin
(
# 707 "FStar.TypeChecker.Util.fst"
let us = (let _150_574 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_574)::[])
in (
# 708 "FStar.TypeChecker.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _150_594 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _150_593 = (let _150_591 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_590 = (let _150_589 = (FStar_Syntax_Syntax.as_arg g)
in (let _150_588 = (let _150_587 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _150_586 = (let _150_585 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_150_585)::[])
in (_150_587)::_150_586))
in (_150_589)::_150_588))
in (_150_591)::_150_590))
in (let _150_592 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _150_594 _150_593 None _150_592)))))
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
let wp = (let _150_601 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _150_600 = (let _150_599 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_598 = (let _150_597 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _150_596 = (let _150_595 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_595)::[])
in (_150_597)::_150_596))
in (_150_599)::_150_598))
in (FStar_Syntax_Syntax.mk_Tm_app _150_601 _150_600 None wp.FStar_Syntax_Syntax.pos)))
in (
# 715 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_606 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _150_605 = (let _150_604 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_603 = (let _150_602 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_602)::[])
in (_150_604)::_150_603))
in (FStar_Syntax_Syntax.mk_Tm_app _150_606 _150_605 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end))))
end))
end))
in (let _150_607 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _150_607; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp})))

# 722 "FStar.TypeChecker.Util.fst"
let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (
# 723 "FStar.TypeChecker.Util.fst"
let eff = (FStar_List.fold_left (fun eff _69_949 -> (match (_69_949) with
| (_69_947, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (
# 724 "FStar.TypeChecker.Util.fst"
let bind_cases = (fun _69_952 -> (match (()) with
| () -> begin
(
# 725 "FStar.TypeChecker.Util.fst"
let us = (let _150_618 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_618)::[])
in (
# 726 "FStar.TypeChecker.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _150_638 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _150_637 = (let _150_635 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_634 = (let _150_633 = (FStar_Syntax_Syntax.as_arg g)
in (let _150_632 = (let _150_631 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _150_630 = (let _150_629 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_150_629)::[])
in (_150_631)::_150_630))
in (_150_633)::_150_632))
in (_150_635)::_150_634))
in (let _150_636 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _150_638 _150_637 None _150_636)))))
in (
# 728 "FStar.TypeChecker.Util.fst"
let default_case = (
# 729 "FStar.TypeChecker.Util.fst"
let post_k = (let _150_641 = (let _150_639 = (FStar_Syntax_Syntax.null_binder res_t)
in (_150_639)::[])
in (let _150_640 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _150_641 _150_640)))
in (
# 730 "FStar.TypeChecker.Util.fst"
let kwp = (let _150_644 = (let _150_642 = (FStar_Syntax_Syntax.null_binder post_k)
in (_150_642)::[])
in (let _150_643 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _150_644 _150_643)))
in (
# 731 "FStar.TypeChecker.Util.fst"
let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (
# 732 "FStar.TypeChecker.Util.fst"
let wp = (let _150_651 = (let _150_645 = (FStar_Syntax_Syntax.mk_binder post)
in (_150_645)::[])
in (let _150_650 = (let _150_649 = (let _150_646 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Errors.exhaustiveness_check _150_646))
in (let _150_648 = (let _150_647 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.false_lid _150_647))
in (FStar_All.pipe_left _150_649 _150_648)))
in (FStar_Syntax_Util.abs _150_651 _150_650 None)))
in (
# 733 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_655 = (let _150_652 = (FStar_Syntax_Syntax.mk_binder post)
in (_150_652)::[])
in (let _150_654 = (let _150_653 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid _150_653))
in (FStar_Syntax_Util.abs _150_655 _150_654 None)))
in (
# 734 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (
# 736 "FStar.TypeChecker.Util.fst"
let comp = (FStar_List.fold_right (fun _69_969 celse -> (match (_69_969) with
| (g, cthen) -> begin
(
# 737 "FStar.TypeChecker.Util.fst"
let _69_987 = (let _150_658 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _150_658 celse))
in (match (_69_987) with
| ((md, _69_973, _69_975), (_69_978, wp_then, wlp_then), (_69_983, wp_else, wlp_else)) -> begin
(let _150_660 = (ifthenelse md res_t g wp_then wp_else)
in (let _150_659 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _150_660 _150_659 [])))
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
let _69_995 = (destruct_comp comp)
in (match (_69_995) with
| (_69_992, wp, wlp) -> begin
(
# 744 "FStar.TypeChecker.Util.fst"
let wp = (let _150_667 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _150_666 = (let _150_665 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_664 = (let _150_663 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _150_662 = (let _150_661 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_661)::[])
in (_150_663)::_150_662))
in (_150_665)::_150_664))
in (FStar_Syntax_Syntax.mk_Tm_app _150_667 _150_666 None wp.FStar_Syntax_Syntax.pos)))
in (
# 745 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_672 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _150_671 = (let _150_670 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_669 = (let _150_668 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_668)::[])
in (_150_670)::_150_669))
in (FStar_Syntax_Syntax.mk_Tm_app _150_672 _150_671 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end))))
end))))
end))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))

# 752 "FStar.TypeChecker.Util.fst"
let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (
# 753 "FStar.TypeChecker.Util.fst"
let close = (fun _69_1002 -> (match (()) with
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
let bs = (let _150_693 = (FStar_Syntax_Syntax.mk_binder x)
in (_150_693)::[])
in (
# 760 "FStar.TypeChecker.Util.fst"
let us = (let _150_695 = (let _150_694 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (_150_694)::[])
in (u_res)::_150_695)
in (
# 761 "FStar.TypeChecker.Util.fst"
let wp = (FStar_Syntax_Util.abs bs wp None)
in (let _150_702 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (let _150_701 = (let _150_700 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_699 = (let _150_698 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _150_697 = (let _150_696 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_696)::[])
in (_150_698)::_150_697))
in (_150_700)::_150_699))
in (FStar_Syntax_Syntax.mk_Tm_app _150_702 _150_701 None wp0.FStar_Syntax_Syntax.pos))))))) bvs wp0))
in (
# 764 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 765 "FStar.TypeChecker.Util.fst"
let _69_1019 = (destruct_comp c)
in (match (_69_1019) with
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
let _69_1024 = lc
in {FStar_Syntax_Syntax.eff_name = _69_1024.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _69_1024.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _69_1024.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))

# 773 "FStar.TypeChecker.Util.fst"
let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (
# 774 "FStar.TypeChecker.Util.fst"
let refine = (fun _69_1030 -> (match (()) with
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
(let _150_713 = (let _150_712 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _150_711 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _150_712 _150_711)))
in (FStar_All.failwith _150_713))
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
let ret = (let _150_715 = (let _150_714 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _150_714 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_715))
in (
# 789 "FStar.TypeChecker.Util.fst"
let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (
# 790 "FStar.TypeChecker.Util.fst"
let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (
# 792 "FStar.TypeChecker.Util.fst"
let c = (let _150_717 = (let _150_716 = (bind env None (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), eq_ret))
in (_150_716.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _150_717 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
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
let _69_1042 = lc
in {FStar_Syntax_Syntax.eff_name = _69_1042.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _69_1042.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))

# 803 "FStar.TypeChecker.Util.fst"
let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (match ((FStar_TypeChecker_Rel.sub_comp env c c')) with
| None -> begin
(let _150_729 = (let _150_728 = (let _150_727 = (FStar_TypeChecker_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _150_726 = (FStar_TypeChecker_Env.get_range env)
in (_150_727, _150_726)))
in FStar_Syntax_Syntax.Error (_150_728))
in (Prims.raise _150_729))
end
| Some (g) -> begin
(e, c', g)
end))

# 809 "FStar.TypeChecker.Util.fst"
let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match ((let _150_738 = (FStar_Syntax_Subst.compress t)
in _150_738.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_69_1056) -> begin
(match ((let _150_739 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _150_739.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _69_1060) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.bool_lid) -> begin
(
# 814 "FStar.TypeChecker.Util.fst"
let _69_1063 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (
# 815 "FStar.TypeChecker.Util.fst"
let b2t = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos)
in (
# 816 "FStar.TypeChecker.Util.fst"
let lc = (let _150_742 = (let _150_741 = (let _150_740 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_740))
in (None, _150_741))
in (bind env (Some (e)) lc _150_742))
in (
# 817 "FStar.TypeChecker.Util.fst"
let e = (let _150_744 = (let _150_743 = (FStar_Syntax_Syntax.as_arg e)
in (_150_743)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _150_744 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (e, lc)))))
end
| _69_1069 -> begin
(e, lc)
end)
end
| _69_1071 -> begin
(e, lc)
end))

# 824 "FStar.TypeChecker.Util.fst"
let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (
# 825 "FStar.TypeChecker.Util.fst"
let gopt = if env.FStar_TypeChecker_Env.use_eq then begin
(let _150_753 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in (_150_753, false))
end else begin
(let _150_754 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in (_150_754, true))
end
in (match (gopt) with
| (None, _69_1079) -> begin
(FStar_TypeChecker_Rel.subtype_fail env lc.FStar_Syntax_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(match ((FStar_TypeChecker_Rel.guard_form g)) with
| FStar_TypeChecker_Common.Trivial -> begin
(
# 833 "FStar.TypeChecker.Util.fst"
let lc = (
# 833 "FStar.TypeChecker.Util.fst"
let _69_1086 = lc
in {FStar_Syntax_Syntax.eff_name = _69_1086.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _69_1086.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _69_1086.FStar_Syntax_Syntax.comp})
in (e, lc, g))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 837 "FStar.TypeChecker.Util.fst"
let g = (
# 837 "FStar.TypeChecker.Util.fst"
let _69_1091 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _69_1091.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _69_1091.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _69_1091.FStar_TypeChecker_Env.implicits})
in (
# 838 "FStar.TypeChecker.Util.fst"
let strengthen = (fun _69_1095 -> (match (()) with
| () -> begin
(
# 840 "FStar.TypeChecker.Util.fst"
let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (match ((let _150_757 = (FStar_Syntax_Subst.compress f)
in _150_757.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_69_1098, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _69_1107); FStar_Syntax_Syntax.tk = _69_1104; FStar_Syntax_Syntax.pos = _69_1102; FStar_Syntax_Syntax.vars = _69_1100}, _69_1112) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) -> begin
(
# 844 "FStar.TypeChecker.Util.fst"
let lc = (
# 844 "FStar.TypeChecker.Util.fst"
let _69_1115 = lc
in {FStar_Syntax_Syntax.eff_name = _69_1115.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _69_1115.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _69_1115.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| _69_1119 -> begin
(
# 848 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 849 "FStar.TypeChecker.Util.fst"
let _69_1121 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_761 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _150_760 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _150_759 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _150_758 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _150_761 _150_760 _150_759 _150_758)))))
end else begin
()
end
in (
# 856 "FStar.TypeChecker.Util.fst"
let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 857 "FStar.TypeChecker.Util.fst"
let _69_1126 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_69_1126) with
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
let us = (let _150_762 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_150_762)::[])
in (
# 863 "FStar.TypeChecker.Util.fst"
let wp = (let _150_767 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ret)
in (let _150_766 = (let _150_765 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_764 = (let _150_763 = (FStar_Syntax_Syntax.as_arg xexp)
in (_150_763)::[])
in (_150_765)::_150_764))
in (FStar_Syntax_Syntax.mk_Tm_app _150_767 _150_766 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)))
in (
# 864 "FStar.TypeChecker.Util.fst"
let cret = (let _150_768 = (mk_comp md t wp wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_768))
in (
# 865 "FStar.TypeChecker.Util.fst"
let guard = if apply_guard then begin
(let _150_770 = (let _150_769 = (FStar_Syntax_Syntax.as_arg xexp)
in (_150_769)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _150_770 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end else begin
f
end
in (
# 866 "FStar.TypeChecker.Util.fst"
let _69_1137 = (let _150_778 = (FStar_All.pipe_left (fun _150_775 -> Some (_150_775)) (FStar_TypeChecker_Errors.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _150_777 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _150_776 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _150_778 _150_777 e cret _150_776))))
in (match (_69_1137) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(
# 870 "FStar.TypeChecker.Util.fst"
let x = (
# 870 "FStar.TypeChecker.Util.fst"
let _69_1138 = x
in {FStar_Syntax_Syntax.ppname = _69_1138.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_1138.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (
# 871 "FStar.TypeChecker.Util.fst"
let c = (let _150_780 = (let _150_779 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_779))
in (bind env (Some (e)) _150_780 (Some (x), eq_ret)))
in (
# 872 "FStar.TypeChecker.Util.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 873 "FStar.TypeChecker.Util.fst"
let _69_1143 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_781 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _150_781))
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
let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _69_3 -> (match (_69_3) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _69_1149 -> begin
[]
end))))
in (
# 877 "FStar.TypeChecker.Util.fst"
let lc = (
# 877 "FStar.TypeChecker.Util.fst"
let _69_1151 = lc
in (let _150_783 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _150_783; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (
# 878 "FStar.TypeChecker.Util.fst"
let g = (
# 878 "FStar.TypeChecker.Util.fst"
let _69_1154 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _69_1154.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _69_1154.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _69_1154.FStar_TypeChecker_Env.implicits})
in (e, lc, g))))))
end)
end)))

# 881 "FStar.TypeChecker.Util.fst"
let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (
# 882 "FStar.TypeChecker.Util.fst"
let mk_post_type = (fun res_t ens -> (
# 883 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _150_795 = (let _150_794 = (let _150_793 = (let _150_792 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _150_792))
in (_150_793)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _150_794 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _150_795))))
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
| (req, _69_1182)::(ens, _69_1177)::_69_1174 -> begin
(let _150_801 = (let _150_798 = (norm req)
in Some (_150_798))
in (let _150_800 = (let _150_799 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _150_799))
in (_150_801, _150_800)))
end
| _69_1186 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 899 "FStar.TypeChecker.Util.fst"
let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (wp, _69_1197)::(wlp, _69_1192)::_69_1189 -> begin
(
# 902 "FStar.TypeChecker.Util.fst"
let _69_1203 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (_69_1203) with
| (us_r, _69_1202) -> begin
(
# 903 "FStar.TypeChecker.Util.fst"
let _69_1207 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (_69_1207) with
| (us_e, _69_1206) -> begin
(
# 904 "FStar.TypeChecker.Util.fst"
let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (
# 905 "FStar.TypeChecker.Util.fst"
let as_req = (let _150_802 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.as_requires r)
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_802 us_r))
in (
# 906 "FStar.TypeChecker.Util.fst"
let as_ens = (let _150_803 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.as_ensures r)
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_803 us_e))
in (
# 907 "FStar.TypeChecker.Util.fst"
let req = (let _150_806 = (let _150_805 = (let _150_804 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_804)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.imp_tag)))::_150_805)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _150_806 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 908 "FStar.TypeChecker.Util.fst"
let ens = (let _150_809 = (let _150_808 = (let _150_807 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_807)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.imp_tag)))::_150_808)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _150_809 None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _150_813 = (let _150_810 = (norm req)
in Some (_150_810))
in (let _150_812 = (let _150_811 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm _150_811))
in (_150_813, _150_812))))))))
end))
end))
end
| _69_1214 -> begin
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
let _69_1225 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_69_1225) with
| (bs, c) -> begin
(
# 925 "FStar.TypeChecker.Util.fst"
let rec aux = (fun subst _69_4 -> (match (_69_4) with
| (x, Some (FStar_Syntax_Syntax.Implicit (dot)))::rest -> begin
(
# 927 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 928 "FStar.TypeChecker.Util.fst"
let _69_1240 = (new_implicit_var env t)
in (match (_69_1240) with
| (v, u, g) -> begin
(
# 929 "FStar.TypeChecker.Util.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, v)))::subst
in (
# 930 "FStar.TypeChecker.Util.fst"
let _69_1246 = (aux subst rest)
in (match (_69_1246) with
| (args, bs, subst, g') -> begin
(let _150_824 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((v, Some (FStar_Syntax_Syntax.Implicit (dot))))::args, bs, subst, _150_824))
end)))
end)))
end
| bs -> begin
([], bs, subst, FStar_TypeChecker_Rel.trivial_guard)
end))
in (
# 934 "FStar.TypeChecker.Util.fst"
let _69_1252 = (aux [] bs)
in (match (_69_1252) with
| (args, bs, subst, guard) -> begin
(match ((args, bs)) with
| ([], _69_1255) -> begin
(e, torig, guard)
end
| (_69_1258, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end
| _69_1262 -> begin
(
# 945 "FStar.TypeChecker.Util.fst"
let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _69_1265 -> begin
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
| _69_1270 -> begin
(e, t, FStar_TypeChecker_Rel.trivial_guard)
end)
end))

# 959 "FStar.TypeChecker.Util.fst"
let gen_univs : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe_uvar Prims.list * (FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  Prims.bool))  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(
# 961 "FStar.TypeChecker.Util.fst"
let s = (let _150_836 = (let _150_835 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _150_835))
in (FStar_All.pipe_right _150_836 FStar_Util.set_elements))
in (
# 962 "FStar.TypeChecker.Util.fst"
let r = (let _150_837 = (FStar_TypeChecker_Env.get_range env)
in Some (_150_837))
in (
# 963 "FStar.TypeChecker.Util.fst"
let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (
# 964 "FStar.TypeChecker.Util.fst"
let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (
# 965 "FStar.TypeChecker.Util.fst"
let _69_1277 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _150_842 = (let _150_839 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _150_839))
in (let _150_841 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _150_840 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _150_842 _150_841 _150_840))))
end else begin
()
end
in (
# 967 "FStar.TypeChecker.Util.fst"
let _69_1279 = (FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))))
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
let _69_1287 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _150_851 = (let _150_850 = (let _150_849 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _150_849 (FStar_List.map (fun u -> (let _150_848 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _150_848 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _150_850 (FStar_String.concat ", ")))
in (FStar_Util.print1 "univs to gen : %s\n" _150_851))
end else begin
()
end
in (
# 978 "FStar.TypeChecker.Util.fst"
let gen = (gen_univs env univs)
in (
# 979 "FStar.TypeChecker.Util.fst"
let _69_1290 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _150_852 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _150_852))
end else begin
()
end
in (
# 981 "FStar.TypeChecker.Util.fst"
let ts = (FStar_Syntax_Subst.close_univ_vars gen t)
in (gen, ts))))))))

# 984 "FStar.TypeChecker.Util.fst"
let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> if (let _150_858 = (FStar_Util.for_all (fun _69_1298 -> (match (_69_1298) with
| (_69_1296, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _150_858)) then begin
None
end else begin
(
# 988 "FStar.TypeChecker.Util.fst"
let norm = (fun c -> (
# 989 "FStar.TypeChecker.Util.fst"
let _69_1301 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _150_861 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _150_861))
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
let _69_1304 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _150_862 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _150_862))
end else begin
()
end
in c))))
in (
# 997 "FStar.TypeChecker.Util.fst"
let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (
# 998 "FStar.TypeChecker.Util.fst"
let gen_uvars = (fun uvs -> (let _150_865 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _150_865 FStar_Util.set_elements)))
in (
# 999 "FStar.TypeChecker.Util.fst"
let _69_1321 = (let _150_867 = (FStar_All.pipe_right ecs (FStar_List.map (fun _69_1311 -> (match (_69_1311) with
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
in (FStar_All.pipe_right _150_867 FStar_List.unzip))
in (match (_69_1321) with
| (univs, uvars) -> begin
(
# 1009 "FStar.TypeChecker.Util.fst"
let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (
# 1010 "FStar.TypeChecker.Util.fst"
let gen_univs = (gen_univs env univs)
in (
# 1011 "FStar.TypeChecker.Util.fst"
let _69_1325 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end else begin
()
end
in (
# 1013 "FStar.TypeChecker.Util.fst"
let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _69_1330 -> (match (_69_1330) with
| (uvs, e, c) -> begin
(
# 1014 "FStar.TypeChecker.Util.fst"
let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _69_1333 -> (match (_69_1333) with
| (u, k) -> begin
(match ((FStar_Unionfind.find u)) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(a, Some (FStar_Syntax_Syntax.imp_tag))
end
| FStar_Syntax_Syntax.Fixed (_69_1367) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _69_1370 -> begin
(
# 1020 "FStar.TypeChecker.Util.fst"
let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (
# 1021 "FStar.TypeChecker.Util.fst"
let _69_1374 = (FStar_Syntax_Util.arrow_formals k)
in (match (_69_1374) with
| (bs, kres) -> begin
(
# 1022 "FStar.TypeChecker.Util.fst"
let a = (let _150_873 = (let _150_872 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _150_871 -> Some (_150_871)) _150_872))
in (FStar_Syntax_Syntax.new_bv _150_873 kres))
in (
# 1023 "FStar.TypeChecker.Util.fst"
let t = (let _150_877 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _150_876 = (let _150_875 = (let _150_874 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _150_874))
in Some (_150_875))
in (FStar_Syntax_Util.abs bs _150_877 _150_876)))
in (
# 1024 "FStar.TypeChecker.Util.fst"
let _69_1377 = (FStar_Syntax_Util.set_uvar u t)
in (a, Some (FStar_Syntax_Syntax.imp_tag)))))
end)))
end)
end))))
in (
# 1028 "FStar.TypeChecker.Util.fst"
let _69_1398 = (match (tvars) with
| [] -> begin
(e, c)
end
| _69_1382 -> begin
(
# 1034 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]) env c)
in (
# 1035 "FStar.TypeChecker.Util.fst"
let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]) env e)
in (
# 1037 "FStar.TypeChecker.Util.fst"
let t = (match ((let _150_878 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _150_878.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(
# 1039 "FStar.TypeChecker.Util.fst"
let _69_1391 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (_69_1391) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| _69_1393 -> begin
(FStar_Syntax_Util.arrow tvars c)
end)
in (
# 1044 "FStar.TypeChecker.Util.fst"
let e' = (FStar_Syntax_Util.abs tvars e None)
in (let _150_879 = (FStar_Syntax_Syntax.mk_Total t)
in (e', _150_879))))))
end)
in (match (_69_1398) with
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
let _69_1408 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_886 = (let _150_885 = (FStar_List.map (fun _69_1407 -> (match (_69_1407) with
| (lb, _69_1404, _69_1406) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _150_885 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _150_886))
end else begin
()
end
in (match ((let _150_888 = (FStar_All.pipe_right lecs (FStar_List.map (fun _69_1414 -> (match (_69_1414) with
| (_69_1411, e, c) -> begin
(e, c)
end))))
in (gen env _150_888))) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun _69_1419 -> (match (_69_1419) with
| (l, t, c) -> begin
(l, [], t, c)
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _69_1427 _69_1431 -> (match ((_69_1427, _69_1431)) with
| ((l, _69_1424, _69_1426), (us, e, c)) -> begin
(
# 1057 "FStar.TypeChecker.Util.fst"
let _69_1432 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _150_894 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _150_893 = (FStar_Syntax_Print.lbname_to_string l)
in (let _150_892 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.print3 "(%s) Generalized %s to %s\n" _150_894 _150_893 _150_892))))
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
(let _150_910 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _150_909 -> Some (_150_909)) _150_910))
end)
end)
in (
# 1078 "FStar.TypeChecker.Util.fst"
let is_var = (fun e -> (match ((let _150_913 = (FStar_Syntax_Subst.compress e)
in _150_913.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (_69_1449) -> begin
true
end
| _69_1452 -> begin
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
let _69_1459 = x
in {FStar_Syntax_Syntax.ppname = _69_1459.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_1459.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| _69_1462 -> begin
(
# 1085 "FStar.TypeChecker.Util.fst"
let _69_1463 = e
in (let _150_918 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _69_1463.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _150_918; FStar_Syntax_Syntax.pos = _69_1463.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _69_1463.FStar_Syntax_Syntax.vars}))
end)))
in (
# 1086 "FStar.TypeChecker.Util.fst"
let env = (
# 1086 "FStar.TypeChecker.Util.fst"
let _69_1465 = env
in (let _150_919 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _69_1465.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _69_1465.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _69_1465.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _69_1465.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _69_1465.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _69_1465.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _69_1465.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _69_1465.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _69_1465.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _69_1465.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _69_1465.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _69_1465.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _69_1465.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _69_1465.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _69_1465.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _150_919; FStar_TypeChecker_Env.is_iface = _69_1465.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _69_1465.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _69_1465.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _69_1465.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _69_1465.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _69_1465.FStar_TypeChecker_Env.use_bv_sorts}))
in (match ((check env t1 t2)) with
| None -> begin
(let _150_923 = (let _150_922 = (let _150_921 = (FStar_TypeChecker_Errors.expected_expression_of_type env t2 e t1)
in (let _150_920 = (FStar_TypeChecker_Env.get_range env)
in (_150_921, _150_920)))
in FStar_Syntax_Syntax.Error (_150_922))
in (Prims.raise _150_923))
end
| Some (g) -> begin
(
# 1090 "FStar.TypeChecker.Util.fst"
let _69_1471 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _150_924 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _150_924))
end else begin
()
end
in (let _150_925 = (decorate e t2)
in (_150_925, g)))
end)))))))

# 1095 "FStar.TypeChecker.Util.fst"
let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (
# 1096 "FStar.TypeChecker.Util.fst"
let discharge = (fun g -> (
# 1097 "FStar.TypeChecker.Util.fst"
let _69_1478 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (
# 1099 "FStar.TypeChecker.Util.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _150_935 = (discharge g)
in (let _150_934 = (lc.FStar_Syntax_Syntax.comp ())
in (_150_935, _150_934)))
end else begin
(
# 1102 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 1103 "FStar.TypeChecker.Util.fst"
let steps = (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.DeltaComp)::[]
in (
# 1104 "FStar.TypeChecker.Util.fst"
let c = (let _150_936 = (FStar_TypeChecker_Normalize.normalize_comp steps env c)
in (FStar_All.pipe_right _150_936 FStar_Syntax_Util.comp_to_comp_typ))
in (
# 1105 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 1106 "FStar.TypeChecker.Util.fst"
let _69_1489 = (destruct_comp c)
in (match (_69_1489) with
| (t, wp, _69_1488) -> begin
(
# 1107 "FStar.TypeChecker.Util.fst"
let vc = (let _150_944 = (let _150_938 = (let _150_937 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_150_937)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _150_938 env md md.FStar_Syntax_Syntax.trivial))
in (let _150_943 = (let _150_941 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_940 = (let _150_939 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_939)::[])
in (_150_941)::_150_940))
in (let _150_942 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk_Tm_app _150_944 _150_943 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _150_942))))
in (
# 1108 "FStar.TypeChecker.Util.fst"
let _69_1491 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _150_945 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _150_945))
end else begin
()
end
in (
# 1110 "FStar.TypeChecker.Util.fst"
let g = (let _150_946 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _150_946))
in (let _150_948 = (discharge g)
in (let _150_947 = (FStar_Syntax_Syntax.mk_Comp c)
in (_150_948, _150_947))))))
end))))))
end)))

# 1116 "FStar.TypeChecker.Util.fst"
let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (
# 1117 "FStar.TypeChecker.Util.fst"
let short_bin_op = (fun f _69_5 -> (match (_69_5) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (fst, _69_1502)::[] -> begin
(f fst)
end
| _69_1506 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (
# 1122 "FStar.TypeChecker.Util.fst"
let op_and_e = (fun e -> (let _150_969 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _150_969 (fun _150_968 -> FStar_TypeChecker_Common.NonTrivial (_150_968)))))
in (
# 1123 "FStar.TypeChecker.Util.fst"
let op_or_e = (fun e -> (let _150_974 = (let _150_972 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _150_972))
in (FStar_All.pipe_right _150_974 (fun _150_973 -> FStar_TypeChecker_Common.NonTrivial (_150_973)))))
in (
# 1124 "FStar.TypeChecker.Util.fst"
let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _150_977 -> FStar_TypeChecker_Common.NonTrivial (_150_977))))
in (
# 1125 "FStar.TypeChecker.Util.fst"
let op_or_t = (fun t -> (let _150_981 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _150_981 (fun _150_980 -> FStar_TypeChecker_Common.NonTrivial (_150_980)))))
in (
# 1126 "FStar.TypeChecker.Util.fst"
let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _150_984 -> FStar_TypeChecker_Common.NonTrivial (_150_984))))
in (
# 1128 "FStar.TypeChecker.Util.fst"
let short_op_ite = (fun _69_6 -> (match (_69_6) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (guard, _69_1521)::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| _then::(guard, _69_1526)::[] -> begin
(let _150_988 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _150_988 (fun _150_987 -> FStar_TypeChecker_Common.NonTrivial (_150_987))))
end
| _69_1531 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (
# 1133 "FStar.TypeChecker.Util.fst"
let table = ((FStar_Syntax_Const.op_And, (short_bin_op op_and_e)))::((FStar_Syntax_Const.op_Or, (short_bin_op op_or_e)))::((FStar_Syntax_Const.and_lid, (short_bin_op op_and_t)))::((FStar_Syntax_Const.or_lid, (short_bin_op op_or_t)))::((FStar_Syntax_Const.imp_lid, (short_bin_op op_imp_t)))::((FStar_Syntax_Const.ite_lid, short_op_ite))::[]
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _69_1536) -> begin
(
# 1143 "FStar.TypeChecker.Util.fst"
let lid = fv.FStar_Syntax_Syntax.v
in (match ((FStar_Util.find_map table (fun _69_1542 -> (match (_69_1542) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _150_1021 = (mk seen_args)
in Some (_150_1021))
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
| _69_1547 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))

# 1150 "FStar.TypeChecker.Util.fst"
let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (match ((let _150_1024 = (FStar_Syntax_Subst.compress l)
in _150_1024.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (v, _69_1551) -> begin
(FStar_Util.for_some (FStar_Ident.lid_equals v.FStar_Syntax_Syntax.v) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| _69_1555 -> begin
false
end))

# 1171 "FStar.TypeChecker.Util.fst"
let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (
# 1172 "FStar.TypeChecker.Util.fst"
let pos = (fun bs -> (match (bs) with
| (hd, _69_1564)::_69_1561 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| _69_1568 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| (_69_1572, Some (FStar_Syntax_Syntax.Implicit (_69_1574)))::_69_1570 -> begin
bs
end
| _69_1580 -> begin
(match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
bs
end
| Some (t) -> begin
(match ((let _150_1031 = (FStar_Syntax_Subst.compress t)
in _150_1031.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', _69_1586) -> begin
(match ((FStar_Util.prefix_until (fun _69_7 -> (match (_69_7) with
| (_69_1591, Some (FStar_Syntax_Syntax.Implicit (_69_1593))) -> begin
false
end
| _69_1598 -> begin
true
end)) bs')) with
| None -> begin
bs
end
| Some ([], _69_1602, _69_1604) -> begin
bs
end
| Some (imps, _69_1609, _69_1611) -> begin
if (FStar_All.pipe_right imps (FStar_Util.for_all (fun _69_1617 -> (match (_69_1617) with
| (x, _69_1616) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end)))) then begin
(
# 1188 "FStar.TypeChecker.Util.fst"
let r = (pos bs)
in (
# 1189 "FStar.TypeChecker.Util.fst"
let imps = (FStar_All.pipe_right imps (FStar_List.map (fun _69_1621 -> (match (_69_1621) with
| (x, i) -> begin
(let _150_1035 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in (_150_1035, i))
end))))
in (FStar_List.append imps bs)))
end else begin
bs
end
end)
end
| _69_1624 -> begin
bs
end)
end)
end)))




