
open Prims
# 31 "FStar.TypeChecker.Util.fst"
type lcomp_with_binder =
(FStar_Syntax_Syntax.bv Prims.option * FStar_Syntax_Syntax.lcomp)

# 78 "FStar.TypeChecker.Util.fst"
let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _150_6 = (FStar_TypeChecker_Env.get_range env)
in (let _150_5 = (FStar_TypeChecker_Errors.failed_to_prove_specification errs)
in (FStar_TypeChecker_Errors.report _150_6 _150_5))))

# 85 "FStar.TypeChecker.Util.fst"
let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _150_9 = (FStar_Syntax_Subst.compress t)
in _150_9.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_69_12) -> begin
true
end
| _69_15 -> begin
false
end))

# 89 "FStar.TypeChecker.Util.fst"
let t_binders : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env -> (let _150_13 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right _150_13 (FStar_List.filter (fun _69_20 -> (match (_69_20) with
| (x, _69_19) -> begin
(is_type x.FStar_Syntax_Syntax.sort)
end))))))

# 93 "FStar.TypeChecker.Util.fst"
let new_uvar_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun env k -> (
# 94 "FStar.TypeChecker.Util.fst"
let bs = if (FStar_ST.read FStar_Options.full_context_dependency) then begin
(FStar_TypeChecker_Env.all_binders env)
end else begin
(t_binders env)
end
in (let _150_18 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Rel.new_uvar _150_18 bs k))))

# 99 "FStar.TypeChecker.Util.fst"
let new_uvar : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env k -> (let _150_23 = (new_uvar_aux env k)
in (Prims.fst _150_23)))

# 101 "FStar.TypeChecker.Util.fst"
let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun _69_1 -> (match (_69_1) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, _69_35); FStar_Syntax_Syntax.tk = _69_32; FStar_Syntax_Syntax.pos = _69_30; FStar_Syntax_Syntax.vars = _69_28} -> begin
uv
end
| _69_40 -> begin
(FStar_All.failwith "Impossible")
end))

# 105 "FStar.TypeChecker.Util.fst"
let new_implicit_var : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.uvar * FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env k -> (match ((FStar_Syntax_Util.destruct k FStar_Syntax_Const.range_of_lid)) with
| Some (_69_48::(tm, _69_45)::[]) -> begin
(
# 108 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))) None tm.FStar_Syntax_Syntax.pos)
in (t, [], FStar_TypeChecker_Rel.trivial_guard))
end
| _69_53 -> begin
(
# 112 "FStar.TypeChecker.Util.fst"
let _69_56 = (new_uvar_aux env k)
in (match (_69_56) with
| (t, u) -> begin
(
# 113 "FStar.TypeChecker.Util.fst"
let g = (
# 113 "FStar.TypeChecker.Util.fst"
let _69_57 = FStar_TypeChecker_Rel.trivial_guard
in (let _150_32 = (let _150_31 = (let _150_30 = (as_uvar u)
in (env, _150_30, t, k, u.FStar_Syntax_Syntax.pos))
in (_150_31)::[])
in {FStar_TypeChecker_Env.guard_f = _69_57.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _69_57.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _69_57.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _150_32}))
in (let _150_35 = (let _150_34 = (let _150_33 = (as_uvar u)
in (_150_33, u.FStar_Syntax_Syntax.pos))
in (_150_34)::[])
in (t, _150_35, g)))
end))
end))

# 116 "FStar.TypeChecker.Util.fst"
let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun r t -> (
# 117 "FStar.TypeChecker.Util.fst"
let uvs = (FStar_Syntax_Free.uvars t)
in if (not ((FStar_Util.set_is_empty uvs))) then begin
(
# 120 "FStar.TypeChecker.Util.fst"
let us = (let _150_42 = (let _150_41 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun _69_66 -> (match (_69_66) with
| (x, _69_65) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) _150_41))
in (FStar_All.pipe_right _150_42 (FStar_String.concat ", ")))
in (
# 122 "FStar.TypeChecker.Util.fst"
let hide_uvar_nums_saved = (FStar_ST.read FStar_Options.hide_uvar_nums)
in (
# 123 "FStar.TypeChecker.Util.fst"
let print_implicits_saved = (FStar_ST.read FStar_Options.print_implicits)
in (
# 124 "FStar.TypeChecker.Util.fst"
let _69_70 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums false)
in (
# 125 "FStar.TypeChecker.Util.fst"
let _69_72 = (FStar_ST.op_Colon_Equals FStar_Options.print_implicits true)
in (
# 126 "FStar.TypeChecker.Util.fst"
let _69_74 = (let _150_44 = (let _150_43 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us _150_43))
in (FStar_TypeChecker_Errors.report r _150_44))
in (
# 129 "FStar.TypeChecker.Util.fst"
let _69_76 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums hide_uvar_nums_saved)
in (FStar_ST.op_Colon_Equals FStar_Options.print_implicits print_implicits_saved))))))))
end else begin
()
end))

# 136 "FStar.TypeChecker.Util.fst"
let force_sort' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' = (fun s -> (match ((FStar_ST.read s.FStar_Syntax_Syntax.tk)) with
| None -> begin
(let _150_49 = (let _150_48 = (FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos)
in (let _150_47 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s" _150_48 _150_47)))
in (FStar_All.failwith _150_49))
end
| Some (tk) -> begin
tk
end))

# 140 "FStar.TypeChecker.Util.fst"
let force_sort = (fun s -> (let _150_51 = (force_sort' s)
in (FStar_Syntax_Syntax.mk _150_51 None s.FStar_Syntax_Syntax.pos)))

# 142 "FStar.TypeChecker.Util.fst"
let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env _69_91 -> (match (_69_91) with
| {FStar_Syntax_Syntax.lbname = _69_90; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _69_86; FStar_Syntax_Syntax.lbdef = e} -> begin
(
# 143 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 146 "FStar.TypeChecker.Util.fst"
let _69_94 = if (univ_vars <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (
# 147 "FStar.TypeChecker.Util.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 148 "FStar.TypeChecker.Util.fst"
let mk_binder = (fun scope a -> (match (a.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 150 "FStar.TypeChecker.Util.fst"
let _69_104 = (FStar_Syntax_Util.type_u ())
in (match (_69_104) with
| (k, _69_103) -> begin
(
# 151 "FStar.TypeChecker.Util.fst"
let t = (let _150_60 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right _150_60 Prims.fst))
in ((
# 152 "FStar.TypeChecker.Util.fst"
let _69_106 = a
in {FStar_Syntax_Syntax.ppname = _69_106.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_106.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), false))
end))
end
| _69_109 -> begin
(a, true)
end))
in (
# 155 "FStar.TypeChecker.Util.fst"
let rec aux = (fun vars e -> (
# 156 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, _69_116) -> begin
(aux vars e)
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _69_122) -> begin
(t, true)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _69_128) -> begin
(
# 162 "FStar.TypeChecker.Util.fst"
let _69_147 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _69_134 _69_137 -> (match ((_69_134, _69_137)) with
| ((scope, bs, check), (a, imp)) -> begin
(
# 163 "FStar.TypeChecker.Util.fst"
let _69_140 = (mk_binder scope a)
in (match (_69_140) with
| (tb, c) -> begin
(
# 164 "FStar.TypeChecker.Util.fst"
let b = (tb, imp)
in (
# 165 "FStar.TypeChecker.Util.fst"
let bs = (FStar_List.append bs ((b)::[]))
in (
# 166 "FStar.TypeChecker.Util.fst"
let scope = (FStar_List.append scope ((b)::[]))
in (scope, bs, (c || check)))))
end))
end)) (vars, [], false)))
in (match (_69_147) with
| (scope, bs, check) -> begin
(
# 170 "FStar.TypeChecker.Util.fst"
let _69_150 = (aux scope body)
in (match (_69_150) with
| (res, check_res) -> begin
(
# 171 "FStar.TypeChecker.Util.fst"
let c = (FStar_Syntax_Util.ml_comp res r)
in (
# 172 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Util.arrow bs c)
in (
# 173 "FStar.TypeChecker.Util.fst"
let _69_153 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_68 = (FStar_Range.string_of_range r)
in (let _150_67 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _150_68 _150_67)))
end else begin
()
end
in (t, (check_res || check)))))
end))
end))
end
| _69_156 -> begin
(let _150_70 = (let _150_69 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _150_69 Prims.fst))
in (_150_70, false))
end)))
in (
# 178 "FStar.TypeChecker.Util.fst"
let _69_159 = (let _150_71 = (t_binders env)
in (aux _150_71 e))
in (match (_69_159) with
| (t, b) -> begin
([], t, b)
end))))))
end
| _69_161 -> begin
(
# 182 "FStar.TypeChecker.Util.fst"
let _69_164 = (FStar_Syntax_Subst.open_univ_vars univ_vars t)
in (match (_69_164) with
| (univ_vars, t) -> begin
(univ_vars, t, false)
end))
end))
end))

# 193 "FStar.TypeChecker.Util.fst"
let pat_as_exps : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term Prims.list * FStar_Syntax_Syntax.pat) = (fun allow_implicits env p -> (
# 198 "FStar.TypeChecker.Util.fst"
let rec pat_as_arg_with_env = (fun allow_wc_dependence env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(
# 207 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) None p.FStar_Syntax_Syntax.p)
in ([], [], [], env, e, p))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _69_177) -> begin
(
# 211 "FStar.TypeChecker.Util.fst"
let _69_183 = (FStar_Syntax_Util.type_u ())
in (match (_69_183) with
| (k, _69_182) -> begin
(
# 212 "FStar.TypeChecker.Util.fst"
let t = (new_uvar env k)
in (
# 213 "FStar.TypeChecker.Util.fst"
let x = (
# 213 "FStar.TypeChecker.Util.fst"
let _69_185 = x
in {FStar_Syntax_Syntax.ppname = _69_185.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_185.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (
# 214 "FStar.TypeChecker.Util.fst"
let _69_190 = (let _150_84 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _150_84 t))
in (match (_69_190) with
| (e, u) -> begin
(
# 215 "FStar.TypeChecker.Util.fst"
let p = (
# 215 "FStar.TypeChecker.Util.fst"
let _69_191 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, e)); FStar_Syntax_Syntax.ty = _69_191.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _69_191.FStar_Syntax_Syntax.p})
in ([], [], [], env, e, p))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 219 "FStar.TypeChecker.Util.fst"
let _69_199 = (FStar_Syntax_Util.type_u ())
in (match (_69_199) with
| (t, _69_198) -> begin
(
# 220 "FStar.TypeChecker.Util.fst"
let x = (
# 220 "FStar.TypeChecker.Util.fst"
let _69_200 = x
in (let _150_85 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _69_200.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_200.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_85}))
in (
# 221 "FStar.TypeChecker.Util.fst"
let env = if allow_wc_dependence then begin
(FStar_TypeChecker_Env.push_bv env x)
end else begin
env
end
in (
# 222 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in ((x)::[], [], (x)::[], env, e, p))))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 226 "FStar.TypeChecker.Util.fst"
let _69_210 = (FStar_Syntax_Util.type_u ())
in (match (_69_210) with
| (t, _69_209) -> begin
(
# 227 "FStar.TypeChecker.Util.fst"
let x = (
# 227 "FStar.TypeChecker.Util.fst"
let _69_211 = x
in (let _150_86 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _69_211.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_211.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_86}))
in (
# 228 "FStar.TypeChecker.Util.fst"
let env = (FStar_TypeChecker_Env.push_bv env x)
in (
# 229 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in ((x)::[], (x)::[], [], env, e, p))))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 233 "FStar.TypeChecker.Util.fst"
let _69_244 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _69_226 _69_229 -> (match ((_69_226, _69_229)) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(
# 234 "FStar.TypeChecker.Util.fst"
let _69_236 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_69_236) with
| (b', a', w', env, te, pat) -> begin
(
# 235 "FStar.TypeChecker.Util.fst"
let arg = if imp then begin
(FStar_Syntax_Syntax.iarg te)
end else begin
(FStar_Syntax_Syntax.as_arg te)
end
in ((b')::b, (a')::a, (w')::w, env, (arg)::args, ((pat, imp))::pats))
end))
end)) ([], [], [], env, [], [])))
in (match (_69_244) with
| (b, a, w, env, args, pats) -> begin
(
# 238 "FStar.TypeChecker.Util.fst"
let e = (let _150_93 = (let _150_92 = (let _150_91 = (let _150_90 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (let _150_89 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app _150_90 _150_89 None p.FStar_Syntax_Syntax.p)))
in (_150_91, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))
in FStar_Syntax_Syntax.Tm_meta (_150_92))
in (FStar_Syntax_Syntax.mk _150_93 None p.FStar_Syntax_Syntax.p))
in (let _150_96 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _150_95 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _150_94 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in (_150_96, _150_95, _150_94, env, e, (
# 244 "FStar.TypeChecker.Util.fst"
let _69_246 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _69_246.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _69_246.FStar_Syntax_Syntax.p}))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (_69_249) -> begin
(FStar_All.failwith "impossible")
end))
in (
# 248 "FStar.TypeChecker.Util.fst"
let rec elaborate_pat = (fun env p -> (
# 249 "FStar.TypeChecker.Util.fst"
let maybe_dot = (fun inaccessible a r -> if (allow_implicits && inaccessible) then begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term ((a, FStar_Syntax_Syntax.tun))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end else begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var (a)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end)
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 255 "FStar.TypeChecker.Util.fst"
let pats = (FStar_List.map (fun _69_264 -> (match (_69_264) with
| (p, imp) -> begin
(let _150_108 = (elaborate_pat env p)
in (_150_108, imp))
end)) pats)
in (
# 256 "FStar.TypeChecker.Util.fst"
let _69_269 = (FStar_TypeChecker_Env.lookup_datacon env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_69_269) with
| (_69_267, t) -> begin
(
# 257 "FStar.TypeChecker.Util.fst"
let _69_273 = (FStar_Syntax_Util.arrow_formals t)
in (match (_69_273) with
| (f, _69_272) -> begin
(
# 258 "FStar.TypeChecker.Util.fst"
let rec aux = (fun formals pats -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _69_284::_69_282) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))))
end
| (_69_290::_69_288, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun _69_296 -> (match (_69_296) with
| (t, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(
# 264 "FStar.TypeChecker.Util.fst"
let a = (let _150_115 = (let _150_114 = (FStar_Syntax_Syntax.range_of_bv t)
in Some (_150_114))
in (FStar_Syntax_Syntax.new_bv _150_115 FStar_Syntax_Syntax.tun))
in (
# 265 "FStar.TypeChecker.Util.fst"
let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (let _150_116 = (maybe_dot inaccessible a r)
in (_150_116, true))))
end
| _69_303 -> begin
(let _150_120 = (let _150_119 = (let _150_118 = (let _150_117 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _150_117))
in (_150_118, (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in FStar_Syntax_Syntax.Error (_150_119))
in (Prims.raise _150_120))
end)
end))))
end
| (f::formals', (p, p_imp)::pats') -> begin
(match (f) with
| (_69_314, Some (FStar_Syntax_Syntax.Implicit (_69_316))) when p_imp -> begin
(let _150_121 = (aux formals' pats')
in ((p, true))::_150_121)
end
| (_69_321, Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(
# 277 "FStar.TypeChecker.Util.fst"
let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (
# 278 "FStar.TypeChecker.Util.fst"
let p = (maybe_dot inaccessible a (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
in (let _150_122 = (aux formals' pats)
in ((p, true))::_150_122)))
end
| (_69_329, imp) -> begin
(let _150_125 = (let _150_123 = (FStar_Syntax_Syntax.is_implicit imp)
in (p, _150_123))
in (let _150_124 = (aux formals' pats')
in (_150_125)::_150_124))
end)
end))
in (
# 284 "FStar.TypeChecker.Util.fst"
let _69_332 = p
in (let _150_128 = (let _150_127 = (let _150_126 = (aux f pats)
in (fv, _150_126))
in FStar_Syntax_Syntax.Pat_cons (_150_127))
in {FStar_Syntax_Syntax.v = _150_128; FStar_Syntax_Syntax.ty = _69_332.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _69_332.FStar_Syntax_Syntax.p})))
end))
end)))
end
| _69_335 -> begin
p
end)))
in (
# 288 "FStar.TypeChecker.Util.fst"
let one_pat = (fun allow_wc_dependence env p -> (
# 289 "FStar.TypeChecker.Util.fst"
let p = (elaborate_pat env p)
in (
# 290 "FStar.TypeChecker.Util.fst"
let _69_347 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_69_347) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))) with
| Some (x) -> begin
(let _150_137 = (let _150_136 = (let _150_135 = (FStar_TypeChecker_Errors.nonlinear_pattern_variable x)
in (_150_135, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_150_136))
in (Prims.raise _150_137))
end
| _69_351 -> begin
(b, a, w, arg, p)
end)
end))))
in (
# 295 "FStar.TypeChecker.Util.fst"
let top_level_pat_as_args = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_disj (q::pats) -> begin
(
# 302 "FStar.TypeChecker.Util.fst"
let _69_367 = (one_pat false env q)
in (match (_69_367) with
| (b, a, _69_364, te, q) -> begin
(
# 303 "FStar.TypeChecker.Util.fst"
let _69_382 = (FStar_List.fold_right (fun p _69_372 -> (match (_69_372) with
| (w, args, pats) -> begin
(
# 304 "FStar.TypeChecker.Util.fst"
let _69_378 = (one_pat false env p)
in (match (_69_378) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv FStar_Syntax_Syntax.bv_eq a a'))) then begin
(let _150_147 = (let _150_146 = (let _150_145 = (FStar_TypeChecker_Errors.disjunctive_pattern_vars a a')
in (let _150_144 = (FStar_TypeChecker_Env.get_range env)
in (_150_145, _150_144)))
in FStar_Syntax_Syntax.Error (_150_146))
in (Prims.raise _150_147))
end else begin
(let _150_149 = (let _150_148 = (FStar_Syntax_Syntax.as_arg arg)
in (_150_148)::args)
in ((FStar_List.append w' w), _150_149, (p)::pats))
end
end))
end)) pats ([], [], []))
in (match (_69_382) with
| (w, args, pats) -> begin
(let _150_151 = (let _150_150 = (FStar_Syntax_Syntax.as_arg te)
in (_150_150)::args)
in ((FStar_List.append b w), _150_151, (
# 309 "FStar.TypeChecker.Util.fst"
let _69_383 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((q)::pats); FStar_Syntax_Syntax.ty = _69_383.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _69_383.FStar_Syntax_Syntax.p})))
end))
end))
end
| _69_386 -> begin
(
# 312 "FStar.TypeChecker.Util.fst"
let _69_394 = (one_pat true env p)
in (match (_69_394) with
| (b, _69_389, _69_391, arg, p) -> begin
(let _150_153 = (let _150_152 = (FStar_Syntax_Syntax.as_arg arg)
in (_150_152)::[])
in (b, _150_153, p))
end))
end))
in (
# 315 "FStar.TypeChecker.Util.fst"
let _69_398 = (top_level_pat_as_args env p)
in (match (_69_398) with
| (b, args, p) -> begin
(
# 316 "FStar.TypeChecker.Util.fst"
let exps = (FStar_All.pipe_right args (FStar_List.map Prims.fst))
in (b, exps, p))
end)))))))

# 319 "FStar.TypeChecker.Util.fst"
let decorate_pattern : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.pat = (fun env p exps -> (
# 320 "FStar.TypeChecker.Util.fst"
let qq = p
in (
# 321 "FStar.TypeChecker.Util.fst"
let rec aux = (fun p e -> (
# 322 "FStar.TypeChecker.Util.fst"
let pkg = (fun q t -> (FStar_Syntax_Syntax.withinfo q t p.FStar_Syntax_Syntax.p))
in (
# 323 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Util.unmeta e)
in (match ((p.FStar_Syntax_Syntax.v, e.FStar_Syntax_Syntax.n)) with
| (_69_412, FStar_Syntax_Syntax.Tm_uinst (e, _69_415)) -> begin
(aux p e)
end
| (FStar_Syntax_Syntax.Pat_constant (_69_420), FStar_Syntax_Syntax.Tm_constant (_69_423)) -> begin
(let _150_168 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v _150_168))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(
# 331 "FStar.TypeChecker.Util.fst"
let _69_431 = if (not ((FStar_Syntax_Syntax.bv_eq x y))) then begin
(let _150_171 = (let _150_170 = (FStar_Syntax_Print.bv_to_string x)
in (let _150_169 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _150_170 _150_169)))
in (FStar_All.failwith _150_171))
end else begin
()
end
in (
# 333 "FStar.TypeChecker.Util.fst"
let _69_433 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _150_173 = (FStar_Syntax_Print.bv_to_string x)
in (let _150_172 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _150_173 _150_172)))
end else begin
()
end
in (
# 335 "FStar.TypeChecker.Util.fst"
let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (
# 336 "FStar.TypeChecker.Util.fst"
let x = (
# 336 "FStar.TypeChecker.Util.fst"
let _69_436 = x
in {FStar_Syntax_Syntax.ppname = _69_436.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_436.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x)) s.FStar_Syntax_Syntax.n)))))
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(
# 340 "FStar.TypeChecker.Util.fst"
let _69_444 = if (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation) then begin
(let _150_176 = (let _150_175 = (FStar_Syntax_Print.bv_to_string x)
in (let _150_174 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _150_175 _150_174)))
in (FStar_All.failwith _150_176))
end else begin
()
end
in (
# 342 "FStar.TypeChecker.Util.fst"
let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (
# 343 "FStar.TypeChecker.Util.fst"
let x = (
# 343 "FStar.TypeChecker.Util.fst"
let _69_447 = x
in {FStar_Syntax_Syntax.ppname = _69_447.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_447.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x)) s.FStar_Syntax_Syntax.n))))
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _69_452), _69_456) -> begin
(
# 347 "FStar.TypeChecker.Util.fst"
let s = (force_sort e)
in (
# 348 "FStar.TypeChecker.Util.fst"
let x = (
# 348 "FStar.TypeChecker.Util.fst"
let _69_459 = x
in {FStar_Syntax_Syntax.ppname = _69_459.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_459.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
(
# 352 "FStar.TypeChecker.Util.fst"
let _69_469 = if (not ((FStar_Syntax_Syntax.fv_eq fv fv'))) then begin
(let _150_177 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _150_177))
end else begin
()
end
in (let _150_178 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv', []))) _150_178)))
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
(
# 359 "FStar.TypeChecker.Util.fst"
let _69_512 = if (let _150_179 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right _150_179 Prims.op_Negation)) then begin
(let _150_180 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _150_180))
end else begin
()
end
in (
# 362 "FStar.TypeChecker.Util.fst"
let fv = fv'
in (
# 363 "FStar.TypeChecker.Util.fst"
let rec match_args = (fun matched_pats args argpats -> (match ((args, argpats)) with
| ([], []) -> begin
(let _150_187 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev matched_pats)))) _150_187))
end
| (arg::args, (argpat, _69_528)::argpats) -> begin
(match ((arg, argpat.FStar_Syntax_Syntax.v)) with
| ((e, Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (_69_538)) -> begin
(
# 368 "FStar.TypeChecker.Util.fst"
let x = (let _150_188 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _150_188))
in (
# 369 "FStar.TypeChecker.Util.fst"
let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((e, imp), _69_547) -> begin
(
# 373 "FStar.TypeChecker.Util.fst"
let pat = (let _150_190 = (aux argpat e)
in (let _150_189 = (FStar_Syntax_Syntax.is_implicit imp)
in (_150_190, _150_189)))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _69_551 -> begin
(let _150_193 = (let _150_192 = (FStar_Syntax_Print.pat_to_string p)
in (let _150_191 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _150_192 _150_191)))
in (FStar_All.failwith _150_193))
end))
in (match_args [] args argpats))))
end
| _69_553 -> begin
(let _150_198 = (let _150_197 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (let _150_196 = (FStar_Syntax_Print.pat_to_string qq)
in (let _150_195 = (let _150_194 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right _150_194 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _150_197 _150_196 _150_195))))
in (FStar_All.failwith _150_198))
end))))
in (match ((p.FStar_Syntax_Syntax.v, exps)) with
| (FStar_Syntax_Syntax.Pat_disj (ps), _69_557) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(
# 386 "FStar.TypeChecker.Util.fst"
let ps = (FStar_List.map2 aux ps exps)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj (ps)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p))
end
| (_69_561, e::[]) -> begin
(aux p e)
end
| _69_566 -> begin
(FStar_All.failwith "Unexpected number of patterns")
end))))

# 394 "FStar.TypeChecker.Util.fst"
let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (
# 395 "FStar.TypeChecker.Util.fst"
let topt = Some (pat.FStar_Syntax_Syntax.ty)
in (
# 396 "FStar.TypeChecker.Util.fst"
let mk = (fun f -> (FStar_Syntax_Syntax.mk f topt pat.FStar_Syntax_Syntax.p))
in (
# 398 "FStar.TypeChecker.Util.fst"
let pat_as_arg = (fun _69_574 -> (match (_69_574) with
| (p, i) -> begin
(
# 399 "FStar.TypeChecker.Util.fst"
let _69_577 = (decorated_pattern_as_term p)
in (match (_69_577) with
| (vars, te) -> begin
(let _150_206 = (let _150_205 = (FStar_Syntax_Syntax.as_implicit i)
in (te, _150_205))
in (vars, _150_206))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_69_579) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _150_207 = (mk (FStar_Syntax_Syntax.Tm_constant (c)))
in ([], _150_207))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(let _150_208 = (mk (FStar_Syntax_Syntax.Tm_name (x)))
in ((x)::[], _150_208))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 413 "FStar.TypeChecker.Util.fst"
let _69_592 = (let _150_209 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _150_209 FStar_List.unzip))
in (match (_69_592) with
| (vars, args) -> begin
(
# 414 "FStar.TypeChecker.Util.fst"
let vars = (FStar_List.flatten vars)
in (let _150_213 = (let _150_212 = (let _150_211 = (let _150_210 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (_150_210, args))
in FStar_Syntax_Syntax.Tm_app (_150_211))
in (mk _150_212))
in (vars, _150_213)))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
([], e)
end)))))

# 424 "FStar.TypeChecker.Util.fst"
let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (
# 425 "FStar.TypeChecker.Util.fst"
let _69_616 = (match (c.FStar_Syntax_Syntax.effect_args) with
| (wp, _69_605)::(wlp, _69_601)::[] -> begin
(wp, wlp)
end
| _69_609 -> begin
(let _150_219 = (let _150_218 = (let _150_217 = (FStar_List.map (fun _69_613 -> (match (_69_613) with
| (x, _69_612) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right _150_217 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str _150_218))
in (FStar_All.failwith _150_219))
end)
in (match (_69_616) with
| (wp, wlp) -> begin
(c.FStar_Syntax_Syntax.result_typ, wp, wlp)
end)))

# 431 "FStar.TypeChecker.Util.fst"
let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (
# 432 "FStar.TypeChecker.Util.fst"
let _69_624 = (destruct_comp c)
in (match (_69_624) with
| (_69_621, wp, wlp) -> begin
(let _150_241 = (let _150_240 = (let _150_236 = (lift c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _150_236))
in (let _150_239 = (let _150_238 = (let _150_237 = (lift c.FStar_Syntax_Syntax.result_typ wlp)
in (FStar_Syntax_Syntax.as_arg _150_237))
in (_150_238)::[])
in (_150_240)::_150_239))
in {FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _150_241; FStar_Syntax_Syntax.flags = []})
end)))

# 438 "FStar.TypeChecker.Util.fst"
let norm_eff_name : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (
# 439 "FStar.TypeChecker.Util.fst"
let cache = (FStar_Util.smap_create 20)
in (fun env l -> (
# 441 "FStar.TypeChecker.Util.fst"
let rec find = (fun l -> (match ((FStar_TypeChecker_Env.lookup_effect_abbrev env FStar_Syntax_Syntax.U_unknown l)) with
| None -> begin
None
end
| Some (_69_632, c) -> begin
(
# 445 "FStar.TypeChecker.Util.fst"
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
# 449 "FStar.TypeChecker.Util.fst"
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
# 454 "FStar.TypeChecker.Util.fst"
let _69_646 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))

# 460 "FStar.TypeChecker.Util.fst"
let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (
# 461 "FStar.TypeChecker.Util.fst"
let _69_657 = (let _150_255 = (norm_eff_name env l1)
in (let _150_254 = (norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _150_255 _150_254)))
in (match (_69_657) with
| (m, _69_654, _69_656) -> begin
m
end)))

# 464 "FStar.TypeChecker.Util.fst"
let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> if ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2)) then begin
FStar_Syntax_Const.effect_Tot_lid
end else begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)

# 470 "FStar.TypeChecker.Util.fst"
let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)) = (fun env c1 c2 -> (
# 471 "FStar.TypeChecker.Util.fst"
let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (
# 472 "FStar.TypeChecker.Util.fst"
let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (
# 473 "FStar.TypeChecker.Util.fst"
let _69_669 = (FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (_69_669) with
| (m, lift1, lift2) -> begin
(
# 474 "FStar.TypeChecker.Util.fst"
let m1 = (lift_comp c1 m lift1)
in (
# 475 "FStar.TypeChecker.Util.fst"
let m2 = (lift_comp c2 m lift2)
in (
# 476 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (
# 477 "FStar.TypeChecker.Util.fst"
let _69_675 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (_69_675) with
| (a, kwp) -> begin
(let _150_269 = (destruct_comp m1)
in (let _150_268 = (destruct_comp m2)
in ((md, a, kwp), _150_269, _150_268)))
end)))))
end)))))

# 480 "FStar.TypeChecker.Util.fst"
let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (
# 481 "FStar.TypeChecker.Util.fst"
let l = (norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)))

# 484 "FStar.TypeChecker.Util.fst"
let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (
# 485 "FStar.TypeChecker.Util.fst"
let l = (norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid))))

# 489 "FStar.TypeChecker.Util.fst"
let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md result wp wlp flags -> (let _150_292 = (let _150_291 = (let _150_290 = (FStar_Syntax_Syntax.as_arg wp)
in (let _150_289 = (let _150_288 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_288)::[])
in (_150_290)::_150_289))
in {FStar_Syntax_Syntax.effect_name = md.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = _150_291; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp _150_292)))

# 495 "FStar.TypeChecker.Util.fst"
let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (
# 496 "FStar.TypeChecker.Util.fst"
let _69_689 = lc
in (let _150_299 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _69_689.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _150_299; FStar_Syntax_Syntax.cflags = _69_689.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _69_691 -> (match (()) with
| () -> begin
(let _150_298 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _150_298))
end))})))

# 499 "FStar.TypeChecker.Util.fst"
let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _150_302 = (FStar_Syntax_Subst.compress t)
in _150_302.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_69_694) -> begin
true
end
| _69_697 -> begin
false
end))

# 503 "FStar.TypeChecker.Util.fst"
let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v -> (
# 505 "FStar.TypeChecker.Util.fst"
let c = if (let _150_309 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation _150_309)) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(
# 508 "FStar.TypeChecker.Util.fst"
let m = (let _150_310 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must _150_310))
in (
# 509 "FStar.TypeChecker.Util.fst"
let _69_704 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_69_704) with
| (a, kwp) -> begin
(
# 510 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 511 "FStar.TypeChecker.Util.fst"
let wp = (let _150_318 = (let _150_317 = (let _150_312 = (let _150_311 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_150_311)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _150_312 env m m.FStar_Syntax_Syntax.ret))
in (let _150_316 = (let _150_315 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_314 = (let _150_313 = (FStar_Syntax_Syntax.as_arg v)
in (_150_313)::[])
in (_150_315)::_150_314))
in (FStar_Syntax_Syntax.mk_Tm_app _150_317 _150_316 (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _150_318))
in (
# 512 "FStar.TypeChecker.Util.fst"
let wlp = wp
in (mk_comp m t wp wlp ((FStar_Syntax_Syntax.RETURN)::[])))))
end)))
end
in (
# 514 "FStar.TypeChecker.Util.fst"
let _69_709 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return"))) then begin
(let _150_321 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _150_320 = (FStar_Syntax_Print.term_to_string v)
in (let _150_319 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _150_321 _150_320 _150_319))))
end else begin
()
end
in c)))

# 519 "FStar.TypeChecker.Util.fst"
let bind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun env e1opt lc1 _69_716 -> (match (_69_716) with
| (b, lc2) -> begin
(
# 520 "FStar.TypeChecker.Util.fst"
let _69_724 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(
# 522 "FStar.TypeChecker.Util.fst"
let bstr = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _150_332 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (let _150_331 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _150_330 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" _150_332 _150_331 bstr _150_330)))))
end else begin
()
end
in (
# 528 "FStar.TypeChecker.Util.fst"
let bind_it = (fun _69_727 -> (match (()) with
| () -> begin
(
# 529 "FStar.TypeChecker.Util.fst"
let c1 = (lc1.FStar_Syntax_Syntax.comp ())
in (
# 530 "FStar.TypeChecker.Util.fst"
let c2 = (lc2.FStar_Syntax_Syntax.comp ())
in (
# 531 "FStar.TypeChecker.Util.fst"
let _69_733 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_339 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _150_338 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _150_337 = (FStar_Syntax_Print.comp_to_string c1)
in (let _150_336 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (let _150_335 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" _150_339 _150_338 _150_337 _150_336 _150_335))))))
end else begin
()
end
in (
# 540 "FStar.TypeChecker.Util.fst"
let try_simplify = (fun _69_736 -> (match (()) with
| () -> begin
(
# 541 "FStar.TypeChecker.Util.fst"
let aux = (fun _69_738 -> (match (()) with
| () -> begin
if (FStar_Syntax_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some ((c2, "trivial no binder"))
end
| Some (_69_741) -> begin
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
(let _150_345 = (let _150_344 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in (_150_344, "both gtot"))
in Some (_150_345))
end else begin
(match ((e1opt, b)) with
| (Some (e), Some (x)) -> begin
if ((FStar_Syntax_Util.is_total_comp c1) && (not ((FStar_Syntax_Syntax.is_null_bv x)))) then begin
(let _150_347 = (let _150_346 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT ((x, e)))::[]) c2)
in (_150_346, "substituted e"))
in Some (_150_347))
end else begin
(aux ())
end
end
| _69_749 -> begin
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
# 568 "FStar.TypeChecker.Util.fst"
let _69_767 = (lift_and_destruct env c1 c2)
in (match (_69_767) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(
# 569 "FStar.TypeChecker.Util.fst"
let bs = (match (b) with
| None -> begin
(let _150_348 = (FStar_Syntax_Syntax.null_binder t1)
in (_150_348)::[])
end
| Some (x) -> begin
(let _150_349 = (FStar_Syntax_Syntax.mk_binder x)
in (_150_349)::[])
end)
in (
# 572 "FStar.TypeChecker.Util.fst"
let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp None))
in (
# 573 "FStar.TypeChecker.Util.fst"
let wp_args = (let _150_364 = (FStar_Syntax_Syntax.as_arg t1)
in (let _150_363 = (let _150_362 = (FStar_Syntax_Syntax.as_arg t2)
in (let _150_361 = (let _150_360 = (FStar_Syntax_Syntax.as_arg wp1)
in (let _150_359 = (let _150_358 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _150_357 = (let _150_356 = (let _150_352 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg _150_352))
in (let _150_355 = (let _150_354 = (let _150_353 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _150_353))
in (_150_354)::[])
in (_150_356)::_150_355))
in (_150_358)::_150_357))
in (_150_360)::_150_359))
in (_150_362)::_150_361))
in (_150_364)::_150_363))
in (
# 574 "FStar.TypeChecker.Util.fst"
let wlp_args = (let _150_372 = (FStar_Syntax_Syntax.as_arg t1)
in (let _150_371 = (let _150_370 = (FStar_Syntax_Syntax.as_arg t2)
in (let _150_369 = (let _150_368 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _150_367 = (let _150_366 = (let _150_365 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _150_365))
in (_150_366)::[])
in (_150_368)::_150_367))
in (_150_370)::_150_369))
in (_150_372)::_150_371))
in (
# 575 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t2)))::[]) kwp)
in (
# 576 "FStar.TypeChecker.Util.fst"
let us = (let _150_375 = (env.FStar_TypeChecker_Env.universe_of env t1)
in (let _150_374 = (let _150_373 = (env.FStar_TypeChecker_Env.universe_of env t2)
in (_150_373)::[])
in (_150_375)::_150_374))
in (
# 577 "FStar.TypeChecker.Util.fst"
let wp = (let _150_376 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _150_376 wp_args None t2.FStar_Syntax_Syntax.pos))
in (
# 578 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_377 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wlp)
in (FStar_Syntax_Syntax.mk_Tm_app _150_377 wlp_args None t2.FStar_Syntax_Syntax.pos))
in (
# 579 "FStar.TypeChecker.Util.fst"
let c = (mk_comp md t2 wp wlp [])
in c)))))))))
end))
end)))))
end))
in (let _150_378 = (join_lcomp env lc1 lc2)
in {FStar_Syntax_Syntax.eff_name = _150_378; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it})))
end))

# 586 "FStar.TypeChecker.Util.fst"
let lift_formula : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t mk_wp mk_wlp f -> (
# 587 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 588 "FStar.TypeChecker.Util.fst"
let _69_789 = (FStar_TypeChecker_Env.wp_signature env md_pure.FStar_Syntax_Syntax.mname)
in (match (_69_789) with
| (a, kwp) -> begin
(
# 589 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 590 "FStar.TypeChecker.Util.fst"
let wp = (let _150_392 = (let _150_391 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_390 = (let _150_389 = (FStar_Syntax_Syntax.as_arg f)
in (_150_389)::[])
in (_150_391)::_150_390))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wp _150_392 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (
# 591 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_396 = (let _150_395 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_394 = (let _150_393 = (FStar_Syntax_Syntax.as_arg f)
in (_150_393)::[])
in (_150_395)::_150_394))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wlp _150_396 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (mk_comp md_pure FStar_TypeChecker_Common.t_unit wp wlp []))))
end))))

# 594 "FStar.TypeChecker.Util.fst"
let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((f, FStar_Syntax_Syntax.Meta_labeled ((reason, r, false))))) None f.FStar_Syntax_Syntax.pos))

# 597 "FStar.TypeChecker.Util.fst"
let label_opt : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _150_420 = (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)
in (FStar_All.pipe_left Prims.op_Negation _150_420)) then begin
f
end else begin
(let _150_421 = (reason ())
in (label _150_421 r f))
end
end))

# 604 "FStar.TypeChecker.Util.fst"
let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 606 "FStar.TypeChecker.Util.fst"
let _69_809 = g
in (let _150_429 = (let _150_428 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_150_428))
in {FStar_TypeChecker_Env.guard_f = _150_429; FStar_TypeChecker_Env.deferred = _69_809.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _69_809.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _69_809.FStar_TypeChecker_Env.implicits}))
end))

# 608 "FStar.TypeChecker.Util.fst"
let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(
# 610 "FStar.TypeChecker.Util.fst"
let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| _69_820 -> begin
g2
end))

# 614 "FStar.TypeChecker.Util.fst"
let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (
# 615 "FStar.TypeChecker.Util.fst"
let weaken = (fun _69_825 -> (match (()) with
| () -> begin
(
# 616 "FStar.TypeChecker.Util.fst"
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
# 622 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 623 "FStar.TypeChecker.Util.fst"
let _69_834 = (destruct_comp c)
in (match (_69_834) with
| (res_t, wp, wlp) -> begin
(
# 624 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 625 "FStar.TypeChecker.Util.fst"
let us = (let _150_442 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_442)::[])
in (
# 626 "FStar.TypeChecker.Util.fst"
let wp = (let _150_449 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _150_448 = (let _150_447 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_446 = (let _150_445 = (FStar_Syntax_Syntax.as_arg f)
in (let _150_444 = (let _150_443 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_443)::[])
in (_150_445)::_150_444))
in (_150_447)::_150_446))
in (FStar_Syntax_Syntax.mk_Tm_app _150_449 _150_448 None wp.FStar_Syntax_Syntax.pos)))
in (
# 627 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_456 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _150_455 = (let _150_454 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_453 = (let _150_452 = (FStar_Syntax_Syntax.as_arg f)
in (let _150_451 = (let _150_450 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_450)::[])
in (_150_452)::_150_451))
in (_150_454)::_150_453))
in (FStar_Syntax_Syntax.mk_Tm_app _150_456 _150_455 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp c.FStar_Syntax_Syntax.flags)))))
end)))
end
end))
end))
in (
# 629 "FStar.TypeChecker.Util.fst"
let _69_839 = lc
in {FStar_Syntax_Syntax.eff_name = _69_839.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _69_839.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _69_839.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))

# 631 "FStar.TypeChecker.Util.fst"
let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> if (FStar_TypeChecker_Rel.is_trivial g0) then begin
(lc, g0)
end else begin
(
# 635 "FStar.TypeChecker.Util.fst"
let _69_846 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_476 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _150_475 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _150_476 _150_475)))
end else begin
()
end
in (
# 639 "FStar.TypeChecker.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _69_2 -> (match (_69_2) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _69_852 -> begin
[]
end))))
in (
# 640 "FStar.TypeChecker.Util.fst"
let strengthen = (fun _69_855 -> (match (()) with
| () -> begin
(
# 641 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 642 "FStar.TypeChecker.Util.fst"
let g0 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (match ((FStar_TypeChecker_Rel.guard_form g0)) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 646 "FStar.TypeChecker.Util.fst"
let c = if ((FStar_Syntax_Util.is_pure_or_ghost_comp c) && (not ((FStar_Syntax_Util.is_partial_return c)))) then begin
(
# 649 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.gen_bv "strengthen_pre_x" None (FStar_Syntax_Util.comp_result c))
in (
# 650 "FStar.TypeChecker.Util.fst"
let xret = (let _150_481 = (let _150_480 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _150_480))
in (FStar_Syntax_Util.comp_set_flags _150_481 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (
# 651 "FStar.TypeChecker.Util.fst"
let lc = (bind env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), (FStar_Syntax_Util.lcomp_of_comp xret)))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (
# 655 "FStar.TypeChecker.Util.fst"
let _69_865 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_483 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _150_482 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _150_483 _150_482)))
end else begin
()
end
in (
# 660 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 661 "FStar.TypeChecker.Util.fst"
let _69_871 = (destruct_comp c)
in (match (_69_871) with
| (res_t, wp, wlp) -> begin
(
# 662 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 663 "FStar.TypeChecker.Util.fst"
let us = (let _150_484 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_484)::[])
in (
# 664 "FStar.TypeChecker.Util.fst"
let wp = (let _150_493 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assert_p)
in (let _150_492 = (let _150_491 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_490 = (let _150_489 = (let _150_486 = (let _150_485 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason _150_485 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _150_486))
in (let _150_488 = (let _150_487 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_487)::[])
in (_150_489)::_150_488))
in (_150_491)::_150_490))
in (FStar_Syntax_Syntax.mk_Tm_app _150_493 _150_492 None wp.FStar_Syntax_Syntax.pos)))
in (
# 665 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_500 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _150_499 = (let _150_498 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_497 = (let _150_496 = (FStar_Syntax_Syntax.as_arg f)
in (let _150_495 = (let _150_494 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_494)::[])
in (_150_496)::_150_495))
in (_150_498)::_150_497))
in (FStar_Syntax_Syntax.mk_Tm_app _150_500 _150_499 None wlp.FStar_Syntax_Syntax.pos)))
in (
# 667 "FStar.TypeChecker.Util.fst"
let _69_876 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_501 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _150_501))
end else begin
()
end
in (
# 671 "FStar.TypeChecker.Util.fst"
let c2 = (mk_comp md res_t wp wlp flags)
in c2))))))
end)))))
end)))
end))
in (let _150_505 = (
# 673 "FStar.TypeChecker.Util.fst"
let _69_879 = lc
in (let _150_504 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _150_503 = if ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _150_502 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _150_502))) then begin
flags
end else begin
[]
end
in {FStar_Syntax_Syntax.eff_name = _150_504; FStar_Syntax_Syntax.res_typ = _69_879.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _150_503; FStar_Syntax_Syntax.comp = strengthen})))
in (_150_505, (
# 676 "FStar.TypeChecker.Util.fst"
let _69_881 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _69_881.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _69_881.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _69_881.FStar_TypeChecker_Env.implicits}))))))
end)

# 678 "FStar.TypeChecker.Util.fst"
let record_application_site : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (
# 679 "FStar.TypeChecker.Util.fst"
let comp = (fun _69_887 -> (match (()) with
| () -> begin
(
# 680 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 681 "FStar.TypeChecker.Util.fst"
let res_t = (FStar_Syntax_Util.comp_result c)
in if (((FStar_Syntax_Util.is_trivial_wp c) || (let _150_514 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals _150_514 FStar_Syntax_Const.prims_lid))) || (FStar_Syntax_Syntax.is_teff res_t)) then begin
c
end else begin
(
# 686 "FStar.TypeChecker.Util.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (FStar_TypeChecker_Common.t_unit)))
in (
# 687 "FStar.TypeChecker.Util.fst"
let _69_895 = (strengthen_precondition (Some ((fun _69_891 -> (match (()) with
| () -> begin
"push"
end)))) env e (FStar_Syntax_Util.lcomp_of_comp c) g)
in (match (_69_895) with
| (c, _69_894) -> begin
(
# 688 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 689 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 690 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 691 "FStar.TypeChecker.Util.fst"
let us = (let _150_518 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_518)::[])
in (
# 692 "FStar.TypeChecker.Util.fst"
let xret = (let _150_523 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _150_522 = (let _150_521 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_520 = (let _150_519 = (FStar_Syntax_Syntax.as_arg xexp)
in (_150_519)::[])
in (_150_521)::_150_520))
in (FStar_Syntax_Syntax.mk_Tm_app _150_523 _150_522 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 693 "FStar.TypeChecker.Util.fst"
let xret_comp = (let _150_524 = (mk_comp md_pure res_t xret xret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_524))
in (
# 694 "FStar.TypeChecker.Util.fst"
let lc = (let _150_530 = (let _150_529 = (let _150_528 = (strengthen_precondition (Some ((fun _69_902 -> (match (()) with
| () -> begin
"pop"
end)))) env xexp xret_comp g)
in (FStar_All.pipe_left Prims.fst _150_528))
in (Some (x), _150_529))
in (bind env None c _150_530))
in (lc.FStar_Syntax_Syntax.comp ()))))))))
end)))
end))
end))
in (
# 696 "FStar.TypeChecker.Util.fst"
let _69_904 = lc
in {FStar_Syntax_Syntax.eff_name = _69_904.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _69_904.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _69_904.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = comp})))

# 698 "FStar.TypeChecker.Util.fst"
let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env comp res_t -> (
# 699 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 700 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 701 "FStar.TypeChecker.Util.fst"
let y = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 702 "FStar.TypeChecker.Util.fst"
let _69_914 = (let _150_538 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _150_537 = (FStar_Syntax_Syntax.bv_to_name y)
in (_150_538, _150_537)))
in (match (_69_914) with
| (xexp, yexp) -> begin
(
# 703 "FStar.TypeChecker.Util.fst"
let us = (let _150_539 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_539)::[])
in (
# 704 "FStar.TypeChecker.Util.fst"
let yret = (let _150_544 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _150_543 = (let _150_542 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_541 = (let _150_540 = (FStar_Syntax_Syntax.as_arg yexp)
in (_150_540)::[])
in (_150_542)::_150_541))
in (FStar_Syntax_Syntax.mk_Tm_app _150_544 _150_543 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 705 "FStar.TypeChecker.Util.fst"
let x_eq_y_yret = (let _150_552 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _150_551 = (let _150_550 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_549 = (let _150_548 = (let _150_545 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _150_545))
in (let _150_547 = (let _150_546 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_150_546)::[])
in (_150_548)::_150_547))
in (_150_550)::_150_549))
in (FStar_Syntax_Syntax.mk_Tm_app _150_552 _150_551 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 706 "FStar.TypeChecker.Util.fst"
let forall_y_x_eq_y_yret = (let _150_562 = (FStar_TypeChecker_Env.inst_effect_fun_with (FStar_List.append us us) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _150_561 = (let _150_560 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_559 = (let _150_558 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_557 = (let _150_556 = (let _150_555 = (let _150_554 = (let _150_553 = (FStar_Syntax_Syntax.mk_binder y)
in (_150_553)::[])
in (FStar_Syntax_Util.abs _150_554 x_eq_y_yret None))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _150_555))
in (_150_556)::[])
in (_150_558)::_150_557))
in (_150_560)::_150_559))
in (FStar_Syntax_Syntax.mk_Tm_app _150_562 _150_561 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 707 "FStar.TypeChecker.Util.fst"
let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (
# 708 "FStar.TypeChecker.Util.fst"
let lc = (bind env None (FStar_Syntax_Util.lcomp_of_comp comp) (Some (x), (FStar_Syntax_Util.lcomp_of_comp lc2)))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))

# 711 "FStar.TypeChecker.Util.fst"
let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (
# 712 "FStar.TypeChecker.Util.fst"
let comp = (fun _69_926 -> (match (()) with
| () -> begin
(
# 713 "FStar.TypeChecker.Util.fst"
let _69_942 = (let _150_574 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _150_573 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _150_574 _150_573)))
in (match (_69_942) with
| ((md, _69_929, _69_931), (res_t, wp_then, wlp_then), (_69_938, wp_else, wlp_else)) -> begin
(
# 714 "FStar.TypeChecker.Util.fst"
let us = (let _150_575 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_575)::[])
in (
# 715 "FStar.TypeChecker.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _150_595 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _150_594 = (let _150_592 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_591 = (let _150_590 = (FStar_Syntax_Syntax.as_arg g)
in (let _150_589 = (let _150_588 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _150_587 = (let _150_586 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_150_586)::[])
in (_150_588)::_150_587))
in (_150_590)::_150_589))
in (_150_592)::_150_591))
in (let _150_593 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _150_595 _150_594 None _150_593)))))
in (
# 716 "FStar.TypeChecker.Util.fst"
let wp = (ifthenelse md res_t guard wp_then wp_else)
in (
# 717 "FStar.TypeChecker.Util.fst"
let wlp = (ifthenelse md res_t guard wlp_then wlp_else)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(
# 719 "FStar.TypeChecker.Util.fst"
let comp = (mk_comp md res_t wp wlp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(
# 721 "FStar.TypeChecker.Util.fst"
let wp = (let _150_602 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _150_601 = (let _150_600 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_599 = (let _150_598 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _150_597 = (let _150_596 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_596)::[])
in (_150_598)::_150_597))
in (_150_600)::_150_599))
in (FStar_Syntax_Syntax.mk_Tm_app _150_602 _150_601 None wp.FStar_Syntax_Syntax.pos)))
in (
# 722 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_607 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _150_606 = (let _150_605 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_604 = (let _150_603 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_603)::[])
in (_150_605)::_150_604))
in (FStar_Syntax_Syntax.mk_Tm_app _150_607 _150_606 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end))))
end))
end))
in (let _150_608 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _150_608; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp})))

# 729 "FStar.TypeChecker.Util.fst"
let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (let _150_614 = (let _150_613 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid _150_613))
in (FStar_Syntax_Syntax.fvar _150_614 FStar_Syntax_Syntax.Delta_constant None)))

# 731 "FStar.TypeChecker.Util.fst"
let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (
# 732 "FStar.TypeChecker.Util.fst"
let eff = (FStar_List.fold_left (fun eff _69_964 -> (match (_69_964) with
| (_69_962, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (
# 733 "FStar.TypeChecker.Util.fst"
let bind_cases = (fun _69_967 -> (match (()) with
| () -> begin
(
# 734 "FStar.TypeChecker.Util.fst"
let us = (let _150_625 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_625)::[])
in (
# 735 "FStar.TypeChecker.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _150_645 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _150_644 = (let _150_642 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_641 = (let _150_640 = (FStar_Syntax_Syntax.as_arg g)
in (let _150_639 = (let _150_638 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _150_637 = (let _150_636 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_150_636)::[])
in (_150_638)::_150_637))
in (_150_640)::_150_639))
in (_150_642)::_150_641))
in (let _150_643 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _150_645 _150_644 None _150_643)))))
in (
# 737 "FStar.TypeChecker.Util.fst"
let default_case = (
# 738 "FStar.TypeChecker.Util.fst"
let post_k = (let _150_648 = (let _150_646 = (FStar_Syntax_Syntax.null_binder res_t)
in (_150_646)::[])
in (let _150_647 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _150_648 _150_647)))
in (
# 739 "FStar.TypeChecker.Util.fst"
let kwp = (let _150_651 = (let _150_649 = (FStar_Syntax_Syntax.null_binder post_k)
in (_150_649)::[])
in (let _150_650 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _150_651 _150_650)))
in (
# 740 "FStar.TypeChecker.Util.fst"
let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (
# 741 "FStar.TypeChecker.Util.fst"
let wp = (let _150_657 = (let _150_652 = (FStar_Syntax_Syntax.mk_binder post)
in (_150_652)::[])
in (let _150_656 = (let _150_655 = (let _150_653 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Errors.exhaustiveness_check _150_653))
in (let _150_654 = (fvar_const env FStar_Syntax_Const.false_lid)
in (FStar_All.pipe_left _150_655 _150_654)))
in (FStar_Syntax_Util.abs _150_657 _150_656 None)))
in (
# 742 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_660 = (let _150_658 = (FStar_Syntax_Syntax.mk_binder post)
in (_150_658)::[])
in (let _150_659 = (fvar_const env FStar_Syntax_Const.true_lid)
in (FStar_Syntax_Util.abs _150_660 _150_659 None)))
in (
# 743 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (
# 745 "FStar.TypeChecker.Util.fst"
let comp = (FStar_List.fold_right (fun _69_984 celse -> (match (_69_984) with
| (g, cthen) -> begin
(
# 746 "FStar.TypeChecker.Util.fst"
let _69_1002 = (let _150_663 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _150_663 celse))
in (match (_69_1002) with
| ((md, _69_988, _69_990), (_69_993, wp_then, wlp_then), (_69_998, wp_else, wlp_else)) -> begin
(let _150_665 = (ifthenelse md res_t g wp_then wp_else)
in (let _150_664 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _150_665 _150_664 [])))
end))
end)) lcases default_case)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(add_equality_to_post_condition env comp res_t)
end else begin
(
# 750 "FStar.TypeChecker.Util.fst"
let comp = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (
# 751 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env comp.FStar_Syntax_Syntax.effect_name)
in (
# 752 "FStar.TypeChecker.Util.fst"
let _69_1010 = (destruct_comp comp)
in (match (_69_1010) with
| (_69_1007, wp, wlp) -> begin
(
# 753 "FStar.TypeChecker.Util.fst"
let wp = (let _150_672 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _150_671 = (let _150_670 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_669 = (let _150_668 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _150_667 = (let _150_666 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_666)::[])
in (_150_668)::_150_667))
in (_150_670)::_150_669))
in (FStar_Syntax_Syntax.mk_Tm_app _150_672 _150_671 None wp.FStar_Syntax_Syntax.pos)))
in (
# 754 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_677 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _150_676 = (let _150_675 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_674 = (let _150_673 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_673)::[])
in (_150_675)::_150_674))
in (FStar_Syntax_Syntax.mk_Tm_app _150_677 _150_676 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end))))
end))))
end))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))

# 761 "FStar.TypeChecker.Util.fst"
let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (
# 762 "FStar.TypeChecker.Util.fst"
let close = (fun _69_1017 -> (match (()) with
| () -> begin
(
# 763 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in if (FStar_Syntax_Util.is_ml_comp c) then begin
c
end else begin
(
# 766 "FStar.TypeChecker.Util.fst"
let close_wp = (fun u_res md res_t bvs wp0 -> (FStar_List.fold_right (fun x wp -> (
# 768 "FStar.TypeChecker.Util.fst"
let bs = (let _150_698 = (FStar_Syntax_Syntax.mk_binder x)
in (_150_698)::[])
in (
# 769 "FStar.TypeChecker.Util.fst"
let us = (let _150_700 = (let _150_699 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (_150_699)::[])
in (u_res)::_150_700)
in (
# 770 "FStar.TypeChecker.Util.fst"
let wp = (FStar_Syntax_Util.abs bs wp None)
in (let _150_707 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (let _150_706 = (let _150_705 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_704 = (let _150_703 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _150_702 = (let _150_701 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_701)::[])
in (_150_703)::_150_702))
in (_150_705)::_150_704))
in (FStar_Syntax_Syntax.mk_Tm_app _150_707 _150_706 None wp0.FStar_Syntax_Syntax.pos))))))) bvs wp0))
in (
# 773 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 774 "FStar.TypeChecker.Util.fst"
let _69_1034 = (destruct_comp c)
in (match (_69_1034) with
| (t, wp, wlp) -> begin
(
# 775 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 776 "FStar.TypeChecker.Util.fst"
let u_res = (env.FStar_TypeChecker_Env.universe_of env c.FStar_Syntax_Syntax.result_typ)
in (
# 777 "FStar.TypeChecker.Util.fst"
let wp = (close_wp u_res md c.FStar_Syntax_Syntax.result_typ bvs wp)
in (
# 778 "FStar.TypeChecker.Util.fst"
let wlp = (close_wp u_res md c.FStar_Syntax_Syntax.result_typ bvs wlp)
in (mk_comp md c.FStar_Syntax_Syntax.result_typ wp wlp c.FStar_Syntax_Syntax.flags)))))
end))))
end)
end))
in (
# 780 "FStar.TypeChecker.Util.fst"
let _69_1039 = lc
in {FStar_Syntax_Syntax.eff_name = _69_1039.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _69_1039.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _69_1039.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))

# 782 "FStar.TypeChecker.Util.fst"
let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (
# 783 "FStar.TypeChecker.Util.fst"
let refine = (fun _69_1045 -> (match (()) with
| () -> begin
(
# 784 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in if (not ((is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name))) then begin
c
end else begin
if (FStar_Syntax_Util.is_partial_return c) then begin
c
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c) && (not ((FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)))) then begin
(let _150_718 = (let _150_717 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _150_716 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _150_717 _150_716)))
in (FStar_All.failwith _150_718))
end else begin
(
# 792 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 793 "FStar.TypeChecker.Util.fst"
let t = c.FStar_Syntax_Syntax.result_typ
in (
# 794 "FStar.TypeChecker.Util.fst"
let c = (FStar_Syntax_Syntax.mk_Comp c)
in (
# 795 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (
# 796 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 797 "FStar.TypeChecker.Util.fst"
let ret = (let _150_720 = (let _150_719 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _150_719 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_720))
in (
# 798 "FStar.TypeChecker.Util.fst"
let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (
# 799 "FStar.TypeChecker.Util.fst"
let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (
# 801 "FStar.TypeChecker.Util.fst"
let c = (let _150_722 = (let _150_721 = (bind env None (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), eq_ret))
in (_150_721.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _150_722 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
in c)))))))))
end
end
end)
end))
in (
# 804 "FStar.TypeChecker.Util.fst"
let flags = if (((not ((FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)) && (not ((FStar_Syntax_Util.is_lcomp_partial_return lc)))) then begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_Syntax_Syntax.cflags
end else begin
lc.FStar_Syntax_Syntax.cflags
end
in (
# 810 "FStar.TypeChecker.Util.fst"
let _69_1057 = lc
in {FStar_Syntax_Syntax.eff_name = _69_1057.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _69_1057.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))

# 812 "FStar.TypeChecker.Util.fst"
let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (match ((FStar_TypeChecker_Rel.sub_comp env c c')) with
| None -> begin
(let _150_734 = (let _150_733 = (let _150_732 = (FStar_TypeChecker_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _150_731 = (FStar_TypeChecker_Env.get_range env)
in (_150_732, _150_731)))
in FStar_Syntax_Syntax.Error (_150_733))
in (Prims.raise _150_734))
end
| Some (g) -> begin
(e, c', g)
end))

# 818 "FStar.TypeChecker.Util.fst"
let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match ((let _150_743 = (FStar_Syntax_Subst.compress t)
in _150_743.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_69_1071) -> begin
(match ((let _150_744 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _150_744.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid) -> begin
(
# 823 "FStar.TypeChecker.Util.fst"
let _69_1075 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (
# 824 "FStar.TypeChecker.Util.fst"
let b2t = (let _150_745 = (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar _150_745 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (
# 825 "FStar.TypeChecker.Util.fst"
let lc = (let _150_748 = (let _150_747 = (let _150_746 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_746))
in (None, _150_747))
in (bind env (Some (e)) lc _150_748))
in (
# 826 "FStar.TypeChecker.Util.fst"
let e = (let _150_750 = (let _150_749 = (FStar_Syntax_Syntax.as_arg e)
in (_150_749)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _150_750 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (e, lc)))))
end
| _69_1081 -> begin
(e, lc)
end)
end
| _69_1083 -> begin
(e, lc)
end))

# 833 "FStar.TypeChecker.Util.fst"
let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (
# 834 "FStar.TypeChecker.Util.fst"
let gopt = if env.FStar_TypeChecker_Env.use_eq then begin
(let _150_759 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in (_150_759, false))
end else begin
(let _150_760 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in (_150_760, true))
end
in (match (gopt) with
| (None, _69_1091) -> begin
(FStar_TypeChecker_Rel.subtype_fail env lc.FStar_Syntax_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(match ((FStar_TypeChecker_Rel.guard_form g)) with
| FStar_TypeChecker_Common.Trivial -> begin
(
# 842 "FStar.TypeChecker.Util.fst"
let lc = (
# 842 "FStar.TypeChecker.Util.fst"
let _69_1098 = lc
in {FStar_Syntax_Syntax.eff_name = _69_1098.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _69_1098.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _69_1098.FStar_Syntax_Syntax.comp})
in (e, lc, g))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 846 "FStar.TypeChecker.Util.fst"
let g = (
# 846 "FStar.TypeChecker.Util.fst"
let _69_1103 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _69_1103.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _69_1103.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _69_1103.FStar_TypeChecker_Env.implicits})
in (
# 847 "FStar.TypeChecker.Util.fst"
let strengthen = (fun _69_1107 -> (match (()) with
| () -> begin
(
# 849 "FStar.TypeChecker.Util.fst"
let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (match ((let _150_763 = (FStar_Syntax_Subst.compress f)
in _150_763.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_69_1110, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _69_1116; FStar_Syntax_Syntax.pos = _69_1114; FStar_Syntax_Syntax.vars = _69_1112}, _69_1121) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
(
# 853 "FStar.TypeChecker.Util.fst"
let lc = (
# 853 "FStar.TypeChecker.Util.fst"
let _69_1124 = lc
in {FStar_Syntax_Syntax.eff_name = _69_1124.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _69_1124.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _69_1124.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| _69_1128 -> begin
(
# 857 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 858 "FStar.TypeChecker.Util.fst"
let _69_1130 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_767 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _150_766 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _150_765 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _150_764 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _150_767 _150_766 _150_765 _150_764)))))
end else begin
()
end
in (
# 865 "FStar.TypeChecker.Util.fst"
let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 866 "FStar.TypeChecker.Util.fst"
let _69_1135 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_69_1135) with
| (a, kwp) -> begin
(
# 867 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 868 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env ct.FStar_Syntax_Syntax.effect_name)
in (
# 869 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (
# 870 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 871 "FStar.TypeChecker.Util.fst"
let us = (let _150_768 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_150_768)::[])
in (
# 872 "FStar.TypeChecker.Util.fst"
let wp = (let _150_773 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ret)
in (let _150_772 = (let _150_771 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_770 = (let _150_769 = (FStar_Syntax_Syntax.as_arg xexp)
in (_150_769)::[])
in (_150_771)::_150_770))
in (FStar_Syntax_Syntax.mk_Tm_app _150_773 _150_772 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)))
in (
# 873 "FStar.TypeChecker.Util.fst"
let cret = (let _150_774 = (mk_comp md t wp wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_774))
in (
# 874 "FStar.TypeChecker.Util.fst"
let guard = if apply_guard then begin
(let _150_776 = (let _150_775 = (FStar_Syntax_Syntax.as_arg xexp)
in (_150_775)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _150_776 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end else begin
f
end
in (
# 875 "FStar.TypeChecker.Util.fst"
let _69_1146 = (let _150_784 = (FStar_All.pipe_left (fun _150_781 -> Some (_150_781)) (FStar_TypeChecker_Errors.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _150_783 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _150_782 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _150_784 _150_783 e cret _150_782))))
in (match (_69_1146) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(
# 879 "FStar.TypeChecker.Util.fst"
let x = (
# 879 "FStar.TypeChecker.Util.fst"
let _69_1147 = x
in {FStar_Syntax_Syntax.ppname = _69_1147.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_1147.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (
# 880 "FStar.TypeChecker.Util.fst"
let c = (let _150_786 = (let _150_785 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_785))
in (bind env (Some (e)) _150_786 (Some (x), eq_ret)))
in (
# 881 "FStar.TypeChecker.Util.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 882 "FStar.TypeChecker.Util.fst"
let _69_1152 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_787 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _150_787))
end else begin
()
end
in c))))
end))))))))))
end)))))
end))
end))
in (
# 885 "FStar.TypeChecker.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _69_3 -> (match (_69_3) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _69_1158 -> begin
[]
end))))
in (
# 886 "FStar.TypeChecker.Util.fst"
let lc = (
# 886 "FStar.TypeChecker.Util.fst"
let _69_1160 = lc
in (let _150_789 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _150_789; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (
# 887 "FStar.TypeChecker.Util.fst"
let g = (
# 887 "FStar.TypeChecker.Util.fst"
let _69_1163 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _69_1163.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _69_1163.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _69_1163.FStar_TypeChecker_Env.implicits})
in (e, lc, g))))))
end)
end)))

# 890 "FStar.TypeChecker.Util.fst"
let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (
# 891 "FStar.TypeChecker.Util.fst"
let mk_post_type = (fun res_t ens -> (
# 892 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _150_801 = (let _150_800 = (let _150_799 = (let _150_798 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _150_798))
in (_150_799)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _150_800 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _150_801))))
in (
# 894 "FStar.TypeChecker.Util.fst"
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
| (req, _69_1191)::(ens, _69_1186)::_69_1183 -> begin
(let _150_807 = (let _150_804 = (norm req)
in Some (_150_804))
in (let _150_806 = (let _150_805 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _150_805))
in (_150_807, _150_806)))
end
| _69_1195 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 908 "FStar.TypeChecker.Util.fst"
let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (wp, _69_1206)::(wlp, _69_1201)::_69_1198 -> begin
(
# 911 "FStar.TypeChecker.Util.fst"
let _69_1212 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (_69_1212) with
| (us_r, _69_1211) -> begin
(
# 912 "FStar.TypeChecker.Util.fst"
let _69_1216 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (_69_1216) with
| (us_e, _69_1215) -> begin
(
# 913 "FStar.TypeChecker.Util.fst"
let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (
# 914 "FStar.TypeChecker.Util.fst"
let as_req = (let _150_809 = (let _150_808 = (FStar_Ident.set_lid_range FStar_Syntax_Const.as_requires r)
in (FStar_Syntax_Syntax.fvar _150_808 FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_809 us_r))
in (
# 915 "FStar.TypeChecker.Util.fst"
let as_ens = (let _150_811 = (let _150_810 = (FStar_Ident.set_lid_range FStar_Syntax_Const.as_ensures r)
in (FStar_Syntax_Syntax.fvar _150_810 FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_811 us_e))
in (
# 916 "FStar.TypeChecker.Util.fst"
let req = (let _150_814 = (let _150_813 = (let _150_812 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_812)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.imp_tag)))::_150_813)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _150_814 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 917 "FStar.TypeChecker.Util.fst"
let ens = (let _150_817 = (let _150_816 = (let _150_815 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_815)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.imp_tag)))::_150_816)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _150_817 None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _150_821 = (let _150_818 = (norm req)
in Some (_150_818))
in (let _150_820 = (let _150_819 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm _150_819))
in (_150_821, _150_820))))))))
end))
end))
end
| _69_1223 -> begin
(FStar_All.failwith "Impossible")
end))
end
end)
end)))

# 927 "FStar.TypeChecker.Util.fst"
let maybe_instantiate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (
# 928 "FStar.TypeChecker.Util.fst"
let torig = (FStar_Syntax_Subst.compress t)
in if (not (env.FStar_TypeChecker_Env.instantiate_imp)) then begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end else begin
(match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 933 "FStar.TypeChecker.Util.fst"
let _69_1234 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_69_1234) with
| (bs, c) -> begin
(
# 934 "FStar.TypeChecker.Util.fst"
let rec aux = (fun subst _69_4 -> (match (_69_4) with
| (x, Some (FStar_Syntax_Syntax.Implicit (dot)))::rest -> begin
(
# 936 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 937 "FStar.TypeChecker.Util.fst"
let _69_1250 = (new_implicit_var env t)
in (match (_69_1250) with
| (v, _69_1248, g) -> begin
(
# 938 "FStar.TypeChecker.Util.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, v)))::subst
in (
# 939 "FStar.TypeChecker.Util.fst"
let _69_1256 = (aux subst rest)
in (match (_69_1256) with
| (args, bs, subst, g') -> begin
(let _150_832 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((v, Some (FStar_Syntax_Syntax.Implicit (dot))))::args, bs, subst, _150_832))
end)))
end)))
end
| bs -> begin
([], bs, subst, FStar_TypeChecker_Rel.trivial_guard)
end))
in (
# 943 "FStar.TypeChecker.Util.fst"
let _69_1262 = (aux [] bs)
in (match (_69_1262) with
| (args, bs, subst, guard) -> begin
(match ((args, bs)) with
| ([], _69_1265) -> begin
(e, torig, guard)
end
| (_69_1268, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end
| _69_1272 -> begin
(
# 954 "FStar.TypeChecker.Util.fst"
let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _69_1275 -> begin
(FStar_Syntax_Util.arrow bs c)
end)
in (
# 957 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.subst subst t)
in (
# 958 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk_Tm_app e args (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (e, t, guard))))
end)
end)))
end))
end
| _69_1280 -> begin
(e, t, FStar_TypeChecker_Rel.trivial_guard)
end)
end))

# 968 "FStar.TypeChecker.Util.fst"
let gen_univs : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe_uvar Prims.list * (FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  Prims.bool))  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(
# 970 "FStar.TypeChecker.Util.fst"
let s = (let _150_844 = (let _150_843 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _150_843))
in (FStar_All.pipe_right _150_844 FStar_Util.set_elements))
in (
# 971 "FStar.TypeChecker.Util.fst"
let r = (let _150_845 = (FStar_TypeChecker_Env.get_range env)
in Some (_150_845))
in (
# 972 "FStar.TypeChecker.Util.fst"
let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (
# 973 "FStar.TypeChecker.Util.fst"
let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (
# 974 "FStar.TypeChecker.Util.fst"
let _69_1287 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _150_850 = (let _150_847 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _150_847))
in (let _150_849 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _150_848 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _150_850 _150_849 _150_848))))
end else begin
()
end
in (
# 976 "FStar.TypeChecker.Util.fst"
let _69_1289 = (FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))))
in u_name))))))
in u_names)))
end)

# 980 "FStar.TypeChecker.Util.fst"
let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t -> (
# 981 "FStar.TypeChecker.Util.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (
# 982 "FStar.TypeChecker.Util.fst"
let univs = (FStar_Syntax_Free.univs t)
in (
# 983 "FStar.TypeChecker.Util.fst"
let _69_1297 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _150_859 = (let _150_858 = (let _150_857 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _150_857 (FStar_List.map (fun u -> (let _150_856 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _150_856 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _150_858 (FStar_String.concat ", ")))
in (FStar_Util.print1 "univs to gen : %s\n" _150_859))
end else begin
()
end
in (
# 987 "FStar.TypeChecker.Util.fst"
let gen = (gen_univs env univs)
in (
# 988 "FStar.TypeChecker.Util.fst"
let _69_1300 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _150_860 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _150_860))
end else begin
()
end
in (
# 990 "FStar.TypeChecker.Util.fst"
let ts = (FStar_Syntax_Subst.close_univ_vars gen t)
in (gen, ts))))))))

# 993 "FStar.TypeChecker.Util.fst"
let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> if (let _150_866 = (FStar_Util.for_all (fun _69_1308 -> (match (_69_1308) with
| (_69_1306, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _150_866)) then begin
None
end else begin
(
# 997 "FStar.TypeChecker.Util.fst"
let norm = (fun c -> (
# 998 "FStar.TypeChecker.Util.fst"
let _69_1311 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _150_869 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _150_869))
end else begin
()
end
in (
# 1000 "FStar.TypeChecker.Util.fst"
let c = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.Eta)::[]) env c)
end else begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env c)
end
in (
# 1003 "FStar.TypeChecker.Util.fst"
let _69_1314 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _150_870 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _150_870))
end else begin
()
end
in c))))
in (
# 1006 "FStar.TypeChecker.Util.fst"
let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (
# 1007 "FStar.TypeChecker.Util.fst"
let gen_uvars = (fun uvs -> (let _150_873 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _150_873 FStar_Util.set_elements)))
in (
# 1008 "FStar.TypeChecker.Util.fst"
let _69_1331 = (let _150_875 = (FStar_All.pipe_right ecs (FStar_List.map (fun _69_1321 -> (match (_69_1321) with
| (e, c) -> begin
(
# 1009 "FStar.TypeChecker.Util.fst"
let t = (FStar_All.pipe_right (FStar_Syntax_Util.comp_result c) FStar_Syntax_Subst.compress)
in (
# 1010 "FStar.TypeChecker.Util.fst"
let c = (norm c)
in (
# 1011 "FStar.TypeChecker.Util.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (
# 1012 "FStar.TypeChecker.Util.fst"
let t = ct.FStar_Syntax_Syntax.result_typ
in (
# 1013 "FStar.TypeChecker.Util.fst"
let univs = (FStar_Syntax_Free.univs t)
in (
# 1014 "FStar.TypeChecker.Util.fst"
let uvt = (FStar_Syntax_Free.uvars t)
in (
# 1015 "FStar.TypeChecker.Util.fst"
let uvs = (gen_uvars uvt)
in (univs, (uvs, e, c)))))))))
end))))
in (FStar_All.pipe_right _150_875 FStar_List.unzip))
in (match (_69_1331) with
| (univs, uvars) -> begin
(
# 1018 "FStar.TypeChecker.Util.fst"
let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (
# 1019 "FStar.TypeChecker.Util.fst"
let gen_univs = (gen_univs env univs)
in (
# 1020 "FStar.TypeChecker.Util.fst"
let _69_1335 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end else begin
()
end
in (
# 1022 "FStar.TypeChecker.Util.fst"
let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _69_1340 -> (match (_69_1340) with
| (uvs, e, c) -> begin
(
# 1023 "FStar.TypeChecker.Util.fst"
let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _69_1343 -> (match (_69_1343) with
| (u, k) -> begin
(match ((FStar_Unionfind.find u)) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(a, Some (FStar_Syntax_Syntax.imp_tag))
end
| FStar_Syntax_Syntax.Fixed (_69_1377) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _69_1380 -> begin
(
# 1029 "FStar.TypeChecker.Util.fst"
let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (
# 1030 "FStar.TypeChecker.Util.fst"
let _69_1384 = (FStar_Syntax_Util.arrow_formals k)
in (match (_69_1384) with
| (bs, kres) -> begin
(
# 1031 "FStar.TypeChecker.Util.fst"
let a = (let _150_881 = (let _150_880 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _150_879 -> Some (_150_879)) _150_880))
in (FStar_Syntax_Syntax.new_bv _150_881 kres))
in (
# 1032 "FStar.TypeChecker.Util.fst"
let t = (let _150_885 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _150_884 = (let _150_883 = (let _150_882 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _150_882))
in Some (_150_883))
in (FStar_Syntax_Util.abs bs _150_885 _150_884)))
in (
# 1033 "FStar.TypeChecker.Util.fst"
let _69_1387 = (FStar_Syntax_Util.set_uvar u t)
in (a, Some (FStar_Syntax_Syntax.imp_tag)))))
end)))
end)
end))))
in (
# 1037 "FStar.TypeChecker.Util.fst"
let _69_1411 = (match (tvars) with
| [] -> begin
(e, c)
end
| _69_1392 -> begin
(
# 1043 "FStar.TypeChecker.Util.fst"
let _69_1395 = (e, c)
in (match (_69_1395) with
| (e0, c0) -> begin
(
# 1044 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.BetaUVars)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::[]) env c)
in (
# 1045 "FStar.TypeChecker.Util.fst"
let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.BetaUVars)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::[]) env e)
in (
# 1047 "FStar.TypeChecker.Util.fst"
let t = (match ((let _150_886 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _150_886.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(
# 1049 "FStar.TypeChecker.Util.fst"
let _69_1404 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (_69_1404) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| _69_1406 -> begin
(FStar_Syntax_Util.arrow tvars c)
end)
in (
# 1054 "FStar.TypeChecker.Util.fst"
let e' = (FStar_Syntax_Util.abs tvars e None)
in (let _150_887 = (FStar_Syntax_Syntax.mk_Total t)
in (e', _150_887))))))
end))
end)
in (match (_69_1411) with
| (e, c) -> begin
(gen_univs, e, c)
end)))
end))))
in Some (ecs)))))
end)))))
end)

# 1059 "FStar.TypeChecker.Util.fst"
let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> (
# 1060 "FStar.TypeChecker.Util.fst"
let _69_1421 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_894 = (let _150_893 = (FStar_List.map (fun _69_1420 -> (match (_69_1420) with
| (lb, _69_1417, _69_1419) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _150_893 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _150_894))
end else begin
()
end
in (match ((let _150_896 = (FStar_All.pipe_right lecs (FStar_List.map (fun _69_1427 -> (match (_69_1427) with
| (_69_1424, e, c) -> begin
(e, c)
end))))
in (gen env _150_896))) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun _69_1432 -> (match (_69_1432) with
| (l, t, c) -> begin
(l, [], t, c)
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _69_1440 _69_1444 -> (match ((_69_1440, _69_1444)) with
| ((l, _69_1437, _69_1439), (us, e, c)) -> begin
(
# 1067 "FStar.TypeChecker.Util.fst"
let _69_1445 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _150_902 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _150_901 = (FStar_Syntax_Print.lbname_to_string l)
in (let _150_900 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.print3 "(%s) Generalized %s to %s\n" _150_902 _150_901 _150_900))))
end else begin
()
end
in (l, us, e, c))
end)) lecs ecs)
end)))

# 1080 "FStar.TypeChecker.Util.fst"
let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (
# 1081 "FStar.TypeChecker.Util.fst"
let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (
# 1082 "FStar.TypeChecker.Util.fst"
let check = (fun env t1 t2 -> if env.FStar_TypeChecker_Env.use_eq then begin
(FStar_TypeChecker_Rel.try_teq env t1 t2)
end else begin
(match ((FStar_TypeChecker_Rel.try_subtype env t1 t2)) with
| None -> begin
None
end
| Some (f) -> begin
(let _150_918 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _150_917 -> Some (_150_917)) _150_918))
end)
end)
in (
# 1088 "FStar.TypeChecker.Util.fst"
let is_var = (fun e -> (match ((let _150_921 = (FStar_Syntax_Subst.compress e)
in _150_921.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (_69_1462) -> begin
true
end
| _69_1465 -> begin
false
end))
in (
# 1091 "FStar.TypeChecker.Util.fst"
let decorate = (fun e t -> (
# 1092 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((
# 1094 "FStar.TypeChecker.Util.fst"
let _69_1472 = x
in {FStar_Syntax_Syntax.ppname = _69_1472.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_1472.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| _69_1475 -> begin
(
# 1095 "FStar.TypeChecker.Util.fst"
let _69_1476 = e
in (let _150_926 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _69_1476.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _150_926; FStar_Syntax_Syntax.pos = _69_1476.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _69_1476.FStar_Syntax_Syntax.vars}))
end)))
in (
# 1096 "FStar.TypeChecker.Util.fst"
let env = (
# 1096 "FStar.TypeChecker.Util.fst"
let _69_1478 = env
in (let _150_927 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _69_1478.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _69_1478.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _69_1478.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _69_1478.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _69_1478.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _69_1478.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _69_1478.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _69_1478.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _69_1478.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _69_1478.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _69_1478.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _69_1478.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _69_1478.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _69_1478.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _69_1478.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _150_927; FStar_TypeChecker_Env.is_iface = _69_1478.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _69_1478.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _69_1478.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _69_1478.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _69_1478.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _69_1478.FStar_TypeChecker_Env.use_bv_sorts}))
in (match ((check env t1 t2)) with
| None -> begin
(let _150_931 = (let _150_930 = (let _150_929 = (FStar_TypeChecker_Errors.expected_expression_of_type env t2 e t1)
in (let _150_928 = (FStar_TypeChecker_Env.get_range env)
in (_150_929, _150_928)))
in FStar_Syntax_Syntax.Error (_150_930))
in (Prims.raise _150_931))
end
| Some (g) -> begin
(
# 1100 "FStar.TypeChecker.Util.fst"
let _69_1484 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _150_932 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _150_932))
end else begin
()
end
in (let _150_933 = (decorate e t2)
in (_150_933, g)))
end)))))))

# 1105 "FStar.TypeChecker.Util.fst"
let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (
# 1106 "FStar.TypeChecker.Util.fst"
let discharge = (fun g -> (
# 1107 "FStar.TypeChecker.Util.fst"
let _69_1491 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (
# 1109 "FStar.TypeChecker.Util.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _150_943 = (discharge g)
in (let _150_942 = (lc.FStar_Syntax_Syntax.comp ())
in (_150_943, _150_942)))
end else begin
(
# 1112 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 1113 "FStar.TypeChecker.Util.fst"
let steps = (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.DeltaComp)::[]
in (
# 1114 "FStar.TypeChecker.Util.fst"
let c = (let _150_944 = (FStar_TypeChecker_Normalize.normalize_comp steps env c)
in (FStar_All.pipe_right _150_944 FStar_Syntax_Util.comp_to_comp_typ))
in (
# 1115 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 1116 "FStar.TypeChecker.Util.fst"
let _69_1502 = (destruct_comp c)
in (match (_69_1502) with
| (t, wp, _69_1501) -> begin
(
# 1117 "FStar.TypeChecker.Util.fst"
let vc = (let _150_952 = (let _150_946 = (let _150_945 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_150_945)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _150_946 env md md.FStar_Syntax_Syntax.trivial))
in (let _150_951 = (let _150_949 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_948 = (let _150_947 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_947)::[])
in (_150_949)::_150_948))
in (let _150_950 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk_Tm_app _150_952 _150_951 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _150_950))))
in (
# 1118 "FStar.TypeChecker.Util.fst"
let _69_1504 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _150_953 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _150_953))
end else begin
()
end
in (
# 1120 "FStar.TypeChecker.Util.fst"
let g = (let _150_954 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _150_954))
in (let _150_956 = (discharge g)
in (let _150_955 = (FStar_Syntax_Syntax.mk_Comp c)
in (_150_956, _150_955))))))
end))))))
end)))

# 1126 "FStar.TypeChecker.Util.fst"
let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (
# 1127 "FStar.TypeChecker.Util.fst"
let short_bin_op = (fun f _69_5 -> (match (_69_5) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (fst, _69_1515)::[] -> begin
(f fst)
end
| _69_1519 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (
# 1132 "FStar.TypeChecker.Util.fst"
let op_and_e = (fun e -> (let _150_977 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _150_977 (fun _150_976 -> FStar_TypeChecker_Common.NonTrivial (_150_976)))))
in (
# 1133 "FStar.TypeChecker.Util.fst"
let op_or_e = (fun e -> (let _150_982 = (let _150_980 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _150_980))
in (FStar_All.pipe_right _150_982 (fun _150_981 -> FStar_TypeChecker_Common.NonTrivial (_150_981)))))
in (
# 1134 "FStar.TypeChecker.Util.fst"
let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _150_985 -> FStar_TypeChecker_Common.NonTrivial (_150_985))))
in (
# 1135 "FStar.TypeChecker.Util.fst"
let op_or_t = (fun t -> (let _150_989 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _150_989 (fun _150_988 -> FStar_TypeChecker_Common.NonTrivial (_150_988)))))
in (
# 1136 "FStar.TypeChecker.Util.fst"
let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _150_992 -> FStar_TypeChecker_Common.NonTrivial (_150_992))))
in (
# 1138 "FStar.TypeChecker.Util.fst"
let short_op_ite = (fun _69_6 -> (match (_69_6) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (guard, _69_1534)::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| _then::(guard, _69_1539)::[] -> begin
(let _150_996 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _150_996 (fun _150_995 -> FStar_TypeChecker_Common.NonTrivial (_150_995))))
end
| _69_1544 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (
# 1143 "FStar.TypeChecker.Util.fst"
let table = ((FStar_Syntax_Const.op_And, (short_bin_op op_and_e)))::((FStar_Syntax_Const.op_Or, (short_bin_op op_or_e)))::((FStar_Syntax_Const.and_lid, (short_bin_op op_and_t)))::((FStar_Syntax_Const.or_lid, (short_bin_op op_or_t)))::((FStar_Syntax_Const.imp_lid, (short_bin_op op_imp_t)))::((FStar_Syntax_Const.ite_lid, short_op_ite))::[]
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(
# 1153 "FStar.TypeChecker.Util.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((FStar_Util.find_map table (fun _69_1552 -> (match (_69_1552) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _150_1029 = (mk seen_args)
in Some (_150_1029))
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
| _69_1557 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))

# 1160 "FStar.TypeChecker.Util.fst"
let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (match ((let _150_1032 = (FStar_Syntax_Util.un_uinst l)
in _150_1032.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| _69_1562 -> begin
false
end))

# 1181 "FStar.TypeChecker.Util.fst"
let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (
# 1182 "FStar.TypeChecker.Util.fst"
let pos = (fun bs -> (match (bs) with
| (hd, _69_1571)::_69_1568 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| _69_1575 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| (_69_1579, Some (FStar_Syntax_Syntax.Implicit (_69_1581)))::_69_1577 -> begin
bs
end
| _69_1587 -> begin
(match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
bs
end
| Some (t) -> begin
(match ((let _150_1039 = (FStar_Syntax_Subst.compress t)
in _150_1039.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', _69_1593) -> begin
(match ((FStar_Util.prefix_until (fun _69_7 -> (match (_69_7) with
| (_69_1598, Some (FStar_Syntax_Syntax.Implicit (_69_1600))) -> begin
false
end
| _69_1605 -> begin
true
end)) bs')) with
| None -> begin
bs
end
| Some ([], _69_1609, _69_1611) -> begin
bs
end
| Some (imps, _69_1616, _69_1618) -> begin
if (FStar_All.pipe_right imps (FStar_Util.for_all (fun _69_1624 -> (match (_69_1624) with
| (x, _69_1623) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end)))) then begin
(
# 1198 "FStar.TypeChecker.Util.fst"
let r = (pos bs)
in (
# 1199 "FStar.TypeChecker.Util.fst"
let imps = (FStar_All.pipe_right imps (FStar_List.map (fun _69_1628 -> (match (_69_1628) with
| (x, i) -> begin
(let _150_1043 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in (_150_1043, i))
end))))
in (FStar_List.append imps bs)))
end else begin
bs
end
end)
end
| _69_1631 -> begin
bs
end)
end)
end)))




