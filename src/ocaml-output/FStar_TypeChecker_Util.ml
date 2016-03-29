
open Prims
# 29 "FStar.TypeChecker.Util.fst"
type lcomp_with_binder =
(FStar_Syntax_Syntax.bv Prims.option * FStar_Syntax_Syntax.lcomp)

# 75 "FStar.TypeChecker.Util.fst"
let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _136_6 = (FStar_TypeChecker_Env.get_range env)
in (let _136_5 = (FStar_TypeChecker_Errors.failed_to_prove_specification errs)
in (FStar_TypeChecker_Errors.report _136_6 _136_5))))

# 80 "FStar.TypeChecker.Util.fst"
let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _136_9 = (FStar_Syntax_Subst.compress t)
in _136_9.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_12) -> begin
true
end
| _57_15 -> begin
false
end))

# 87 "FStar.TypeChecker.Util.fst"
let t_binders : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env -> (let _136_13 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right _136_13 (FStar_List.filter (fun _57_20 -> (match (_57_20) with
| (x, _57_19) -> begin
(is_type x.FStar_Syntax_Syntax.sort)
end))))))

# 90 "FStar.TypeChecker.Util.fst"
let new_uvar_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun env k -> (
# 94 "FStar.TypeChecker.Util.fst"
let bs = if (FStar_ST.read FStar_Options.full_context_dependency) then begin
(FStar_TypeChecker_Env.all_binders env)
end else begin
(t_binders env)
end
in (let _136_18 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Rel.new_uvar _136_18 bs k))))

# 97 "FStar.TypeChecker.Util.fst"
let new_uvar : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env k -> (let _136_23 = (new_uvar_aux env k)
in (Prims.fst _136_23)))

# 99 "FStar.TypeChecker.Util.fst"
let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun _57_1 -> (match (_57_1) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, _57_35); FStar_Syntax_Syntax.tk = _57_32; FStar_Syntax_Syntax.pos = _57_30; FStar_Syntax_Syntax.vars = _57_28} -> begin
uv
end
| _57_40 -> begin
(FStar_All.failwith "Impossible")
end))

# 103 "FStar.TypeChecker.Util.fst"
let new_implicit_var : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.uvar * FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env k -> (match ((FStar_Syntax_Util.destruct k FStar_Syntax_Const.range_of_lid)) with
| Some (_57_48::(tm, _57_45)::[]) -> begin
(
# 108 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))) None tm.FStar_Syntax_Syntax.pos)
in (t, [], FStar_TypeChecker_Rel.trivial_guard))
end
| _57_53 -> begin
(
# 112 "FStar.TypeChecker.Util.fst"
let _57_56 = (new_uvar_aux env k)
in (match (_57_56) with
| (t, u) -> begin
(
# 113 "FStar.TypeChecker.Util.fst"
let g = (
# 113 "FStar.TypeChecker.Util.fst"
let _57_57 = FStar_TypeChecker_Rel.trivial_guard
in (let _136_32 = (let _136_31 = (let _136_30 = (as_uvar u)
in (env, _136_30, t, k, u.FStar_Syntax_Syntax.pos))
in (_136_31)::[])
in {FStar_TypeChecker_Env.guard_f = _57_57.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_57.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_57.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _136_32}))
in (let _136_35 = (let _136_34 = (let _136_33 = (as_uvar u)
in (_136_33, u.FStar_Syntax_Syntax.pos))
in (_136_34)::[])
in (t, _136_35, g)))
end))
end))

# 114 "FStar.TypeChecker.Util.fst"
let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun r t -> (
# 117 "FStar.TypeChecker.Util.fst"
let uvs = (FStar_Syntax_Free.uvars t)
in if (not ((FStar_Util.set_is_empty uvs))) then begin
(
# 120 "FStar.TypeChecker.Util.fst"
let us = (let _136_42 = (let _136_41 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun _57_66 -> (match (_57_66) with
| (x, _57_65) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) _136_41))
in (FStar_All.pipe_right _136_42 (FStar_String.concat ", ")))
in (
# 122 "FStar.TypeChecker.Util.fst"
let hide_uvar_nums_saved = (FStar_ST.read FStar_Options.hide_uvar_nums)
in (
# 123 "FStar.TypeChecker.Util.fst"
let print_implicits_saved = (FStar_ST.read FStar_Options.print_implicits)
in (
# 124 "FStar.TypeChecker.Util.fst"
let _57_70 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums false)
in (
# 125 "FStar.TypeChecker.Util.fst"
let _57_72 = (FStar_ST.op_Colon_Equals FStar_Options.print_implicits true)
in (
# 126 "FStar.TypeChecker.Util.fst"
let _57_74 = (let _136_44 = (let _136_43 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us _136_43))
in (FStar_TypeChecker_Errors.report r _136_44))
in (
# 129 "FStar.TypeChecker.Util.fst"
let _57_76 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums hide_uvar_nums_saved)
in (FStar_ST.op_Colon_Equals FStar_Options.print_implicits print_implicits_saved))))))))
end else begin
()
end))

# 130 "FStar.TypeChecker.Util.fst"
let force_sort' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' = (fun s -> (match ((FStar_ST.read s.FStar_Syntax_Syntax.tk)) with
| None -> begin
(let _136_49 = (let _136_48 = (FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos)
in (let _136_47 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s" _136_48 _136_47)))
in (FStar_All.failwith _136_49))
end
| Some (tk) -> begin
tk
end))

# 138 "FStar.TypeChecker.Util.fst"
let force_sort = (fun s -> (let _136_51 = (force_sort' s)
in (FStar_Syntax_Syntax.mk _136_51 None s.FStar_Syntax_Syntax.pos)))

# 140 "FStar.TypeChecker.Util.fst"
let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env _57_91 -> (match (_57_91) with
| {FStar_Syntax_Syntax.lbname = _57_90; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _57_86; FStar_Syntax_Syntax.lbdef = e} -> begin
(
# 143 "FStar.TypeChecker.Util.fst"
let rng = t.FStar_Syntax_Syntax.pos
in (
# 144 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 147 "FStar.TypeChecker.Util.fst"
let _57_95 = if (univ_vars <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (
# 148 "FStar.TypeChecker.Util.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 149 "FStar.TypeChecker.Util.fst"
let mk_binder = (fun scope a -> (match (a.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 151 "FStar.TypeChecker.Util.fst"
let _57_105 = (FStar_Syntax_Util.type_u ())
in (match (_57_105) with
| (k, _57_104) -> begin
(
# 152 "FStar.TypeChecker.Util.fst"
let t = (let _136_60 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right _136_60 Prims.fst))
in ((
# 153 "FStar.TypeChecker.Util.fst"
let _57_107 = a
in {FStar_Syntax_Syntax.ppname = _57_107.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_107.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), false))
end))
end
| _57_110 -> begin
(a, true)
end))
in (
# 156 "FStar.TypeChecker.Util.fst"
let rec aux = (fun vars e -> (
# 157 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, _57_117) -> begin
(aux vars e)
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _57_123) -> begin
(t, true)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _57_129) -> begin
(
# 163 "FStar.TypeChecker.Util.fst"
let _57_148 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _57_135 _57_138 -> (match ((_57_135, _57_138)) with
| ((scope, bs, check), (a, imp)) -> begin
(
# 164 "FStar.TypeChecker.Util.fst"
let _57_141 = (mk_binder scope a)
in (match (_57_141) with
| (tb, c) -> begin
(
# 165 "FStar.TypeChecker.Util.fst"
let b = (tb, imp)
in (
# 166 "FStar.TypeChecker.Util.fst"
let bs = (FStar_List.append bs ((b)::[]))
in (
# 167 "FStar.TypeChecker.Util.fst"
let scope = (FStar_List.append scope ((b)::[]))
in (scope, bs, (c || check)))))
end))
end)) (vars, [], false)))
in (match (_57_148) with
| (scope, bs, check) -> begin
(
# 171 "FStar.TypeChecker.Util.fst"
let _57_151 = (aux scope body)
in (match (_57_151) with
| (res, check_res) -> begin
(
# 172 "FStar.TypeChecker.Util.fst"
let c = (match (res) with
| FStar_Util.Inl (t) -> begin
(FStar_Syntax_Util.ml_comp t r)
end
| FStar_Util.Inr (c) -> begin
c
end)
in (
# 175 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Util.arrow bs c)
in (
# 176 "FStar.TypeChecker.Util.fst"
let _57_158 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _136_68 = (FStar_Range.string_of_range r)
in (let _136_67 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _136_68 _136_67)))
end else begin
()
end
in (FStar_Util.Inl (t), (check_res || check)))))
end))
end))
end
| _57_161 -> begin
(let _136_71 = (let _136_70 = (let _136_69 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _136_69 Prims.fst))
in FStar_Util.Inl (_136_70))
in (_136_71, false))
end)))
in (
# 181 "FStar.TypeChecker.Util.fst"
let _57_164 = (let _136_72 = (t_binders env)
in (aux _136_72 e))
in (match (_57_164) with
| (t, b) -> begin
(
# 182 "FStar.TypeChecker.Util.fst"
let t = (match (t) with
| FStar_Util.Inr (c) -> begin
(let _136_76 = (let _136_75 = (let _136_74 = (let _136_73 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" _136_73))
in (_136_74, rng))
in FStar_Syntax_Syntax.Error (_136_75))
in (Prims.raise _136_76))
end
| FStar_Util.Inl (t) -> begin
t
end)
in ([], t, b))
end))))))
end
| _57_171 -> begin
(
# 191 "FStar.TypeChecker.Util.fst"
let _57_174 = (FStar_Syntax_Subst.open_univ_vars univ_vars t)
in (match (_57_174) with
| (univ_vars, t) -> begin
(univ_vars, t, false)
end))
end)))
end))

# 192 "FStar.TypeChecker.Util.fst"
let pat_as_exps : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term Prims.list * FStar_Syntax_Syntax.pat) = (fun allow_implicits env p -> (
# 207 "FStar.TypeChecker.Util.fst"
let rec pat_as_arg_with_env = (fun allow_wc_dependence env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(
# 216 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) None p.FStar_Syntax_Syntax.p)
in ([], [], [], env, e, p))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _57_187) -> begin
(
# 220 "FStar.TypeChecker.Util.fst"
let _57_193 = (FStar_Syntax_Util.type_u ())
in (match (_57_193) with
| (k, _57_192) -> begin
(
# 221 "FStar.TypeChecker.Util.fst"
let t = (new_uvar env k)
in (
# 222 "FStar.TypeChecker.Util.fst"
let x = (
# 222 "FStar.TypeChecker.Util.fst"
let _57_195 = x
in {FStar_Syntax_Syntax.ppname = _57_195.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_195.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (
# 223 "FStar.TypeChecker.Util.fst"
let _57_200 = (let _136_89 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _136_89 t))
in (match (_57_200) with
| (e, u) -> begin
(
# 224 "FStar.TypeChecker.Util.fst"
let p = (
# 224 "FStar.TypeChecker.Util.fst"
let _57_201 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, e)); FStar_Syntax_Syntax.ty = _57_201.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _57_201.FStar_Syntax_Syntax.p})
in ([], [], [], env, e, p))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 228 "FStar.TypeChecker.Util.fst"
let _57_209 = (FStar_Syntax_Util.type_u ())
in (match (_57_209) with
| (t, _57_208) -> begin
(
# 229 "FStar.TypeChecker.Util.fst"
let x = (
# 229 "FStar.TypeChecker.Util.fst"
let _57_210 = x
in (let _136_90 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _57_210.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_210.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _136_90}))
in (
# 230 "FStar.TypeChecker.Util.fst"
let env = if allow_wc_dependence then begin
(FStar_TypeChecker_Env.push_bv env x)
end else begin
env
end
in (
# 231 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in ((x)::[], [], (x)::[], env, e, p))))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 235 "FStar.TypeChecker.Util.fst"
let _57_220 = (FStar_Syntax_Util.type_u ())
in (match (_57_220) with
| (t, _57_219) -> begin
(
# 236 "FStar.TypeChecker.Util.fst"
let x = (
# 236 "FStar.TypeChecker.Util.fst"
let _57_221 = x
in (let _136_91 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _57_221.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_221.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _136_91}))
in (
# 237 "FStar.TypeChecker.Util.fst"
let env = (FStar_TypeChecker_Env.push_bv env x)
in (
# 238 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in ((x)::[], (x)::[], [], env, e, p))))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 242 "FStar.TypeChecker.Util.fst"
let _57_254 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _57_236 _57_239 -> (match ((_57_236, _57_239)) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(
# 243 "FStar.TypeChecker.Util.fst"
let _57_246 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_57_246) with
| (b', a', w', env, te, pat) -> begin
(
# 244 "FStar.TypeChecker.Util.fst"
let arg = if imp then begin
(FStar_Syntax_Syntax.iarg te)
end else begin
(FStar_Syntax_Syntax.as_arg te)
end
in ((b')::b, (a')::a, (w')::w, env, (arg)::args, ((pat, imp))::pats))
end))
end)) ([], [], [], env, [], [])))
in (match (_57_254) with
| (b, a, w, env, args, pats) -> begin
(
# 247 "FStar.TypeChecker.Util.fst"
let e = (let _136_98 = (let _136_97 = (let _136_96 = (let _136_95 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (let _136_94 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app _136_95 _136_94 None p.FStar_Syntax_Syntax.p)))
in (_136_96, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))
in FStar_Syntax_Syntax.Tm_meta (_136_97))
in (FStar_Syntax_Syntax.mk _136_98 None p.FStar_Syntax_Syntax.p))
in (let _136_101 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _136_100 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _136_99 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in (_136_101, _136_100, _136_99, env, e, (
# 253 "FStar.TypeChecker.Util.fst"
let _57_256 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _57_256.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _57_256.FStar_Syntax_Syntax.p}))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (_57_259) -> begin
(FStar_All.failwith "impossible")
end))
in (
# 257 "FStar.TypeChecker.Util.fst"
let rec elaborate_pat = (fun env p -> (
# 258 "FStar.TypeChecker.Util.fst"
let maybe_dot = (fun inaccessible a r -> if (allow_implicits && inaccessible) then begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term ((a, FStar_Syntax_Syntax.tun))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end else begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var (a)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end)
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 264 "FStar.TypeChecker.Util.fst"
let pats = (FStar_List.map (fun _57_274 -> (match (_57_274) with
| (p, imp) -> begin
(let _136_113 = (elaborate_pat env p)
in (_136_113, imp))
end)) pats)
in (
# 265 "FStar.TypeChecker.Util.fst"
let _57_279 = (FStar_TypeChecker_Env.lookup_datacon env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_279) with
| (_57_277, t) -> begin
(
# 266 "FStar.TypeChecker.Util.fst"
let _57_283 = (FStar_Syntax_Util.arrow_formals t)
in (match (_57_283) with
| (f, _57_282) -> begin
(
# 267 "FStar.TypeChecker.Util.fst"
let rec aux = (fun formals pats -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _57_294::_57_292) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))))
end
| (_57_300::_57_298, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun _57_306 -> (match (_57_306) with
| (t, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(
# 273 "FStar.TypeChecker.Util.fst"
let a = (let _136_120 = (let _136_119 = (FStar_Syntax_Syntax.range_of_bv t)
in Some (_136_119))
in (FStar_Syntax_Syntax.new_bv _136_120 FStar_Syntax_Syntax.tun))
in (
# 274 "FStar.TypeChecker.Util.fst"
let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (let _136_121 = (maybe_dot inaccessible a r)
in (_136_121, true))))
end
| _57_313 -> begin
(let _136_125 = (let _136_124 = (let _136_123 = (let _136_122 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _136_122))
in (_136_123, (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in FStar_Syntax_Syntax.Error (_136_124))
in (Prims.raise _136_125))
end)
end))))
end
| (f::formals', (p, p_imp)::pats') -> begin
(match (f) with
| (_57_324, Some (FStar_Syntax_Syntax.Implicit (_57_326))) when p_imp -> begin
(let _136_126 = (aux formals' pats')
in ((p, true))::_136_126)
end
| (_57_331, Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(
# 286 "FStar.TypeChecker.Util.fst"
let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (
# 287 "FStar.TypeChecker.Util.fst"
let p = (maybe_dot inaccessible a (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
in (let _136_127 = (aux formals' pats)
in ((p, true))::_136_127)))
end
| (_57_339, imp) -> begin
(let _136_130 = (let _136_128 = (FStar_Syntax_Syntax.is_implicit imp)
in (p, _136_128))
in (let _136_129 = (aux formals' pats')
in (_136_130)::_136_129))
end)
end))
in (
# 293 "FStar.TypeChecker.Util.fst"
let _57_342 = p
in (let _136_133 = (let _136_132 = (let _136_131 = (aux f pats)
in (fv, _136_131))
in FStar_Syntax_Syntax.Pat_cons (_136_132))
in {FStar_Syntax_Syntax.v = _136_133; FStar_Syntax_Syntax.ty = _57_342.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _57_342.FStar_Syntax_Syntax.p})))
end))
end)))
end
| _57_345 -> begin
p
end)))
in (
# 297 "FStar.TypeChecker.Util.fst"
let one_pat = (fun allow_wc_dependence env p -> (
# 298 "FStar.TypeChecker.Util.fst"
let p = (elaborate_pat env p)
in (
# 299 "FStar.TypeChecker.Util.fst"
let _57_357 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_57_357) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))) with
| Some (x) -> begin
(let _136_142 = (let _136_141 = (let _136_140 = (FStar_TypeChecker_Errors.nonlinear_pattern_variable x)
in (_136_140, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_136_141))
in (Prims.raise _136_142))
end
| _57_361 -> begin
(b, a, w, arg, p)
end)
end))))
in (
# 304 "FStar.TypeChecker.Util.fst"
let top_level_pat_as_args = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_disj (q::pats) -> begin
(
# 311 "FStar.TypeChecker.Util.fst"
let _57_377 = (one_pat false env q)
in (match (_57_377) with
| (b, a, _57_374, te, q) -> begin
(
# 312 "FStar.TypeChecker.Util.fst"
let _57_392 = (FStar_List.fold_right (fun p _57_382 -> (match (_57_382) with
| (w, args, pats) -> begin
(
# 313 "FStar.TypeChecker.Util.fst"
let _57_388 = (one_pat false env p)
in (match (_57_388) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv FStar_Syntax_Syntax.bv_eq a a'))) then begin
(let _136_152 = (let _136_151 = (let _136_150 = (FStar_TypeChecker_Errors.disjunctive_pattern_vars a a')
in (let _136_149 = (FStar_TypeChecker_Env.get_range env)
in (_136_150, _136_149)))
in FStar_Syntax_Syntax.Error (_136_151))
in (Prims.raise _136_152))
end else begin
(let _136_154 = (let _136_153 = (FStar_Syntax_Syntax.as_arg arg)
in (_136_153)::args)
in ((FStar_List.append w' w), _136_154, (p)::pats))
end
end))
end)) pats ([], [], []))
in (match (_57_392) with
| (w, args, pats) -> begin
(let _136_156 = (let _136_155 = (FStar_Syntax_Syntax.as_arg te)
in (_136_155)::args)
in ((FStar_List.append b w), _136_156, (
# 318 "FStar.TypeChecker.Util.fst"
let _57_393 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((q)::pats); FStar_Syntax_Syntax.ty = _57_393.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _57_393.FStar_Syntax_Syntax.p})))
end))
end))
end
| _57_396 -> begin
(
# 321 "FStar.TypeChecker.Util.fst"
let _57_404 = (one_pat true env p)
in (match (_57_404) with
| (b, _57_399, _57_401, arg, p) -> begin
(let _136_158 = (let _136_157 = (FStar_Syntax_Syntax.as_arg arg)
in (_136_157)::[])
in (b, _136_158, p))
end))
end))
in (
# 324 "FStar.TypeChecker.Util.fst"
let _57_408 = (top_level_pat_as_args env p)
in (match (_57_408) with
| (b, args, p) -> begin
(
# 325 "FStar.TypeChecker.Util.fst"
let exps = (FStar_All.pipe_right args (FStar_List.map Prims.fst))
in (b, exps, p))
end)))))))

# 326 "FStar.TypeChecker.Util.fst"
let decorate_pattern : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.pat = (fun env p exps -> (
# 329 "FStar.TypeChecker.Util.fst"
let qq = p
in (
# 330 "FStar.TypeChecker.Util.fst"
let rec aux = (fun p e -> (
# 331 "FStar.TypeChecker.Util.fst"
let pkg = (fun q t -> (FStar_Syntax_Syntax.withinfo q t p.FStar_Syntax_Syntax.p))
in (
# 332 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Util.unmeta e)
in (match ((p.FStar_Syntax_Syntax.v, e.FStar_Syntax_Syntax.n)) with
| (_57_422, FStar_Syntax_Syntax.Tm_uinst (e, _57_425)) -> begin
(aux p e)
end
| (FStar_Syntax_Syntax.Pat_constant (_57_430), FStar_Syntax_Syntax.Tm_constant (_57_433)) -> begin
(let _136_173 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v _136_173))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(
# 340 "FStar.TypeChecker.Util.fst"
let _57_441 = if (not ((FStar_Syntax_Syntax.bv_eq x y))) then begin
(let _136_176 = (let _136_175 = (FStar_Syntax_Print.bv_to_string x)
in (let _136_174 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _136_175 _136_174)))
in (FStar_All.failwith _136_176))
end else begin
()
end
in (
# 342 "FStar.TypeChecker.Util.fst"
let _57_443 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _136_178 = (FStar_Syntax_Print.bv_to_string x)
in (let _136_177 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _136_178 _136_177)))
end else begin
()
end
in (
# 344 "FStar.TypeChecker.Util.fst"
let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (
# 345 "FStar.TypeChecker.Util.fst"
let x = (
# 345 "FStar.TypeChecker.Util.fst"
let _57_446 = x
in {FStar_Syntax_Syntax.ppname = _57_446.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_446.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x)) s.FStar_Syntax_Syntax.n)))))
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(
# 349 "FStar.TypeChecker.Util.fst"
let _57_454 = if (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation) then begin
(let _136_181 = (let _136_180 = (FStar_Syntax_Print.bv_to_string x)
in (let _136_179 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _136_180 _136_179)))
in (FStar_All.failwith _136_181))
end else begin
()
end
in (
# 351 "FStar.TypeChecker.Util.fst"
let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (
# 352 "FStar.TypeChecker.Util.fst"
let x = (
# 352 "FStar.TypeChecker.Util.fst"
let _57_457 = x
in {FStar_Syntax_Syntax.ppname = _57_457.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_457.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x)) s.FStar_Syntax_Syntax.n))))
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _57_462), _57_466) -> begin
(
# 356 "FStar.TypeChecker.Util.fst"
let s = (force_sort e)
in (
# 357 "FStar.TypeChecker.Util.fst"
let x = (
# 357 "FStar.TypeChecker.Util.fst"
let _57_469 = x
in {FStar_Syntax_Syntax.ppname = _57_469.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_469.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
(
# 361 "FStar.TypeChecker.Util.fst"
let _57_479 = if (not ((FStar_Syntax_Syntax.fv_eq fv fv'))) then begin
(let _136_182 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _136_182))
end else begin
()
end
in (let _136_183 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv', []))) _136_183)))
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
(
# 368 "FStar.TypeChecker.Util.fst"
let _57_522 = if (let _136_184 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right _136_184 Prims.op_Negation)) then begin
(let _136_185 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _136_185))
end else begin
()
end
in (
# 371 "FStar.TypeChecker.Util.fst"
let fv = fv'
in (
# 372 "FStar.TypeChecker.Util.fst"
let rec match_args = (fun matched_pats args argpats -> (match ((args, argpats)) with
| ([], []) -> begin
(let _136_192 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev matched_pats)))) _136_192))
end
| (arg::args, (argpat, _57_538)::argpats) -> begin
(match ((arg, argpat.FStar_Syntax_Syntax.v)) with
| ((e, Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (_57_548)) -> begin
(
# 377 "FStar.TypeChecker.Util.fst"
let x = (let _136_193 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _136_193))
in (
# 378 "FStar.TypeChecker.Util.fst"
let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((e, imp), _57_557) -> begin
(
# 382 "FStar.TypeChecker.Util.fst"
let pat = (let _136_195 = (aux argpat e)
in (let _136_194 = (FStar_Syntax_Syntax.is_implicit imp)
in (_136_195, _136_194)))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _57_561 -> begin
(let _136_198 = (let _136_197 = (FStar_Syntax_Print.pat_to_string p)
in (let _136_196 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _136_197 _136_196)))
in (FStar_All.failwith _136_198))
end))
in (match_args [] args argpats))))
end
| _57_563 -> begin
(let _136_203 = (let _136_202 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (let _136_201 = (FStar_Syntax_Print.pat_to_string qq)
in (let _136_200 = (let _136_199 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right _136_199 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _136_202 _136_201 _136_200))))
in (FStar_All.failwith _136_203))
end))))
in (match ((p.FStar_Syntax_Syntax.v, exps)) with
| (FStar_Syntax_Syntax.Pat_disj (ps), _57_567) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(
# 395 "FStar.TypeChecker.Util.fst"
let ps = (FStar_List.map2 aux ps exps)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj (ps)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p))
end
| (_57_571, e::[]) -> begin
(aux p e)
end
| _57_576 -> begin
(FStar_All.failwith "Unexpected number of patterns")
end))))

# 401 "FStar.TypeChecker.Util.fst"
let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (
# 404 "FStar.TypeChecker.Util.fst"
let topt = Some (pat.FStar_Syntax_Syntax.ty)
in (
# 405 "FStar.TypeChecker.Util.fst"
let mk = (fun f -> (FStar_Syntax_Syntax.mk f topt pat.FStar_Syntax_Syntax.p))
in (
# 407 "FStar.TypeChecker.Util.fst"
let pat_as_arg = (fun _57_584 -> (match (_57_584) with
| (p, i) -> begin
(
# 408 "FStar.TypeChecker.Util.fst"
let _57_587 = (decorated_pattern_as_term p)
in (match (_57_587) with
| (vars, te) -> begin
(let _136_211 = (let _136_210 = (FStar_Syntax_Syntax.as_implicit i)
in (te, _136_210))
in (vars, _136_211))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_57_589) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _136_212 = (mk (FStar_Syntax_Syntax.Tm_constant (c)))
in ([], _136_212))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(let _136_213 = (mk (FStar_Syntax_Syntax.Tm_name (x)))
in ((x)::[], _136_213))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 422 "FStar.TypeChecker.Util.fst"
let _57_602 = (let _136_214 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _136_214 FStar_List.unzip))
in (match (_57_602) with
| (vars, args) -> begin
(
# 423 "FStar.TypeChecker.Util.fst"
let vars = (FStar_List.flatten vars)
in (let _136_218 = (let _136_217 = (let _136_216 = (let _136_215 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (_136_215, args))
in FStar_Syntax_Syntax.Tm_app (_136_216))
in (mk _136_217))
in (vars, _136_218)))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
([], e)
end)))))

# 427 "FStar.TypeChecker.Util.fst"
let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (
# 434 "FStar.TypeChecker.Util.fst"
let _57_626 = (match (c.FStar_Syntax_Syntax.effect_args) with
| (wp, _57_615)::(wlp, _57_611)::[] -> begin
(wp, wlp)
end
| _57_619 -> begin
(let _136_224 = (let _136_223 = (let _136_222 = (FStar_List.map (fun _57_623 -> (match (_57_623) with
| (x, _57_622) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right _136_222 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str _136_223))
in (FStar_All.failwith _136_224))
end)
in (match (_57_626) with
| (wp, wlp) -> begin
(c.FStar_Syntax_Syntax.result_typ, wp, wlp)
end)))

# 438 "FStar.TypeChecker.Util.fst"
let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (
# 441 "FStar.TypeChecker.Util.fst"
let _57_634 = (destruct_comp c)
in (match (_57_634) with
| (_57_631, wp, wlp) -> begin
(let _136_246 = (let _136_245 = (let _136_241 = (lift c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _136_241))
in (let _136_244 = (let _136_243 = (let _136_242 = (lift c.FStar_Syntax_Syntax.result_typ wlp)
in (FStar_Syntax_Syntax.as_arg _136_242))
in (_136_243)::[])
in (_136_245)::_136_244))
in {FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _136_246; FStar_Syntax_Syntax.flags = []})
end)))

# 445 "FStar.TypeChecker.Util.fst"
let norm_eff_name : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (
# 448 "FStar.TypeChecker.Util.fst"
let cache = (FStar_Util.smap_create 20)
in (fun env l -> (
# 450 "FStar.TypeChecker.Util.fst"
let rec find = (fun l -> (match ((FStar_TypeChecker_Env.lookup_effect_abbrev env FStar_Syntax_Syntax.U_unknown l)) with
| None -> begin
None
end
| Some (_57_642, c) -> begin
(
# 454 "FStar.TypeChecker.Util.fst"
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
# 458 "FStar.TypeChecker.Util.fst"
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
# 463 "FStar.TypeChecker.Util.fst"
let _57_656 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))

# 466 "FStar.TypeChecker.Util.fst"
let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (
# 470 "FStar.TypeChecker.Util.fst"
let _57_667 = (let _136_260 = (norm_eff_name env l1)
in (let _136_259 = (norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _136_260 _136_259)))
in (match (_57_667) with
| (m, _57_664, _57_666) -> begin
m
end)))

# 471 "FStar.TypeChecker.Util.fst"
let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> if ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2)) then begin
FStar_Syntax_Const.effect_Tot_lid
end else begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)

# 477 "FStar.TypeChecker.Util.fst"
let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)) = (fun env c1 c2 -> (
# 480 "FStar.TypeChecker.Util.fst"
let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (
# 481 "FStar.TypeChecker.Util.fst"
let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (
# 482 "FStar.TypeChecker.Util.fst"
let _57_679 = (FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (_57_679) with
| (m, lift1, lift2) -> begin
(
# 483 "FStar.TypeChecker.Util.fst"
let m1 = (lift_comp c1 m lift1)
in (
# 484 "FStar.TypeChecker.Util.fst"
let m2 = (lift_comp c2 m lift2)
in (
# 485 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (
# 486 "FStar.TypeChecker.Util.fst"
let _57_685 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (_57_685) with
| (a, kwp) -> begin
(let _136_274 = (destruct_comp m1)
in (let _136_273 = (destruct_comp m2)
in ((md, a, kwp), _136_274, _136_273)))
end)))))
end)))))

# 487 "FStar.TypeChecker.Util.fst"
let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (
# 490 "FStar.TypeChecker.Util.fst"
let l = (norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)))

# 491 "FStar.TypeChecker.Util.fst"
let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (
# 494 "FStar.TypeChecker.Util.fst"
let l = (norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid))))

# 496 "FStar.TypeChecker.Util.fst"
let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md result wp wlp flags -> (let _136_297 = (let _136_296 = (let _136_295 = (FStar_Syntax_Syntax.as_arg wp)
in (let _136_294 = (let _136_293 = (FStar_Syntax_Syntax.as_arg wlp)
in (_136_293)::[])
in (_136_295)::_136_294))
in {FStar_Syntax_Syntax.effect_name = md.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = _136_296; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp _136_297)))

# 502 "FStar.TypeChecker.Util.fst"
let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (
# 505 "FStar.TypeChecker.Util.fst"
let _57_699 = lc
in (let _136_304 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _57_699.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _136_304; FStar_Syntax_Syntax.cflags = _57_699.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _57_701 -> (match (()) with
| () -> begin
(let _136_303 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _136_303))
end))})))

# 506 "FStar.TypeChecker.Util.fst"
let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _136_307 = (FStar_Syntax_Subst.compress t)
in _136_307.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_704) -> begin
true
end
| _57_707 -> begin
false
end))

# 510 "FStar.TypeChecker.Util.fst"
let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v -> (
# 514 "FStar.TypeChecker.Util.fst"
let c = if (let _136_314 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation _136_314)) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(
# 517 "FStar.TypeChecker.Util.fst"
let m = (let _136_315 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must _136_315))
in (
# 518 "FStar.TypeChecker.Util.fst"
let _57_714 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_57_714) with
| (a, kwp) -> begin
(
# 519 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 520 "FStar.TypeChecker.Util.fst"
let wp = (let _136_323 = (let _136_322 = (let _136_317 = (let _136_316 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_136_316)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _136_317 env m m.FStar_Syntax_Syntax.ret))
in (let _136_321 = (let _136_320 = (FStar_Syntax_Syntax.as_arg t)
in (let _136_319 = (let _136_318 = (FStar_Syntax_Syntax.as_arg v)
in (_136_318)::[])
in (_136_320)::_136_319))
in (FStar_Syntax_Syntax.mk_Tm_app _136_322 _136_321 (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _136_323))
in (
# 521 "FStar.TypeChecker.Util.fst"
let wlp = wp
in (mk_comp m t wp wlp ((FStar_Syntax_Syntax.RETURN)::[])))))
end)))
end
in (
# 523 "FStar.TypeChecker.Util.fst"
let _57_719 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return"))) then begin
(let _136_326 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _136_325 = (FStar_Syntax_Print.term_to_string v)
in (let _136_324 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _136_326 _136_325 _136_324))))
end else begin
()
end
in c)))

# 526 "FStar.TypeChecker.Util.fst"
let bind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun env e1opt lc1 _57_726 -> (match (_57_726) with
| (b, lc2) -> begin
(
# 529 "FStar.TypeChecker.Util.fst"
let _57_734 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(
# 531 "FStar.TypeChecker.Util.fst"
let bstr = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _136_337 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (let _136_336 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _136_335 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" _136_337 _136_336 bstr _136_335)))))
end else begin
()
end
in (
# 537 "FStar.TypeChecker.Util.fst"
let bind_it = (fun _57_737 -> (match (()) with
| () -> begin
(
# 538 "FStar.TypeChecker.Util.fst"
let c1 = (lc1.FStar_Syntax_Syntax.comp ())
in (
# 539 "FStar.TypeChecker.Util.fst"
let c2 = (lc2.FStar_Syntax_Syntax.comp ())
in (
# 540 "FStar.TypeChecker.Util.fst"
let _57_743 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _136_344 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _136_343 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _136_342 = (FStar_Syntax_Print.comp_to_string c1)
in (let _136_341 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (let _136_340 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" _136_344 _136_343 _136_342 _136_341 _136_340))))))
end else begin
()
end
in (
# 549 "FStar.TypeChecker.Util.fst"
let try_simplify = (fun _57_746 -> (match (()) with
| () -> begin
(
# 550 "FStar.TypeChecker.Util.fst"
let aux = (fun _57_748 -> (match (()) with
| () -> begin
if (FStar_Syntax_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some ((c2, "trivial no binder"))
end
| Some (_57_751) -> begin
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
in (
# 561 "FStar.TypeChecker.Util.fst"
let subst_c2 = (fun reason -> (match ((e1opt, b)) with
| (Some (e), Some (x)) -> begin
(let _136_352 = (let _136_351 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT ((x, e)))::[]) c2)
in (_136_351, reason))
in Some (_136_352))
end
| _57_761 -> begin
(aux ())
end))
in if ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2)) then begin
(subst_c2 "both total")
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2)) then begin
(let _136_354 = (let _136_353 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in (_136_353, "both gtot"))
in Some (_136_354))
end else begin
(match ((e1opt, b)) with
| (Some (e), Some (x)) -> begin
if ((FStar_Syntax_Util.is_total_comp c1) && (not ((FStar_Syntax_Syntax.is_null_bv x)))) then begin
(subst_c2 "substituted e")
end else begin
(aux ())
end
end
| _57_768 -> begin
(aux ())
end)
end
end))
end))
in (match ((try_simplify ())) with
| Some (c, reason) -> begin
c
end
| None -> begin
(
# 582 "FStar.TypeChecker.Util.fst"
let _57_786 = (lift_and_destruct env c1 c2)
in (match (_57_786) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(
# 583 "FStar.TypeChecker.Util.fst"
let bs = (match (b) with
| None -> begin
(let _136_355 = (FStar_Syntax_Syntax.null_binder t1)
in (_136_355)::[])
end
| Some (x) -> begin
(let _136_356 = (FStar_Syntax_Syntax.mk_binder x)
in (_136_356)::[])
end)
in (
# 586 "FStar.TypeChecker.Util.fst"
let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp None))
in (
# 587 "FStar.TypeChecker.Util.fst"
let wp_args = (let _136_371 = (FStar_Syntax_Syntax.as_arg t1)
in (let _136_370 = (let _136_369 = (FStar_Syntax_Syntax.as_arg t2)
in (let _136_368 = (let _136_367 = (FStar_Syntax_Syntax.as_arg wp1)
in (let _136_366 = (let _136_365 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _136_364 = (let _136_363 = (let _136_359 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg _136_359))
in (let _136_362 = (let _136_361 = (let _136_360 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _136_360))
in (_136_361)::[])
in (_136_363)::_136_362))
in (_136_365)::_136_364))
in (_136_367)::_136_366))
in (_136_369)::_136_368))
in (_136_371)::_136_370))
in (
# 588 "FStar.TypeChecker.Util.fst"
let wlp_args = (let _136_379 = (FStar_Syntax_Syntax.as_arg t1)
in (let _136_378 = (let _136_377 = (FStar_Syntax_Syntax.as_arg t2)
in (let _136_376 = (let _136_375 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _136_374 = (let _136_373 = (let _136_372 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _136_372))
in (_136_373)::[])
in (_136_375)::_136_374))
in (_136_377)::_136_376))
in (_136_379)::_136_378))
in (
# 589 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t2)))::[]) kwp)
in (
# 590 "FStar.TypeChecker.Util.fst"
let us = (let _136_382 = (env.FStar_TypeChecker_Env.universe_of env t1)
in (let _136_381 = (let _136_380 = (env.FStar_TypeChecker_Env.universe_of env t2)
in (_136_380)::[])
in (_136_382)::_136_381))
in (
# 591 "FStar.TypeChecker.Util.fst"
let wp = (let _136_383 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _136_383 wp_args None t2.FStar_Syntax_Syntax.pos))
in (
# 592 "FStar.TypeChecker.Util.fst"
let wlp = (let _136_384 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wlp)
in (FStar_Syntax_Syntax.mk_Tm_app _136_384 wlp_args None t2.FStar_Syntax_Syntax.pos))
in (
# 593 "FStar.TypeChecker.Util.fst"
let c = (mk_comp md t2 wp wlp [])
in c)))))))))
end))
end)))))
end))
in (let _136_385 = (join_lcomp env lc1 lc2)
in {FStar_Syntax_Syntax.eff_name = _136_385; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it})))
end))

# 598 "FStar.TypeChecker.Util.fst"
let lift_formula : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t mk_wp mk_wlp f -> (
# 601 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 602 "FStar.TypeChecker.Util.fst"
let _57_808 = (FStar_TypeChecker_Env.wp_signature env md_pure.FStar_Syntax_Syntax.mname)
in (match (_57_808) with
| (a, kwp) -> begin
(
# 603 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 604 "FStar.TypeChecker.Util.fst"
let wp = (let _136_399 = (let _136_398 = (FStar_Syntax_Syntax.as_arg t)
in (let _136_397 = (let _136_396 = (FStar_Syntax_Syntax.as_arg f)
in (_136_396)::[])
in (_136_398)::_136_397))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wp _136_399 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (
# 605 "FStar.TypeChecker.Util.fst"
let wlp = (let _136_403 = (let _136_402 = (FStar_Syntax_Syntax.as_arg t)
in (let _136_401 = (let _136_400 = (FStar_Syntax_Syntax.as_arg f)
in (_136_400)::[])
in (_136_402)::_136_401))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wlp _136_403 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (mk_comp md_pure FStar_TypeChecker_Common.t_unit wp wlp []))))
end))))

# 606 "FStar.TypeChecker.Util.fst"
let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((f, FStar_Syntax_Syntax.Meta_labeled ((reason, r, false))))) None f.FStar_Syntax_Syntax.pos))

# 609 "FStar.TypeChecker.Util.fst"
let label_opt : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _136_427 = (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)
in (FStar_All.pipe_left Prims.op_Negation _136_427)) then begin
f
end else begin
(let _136_428 = (reason ())
in (label _136_428 r f))
end
end))

# 616 "FStar.TypeChecker.Util.fst"
let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 620 "FStar.TypeChecker.Util.fst"
let _57_828 = g
in (let _136_436 = (let _136_435 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_136_435))
in {FStar_TypeChecker_Env.guard_f = _136_436; FStar_TypeChecker_Env.deferred = _57_828.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_828.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_828.FStar_TypeChecker_Env.implicits}))
end))

# 620 "FStar.TypeChecker.Util.fst"
let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(
# 624 "FStar.TypeChecker.Util.fst"
let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| _57_839 -> begin
g2
end))

# 626 "FStar.TypeChecker.Util.fst"
let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (
# 629 "FStar.TypeChecker.Util.fst"
let weaken = (fun _57_844 -> (match (()) with
| () -> begin
(
# 630 "FStar.TypeChecker.Util.fst"
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
# 636 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 637 "FStar.TypeChecker.Util.fst"
let _57_853 = (destruct_comp c)
in (match (_57_853) with
| (res_t, wp, wlp) -> begin
(
# 638 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 639 "FStar.TypeChecker.Util.fst"
let us = (let _136_449 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_136_449)::[])
in (
# 640 "FStar.TypeChecker.Util.fst"
let wp = (let _136_456 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _136_455 = (let _136_454 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _136_453 = (let _136_452 = (FStar_Syntax_Syntax.as_arg f)
in (let _136_451 = (let _136_450 = (FStar_Syntax_Syntax.as_arg wp)
in (_136_450)::[])
in (_136_452)::_136_451))
in (_136_454)::_136_453))
in (FStar_Syntax_Syntax.mk_Tm_app _136_456 _136_455 None wp.FStar_Syntax_Syntax.pos)))
in (
# 641 "FStar.TypeChecker.Util.fst"
let wlp = (let _136_463 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _136_462 = (let _136_461 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _136_460 = (let _136_459 = (FStar_Syntax_Syntax.as_arg f)
in (let _136_458 = (let _136_457 = (FStar_Syntax_Syntax.as_arg wlp)
in (_136_457)::[])
in (_136_459)::_136_458))
in (_136_461)::_136_460))
in (FStar_Syntax_Syntax.mk_Tm_app _136_463 _136_462 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp c.FStar_Syntax_Syntax.flags)))))
end)))
end
end))
end))
in (
# 643 "FStar.TypeChecker.Util.fst"
let _57_858 = lc
in {FStar_Syntax_Syntax.eff_name = _57_858.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _57_858.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _57_858.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))

# 643 "FStar.TypeChecker.Util.fst"
let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> if (FStar_TypeChecker_Rel.is_trivial g0) then begin
(lc, g0)
end else begin
(
# 649 "FStar.TypeChecker.Util.fst"
let _57_865 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _136_483 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _136_482 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _136_483 _136_482)))
end else begin
()
end
in (
# 653 "FStar.TypeChecker.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _57_2 -> (match (_57_2) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _57_871 -> begin
[]
end))))
in (
# 654 "FStar.TypeChecker.Util.fst"
let strengthen = (fun _57_874 -> (match (()) with
| () -> begin
(
# 655 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 656 "FStar.TypeChecker.Util.fst"
let g0 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (match ((FStar_TypeChecker_Rel.guard_form g0)) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 660 "FStar.TypeChecker.Util.fst"
let c = if ((FStar_Syntax_Util.is_pure_or_ghost_comp c) && (not ((FStar_Syntax_Util.is_partial_return c)))) then begin
(
# 663 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.gen_bv "strengthen_pre_x" None (FStar_Syntax_Util.comp_result c))
in (
# 664 "FStar.TypeChecker.Util.fst"
let xret = (let _136_488 = (let _136_487 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _136_487))
in (FStar_Syntax_Util.comp_set_flags _136_488 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (
# 665 "FStar.TypeChecker.Util.fst"
let lc = (bind env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), (FStar_Syntax_Util.lcomp_of_comp xret)))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (
# 669 "FStar.TypeChecker.Util.fst"
let _57_884 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _136_490 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _136_489 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _136_490 _136_489)))
end else begin
()
end
in (
# 674 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 675 "FStar.TypeChecker.Util.fst"
let _57_890 = (destruct_comp c)
in (match (_57_890) with
| (res_t, wp, wlp) -> begin
(
# 676 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 677 "FStar.TypeChecker.Util.fst"
let us = (let _136_491 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_136_491)::[])
in (
# 678 "FStar.TypeChecker.Util.fst"
let wp = (let _136_500 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assert_p)
in (let _136_499 = (let _136_498 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _136_497 = (let _136_496 = (let _136_493 = (let _136_492 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason _136_492 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _136_493))
in (let _136_495 = (let _136_494 = (FStar_Syntax_Syntax.as_arg wp)
in (_136_494)::[])
in (_136_496)::_136_495))
in (_136_498)::_136_497))
in (FStar_Syntax_Syntax.mk_Tm_app _136_500 _136_499 None wp.FStar_Syntax_Syntax.pos)))
in (
# 679 "FStar.TypeChecker.Util.fst"
let wlp = (let _136_507 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _136_506 = (let _136_505 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _136_504 = (let _136_503 = (FStar_Syntax_Syntax.as_arg f)
in (let _136_502 = (let _136_501 = (FStar_Syntax_Syntax.as_arg wlp)
in (_136_501)::[])
in (_136_503)::_136_502))
in (_136_505)::_136_504))
in (FStar_Syntax_Syntax.mk_Tm_app _136_507 _136_506 None wlp.FStar_Syntax_Syntax.pos)))
in (
# 681 "FStar.TypeChecker.Util.fst"
let _57_895 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _136_508 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _136_508))
end else begin
()
end
in (
# 685 "FStar.TypeChecker.Util.fst"
let c2 = (mk_comp md res_t wp wlp flags)
in c2))))))
end)))))
end)))
end))
in (let _136_512 = (
# 687 "FStar.TypeChecker.Util.fst"
let _57_898 = lc
in (let _136_511 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _136_510 = if ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _136_509 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _136_509))) then begin
flags
end else begin
[]
end
in {FStar_Syntax_Syntax.eff_name = _136_511; FStar_Syntax_Syntax.res_typ = _57_898.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _136_510; FStar_Syntax_Syntax.comp = strengthen})))
in (_136_512, (
# 690 "FStar.TypeChecker.Util.fst"
let _57_900 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_900.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_900.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_900.FStar_TypeChecker_Env.implicits}))))))
end)

# 690 "FStar.TypeChecker.Util.fst"
let record_application_site : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (
# 693 "FStar.TypeChecker.Util.fst"
let comp = (fun _57_906 -> (match (()) with
| () -> begin
(
# 694 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 695 "FStar.TypeChecker.Util.fst"
let res_t = (FStar_Syntax_Util.comp_result c)
in if (((FStar_Syntax_Util.is_trivial_wp c) || (let _136_521 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals _136_521 FStar_Syntax_Const.prims_lid))) || (FStar_Syntax_Syntax.is_teff res_t)) then begin
c
end else begin
(
# 700 "FStar.TypeChecker.Util.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (FStar_TypeChecker_Common.t_unit)))
in (
# 701 "FStar.TypeChecker.Util.fst"
let _57_914 = (strengthen_precondition (Some ((fun _57_910 -> (match (()) with
| () -> begin
"push"
end)))) env e (FStar_Syntax_Util.lcomp_of_comp c) g)
in (match (_57_914) with
| (c, _57_913) -> begin
(
# 702 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 703 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 704 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 705 "FStar.TypeChecker.Util.fst"
let us = (let _136_525 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_136_525)::[])
in (
# 706 "FStar.TypeChecker.Util.fst"
let xret = (let _136_530 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _136_529 = (let _136_528 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _136_527 = (let _136_526 = (FStar_Syntax_Syntax.as_arg xexp)
in (_136_526)::[])
in (_136_528)::_136_527))
in (FStar_Syntax_Syntax.mk_Tm_app _136_530 _136_529 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 707 "FStar.TypeChecker.Util.fst"
let xret_comp = (let _136_531 = (mk_comp md_pure res_t xret xret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _136_531))
in (
# 708 "FStar.TypeChecker.Util.fst"
let lc = (let _136_537 = (let _136_536 = (let _136_535 = (strengthen_precondition (Some ((fun _57_921 -> (match (()) with
| () -> begin
"pop"
end)))) env xexp xret_comp g)
in (FStar_All.pipe_left Prims.fst _136_535))
in (Some (x), _136_536))
in (bind env None c _136_537))
in (lc.FStar_Syntax_Syntax.comp ()))))))))
end)))
end))
end))
in (
# 710 "FStar.TypeChecker.Util.fst"
let _57_923 = lc
in {FStar_Syntax_Syntax.eff_name = _57_923.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _57_923.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _57_923.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = comp})))

# 710 "FStar.TypeChecker.Util.fst"
let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env comp res_t -> (
# 713 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 714 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 715 "FStar.TypeChecker.Util.fst"
let y = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 716 "FStar.TypeChecker.Util.fst"
let _57_933 = (let _136_545 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _136_544 = (FStar_Syntax_Syntax.bv_to_name y)
in (_136_545, _136_544)))
in (match (_57_933) with
| (xexp, yexp) -> begin
(
# 717 "FStar.TypeChecker.Util.fst"
let us = (let _136_546 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_136_546)::[])
in (
# 718 "FStar.TypeChecker.Util.fst"
let yret = (let _136_551 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _136_550 = (let _136_549 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _136_548 = (let _136_547 = (FStar_Syntax_Syntax.as_arg yexp)
in (_136_547)::[])
in (_136_549)::_136_548))
in (FStar_Syntax_Syntax.mk_Tm_app _136_551 _136_550 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 719 "FStar.TypeChecker.Util.fst"
let x_eq_y_yret = (let _136_559 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _136_558 = (let _136_557 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _136_556 = (let _136_555 = (let _136_552 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _136_552))
in (let _136_554 = (let _136_553 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_136_553)::[])
in (_136_555)::_136_554))
in (_136_557)::_136_556))
in (FStar_Syntax_Syntax.mk_Tm_app _136_559 _136_558 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 720 "FStar.TypeChecker.Util.fst"
let forall_y_x_eq_y_yret = (let _136_569 = (FStar_TypeChecker_Env.inst_effect_fun_with (FStar_List.append us us) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _136_568 = (let _136_567 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _136_566 = (let _136_565 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _136_564 = (let _136_563 = (let _136_562 = (let _136_561 = (let _136_560 = (FStar_Syntax_Syntax.mk_binder y)
in (_136_560)::[])
in (FStar_Syntax_Util.abs _136_561 x_eq_y_yret None))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _136_562))
in (_136_563)::[])
in (_136_565)::_136_564))
in (_136_567)::_136_566))
in (FStar_Syntax_Syntax.mk_Tm_app _136_569 _136_568 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 721 "FStar.TypeChecker.Util.fst"
let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (
# 722 "FStar.TypeChecker.Util.fst"
let lc = (bind env None (FStar_Syntax_Util.lcomp_of_comp comp) (Some (x), (FStar_Syntax_Util.lcomp_of_comp lc2)))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))

# 723 "FStar.TypeChecker.Util.fst"
let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (
# 726 "FStar.TypeChecker.Util.fst"
let comp = (fun _57_945 -> (match (()) with
| () -> begin
(
# 727 "FStar.TypeChecker.Util.fst"
let _57_961 = (let _136_581 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _136_580 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _136_581 _136_580)))
in (match (_57_961) with
| ((md, _57_948, _57_950), (res_t, wp_then, wlp_then), (_57_957, wp_else, wlp_else)) -> begin
(
# 728 "FStar.TypeChecker.Util.fst"
let us = (let _136_582 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_136_582)::[])
in (
# 729 "FStar.TypeChecker.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _136_602 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _136_601 = (let _136_599 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _136_598 = (let _136_597 = (FStar_Syntax_Syntax.as_arg g)
in (let _136_596 = (let _136_595 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _136_594 = (let _136_593 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_136_593)::[])
in (_136_595)::_136_594))
in (_136_597)::_136_596))
in (_136_599)::_136_598))
in (let _136_600 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _136_602 _136_601 None _136_600)))))
in (
# 730 "FStar.TypeChecker.Util.fst"
let wp = (ifthenelse md res_t guard wp_then wp_else)
in (
# 731 "FStar.TypeChecker.Util.fst"
let wlp = (ifthenelse md res_t guard wlp_then wlp_else)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(
# 733 "FStar.TypeChecker.Util.fst"
let comp = (mk_comp md res_t wp wlp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(
# 735 "FStar.TypeChecker.Util.fst"
let wp = (let _136_609 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _136_608 = (let _136_607 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _136_606 = (let _136_605 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _136_604 = (let _136_603 = (FStar_Syntax_Syntax.as_arg wp)
in (_136_603)::[])
in (_136_605)::_136_604))
in (_136_607)::_136_606))
in (FStar_Syntax_Syntax.mk_Tm_app _136_609 _136_608 None wp.FStar_Syntax_Syntax.pos)))
in (
# 736 "FStar.TypeChecker.Util.fst"
let wlp = (let _136_614 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _136_613 = (let _136_612 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _136_611 = (let _136_610 = (FStar_Syntax_Syntax.as_arg wlp)
in (_136_610)::[])
in (_136_612)::_136_611))
in (FStar_Syntax_Syntax.mk_Tm_app _136_614 _136_613 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end))))
end))
end))
in (let _136_615 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _136_615; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp})))

# 741 "FStar.TypeChecker.Util.fst"
let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (let _136_621 = (let _136_620 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid _136_620))
in (FStar_Syntax_Syntax.fvar _136_621 FStar_Syntax_Syntax.Delta_constant None)))

# 743 "FStar.TypeChecker.Util.fst"
let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (
# 746 "FStar.TypeChecker.Util.fst"
let eff = (FStar_List.fold_left (fun eff _57_983 -> (match (_57_983) with
| (_57_981, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (
# 747 "FStar.TypeChecker.Util.fst"
let bind_cases = (fun _57_986 -> (match (()) with
| () -> begin
(
# 748 "FStar.TypeChecker.Util.fst"
let us = (let _136_632 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_136_632)::[])
in (
# 749 "FStar.TypeChecker.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _136_652 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _136_651 = (let _136_649 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _136_648 = (let _136_647 = (FStar_Syntax_Syntax.as_arg g)
in (let _136_646 = (let _136_645 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _136_644 = (let _136_643 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_136_643)::[])
in (_136_645)::_136_644))
in (_136_647)::_136_646))
in (_136_649)::_136_648))
in (let _136_650 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _136_652 _136_651 None _136_650)))))
in (
# 751 "FStar.TypeChecker.Util.fst"
let default_case = (
# 752 "FStar.TypeChecker.Util.fst"
let post_k = (let _136_655 = (let _136_653 = (FStar_Syntax_Syntax.null_binder res_t)
in (_136_653)::[])
in (let _136_654 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _136_655 _136_654)))
in (
# 753 "FStar.TypeChecker.Util.fst"
let kwp = (let _136_658 = (let _136_656 = (FStar_Syntax_Syntax.null_binder post_k)
in (_136_656)::[])
in (let _136_657 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _136_658 _136_657)))
in (
# 754 "FStar.TypeChecker.Util.fst"
let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (
# 755 "FStar.TypeChecker.Util.fst"
let wp = (let _136_664 = (let _136_659 = (FStar_Syntax_Syntax.mk_binder post)
in (_136_659)::[])
in (let _136_663 = (let _136_662 = (let _136_660 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Errors.exhaustiveness_check _136_660))
in (let _136_661 = (fvar_const env FStar_Syntax_Const.false_lid)
in (FStar_All.pipe_left _136_662 _136_661)))
in (FStar_Syntax_Util.abs _136_664 _136_663 None)))
in (
# 756 "FStar.TypeChecker.Util.fst"
let wlp = (let _136_667 = (let _136_665 = (FStar_Syntax_Syntax.mk_binder post)
in (_136_665)::[])
in (let _136_666 = (fvar_const env FStar_Syntax_Const.true_lid)
in (FStar_Syntax_Util.abs _136_667 _136_666 None)))
in (
# 757 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (
# 759 "FStar.TypeChecker.Util.fst"
let comp = (FStar_List.fold_right (fun _57_1003 celse -> (match (_57_1003) with
| (g, cthen) -> begin
(
# 760 "FStar.TypeChecker.Util.fst"
let _57_1021 = (let _136_670 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _136_670 celse))
in (match (_57_1021) with
| ((md, _57_1007, _57_1009), (_57_1012, wp_then, wlp_then), (_57_1017, wp_else, wlp_else)) -> begin
(let _136_672 = (ifthenelse md res_t g wp_then wp_else)
in (let _136_671 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _136_672 _136_671 [])))
end))
end)) lcases default_case)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(add_equality_to_post_condition env comp res_t)
end else begin
(
# 764 "FStar.TypeChecker.Util.fst"
let comp = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (
# 765 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env comp.FStar_Syntax_Syntax.effect_name)
in (
# 766 "FStar.TypeChecker.Util.fst"
let _57_1029 = (destruct_comp comp)
in (match (_57_1029) with
| (_57_1026, wp, wlp) -> begin
(
# 767 "FStar.TypeChecker.Util.fst"
let wp = (let _136_679 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _136_678 = (let _136_677 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _136_676 = (let _136_675 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _136_674 = (let _136_673 = (FStar_Syntax_Syntax.as_arg wp)
in (_136_673)::[])
in (_136_675)::_136_674))
in (_136_677)::_136_676))
in (FStar_Syntax_Syntax.mk_Tm_app _136_679 _136_678 None wp.FStar_Syntax_Syntax.pos)))
in (
# 768 "FStar.TypeChecker.Util.fst"
let wlp = (let _136_684 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _136_683 = (let _136_682 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _136_681 = (let _136_680 = (FStar_Syntax_Syntax.as_arg wlp)
in (_136_680)::[])
in (_136_682)::_136_681))
in (FStar_Syntax_Syntax.mk_Tm_app _136_684 _136_683 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end))))
end))))
end))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))

# 773 "FStar.TypeChecker.Util.fst"
let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (
# 776 "FStar.TypeChecker.Util.fst"
let close = (fun _57_1036 -> (match (()) with
| () -> begin
(
# 777 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in if (FStar_Syntax_Util.is_ml_comp c) then begin
c
end else begin
(
# 780 "FStar.TypeChecker.Util.fst"
let close_wp = (fun u_res md res_t bvs wp0 -> (FStar_List.fold_right (fun x wp -> (
# 782 "FStar.TypeChecker.Util.fst"
let bs = (let _136_705 = (FStar_Syntax_Syntax.mk_binder x)
in (_136_705)::[])
in (
# 783 "FStar.TypeChecker.Util.fst"
let us = (let _136_707 = (let _136_706 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (_136_706)::[])
in (u_res)::_136_707)
in (
# 784 "FStar.TypeChecker.Util.fst"
let wp = (FStar_Syntax_Util.abs bs wp None)
in (let _136_714 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (let _136_713 = (let _136_712 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _136_711 = (let _136_710 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _136_709 = (let _136_708 = (FStar_Syntax_Syntax.as_arg wp)
in (_136_708)::[])
in (_136_710)::_136_709))
in (_136_712)::_136_711))
in (FStar_Syntax_Syntax.mk_Tm_app _136_714 _136_713 None wp0.FStar_Syntax_Syntax.pos))))))) bvs wp0))
in (
# 787 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 788 "FStar.TypeChecker.Util.fst"
let _57_1053 = (destruct_comp c)
in (match (_57_1053) with
| (t, wp, wlp) -> begin
(
# 789 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 790 "FStar.TypeChecker.Util.fst"
let u_res = (env.FStar_TypeChecker_Env.universe_of env c.FStar_Syntax_Syntax.result_typ)
in (
# 791 "FStar.TypeChecker.Util.fst"
let wp = (close_wp u_res md c.FStar_Syntax_Syntax.result_typ bvs wp)
in (
# 792 "FStar.TypeChecker.Util.fst"
let wlp = (close_wp u_res md c.FStar_Syntax_Syntax.result_typ bvs wlp)
in (mk_comp md c.FStar_Syntax_Syntax.result_typ wp wlp c.FStar_Syntax_Syntax.flags)))))
end))))
end)
end))
in (
# 794 "FStar.TypeChecker.Util.fst"
let _57_1058 = lc
in {FStar_Syntax_Syntax.eff_name = _57_1058.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _57_1058.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _57_1058.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))

# 794 "FStar.TypeChecker.Util.fst"
let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (
# 797 "FStar.TypeChecker.Util.fst"
let refine = (fun _57_1064 -> (match (()) with
| () -> begin
(
# 798 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in if (not ((is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name))) then begin
c
end else begin
if (FStar_Syntax_Util.is_partial_return c) then begin
c
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c) && (not ((FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)))) then begin
(let _136_725 = (let _136_724 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _136_723 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _136_724 _136_723)))
in (FStar_All.failwith _136_725))
end else begin
(
# 806 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 807 "FStar.TypeChecker.Util.fst"
let t = c.FStar_Syntax_Syntax.result_typ
in (
# 808 "FStar.TypeChecker.Util.fst"
let c = (FStar_Syntax_Syntax.mk_Comp c)
in (
# 809 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (
# 810 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 811 "FStar.TypeChecker.Util.fst"
let ret = (let _136_727 = (let _136_726 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _136_726 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _136_727))
in (
# 812 "FStar.TypeChecker.Util.fst"
let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (
# 813 "FStar.TypeChecker.Util.fst"
let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (
# 815 "FStar.TypeChecker.Util.fst"
let c = (let _136_729 = (let _136_728 = (bind env None (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), eq_ret))
in (_136_728.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _136_729 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
in c)))))))))
end
end
end)
end))
in (
# 818 "FStar.TypeChecker.Util.fst"
let flags = if (((not ((FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)) && (not ((FStar_Syntax_Util.is_lcomp_partial_return lc)))) then begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_Syntax_Syntax.cflags
end else begin
lc.FStar_Syntax_Syntax.cflags
end
in (
# 824 "FStar.TypeChecker.Util.fst"
let _57_1076 = lc
in {FStar_Syntax_Syntax.eff_name = _57_1076.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _57_1076.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))

# 824 "FStar.TypeChecker.Util.fst"
let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (match ((FStar_TypeChecker_Rel.sub_comp env c c')) with
| None -> begin
(let _136_741 = (let _136_740 = (let _136_739 = (FStar_TypeChecker_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _136_738 = (FStar_TypeChecker_Env.get_range env)
in (_136_739, _136_738)))
in FStar_Syntax_Syntax.Error (_136_740))
in (Prims.raise _136_741))
end
| Some (g) -> begin
(e, c', g)
end))

# 830 "FStar.TypeChecker.Util.fst"
let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match ((let _136_750 = (FStar_Syntax_Subst.compress t)
in _136_750.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_1090) -> begin
(match ((let _136_751 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _136_751.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid) -> begin
(
# 837 "FStar.TypeChecker.Util.fst"
let _57_1094 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (
# 838 "FStar.TypeChecker.Util.fst"
let b2t = (let _136_752 = (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar _136_752 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (
# 839 "FStar.TypeChecker.Util.fst"
let lc = (let _136_755 = (let _136_754 = (let _136_753 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _136_753))
in (None, _136_754))
in (bind env (Some (e)) lc _136_755))
in (
# 840 "FStar.TypeChecker.Util.fst"
let e = (let _136_757 = (let _136_756 = (FStar_Syntax_Syntax.as_arg e)
in (_136_756)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _136_757 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (e, lc)))))
end
| _57_1100 -> begin
(e, lc)
end)
end
| _57_1102 -> begin
(e, lc)
end))

# 845 "FStar.TypeChecker.Util.fst"
let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (
# 848 "FStar.TypeChecker.Util.fst"
let gopt = if env.FStar_TypeChecker_Env.use_eq then begin
(let _136_766 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in (_136_766, false))
end else begin
(let _136_767 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in (_136_767, true))
end
in (match (gopt) with
| (None, _57_1110) -> begin
(FStar_TypeChecker_Rel.subtype_fail env lc.FStar_Syntax_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(match ((FStar_TypeChecker_Rel.guard_form g)) with
| FStar_TypeChecker_Common.Trivial -> begin
(
# 856 "FStar.TypeChecker.Util.fst"
let lc = (
# 856 "FStar.TypeChecker.Util.fst"
let _57_1117 = lc
in {FStar_Syntax_Syntax.eff_name = _57_1117.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _57_1117.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _57_1117.FStar_Syntax_Syntax.comp})
in (e, lc, g))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 860 "FStar.TypeChecker.Util.fst"
let g = (
# 860 "FStar.TypeChecker.Util.fst"
let _57_1122 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_1122.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_1122.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_1122.FStar_TypeChecker_Env.implicits})
in (
# 861 "FStar.TypeChecker.Util.fst"
let strengthen = (fun _57_1126 -> (match (()) with
| () -> begin
(
# 863 "FStar.TypeChecker.Util.fst"
let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (match ((let _136_770 = (FStar_Syntax_Subst.compress f)
in _136_770.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_57_1129, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _57_1135; FStar_Syntax_Syntax.pos = _57_1133; FStar_Syntax_Syntax.vars = _57_1131}, _57_1140) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
(
# 867 "FStar.TypeChecker.Util.fst"
let lc = (
# 867 "FStar.TypeChecker.Util.fst"
let _57_1143 = lc
in {FStar_Syntax_Syntax.eff_name = _57_1143.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _57_1143.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _57_1143.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| _57_1147 -> begin
(
# 871 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 872 "FStar.TypeChecker.Util.fst"
let _57_1149 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _136_774 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _136_773 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _136_772 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _136_771 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _136_774 _136_773 _136_772 _136_771)))))
end else begin
()
end
in (
# 879 "FStar.TypeChecker.Util.fst"
let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 880 "FStar.TypeChecker.Util.fst"
let _57_1154 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_57_1154) with
| (a, kwp) -> begin
(
# 881 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 882 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env ct.FStar_Syntax_Syntax.effect_name)
in (
# 883 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (
# 884 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 885 "FStar.TypeChecker.Util.fst"
let us = (let _136_775 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_136_775)::[])
in (
# 886 "FStar.TypeChecker.Util.fst"
let wp = (let _136_780 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ret)
in (let _136_779 = (let _136_778 = (FStar_Syntax_Syntax.as_arg t)
in (let _136_777 = (let _136_776 = (FStar_Syntax_Syntax.as_arg xexp)
in (_136_776)::[])
in (_136_778)::_136_777))
in (FStar_Syntax_Syntax.mk_Tm_app _136_780 _136_779 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)))
in (
# 887 "FStar.TypeChecker.Util.fst"
let cret = (let _136_781 = (mk_comp md t wp wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _136_781))
in (
# 888 "FStar.TypeChecker.Util.fst"
let guard = if apply_guard then begin
(let _136_783 = (let _136_782 = (FStar_Syntax_Syntax.as_arg xexp)
in (_136_782)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _136_783 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end else begin
f
end
in (
# 889 "FStar.TypeChecker.Util.fst"
let _57_1165 = (let _136_791 = (FStar_All.pipe_left (fun _136_788 -> Some (_136_788)) (FStar_TypeChecker_Errors.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _136_790 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _136_789 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _136_791 _136_790 e cret _136_789))))
in (match (_57_1165) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(
# 893 "FStar.TypeChecker.Util.fst"
let x = (
# 893 "FStar.TypeChecker.Util.fst"
let _57_1166 = x
in {FStar_Syntax_Syntax.ppname = _57_1166.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1166.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (
# 894 "FStar.TypeChecker.Util.fst"
let c = (let _136_793 = (let _136_792 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _136_792))
in (bind env (Some (e)) _136_793 (Some (x), eq_ret)))
in (
# 895 "FStar.TypeChecker.Util.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 896 "FStar.TypeChecker.Util.fst"
let _57_1171 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _136_794 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _136_794))
end else begin
()
end
in c))))
end))))))))))
end)))))
end))
end))
in (
# 899 "FStar.TypeChecker.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _57_3 -> (match (_57_3) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _57_1177 -> begin
[]
end))))
in (
# 900 "FStar.TypeChecker.Util.fst"
let lc = (
# 900 "FStar.TypeChecker.Util.fst"
let _57_1179 = lc
in (let _136_796 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _136_796; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (
# 901 "FStar.TypeChecker.Util.fst"
let g = (
# 901 "FStar.TypeChecker.Util.fst"
let _57_1182 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_1182.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_1182.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_1182.FStar_TypeChecker_Env.implicits})
in (e, lc, g))))))
end)
end)))

# 902 "FStar.TypeChecker.Util.fst"
let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (
# 905 "FStar.TypeChecker.Util.fst"
let mk_post_type = (fun res_t ens -> (
# 906 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _136_808 = (let _136_807 = (let _136_806 = (let _136_805 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _136_805))
in (_136_806)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _136_807 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _136_808))))
in (
# 908 "FStar.TypeChecker.Util.fst"
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
| (req, _57_1210)::(ens, _57_1205)::_57_1202 -> begin
(let _136_814 = (let _136_811 = (norm req)
in Some (_136_811))
in (let _136_813 = (let _136_812 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _136_812))
in (_136_814, _136_813)))
end
| _57_1214 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 922 "FStar.TypeChecker.Util.fst"
let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (wp, _57_1225)::(wlp, _57_1220)::_57_1217 -> begin
(
# 925 "FStar.TypeChecker.Util.fst"
let _57_1231 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (_57_1231) with
| (us_r, _57_1230) -> begin
(
# 926 "FStar.TypeChecker.Util.fst"
let _57_1235 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (_57_1235) with
| (us_e, _57_1234) -> begin
(
# 927 "FStar.TypeChecker.Util.fst"
let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (
# 928 "FStar.TypeChecker.Util.fst"
let as_req = (let _136_816 = (let _136_815 = (FStar_Ident.set_lid_range FStar_Syntax_Const.as_requires r)
in (FStar_Syntax_Syntax.fvar _136_815 FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _136_816 us_r))
in (
# 929 "FStar.TypeChecker.Util.fst"
let as_ens = (let _136_818 = (let _136_817 = (FStar_Ident.set_lid_range FStar_Syntax_Const.as_ensures r)
in (FStar_Syntax_Syntax.fvar _136_817 FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _136_818 us_e))
in (
# 930 "FStar.TypeChecker.Util.fst"
let req = (let _136_821 = (let _136_820 = (let _136_819 = (FStar_Syntax_Syntax.as_arg wp)
in (_136_819)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.imp_tag)))::_136_820)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _136_821 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 931 "FStar.TypeChecker.Util.fst"
let ens = (let _136_824 = (let _136_823 = (let _136_822 = (FStar_Syntax_Syntax.as_arg wlp)
in (_136_822)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.imp_tag)))::_136_823)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _136_824 None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _136_828 = (let _136_825 = (norm req)
in Some (_136_825))
in (let _136_827 = (let _136_826 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm _136_826))
in (_136_828, _136_827))))))))
end))
end))
end
| _57_1242 -> begin
(FStar_All.failwith "Impossible")
end))
end
end)
end)))

# 936 "FStar.TypeChecker.Util.fst"
let maybe_instantiate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (
# 942 "FStar.TypeChecker.Util.fst"
let torig = (FStar_Syntax_Subst.compress t)
in if (not (env.FStar_TypeChecker_Env.instantiate_imp)) then begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end else begin
(match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 947 "FStar.TypeChecker.Util.fst"
let _57_1253 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_1253) with
| (bs, c) -> begin
(
# 948 "FStar.TypeChecker.Util.fst"
let rec aux = (fun subst _57_4 -> (match (_57_4) with
| (x, Some (FStar_Syntax_Syntax.Implicit (dot)))::rest -> begin
(
# 950 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 951 "FStar.TypeChecker.Util.fst"
let _57_1269 = (new_implicit_var env t)
in (match (_57_1269) with
| (v, _57_1267, g) -> begin
(
# 952 "FStar.TypeChecker.Util.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, v)))::subst
in (
# 953 "FStar.TypeChecker.Util.fst"
let _57_1275 = (aux subst rest)
in (match (_57_1275) with
| (args, bs, subst, g') -> begin
(let _136_839 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((v, Some (FStar_Syntax_Syntax.Implicit (dot))))::args, bs, subst, _136_839))
end)))
end)))
end
| bs -> begin
([], bs, subst, FStar_TypeChecker_Rel.trivial_guard)
end))
in (
# 957 "FStar.TypeChecker.Util.fst"
let _57_1281 = (aux [] bs)
in (match (_57_1281) with
| (args, bs, subst, guard) -> begin
(match ((args, bs)) with
| ([], _57_1284) -> begin
(e, torig, guard)
end
| (_57_1287, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end
| _57_1291 -> begin
(
# 968 "FStar.TypeChecker.Util.fst"
let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _57_1294 -> begin
(FStar_Syntax_Util.arrow bs c)
end)
in (
# 971 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.subst subst t)
in (
# 972 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk_Tm_app e args (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (e, t, guard))))
end)
end)))
end))
end
| _57_1299 -> begin
(e, t, FStar_TypeChecker_Rel.trivial_guard)
end)
end))

# 976 "FStar.TypeChecker.Util.fst"
let gen_univs : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe_uvar Prims.list * (FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  Prims.bool))  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(
# 984 "FStar.TypeChecker.Util.fst"
let s = (let _136_851 = (let _136_850 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _136_850))
in (FStar_All.pipe_right _136_851 FStar_Util.set_elements))
in (
# 985 "FStar.TypeChecker.Util.fst"
let r = (let _136_852 = (FStar_TypeChecker_Env.get_range env)
in Some (_136_852))
in (
# 986 "FStar.TypeChecker.Util.fst"
let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (
# 987 "FStar.TypeChecker.Util.fst"
let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (
# 988 "FStar.TypeChecker.Util.fst"
let _57_1306 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _136_857 = (let _136_854 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _136_854))
in (let _136_856 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _136_855 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _136_857 _136_856 _136_855))))
end else begin
()
end
in (
# 990 "FStar.TypeChecker.Util.fst"
let _57_1308 = (FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))))
in u_name))))))
in u_names)))
end)

# 992 "FStar.TypeChecker.Util.fst"
let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t -> (
# 995 "FStar.TypeChecker.Util.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (
# 996 "FStar.TypeChecker.Util.fst"
let univs = (FStar_Syntax_Free.univs t)
in (
# 997 "FStar.TypeChecker.Util.fst"
let _57_1316 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _136_866 = (let _136_865 = (let _136_864 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _136_864 (FStar_List.map (fun u -> (let _136_863 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _136_863 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _136_865 (FStar_String.concat ", ")))
in (FStar_Util.print1 "univs to gen : %s\n" _136_866))
end else begin
()
end
in (
# 1001 "FStar.TypeChecker.Util.fst"
let gen = (gen_univs env univs)
in (
# 1002 "FStar.TypeChecker.Util.fst"
let _57_1319 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _136_867 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _136_867))
end else begin
()
end
in (
# 1004 "FStar.TypeChecker.Util.fst"
let ts = (FStar_Syntax_Subst.close_univ_vars gen t)
in (gen, ts))))))))

# 1005 "FStar.TypeChecker.Util.fst"
let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> if (let _136_873 = (FStar_Util.for_all (fun _57_1327 -> (match (_57_1327) with
| (_57_1325, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _136_873)) then begin
None
end else begin
(
# 1011 "FStar.TypeChecker.Util.fst"
let norm = (fun c -> (
# 1012 "FStar.TypeChecker.Util.fst"
let _57_1330 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _136_876 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _136_876))
end else begin
()
end
in (
# 1014 "FStar.TypeChecker.Util.fst"
let c = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.Eta)::[]) env c)
end else begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env c)
end
in (
# 1017 "FStar.TypeChecker.Util.fst"
let _57_1333 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _136_877 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _136_877))
end else begin
()
end
in c))))
in (
# 1020 "FStar.TypeChecker.Util.fst"
let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (
# 1021 "FStar.TypeChecker.Util.fst"
let gen_uvars = (fun uvs -> (let _136_880 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _136_880 FStar_Util.set_elements)))
in (
# 1022 "FStar.TypeChecker.Util.fst"
let _57_1350 = (let _136_882 = (FStar_All.pipe_right ecs (FStar_List.map (fun _57_1340 -> (match (_57_1340) with
| (e, c) -> begin
(
# 1023 "FStar.TypeChecker.Util.fst"
let t = (FStar_All.pipe_right (FStar_Syntax_Util.comp_result c) FStar_Syntax_Subst.compress)
in (
# 1024 "FStar.TypeChecker.Util.fst"
let c = (norm c)
in (
# 1025 "FStar.TypeChecker.Util.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (
# 1026 "FStar.TypeChecker.Util.fst"
let t = ct.FStar_Syntax_Syntax.result_typ
in (
# 1027 "FStar.TypeChecker.Util.fst"
let univs = (FStar_Syntax_Free.univs t)
in (
# 1028 "FStar.TypeChecker.Util.fst"
let uvt = (FStar_Syntax_Free.uvars t)
in (
# 1029 "FStar.TypeChecker.Util.fst"
let uvs = (gen_uvars uvt)
in (univs, (uvs, e, c)))))))))
end))))
in (FStar_All.pipe_right _136_882 FStar_List.unzip))
in (match (_57_1350) with
| (univs, uvars) -> begin
(
# 1032 "FStar.TypeChecker.Util.fst"
let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (
# 1033 "FStar.TypeChecker.Util.fst"
let gen_univs = (gen_univs env univs)
in (
# 1034 "FStar.TypeChecker.Util.fst"
let _57_1354 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end else begin
()
end
in (
# 1036 "FStar.TypeChecker.Util.fst"
let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _57_1359 -> (match (_57_1359) with
| (uvs, e, c) -> begin
(
# 1037 "FStar.TypeChecker.Util.fst"
let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _57_1362 -> (match (_57_1362) with
| (u, k) -> begin
(match ((FStar_Unionfind.find u)) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(a, Some (FStar_Syntax_Syntax.imp_tag))
end
| FStar_Syntax_Syntax.Fixed (_57_1396) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _57_1399 -> begin
(
# 1043 "FStar.TypeChecker.Util.fst"
let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (
# 1044 "FStar.TypeChecker.Util.fst"
let _57_1403 = (FStar_Syntax_Util.arrow_formals k)
in (match (_57_1403) with
| (bs, kres) -> begin
(
# 1045 "FStar.TypeChecker.Util.fst"
let a = (let _136_888 = (let _136_887 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _136_886 -> Some (_136_886)) _136_887))
in (FStar_Syntax_Syntax.new_bv _136_888 kres))
in (
# 1046 "FStar.TypeChecker.Util.fst"
let t = (let _136_892 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _136_891 = (let _136_890 = (let _136_889 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _136_889))
in Some (_136_890))
in (FStar_Syntax_Util.abs bs _136_892 _136_891)))
in (
# 1047 "FStar.TypeChecker.Util.fst"
let _57_1406 = (FStar_Syntax_Util.set_uvar u t)
in (a, Some (FStar_Syntax_Syntax.imp_tag)))))
end)))
end)
end))))
in (
# 1051 "FStar.TypeChecker.Util.fst"
let _57_1430 = (match (tvars) with
| [] -> begin
(e, c)
end
| _57_1411 -> begin
(
# 1057 "FStar.TypeChecker.Util.fst"
let _57_1414 = (e, c)
in (match (_57_1414) with
| (e0, c0) -> begin
(
# 1058 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.BetaUVars)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::[]) env c)
in (
# 1059 "FStar.TypeChecker.Util.fst"
let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.BetaUVars)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::[]) env e)
in (
# 1061 "FStar.TypeChecker.Util.fst"
let t = (match ((let _136_893 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _136_893.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(
# 1063 "FStar.TypeChecker.Util.fst"
let _57_1423 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (_57_1423) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| _57_1425 -> begin
(FStar_Syntax_Util.arrow tvars c)
end)
in (
# 1068 "FStar.TypeChecker.Util.fst"
let e' = (FStar_Syntax_Util.abs tvars e None)
in (let _136_894 = (FStar_Syntax_Syntax.mk_Total t)
in (e', _136_894))))))
end))
end)
in (match (_57_1430) with
| (e, c) -> begin
(gen_univs, e, c)
end)))
end))))
in Some (ecs)))))
end)))))
end)

# 1071 "FStar.TypeChecker.Util.fst"
let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> (
# 1074 "FStar.TypeChecker.Util.fst"
let _57_1440 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _136_901 = (let _136_900 = (FStar_List.map (fun _57_1439 -> (match (_57_1439) with
| (lb, _57_1436, _57_1438) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _136_900 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _136_901))
end else begin
()
end
in (match ((let _136_903 = (FStar_All.pipe_right lecs (FStar_List.map (fun _57_1446 -> (match (_57_1446) with
| (_57_1443, e, c) -> begin
(e, c)
end))))
in (gen env _136_903))) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun _57_1451 -> (match (_57_1451) with
| (l, t, c) -> begin
(l, [], t, c)
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _57_1459 _57_1463 -> (match ((_57_1459, _57_1463)) with
| ((l, _57_1456, _57_1458), (us, e, c)) -> begin
(
# 1081 "FStar.TypeChecker.Util.fst"
let _57_1464 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _136_909 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _136_908 = (FStar_Syntax_Print.lbname_to_string l)
in (let _136_907 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.print3 "(%s) Generalized %s to %s\n" _136_909 _136_908 _136_907))))
end else begin
()
end
in (l, us, e, c))
end)) lecs ecs)
end)))

# 1086 "FStar.TypeChecker.Util.fst"
let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (
# 1095 "FStar.TypeChecker.Util.fst"
let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (
# 1096 "FStar.TypeChecker.Util.fst"
let check = (fun env t1 t2 -> if env.FStar_TypeChecker_Env.use_eq then begin
(FStar_TypeChecker_Rel.try_teq env t1 t2)
end else begin
(match ((FStar_TypeChecker_Rel.try_subtype env t1 t2)) with
| None -> begin
None
end
| Some (f) -> begin
(let _136_925 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _136_924 -> Some (_136_924)) _136_925))
end)
end)
in (
# 1102 "FStar.TypeChecker.Util.fst"
let is_var = (fun e -> (match ((let _136_928 = (FStar_Syntax_Subst.compress e)
in _136_928.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (_57_1481) -> begin
true
end
| _57_1484 -> begin
false
end))
in (
# 1105 "FStar.TypeChecker.Util.fst"
let decorate = (fun e t -> (
# 1106 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((
# 1108 "FStar.TypeChecker.Util.fst"
let _57_1491 = x
in {FStar_Syntax_Syntax.ppname = _57_1491.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1491.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| _57_1494 -> begin
(
# 1109 "FStar.TypeChecker.Util.fst"
let _57_1495 = e
in (let _136_933 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _57_1495.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _136_933; FStar_Syntax_Syntax.pos = _57_1495.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_1495.FStar_Syntax_Syntax.vars}))
end)))
in (
# 1110 "FStar.TypeChecker.Util.fst"
let env = (
# 1110 "FStar.TypeChecker.Util.fst"
let _57_1497 = env
in (let _136_934 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _57_1497.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1497.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1497.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1497.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1497.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1497.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1497.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1497.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1497.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1497.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1497.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1497.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1497.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1497.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1497.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _136_934; FStar_TypeChecker_Env.is_iface = _57_1497.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1497.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _57_1497.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _57_1497.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1497.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1497.FStar_TypeChecker_Env.use_bv_sorts}))
in (match ((check env t1 t2)) with
| None -> begin
(let _136_938 = (let _136_937 = (let _136_936 = (FStar_TypeChecker_Errors.expected_expression_of_type env t2 e t1)
in (let _136_935 = (FStar_TypeChecker_Env.get_range env)
in (_136_936, _136_935)))
in FStar_Syntax_Syntax.Error (_136_937))
in (Prims.raise _136_938))
end
| Some (g) -> begin
(
# 1114 "FStar.TypeChecker.Util.fst"
let _57_1503 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _136_939 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _136_939))
end else begin
()
end
in (let _136_940 = (decorate e t2)
in (_136_940, g)))
end)))))))

# 1116 "FStar.TypeChecker.Util.fst"
let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (
# 1120 "FStar.TypeChecker.Util.fst"
let discharge = (fun g -> (
# 1121 "FStar.TypeChecker.Util.fst"
let _57_1510 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (
# 1123 "FStar.TypeChecker.Util.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _136_950 = (discharge g)
in (let _136_949 = (lc.FStar_Syntax_Syntax.comp ())
in (_136_950, _136_949)))
end else begin
(
# 1126 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 1127 "FStar.TypeChecker.Util.fst"
let steps = (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.DeltaComp)::[]
in (
# 1128 "FStar.TypeChecker.Util.fst"
let c = (let _136_951 = (FStar_TypeChecker_Normalize.normalize_comp steps env c)
in (FStar_All.pipe_right _136_951 FStar_Syntax_Util.comp_to_comp_typ))
in (
# 1129 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 1130 "FStar.TypeChecker.Util.fst"
let _57_1521 = (destruct_comp c)
in (match (_57_1521) with
| (t, wp, _57_1520) -> begin
(
# 1131 "FStar.TypeChecker.Util.fst"
let vc = (let _136_959 = (let _136_953 = (let _136_952 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_136_952)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _136_953 env md md.FStar_Syntax_Syntax.trivial))
in (let _136_958 = (let _136_956 = (FStar_Syntax_Syntax.as_arg t)
in (let _136_955 = (let _136_954 = (FStar_Syntax_Syntax.as_arg wp)
in (_136_954)::[])
in (_136_956)::_136_955))
in (let _136_957 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk_Tm_app _136_959 _136_958 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _136_957))))
in (
# 1132 "FStar.TypeChecker.Util.fst"
let _57_1523 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _136_960 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _136_960))
end else begin
()
end
in (
# 1134 "FStar.TypeChecker.Util.fst"
let g = (let _136_961 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _136_961))
in (let _136_963 = (discharge g)
in (let _136_962 = (FStar_Syntax_Syntax.mk_Comp c)
in (_136_963, _136_962))))))
end))))))
end)))

# 1135 "FStar.TypeChecker.Util.fst"
let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (
# 1141 "FStar.TypeChecker.Util.fst"
let short_bin_op = (fun f _57_5 -> (match (_57_5) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (fst, _57_1534)::[] -> begin
(f fst)
end
| _57_1538 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (
# 1146 "FStar.TypeChecker.Util.fst"
let op_and_e = (fun e -> (let _136_984 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _136_984 (fun _136_983 -> FStar_TypeChecker_Common.NonTrivial (_136_983)))))
in (
# 1147 "FStar.TypeChecker.Util.fst"
let op_or_e = (fun e -> (let _136_989 = (let _136_987 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _136_987))
in (FStar_All.pipe_right _136_989 (fun _136_988 -> FStar_TypeChecker_Common.NonTrivial (_136_988)))))
in (
# 1148 "FStar.TypeChecker.Util.fst"
let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _136_992 -> FStar_TypeChecker_Common.NonTrivial (_136_992))))
in (
# 1149 "FStar.TypeChecker.Util.fst"
let op_or_t = (fun t -> (let _136_996 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _136_996 (fun _136_995 -> FStar_TypeChecker_Common.NonTrivial (_136_995)))))
in (
# 1150 "FStar.TypeChecker.Util.fst"
let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _136_999 -> FStar_TypeChecker_Common.NonTrivial (_136_999))))
in (
# 1152 "FStar.TypeChecker.Util.fst"
let short_op_ite = (fun _57_6 -> (match (_57_6) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (guard, _57_1553)::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| _then::(guard, _57_1558)::[] -> begin
(let _136_1003 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _136_1003 (fun _136_1002 -> FStar_TypeChecker_Common.NonTrivial (_136_1002))))
end
| _57_1563 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (
# 1157 "FStar.TypeChecker.Util.fst"
let table = ((FStar_Syntax_Const.op_And, (short_bin_op op_and_e)))::((FStar_Syntax_Const.op_Or, (short_bin_op op_or_e)))::((FStar_Syntax_Const.and_lid, (short_bin_op op_and_t)))::((FStar_Syntax_Const.or_lid, (short_bin_op op_or_t)))::((FStar_Syntax_Const.imp_lid, (short_bin_op op_imp_t)))::((FStar_Syntax_Const.ite_lid, short_op_ite))::[]
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(
# 1167 "FStar.TypeChecker.Util.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((FStar_Util.find_map table (fun _57_1571 -> (match (_57_1571) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _136_1036 = (mk seen_args)
in Some (_136_1036))
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
| _57_1576 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))

# 1172 "FStar.TypeChecker.Util.fst"
let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (match ((let _136_1039 = (FStar_Syntax_Util.un_uinst l)
in _136_1039.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| _57_1581 -> begin
false
end))

# 1184 "FStar.TypeChecker.Util.fst"
let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (
# 1196 "FStar.TypeChecker.Util.fst"
let pos = (fun bs -> (match (bs) with
| (hd, _57_1590)::_57_1587 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| _57_1594 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| (_57_1598, Some (FStar_Syntax_Syntax.Implicit (_57_1600)))::_57_1596 -> begin
bs
end
| _57_1606 -> begin
(match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
bs
end
| Some (t) -> begin
(match ((let _136_1046 = (FStar_Syntax_Subst.compress t)
in _136_1046.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', _57_1612) -> begin
(match ((FStar_Util.prefix_until (fun _57_7 -> (match (_57_7) with
| (_57_1617, Some (FStar_Syntax_Syntax.Implicit (_57_1619))) -> begin
false
end
| _57_1624 -> begin
true
end)) bs')) with
| None -> begin
bs
end
| Some ([], _57_1628, _57_1630) -> begin
bs
end
| Some (imps, _57_1635, _57_1637) -> begin
if (FStar_All.pipe_right imps (FStar_Util.for_all (fun _57_1643 -> (match (_57_1643) with
| (x, _57_1642) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end)))) then begin
(
# 1212 "FStar.TypeChecker.Util.fst"
let r = (pos bs)
in (
# 1213 "FStar.TypeChecker.Util.fst"
let imps = (FStar_All.pipe_right imps (FStar_List.map (fun _57_1647 -> (match (_57_1647) with
| (x, i) -> begin
(let _136_1050 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in (_136_1050, i))
end))))
in (FStar_List.append imps bs)))
end else begin
bs
end
end)
end
| _57_1650 -> begin
bs
end)
end)
end)))




