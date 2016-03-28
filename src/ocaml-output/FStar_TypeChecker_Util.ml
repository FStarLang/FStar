
open Prims
# 31 "FStar.TypeChecker.Util.fst"
type lcomp_with_binder =
(FStar_Syntax_Syntax.bv Prims.option * FStar_Syntax_Syntax.lcomp)

# 78 "FStar.TypeChecker.Util.fst"
let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _148_6 = (FStar_TypeChecker_Env.get_range env)
in (let _148_5 = (FStar_TypeChecker_Errors.failed_to_prove_specification errs)
in (FStar_TypeChecker_Errors.report _148_6 _148_5))))

# 85 "FStar.TypeChecker.Util.fst"
let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _148_9 = (FStar_Syntax_Subst.compress t)
in _148_9.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_63_12) -> begin
true
end
| _63_15 -> begin
false
end))

# 89 "FStar.TypeChecker.Util.fst"
let t_binders : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env -> (let _148_13 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right _148_13 (FStar_List.filter (fun _63_20 -> (match (_63_20) with
| (x, _63_19) -> begin
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
in (let _148_18 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Rel.new_uvar _148_18 bs k))))

# 99 "FStar.TypeChecker.Util.fst"
let new_uvar : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env k -> (let _148_23 = (new_uvar_aux env k)
in (Prims.fst _148_23)))

# 101 "FStar.TypeChecker.Util.fst"
let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun _63_1 -> (match (_63_1) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, _63_35); FStar_Syntax_Syntax.tk = _63_32; FStar_Syntax_Syntax.pos = _63_30; FStar_Syntax_Syntax.vars = _63_28} -> begin
uv
end
| _63_40 -> begin
(FStar_All.failwith "Impossible")
end))

# 105 "FStar.TypeChecker.Util.fst"
let new_implicit_var : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.uvar * FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env k -> (match ((FStar_Syntax_Util.destruct k FStar_Syntax_Const.range_of_lid)) with
| Some (_63_48::(tm, _63_45)::[]) -> begin
(
# 108 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))) None tm.FStar_Syntax_Syntax.pos)
in (t, [], FStar_TypeChecker_Rel.trivial_guard))
end
| _63_53 -> begin
(
# 112 "FStar.TypeChecker.Util.fst"
let _63_56 = (new_uvar_aux env k)
in (match (_63_56) with
| (t, u) -> begin
(
# 113 "FStar.TypeChecker.Util.fst"
let g = (
# 113 "FStar.TypeChecker.Util.fst"
let _63_57 = FStar_TypeChecker_Rel.trivial_guard
in (let _148_32 = (let _148_31 = (let _148_30 = (as_uvar u)
in (env, _148_30, t, k, u.FStar_Syntax_Syntax.pos))
in (_148_31)::[])
in {FStar_TypeChecker_Env.guard_f = _63_57.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _63_57.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _63_57.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _148_32}))
in (let _148_35 = (let _148_34 = (let _148_33 = (as_uvar u)
in (_148_33, u.FStar_Syntax_Syntax.pos))
in (_148_34)::[])
in (t, _148_35, g)))
end))
end))

# 116 "FStar.TypeChecker.Util.fst"
let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun r t -> (
# 117 "FStar.TypeChecker.Util.fst"
let uvs = (FStar_Syntax_Free.uvars t)
in if (not ((FStar_Util.set_is_empty uvs))) then begin
(
# 120 "FStar.TypeChecker.Util.fst"
let us = (let _148_42 = (let _148_41 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun _63_66 -> (match (_63_66) with
| (x, _63_65) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) _148_41))
in (FStar_All.pipe_right _148_42 (FStar_String.concat ", ")))
in (
# 122 "FStar.TypeChecker.Util.fst"
let hide_uvar_nums_saved = (FStar_ST.read FStar_Options.hide_uvar_nums)
in (
# 123 "FStar.TypeChecker.Util.fst"
let print_implicits_saved = (FStar_ST.read FStar_Options.print_implicits)
in (
# 124 "FStar.TypeChecker.Util.fst"
let _63_70 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums false)
in (
# 125 "FStar.TypeChecker.Util.fst"
let _63_72 = (FStar_ST.op_Colon_Equals FStar_Options.print_implicits true)
in (
# 126 "FStar.TypeChecker.Util.fst"
let _63_74 = (let _148_44 = (let _148_43 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us _148_43))
in (FStar_TypeChecker_Errors.report r _148_44))
in (
# 129 "FStar.TypeChecker.Util.fst"
let _63_76 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums hide_uvar_nums_saved)
in (FStar_ST.op_Colon_Equals FStar_Options.print_implicits print_implicits_saved))))))))
end else begin
()
end))

# 136 "FStar.TypeChecker.Util.fst"
let force_sort' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' = (fun s -> (match ((FStar_ST.read s.FStar_Syntax_Syntax.tk)) with
| None -> begin
(let _148_49 = (let _148_48 = (FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos)
in (let _148_47 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s" _148_48 _148_47)))
in (FStar_All.failwith _148_49))
end
| Some (tk) -> begin
tk
end))

# 140 "FStar.TypeChecker.Util.fst"
let force_sort = (fun s -> (let _148_51 = (force_sort' s)
in (FStar_Syntax_Syntax.mk _148_51 None s.FStar_Syntax_Syntax.pos)))

# 142 "FStar.TypeChecker.Util.fst"
let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env _63_91 -> (match (_63_91) with
| {FStar_Syntax_Syntax.lbname = _63_90; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _63_86; FStar_Syntax_Syntax.lbdef = e} -> begin
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
let _63_95 = if (univ_vars <> []) then begin
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
let _63_105 = (FStar_Syntax_Util.type_u ())
in (match (_63_105) with
| (k, _63_104) -> begin
(
# 152 "FStar.TypeChecker.Util.fst"
let t = (let _148_60 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right _148_60 Prims.fst))
in ((
# 153 "FStar.TypeChecker.Util.fst"
let _63_107 = a
in {FStar_Syntax_Syntax.ppname = _63_107.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_107.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), false))
end))
end
| _63_110 -> begin
(a, true)
end))
in (
# 156 "FStar.TypeChecker.Util.fst"
let rec aux = (fun vars e -> (
# 157 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, _63_117) -> begin
(aux vars e)
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _63_123) -> begin
(t, true)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _63_129) -> begin
(
# 163 "FStar.TypeChecker.Util.fst"
let _63_148 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _63_135 _63_138 -> (match ((_63_135, _63_138)) with
| ((scope, bs, check), (a, imp)) -> begin
(
# 164 "FStar.TypeChecker.Util.fst"
let _63_141 = (mk_binder scope a)
in (match (_63_141) with
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
in (match (_63_148) with
| (scope, bs, check) -> begin
(
# 171 "FStar.TypeChecker.Util.fst"
let _63_151 = (aux scope body)
in (match (_63_151) with
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
let _63_158 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_68 = (FStar_Range.string_of_range r)
in (let _148_67 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _148_68 _148_67)))
end else begin
()
end
in (FStar_Util.Inl (t), (check_res || check)))))
end))
end))
end
| _63_161 -> begin
(let _148_71 = (let _148_70 = (let _148_69 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _148_69 Prims.fst))
in FStar_Util.Inl (_148_70))
in (_148_71, false))
end)))
in (
# 181 "FStar.TypeChecker.Util.fst"
let _63_164 = (let _148_72 = (t_binders env)
in (aux _148_72 e))
in (match (_63_164) with
| (t, b) -> begin
(
# 182 "FStar.TypeChecker.Util.fst"
let t = (match (t) with
| FStar_Util.Inr (c) -> begin
(let _148_76 = (let _148_75 = (let _148_74 = (let _148_73 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" _148_73))
in (_148_74, rng))
in FStar_Syntax_Syntax.Error (_148_75))
in (Prims.raise _148_76))
end
| FStar_Util.Inl (t) -> begin
t
end)
in ([], t, b))
end))))))
end
| _63_171 -> begin
(
# 191 "FStar.TypeChecker.Util.fst"
let _63_174 = (FStar_Syntax_Subst.open_univ_vars univ_vars t)
in (match (_63_174) with
| (univ_vars, t) -> begin
(univ_vars, t, false)
end))
end)))
end))

# 202 "FStar.TypeChecker.Util.fst"
let pat_as_exps : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term Prims.list * FStar_Syntax_Syntax.pat) = (fun allow_implicits env p -> (
# 207 "FStar.TypeChecker.Util.fst"
let rec pat_as_arg_with_env = (fun allow_wc_dependence env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(
# 216 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) None p.FStar_Syntax_Syntax.p)
in ([], [], [], env, e, p))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _63_187) -> begin
(
# 220 "FStar.TypeChecker.Util.fst"
let _63_193 = (FStar_Syntax_Util.type_u ())
in (match (_63_193) with
| (k, _63_192) -> begin
(
# 221 "FStar.TypeChecker.Util.fst"
let t = (new_uvar env k)
in (
# 222 "FStar.TypeChecker.Util.fst"
let x = (
# 222 "FStar.TypeChecker.Util.fst"
let _63_195 = x
in {FStar_Syntax_Syntax.ppname = _63_195.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_195.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (
# 223 "FStar.TypeChecker.Util.fst"
let _63_200 = (let _148_89 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _148_89 t))
in (match (_63_200) with
| (e, u) -> begin
(
# 224 "FStar.TypeChecker.Util.fst"
let p = (
# 224 "FStar.TypeChecker.Util.fst"
let _63_201 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, e)); FStar_Syntax_Syntax.ty = _63_201.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _63_201.FStar_Syntax_Syntax.p})
in ([], [], [], env, e, p))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 228 "FStar.TypeChecker.Util.fst"
let _63_209 = (FStar_Syntax_Util.type_u ())
in (match (_63_209) with
| (t, _63_208) -> begin
(
# 229 "FStar.TypeChecker.Util.fst"
let x = (
# 229 "FStar.TypeChecker.Util.fst"
let _63_210 = x
in (let _148_90 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _63_210.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_210.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_90}))
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
let _63_220 = (FStar_Syntax_Util.type_u ())
in (match (_63_220) with
| (t, _63_219) -> begin
(
# 236 "FStar.TypeChecker.Util.fst"
let x = (
# 236 "FStar.TypeChecker.Util.fst"
let _63_221 = x
in (let _148_91 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _63_221.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_221.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_91}))
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
let _63_254 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _63_236 _63_239 -> (match ((_63_236, _63_239)) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(
# 243 "FStar.TypeChecker.Util.fst"
let _63_246 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_63_246) with
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
in (match (_63_254) with
| (b, a, w, env, args, pats) -> begin
(
# 247 "FStar.TypeChecker.Util.fst"
let e = (let _148_98 = (let _148_97 = (let _148_96 = (let _148_95 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (let _148_94 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app _148_95 _148_94 None p.FStar_Syntax_Syntax.p)))
in (_148_96, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))
in FStar_Syntax_Syntax.Tm_meta (_148_97))
in (FStar_Syntax_Syntax.mk _148_98 None p.FStar_Syntax_Syntax.p))
in (let _148_101 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _148_100 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _148_99 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in (_148_101, _148_100, _148_99, env, e, (
# 253 "FStar.TypeChecker.Util.fst"
let _63_256 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _63_256.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _63_256.FStar_Syntax_Syntax.p}))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (_63_259) -> begin
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
let pats = (FStar_List.map (fun _63_274 -> (match (_63_274) with
| (p, imp) -> begin
(let _148_113 = (elaborate_pat env p)
in (_148_113, imp))
end)) pats)
in (
# 265 "FStar.TypeChecker.Util.fst"
let _63_279 = (FStar_TypeChecker_Env.lookup_datacon env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_63_279) with
| (_63_277, t) -> begin
(
# 266 "FStar.TypeChecker.Util.fst"
let _63_283 = (FStar_Syntax_Util.arrow_formals t)
in (match (_63_283) with
| (f, _63_282) -> begin
(
# 267 "FStar.TypeChecker.Util.fst"
let rec aux = (fun formals pats -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _63_294::_63_292) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))))
end
| (_63_300::_63_298, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun _63_306 -> (match (_63_306) with
| (t, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(
# 273 "FStar.TypeChecker.Util.fst"
let a = (let _148_120 = (let _148_119 = (FStar_Syntax_Syntax.range_of_bv t)
in Some (_148_119))
in (FStar_Syntax_Syntax.new_bv _148_120 FStar_Syntax_Syntax.tun))
in (
# 274 "FStar.TypeChecker.Util.fst"
let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (let _148_121 = (maybe_dot inaccessible a r)
in (_148_121, true))))
end
| _63_313 -> begin
(let _148_125 = (let _148_124 = (let _148_123 = (let _148_122 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _148_122))
in (_148_123, (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in FStar_Syntax_Syntax.Error (_148_124))
in (Prims.raise _148_125))
end)
end))))
end
| (f::formals', (p, p_imp)::pats') -> begin
(match (f) with
| (_63_324, Some (FStar_Syntax_Syntax.Implicit (_63_326))) when p_imp -> begin
(let _148_126 = (aux formals' pats')
in ((p, true))::_148_126)
end
| (_63_331, Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(
# 286 "FStar.TypeChecker.Util.fst"
let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (
# 287 "FStar.TypeChecker.Util.fst"
let p = (maybe_dot inaccessible a (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
in (let _148_127 = (aux formals' pats)
in ((p, true))::_148_127)))
end
| (_63_339, imp) -> begin
(let _148_130 = (let _148_128 = (FStar_Syntax_Syntax.is_implicit imp)
in (p, _148_128))
in (let _148_129 = (aux formals' pats')
in (_148_130)::_148_129))
end)
end))
in (
# 293 "FStar.TypeChecker.Util.fst"
let _63_342 = p
in (let _148_133 = (let _148_132 = (let _148_131 = (aux f pats)
in (fv, _148_131))
in FStar_Syntax_Syntax.Pat_cons (_148_132))
in {FStar_Syntax_Syntax.v = _148_133; FStar_Syntax_Syntax.ty = _63_342.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _63_342.FStar_Syntax_Syntax.p})))
end))
end)))
end
| _63_345 -> begin
p
end)))
in (
# 297 "FStar.TypeChecker.Util.fst"
let one_pat = (fun allow_wc_dependence env p -> (
# 298 "FStar.TypeChecker.Util.fst"
let p = (elaborate_pat env p)
in (
# 299 "FStar.TypeChecker.Util.fst"
let _63_357 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_63_357) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))) with
| Some (x) -> begin
(let _148_142 = (let _148_141 = (let _148_140 = (FStar_TypeChecker_Errors.nonlinear_pattern_variable x)
in (_148_140, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_148_141))
in (Prims.raise _148_142))
end
| _63_361 -> begin
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
let _63_377 = (one_pat false env q)
in (match (_63_377) with
| (b, a, _63_374, te, q) -> begin
(
# 312 "FStar.TypeChecker.Util.fst"
let _63_392 = (FStar_List.fold_right (fun p _63_382 -> (match (_63_382) with
| (w, args, pats) -> begin
(
# 313 "FStar.TypeChecker.Util.fst"
let _63_388 = (one_pat false env p)
in (match (_63_388) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv FStar_Syntax_Syntax.bv_eq a a'))) then begin
(let _148_152 = (let _148_151 = (let _148_150 = (FStar_TypeChecker_Errors.disjunctive_pattern_vars a a')
in (let _148_149 = (FStar_TypeChecker_Env.get_range env)
in (_148_150, _148_149)))
in FStar_Syntax_Syntax.Error (_148_151))
in (Prims.raise _148_152))
end else begin
(let _148_154 = (let _148_153 = (FStar_Syntax_Syntax.as_arg arg)
in (_148_153)::args)
in ((FStar_List.append w' w), _148_154, (p)::pats))
end
end))
end)) pats ([], [], []))
in (match (_63_392) with
| (w, args, pats) -> begin
(let _148_156 = (let _148_155 = (FStar_Syntax_Syntax.as_arg te)
in (_148_155)::args)
in ((FStar_List.append b w), _148_156, (
# 318 "FStar.TypeChecker.Util.fst"
let _63_393 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((q)::pats); FStar_Syntax_Syntax.ty = _63_393.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _63_393.FStar_Syntax_Syntax.p})))
end))
end))
end
| _63_396 -> begin
(
# 321 "FStar.TypeChecker.Util.fst"
let _63_404 = (one_pat true env p)
in (match (_63_404) with
| (b, _63_399, _63_401, arg, p) -> begin
(let _148_158 = (let _148_157 = (FStar_Syntax_Syntax.as_arg arg)
in (_148_157)::[])
in (b, _148_158, p))
end))
end))
in (
# 324 "FStar.TypeChecker.Util.fst"
let _63_408 = (top_level_pat_as_args env p)
in (match (_63_408) with
| (b, args, p) -> begin
(
# 325 "FStar.TypeChecker.Util.fst"
let exps = (FStar_All.pipe_right args (FStar_List.map Prims.fst))
in (b, exps, p))
end)))))))

# 328 "FStar.TypeChecker.Util.fst"
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
| (_63_422, FStar_Syntax_Syntax.Tm_uinst (e, _63_425)) -> begin
(aux p e)
end
| (FStar_Syntax_Syntax.Pat_constant (_63_430), FStar_Syntax_Syntax.Tm_constant (_63_433)) -> begin
(let _148_173 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v _148_173))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(
# 340 "FStar.TypeChecker.Util.fst"
let _63_441 = if (not ((FStar_Syntax_Syntax.bv_eq x y))) then begin
(let _148_176 = (let _148_175 = (FStar_Syntax_Print.bv_to_string x)
in (let _148_174 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _148_175 _148_174)))
in (FStar_All.failwith _148_176))
end else begin
()
end
in (
# 342 "FStar.TypeChecker.Util.fst"
let _63_443 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _148_178 = (FStar_Syntax_Print.bv_to_string x)
in (let _148_177 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _148_178 _148_177)))
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
let _63_446 = x
in {FStar_Syntax_Syntax.ppname = _63_446.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_446.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x)) s.FStar_Syntax_Syntax.n)))))
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(
# 349 "FStar.TypeChecker.Util.fst"
let _63_454 = if (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation) then begin
(let _148_181 = (let _148_180 = (FStar_Syntax_Print.bv_to_string x)
in (let _148_179 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _148_180 _148_179)))
in (FStar_All.failwith _148_181))
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
let _63_457 = x
in {FStar_Syntax_Syntax.ppname = _63_457.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_457.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x)) s.FStar_Syntax_Syntax.n))))
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _63_462), _63_466) -> begin
(
# 356 "FStar.TypeChecker.Util.fst"
let s = (force_sort e)
in (
# 357 "FStar.TypeChecker.Util.fst"
let x = (
# 357 "FStar.TypeChecker.Util.fst"
let _63_469 = x
in {FStar_Syntax_Syntax.ppname = _63_469.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_469.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
(
# 361 "FStar.TypeChecker.Util.fst"
let _63_479 = if (not ((FStar_Syntax_Syntax.fv_eq fv fv'))) then begin
(let _148_182 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _148_182))
end else begin
()
end
in (let _148_183 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv', []))) _148_183)))
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
(
# 368 "FStar.TypeChecker.Util.fst"
let _63_522 = if (let _148_184 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right _148_184 Prims.op_Negation)) then begin
(let _148_185 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _148_185))
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
(let _148_192 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev matched_pats)))) _148_192))
end
| (arg::args, (argpat, _63_538)::argpats) -> begin
(match ((arg, argpat.FStar_Syntax_Syntax.v)) with
| ((e, Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (_63_548)) -> begin
(
# 377 "FStar.TypeChecker.Util.fst"
let x = (let _148_193 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _148_193))
in (
# 378 "FStar.TypeChecker.Util.fst"
let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((e, imp), _63_557) -> begin
(
# 382 "FStar.TypeChecker.Util.fst"
let pat = (let _148_195 = (aux argpat e)
in (let _148_194 = (FStar_Syntax_Syntax.is_implicit imp)
in (_148_195, _148_194)))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _63_561 -> begin
(let _148_198 = (let _148_197 = (FStar_Syntax_Print.pat_to_string p)
in (let _148_196 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _148_197 _148_196)))
in (FStar_All.failwith _148_198))
end))
in (match_args [] args argpats))))
end
| _63_563 -> begin
(let _148_203 = (let _148_202 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (let _148_201 = (FStar_Syntax_Print.pat_to_string qq)
in (let _148_200 = (let _148_199 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right _148_199 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _148_202 _148_201 _148_200))))
in (FStar_All.failwith _148_203))
end))))
in (match ((p.FStar_Syntax_Syntax.v, exps)) with
| (FStar_Syntax_Syntax.Pat_disj (ps), _63_567) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(
# 395 "FStar.TypeChecker.Util.fst"
let ps = (FStar_List.map2 aux ps exps)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj (ps)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p))
end
| (_63_571, e::[]) -> begin
(aux p e)
end
| _63_576 -> begin
(FStar_All.failwith "Unexpected number of patterns")
end))))

# 403 "FStar.TypeChecker.Util.fst"
let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (
# 404 "FStar.TypeChecker.Util.fst"
let topt = Some (pat.FStar_Syntax_Syntax.ty)
in (
# 405 "FStar.TypeChecker.Util.fst"
let mk = (fun f -> (FStar_Syntax_Syntax.mk f topt pat.FStar_Syntax_Syntax.p))
in (
# 407 "FStar.TypeChecker.Util.fst"
let pat_as_arg = (fun _63_584 -> (match (_63_584) with
| (p, i) -> begin
(
# 408 "FStar.TypeChecker.Util.fst"
let _63_587 = (decorated_pattern_as_term p)
in (match (_63_587) with
| (vars, te) -> begin
(let _148_211 = (let _148_210 = (FStar_Syntax_Syntax.as_implicit i)
in (te, _148_210))
in (vars, _148_211))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_63_589) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _148_212 = (mk (FStar_Syntax_Syntax.Tm_constant (c)))
in ([], _148_212))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(let _148_213 = (mk (FStar_Syntax_Syntax.Tm_name (x)))
in ((x)::[], _148_213))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 422 "FStar.TypeChecker.Util.fst"
let _63_602 = (let _148_214 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _148_214 FStar_List.unzip))
in (match (_63_602) with
| (vars, args) -> begin
(
# 423 "FStar.TypeChecker.Util.fst"
let vars = (FStar_List.flatten vars)
in (let _148_218 = (let _148_217 = (let _148_216 = (let _148_215 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (_148_215, args))
in FStar_Syntax_Syntax.Tm_app (_148_216))
in (mk _148_217))
in (vars, _148_218)))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
([], e)
end)))))

# 433 "FStar.TypeChecker.Util.fst"
let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (
# 434 "FStar.TypeChecker.Util.fst"
let _63_626 = (match (c.FStar_Syntax_Syntax.effect_args) with
| (wp, _63_615)::(wlp, _63_611)::[] -> begin
(wp, wlp)
end
| _63_619 -> begin
(let _148_224 = (let _148_223 = (let _148_222 = (FStar_List.map (fun _63_623 -> (match (_63_623) with
| (x, _63_622) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right _148_222 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str _148_223))
in (FStar_All.failwith _148_224))
end)
in (match (_63_626) with
| (wp, wlp) -> begin
(c.FStar_Syntax_Syntax.result_typ, wp, wlp)
end)))

# 440 "FStar.TypeChecker.Util.fst"
let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (
# 441 "FStar.TypeChecker.Util.fst"
let _63_634 = (destruct_comp c)
in (match (_63_634) with
| (_63_631, wp, wlp) -> begin
(let _148_246 = (let _148_245 = (let _148_241 = (lift c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _148_241))
in (let _148_244 = (let _148_243 = (let _148_242 = (lift c.FStar_Syntax_Syntax.result_typ wlp)
in (FStar_Syntax_Syntax.as_arg _148_242))
in (_148_243)::[])
in (_148_245)::_148_244))
in {FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _148_246; FStar_Syntax_Syntax.flags = []})
end)))

# 447 "FStar.TypeChecker.Util.fst"
let norm_eff_name : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (
# 448 "FStar.TypeChecker.Util.fst"
let cache = (FStar_Util.smap_create 20)
in (fun env l -> (
# 450 "FStar.TypeChecker.Util.fst"
let rec find = (fun l -> (match ((FStar_TypeChecker_Env.lookup_effect_abbrev env FStar_Syntax_Syntax.U_unknown l)) with
| None -> begin
None
end
| Some (_63_642, c) -> begin
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
let _63_656 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))

# 469 "FStar.TypeChecker.Util.fst"
let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (
# 470 "FStar.TypeChecker.Util.fst"
let _63_667 = (let _148_260 = (norm_eff_name env l1)
in (let _148_259 = (norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _148_260 _148_259)))
in (match (_63_667) with
| (m, _63_664, _63_666) -> begin
m
end)))

# 473 "FStar.TypeChecker.Util.fst"
let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> if ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2)) then begin
FStar_Syntax_Const.effect_Tot_lid
end else begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)

# 479 "FStar.TypeChecker.Util.fst"
let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)) = (fun env c1 c2 -> (
# 480 "FStar.TypeChecker.Util.fst"
let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (
# 481 "FStar.TypeChecker.Util.fst"
let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (
# 482 "FStar.TypeChecker.Util.fst"
let _63_679 = (FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (_63_679) with
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
let _63_685 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (_63_685) with
| (a, kwp) -> begin
(let _148_274 = (destruct_comp m1)
in (let _148_273 = (destruct_comp m2)
in ((md, a, kwp), _148_274, _148_273)))
end)))))
end)))))

# 489 "FStar.TypeChecker.Util.fst"
let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (
# 490 "FStar.TypeChecker.Util.fst"
let l = (norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)))

# 493 "FStar.TypeChecker.Util.fst"
let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (
# 494 "FStar.TypeChecker.Util.fst"
let l = (norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid))))

# 498 "FStar.TypeChecker.Util.fst"
let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md result wp wlp flags -> (let _148_297 = (let _148_296 = (let _148_295 = (FStar_Syntax_Syntax.as_arg wp)
in (let _148_294 = (let _148_293 = (FStar_Syntax_Syntax.as_arg wlp)
in (_148_293)::[])
in (_148_295)::_148_294))
in {FStar_Syntax_Syntax.effect_name = md.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = _148_296; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp _148_297)))

# 504 "FStar.TypeChecker.Util.fst"
let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (
# 505 "FStar.TypeChecker.Util.fst"
let _63_699 = lc
in (let _148_304 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _63_699.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _148_304; FStar_Syntax_Syntax.cflags = _63_699.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _63_701 -> (match (()) with
| () -> begin
(let _148_303 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _148_303))
end))})))

# 508 "FStar.TypeChecker.Util.fst"
let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _148_307 = (FStar_Syntax_Subst.compress t)
in _148_307.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_63_704) -> begin
true
end
| _63_707 -> begin
false
end))

# 512 "FStar.TypeChecker.Util.fst"
let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v -> (
# 514 "FStar.TypeChecker.Util.fst"
let c = if (let _148_314 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation _148_314)) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(
# 517 "FStar.TypeChecker.Util.fst"
let m = (let _148_315 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must _148_315))
in (
# 518 "FStar.TypeChecker.Util.fst"
let _63_714 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_63_714) with
| (a, kwp) -> begin
(
# 519 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 520 "FStar.TypeChecker.Util.fst"
let wp = (let _148_323 = (let _148_322 = (let _148_317 = (let _148_316 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_148_316)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _148_317 env m m.FStar_Syntax_Syntax.ret))
in (let _148_321 = (let _148_320 = (FStar_Syntax_Syntax.as_arg t)
in (let _148_319 = (let _148_318 = (FStar_Syntax_Syntax.as_arg v)
in (_148_318)::[])
in (_148_320)::_148_319))
in (FStar_Syntax_Syntax.mk_Tm_app _148_322 _148_321 (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _148_323))
in (
# 521 "FStar.TypeChecker.Util.fst"
let wlp = wp
in (mk_comp m t wp wlp ((FStar_Syntax_Syntax.RETURN)::[])))))
end)))
end
in (
# 523 "FStar.TypeChecker.Util.fst"
let _63_719 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return"))) then begin
(let _148_326 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _148_325 = (FStar_Syntax_Print.term_to_string v)
in (let _148_324 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _148_326 _148_325 _148_324))))
end else begin
()
end
in c)))

# 528 "FStar.TypeChecker.Util.fst"
let bind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun env e1opt lc1 _63_726 -> (match (_63_726) with
| (b, lc2) -> begin
(
# 529 "FStar.TypeChecker.Util.fst"
let _63_734 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(
# 531 "FStar.TypeChecker.Util.fst"
let bstr = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _148_337 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (let _148_336 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _148_335 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" _148_337 _148_336 bstr _148_335)))))
end else begin
()
end
in (
# 537 "FStar.TypeChecker.Util.fst"
let bind_it = (fun _63_737 -> (match (()) with
| () -> begin
(
# 538 "FStar.TypeChecker.Util.fst"
let c1 = (lc1.FStar_Syntax_Syntax.comp ())
in (
# 539 "FStar.TypeChecker.Util.fst"
let c2 = (lc2.FStar_Syntax_Syntax.comp ())
in (
# 540 "FStar.TypeChecker.Util.fst"
let _63_743 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _148_344 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _148_343 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _148_342 = (FStar_Syntax_Print.comp_to_string c1)
in (let _148_341 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (let _148_340 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" _148_344 _148_343 _148_342 _148_341 _148_340))))))
end else begin
()
end
in (
# 549 "FStar.TypeChecker.Util.fst"
let try_simplify = (fun _63_746 -> (match (()) with
| () -> begin
(
# 550 "FStar.TypeChecker.Util.fst"
let aux = (fun _63_748 -> (match (()) with
| () -> begin
if (FStar_Syntax_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some ((c2, "trivial no binder"))
end
| Some (_63_751) -> begin
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
(let _148_352 = (let _148_351 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT ((x, e)))::[]) c2)
in (_148_351, reason))
in Some (_148_352))
end
| _63_761 -> begin
(aux ())
end))
in if ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2)) then begin
(subst_c2 "both total")
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2)) then begin
(let _148_354 = (let _148_353 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in (_148_353, "both gtot"))
in Some (_148_354))
end else begin
(match ((e1opt, b)) with
| (Some (e), Some (x)) -> begin
if ((FStar_Syntax_Util.is_total_comp c1) && (not ((FStar_Syntax_Syntax.is_null_bv x)))) then begin
(subst_c2 "substituted e")
end else begin
(aux ())
end
end
| _63_768 -> begin
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
let _63_786 = (lift_and_destruct env c1 c2)
in (match (_63_786) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(
# 583 "FStar.TypeChecker.Util.fst"
let bs = (match (b) with
| None -> begin
(let _148_355 = (FStar_Syntax_Syntax.null_binder t1)
in (_148_355)::[])
end
| Some (x) -> begin
(let _148_356 = (FStar_Syntax_Syntax.mk_binder x)
in (_148_356)::[])
end)
in (
# 586 "FStar.TypeChecker.Util.fst"
let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp None))
in (
# 587 "FStar.TypeChecker.Util.fst"
let wp_args = (let _148_371 = (FStar_Syntax_Syntax.as_arg t1)
in (let _148_370 = (let _148_369 = (FStar_Syntax_Syntax.as_arg t2)
in (let _148_368 = (let _148_367 = (FStar_Syntax_Syntax.as_arg wp1)
in (let _148_366 = (let _148_365 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _148_364 = (let _148_363 = (let _148_359 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg _148_359))
in (let _148_362 = (let _148_361 = (let _148_360 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _148_360))
in (_148_361)::[])
in (_148_363)::_148_362))
in (_148_365)::_148_364))
in (_148_367)::_148_366))
in (_148_369)::_148_368))
in (_148_371)::_148_370))
in (
# 588 "FStar.TypeChecker.Util.fst"
let wlp_args = (let _148_379 = (FStar_Syntax_Syntax.as_arg t1)
in (let _148_378 = (let _148_377 = (FStar_Syntax_Syntax.as_arg t2)
in (let _148_376 = (let _148_375 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _148_374 = (let _148_373 = (let _148_372 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _148_372))
in (_148_373)::[])
in (_148_375)::_148_374))
in (_148_377)::_148_376))
in (_148_379)::_148_378))
in (
# 589 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t2)))::[]) kwp)
in (
# 590 "FStar.TypeChecker.Util.fst"
let us = (let _148_382 = (env.FStar_TypeChecker_Env.universe_of env t1)
in (let _148_381 = (let _148_380 = (env.FStar_TypeChecker_Env.universe_of env t2)
in (_148_380)::[])
in (_148_382)::_148_381))
in (
# 591 "FStar.TypeChecker.Util.fst"
let wp = (let _148_383 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _148_383 wp_args None t2.FStar_Syntax_Syntax.pos))
in (
# 592 "FStar.TypeChecker.Util.fst"
let wlp = (let _148_384 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wlp)
in (FStar_Syntax_Syntax.mk_Tm_app _148_384 wlp_args None t2.FStar_Syntax_Syntax.pos))
in (
# 593 "FStar.TypeChecker.Util.fst"
let c = (mk_comp md t2 wp wlp [])
in c)))))))))
end))
end)))))
end))
in (let _148_385 = (join_lcomp env lc1 lc2)
in {FStar_Syntax_Syntax.eff_name = _148_385; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it})))
end))

# 600 "FStar.TypeChecker.Util.fst"
let lift_formula : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t mk_wp mk_wlp f -> (
# 601 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 602 "FStar.TypeChecker.Util.fst"
let _63_808 = (FStar_TypeChecker_Env.wp_signature env md_pure.FStar_Syntax_Syntax.mname)
in (match (_63_808) with
| (a, kwp) -> begin
(
# 603 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 604 "FStar.TypeChecker.Util.fst"
let wp = (let _148_399 = (let _148_398 = (FStar_Syntax_Syntax.as_arg t)
in (let _148_397 = (let _148_396 = (FStar_Syntax_Syntax.as_arg f)
in (_148_396)::[])
in (_148_398)::_148_397))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wp _148_399 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (
# 605 "FStar.TypeChecker.Util.fst"
let wlp = (let _148_403 = (let _148_402 = (FStar_Syntax_Syntax.as_arg t)
in (let _148_401 = (let _148_400 = (FStar_Syntax_Syntax.as_arg f)
in (_148_400)::[])
in (_148_402)::_148_401))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wlp _148_403 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (mk_comp md_pure FStar_TypeChecker_Common.t_unit wp wlp []))))
end))))

# 608 "FStar.TypeChecker.Util.fst"
let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((f, FStar_Syntax_Syntax.Meta_labeled ((reason, r, false))))) None f.FStar_Syntax_Syntax.pos))

# 611 "FStar.TypeChecker.Util.fst"
let label_opt : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _148_427 = (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)
in (FStar_All.pipe_left Prims.op_Negation _148_427)) then begin
f
end else begin
(let _148_428 = (reason ())
in (label _148_428 r f))
end
end))

# 618 "FStar.TypeChecker.Util.fst"
let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 620 "FStar.TypeChecker.Util.fst"
let _63_828 = g
in (let _148_436 = (let _148_435 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_148_435))
in {FStar_TypeChecker_Env.guard_f = _148_436; FStar_TypeChecker_Env.deferred = _63_828.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _63_828.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _63_828.FStar_TypeChecker_Env.implicits}))
end))

# 622 "FStar.TypeChecker.Util.fst"
let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(
# 624 "FStar.TypeChecker.Util.fst"
let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| _63_839 -> begin
g2
end))

# 628 "FStar.TypeChecker.Util.fst"
let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (
# 629 "FStar.TypeChecker.Util.fst"
let weaken = (fun _63_844 -> (match (()) with
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
let _63_853 = (destruct_comp c)
in (match (_63_853) with
| (res_t, wp, wlp) -> begin
(
# 638 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 639 "FStar.TypeChecker.Util.fst"
let us = (let _148_449 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_148_449)::[])
in (
# 640 "FStar.TypeChecker.Util.fst"
let wp = (let _148_456 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _148_455 = (let _148_454 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_453 = (let _148_452 = (FStar_Syntax_Syntax.as_arg f)
in (let _148_451 = (let _148_450 = (FStar_Syntax_Syntax.as_arg wp)
in (_148_450)::[])
in (_148_452)::_148_451))
in (_148_454)::_148_453))
in (FStar_Syntax_Syntax.mk_Tm_app _148_456 _148_455 None wp.FStar_Syntax_Syntax.pos)))
in (
# 641 "FStar.TypeChecker.Util.fst"
let wlp = (let _148_463 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _148_462 = (let _148_461 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_460 = (let _148_459 = (FStar_Syntax_Syntax.as_arg f)
in (let _148_458 = (let _148_457 = (FStar_Syntax_Syntax.as_arg wlp)
in (_148_457)::[])
in (_148_459)::_148_458))
in (_148_461)::_148_460))
in (FStar_Syntax_Syntax.mk_Tm_app _148_463 _148_462 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp c.FStar_Syntax_Syntax.flags)))))
end)))
end
end))
end))
in (
# 643 "FStar.TypeChecker.Util.fst"
let _63_858 = lc
in {FStar_Syntax_Syntax.eff_name = _63_858.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _63_858.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _63_858.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))

# 645 "FStar.TypeChecker.Util.fst"
let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> if (FStar_TypeChecker_Rel.is_trivial g0) then begin
(lc, g0)
end else begin
(
# 649 "FStar.TypeChecker.Util.fst"
let _63_865 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _148_483 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _148_482 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _148_483 _148_482)))
end else begin
()
end
in (
# 653 "FStar.TypeChecker.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _63_2 -> (match (_63_2) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _63_871 -> begin
[]
end))))
in (
# 654 "FStar.TypeChecker.Util.fst"
let strengthen = (fun _63_874 -> (match (()) with
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
let xret = (let _148_488 = (let _148_487 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _148_487))
in (FStar_Syntax_Util.comp_set_flags _148_488 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (
# 665 "FStar.TypeChecker.Util.fst"
let lc = (bind env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), (FStar_Syntax_Util.lcomp_of_comp xret)))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (
# 669 "FStar.TypeChecker.Util.fst"
let _63_884 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _148_490 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _148_489 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _148_490 _148_489)))
end else begin
()
end
in (
# 674 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 675 "FStar.TypeChecker.Util.fst"
let _63_890 = (destruct_comp c)
in (match (_63_890) with
| (res_t, wp, wlp) -> begin
(
# 676 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 677 "FStar.TypeChecker.Util.fst"
let us = (let _148_491 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_148_491)::[])
in (
# 678 "FStar.TypeChecker.Util.fst"
let wp = (let _148_500 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assert_p)
in (let _148_499 = (let _148_498 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_497 = (let _148_496 = (let _148_493 = (let _148_492 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason _148_492 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _148_493))
in (let _148_495 = (let _148_494 = (FStar_Syntax_Syntax.as_arg wp)
in (_148_494)::[])
in (_148_496)::_148_495))
in (_148_498)::_148_497))
in (FStar_Syntax_Syntax.mk_Tm_app _148_500 _148_499 None wp.FStar_Syntax_Syntax.pos)))
in (
# 679 "FStar.TypeChecker.Util.fst"
let wlp = (let _148_507 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _148_506 = (let _148_505 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_504 = (let _148_503 = (FStar_Syntax_Syntax.as_arg f)
in (let _148_502 = (let _148_501 = (FStar_Syntax_Syntax.as_arg wlp)
in (_148_501)::[])
in (_148_503)::_148_502))
in (_148_505)::_148_504))
in (FStar_Syntax_Syntax.mk_Tm_app _148_507 _148_506 None wlp.FStar_Syntax_Syntax.pos)))
in (
# 681 "FStar.TypeChecker.Util.fst"
let _63_895 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _148_508 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _148_508))
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
in (let _148_512 = (
# 687 "FStar.TypeChecker.Util.fst"
let _63_898 = lc
in (let _148_511 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _148_510 = if ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _148_509 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _148_509))) then begin
flags
end else begin
[]
end
in {FStar_Syntax_Syntax.eff_name = _148_511; FStar_Syntax_Syntax.res_typ = _63_898.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _148_510; FStar_Syntax_Syntax.comp = strengthen})))
in (_148_512, (
# 690 "FStar.TypeChecker.Util.fst"
let _63_900 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _63_900.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _63_900.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _63_900.FStar_TypeChecker_Env.implicits}))))))
end)

# 692 "FStar.TypeChecker.Util.fst"
let record_application_site : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (
# 693 "FStar.TypeChecker.Util.fst"
let comp = (fun _63_906 -> (match (()) with
| () -> begin
(
# 694 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 695 "FStar.TypeChecker.Util.fst"
let res_t = (FStar_Syntax_Util.comp_result c)
in if (((FStar_Syntax_Util.is_trivial_wp c) || (let _148_521 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals _148_521 FStar_Syntax_Const.prims_lid))) || (FStar_Syntax_Syntax.is_teff res_t)) then begin
c
end else begin
(
# 700 "FStar.TypeChecker.Util.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (FStar_TypeChecker_Common.t_unit)))
in (
# 701 "FStar.TypeChecker.Util.fst"
let _63_914 = (strengthen_precondition (Some ((fun _63_910 -> (match (()) with
| () -> begin
"push"
end)))) env e (FStar_Syntax_Util.lcomp_of_comp c) g)
in (match (_63_914) with
| (c, _63_913) -> begin
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
let us = (let _148_525 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_148_525)::[])
in (
# 706 "FStar.TypeChecker.Util.fst"
let xret = (let _148_530 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _148_529 = (let _148_528 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_527 = (let _148_526 = (FStar_Syntax_Syntax.as_arg xexp)
in (_148_526)::[])
in (_148_528)::_148_527))
in (FStar_Syntax_Syntax.mk_Tm_app _148_530 _148_529 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 707 "FStar.TypeChecker.Util.fst"
let xret_comp = (let _148_531 = (mk_comp md_pure res_t xret xret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_531))
in (
# 708 "FStar.TypeChecker.Util.fst"
let lc = (let _148_537 = (let _148_536 = (let _148_535 = (strengthen_precondition (Some ((fun _63_921 -> (match (()) with
| () -> begin
"pop"
end)))) env xexp xret_comp g)
in (FStar_All.pipe_left Prims.fst _148_535))
in (Some (x), _148_536))
in (bind env None c _148_537))
in (lc.FStar_Syntax_Syntax.comp ()))))))))
end)))
end))
end))
in (
# 710 "FStar.TypeChecker.Util.fst"
let _63_923 = lc
in {FStar_Syntax_Syntax.eff_name = _63_923.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _63_923.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _63_923.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = comp})))

# 712 "FStar.TypeChecker.Util.fst"
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
let _63_933 = (let _148_545 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _148_544 = (FStar_Syntax_Syntax.bv_to_name y)
in (_148_545, _148_544)))
in (match (_63_933) with
| (xexp, yexp) -> begin
(
# 717 "FStar.TypeChecker.Util.fst"
let us = (let _148_546 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_148_546)::[])
in (
# 718 "FStar.TypeChecker.Util.fst"
let yret = (let _148_551 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _148_550 = (let _148_549 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_548 = (let _148_547 = (FStar_Syntax_Syntax.as_arg yexp)
in (_148_547)::[])
in (_148_549)::_148_548))
in (FStar_Syntax_Syntax.mk_Tm_app _148_551 _148_550 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 719 "FStar.TypeChecker.Util.fst"
let x_eq_y_yret = (let _148_559 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _148_558 = (let _148_557 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_556 = (let _148_555 = (let _148_552 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _148_552))
in (let _148_554 = (let _148_553 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_148_553)::[])
in (_148_555)::_148_554))
in (_148_557)::_148_556))
in (FStar_Syntax_Syntax.mk_Tm_app _148_559 _148_558 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 720 "FStar.TypeChecker.Util.fst"
let forall_y_x_eq_y_yret = (let _148_569 = (FStar_TypeChecker_Env.inst_effect_fun_with (FStar_List.append us us) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _148_568 = (let _148_567 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_566 = (let _148_565 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_564 = (let _148_563 = (let _148_562 = (let _148_561 = (let _148_560 = (FStar_Syntax_Syntax.mk_binder y)
in (_148_560)::[])
in (FStar_Syntax_Util.abs _148_561 x_eq_y_yret None))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _148_562))
in (_148_563)::[])
in (_148_565)::_148_564))
in (_148_567)::_148_566))
in (FStar_Syntax_Syntax.mk_Tm_app _148_569 _148_568 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 721 "FStar.TypeChecker.Util.fst"
let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (
# 722 "FStar.TypeChecker.Util.fst"
let lc = (bind env None (FStar_Syntax_Util.lcomp_of_comp comp) (Some (x), (FStar_Syntax_Util.lcomp_of_comp lc2)))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))

# 725 "FStar.TypeChecker.Util.fst"
let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (
# 726 "FStar.TypeChecker.Util.fst"
let comp = (fun _63_945 -> (match (()) with
| () -> begin
(
# 727 "FStar.TypeChecker.Util.fst"
let _63_961 = (let _148_581 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _148_580 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _148_581 _148_580)))
in (match (_63_961) with
| ((md, _63_948, _63_950), (res_t, wp_then, wlp_then), (_63_957, wp_else, wlp_else)) -> begin
(
# 728 "FStar.TypeChecker.Util.fst"
let us = (let _148_582 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_148_582)::[])
in (
# 729 "FStar.TypeChecker.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _148_602 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _148_601 = (let _148_599 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_598 = (let _148_597 = (FStar_Syntax_Syntax.as_arg g)
in (let _148_596 = (let _148_595 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _148_594 = (let _148_593 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_148_593)::[])
in (_148_595)::_148_594))
in (_148_597)::_148_596))
in (_148_599)::_148_598))
in (let _148_600 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _148_602 _148_601 None _148_600)))))
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
let wp = (let _148_609 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _148_608 = (let _148_607 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_606 = (let _148_605 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _148_604 = (let _148_603 = (FStar_Syntax_Syntax.as_arg wp)
in (_148_603)::[])
in (_148_605)::_148_604))
in (_148_607)::_148_606))
in (FStar_Syntax_Syntax.mk_Tm_app _148_609 _148_608 None wp.FStar_Syntax_Syntax.pos)))
in (
# 736 "FStar.TypeChecker.Util.fst"
let wlp = (let _148_614 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _148_613 = (let _148_612 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_611 = (let _148_610 = (FStar_Syntax_Syntax.as_arg wlp)
in (_148_610)::[])
in (_148_612)::_148_611))
in (FStar_Syntax_Syntax.mk_Tm_app _148_614 _148_613 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end))))
end))
end))
in (let _148_615 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _148_615; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp})))

# 743 "FStar.TypeChecker.Util.fst"
let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (let _148_621 = (let _148_620 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid _148_620))
in (FStar_Syntax_Syntax.fvar _148_621 FStar_Syntax_Syntax.Delta_constant None)))

# 745 "FStar.TypeChecker.Util.fst"
let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (
# 746 "FStar.TypeChecker.Util.fst"
let eff = (FStar_List.fold_left (fun eff _63_983 -> (match (_63_983) with
| (_63_981, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (
# 747 "FStar.TypeChecker.Util.fst"
let bind_cases = (fun _63_986 -> (match (()) with
| () -> begin
(
# 748 "FStar.TypeChecker.Util.fst"
let us = (let _148_632 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_148_632)::[])
in (
# 749 "FStar.TypeChecker.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _148_652 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _148_651 = (let _148_649 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_648 = (let _148_647 = (FStar_Syntax_Syntax.as_arg g)
in (let _148_646 = (let _148_645 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _148_644 = (let _148_643 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_148_643)::[])
in (_148_645)::_148_644))
in (_148_647)::_148_646))
in (_148_649)::_148_648))
in (let _148_650 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _148_652 _148_651 None _148_650)))))
in (
# 751 "FStar.TypeChecker.Util.fst"
let default_case = (
# 752 "FStar.TypeChecker.Util.fst"
let post_k = (let _148_655 = (let _148_653 = (FStar_Syntax_Syntax.null_binder res_t)
in (_148_653)::[])
in (let _148_654 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _148_655 _148_654)))
in (
# 753 "FStar.TypeChecker.Util.fst"
let kwp = (let _148_658 = (let _148_656 = (FStar_Syntax_Syntax.null_binder post_k)
in (_148_656)::[])
in (let _148_657 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _148_658 _148_657)))
in (
# 754 "FStar.TypeChecker.Util.fst"
let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (
# 755 "FStar.TypeChecker.Util.fst"
let wp = (let _148_664 = (let _148_659 = (FStar_Syntax_Syntax.mk_binder post)
in (_148_659)::[])
in (let _148_663 = (let _148_662 = (let _148_660 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Errors.exhaustiveness_check _148_660))
in (let _148_661 = (fvar_const env FStar_Syntax_Const.false_lid)
in (FStar_All.pipe_left _148_662 _148_661)))
in (FStar_Syntax_Util.abs _148_664 _148_663 None)))
in (
# 756 "FStar.TypeChecker.Util.fst"
let wlp = (let _148_667 = (let _148_665 = (FStar_Syntax_Syntax.mk_binder post)
in (_148_665)::[])
in (let _148_666 = (fvar_const env FStar_Syntax_Const.true_lid)
in (FStar_Syntax_Util.abs _148_667 _148_666 None)))
in (
# 757 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (
# 759 "FStar.TypeChecker.Util.fst"
let comp = (FStar_List.fold_right (fun _63_1003 celse -> (match (_63_1003) with
| (g, cthen) -> begin
(
# 760 "FStar.TypeChecker.Util.fst"
let _63_1021 = (let _148_670 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _148_670 celse))
in (match (_63_1021) with
| ((md, _63_1007, _63_1009), (_63_1012, wp_then, wlp_then), (_63_1017, wp_else, wlp_else)) -> begin
(let _148_672 = (ifthenelse md res_t g wp_then wp_else)
in (let _148_671 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _148_672 _148_671 [])))
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
let _63_1029 = (destruct_comp comp)
in (match (_63_1029) with
| (_63_1026, wp, wlp) -> begin
(
# 767 "FStar.TypeChecker.Util.fst"
let wp = (let _148_679 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _148_678 = (let _148_677 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_676 = (let _148_675 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _148_674 = (let _148_673 = (FStar_Syntax_Syntax.as_arg wp)
in (_148_673)::[])
in (_148_675)::_148_674))
in (_148_677)::_148_676))
in (FStar_Syntax_Syntax.mk_Tm_app _148_679 _148_678 None wp.FStar_Syntax_Syntax.pos)))
in (
# 768 "FStar.TypeChecker.Util.fst"
let wlp = (let _148_684 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _148_683 = (let _148_682 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_681 = (let _148_680 = (FStar_Syntax_Syntax.as_arg wlp)
in (_148_680)::[])
in (_148_682)::_148_681))
in (FStar_Syntax_Syntax.mk_Tm_app _148_684 _148_683 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end))))
end))))
end))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))

# 775 "FStar.TypeChecker.Util.fst"
let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (
# 776 "FStar.TypeChecker.Util.fst"
let close = (fun _63_1036 -> (match (()) with
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
let bs = (let _148_705 = (FStar_Syntax_Syntax.mk_binder x)
in (_148_705)::[])
in (
# 783 "FStar.TypeChecker.Util.fst"
let us = (let _148_707 = (let _148_706 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (_148_706)::[])
in (u_res)::_148_707)
in (
# 784 "FStar.TypeChecker.Util.fst"
let wp = (FStar_Syntax_Util.abs bs wp None)
in (let _148_714 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (let _148_713 = (let _148_712 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_711 = (let _148_710 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _148_709 = (let _148_708 = (FStar_Syntax_Syntax.as_arg wp)
in (_148_708)::[])
in (_148_710)::_148_709))
in (_148_712)::_148_711))
in (FStar_Syntax_Syntax.mk_Tm_app _148_714 _148_713 None wp0.FStar_Syntax_Syntax.pos))))))) bvs wp0))
in (
# 787 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 788 "FStar.TypeChecker.Util.fst"
let _63_1053 = (destruct_comp c)
in (match (_63_1053) with
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
let _63_1058 = lc
in {FStar_Syntax_Syntax.eff_name = _63_1058.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _63_1058.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _63_1058.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))

# 796 "FStar.TypeChecker.Util.fst"
let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (
# 797 "FStar.TypeChecker.Util.fst"
let refine = (fun _63_1064 -> (match (()) with
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
(let _148_725 = (let _148_724 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _148_723 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _148_724 _148_723)))
in (FStar_All.failwith _148_725))
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
let ret = (let _148_727 = (let _148_726 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _148_726 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_727))
in (
# 812 "FStar.TypeChecker.Util.fst"
let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (
# 813 "FStar.TypeChecker.Util.fst"
let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (
# 815 "FStar.TypeChecker.Util.fst"
let c = (let _148_729 = (let _148_728 = (bind env None (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), eq_ret))
in (_148_728.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _148_729 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
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
let _63_1076 = lc
in {FStar_Syntax_Syntax.eff_name = _63_1076.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _63_1076.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))

# 826 "FStar.TypeChecker.Util.fst"
let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (match ((FStar_TypeChecker_Rel.sub_comp env c c')) with
| None -> begin
(let _148_741 = (let _148_740 = (let _148_739 = (FStar_TypeChecker_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _148_738 = (FStar_TypeChecker_Env.get_range env)
in (_148_739, _148_738)))
in FStar_Syntax_Syntax.Error (_148_740))
in (Prims.raise _148_741))
end
| Some (g) -> begin
(e, c', g)
end))

# 832 "FStar.TypeChecker.Util.fst"
let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match ((let _148_750 = (FStar_Syntax_Subst.compress t)
in _148_750.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_63_1090) -> begin
(match ((let _148_751 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _148_751.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid) -> begin
(
# 837 "FStar.TypeChecker.Util.fst"
let _63_1094 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (
# 838 "FStar.TypeChecker.Util.fst"
let b2t = (let _148_752 = (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar _148_752 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (
# 839 "FStar.TypeChecker.Util.fst"
let lc = (let _148_755 = (let _148_754 = (let _148_753 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_753))
in (None, _148_754))
in (bind env (Some (e)) lc _148_755))
in (
# 840 "FStar.TypeChecker.Util.fst"
let e = (let _148_757 = (let _148_756 = (FStar_Syntax_Syntax.as_arg e)
in (_148_756)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _148_757 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (e, lc)))))
end
| _63_1100 -> begin
(e, lc)
end)
end
| _63_1102 -> begin
(e, lc)
end))

# 847 "FStar.TypeChecker.Util.fst"
let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (
# 848 "FStar.TypeChecker.Util.fst"
let gopt = if env.FStar_TypeChecker_Env.use_eq then begin
(let _148_766 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in (_148_766, false))
end else begin
(let _148_767 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in (_148_767, true))
end
in (match (gopt) with
| (None, _63_1110) -> begin
(FStar_TypeChecker_Rel.subtype_fail env lc.FStar_Syntax_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(match ((FStar_TypeChecker_Rel.guard_form g)) with
| FStar_TypeChecker_Common.Trivial -> begin
(
# 856 "FStar.TypeChecker.Util.fst"
let lc = (
# 856 "FStar.TypeChecker.Util.fst"
let _63_1117 = lc
in {FStar_Syntax_Syntax.eff_name = _63_1117.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _63_1117.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _63_1117.FStar_Syntax_Syntax.comp})
in (e, lc, g))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 860 "FStar.TypeChecker.Util.fst"
let g = (
# 860 "FStar.TypeChecker.Util.fst"
let _63_1122 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _63_1122.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _63_1122.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _63_1122.FStar_TypeChecker_Env.implicits})
in (
# 861 "FStar.TypeChecker.Util.fst"
let strengthen = (fun _63_1126 -> (match (()) with
| () -> begin
(
# 863 "FStar.TypeChecker.Util.fst"
let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (match ((let _148_770 = (FStar_Syntax_Subst.compress f)
in _148_770.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_63_1129, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _63_1135; FStar_Syntax_Syntax.pos = _63_1133; FStar_Syntax_Syntax.vars = _63_1131}, _63_1140) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
(
# 867 "FStar.TypeChecker.Util.fst"
let lc = (
# 867 "FStar.TypeChecker.Util.fst"
let _63_1143 = lc
in {FStar_Syntax_Syntax.eff_name = _63_1143.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _63_1143.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _63_1143.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| _63_1147 -> begin
(
# 871 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 872 "FStar.TypeChecker.Util.fst"
let _63_1149 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _148_774 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _148_773 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _148_772 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _148_771 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _148_774 _148_773 _148_772 _148_771)))))
end else begin
()
end
in (
# 879 "FStar.TypeChecker.Util.fst"
let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 880 "FStar.TypeChecker.Util.fst"
let _63_1154 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_63_1154) with
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
let us = (let _148_775 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_148_775)::[])
in (
# 886 "FStar.TypeChecker.Util.fst"
let wp = (let _148_780 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ret)
in (let _148_779 = (let _148_778 = (FStar_Syntax_Syntax.as_arg t)
in (let _148_777 = (let _148_776 = (FStar_Syntax_Syntax.as_arg xexp)
in (_148_776)::[])
in (_148_778)::_148_777))
in (FStar_Syntax_Syntax.mk_Tm_app _148_780 _148_779 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)))
in (
# 887 "FStar.TypeChecker.Util.fst"
let cret = (let _148_781 = (mk_comp md t wp wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_781))
in (
# 888 "FStar.TypeChecker.Util.fst"
let guard = if apply_guard then begin
(let _148_783 = (let _148_782 = (FStar_Syntax_Syntax.as_arg xexp)
in (_148_782)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _148_783 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end else begin
f
end
in (
# 889 "FStar.TypeChecker.Util.fst"
let _63_1165 = (let _148_791 = (FStar_All.pipe_left (fun _148_788 -> Some (_148_788)) (FStar_TypeChecker_Errors.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _148_790 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _148_789 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _148_791 _148_790 e cret _148_789))))
in (match (_63_1165) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(
# 893 "FStar.TypeChecker.Util.fst"
let x = (
# 893 "FStar.TypeChecker.Util.fst"
let _63_1166 = x
in {FStar_Syntax_Syntax.ppname = _63_1166.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_1166.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (
# 894 "FStar.TypeChecker.Util.fst"
let c = (let _148_793 = (let _148_792 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_792))
in (bind env (Some (e)) _148_793 (Some (x), eq_ret)))
in (
# 895 "FStar.TypeChecker.Util.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 896 "FStar.TypeChecker.Util.fst"
let _63_1171 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _148_794 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _148_794))
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
let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _63_3 -> (match (_63_3) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _63_1177 -> begin
[]
end))))
in (
# 900 "FStar.TypeChecker.Util.fst"
let lc = (
# 900 "FStar.TypeChecker.Util.fst"
let _63_1179 = lc
in (let _148_796 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _148_796; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (
# 901 "FStar.TypeChecker.Util.fst"
let g = (
# 901 "FStar.TypeChecker.Util.fst"
let _63_1182 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _63_1182.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _63_1182.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _63_1182.FStar_TypeChecker_Env.implicits})
in (e, lc, g))))))
end)
end)))

# 904 "FStar.TypeChecker.Util.fst"
let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (
# 905 "FStar.TypeChecker.Util.fst"
let mk_post_type = (fun res_t ens -> (
# 906 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _148_808 = (let _148_807 = (let _148_806 = (let _148_805 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _148_805))
in (_148_806)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _148_807 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _148_808))))
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
| (req, _63_1210)::(ens, _63_1205)::_63_1202 -> begin
(let _148_814 = (let _148_811 = (norm req)
in Some (_148_811))
in (let _148_813 = (let _148_812 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _148_812))
in (_148_814, _148_813)))
end
| _63_1214 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 922 "FStar.TypeChecker.Util.fst"
let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (wp, _63_1225)::(wlp, _63_1220)::_63_1217 -> begin
(
# 925 "FStar.TypeChecker.Util.fst"
let _63_1231 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (_63_1231) with
| (us_r, _63_1230) -> begin
(
# 926 "FStar.TypeChecker.Util.fst"
let _63_1235 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (_63_1235) with
| (us_e, _63_1234) -> begin
(
# 927 "FStar.TypeChecker.Util.fst"
let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (
# 928 "FStar.TypeChecker.Util.fst"
let as_req = (let _148_816 = (let _148_815 = (FStar_Ident.set_lid_range FStar_Syntax_Const.as_requires r)
in (FStar_Syntax_Syntax.fvar _148_815 FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _148_816 us_r))
in (
# 929 "FStar.TypeChecker.Util.fst"
let as_ens = (let _148_818 = (let _148_817 = (FStar_Ident.set_lid_range FStar_Syntax_Const.as_ensures r)
in (FStar_Syntax_Syntax.fvar _148_817 FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _148_818 us_e))
in (
# 930 "FStar.TypeChecker.Util.fst"
let req = (let _148_821 = (let _148_820 = (let _148_819 = (FStar_Syntax_Syntax.as_arg wp)
in (_148_819)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.imp_tag)))::_148_820)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _148_821 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 931 "FStar.TypeChecker.Util.fst"
let ens = (let _148_824 = (let _148_823 = (let _148_822 = (FStar_Syntax_Syntax.as_arg wlp)
in (_148_822)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.imp_tag)))::_148_823)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _148_824 None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _148_828 = (let _148_825 = (norm req)
in Some (_148_825))
in (let _148_827 = (let _148_826 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm _148_826))
in (_148_828, _148_827))))))))
end))
end))
end
| _63_1242 -> begin
(FStar_All.failwith "Impossible")
end))
end
end)
end)))

# 941 "FStar.TypeChecker.Util.fst"
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
let _63_1253 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_63_1253) with
| (bs, c) -> begin
(
# 948 "FStar.TypeChecker.Util.fst"
let rec aux = (fun subst _63_4 -> (match (_63_4) with
| (x, Some (FStar_Syntax_Syntax.Implicit (dot)))::rest -> begin
(
# 950 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 951 "FStar.TypeChecker.Util.fst"
let _63_1269 = (new_implicit_var env t)
in (match (_63_1269) with
| (v, _63_1267, g) -> begin
(
# 952 "FStar.TypeChecker.Util.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, v)))::subst
in (
# 953 "FStar.TypeChecker.Util.fst"
let _63_1275 = (aux subst rest)
in (match (_63_1275) with
| (args, bs, subst, g') -> begin
(let _148_839 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((v, Some (FStar_Syntax_Syntax.Implicit (dot))))::args, bs, subst, _148_839))
end)))
end)))
end
| bs -> begin
([], bs, subst, FStar_TypeChecker_Rel.trivial_guard)
end))
in (
# 957 "FStar.TypeChecker.Util.fst"
let _63_1281 = (aux [] bs)
in (match (_63_1281) with
| (args, bs, subst, guard) -> begin
(match ((args, bs)) with
| ([], _63_1284) -> begin
(e, torig, guard)
end
| (_63_1287, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end
| _63_1291 -> begin
(
# 968 "FStar.TypeChecker.Util.fst"
let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _63_1294 -> begin
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
| _63_1299 -> begin
(e, t, FStar_TypeChecker_Rel.trivial_guard)
end)
end))

# 982 "FStar.TypeChecker.Util.fst"
let gen_univs : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe_uvar Prims.list * (FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  Prims.bool))  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(
# 984 "FStar.TypeChecker.Util.fst"
let s = (let _148_851 = (let _148_850 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _148_850))
in (FStar_All.pipe_right _148_851 FStar_Util.set_elements))
in (
# 985 "FStar.TypeChecker.Util.fst"
let r = (let _148_852 = (FStar_TypeChecker_Env.get_range env)
in Some (_148_852))
in (
# 986 "FStar.TypeChecker.Util.fst"
let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (
# 987 "FStar.TypeChecker.Util.fst"
let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (
# 988 "FStar.TypeChecker.Util.fst"
let _63_1306 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _148_857 = (let _148_854 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _148_854))
in (let _148_856 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _148_855 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _148_857 _148_856 _148_855))))
end else begin
()
end
in (
# 990 "FStar.TypeChecker.Util.fst"
let _63_1308 = (FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))))
in u_name))))))
in u_names)))
end)

# 994 "FStar.TypeChecker.Util.fst"
let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t -> (
# 995 "FStar.TypeChecker.Util.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (
# 996 "FStar.TypeChecker.Util.fst"
let univs = (FStar_Syntax_Free.univs t)
in (
# 997 "FStar.TypeChecker.Util.fst"
let _63_1316 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _148_866 = (let _148_865 = (let _148_864 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _148_864 (FStar_List.map (fun u -> (let _148_863 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _148_863 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _148_865 (FStar_String.concat ", ")))
in (FStar_Util.print1 "univs to gen : %s\n" _148_866))
end else begin
()
end
in (
# 1001 "FStar.TypeChecker.Util.fst"
let gen = (gen_univs env univs)
in (
# 1002 "FStar.TypeChecker.Util.fst"
let _63_1319 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _148_867 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _148_867))
end else begin
()
end
in (
# 1004 "FStar.TypeChecker.Util.fst"
let ts = (FStar_Syntax_Subst.close_univ_vars gen t)
in (gen, ts))))))))

# 1007 "FStar.TypeChecker.Util.fst"
let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> if (let _148_873 = (FStar_Util.for_all (fun _63_1327 -> (match (_63_1327) with
| (_63_1325, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _148_873)) then begin
None
end else begin
(
# 1011 "FStar.TypeChecker.Util.fst"
let norm = (fun c -> (
# 1012 "FStar.TypeChecker.Util.fst"
let _63_1330 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _148_876 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _148_876))
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
let _63_1333 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _148_877 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _148_877))
end else begin
()
end
in c))))
in (
# 1020 "FStar.TypeChecker.Util.fst"
let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (
# 1021 "FStar.TypeChecker.Util.fst"
let gen_uvars = (fun uvs -> (let _148_880 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _148_880 FStar_Util.set_elements)))
in (
# 1022 "FStar.TypeChecker.Util.fst"
let _63_1350 = (let _148_882 = (FStar_All.pipe_right ecs (FStar_List.map (fun _63_1340 -> (match (_63_1340) with
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
in (FStar_All.pipe_right _148_882 FStar_List.unzip))
in (match (_63_1350) with
| (univs, uvars) -> begin
(
# 1032 "FStar.TypeChecker.Util.fst"
let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (
# 1033 "FStar.TypeChecker.Util.fst"
let gen_univs = (gen_univs env univs)
in (
# 1034 "FStar.TypeChecker.Util.fst"
let _63_1354 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end else begin
()
end
in (
# 1036 "FStar.TypeChecker.Util.fst"
let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _63_1359 -> (match (_63_1359) with
| (uvs, e, c) -> begin
(
# 1037 "FStar.TypeChecker.Util.fst"
let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _63_1362 -> (match (_63_1362) with
| (u, k) -> begin
(match ((FStar_Unionfind.find u)) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(a, Some (FStar_Syntax_Syntax.imp_tag))
end
| FStar_Syntax_Syntax.Fixed (_63_1396) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _63_1399 -> begin
(
# 1043 "FStar.TypeChecker.Util.fst"
let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (
# 1044 "FStar.TypeChecker.Util.fst"
let _63_1403 = (FStar_Syntax_Util.arrow_formals k)
in (match (_63_1403) with
| (bs, kres) -> begin
(
# 1045 "FStar.TypeChecker.Util.fst"
let a = (let _148_888 = (let _148_887 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _148_886 -> Some (_148_886)) _148_887))
in (FStar_Syntax_Syntax.new_bv _148_888 kres))
in (
# 1046 "FStar.TypeChecker.Util.fst"
let t = (let _148_892 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _148_891 = (let _148_890 = (let _148_889 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _148_889))
in Some (_148_890))
in (FStar_Syntax_Util.abs bs _148_892 _148_891)))
in (
# 1047 "FStar.TypeChecker.Util.fst"
let _63_1406 = (FStar_Syntax_Util.set_uvar u t)
in (a, Some (FStar_Syntax_Syntax.imp_tag)))))
end)))
end)
end))))
in (
# 1051 "FStar.TypeChecker.Util.fst"
let _63_1430 = (match (tvars) with
| [] -> begin
(e, c)
end
| _63_1411 -> begin
(
# 1057 "FStar.TypeChecker.Util.fst"
let _63_1414 = (e, c)
in (match (_63_1414) with
| (e0, c0) -> begin
(
# 1058 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.BetaUVars)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::[]) env c)
in (
# 1059 "FStar.TypeChecker.Util.fst"
let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.BetaUVars)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::[]) env e)
in (
# 1061 "FStar.TypeChecker.Util.fst"
let t = (match ((let _148_893 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _148_893.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(
# 1063 "FStar.TypeChecker.Util.fst"
let _63_1423 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (_63_1423) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| _63_1425 -> begin
(FStar_Syntax_Util.arrow tvars c)
end)
in (
# 1068 "FStar.TypeChecker.Util.fst"
let e' = (FStar_Syntax_Util.abs tvars e None)
in (let _148_894 = (FStar_Syntax_Syntax.mk_Total t)
in (e', _148_894))))))
end))
end)
in (match (_63_1430) with
| (e, c) -> begin
(gen_univs, e, c)
end)))
end))))
in Some (ecs)))))
end)))))
end)

# 1073 "FStar.TypeChecker.Util.fst"
let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> (
# 1074 "FStar.TypeChecker.Util.fst"
let _63_1440 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_901 = (let _148_900 = (FStar_List.map (fun _63_1439 -> (match (_63_1439) with
| (lb, _63_1436, _63_1438) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _148_900 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _148_901))
end else begin
()
end
in (match ((let _148_903 = (FStar_All.pipe_right lecs (FStar_List.map (fun _63_1446 -> (match (_63_1446) with
| (_63_1443, e, c) -> begin
(e, c)
end))))
in (gen env _148_903))) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun _63_1451 -> (match (_63_1451) with
| (l, t, c) -> begin
(l, [], t, c)
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _63_1459 _63_1463 -> (match ((_63_1459, _63_1463)) with
| ((l, _63_1456, _63_1458), (us, e, c)) -> begin
(
# 1081 "FStar.TypeChecker.Util.fst"
let _63_1464 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _148_909 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _148_908 = (FStar_Syntax_Print.lbname_to_string l)
in (let _148_907 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.print3 "(%s) Generalized %s to %s\n" _148_909 _148_908 _148_907))))
end else begin
()
end
in (l, us, e, c))
end)) lecs ecs)
end)))

# 1094 "FStar.TypeChecker.Util.fst"
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
(let _148_925 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _148_924 -> Some (_148_924)) _148_925))
end)
end)
in (
# 1102 "FStar.TypeChecker.Util.fst"
let is_var = (fun e -> (match ((let _148_928 = (FStar_Syntax_Subst.compress e)
in _148_928.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (_63_1481) -> begin
true
end
| _63_1484 -> begin
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
let _63_1491 = x
in {FStar_Syntax_Syntax.ppname = _63_1491.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_1491.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| _63_1494 -> begin
(
# 1109 "FStar.TypeChecker.Util.fst"
let _63_1495 = e
in (let _148_933 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _63_1495.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _148_933; FStar_Syntax_Syntax.pos = _63_1495.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _63_1495.FStar_Syntax_Syntax.vars}))
end)))
in (
# 1110 "FStar.TypeChecker.Util.fst"
let env = (
# 1110 "FStar.TypeChecker.Util.fst"
let _63_1497 = env
in (let _148_934 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _63_1497.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _63_1497.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _63_1497.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _63_1497.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _63_1497.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _63_1497.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _63_1497.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _63_1497.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _63_1497.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _63_1497.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _63_1497.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _63_1497.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _63_1497.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _63_1497.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _63_1497.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _148_934; FStar_TypeChecker_Env.is_iface = _63_1497.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _63_1497.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _63_1497.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _63_1497.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _63_1497.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _63_1497.FStar_TypeChecker_Env.use_bv_sorts}))
in (match ((check env t1 t2)) with
| None -> begin
(let _148_938 = (let _148_937 = (let _148_936 = (FStar_TypeChecker_Errors.expected_expression_of_type env t2 e t1)
in (let _148_935 = (FStar_TypeChecker_Env.get_range env)
in (_148_936, _148_935)))
in FStar_Syntax_Syntax.Error (_148_937))
in (Prims.raise _148_938))
end
| Some (g) -> begin
(
# 1114 "FStar.TypeChecker.Util.fst"
let _63_1503 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _148_939 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _148_939))
end else begin
()
end
in (let _148_940 = (decorate e t2)
in (_148_940, g)))
end)))))))

# 1119 "FStar.TypeChecker.Util.fst"
let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (
# 1120 "FStar.TypeChecker.Util.fst"
let discharge = (fun g -> (
# 1121 "FStar.TypeChecker.Util.fst"
let _63_1510 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (
# 1123 "FStar.TypeChecker.Util.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _148_950 = (discharge g)
in (let _148_949 = (lc.FStar_Syntax_Syntax.comp ())
in (_148_950, _148_949)))
end else begin
(
# 1126 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 1127 "FStar.TypeChecker.Util.fst"
let steps = (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.DeltaComp)::[]
in (
# 1128 "FStar.TypeChecker.Util.fst"
let c = (let _148_951 = (FStar_TypeChecker_Normalize.normalize_comp steps env c)
in (FStar_All.pipe_right _148_951 FStar_Syntax_Util.comp_to_comp_typ))
in (
# 1129 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 1130 "FStar.TypeChecker.Util.fst"
let _63_1521 = (destruct_comp c)
in (match (_63_1521) with
| (t, wp, _63_1520) -> begin
(
# 1131 "FStar.TypeChecker.Util.fst"
let vc = (let _148_959 = (let _148_953 = (let _148_952 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_148_952)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _148_953 env md md.FStar_Syntax_Syntax.trivial))
in (let _148_958 = (let _148_956 = (FStar_Syntax_Syntax.as_arg t)
in (let _148_955 = (let _148_954 = (FStar_Syntax_Syntax.as_arg wp)
in (_148_954)::[])
in (_148_956)::_148_955))
in (let _148_957 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk_Tm_app _148_959 _148_958 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _148_957))))
in (
# 1132 "FStar.TypeChecker.Util.fst"
let _63_1523 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _148_960 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _148_960))
end else begin
()
end
in (
# 1134 "FStar.TypeChecker.Util.fst"
let g = (let _148_961 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _148_961))
in (let _148_963 = (discharge g)
in (let _148_962 = (FStar_Syntax_Syntax.mk_Comp c)
in (_148_963, _148_962))))))
end))))))
end)))

# 1140 "FStar.TypeChecker.Util.fst"
let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (
# 1141 "FStar.TypeChecker.Util.fst"
let short_bin_op = (fun f _63_5 -> (match (_63_5) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (fst, _63_1534)::[] -> begin
(f fst)
end
| _63_1538 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (
# 1146 "FStar.TypeChecker.Util.fst"
let op_and_e = (fun e -> (let _148_984 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _148_984 (fun _148_983 -> FStar_TypeChecker_Common.NonTrivial (_148_983)))))
in (
# 1147 "FStar.TypeChecker.Util.fst"
let op_or_e = (fun e -> (let _148_989 = (let _148_987 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _148_987))
in (FStar_All.pipe_right _148_989 (fun _148_988 -> FStar_TypeChecker_Common.NonTrivial (_148_988)))))
in (
# 1148 "FStar.TypeChecker.Util.fst"
let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _148_992 -> FStar_TypeChecker_Common.NonTrivial (_148_992))))
in (
# 1149 "FStar.TypeChecker.Util.fst"
let op_or_t = (fun t -> (let _148_996 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _148_996 (fun _148_995 -> FStar_TypeChecker_Common.NonTrivial (_148_995)))))
in (
# 1150 "FStar.TypeChecker.Util.fst"
let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _148_999 -> FStar_TypeChecker_Common.NonTrivial (_148_999))))
in (
# 1152 "FStar.TypeChecker.Util.fst"
let short_op_ite = (fun _63_6 -> (match (_63_6) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (guard, _63_1553)::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| _then::(guard, _63_1558)::[] -> begin
(let _148_1003 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _148_1003 (fun _148_1002 -> FStar_TypeChecker_Common.NonTrivial (_148_1002))))
end
| _63_1563 -> begin
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
in (match ((FStar_Util.find_map table (fun _63_1571 -> (match (_63_1571) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _148_1036 = (mk seen_args)
in Some (_148_1036))
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
| _63_1576 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))

# 1174 "FStar.TypeChecker.Util.fst"
let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (match ((let _148_1039 = (FStar_Syntax_Util.un_uinst l)
in _148_1039.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| _63_1581 -> begin
false
end))

# 1195 "FStar.TypeChecker.Util.fst"
let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (
# 1196 "FStar.TypeChecker.Util.fst"
let pos = (fun bs -> (match (bs) with
| (hd, _63_1590)::_63_1587 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| _63_1594 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| (_63_1598, Some (FStar_Syntax_Syntax.Implicit (_63_1600)))::_63_1596 -> begin
bs
end
| _63_1606 -> begin
(match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
bs
end
| Some (t) -> begin
(match ((let _148_1046 = (FStar_Syntax_Subst.compress t)
in _148_1046.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', _63_1612) -> begin
(match ((FStar_Util.prefix_until (fun _63_7 -> (match (_63_7) with
| (_63_1617, Some (FStar_Syntax_Syntax.Implicit (_63_1619))) -> begin
false
end
| _63_1624 -> begin
true
end)) bs')) with
| None -> begin
bs
end
| Some ([], _63_1628, _63_1630) -> begin
bs
end
| Some (imps, _63_1635, _63_1637) -> begin
if (FStar_All.pipe_right imps (FStar_Util.for_all (fun _63_1643 -> (match (_63_1643) with
| (x, _63_1642) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end)))) then begin
(
# 1212 "FStar.TypeChecker.Util.fst"
let r = (pos bs)
in (
# 1213 "FStar.TypeChecker.Util.fst"
let imps = (FStar_All.pipe_right imps (FStar_List.map (fun _63_1647 -> (match (_63_1647) with
| (x, i) -> begin
(let _148_1050 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in (_148_1050, i))
end))))
in (FStar_List.append imps bs)))
end else begin
bs
end
end)
end
| _63_1650 -> begin
bs
end)
end)
end)))




