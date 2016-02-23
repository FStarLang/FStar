
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
| FStar_Syntax_Syntax.Tm_type (_71_14) -> begin
true
end
| _71_17 -> begin
false
end))

# 88 "FStar.TypeChecker.Util.fst"
let t_binders : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env -> (let _150_13 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right _150_13 (FStar_List.filter (fun _71_22 -> (match (_71_22) with
| (x, _71_21) -> begin
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
let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun _71_1 -> (match (_71_1) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, _71_37); FStar_Syntax_Syntax.tk = _71_34; FStar_Syntax_Syntax.pos = _71_32; FStar_Syntax_Syntax.vars = _71_30} -> begin
uv
end
| _71_42 -> begin
(FStar_All.failwith "Impossible")
end))

# 104 "FStar.TypeChecker.Util.fst"
let new_implicit_var : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.uvar * FStar_Range.range) * FStar_TypeChecker_Env.guard_t) = (fun env k -> (
# 105 "FStar.TypeChecker.Util.fst"
let _71_47 = (new_uvar_aux env k)
in (match (_71_47) with
| (t, u) -> begin
(
# 106 "FStar.TypeChecker.Util.fst"
let g = (
# 106 "FStar.TypeChecker.Util.fst"
let _71_48 = FStar_TypeChecker_Rel.trivial_guard
in (let _150_32 = (let _150_31 = (let _150_30 = (as_uvar u)
in (env, _150_30, t, k, u.FStar_Syntax_Syntax.pos))
in (_150_31)::[])
in {FStar_TypeChecker_Env.guard_f = _71_48.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _71_48.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _71_48.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _150_32}))
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
in (FStar_List.map (fun _71_57 -> (match (_71_57) with
| (x, _71_56) -> begin
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
let _71_61 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums false)
in (
# 118 "FStar.TypeChecker.Util.fst"
let _71_63 = (FStar_ST.op_Colon_Equals FStar_Options.print_implicits true)
in (
# 119 "FStar.TypeChecker.Util.fst"
let _71_65 = (let _150_43 = (let _150_42 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us _150_42))
in (FStar_TypeChecker_Errors.report r _150_43))
in (
# 122 "FStar.TypeChecker.Util.fst"
let _71_67 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums hide_uvar_nums_saved)
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
let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env _71_82 -> (match (_71_82) with
| {FStar_Syntax_Syntax.lbname = _71_81; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _71_77; FStar_Syntax_Syntax.lbdef = e} -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 138 "FStar.TypeChecker.Util.fst"
let _71_84 = if (univ_vars <> []) then begin
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
let _71_94 = (FStar_Syntax_Util.type_u ())
in (match (_71_94) with
| (k, _71_93) -> begin
(
# 143 "FStar.TypeChecker.Util.fst"
let t = (let _150_59 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right _150_59 Prims.fst))
in ((
# 144 "FStar.TypeChecker.Util.fst"
let _71_96 = a
in {FStar_Syntax_Syntax.ppname = _71_96.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _71_96.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), false))
end))
end
| _71_99 -> begin
(a, true)
end))
in (
# 147 "FStar.TypeChecker.Util.fst"
let rec aux = (fun vars e -> (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, _71_105) -> begin
(aux vars e)
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _71_111) -> begin
(t, true)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _71_117) -> begin
(
# 153 "FStar.TypeChecker.Util.fst"
let _71_136 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _71_123 _71_126 -> (match ((_71_123, _71_126)) with
| ((scope, bs, check), (a, imp)) -> begin
(
# 154 "FStar.TypeChecker.Util.fst"
let _71_129 = (mk_binder scope a)
in (match (_71_129) with
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
in (match (_71_136) with
| (scope, bs, check) -> begin
(
# 161 "FStar.TypeChecker.Util.fst"
let _71_139 = (aux scope body)
in (match (_71_139) with
| (res, check_res) -> begin
(
# 162 "FStar.TypeChecker.Util.fst"
let c = (FStar_Syntax_Util.ml_comp res r)
in (
# 163 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Util.arrow bs c)
in (
# 164 "FStar.TypeChecker.Util.fst"
let _71_142 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
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
| _71_145 -> begin
(let _150_69 = (let _150_68 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _150_68 Prims.fst))
in (_150_69, false))
end))
in (
# 169 "FStar.TypeChecker.Util.fst"
let _71_148 = (let _150_70 = (t_binders env)
in (aux _150_70 e))
in (match (_71_148) with
| (t, b) -> begin
([], t, b)
end))))))
end
| _71_150 -> begin
(
# 173 "FStar.TypeChecker.Util.fst"
let _71_153 = (FStar_Syntax_Subst.open_univ_vars univ_vars t)
in (match (_71_153) with
| (univ_vars, t) -> begin
(univ_vars, t, false)
end))
end)
end))

# 179 "FStar.TypeChecker.Util.fst"
let is_implicit : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _71_2 -> (match (_71_2) with
| Some (FStar_Syntax_Syntax.Implicit) -> begin
true
end
| _71_158 -> begin
false
end))

# 180 "FStar.TypeChecker.Util.fst"
let as_imp : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _71_3 -> (match (_71_3) with
| Some (FStar_Syntax_Syntax.Implicit) -> begin
true
end
| _71_163 -> begin
false
end))

# 187 "FStar.TypeChecker.Util.fst"
let pat_as_exps : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term Prims.list * FStar_Syntax_Syntax.pat) = (fun allow_implicits env p -> (
# 192 "FStar.TypeChecker.Util.fst"
let rec pat_as_arg_with_env = (fun allow_wc_dependence env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(
# 201 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) None p.FStar_Syntax_Syntax.p)
in ([], [], [], env, e, p))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _71_176) -> begin
(
# 205 "FStar.TypeChecker.Util.fst"
let _71_182 = (FStar_Syntax_Util.type_u ())
in (match (_71_182) with
| (k, _71_181) -> begin
(
# 206 "FStar.TypeChecker.Util.fst"
let t = (new_uvar env k)
in (
# 207 "FStar.TypeChecker.Util.fst"
let x = (
# 207 "FStar.TypeChecker.Util.fst"
let _71_184 = x
in {FStar_Syntax_Syntax.ppname = _71_184.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _71_184.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (
# 208 "FStar.TypeChecker.Util.fst"
let _71_189 = (let _150_87 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _150_87 t))
in (match (_71_189) with
| (e, u) -> begin
(
# 209 "FStar.TypeChecker.Util.fst"
let p = (
# 209 "FStar.TypeChecker.Util.fst"
let _71_190 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, e)); FStar_Syntax_Syntax.ty = _71_190.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _71_190.FStar_Syntax_Syntax.p})
in ([], [], [], env, e, p))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 213 "FStar.TypeChecker.Util.fst"
let _71_198 = (FStar_Syntax_Util.type_u ())
in (match (_71_198) with
| (t, _71_197) -> begin
(
# 214 "FStar.TypeChecker.Util.fst"
let x = (
# 214 "FStar.TypeChecker.Util.fst"
let _71_199 = x
in (let _150_88 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _71_199.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _71_199.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_88}))
in (
# 215 "FStar.TypeChecker.Util.fst"
let env = if allow_wc_dependence then begin
(FStar_TypeChecker_Env.push_bv env x)
end else begin
env
end
in (
# 216 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in ((x)::[], [], (x)::[], env, e, p))))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 220 "FStar.TypeChecker.Util.fst"
let _71_209 = (FStar_Syntax_Util.type_u ())
in (match (_71_209) with
| (t, _71_208) -> begin
(
# 221 "FStar.TypeChecker.Util.fst"
let x = (
# 221 "FStar.TypeChecker.Util.fst"
let _71_210 = x
in (let _150_89 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _71_210.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _71_210.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_89}))
in (
# 222 "FStar.TypeChecker.Util.fst"
let env = (FStar_TypeChecker_Env.push_bv env x)
in (
# 223 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in ((x)::[], (x)::[], [], env, e, p))))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 227 "FStar.TypeChecker.Util.fst"
let _71_243 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _71_225 _71_228 -> (match ((_71_225, _71_228)) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(
# 228 "FStar.TypeChecker.Util.fst"
let _71_235 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_71_235) with
| (b', a', w', env, te, pat) -> begin
(
# 229 "FStar.TypeChecker.Util.fst"
let arg = if imp then begin
(FStar_Syntax_Syntax.iarg te)
end else begin
(FStar_Syntax_Syntax.as_arg te)
end
in ((b')::b, (a')::a, (w')::w, env, (arg)::args, ((pat, imp))::pats))
end))
end)) ([], [], [], env, [], [])))
in (match (_71_243) with
| (b, a, w, env, args, pats) -> begin
(
# 232 "FStar.TypeChecker.Util.fst"
let e = (let _150_96 = (let _150_95 = (let _150_94 = (let _150_93 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (let _150_92 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app _150_93 _150_92 None p.FStar_Syntax_Syntax.p)))
in (_150_94, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))
in FStar_Syntax_Syntax.Tm_meta (_150_95))
in (FStar_Syntax_Syntax.mk _150_96 None p.FStar_Syntax_Syntax.p))
in (let _150_99 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _150_98 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _150_97 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in (_150_99, _150_98, _150_97, env, e, (
# 238 "FStar.TypeChecker.Util.fst"
let _71_245 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _71_245.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _71_245.FStar_Syntax_Syntax.p}))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (_71_248) -> begin
(FStar_All.failwith "impossible")
end))
in (
# 242 "FStar.TypeChecker.Util.fst"
let rec elaborate_pat = (fun env p -> (
# 243 "FStar.TypeChecker.Util.fst"
let maybe_dot = (fun a r -> if allow_implicits then begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term ((a, FStar_Syntax_Syntax.tun))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end else begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var (a)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end)
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 249 "FStar.TypeChecker.Util.fst"
let pats = (FStar_List.map (fun _71_262 -> (match (_71_262) with
| (p, imp) -> begin
(let _150_109 = (elaborate_pat env p)
in (_150_109, imp))
end)) pats)
in (
# 250 "FStar.TypeChecker.Util.fst"
let _71_267 = (FStar_TypeChecker_Env.lookup_datacon env (Prims.fst fv).FStar_Syntax_Syntax.v)
in (match (_71_267) with
| (_71_265, t) -> begin
(
# 251 "FStar.TypeChecker.Util.fst"
let _71_271 = (FStar_Syntax_Util.arrow_formals t)
in (match (_71_271) with
| (f, _71_270) -> begin
(
# 252 "FStar.TypeChecker.Util.fst"
let rec aux = (fun formals pats -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _71_282::_71_280) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v)))))
end
| (_71_288::_71_286, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun _71_294 -> (match (_71_294) with
| (t, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit) -> begin
(
# 258 "FStar.TypeChecker.Util.fst"
let a = (let _150_116 = (let _150_115 = (FStar_Syntax_Syntax.range_of_bv t)
in Some (_150_115))
in (FStar_Syntax_Syntax.new_bv _150_116 FStar_Syntax_Syntax.tun))
in (
# 259 "FStar.TypeChecker.Util.fst"
let r = (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v)
in (let _150_117 = (maybe_dot a r)
in (_150_117, true))))
end
| _71_300 -> begin
(let _150_121 = (let _150_120 = (let _150_119 = (let _150_118 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _150_118))
in (_150_119, (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v)))
in FStar_Syntax_Syntax.Error (_150_120))
in (Prims.raise _150_121))
end)
end))))
end
| (f::formals', (p, p_imp)::pats') -> begin
(match (f) with
| (_71_311, Some (FStar_Syntax_Syntax.Implicit)) when p_imp -> begin
(let _150_122 = (aux formals' pats')
in ((p, true))::_150_122)
end
| (_71_316, Some (FStar_Syntax_Syntax.Implicit)) -> begin
(
# 271 "FStar.TypeChecker.Util.fst"
let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (
# 272 "FStar.TypeChecker.Util.fst"
let p = (maybe_dot a (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v))
in (let _150_123 = (aux formals' pats)
in ((p, true))::_150_123)))
end
| (_71_323, imp) -> begin
(let _150_124 = (aux formals' pats')
in ((p, (as_imp imp)))::_150_124)
end)
end))
in (
# 278 "FStar.TypeChecker.Util.fst"
let _71_326 = p
in (let _150_127 = (let _150_126 = (let _150_125 = (aux f pats)
in (fv, _150_125))
in FStar_Syntax_Syntax.Pat_cons (_150_126))
in {FStar_Syntax_Syntax.v = _150_127; FStar_Syntax_Syntax.ty = _71_326.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _71_326.FStar_Syntax_Syntax.p})))
end))
end)))
end
| _71_329 -> begin
p
end)))
in (
# 282 "FStar.TypeChecker.Util.fst"
let one_pat = (fun allow_wc_dependence env p -> (
# 283 "FStar.TypeChecker.Util.fst"
let p = (elaborate_pat env p)
in (
# 284 "FStar.TypeChecker.Util.fst"
let _71_341 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_71_341) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))) with
| Some (x) -> begin
(let _150_136 = (let _150_135 = (let _150_134 = (FStar_TypeChecker_Errors.nonlinear_pattern_variable x)
in (_150_134, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_150_135))
in (Prims.raise _150_136))
end
| _71_345 -> begin
(b, a, w, arg, p)
end)
end))))
in (
# 289 "FStar.TypeChecker.Util.fst"
let top_level_pat_as_args = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_disj (q::pats) -> begin
(
# 296 "FStar.TypeChecker.Util.fst"
let _71_361 = (one_pat false env q)
in (match (_71_361) with
| (b, a, _71_358, te, q) -> begin
(
# 297 "FStar.TypeChecker.Util.fst"
let _71_376 = (FStar_List.fold_right (fun p _71_366 -> (match (_71_366) with
| (w, args, pats) -> begin
(
# 298 "FStar.TypeChecker.Util.fst"
let _71_372 = (one_pat false env p)
in (match (_71_372) with
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
in (match (_71_376) with
| (w, args, pats) -> begin
(let _150_150 = (let _150_149 = (FStar_Syntax_Syntax.as_arg te)
in (_150_149)::args)
in ((FStar_List.append b w), _150_150, (
# 303 "FStar.TypeChecker.Util.fst"
let _71_377 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((q)::pats); FStar_Syntax_Syntax.ty = _71_377.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _71_377.FStar_Syntax_Syntax.p})))
end))
end))
end
| _71_380 -> begin
(
# 306 "FStar.TypeChecker.Util.fst"
let _71_388 = (one_pat true env p)
in (match (_71_388) with
| (b, _71_383, _71_385, arg, p) -> begin
(let _150_152 = (let _150_151 = (FStar_Syntax_Syntax.as_arg arg)
in (_150_151)::[])
in (b, _150_152, p))
end))
end))
in (
# 309 "FStar.TypeChecker.Util.fst"
let _71_392 = (top_level_pat_as_args env p)
in (match (_71_392) with
| (b, args, p) -> begin
(
# 310 "FStar.TypeChecker.Util.fst"
let exps = (FStar_All.pipe_right args (FStar_List.map Prims.fst))
in (b, exps, p))
end)))))))

# 313 "FStar.TypeChecker.Util.fst"
let decorate_pattern : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.pat = (fun env p exps -> (
# 314 "FStar.TypeChecker.Util.fst"
let qq = p
in (
# 315 "FStar.TypeChecker.Util.fst"
let rec aux = (fun p e -> (
# 316 "FStar.TypeChecker.Util.fst"
let pkg = (fun q t -> (FStar_Syntax_Syntax.withinfo q t p.FStar_Syntax_Syntax.p))
in (
# 317 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Util.unmeta e)
in (match ((p.FStar_Syntax_Syntax.v, e.FStar_Syntax_Syntax.n)) with
| (_71_406, FStar_Syntax_Syntax.Tm_uinst (e, _71_409)) -> begin
(aux p e)
end
| (FStar_Syntax_Syntax.Pat_constant (_71_414), FStar_Syntax_Syntax.Tm_constant (_71_417)) -> begin
(let _150_167 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v _150_167))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(
# 325 "FStar.TypeChecker.Util.fst"
let _71_425 = if (not ((FStar_Syntax_Syntax.bv_eq x y))) then begin
(let _150_170 = (let _150_169 = (FStar_Syntax_Print.bv_to_string x)
in (let _150_168 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _150_169 _150_168)))
in (FStar_All.failwith _150_170))
end else begin
()
end
in (
# 327 "FStar.TypeChecker.Util.fst"
let _71_427 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _150_172 = (FStar_Syntax_Print.bv_to_string x)
in (let _150_171 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _150_172 _150_171)))
end else begin
()
end
in (
# 329 "FStar.TypeChecker.Util.fst"
let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (
# 330 "FStar.TypeChecker.Util.fst"
let x = (
# 330 "FStar.TypeChecker.Util.fst"
let _71_430 = x
in {FStar_Syntax_Syntax.ppname = _71_430.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _71_430.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x)) s.FStar_Syntax_Syntax.n)))))
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(
# 334 "FStar.TypeChecker.Util.fst"
let _71_438 = if (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation) then begin
(let _150_175 = (let _150_174 = (FStar_Syntax_Print.bv_to_string x)
in (let _150_173 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _150_174 _150_173)))
in (FStar_All.failwith _150_175))
end else begin
()
end
in (
# 336 "FStar.TypeChecker.Util.fst"
let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (
# 337 "FStar.TypeChecker.Util.fst"
let x = (
# 337 "FStar.TypeChecker.Util.fst"
let _71_441 = x
in {FStar_Syntax_Syntax.ppname = _71_441.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _71_441.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x)) s.FStar_Syntax_Syntax.n))))
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _71_446), _71_450) -> begin
(
# 341 "FStar.TypeChecker.Util.fst"
let s = (force_sort e)
in (
# 342 "FStar.TypeChecker.Util.fst"
let x = (
# 342 "FStar.TypeChecker.Util.fst"
let _71_453 = x
in {FStar_Syntax_Syntax.ppname = _71_453.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _71_453.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
(
# 346 "FStar.TypeChecker.Util.fst"
let _71_463 = if (not ((FStar_Syntax_Syntax.fv_eq fv fv'))) then begin
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
# 353 "FStar.TypeChecker.Util.fst"
let _71_506 = if (let _150_178 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right _150_178 Prims.op_Negation)) then begin
(let _150_179 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" (Prims.fst fv).FStar_Syntax_Syntax.v.FStar_Ident.str (Prims.fst fv').FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _150_179))
end else begin
()
end
in (
# 356 "FStar.TypeChecker.Util.fst"
let fv = fv'
in (
# 357 "FStar.TypeChecker.Util.fst"
let rec match_args = (fun matched_pats args argpats -> (match ((args, argpats)) with
| ([], []) -> begin
(let _150_186 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev matched_pats)))) _150_186))
end
| (arg::args, (argpat, _71_522)::argpats) -> begin
(match ((arg, argpat.FStar_Syntax_Syntax.v)) with
| ((e, Some (FStar_Syntax_Syntax.Implicit)), FStar_Syntax_Syntax.Pat_dot_term (_71_531)) -> begin
(
# 362 "FStar.TypeChecker.Util.fst"
let x = (let _150_187 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _150_187))
in (
# 363 "FStar.TypeChecker.Util.fst"
let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((e, imp), _71_540) -> begin
(
# 367 "FStar.TypeChecker.Util.fst"
let pat = (let _150_188 = (aux argpat e)
in (_150_188, (as_imp imp)))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _71_544 -> begin
(let _150_191 = (let _150_190 = (FStar_Syntax_Print.pat_to_string p)
in (let _150_189 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _150_190 _150_189)))
in (FStar_All.failwith _150_191))
end))
in (match_args [] args argpats))))
end
| _71_546 -> begin
(let _150_196 = (let _150_195 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (let _150_194 = (FStar_Syntax_Print.pat_to_string qq)
in (let _150_193 = (let _150_192 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right _150_192 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _150_195 _150_194 _150_193))))
in (FStar_All.failwith _150_196))
end))))
in (match ((p.FStar_Syntax_Syntax.v, exps)) with
| (FStar_Syntax_Syntax.Pat_disj (ps), _71_550) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(
# 380 "FStar.TypeChecker.Util.fst"
let ps = (FStar_List.map2 aux ps exps)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj (ps)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p))
end
| (_71_554, e::[]) -> begin
(aux p e)
end
| _71_559 -> begin
(FStar_All.failwith "Unexpected number of patterns")
end))))

# 388 "FStar.TypeChecker.Util.fst"
let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (
# 389 "FStar.TypeChecker.Util.fst"
let topt = Some (pat.FStar_Syntax_Syntax.ty)
in (
# 390 "FStar.TypeChecker.Util.fst"
let mk = (fun f -> (FStar_Syntax_Syntax.mk f topt pat.FStar_Syntax_Syntax.p))
in (
# 392 "FStar.TypeChecker.Util.fst"
let pat_as_arg = (fun _71_567 -> (match (_71_567) with
| (p, i) -> begin
(
# 393 "FStar.TypeChecker.Util.fst"
let _71_570 = (decorated_pattern_as_term p)
in (match (_71_570) with
| (vars, te) -> begin
(let _150_204 = (let _150_203 = (FStar_Syntax_Syntax.as_implicit i)
in (te, _150_203))
in (vars, _150_204))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_71_572) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _150_205 = (mk (FStar_Syntax_Syntax.Tm_constant (c)))
in ([], _150_205))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(let _150_206 = (mk (FStar_Syntax_Syntax.Tm_name (x)))
in ((x)::[], _150_206))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 407 "FStar.TypeChecker.Util.fst"
let _71_585 = (let _150_207 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _150_207 FStar_List.unzip))
in (match (_71_585) with
| (vars, args) -> begin
(
# 408 "FStar.TypeChecker.Util.fst"
let vars = (FStar_List.flatten vars)
in (let _150_211 = (let _150_210 = (let _150_209 = (let _150_208 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (_150_208, args))
in FStar_Syntax_Syntax.Tm_app (_150_209))
in (mk _150_210))
in (vars, _150_211)))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
([], e)
end)))))

# 418 "FStar.TypeChecker.Util.fst"
let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (
# 419 "FStar.TypeChecker.Util.fst"
let _71_609 = (match (c.FStar_Syntax_Syntax.effect_args) with
| (wp, _71_598)::(wlp, _71_594)::[] -> begin
(wp, wlp)
end
| _71_602 -> begin
(let _150_217 = (let _150_216 = (let _150_215 = (FStar_List.map (fun _71_606 -> (match (_71_606) with
| (x, _71_605) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right _150_215 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str _150_216))
in (FStar_All.failwith _150_217))
end)
in (match (_71_609) with
| (wp, wlp) -> begin
(c.FStar_Syntax_Syntax.result_typ, wp, wlp)
end)))

# 425 "FStar.TypeChecker.Util.fst"
let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (
# 426 "FStar.TypeChecker.Util.fst"
let _71_617 = (destruct_comp c)
in (match (_71_617) with
| (_71_614, wp, wlp) -> begin
(let _150_239 = (let _150_238 = (let _150_234 = (lift c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _150_234))
in (let _150_237 = (let _150_236 = (let _150_235 = (lift c.FStar_Syntax_Syntax.result_typ wlp)
in (FStar_Syntax_Syntax.as_arg _150_235))
in (_150_236)::[])
in (_150_238)::_150_237))
in {FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _150_239; FStar_Syntax_Syntax.flags = []})
end)))

# 432 "FStar.TypeChecker.Util.fst"
let norm_eff_name : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (
# 433 "FStar.TypeChecker.Util.fst"
let cache = (FStar_Util.smap_create 20)
in (fun env l -> (
# 435 "FStar.TypeChecker.Util.fst"
let rec find = (fun l -> (match ((FStar_TypeChecker_Env.lookup_effect_abbrev env FStar_Syntax_Syntax.U_unknown l)) with
| None -> begin
None
end
| Some (_71_625, c) -> begin
(
# 439 "FStar.TypeChecker.Util.fst"
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
# 443 "FStar.TypeChecker.Util.fst"
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
# 448 "FStar.TypeChecker.Util.fst"
let _71_639 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))

# 454 "FStar.TypeChecker.Util.fst"
let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (
# 455 "FStar.TypeChecker.Util.fst"
let _71_650 = (let _150_253 = (norm_eff_name env l1)
in (let _150_252 = (norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _150_253 _150_252)))
in (match (_71_650) with
| (m, _71_647, _71_649) -> begin
m
end)))

# 458 "FStar.TypeChecker.Util.fst"
let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> if ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2)) then begin
FStar_Syntax_Const.effect_Tot_lid
end else begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)

# 464 "FStar.TypeChecker.Util.fst"
let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)) = (fun env c1 c2 -> (
# 465 "FStar.TypeChecker.Util.fst"
let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (
# 466 "FStar.TypeChecker.Util.fst"
let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (
# 467 "FStar.TypeChecker.Util.fst"
let _71_662 = (FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (_71_662) with
| (m, lift1, lift2) -> begin
(
# 468 "FStar.TypeChecker.Util.fst"
let m1 = (lift_comp c1 m lift1)
in (
# 469 "FStar.TypeChecker.Util.fst"
let m2 = (lift_comp c2 m lift2)
in (
# 470 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (
# 471 "FStar.TypeChecker.Util.fst"
let _71_668 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (_71_668) with
| (a, kwp) -> begin
(let _150_267 = (destruct_comp m1)
in (let _150_266 = (destruct_comp m2)
in ((md, a, kwp), _150_267, _150_266)))
end)))))
end)))))

# 474 "FStar.TypeChecker.Util.fst"
let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (
# 475 "FStar.TypeChecker.Util.fst"
let l = (norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)))

# 478 "FStar.TypeChecker.Util.fst"
let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (
# 479 "FStar.TypeChecker.Util.fst"
let l = (norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid))))

# 483 "FStar.TypeChecker.Util.fst"
let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md result wp wlp flags -> (let _150_290 = (let _150_289 = (let _150_288 = (FStar_Syntax_Syntax.as_arg wp)
in (let _150_287 = (let _150_286 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_286)::[])
in (_150_288)::_150_287))
in {FStar_Syntax_Syntax.effect_name = md.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = _150_289; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp _150_290)))

# 489 "FStar.TypeChecker.Util.fst"
let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (
# 490 "FStar.TypeChecker.Util.fst"
let _71_682 = lc
in (let _150_297 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _71_682.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _150_297; FStar_Syntax_Syntax.cflags = _71_682.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _71_684 -> (match (()) with
| () -> begin
(let _150_296 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _150_296))
end))})))

# 493 "FStar.TypeChecker.Util.fst"
let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _150_300 = (FStar_Syntax_Subst.compress t)
in _150_300.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_71_687) -> begin
true
end
| _71_690 -> begin
false
end))

# 497 "FStar.TypeChecker.Util.fst"
let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v -> (
# 499 "FStar.TypeChecker.Util.fst"
let c = if (let _150_307 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation _150_307)) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(
# 502 "FStar.TypeChecker.Util.fst"
let m = (let _150_308 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must _150_308))
in (
# 503 "FStar.TypeChecker.Util.fst"
let _71_697 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_71_697) with
| (a, kwp) -> begin
(
# 504 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 505 "FStar.TypeChecker.Util.fst"
let wp = (let _150_316 = (let _150_315 = (let _150_310 = (let _150_309 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_150_309)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _150_310 env m m.FStar_Syntax_Syntax.ret))
in (let _150_314 = (let _150_313 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_312 = (let _150_311 = (FStar_Syntax_Syntax.as_arg v)
in (_150_311)::[])
in (_150_313)::_150_312))
in (FStar_Syntax_Syntax.mk_Tm_app _150_315 _150_314 (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _150_316))
in (
# 506 "FStar.TypeChecker.Util.fst"
let wlp = wp
in (mk_comp m t wp wlp ((FStar_Syntax_Syntax.RETURN)::[])))))
end)))
end
in (
# 508 "FStar.TypeChecker.Util.fst"
let _71_702 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return"))) then begin
(let _150_319 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _150_318 = (FStar_Syntax_Print.term_to_string v)
in (let _150_317 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _150_319 _150_318 _150_317))))
end else begin
()
end
in c)))

# 513 "FStar.TypeChecker.Util.fst"
let bind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun env e1opt lc1 _71_709 -> (match (_71_709) with
| (b, lc2) -> begin
(
# 514 "FStar.TypeChecker.Util.fst"
let _71_717 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(
# 516 "FStar.TypeChecker.Util.fst"
let bstr = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _150_330 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (let _150_329 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _150_328 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" _150_330 _150_329 bstr _150_328)))))
end else begin
()
end
in (
# 522 "FStar.TypeChecker.Util.fst"
let bind_it = (fun _71_720 -> (match (()) with
| () -> begin
(
# 523 "FStar.TypeChecker.Util.fst"
let c1 = (lc1.FStar_Syntax_Syntax.comp ())
in (
# 524 "FStar.TypeChecker.Util.fst"
let c2 = (lc2.FStar_Syntax_Syntax.comp ())
in (
# 525 "FStar.TypeChecker.Util.fst"
let _71_726 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_337 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _150_336 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _150_335 = (FStar_Syntax_Print.comp_to_string c1)
in (let _150_334 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (let _150_333 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" _150_337 _150_336 _150_335 _150_334 _150_333))))))
end else begin
()
end
in (
# 534 "FStar.TypeChecker.Util.fst"
let try_simplify = (fun _71_729 -> (match (()) with
| () -> begin
(
# 535 "FStar.TypeChecker.Util.fst"
let aux = (fun _71_731 -> (match (()) with
| () -> begin
if (FStar_Syntax_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some ((c2, "trivial no binder"))
end
| Some (_71_734) -> begin
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
(let _150_343 = (let _150_342 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in (_150_342, "both gtot"))
in Some (_150_343))
end else begin
(match ((e1opt, b)) with
| (Some (e), Some (x)) -> begin
if ((FStar_Syntax_Util.is_total_comp c1) && (not ((FStar_Syntax_Syntax.is_null_bv x)))) then begin
(let _150_345 = (let _150_344 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT ((x, e)))::[]) c2)
in (_150_344, "substituted e"))
in Some (_150_345))
end else begin
(aux ())
end
end
| _71_742 -> begin
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
# 562 "FStar.TypeChecker.Util.fst"
let _71_760 = (lift_and_destruct env c1 c2)
in (match (_71_760) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(
# 563 "FStar.TypeChecker.Util.fst"
let bs = (match (b) with
| None -> begin
(let _150_346 = (FStar_Syntax_Syntax.null_binder t1)
in (_150_346)::[])
end
| Some (x) -> begin
(let _150_347 = (FStar_Syntax_Syntax.mk_binder x)
in (_150_347)::[])
end)
in (
# 566 "FStar.TypeChecker.Util.fst"
let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp None))
in (
# 567 "FStar.TypeChecker.Util.fst"
let wp_args = (let _150_362 = (FStar_Syntax_Syntax.as_arg t1)
in (let _150_361 = (let _150_360 = (FStar_Syntax_Syntax.as_arg t2)
in (let _150_359 = (let _150_358 = (FStar_Syntax_Syntax.as_arg wp1)
in (let _150_357 = (let _150_356 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _150_355 = (let _150_354 = (let _150_350 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg _150_350))
in (let _150_353 = (let _150_352 = (let _150_351 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _150_351))
in (_150_352)::[])
in (_150_354)::_150_353))
in (_150_356)::_150_355))
in (_150_358)::_150_357))
in (_150_360)::_150_359))
in (_150_362)::_150_361))
in (
# 568 "FStar.TypeChecker.Util.fst"
let wlp_args = (let _150_370 = (FStar_Syntax_Syntax.as_arg t1)
in (let _150_369 = (let _150_368 = (FStar_Syntax_Syntax.as_arg t2)
in (let _150_367 = (let _150_366 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _150_365 = (let _150_364 = (let _150_363 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _150_363))
in (_150_364)::[])
in (_150_366)::_150_365))
in (_150_368)::_150_367))
in (_150_370)::_150_369))
in (
# 569 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t2)))::[]) kwp)
in (
# 570 "FStar.TypeChecker.Util.fst"
let us = (let _150_373 = (env.FStar_TypeChecker_Env.universe_of env t1)
in (let _150_372 = (let _150_371 = (env.FStar_TypeChecker_Env.universe_of env t2)
in (_150_371)::[])
in (_150_373)::_150_372))
in (
# 571 "FStar.TypeChecker.Util.fst"
let wp = (let _150_374 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _150_374 wp_args None t2.FStar_Syntax_Syntax.pos))
in (
# 572 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_375 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wlp)
in (FStar_Syntax_Syntax.mk_Tm_app _150_375 wlp_args None t2.FStar_Syntax_Syntax.pos))
in (
# 573 "FStar.TypeChecker.Util.fst"
let c = (mk_comp md t2 wp wlp [])
in c)))))))))
end))
end)))))
end))
in (let _150_376 = (join_lcomp env lc1 lc2)
in {FStar_Syntax_Syntax.eff_name = _150_376; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it})))
end))

# 580 "FStar.TypeChecker.Util.fst"
let lift_formula : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t mk_wp mk_wlp f -> (
# 581 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 582 "FStar.TypeChecker.Util.fst"
let _71_782 = (FStar_TypeChecker_Env.wp_signature env md_pure.FStar_Syntax_Syntax.mname)
in (match (_71_782) with
| (a, kwp) -> begin
(
# 583 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 584 "FStar.TypeChecker.Util.fst"
let wp = (let _150_390 = (let _150_389 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_388 = (let _150_387 = (FStar_Syntax_Syntax.as_arg f)
in (_150_387)::[])
in (_150_389)::_150_388))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wp _150_390 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (
# 585 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_394 = (let _150_393 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_392 = (let _150_391 = (FStar_Syntax_Syntax.as_arg f)
in (_150_391)::[])
in (_150_393)::_150_392))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wlp _150_394 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (mk_comp md_pure FStar_TypeChecker_Recheck.t_unit wp wlp []))))
end))))

# 588 "FStar.TypeChecker.Util.fst"
let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((f, FStar_Syntax_Syntax.Meta_labeled ((reason, r, false))))) None f.FStar_Syntax_Syntax.pos))

# 591 "FStar.TypeChecker.Util.fst"
let label_opt : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _150_418 = (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)
in (FStar_All.pipe_left Prims.op_Negation _150_418)) then begin
f
end else begin
(let _150_419 = (reason ())
in (label _150_419 r f))
end
end))

# 598 "FStar.TypeChecker.Util.fst"
let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 600 "FStar.TypeChecker.Util.fst"
let _71_802 = g
in (let _150_427 = (let _150_426 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_150_426))
in {FStar_TypeChecker_Env.guard_f = _150_427; FStar_TypeChecker_Env.deferred = _71_802.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _71_802.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _71_802.FStar_TypeChecker_Env.implicits}))
end))

# 602 "FStar.TypeChecker.Util.fst"
let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(
# 604 "FStar.TypeChecker.Util.fst"
let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| _71_813 -> begin
g2
end))

# 608 "FStar.TypeChecker.Util.fst"
let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (
# 609 "FStar.TypeChecker.Util.fst"
let weaken = (fun _71_818 -> (match (()) with
| () -> begin
(
# 610 "FStar.TypeChecker.Util.fst"
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
# 616 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 617 "FStar.TypeChecker.Util.fst"
let _71_827 = (destruct_comp c)
in (match (_71_827) with
| (res_t, wp, wlp) -> begin
(
# 618 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 619 "FStar.TypeChecker.Util.fst"
let us = (let _150_440 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_440)::[])
in (
# 620 "FStar.TypeChecker.Util.fst"
let wp = (let _150_447 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _150_446 = (let _150_445 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_444 = (let _150_443 = (FStar_Syntax_Syntax.as_arg f)
in (let _150_442 = (let _150_441 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_441)::[])
in (_150_443)::_150_442))
in (_150_445)::_150_444))
in (FStar_Syntax_Syntax.mk_Tm_app _150_447 _150_446 None wp.FStar_Syntax_Syntax.pos)))
in (
# 621 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_454 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _150_453 = (let _150_452 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_451 = (let _150_450 = (FStar_Syntax_Syntax.as_arg f)
in (let _150_449 = (let _150_448 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_448)::[])
in (_150_450)::_150_449))
in (_150_452)::_150_451))
in (FStar_Syntax_Syntax.mk_Tm_app _150_454 _150_453 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp c.FStar_Syntax_Syntax.flags)))))
end)))
end
end))
end))
in (
# 623 "FStar.TypeChecker.Util.fst"
let _71_832 = lc
in {FStar_Syntax_Syntax.eff_name = _71_832.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _71_832.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _71_832.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))

# 625 "FStar.TypeChecker.Util.fst"
let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> if (FStar_TypeChecker_Rel.is_trivial g0) then begin
(lc, g0)
end else begin
(
# 629 "FStar.TypeChecker.Util.fst"
let _71_839 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_474 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _150_473 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _150_474 _150_473)))
end else begin
()
end
in (
# 633 "FStar.TypeChecker.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _71_4 -> (match (_71_4) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _71_845 -> begin
[]
end))))
in (
# 634 "FStar.TypeChecker.Util.fst"
let strengthen = (fun _71_848 -> (match (()) with
| () -> begin
(
# 635 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 636 "FStar.TypeChecker.Util.fst"
let g0 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (match ((FStar_TypeChecker_Rel.guard_form g0)) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 640 "FStar.TypeChecker.Util.fst"
let c = if (true || (((FStar_Syntax_Util.is_pure_or_ghost_comp c) && (not ((is_function (FStar_Syntax_Util.comp_result c))))) && (not ((FStar_Syntax_Util.is_partial_return c))))) then begin
(
# 645 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.gen_bv "strengthen_pre_x" None (FStar_Syntax_Util.comp_result c))
in (
# 646 "FStar.TypeChecker.Util.fst"
let xret = (let _150_479 = (let _150_478 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _150_478))
in (FStar_Syntax_Util.comp_set_flags _150_479 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (
# 647 "FStar.TypeChecker.Util.fst"
let lc = (bind env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), (FStar_Syntax_Util.lcomp_of_comp xret)))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (
# 651 "FStar.TypeChecker.Util.fst"
let _71_858 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_481 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _150_480 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _150_481 _150_480)))
end else begin
()
end
in (
# 656 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 657 "FStar.TypeChecker.Util.fst"
let _71_864 = (destruct_comp c)
in (match (_71_864) with
| (res_t, wp, wlp) -> begin
(
# 658 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 659 "FStar.TypeChecker.Util.fst"
let us = (let _150_482 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_482)::[])
in (
# 660 "FStar.TypeChecker.Util.fst"
let wp = (let _150_491 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assert_p)
in (let _150_490 = (let _150_489 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_488 = (let _150_487 = (let _150_484 = (let _150_483 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason _150_483 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _150_484))
in (let _150_486 = (let _150_485 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_485)::[])
in (_150_487)::_150_486))
in (_150_489)::_150_488))
in (FStar_Syntax_Syntax.mk_Tm_app _150_491 _150_490 None wp.FStar_Syntax_Syntax.pos)))
in (
# 661 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_498 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _150_497 = (let _150_496 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_495 = (let _150_494 = (FStar_Syntax_Syntax.as_arg f)
in (let _150_493 = (let _150_492 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_492)::[])
in (_150_494)::_150_493))
in (_150_496)::_150_495))
in (FStar_Syntax_Syntax.mk_Tm_app _150_498 _150_497 None wlp.FStar_Syntax_Syntax.pos)))
in (
# 663 "FStar.TypeChecker.Util.fst"
let _71_869 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_499 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _150_499))
end else begin
()
end
in (
# 667 "FStar.TypeChecker.Util.fst"
let c2 = (mk_comp md res_t wp wlp flags)
in c2))))))
end)))))
end)))
end))
in (let _150_503 = (
# 669 "FStar.TypeChecker.Util.fst"
let _71_872 = lc
in (let _150_502 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _150_501 = if ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _150_500 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _150_500))) then begin
flags
end else begin
[]
end
in {FStar_Syntax_Syntax.eff_name = _150_502; FStar_Syntax_Syntax.res_typ = _71_872.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _150_501; FStar_Syntax_Syntax.comp = strengthen})))
in (_150_503, (
# 672 "FStar.TypeChecker.Util.fst"
let _71_874 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _71_874.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _71_874.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _71_874.FStar_TypeChecker_Env.implicits}))))))
end)

# 674 "FStar.TypeChecker.Util.fst"
let record_application_site : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (
# 675 "FStar.TypeChecker.Util.fst"
let comp = (fun _71_880 -> (match (()) with
| () -> begin
(
# 676 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 677 "FStar.TypeChecker.Util.fst"
let res_t = (FStar_Syntax_Util.comp_result c)
in if (((FStar_Syntax_Util.is_trivial_wp c) || (let _150_512 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals _150_512 FStar_Syntax_Const.prims_lid))) || (FStar_Syntax_Syntax.is_teff res_t)) then begin
c
end else begin
(
# 682 "FStar.TypeChecker.Util.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (FStar_TypeChecker_Recheck.t_unit)))
in (
# 683 "FStar.TypeChecker.Util.fst"
let _71_888 = (strengthen_precondition (Some ((fun _71_884 -> (match (()) with
| () -> begin
"push"
end)))) env e (FStar_Syntax_Util.lcomp_of_comp c) g)
in (match (_71_888) with
| (c, _71_887) -> begin
(
# 684 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 685 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 686 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 687 "FStar.TypeChecker.Util.fst"
let us = (let _150_516 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_516)::[])
in (
# 688 "FStar.TypeChecker.Util.fst"
let xret = (let _150_521 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _150_520 = (let _150_519 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_518 = (let _150_517 = (FStar_Syntax_Syntax.as_arg xexp)
in (_150_517)::[])
in (_150_519)::_150_518))
in (FStar_Syntax_Syntax.mk_Tm_app _150_521 _150_520 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 689 "FStar.TypeChecker.Util.fst"
let xret_comp = (let _150_522 = (mk_comp md_pure res_t xret xret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_522))
in (
# 690 "FStar.TypeChecker.Util.fst"
let lc = (let _150_528 = (let _150_527 = (let _150_526 = (strengthen_precondition (Some ((fun _71_895 -> (match (()) with
| () -> begin
"pop"
end)))) env xexp xret_comp g)
in (FStar_All.pipe_left Prims.fst _150_526))
in (Some (x), _150_527))
in (bind env None c _150_528))
in (lc.FStar_Syntax_Syntax.comp ()))))))))
end)))
end))
end))
in (
# 692 "FStar.TypeChecker.Util.fst"
let _71_897 = lc
in {FStar_Syntax_Syntax.eff_name = _71_897.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _71_897.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _71_897.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = comp})))

# 694 "FStar.TypeChecker.Util.fst"
let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env comp res_t -> (
# 695 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 696 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 697 "FStar.TypeChecker.Util.fst"
let y = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 698 "FStar.TypeChecker.Util.fst"
let _71_907 = (let _150_536 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _150_535 = (FStar_Syntax_Syntax.bv_to_name y)
in (_150_536, _150_535)))
in (match (_71_907) with
| (xexp, yexp) -> begin
(
# 699 "FStar.TypeChecker.Util.fst"
let us = (let _150_537 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_537)::[])
in (
# 700 "FStar.TypeChecker.Util.fst"
let yret = (let _150_542 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _150_541 = (let _150_540 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_539 = (let _150_538 = (FStar_Syntax_Syntax.as_arg yexp)
in (_150_538)::[])
in (_150_540)::_150_539))
in (FStar_Syntax_Syntax.mk_Tm_app _150_542 _150_541 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 701 "FStar.TypeChecker.Util.fst"
let x_eq_y_yret = (let _150_550 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _150_549 = (let _150_548 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_547 = (let _150_546 = (let _150_543 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _150_543))
in (let _150_545 = (let _150_544 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_150_544)::[])
in (_150_546)::_150_545))
in (_150_548)::_150_547))
in (FStar_Syntax_Syntax.mk_Tm_app _150_550 _150_549 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 702 "FStar.TypeChecker.Util.fst"
let forall_y_x_eq_y_yret = (let _150_560 = (FStar_TypeChecker_Env.inst_effect_fun_with (FStar_List.append us us) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _150_559 = (let _150_558 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_557 = (let _150_556 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_555 = (let _150_554 = (let _150_553 = (let _150_552 = (let _150_551 = (FStar_Syntax_Syntax.mk_binder y)
in (_150_551)::[])
in (FStar_Syntax_Util.abs _150_552 x_eq_y_yret None))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _150_553))
in (_150_554)::[])
in (_150_556)::_150_555))
in (_150_558)::_150_557))
in (FStar_Syntax_Syntax.mk_Tm_app _150_560 _150_559 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 703 "FStar.TypeChecker.Util.fst"
let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (
# 704 "FStar.TypeChecker.Util.fst"
let lc = (bind env None (FStar_Syntax_Util.lcomp_of_comp comp) (Some (x), (FStar_Syntax_Util.lcomp_of_comp lc2)))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))

# 707 "FStar.TypeChecker.Util.fst"
let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (
# 708 "FStar.TypeChecker.Util.fst"
let comp = (fun _71_919 -> (match (()) with
| () -> begin
(
# 709 "FStar.TypeChecker.Util.fst"
let _71_935 = (let _150_572 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _150_571 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _150_572 _150_571)))
in (match (_71_935) with
| ((md, _71_922, _71_924), (res_t, wp_then, wlp_then), (_71_931, wp_else, wlp_else)) -> begin
(
# 710 "FStar.TypeChecker.Util.fst"
let us = (let _150_573 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_573)::[])
in (
# 711 "FStar.TypeChecker.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _150_593 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _150_592 = (let _150_590 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_589 = (let _150_588 = (FStar_Syntax_Syntax.as_arg g)
in (let _150_587 = (let _150_586 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _150_585 = (let _150_584 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_150_584)::[])
in (_150_586)::_150_585))
in (_150_588)::_150_587))
in (_150_590)::_150_589))
in (let _150_591 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _150_593 _150_592 None _150_591)))))
in (
# 712 "FStar.TypeChecker.Util.fst"
let wp = (ifthenelse md res_t guard wp_then wp_else)
in (
# 713 "FStar.TypeChecker.Util.fst"
let wlp = (ifthenelse md res_t guard wlp_then wlp_else)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(
# 715 "FStar.TypeChecker.Util.fst"
let comp = (mk_comp md res_t wp wlp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(
# 717 "FStar.TypeChecker.Util.fst"
let wp = (let _150_600 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _150_599 = (let _150_598 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_597 = (let _150_596 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _150_595 = (let _150_594 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_594)::[])
in (_150_596)::_150_595))
in (_150_598)::_150_597))
in (FStar_Syntax_Syntax.mk_Tm_app _150_600 _150_599 None wp.FStar_Syntax_Syntax.pos)))
in (
# 718 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_605 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _150_604 = (let _150_603 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_602 = (let _150_601 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_601)::[])
in (_150_603)::_150_602))
in (FStar_Syntax_Syntax.mk_Tm_app _150_605 _150_604 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end))))
end))
end))
in (let _150_606 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _150_606; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp})))

# 725 "FStar.TypeChecker.Util.fst"
let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (
# 726 "FStar.TypeChecker.Util.fst"
let eff = (FStar_List.fold_left (fun eff _71_955 -> (match (_71_955) with
| (_71_953, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (
# 727 "FStar.TypeChecker.Util.fst"
let bind_cases = (fun _71_958 -> (match (()) with
| () -> begin
(
# 728 "FStar.TypeChecker.Util.fst"
let us = (let _150_617 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_617)::[])
in (
# 729 "FStar.TypeChecker.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _150_637 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _150_636 = (let _150_634 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_633 = (let _150_632 = (FStar_Syntax_Syntax.as_arg g)
in (let _150_631 = (let _150_630 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _150_629 = (let _150_628 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_150_628)::[])
in (_150_630)::_150_629))
in (_150_632)::_150_631))
in (_150_634)::_150_633))
in (let _150_635 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _150_637 _150_636 None _150_635)))))
in (
# 731 "FStar.TypeChecker.Util.fst"
let default_case = (
# 732 "FStar.TypeChecker.Util.fst"
let post_k = (let _150_640 = (let _150_638 = (FStar_Syntax_Syntax.null_binder res_t)
in (_150_638)::[])
in (let _150_639 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _150_640 _150_639)))
in (
# 733 "FStar.TypeChecker.Util.fst"
let kwp = (let _150_643 = (let _150_641 = (FStar_Syntax_Syntax.null_binder post_k)
in (_150_641)::[])
in (let _150_642 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _150_643 _150_642)))
in (
# 734 "FStar.TypeChecker.Util.fst"
let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (
# 735 "FStar.TypeChecker.Util.fst"
let wp = (let _150_650 = (let _150_644 = (FStar_Syntax_Syntax.mk_binder post)
in (_150_644)::[])
in (let _150_649 = (let _150_648 = (let _150_645 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Errors.exhaustiveness_check _150_645))
in (let _150_647 = (let _150_646 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.false_lid _150_646))
in (FStar_All.pipe_left _150_648 _150_647)))
in (FStar_Syntax_Util.abs _150_650 _150_649 None)))
in (
# 736 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_654 = (let _150_651 = (FStar_Syntax_Syntax.mk_binder post)
in (_150_651)::[])
in (let _150_653 = (let _150_652 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid _150_652))
in (FStar_Syntax_Util.abs _150_654 _150_653 None)))
in (
# 737 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (
# 739 "FStar.TypeChecker.Util.fst"
let comp = (FStar_List.fold_right (fun _71_975 celse -> (match (_71_975) with
| (g, cthen) -> begin
(
# 740 "FStar.TypeChecker.Util.fst"
let _71_993 = (let _150_657 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _150_657 celse))
in (match (_71_993) with
| ((md, _71_979, _71_981), (_71_984, wp_then, wlp_then), (_71_989, wp_else, wlp_else)) -> begin
(let _150_659 = (ifthenelse md res_t g wp_then wp_else)
in (let _150_658 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _150_659 _150_658 [])))
end))
end)) lcases default_case)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(add_equality_to_post_condition env comp res_t)
end else begin
(
# 744 "FStar.TypeChecker.Util.fst"
let comp = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (
# 745 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env comp.FStar_Syntax_Syntax.effect_name)
in (
# 746 "FStar.TypeChecker.Util.fst"
let _71_1001 = (destruct_comp comp)
in (match (_71_1001) with
| (_71_998, wp, wlp) -> begin
(
# 747 "FStar.TypeChecker.Util.fst"
let wp = (let _150_666 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _150_665 = (let _150_664 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_663 = (let _150_662 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _150_661 = (let _150_660 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_660)::[])
in (_150_662)::_150_661))
in (_150_664)::_150_663))
in (FStar_Syntax_Syntax.mk_Tm_app _150_666 _150_665 None wp.FStar_Syntax_Syntax.pos)))
in (
# 748 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_671 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _150_670 = (let _150_669 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_668 = (let _150_667 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_667)::[])
in (_150_669)::_150_668))
in (FStar_Syntax_Syntax.mk_Tm_app _150_671 _150_670 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end))))
end))))
end))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))

# 755 "FStar.TypeChecker.Util.fst"
let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (
# 756 "FStar.TypeChecker.Util.fst"
let close = (fun _71_1008 -> (match (()) with
| () -> begin
(
# 757 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in if (FStar_Syntax_Util.is_ml_comp c) then begin
c
end else begin
(
# 760 "FStar.TypeChecker.Util.fst"
let close_wp = (fun u_res md res_t bvs wp0 -> (FStar_List.fold_right (fun x wp -> (
# 762 "FStar.TypeChecker.Util.fst"
let bs = (let _150_692 = (FStar_Syntax_Syntax.mk_binder x)
in (_150_692)::[])
in (
# 763 "FStar.TypeChecker.Util.fst"
let us = (let _150_694 = (let _150_693 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (_150_693)::[])
in (u_res)::_150_694)
in (
# 764 "FStar.TypeChecker.Util.fst"
let wp = (FStar_Syntax_Util.abs bs wp None)
in (let _150_701 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (let _150_700 = (let _150_699 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_698 = (let _150_697 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _150_696 = (let _150_695 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_695)::[])
in (_150_697)::_150_696))
in (_150_699)::_150_698))
in (FStar_Syntax_Syntax.mk_Tm_app _150_701 _150_700 None wp0.FStar_Syntax_Syntax.pos))))))) bvs wp0))
in (
# 767 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 768 "FStar.TypeChecker.Util.fst"
let _71_1025 = (destruct_comp c)
in (match (_71_1025) with
| (t, wp, wlp) -> begin
(
# 769 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 770 "FStar.TypeChecker.Util.fst"
let u_res = (env.FStar_TypeChecker_Env.universe_of env c.FStar_Syntax_Syntax.result_typ)
in (
# 771 "FStar.TypeChecker.Util.fst"
let wp = (close_wp u_res md c.FStar_Syntax_Syntax.result_typ bvs wp)
in (
# 772 "FStar.TypeChecker.Util.fst"
let wlp = (close_wp u_res md c.FStar_Syntax_Syntax.result_typ bvs wlp)
in (mk_comp md c.FStar_Syntax_Syntax.result_typ wp wlp c.FStar_Syntax_Syntax.flags)))))
end))))
end)
end))
in (
# 774 "FStar.TypeChecker.Util.fst"
let _71_1030 = lc
in {FStar_Syntax_Syntax.eff_name = _71_1030.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _71_1030.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _71_1030.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))

# 776 "FStar.TypeChecker.Util.fst"
let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (
# 777 "FStar.TypeChecker.Util.fst"
let refine = (fun _71_1036 -> (match (()) with
| () -> begin
(
# 778 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in if (not ((is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name))) then begin
c
end else begin
if (FStar_Syntax_Util.is_partial_return c) then begin
c
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c) && (not ((FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)))) then begin
(let _150_712 = (let _150_711 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _150_710 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _150_711 _150_710)))
in (FStar_All.failwith _150_712))
end else begin
(
# 786 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 787 "FStar.TypeChecker.Util.fst"
let t = c.FStar_Syntax_Syntax.result_typ
in (
# 788 "FStar.TypeChecker.Util.fst"
let c = (FStar_Syntax_Syntax.mk_Comp c)
in (
# 789 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (
# 790 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 791 "FStar.TypeChecker.Util.fst"
let ret = (let _150_714 = (let _150_713 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _150_713 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_714))
in (
# 792 "FStar.TypeChecker.Util.fst"
let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (
# 793 "FStar.TypeChecker.Util.fst"
let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (
# 795 "FStar.TypeChecker.Util.fst"
let c = (let _150_716 = (let _150_715 = (bind env None (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), eq_ret))
in (_150_715.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _150_716 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
in c)))))))))
end
end
end)
end))
in (
# 798 "FStar.TypeChecker.Util.fst"
let flags = if (((not ((FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)) && (not ((FStar_Syntax_Util.is_lcomp_partial_return lc)))) then begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_Syntax_Syntax.cflags
end else begin
lc.FStar_Syntax_Syntax.cflags
end
in (
# 804 "FStar.TypeChecker.Util.fst"
let _71_1048 = lc
in {FStar_Syntax_Syntax.eff_name = _71_1048.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _71_1048.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))

# 806 "FStar.TypeChecker.Util.fst"
let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (match ((FStar_TypeChecker_Rel.sub_comp env c c')) with
| None -> begin
(let _150_728 = (let _150_727 = (let _150_726 = (FStar_TypeChecker_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _150_725 = (FStar_TypeChecker_Env.get_range env)
in (_150_726, _150_725)))
in FStar_Syntax_Syntax.Error (_150_727))
in (Prims.raise _150_728))
end
| Some (g) -> begin
(e, c', g)
end))

# 812 "FStar.TypeChecker.Util.fst"
let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match ((let _150_737 = (FStar_Syntax_Subst.compress t)
in _150_737.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_71_1062) -> begin
(match ((let _150_738 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _150_738.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _71_1066) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.bool_lid) -> begin
(
# 817 "FStar.TypeChecker.Util.fst"
let _71_1069 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (
# 818 "FStar.TypeChecker.Util.fst"
let b2t = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos)
in (
# 819 "FStar.TypeChecker.Util.fst"
let lc = (let _150_741 = (let _150_740 = (let _150_739 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_739))
in (None, _150_740))
in (bind env (Some (e)) lc _150_741))
in (
# 820 "FStar.TypeChecker.Util.fst"
let e = (let _150_743 = (let _150_742 = (FStar_Syntax_Syntax.as_arg e)
in (_150_742)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _150_743 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (e, lc)))))
end
| _71_1075 -> begin
(e, lc)
end)
end
| _71_1077 -> begin
(e, lc)
end))

# 827 "FStar.TypeChecker.Util.fst"
let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (
# 828 "FStar.TypeChecker.Util.fst"
let gopt = if env.FStar_TypeChecker_Env.use_eq then begin
(let _150_752 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in (_150_752, false))
end else begin
(let _150_753 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in (_150_753, true))
end
in (match (gopt) with
| (None, _71_1085) -> begin
(FStar_TypeChecker_Rel.subtype_fail env lc.FStar_Syntax_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(match ((FStar_TypeChecker_Rel.guard_form g)) with
| FStar_TypeChecker_Common.Trivial -> begin
(
# 836 "FStar.TypeChecker.Util.fst"
let lc = (
# 836 "FStar.TypeChecker.Util.fst"
let _71_1092 = lc
in {FStar_Syntax_Syntax.eff_name = _71_1092.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _71_1092.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _71_1092.FStar_Syntax_Syntax.comp})
in (e, lc, g))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 840 "FStar.TypeChecker.Util.fst"
let g = (
# 840 "FStar.TypeChecker.Util.fst"
let _71_1097 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _71_1097.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _71_1097.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _71_1097.FStar_TypeChecker_Env.implicits})
in (
# 841 "FStar.TypeChecker.Util.fst"
let strengthen = (fun _71_1101 -> (match (()) with
| () -> begin
(
# 843 "FStar.TypeChecker.Util.fst"
let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (match ((let _150_756 = (FStar_Syntax_Subst.compress f)
in _150_756.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_71_1104, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _71_1113); FStar_Syntax_Syntax.tk = _71_1110; FStar_Syntax_Syntax.pos = _71_1108; FStar_Syntax_Syntax.vars = _71_1106}, _71_1118) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) -> begin
(
# 847 "FStar.TypeChecker.Util.fst"
let lc = (
# 847 "FStar.TypeChecker.Util.fst"
let _71_1121 = lc
in {FStar_Syntax_Syntax.eff_name = _71_1121.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _71_1121.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _71_1121.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| _71_1125 -> begin
(
# 851 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 852 "FStar.TypeChecker.Util.fst"
let _71_1127 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_760 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _150_759 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _150_758 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _150_757 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _150_760 _150_759 _150_758 _150_757)))))
end else begin
()
end
in (
# 859 "FStar.TypeChecker.Util.fst"
let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 860 "FStar.TypeChecker.Util.fst"
let _71_1132 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_71_1132) with
| (a, kwp) -> begin
(
# 861 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 862 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env ct.FStar_Syntax_Syntax.effect_name)
in (
# 863 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (
# 864 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 865 "FStar.TypeChecker.Util.fst"
let us = (let _150_761 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_150_761)::[])
in (
# 866 "FStar.TypeChecker.Util.fst"
let wp = (let _150_766 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ret)
in (let _150_765 = (let _150_764 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_763 = (let _150_762 = (FStar_Syntax_Syntax.as_arg xexp)
in (_150_762)::[])
in (_150_764)::_150_763))
in (FStar_Syntax_Syntax.mk_Tm_app _150_766 _150_765 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)))
in (
# 867 "FStar.TypeChecker.Util.fst"
let cret = (let _150_767 = (mk_comp md t wp wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_767))
in (
# 868 "FStar.TypeChecker.Util.fst"
let guard = if apply_guard then begin
(let _150_769 = (let _150_768 = (FStar_Syntax_Syntax.as_arg xexp)
in (_150_768)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _150_769 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end else begin
f
end
in (
# 869 "FStar.TypeChecker.Util.fst"
let _71_1143 = (let _150_777 = (FStar_All.pipe_left (fun _150_774 -> Some (_150_774)) (FStar_TypeChecker_Errors.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _150_776 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _150_775 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _150_777 _150_776 e cret _150_775))))
in (match (_71_1143) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(
# 873 "FStar.TypeChecker.Util.fst"
let x = (
# 873 "FStar.TypeChecker.Util.fst"
let _71_1144 = x
in {FStar_Syntax_Syntax.ppname = _71_1144.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _71_1144.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (
# 874 "FStar.TypeChecker.Util.fst"
let c = (let _150_779 = (let _150_778 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_778))
in (bind env (Some (e)) _150_779 (Some (x), eq_ret)))
in (
# 875 "FStar.TypeChecker.Util.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 876 "FStar.TypeChecker.Util.fst"
let _71_1149 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_780 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _150_780))
end else begin
()
end
in c))))
end))))))))))
end)))))
end))
end))
in (
# 879 "FStar.TypeChecker.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _71_5 -> (match (_71_5) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _71_1155 -> begin
[]
end))))
in (
# 880 "FStar.TypeChecker.Util.fst"
let lc = (
# 880 "FStar.TypeChecker.Util.fst"
let _71_1157 = lc
in (let _150_782 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _150_782; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (
# 881 "FStar.TypeChecker.Util.fst"
let g = (
# 881 "FStar.TypeChecker.Util.fst"
let _71_1160 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _71_1160.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _71_1160.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _71_1160.FStar_TypeChecker_Env.implicits})
in (e, lc, g))))))
end)
end)))

# 884 "FStar.TypeChecker.Util.fst"
let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (
# 885 "FStar.TypeChecker.Util.fst"
let mk_post_type = (fun res_t ens -> (
# 886 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _150_794 = (let _150_793 = (let _150_792 = (let _150_791 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _150_791))
in (_150_792)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _150_793 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _150_794))))
in (
# 888 "FStar.TypeChecker.Util.fst"
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
| (req, _71_1188)::(ens, _71_1183)::_71_1180 -> begin
(let _150_800 = (let _150_797 = (norm req)
in Some (_150_797))
in (let _150_799 = (let _150_798 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _150_798))
in (_150_800, _150_799)))
end
| _71_1192 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 902 "FStar.TypeChecker.Util.fst"
let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (wp, _71_1203)::(wlp, _71_1198)::_71_1195 -> begin
(
# 905 "FStar.TypeChecker.Util.fst"
let _71_1209 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (_71_1209) with
| (us_r, _71_1208) -> begin
(
# 906 "FStar.TypeChecker.Util.fst"
let _71_1213 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (_71_1213) with
| (us_e, _71_1212) -> begin
(
# 907 "FStar.TypeChecker.Util.fst"
let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (
# 908 "FStar.TypeChecker.Util.fst"
let as_req = (let _150_801 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.as_requires r)
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_801 us_r))
in (
# 909 "FStar.TypeChecker.Util.fst"
let as_ens = (let _150_802 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.as_ensures r)
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_802 us_e))
in (
# 910 "FStar.TypeChecker.Util.fst"
let req = (let _150_805 = (let _150_804 = (let _150_803 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_803)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.Implicit)))::_150_804)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _150_805 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 911 "FStar.TypeChecker.Util.fst"
let ens = (let _150_808 = (let _150_807 = (let _150_806 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_806)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.Implicit)))::_150_807)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _150_808 None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _150_812 = (let _150_809 = (norm req)
in Some (_150_809))
in (let _150_811 = (let _150_810 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm _150_810))
in (_150_812, _150_811))))))))
end))
end))
end
| _71_1220 -> begin
(FStar_All.failwith "Impossible")
end))
end
end)
end)))

# 921 "FStar.TypeChecker.Util.fst"
let maybe_instantiate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (
# 922 "FStar.TypeChecker.Util.fst"
let torig = (FStar_Syntax_Subst.compress t)
in if (not (env.FStar_TypeChecker_Env.instantiate_imp)) then begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end else begin
(match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 927 "FStar.TypeChecker.Util.fst"
let _71_1231 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_71_1231) with
| (bs, c) -> begin
(
# 928 "FStar.TypeChecker.Util.fst"
let rec aux = (fun subst _71_6 -> (match (_71_6) with
| (x, Some (FStar_Syntax_Syntax.Implicit))::rest -> begin
(
# 930 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 931 "FStar.TypeChecker.Util.fst"
let _71_1245 = (new_implicit_var env t)
in (match (_71_1245) with
| (v, u, g) -> begin
(
# 932 "FStar.TypeChecker.Util.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, v)))::subst
in (
# 933 "FStar.TypeChecker.Util.fst"
let _71_1251 = (aux subst rest)
in (match (_71_1251) with
| (args, bs, subst, g') -> begin
(let _150_823 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((v, Some (FStar_Syntax_Syntax.Implicit)))::args, bs, subst, _150_823))
end)))
end)))
end
| bs -> begin
([], bs, subst, FStar_TypeChecker_Rel.trivial_guard)
end))
in (
# 937 "FStar.TypeChecker.Util.fst"
let _71_1257 = (aux [] bs)
in (match (_71_1257) with
| (args, bs, subst, guard) -> begin
(match ((args, bs)) with
| ([], _71_1260) -> begin
(e, torig, guard)
end
| (_71_1263, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end
| _71_1267 -> begin
(
# 948 "FStar.TypeChecker.Util.fst"
let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _71_1270 -> begin
(FStar_Syntax_Util.arrow bs c)
end)
in (
# 951 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.subst subst t)
in (
# 952 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk_Tm_app e args (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (e, t, guard))))
end)
end)))
end))
end
| _71_1275 -> begin
(e, t, FStar_TypeChecker_Rel.trivial_guard)
end)
end))

# 962 "FStar.TypeChecker.Util.fst"
let gen_univs : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe_uvar Prims.list * (FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  Prims.bool))  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(
# 964 "FStar.TypeChecker.Util.fst"
let s = (let _150_835 = (let _150_834 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _150_834))
in (FStar_All.pipe_right _150_835 FStar_Util.set_elements))
in (
# 965 "FStar.TypeChecker.Util.fst"
let r = (let _150_836 = (FStar_TypeChecker_Env.get_range env)
in Some (_150_836))
in (
# 966 "FStar.TypeChecker.Util.fst"
let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (
# 967 "FStar.TypeChecker.Util.fst"
let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (
# 968 "FStar.TypeChecker.Util.fst"
let _71_1282 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _150_841 = (let _150_838 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _150_838))
in (let _150_840 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _150_839 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _150_841 _150_840 _150_839))))
end else begin
()
end
in (
# 970 "FStar.TypeChecker.Util.fst"
let _71_1284 = (FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))))
in u_name))))))
in u_names)))
end)

# 974 "FStar.TypeChecker.Util.fst"
let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t -> (
# 975 "FStar.TypeChecker.Util.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (
# 976 "FStar.TypeChecker.Util.fst"
let univs = (FStar_Syntax_Free.univs t)
in (
# 977 "FStar.TypeChecker.Util.fst"
let _71_1292 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _150_850 = (let _150_849 = (let _150_848 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _150_848 (FStar_List.map (fun u -> (let _150_847 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _150_847 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _150_849 (FStar_String.concat ", ")))
in (FStar_Util.print1 "univs to gen : %s\n" _150_850))
end else begin
()
end
in (
# 981 "FStar.TypeChecker.Util.fst"
let gen = (gen_univs env univs)
in (
# 982 "FStar.TypeChecker.Util.fst"
let _71_1295 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _150_851 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _150_851))
end else begin
()
end
in (
# 984 "FStar.TypeChecker.Util.fst"
let ts = (FStar_Syntax_Subst.close_univ_vars gen t)
in (gen, ts))))))))

# 987 "FStar.TypeChecker.Util.fst"
let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> if (let _150_857 = (FStar_Util.for_all (fun _71_1303 -> (match (_71_1303) with
| (_71_1301, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _150_857)) then begin
None
end else begin
(
# 991 "FStar.TypeChecker.Util.fst"
let norm = (fun c -> (
# 992 "FStar.TypeChecker.Util.fst"
let _71_1306 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _150_860 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _150_860))
end else begin
()
end
in (
# 994 "FStar.TypeChecker.Util.fst"
let c = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.Eta)::[]) env c)
end else begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env c)
end
in (
# 997 "FStar.TypeChecker.Util.fst"
let _71_1309 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _150_861 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _150_861))
end else begin
()
end
in c))))
in (
# 1000 "FStar.TypeChecker.Util.fst"
let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (
# 1001 "FStar.TypeChecker.Util.fst"
let gen_uvars = (fun uvs -> (let _150_864 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _150_864 FStar_Util.set_elements)))
in (
# 1002 "FStar.TypeChecker.Util.fst"
let _71_1326 = (let _150_866 = (FStar_All.pipe_right ecs (FStar_List.map (fun _71_1316 -> (match (_71_1316) with
| (e, c) -> begin
(
# 1003 "FStar.TypeChecker.Util.fst"
let t = (FStar_All.pipe_right (FStar_Syntax_Util.comp_result c) FStar_Syntax_Subst.compress)
in (
# 1004 "FStar.TypeChecker.Util.fst"
let c = (norm c)
in (
# 1005 "FStar.TypeChecker.Util.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (
# 1006 "FStar.TypeChecker.Util.fst"
let t = ct.FStar_Syntax_Syntax.result_typ
in (
# 1007 "FStar.TypeChecker.Util.fst"
let univs = (FStar_Syntax_Free.univs t)
in (
# 1008 "FStar.TypeChecker.Util.fst"
let uvt = (FStar_Syntax_Free.uvars t)
in (
# 1009 "FStar.TypeChecker.Util.fst"
let uvs = (gen_uvars uvt)
in (univs, (uvs, e, c)))))))))
end))))
in (FStar_All.pipe_right _150_866 FStar_List.unzip))
in (match (_71_1326) with
| (univs, uvars) -> begin
(
# 1012 "FStar.TypeChecker.Util.fst"
let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (
# 1013 "FStar.TypeChecker.Util.fst"
let gen_univs = (gen_univs env univs)
in (
# 1014 "FStar.TypeChecker.Util.fst"
let _71_1330 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end else begin
()
end
in (
# 1016 "FStar.TypeChecker.Util.fst"
let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _71_1335 -> (match (_71_1335) with
| (uvs, e, c) -> begin
(
# 1017 "FStar.TypeChecker.Util.fst"
let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _71_1338 -> (match (_71_1338) with
| (u, k) -> begin
(match ((FStar_Unionfind.find u)) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(a, Some (FStar_Syntax_Syntax.Implicit))
end
| FStar_Syntax_Syntax.Fixed (_71_1372) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _71_1375 -> begin
(
# 1023 "FStar.TypeChecker.Util.fst"
let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (
# 1024 "FStar.TypeChecker.Util.fst"
let _71_1379 = (FStar_Syntax_Util.arrow_formals k)
in (match (_71_1379) with
| (bs, kres) -> begin
(
# 1025 "FStar.TypeChecker.Util.fst"
let a = (let _150_872 = (let _150_871 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _150_870 -> Some (_150_870)) _150_871))
in (FStar_Syntax_Syntax.new_bv _150_872 kres))
in (
# 1026 "FStar.TypeChecker.Util.fst"
let t = (let _150_876 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _150_875 = (let _150_874 = (let _150_873 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _150_873))
in Some (_150_874))
in (FStar_Syntax_Util.abs bs _150_876 _150_875)))
in (
# 1027 "FStar.TypeChecker.Util.fst"
let _71_1382 = (FStar_Syntax_Util.set_uvar u t)
in (a, Some (FStar_Syntax_Syntax.Implicit)))))
end)))
end)
end))))
in (
# 1031 "FStar.TypeChecker.Util.fst"
let _71_1403 = (match (tvars) with
| [] -> begin
(e, c)
end
| _71_1387 -> begin
(
# 1037 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]) env c)
in (
# 1038 "FStar.TypeChecker.Util.fst"
let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]) env e)
in (
# 1040 "FStar.TypeChecker.Util.fst"
let t = (match ((let _150_877 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _150_877.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(
# 1042 "FStar.TypeChecker.Util.fst"
let _71_1396 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (_71_1396) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| _71_1398 -> begin
(FStar_Syntax_Util.arrow tvars c)
end)
in (
# 1047 "FStar.TypeChecker.Util.fst"
let e' = (FStar_Syntax_Util.abs tvars e None)
in (let _150_878 = (FStar_Syntax_Syntax.mk_Total t)
in (e', _150_878))))))
end)
in (match (_71_1403) with
| (e, c) -> begin
(gen_univs, e, c)
end)))
end))))
in Some (ecs)))))
end)))))
end)

# 1052 "FStar.TypeChecker.Util.fst"
let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> (
# 1053 "FStar.TypeChecker.Util.fst"
let _71_1413 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_885 = (let _150_884 = (FStar_List.map (fun _71_1412 -> (match (_71_1412) with
| (lb, _71_1409, _71_1411) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _150_884 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _150_885))
end else begin
()
end
in (match ((let _150_887 = (FStar_All.pipe_right lecs (FStar_List.map (fun _71_1419 -> (match (_71_1419) with
| (_71_1416, e, c) -> begin
(e, c)
end))))
in (gen env _150_887))) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun _71_1424 -> (match (_71_1424) with
| (l, t, c) -> begin
(l, [], t, c)
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _71_1432 _71_1436 -> (match ((_71_1432, _71_1436)) with
| ((l, _71_1429, _71_1431), (us, e, c)) -> begin
(
# 1060 "FStar.TypeChecker.Util.fst"
let _71_1437 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _150_893 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _150_892 = (FStar_Syntax_Print.lbname_to_string l)
in (let _150_891 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.print3 "(%s) Generalized %s to %s\n" _150_893 _150_892 _150_891))))
end else begin
()
end
in (l, us, e, c))
end)) lecs ecs)
end)))

# 1073 "FStar.TypeChecker.Util.fst"
let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (
# 1074 "FStar.TypeChecker.Util.fst"
let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (
# 1075 "FStar.TypeChecker.Util.fst"
let check = (fun env t1 t2 -> if env.FStar_TypeChecker_Env.use_eq then begin
(FStar_TypeChecker_Rel.try_teq env t1 t2)
end else begin
(match ((FStar_TypeChecker_Rel.try_subtype env t1 t2)) with
| None -> begin
None
end
| Some (f) -> begin
(let _150_909 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _150_908 -> Some (_150_908)) _150_909))
end)
end)
in (
# 1081 "FStar.TypeChecker.Util.fst"
let is_var = (fun e -> (match ((let _150_912 = (FStar_Syntax_Subst.compress e)
in _150_912.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (_71_1454) -> begin
true
end
| _71_1457 -> begin
false
end))
in (
# 1084 "FStar.TypeChecker.Util.fst"
let decorate = (fun e t -> (
# 1085 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((
# 1087 "FStar.TypeChecker.Util.fst"
let _71_1464 = x
in {FStar_Syntax_Syntax.ppname = _71_1464.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _71_1464.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| _71_1467 -> begin
(
# 1088 "FStar.TypeChecker.Util.fst"
let _71_1468 = e
in (let _150_917 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _71_1468.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _150_917; FStar_Syntax_Syntax.pos = _71_1468.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _71_1468.FStar_Syntax_Syntax.vars}))
end)))
in (
# 1089 "FStar.TypeChecker.Util.fst"
let env = (
# 1089 "FStar.TypeChecker.Util.fst"
let _71_1470 = env
in (let _150_918 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _71_1470.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _71_1470.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _71_1470.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _71_1470.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _71_1470.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _71_1470.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _71_1470.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _71_1470.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _71_1470.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _71_1470.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _71_1470.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _71_1470.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _71_1470.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _71_1470.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _71_1470.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _150_918; FStar_TypeChecker_Env.is_iface = _71_1470.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _71_1470.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _71_1470.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _71_1470.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _71_1470.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _71_1470.FStar_TypeChecker_Env.use_bv_sorts}))
in (match ((check env t1 t2)) with
| None -> begin
(let _150_922 = (let _150_921 = (let _150_920 = (FStar_TypeChecker_Errors.expected_expression_of_type env t2 e t1)
in (let _150_919 = (FStar_TypeChecker_Env.get_range env)
in (_150_920, _150_919)))
in FStar_Syntax_Syntax.Error (_150_921))
in (Prims.raise _150_922))
end
| Some (g) -> begin
(
# 1093 "FStar.TypeChecker.Util.fst"
let _71_1476 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _150_923 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _150_923))
end else begin
()
end
in (let _150_924 = (decorate e t2)
in (_150_924, g)))
end)))))))

# 1098 "FStar.TypeChecker.Util.fst"
let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (
# 1099 "FStar.TypeChecker.Util.fst"
let discharge = (fun g -> (
# 1100 "FStar.TypeChecker.Util.fst"
let _71_1483 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (
# 1102 "FStar.TypeChecker.Util.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _150_934 = (discharge g)
in (let _150_933 = (lc.FStar_Syntax_Syntax.comp ())
in (_150_934, _150_933)))
end else begin
(
# 1105 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 1106 "FStar.TypeChecker.Util.fst"
let steps = (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.DeltaComp)::[]
in (
# 1107 "FStar.TypeChecker.Util.fst"
let c = (let _150_935 = (FStar_TypeChecker_Normalize.normalize_comp steps env c)
in (FStar_All.pipe_right _150_935 FStar_Syntax_Util.comp_to_comp_typ))
in (
# 1108 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 1109 "FStar.TypeChecker.Util.fst"
let _71_1494 = (destruct_comp c)
in (match (_71_1494) with
| (t, wp, _71_1493) -> begin
(
# 1110 "FStar.TypeChecker.Util.fst"
let vc = (let _150_943 = (let _150_937 = (let _150_936 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_150_936)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _150_937 env md md.FStar_Syntax_Syntax.trivial))
in (let _150_942 = (let _150_940 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_939 = (let _150_938 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_938)::[])
in (_150_940)::_150_939))
in (let _150_941 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk_Tm_app _150_943 _150_942 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _150_941))))
in (
# 1111 "FStar.TypeChecker.Util.fst"
let _71_1496 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _150_944 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _150_944))
end else begin
()
end
in (
# 1113 "FStar.TypeChecker.Util.fst"
let g = (let _150_945 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _150_945))
in (let _150_947 = (discharge g)
in (let _150_946 = (FStar_Syntax_Syntax.mk_Comp c)
in (_150_947, _150_946))))))
end))))))
end)))

# 1119 "FStar.TypeChecker.Util.fst"
let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (
# 1120 "FStar.TypeChecker.Util.fst"
let short_bin_op = (fun f _71_7 -> (match (_71_7) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (fst, _71_1507)::[] -> begin
(f fst)
end
| _71_1511 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (
# 1125 "FStar.TypeChecker.Util.fst"
let op_and_e = (fun e -> (let _150_968 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _150_968 (fun _150_967 -> FStar_TypeChecker_Common.NonTrivial (_150_967)))))
in (
# 1126 "FStar.TypeChecker.Util.fst"
let op_or_e = (fun e -> (let _150_973 = (let _150_971 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _150_971))
in (FStar_All.pipe_right _150_973 (fun _150_972 -> FStar_TypeChecker_Common.NonTrivial (_150_972)))))
in (
# 1127 "FStar.TypeChecker.Util.fst"
let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _150_976 -> FStar_TypeChecker_Common.NonTrivial (_150_976))))
in (
# 1128 "FStar.TypeChecker.Util.fst"
let op_or_t = (fun t -> (let _150_980 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _150_980 (fun _150_979 -> FStar_TypeChecker_Common.NonTrivial (_150_979)))))
in (
# 1129 "FStar.TypeChecker.Util.fst"
let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _150_983 -> FStar_TypeChecker_Common.NonTrivial (_150_983))))
in (
# 1131 "FStar.TypeChecker.Util.fst"
let short_op_ite = (fun _71_8 -> (match (_71_8) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (guard, _71_1526)::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| _then::(guard, _71_1531)::[] -> begin
(let _150_987 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _150_987 (fun _150_986 -> FStar_TypeChecker_Common.NonTrivial (_150_986))))
end
| _71_1536 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (
# 1136 "FStar.TypeChecker.Util.fst"
let table = ((FStar_Syntax_Const.op_And, (short_bin_op op_and_e)))::((FStar_Syntax_Const.op_Or, (short_bin_op op_or_e)))::((FStar_Syntax_Const.and_lid, (short_bin_op op_and_t)))::((FStar_Syntax_Const.or_lid, (short_bin_op op_or_t)))::((FStar_Syntax_Const.imp_lid, (short_bin_op op_imp_t)))::((FStar_Syntax_Const.ite_lid, short_op_ite))::[]
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _71_1541) -> begin
(
# 1146 "FStar.TypeChecker.Util.fst"
let lid = fv.FStar_Syntax_Syntax.v
in (match ((FStar_Util.find_map table (fun _71_1547 -> (match (_71_1547) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _150_1020 = (mk seen_args)
in Some (_150_1020))
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
| _71_1552 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))

# 1153 "FStar.TypeChecker.Util.fst"
let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (match ((let _150_1023 = (FStar_Syntax_Subst.compress l)
in _150_1023.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (v, _71_1556) -> begin
(FStar_Util.for_some (FStar_Ident.lid_equals v.FStar_Syntax_Syntax.v) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| _71_1560 -> begin
false
end))

# 1174 "FStar.TypeChecker.Util.fst"
let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (
# 1175 "FStar.TypeChecker.Util.fst"
let pos = (fun bs -> (match (bs) with
| (hd, _71_1569)::_71_1566 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| _71_1573 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| (_71_1577, Some (FStar_Syntax_Syntax.Implicit))::_71_1575 -> begin
bs
end
| _71_1583 -> begin
(match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
bs
end
| Some (t) -> begin
(match ((let _150_1030 = (FStar_Syntax_Subst.compress t)
in _150_1030.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', _71_1589) -> begin
(match ((FStar_Util.prefix_until (fun _71_9 -> (match (_71_9) with
| (_71_1594, Some (FStar_Syntax_Syntax.Implicit)) -> begin
false
end
| _71_1599 -> begin
true
end)) bs')) with
| None -> begin
bs
end
| Some ([], _71_1603, _71_1605) -> begin
bs
end
| Some (imps, _71_1610, _71_1612) -> begin
if (FStar_All.pipe_right imps (FStar_Util.for_all (fun _71_1618 -> (match (_71_1618) with
| (x, _71_1617) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end)))) then begin
(
# 1191 "FStar.TypeChecker.Util.fst"
let r = (pos bs)
in (
# 1192 "FStar.TypeChecker.Util.fst"
let imps = (FStar_All.pipe_right imps (FStar_List.map (fun _71_1622 -> (match (_71_1622) with
| (x, i) -> begin
(let _150_1034 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in (_150_1034, i))
end))))
in (FStar_List.append imps bs)))
end else begin
bs
end
end)
end
| _71_1625 -> begin
bs
end)
end)
end)))




