
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
let rec find = (fun l -> (match ((FStar_TypeChecker_Env.lookup_effect_abbrev env l)) with
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
let c = (match ((FStar_TypeChecker_Env.lookup_effect_abbrev env FStar_Syntax_Const.effect_GTot_lid)) with
| None -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| _71_696 -> begin
(
# 502 "FStar.TypeChecker.Util.fst"
let m = (let _150_307 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must _150_307))
in (
# 503 "FStar.TypeChecker.Util.fst"
let _71_700 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_71_700) with
| (a, kwp) -> begin
(
# 504 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 505 "FStar.TypeChecker.Util.fst"
let wp = (let _150_313 = (let _150_312 = (FStar_TypeChecker_Env.inst_effect_fun env m m.FStar_Syntax_Syntax.ret)
in (let _150_311 = (let _150_310 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_309 = (let _150_308 = (FStar_Syntax_Syntax.as_arg v)
in (_150_308)::[])
in (_150_310)::_150_309))
in (FStar_Syntax_Syntax.mk_Tm_app _150_312 _150_311 (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _150_313))
in (
# 506 "FStar.TypeChecker.Util.fst"
let wlp = wp
in (mk_comp m t wp wlp ((FStar_Syntax_Syntax.RETURN)::[])))))
end)))
end)
in (
# 508 "FStar.TypeChecker.Util.fst"
let _71_705 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return"))) then begin
(let _150_316 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _150_315 = (FStar_Syntax_Print.term_to_string v)
in (let _150_314 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _150_316 _150_315 _150_314))))
end else begin
()
end
in c)))

# 513 "FStar.TypeChecker.Util.fst"
let bind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun env e1opt lc1 _71_712 -> (match (_71_712) with
| (b, lc2) -> begin
(
# 514 "FStar.TypeChecker.Util.fst"
let _71_720 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(
# 516 "FStar.TypeChecker.Util.fst"
let bstr = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _150_327 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (let _150_326 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _150_325 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" _150_327 _150_326 bstr _150_325)))))
end else begin
()
end
in (
# 522 "FStar.TypeChecker.Util.fst"
let bind_it = (fun _71_723 -> (match (()) with
| () -> begin
(
# 523 "FStar.TypeChecker.Util.fst"
let c1 = (lc1.FStar_Syntax_Syntax.comp ())
in (
# 524 "FStar.TypeChecker.Util.fst"
let c2 = (lc2.FStar_Syntax_Syntax.comp ())
in (
# 525 "FStar.TypeChecker.Util.fst"
let _71_729 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_334 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _150_333 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _150_332 = (FStar_Syntax_Print.comp_to_string c1)
in (let _150_331 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (let _150_330 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" _150_334 _150_333 _150_332 _150_331 _150_330))))))
end else begin
()
end
in (
# 534 "FStar.TypeChecker.Util.fst"
let try_simplify = (fun _71_732 -> (match (()) with
| () -> begin
(
# 535 "FStar.TypeChecker.Util.fst"
let aux = (fun _71_734 -> (match (()) with
| () -> begin
if (FStar_Syntax_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some ((c2, "trivial no binder"))
end
| Some (_71_737) -> begin
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
(let _150_340 = (let _150_339 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in (_150_339, "both gtot"))
in Some (_150_340))
end else begin
(match ((e1opt, b)) with
| (Some (e), Some (x)) -> begin
if ((FStar_Syntax_Util.is_total_comp c1) && (not ((FStar_Syntax_Syntax.is_null_bv x)))) then begin
(let _150_342 = (let _150_341 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT ((x, e)))::[]) c2)
in (_150_341, "substituted e"))
in Some (_150_342))
end else begin
(aux ())
end
end
| _71_745 -> begin
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
let _71_763 = (lift_and_destruct env c1 c2)
in (match (_71_763) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(
# 563 "FStar.TypeChecker.Util.fst"
let bs = (match (b) with
| None -> begin
(let _150_343 = (FStar_Syntax_Syntax.null_binder t1)
in (_150_343)::[])
end
| Some (x) -> begin
(let _150_344 = (FStar_Syntax_Syntax.mk_binder x)
in (_150_344)::[])
end)
in (
# 566 "FStar.TypeChecker.Util.fst"
let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp None))
in (
# 567 "FStar.TypeChecker.Util.fst"
let wp_args = (let _150_359 = (FStar_Syntax_Syntax.as_arg t1)
in (let _150_358 = (let _150_357 = (FStar_Syntax_Syntax.as_arg t2)
in (let _150_356 = (let _150_355 = (FStar_Syntax_Syntax.as_arg wp1)
in (let _150_354 = (let _150_353 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _150_352 = (let _150_351 = (let _150_347 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg _150_347))
in (let _150_350 = (let _150_349 = (let _150_348 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _150_348))
in (_150_349)::[])
in (_150_351)::_150_350))
in (_150_353)::_150_352))
in (_150_355)::_150_354))
in (_150_357)::_150_356))
in (_150_359)::_150_358))
in (
# 568 "FStar.TypeChecker.Util.fst"
let wlp_args = (let _150_367 = (FStar_Syntax_Syntax.as_arg t1)
in (let _150_366 = (let _150_365 = (FStar_Syntax_Syntax.as_arg t2)
in (let _150_364 = (let _150_363 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _150_362 = (let _150_361 = (let _150_360 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _150_360))
in (_150_361)::[])
in (_150_363)::_150_362))
in (_150_365)::_150_364))
in (_150_367)::_150_366))
in (
# 569 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t2)))::[]) kwp)
in (
# 570 "FStar.TypeChecker.Util.fst"
let wp = (let _150_368 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _150_368 wp_args None t2.FStar_Syntax_Syntax.pos))
in (
# 571 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_369 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.bind_wlp)
in (FStar_Syntax_Syntax.mk_Tm_app _150_369 wlp_args None t2.FStar_Syntax_Syntax.pos))
in (
# 572 "FStar.TypeChecker.Util.fst"
let c = (mk_comp md t2 wp wlp [])
in c))))))))
end))
end)))))
end))
in (let _150_370 = (join_lcomp env lc1 lc2)
in {FStar_Syntax_Syntax.eff_name = _150_370; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it})))
end))

# 579 "FStar.TypeChecker.Util.fst"
let lift_formula : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t mk_wp mk_wlp f -> (
# 580 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 581 "FStar.TypeChecker.Util.fst"
let _71_784 = (FStar_TypeChecker_Env.wp_signature env md_pure.FStar_Syntax_Syntax.mname)
in (match (_71_784) with
| (a, kwp) -> begin
(
# 582 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 583 "FStar.TypeChecker.Util.fst"
let wp = (let _150_384 = (let _150_383 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_382 = (let _150_381 = (FStar_Syntax_Syntax.as_arg f)
in (_150_381)::[])
in (_150_383)::_150_382))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wp _150_384 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (
# 584 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_388 = (let _150_387 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_386 = (let _150_385 = (FStar_Syntax_Syntax.as_arg f)
in (_150_385)::[])
in (_150_387)::_150_386))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wlp _150_388 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (mk_comp md_pure FStar_TypeChecker_Recheck.t_unit wp wlp []))))
end))))

# 587 "FStar.TypeChecker.Util.fst"
let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((f, FStar_Syntax_Syntax.Meta_labeled ((reason, r, false))))) None f.FStar_Syntax_Syntax.pos))

# 590 "FStar.TypeChecker.Util.fst"
let label_opt : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _150_412 = (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)
in (FStar_All.pipe_left Prims.op_Negation _150_412)) then begin
f
end else begin
(let _150_413 = (reason ())
in (label _150_413 r f))
end
end))

# 597 "FStar.TypeChecker.Util.fst"
let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 599 "FStar.TypeChecker.Util.fst"
let _71_804 = g
in (let _150_421 = (let _150_420 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_150_420))
in {FStar_TypeChecker_Env.guard_f = _150_421; FStar_TypeChecker_Env.deferred = _71_804.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _71_804.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _71_804.FStar_TypeChecker_Env.implicits}))
end))

# 601 "FStar.TypeChecker.Util.fst"
let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(
# 603 "FStar.TypeChecker.Util.fst"
let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| _71_815 -> begin
g2
end))

# 607 "FStar.TypeChecker.Util.fst"
let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (
# 608 "FStar.TypeChecker.Util.fst"
let weaken = (fun _71_820 -> (match (()) with
| () -> begin
(
# 609 "FStar.TypeChecker.Util.fst"
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
# 615 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 616 "FStar.TypeChecker.Util.fst"
let _71_829 = (destruct_comp c)
in (match (_71_829) with
| (res_t, wp, wlp) -> begin
(
# 617 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 618 "FStar.TypeChecker.Util.fst"
let wp = (let _150_440 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.assume_p)
in (let _150_439 = (let _150_438 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_437 = (let _150_436 = (FStar_Syntax_Syntax.as_arg f)
in (let _150_435 = (let _150_434 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_434)::[])
in (_150_436)::_150_435))
in (_150_438)::_150_437))
in (FStar_Syntax_Syntax.mk_Tm_app _150_440 _150_439 None wp.FStar_Syntax_Syntax.pos)))
in (
# 619 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_447 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.assume_p)
in (let _150_446 = (let _150_445 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_444 = (let _150_443 = (FStar_Syntax_Syntax.as_arg f)
in (let _150_442 = (let _150_441 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_441)::[])
in (_150_443)::_150_442))
in (_150_445)::_150_444))
in (FStar_Syntax_Syntax.mk_Tm_app _150_447 _150_446 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp c.FStar_Syntax_Syntax.flags))))
end)))
end
end))
end))
in (
# 621 "FStar.TypeChecker.Util.fst"
let _71_833 = lc
in {FStar_Syntax_Syntax.eff_name = _71_833.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _71_833.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _71_833.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))

# 623 "FStar.TypeChecker.Util.fst"
let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> if (FStar_TypeChecker_Rel.is_trivial g0) then begin
(lc, g0)
end else begin
(
# 627 "FStar.TypeChecker.Util.fst"
let _71_840 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_467 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _150_466 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _150_467 _150_466)))
end else begin
()
end
in (
# 631 "FStar.TypeChecker.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _71_4 -> (match (_71_4) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _71_846 -> begin
[]
end))))
in (
# 632 "FStar.TypeChecker.Util.fst"
let strengthen = (fun _71_849 -> (match (()) with
| () -> begin
(
# 633 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 634 "FStar.TypeChecker.Util.fst"
let g0 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (match ((FStar_TypeChecker_Rel.guard_form g0)) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 638 "FStar.TypeChecker.Util.fst"
let c = if (true || (((FStar_Syntax_Util.is_pure_or_ghost_comp c) && (not ((is_function (FStar_Syntax_Util.comp_result c))))) && (not ((FStar_Syntax_Util.is_partial_return c))))) then begin
(
# 643 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.gen_bv "strengthen_pre_x" None (FStar_Syntax_Util.comp_result c))
in (
# 644 "FStar.TypeChecker.Util.fst"
let xret = (let _150_472 = (let _150_471 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _150_471))
in (FStar_Syntax_Util.comp_set_flags _150_472 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (
# 645 "FStar.TypeChecker.Util.fst"
let lc = (bind env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), (FStar_Syntax_Util.lcomp_of_comp xret)))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (
# 649 "FStar.TypeChecker.Util.fst"
let _71_859 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_474 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _150_473 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _150_474 _150_473)))
end else begin
()
end
in (
# 654 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 655 "FStar.TypeChecker.Util.fst"
let _71_865 = (destruct_comp c)
in (match (_71_865) with
| (res_t, wp, wlp) -> begin
(
# 656 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 657 "FStar.TypeChecker.Util.fst"
let wp = (let _150_483 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.assert_p)
in (let _150_482 = (let _150_481 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_480 = (let _150_479 = (let _150_476 = (let _150_475 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason _150_475 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _150_476))
in (let _150_478 = (let _150_477 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_477)::[])
in (_150_479)::_150_478))
in (_150_481)::_150_480))
in (FStar_Syntax_Syntax.mk_Tm_app _150_483 _150_482 None wp.FStar_Syntax_Syntax.pos)))
in (
# 658 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_490 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.assume_p)
in (let _150_489 = (let _150_488 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_487 = (let _150_486 = (FStar_Syntax_Syntax.as_arg f)
in (let _150_485 = (let _150_484 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_484)::[])
in (_150_486)::_150_485))
in (_150_488)::_150_487))
in (FStar_Syntax_Syntax.mk_Tm_app _150_490 _150_489 None wlp.FStar_Syntax_Syntax.pos)))
in (
# 660 "FStar.TypeChecker.Util.fst"
let _71_869 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_491 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _150_491))
end else begin
()
end
in (
# 664 "FStar.TypeChecker.Util.fst"
let c2 = (mk_comp md res_t wp wlp flags)
in c2)))))
end)))))
end)))
end))
in (let _150_495 = (
# 666 "FStar.TypeChecker.Util.fst"
let _71_872 = lc
in (let _150_494 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _150_493 = if ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _150_492 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _150_492))) then begin
flags
end else begin
[]
end
in {FStar_Syntax_Syntax.eff_name = _150_494; FStar_Syntax_Syntax.res_typ = _71_872.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _150_493; FStar_Syntax_Syntax.comp = strengthen})))
in (_150_495, (
# 669 "FStar.TypeChecker.Util.fst"
let _71_874 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _71_874.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _71_874.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _71_874.FStar_TypeChecker_Env.implicits}))))))
end)

# 671 "FStar.TypeChecker.Util.fst"
let record_application_site : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (
# 672 "FStar.TypeChecker.Util.fst"
let comp = (fun _71_880 -> (match (()) with
| () -> begin
(
# 673 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 674 "FStar.TypeChecker.Util.fst"
let res_t = (FStar_Syntax_Util.comp_result c)
in if (((FStar_Syntax_Util.is_trivial_wp c) || (let _150_504 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals _150_504 FStar_Syntax_Const.prims_lid))) || (FStar_Syntax_Syntax.is_teff res_t)) then begin
c
end else begin
(
# 679 "FStar.TypeChecker.Util.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (FStar_TypeChecker_Recheck.t_unit)))
in (
# 680 "FStar.TypeChecker.Util.fst"
let _71_888 = (strengthen_precondition (Some ((fun _71_884 -> (match (()) with
| () -> begin
"push"
end)))) env e (FStar_Syntax_Util.lcomp_of_comp c) g)
in (match (_71_888) with
| (c, _71_887) -> begin
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
let xret = (let _150_512 = (FStar_TypeChecker_Env.inst_effect_fun env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _150_511 = (let _150_510 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_509 = (let _150_508 = (FStar_Syntax_Syntax.as_arg xexp)
in (_150_508)::[])
in (_150_510)::_150_509))
in (FStar_Syntax_Syntax.mk_Tm_app _150_512 _150_511 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 685 "FStar.TypeChecker.Util.fst"
let xret_comp = (let _150_513 = (mk_comp md_pure res_t xret xret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_513))
in (
# 686 "FStar.TypeChecker.Util.fst"
let lc = (let _150_519 = (let _150_518 = (let _150_517 = (strengthen_precondition (Some ((fun _71_894 -> (match (()) with
| () -> begin
"pop"
end)))) env xexp xret_comp g)
in (FStar_All.pipe_left Prims.fst _150_517))
in (Some (x), _150_518))
in (bind env None c _150_519))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end)))
end))
end))
in (
# 688 "FStar.TypeChecker.Util.fst"
let _71_896 = lc
in {FStar_Syntax_Syntax.eff_name = _71_896.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _71_896.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _71_896.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = comp})))

# 690 "FStar.TypeChecker.Util.fst"
let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env comp res_t -> (
# 691 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 692 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 693 "FStar.TypeChecker.Util.fst"
let y = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 694 "FStar.TypeChecker.Util.fst"
let _71_906 = (let _150_527 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _150_526 = (FStar_Syntax_Syntax.bv_to_name y)
in (_150_527, _150_526)))
in (match (_71_906) with
| (xexp, yexp) -> begin
(
# 695 "FStar.TypeChecker.Util.fst"
let yret = (let _150_532 = (FStar_TypeChecker_Env.inst_effect_fun env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _150_531 = (let _150_530 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_529 = (let _150_528 = (FStar_Syntax_Syntax.as_arg yexp)
in (_150_528)::[])
in (_150_530)::_150_529))
in (FStar_Syntax_Syntax.mk_Tm_app _150_532 _150_531 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 696 "FStar.TypeChecker.Util.fst"
let x_eq_y_yret = (let _150_540 = (FStar_TypeChecker_Env.inst_effect_fun env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _150_539 = (let _150_538 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_537 = (let _150_536 = (let _150_533 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _150_533))
in (let _150_535 = (let _150_534 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_150_534)::[])
in (_150_536)::_150_535))
in (_150_538)::_150_537))
in (FStar_Syntax_Syntax.mk_Tm_app _150_540 _150_539 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 697 "FStar.TypeChecker.Util.fst"
let forall_y_x_eq_y_yret = (let _150_550 = (FStar_TypeChecker_Env.inst_effect_fun env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _150_549 = (let _150_548 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_547 = (let _150_546 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_545 = (let _150_544 = (let _150_543 = (let _150_542 = (let _150_541 = (FStar_Syntax_Syntax.mk_binder y)
in (_150_541)::[])
in (FStar_Syntax_Util.abs _150_542 x_eq_y_yret None))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _150_543))
in (_150_544)::[])
in (_150_546)::_150_545))
in (_150_548)::_150_547))
in (FStar_Syntax_Syntax.mk_Tm_app _150_550 _150_549 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 698 "FStar.TypeChecker.Util.fst"
let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (
# 699 "FStar.TypeChecker.Util.fst"
let lc = (bind env None (FStar_Syntax_Util.lcomp_of_comp comp) (Some (x), (FStar_Syntax_Util.lcomp_of_comp lc2)))
in (lc.FStar_Syntax_Syntax.comp ()))))))
end))))))

# 702 "FStar.TypeChecker.Util.fst"
let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (
# 703 "FStar.TypeChecker.Util.fst"
let comp = (fun _71_917 -> (match (()) with
| () -> begin
(
# 704 "FStar.TypeChecker.Util.fst"
let _71_933 = (let _150_562 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _150_561 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _150_562 _150_561)))
in (match (_71_933) with
| ((md, _71_920, _71_922), (res_t, wp_then, wlp_then), (_71_929, wp_else, wlp_else)) -> begin
(
# 705 "FStar.TypeChecker.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _150_582 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.if_then_else)
in (let _150_581 = (let _150_579 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_578 = (let _150_577 = (FStar_Syntax_Syntax.as_arg g)
in (let _150_576 = (let _150_575 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _150_574 = (let _150_573 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_150_573)::[])
in (_150_575)::_150_574))
in (_150_577)::_150_576))
in (_150_579)::_150_578))
in (let _150_580 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _150_582 _150_581 None _150_580)))))
in (
# 706 "FStar.TypeChecker.Util.fst"
let wp = (ifthenelse md res_t guard wp_then wp_else)
in (
# 707 "FStar.TypeChecker.Util.fst"
let wlp = (ifthenelse md res_t guard wlp_then wlp_else)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(
# 709 "FStar.TypeChecker.Util.fst"
let comp = (mk_comp md res_t wp wlp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(
# 711 "FStar.TypeChecker.Util.fst"
let wp = (let _150_589 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.ite_wp)
in (let _150_588 = (let _150_587 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_586 = (let _150_585 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _150_584 = (let _150_583 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_583)::[])
in (_150_585)::_150_584))
in (_150_587)::_150_586))
in (FStar_Syntax_Syntax.mk_Tm_app _150_589 _150_588 None wp.FStar_Syntax_Syntax.pos)))
in (
# 712 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_594 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _150_593 = (let _150_592 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_591 = (let _150_590 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_590)::[])
in (_150_592)::_150_591))
in (FStar_Syntax_Syntax.mk_Tm_app _150_594 _150_593 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end)))
end))
end))
in (let _150_595 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _150_595; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp})))

# 719 "FStar.TypeChecker.Util.fst"
let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (
# 720 "FStar.TypeChecker.Util.fst"
let eff = (FStar_List.fold_left (fun eff _71_952 -> (match (_71_952) with
| (_71_950, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (
# 721 "FStar.TypeChecker.Util.fst"
let bind_cases = (fun _71_955 -> (match (()) with
| () -> begin
(
# 722 "FStar.TypeChecker.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _150_625 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.if_then_else)
in (let _150_624 = (let _150_622 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_621 = (let _150_620 = (FStar_Syntax_Syntax.as_arg g)
in (let _150_619 = (let _150_618 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _150_617 = (let _150_616 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_150_616)::[])
in (_150_618)::_150_617))
in (_150_620)::_150_619))
in (_150_622)::_150_621))
in (let _150_623 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _150_625 _150_624 None _150_623)))))
in (
# 724 "FStar.TypeChecker.Util.fst"
let default_case = (
# 725 "FStar.TypeChecker.Util.fst"
let post_k = (let _150_628 = (let _150_626 = (FStar_Syntax_Syntax.null_binder res_t)
in (_150_626)::[])
in (let _150_627 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _150_628 _150_627)))
in (
# 726 "FStar.TypeChecker.Util.fst"
let kwp = (let _150_631 = (let _150_629 = (FStar_Syntax_Syntax.null_binder post_k)
in (_150_629)::[])
in (let _150_630 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _150_631 _150_630)))
in (
# 727 "FStar.TypeChecker.Util.fst"
let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (
# 728 "FStar.TypeChecker.Util.fst"
let wp = (let _150_638 = (let _150_632 = (FStar_Syntax_Syntax.mk_binder post)
in (_150_632)::[])
in (let _150_637 = (let _150_636 = (let _150_633 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Errors.exhaustiveness_check _150_633))
in (let _150_635 = (let _150_634 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.false_lid _150_634))
in (FStar_All.pipe_left _150_636 _150_635)))
in (FStar_Syntax_Util.abs _150_638 _150_637 None)))
in (
# 729 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_642 = (let _150_639 = (FStar_Syntax_Syntax.mk_binder post)
in (_150_639)::[])
in (let _150_641 = (let _150_640 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid _150_640))
in (FStar_Syntax_Util.abs _150_642 _150_641 None)))
in (
# 730 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (
# 732 "FStar.TypeChecker.Util.fst"
let comp = (FStar_List.fold_right (fun _71_971 celse -> (match (_71_971) with
| (g, cthen) -> begin
(
# 733 "FStar.TypeChecker.Util.fst"
let _71_989 = (let _150_645 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _150_645 celse))
in (match (_71_989) with
| ((md, _71_975, _71_977), (_71_980, wp_then, wlp_then), (_71_985, wp_else, wlp_else)) -> begin
(let _150_647 = (ifthenelse md res_t g wp_then wp_else)
in (let _150_646 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _150_647 _150_646 [])))
end))
end)) lcases default_case)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(add_equality_to_post_condition env comp res_t)
end else begin
(
# 737 "FStar.TypeChecker.Util.fst"
let comp = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (
# 738 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env comp.FStar_Syntax_Syntax.effect_name)
in (
# 739 "FStar.TypeChecker.Util.fst"
let _71_997 = (destruct_comp comp)
in (match (_71_997) with
| (_71_994, wp, wlp) -> begin
(
# 740 "FStar.TypeChecker.Util.fst"
let wp = (let _150_654 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.ite_wp)
in (let _150_653 = (let _150_652 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_651 = (let _150_650 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _150_649 = (let _150_648 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_648)::[])
in (_150_650)::_150_649))
in (_150_652)::_150_651))
in (FStar_Syntax_Syntax.mk_Tm_app _150_654 _150_653 None wp.FStar_Syntax_Syntax.pos)))
in (
# 741 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_659 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _150_658 = (let _150_657 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_656 = (let _150_655 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_655)::[])
in (_150_657)::_150_656))
in (FStar_Syntax_Syntax.mk_Tm_app _150_659 _150_658 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end))))
end)))
end))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))

# 748 "FStar.TypeChecker.Util.fst"
let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (
# 749 "FStar.TypeChecker.Util.fst"
let close = (fun _71_1004 -> (match (()) with
| () -> begin
(
# 750 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in if (FStar_Syntax_Util.is_ml_comp c) then begin
c
end else begin
(
# 753 "FStar.TypeChecker.Util.fst"
let close_wp = (fun md res_t bvs wp0 -> (FStar_List.fold_right (fun x wp -> (
# 755 "FStar.TypeChecker.Util.fst"
let bs = (let _150_678 = (FStar_Syntax_Syntax.mk_binder x)
in (_150_678)::[])
in (
# 756 "FStar.TypeChecker.Util.fst"
let wp = (FStar_Syntax_Util.abs bs wp None)
in (let _150_685 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.close_wp)
in (let _150_684 = (let _150_683 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_682 = (let _150_681 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _150_680 = (let _150_679 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_679)::[])
in (_150_681)::_150_680))
in (_150_683)::_150_682))
in (FStar_Syntax_Syntax.mk_Tm_app _150_685 _150_684 None wp0.FStar_Syntax_Syntax.pos)))))) bvs wp0))
in (
# 759 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 760 "FStar.TypeChecker.Util.fst"
let _71_1019 = (destruct_comp c)
in (match (_71_1019) with
| (t, wp, wlp) -> begin
(
# 761 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 762 "FStar.TypeChecker.Util.fst"
let wp = (close_wp md c.FStar_Syntax_Syntax.result_typ bvs wp)
in (
# 763 "FStar.TypeChecker.Util.fst"
let wlp = (close_wp md c.FStar_Syntax_Syntax.result_typ bvs wlp)
in (mk_comp md c.FStar_Syntax_Syntax.result_typ wp wlp c.FStar_Syntax_Syntax.flags))))
end))))
end)
end))
in (
# 765 "FStar.TypeChecker.Util.fst"
let _71_1023 = lc
in {FStar_Syntax_Syntax.eff_name = _71_1023.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _71_1023.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _71_1023.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))

# 767 "FStar.TypeChecker.Util.fst"
let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (
# 768 "FStar.TypeChecker.Util.fst"
let refine = (fun _71_1029 -> (match (()) with
| () -> begin
(
# 769 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in if (not ((is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name))) then begin
c
end else begin
if (FStar_Syntax_Util.is_partial_return c) then begin
c
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c) && (let _150_694 = (FStar_TypeChecker_Env.lookup_effect_abbrev env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left FStar_Option.isNone _150_694))) then begin
(let _150_697 = (let _150_696 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _150_695 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _150_696 _150_695)))
in (FStar_All.failwith _150_697))
end else begin
(
# 776 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 777 "FStar.TypeChecker.Util.fst"
let t = c.FStar_Syntax_Syntax.result_typ
in (
# 778 "FStar.TypeChecker.Util.fst"
let c = (FStar_Syntax_Syntax.mk_Comp c)
in (
# 779 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (
# 780 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 781 "FStar.TypeChecker.Util.fst"
let ret = (let _150_699 = (let _150_698 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _150_698 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_699))
in (
# 782 "FStar.TypeChecker.Util.fst"
let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (
# 783 "FStar.TypeChecker.Util.fst"
let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (
# 785 "FStar.TypeChecker.Util.fst"
let c = (let _150_701 = (let _150_700 = (bind env None (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), eq_ret))
in (_150_700.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _150_701 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
in c)))))))))
end
end
end)
end))
in (
# 788 "FStar.TypeChecker.Util.fst"
let flags = if (((not ((FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)) && (not ((FStar_Syntax_Util.is_lcomp_partial_return lc)))) then begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_Syntax_Syntax.cflags
end else begin
lc.FStar_Syntax_Syntax.cflags
end
in (
# 794 "FStar.TypeChecker.Util.fst"
let _71_1041 = lc
in {FStar_Syntax_Syntax.eff_name = _71_1041.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _71_1041.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))

# 796 "FStar.TypeChecker.Util.fst"
let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (match ((FStar_TypeChecker_Rel.sub_comp env c c')) with
| None -> begin
(let _150_713 = (let _150_712 = (let _150_711 = (FStar_TypeChecker_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _150_710 = (FStar_TypeChecker_Env.get_range env)
in (_150_711, _150_710)))
in FStar_Syntax_Syntax.Error (_150_712))
in (Prims.raise _150_713))
end
| Some (g) -> begin
(e, c', g)
end))

# 802 "FStar.TypeChecker.Util.fst"
let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match ((let _150_722 = (FStar_Syntax_Subst.compress t)
in _150_722.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_71_1055) -> begin
(match ((let _150_723 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _150_723.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _71_1059) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.bool_lid) -> begin
(
# 807 "FStar.TypeChecker.Util.fst"
let _71_1062 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (
# 808 "FStar.TypeChecker.Util.fst"
let b2t = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos)
in (
# 809 "FStar.TypeChecker.Util.fst"
let lc = (let _150_726 = (let _150_725 = (let _150_724 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_724))
in (None, _150_725))
in (bind env (Some (e)) lc _150_726))
in (
# 810 "FStar.TypeChecker.Util.fst"
let e = (let _150_728 = (let _150_727 = (FStar_Syntax_Syntax.as_arg e)
in (_150_727)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _150_728 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (e, lc)))))
end
| _71_1068 -> begin
(e, lc)
end)
end
| _71_1070 -> begin
(e, lc)
end))

# 817 "FStar.TypeChecker.Util.fst"
let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (
# 818 "FStar.TypeChecker.Util.fst"
let gopt = if env.FStar_TypeChecker_Env.use_eq then begin
(let _150_737 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in (_150_737, false))
end else begin
(let _150_738 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in (_150_738, true))
end
in (match (gopt) with
| (None, _71_1078) -> begin
(FStar_TypeChecker_Rel.subtype_fail env lc.FStar_Syntax_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(match ((FStar_TypeChecker_Rel.guard_form g)) with
| FStar_TypeChecker_Common.Trivial -> begin
(
# 826 "FStar.TypeChecker.Util.fst"
let lc = (
# 826 "FStar.TypeChecker.Util.fst"
let _71_1085 = lc
in {FStar_Syntax_Syntax.eff_name = _71_1085.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _71_1085.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _71_1085.FStar_Syntax_Syntax.comp})
in (e, lc, g))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 830 "FStar.TypeChecker.Util.fst"
let g = (
# 830 "FStar.TypeChecker.Util.fst"
let _71_1090 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _71_1090.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _71_1090.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _71_1090.FStar_TypeChecker_Env.implicits})
in (
# 831 "FStar.TypeChecker.Util.fst"
let strengthen = (fun _71_1094 -> (match (()) with
| () -> begin
(
# 833 "FStar.TypeChecker.Util.fst"
let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (match ((let _150_741 = (FStar_Syntax_Subst.compress f)
in _150_741.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_71_1097, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _71_1106); FStar_Syntax_Syntax.tk = _71_1103; FStar_Syntax_Syntax.pos = _71_1101; FStar_Syntax_Syntax.vars = _71_1099}, _71_1111) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) -> begin
(
# 837 "FStar.TypeChecker.Util.fst"
let lc = (
# 837 "FStar.TypeChecker.Util.fst"
let _71_1114 = lc
in {FStar_Syntax_Syntax.eff_name = _71_1114.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _71_1114.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _71_1114.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| _71_1118 -> begin
(
# 841 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 842 "FStar.TypeChecker.Util.fst"
let _71_1120 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_745 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _150_744 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _150_743 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _150_742 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _150_745 _150_744 _150_743 _150_742)))))
end else begin
()
end
in (
# 849 "FStar.TypeChecker.Util.fst"
let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 850 "FStar.TypeChecker.Util.fst"
let _71_1125 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_71_1125) with
| (a, kwp) -> begin
(
# 851 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 852 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env ct.FStar_Syntax_Syntax.effect_name)
in (
# 853 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (
# 854 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 855 "FStar.TypeChecker.Util.fst"
let wp = (let _150_750 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.ret)
in (let _150_749 = (let _150_748 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_747 = (let _150_746 = (FStar_Syntax_Syntax.as_arg xexp)
in (_150_746)::[])
in (_150_748)::_150_747))
in (FStar_Syntax_Syntax.mk_Tm_app _150_750 _150_749 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)))
in (
# 856 "FStar.TypeChecker.Util.fst"
let cret = (let _150_751 = (mk_comp md t wp wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_751))
in (
# 857 "FStar.TypeChecker.Util.fst"
let guard = if apply_guard then begin
(let _150_753 = (let _150_752 = (FStar_Syntax_Syntax.as_arg xexp)
in (_150_752)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _150_753 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end else begin
f
end
in (
# 858 "FStar.TypeChecker.Util.fst"
let _71_1135 = (let _150_761 = (FStar_All.pipe_left (fun _150_758 -> Some (_150_758)) (FStar_TypeChecker_Errors.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _150_760 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _150_759 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _150_761 _150_760 e cret _150_759))))
in (match (_71_1135) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(
# 862 "FStar.TypeChecker.Util.fst"
let x = (
# 862 "FStar.TypeChecker.Util.fst"
let _71_1136 = x
in {FStar_Syntax_Syntax.ppname = _71_1136.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _71_1136.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (
# 863 "FStar.TypeChecker.Util.fst"
let c = (let _150_763 = (let _150_762 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_762))
in (bind env (Some (e)) _150_763 (Some (x), eq_ret)))
in (
# 864 "FStar.TypeChecker.Util.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 865 "FStar.TypeChecker.Util.fst"
let _71_1141 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_764 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _150_764))
end else begin
()
end
in c))))
end)))))))))
end)))))
end))
end))
in (
# 868 "FStar.TypeChecker.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _71_5 -> (match (_71_5) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _71_1147 -> begin
[]
end))))
in (
# 869 "FStar.TypeChecker.Util.fst"
let lc = (
# 869 "FStar.TypeChecker.Util.fst"
let _71_1149 = lc
in (let _150_766 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _150_766; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (
# 870 "FStar.TypeChecker.Util.fst"
let g = (
# 870 "FStar.TypeChecker.Util.fst"
let _71_1152 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _71_1152.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _71_1152.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _71_1152.FStar_TypeChecker_Env.implicits})
in (e, lc, g))))))
end)
end)))

# 873 "FStar.TypeChecker.Util.fst"
let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (
# 874 "FStar.TypeChecker.Util.fst"
let mk_post_type = (fun res_t ens -> (
# 875 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _150_778 = (let _150_777 = (let _150_776 = (let _150_775 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _150_775))
in (_150_776)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _150_777 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _150_778))))
in (
# 877 "FStar.TypeChecker.Util.fst"
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
| (req, _71_1180)::(ens, _71_1175)::_71_1172 -> begin
(let _150_784 = (let _150_781 = (norm req)
in Some (_150_781))
in (let _150_783 = (let _150_782 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _150_782))
in (_150_784, _150_783)))
end
| _71_1184 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 891 "FStar.TypeChecker.Util.fst"
let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (wp, _71_1195)::(wlp, _71_1190)::_71_1187 -> begin
(
# 894 "FStar.TypeChecker.Util.fst"
let _71_1201 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (_71_1201) with
| (us_r, _71_1200) -> begin
(
# 895 "FStar.TypeChecker.Util.fst"
let _71_1205 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (_71_1205) with
| (us_e, _71_1204) -> begin
(
# 896 "FStar.TypeChecker.Util.fst"
let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (
# 897 "FStar.TypeChecker.Util.fst"
let as_req = (let _150_785 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.as_requires r)
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_785 us_r))
in (
# 898 "FStar.TypeChecker.Util.fst"
let as_ens = (let _150_786 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.as_ensures r)
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_786 us_e))
in (
# 899 "FStar.TypeChecker.Util.fst"
let req = (let _150_789 = (let _150_788 = (let _150_787 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_787)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.Implicit)))::_150_788)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _150_789 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 900 "FStar.TypeChecker.Util.fst"
let ens = (let _150_792 = (let _150_791 = (let _150_790 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_790)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.Implicit)))::_150_791)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _150_792 None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _150_796 = (let _150_793 = (norm req)
in Some (_150_793))
in (let _150_795 = (let _150_794 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm _150_794))
in (_150_796, _150_795))))))))
end))
end))
end
| _71_1212 -> begin
(FStar_All.failwith "Impossible")
end))
end
end)
end)))

# 910 "FStar.TypeChecker.Util.fst"
let maybe_instantiate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (
# 911 "FStar.TypeChecker.Util.fst"
let torig = (FStar_Syntax_Subst.compress t)
in if (not (env.FStar_TypeChecker_Env.instantiate_imp)) then begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end else begin
(match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 916 "FStar.TypeChecker.Util.fst"
let _71_1223 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_71_1223) with
| (bs, c) -> begin
(
# 917 "FStar.TypeChecker.Util.fst"
let rec aux = (fun subst _71_6 -> (match (_71_6) with
| (x, Some (FStar_Syntax_Syntax.Implicit))::rest -> begin
(
# 919 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 920 "FStar.TypeChecker.Util.fst"
let _71_1237 = (new_implicit_var env t)
in (match (_71_1237) with
| (v, u, g) -> begin
(
# 921 "FStar.TypeChecker.Util.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, v)))::subst
in (
# 922 "FStar.TypeChecker.Util.fst"
let _71_1243 = (aux subst rest)
in (match (_71_1243) with
| (args, bs, subst, g') -> begin
(let _150_807 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((v, Some (FStar_Syntax_Syntax.Implicit)))::args, bs, subst, _150_807))
end)))
end)))
end
| bs -> begin
([], bs, subst, FStar_TypeChecker_Rel.trivial_guard)
end))
in (
# 926 "FStar.TypeChecker.Util.fst"
let _71_1249 = (aux [] bs)
in (match (_71_1249) with
| (args, bs, subst, guard) -> begin
(match ((args, bs)) with
| ([], _71_1252) -> begin
(e, torig, guard)
end
| (_71_1255, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end
| _71_1259 -> begin
(
# 937 "FStar.TypeChecker.Util.fst"
let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _71_1262 -> begin
(FStar_Syntax_Util.arrow bs c)
end)
in (
# 940 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.subst subst t)
in (
# 941 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk_Tm_app e args (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (e, t, guard))))
end)
end)))
end))
end
| _71_1267 -> begin
(e, t, FStar_TypeChecker_Rel.trivial_guard)
end)
end))

# 951 "FStar.TypeChecker.Util.fst"
let gen_univs : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe_uvar Prims.list * (FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  Prims.bool))  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(
# 953 "FStar.TypeChecker.Util.fst"
let s = (let _150_819 = (let _150_818 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _150_818))
in (FStar_All.pipe_right _150_819 FStar_Util.set_elements))
in (
# 954 "FStar.TypeChecker.Util.fst"
let r = (let _150_820 = (FStar_TypeChecker_Env.get_range env)
in Some (_150_820))
in (
# 955 "FStar.TypeChecker.Util.fst"
let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (
# 956 "FStar.TypeChecker.Util.fst"
let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (
# 957 "FStar.TypeChecker.Util.fst"
let _71_1274 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _150_825 = (let _150_822 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _150_822))
in (let _150_824 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _150_823 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _150_825 _150_824 _150_823))))
end else begin
()
end
in (
# 959 "FStar.TypeChecker.Util.fst"
let _71_1276 = (FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))))
in u_name))))))
in u_names)))
end)

# 963 "FStar.TypeChecker.Util.fst"
let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t -> (
# 964 "FStar.TypeChecker.Util.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (
# 965 "FStar.TypeChecker.Util.fst"
let univs = (FStar_Syntax_Free.univs t)
in (
# 966 "FStar.TypeChecker.Util.fst"
let _71_1284 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _150_834 = (let _150_833 = (let _150_832 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _150_832 (FStar_List.map (fun u -> (let _150_831 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _150_831 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _150_833 (FStar_String.concat ", ")))
in (FStar_Util.print1 "univs to gen : %s\n" _150_834))
end else begin
()
end
in (
# 970 "FStar.TypeChecker.Util.fst"
let gen = (gen_univs env univs)
in (
# 971 "FStar.TypeChecker.Util.fst"
let _71_1287 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _150_835 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _150_835))
end else begin
()
end
in (
# 973 "FStar.TypeChecker.Util.fst"
let ts = (FStar_Syntax_Subst.close_univ_vars gen t)
in (gen, ts))))))))

# 976 "FStar.TypeChecker.Util.fst"
let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> if (let _150_841 = (FStar_Util.for_all (fun _71_1295 -> (match (_71_1295) with
| (_71_1293, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _150_841)) then begin
None
end else begin
(
# 980 "FStar.TypeChecker.Util.fst"
let norm = (fun c -> (
# 981 "FStar.TypeChecker.Util.fst"
let _71_1298 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _150_844 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _150_844))
end else begin
()
end
in (
# 983 "FStar.TypeChecker.Util.fst"
let c = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.Eta)::[]) env c)
end else begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env c)
end
in (
# 986 "FStar.TypeChecker.Util.fst"
let _71_1301 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _150_845 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _150_845))
end else begin
()
end
in c))))
in (
# 989 "FStar.TypeChecker.Util.fst"
let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (
# 990 "FStar.TypeChecker.Util.fst"
let gen_uvars = (fun uvs -> (let _150_848 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _150_848 FStar_Util.set_elements)))
in (
# 991 "FStar.TypeChecker.Util.fst"
let _71_1318 = (let _150_850 = (FStar_All.pipe_right ecs (FStar_List.map (fun _71_1308 -> (match (_71_1308) with
| (e, c) -> begin
(
# 992 "FStar.TypeChecker.Util.fst"
let t = (FStar_All.pipe_right (FStar_Syntax_Util.comp_result c) FStar_Syntax_Subst.compress)
in (
# 993 "FStar.TypeChecker.Util.fst"
let c = (norm c)
in (
# 994 "FStar.TypeChecker.Util.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (
# 995 "FStar.TypeChecker.Util.fst"
let t = ct.FStar_Syntax_Syntax.result_typ
in (
# 996 "FStar.TypeChecker.Util.fst"
let univs = (FStar_Syntax_Free.univs t)
in (
# 997 "FStar.TypeChecker.Util.fst"
let uvt = (FStar_Syntax_Free.uvars t)
in (
# 998 "FStar.TypeChecker.Util.fst"
let uvs = (gen_uvars uvt)
in (univs, (uvs, e, c)))))))))
end))))
in (FStar_All.pipe_right _150_850 FStar_List.unzip))
in (match (_71_1318) with
| (univs, uvars) -> begin
(
# 1001 "FStar.TypeChecker.Util.fst"
let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (
# 1002 "FStar.TypeChecker.Util.fst"
let gen_univs = (gen_univs env univs)
in (
# 1003 "FStar.TypeChecker.Util.fst"
let _71_1322 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end else begin
()
end
in (
# 1006 "FStar.TypeChecker.Util.fst"
let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _71_1327 -> (match (_71_1327) with
| (uvs, e, c) -> begin
(
# 1007 "FStar.TypeChecker.Util.fst"
let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _71_1330 -> (match (_71_1330) with
| (u, k) -> begin
(match ((FStar_Unionfind.find u)) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(a, Some (FStar_Syntax_Syntax.Implicit))
end
| FStar_Syntax_Syntax.Fixed (_71_1364) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _71_1367 -> begin
(
# 1013 "FStar.TypeChecker.Util.fst"
let _71_1370 = (FStar_Syntax_Util.arrow_formals k)
in (match (_71_1370) with
| (bs, kres) -> begin
(
# 1014 "FStar.TypeChecker.Util.fst"
let a = (let _150_856 = (let _150_855 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _150_854 -> Some (_150_854)) _150_855))
in (FStar_Syntax_Syntax.new_bv _150_856 kres))
in (
# 1015 "FStar.TypeChecker.Util.fst"
let t = (let _150_860 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _150_859 = (let _150_858 = (let _150_857 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _150_857))
in Some (_150_858))
in (FStar_Syntax_Util.abs bs _150_860 _150_859)))
in (
# 1016 "FStar.TypeChecker.Util.fst"
let _71_1373 = (FStar_Syntax_Util.set_uvar u t)
in (a, Some (FStar_Syntax_Syntax.Implicit)))))
end))
end)
end))))
in (
# 1019 "FStar.TypeChecker.Util.fst"
let _71_1394 = (match (tvars) with
| [] -> begin
(e, c)
end
| _71_1378 -> begin
(
# 1025 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]) env c)
in (
# 1026 "FStar.TypeChecker.Util.fst"
let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]) env e)
in (
# 1028 "FStar.TypeChecker.Util.fst"
let t = (match ((let _150_861 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _150_861.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(
# 1030 "FStar.TypeChecker.Util.fst"
let _71_1387 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (_71_1387) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| _71_1389 -> begin
(FStar_Syntax_Util.arrow tvars c)
end)
in (
# 1035 "FStar.TypeChecker.Util.fst"
let e' = (FStar_Syntax_Util.abs tvars e None)
in (let _150_862 = (FStar_Syntax_Syntax.mk_Total t)
in (e', _150_862))))))
end)
in (match (_71_1394) with
| (e, c) -> begin
(gen_univs, e, c)
end)))
end))))
in Some (ecs)))))
end)))))
end)

# 1040 "FStar.TypeChecker.Util.fst"
let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> (
# 1041 "FStar.TypeChecker.Util.fst"
let _71_1404 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_869 = (let _150_868 = (FStar_List.map (fun _71_1403 -> (match (_71_1403) with
| (lb, _71_1400, _71_1402) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _150_868 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _150_869))
end else begin
()
end
in (match ((let _150_871 = (FStar_All.pipe_right lecs (FStar_List.map (fun _71_1410 -> (match (_71_1410) with
| (_71_1407, e, c) -> begin
(e, c)
end))))
in (gen env _150_871))) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun _71_1415 -> (match (_71_1415) with
| (l, t, c) -> begin
(l, [], t, c)
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _71_1423 _71_1427 -> (match ((_71_1423, _71_1427)) with
| ((l, _71_1420, _71_1422), (us, e, c)) -> begin
(
# 1048 "FStar.TypeChecker.Util.fst"
let _71_1428 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _150_877 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _150_876 = (FStar_Syntax_Print.lbname_to_string l)
in (let _150_875 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.print3 "(%s) Generalized %s to %s\n" _150_877 _150_876 _150_875))))
end else begin
()
end
in (l, us, e, c))
end)) lecs ecs)
end)))

# 1061 "FStar.TypeChecker.Util.fst"
let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (
# 1062 "FStar.TypeChecker.Util.fst"
let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (
# 1063 "FStar.TypeChecker.Util.fst"
let check = (fun env t1 t2 -> if env.FStar_TypeChecker_Env.use_eq then begin
(FStar_TypeChecker_Rel.try_teq env t1 t2)
end else begin
(match ((FStar_TypeChecker_Rel.try_subtype env t1 t2)) with
| None -> begin
None
end
| Some (f) -> begin
(let _150_893 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _150_892 -> Some (_150_892)) _150_893))
end)
end)
in (
# 1069 "FStar.TypeChecker.Util.fst"
let is_var = (fun e -> (match ((let _150_896 = (FStar_Syntax_Subst.compress e)
in _150_896.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (_71_1445) -> begin
true
end
| _71_1448 -> begin
false
end))
in (
# 1072 "FStar.TypeChecker.Util.fst"
let decorate = (fun e t -> (
# 1073 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((
# 1075 "FStar.TypeChecker.Util.fst"
let _71_1455 = x
in {FStar_Syntax_Syntax.ppname = _71_1455.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _71_1455.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| _71_1458 -> begin
(
# 1076 "FStar.TypeChecker.Util.fst"
let _71_1459 = e
in (let _150_901 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _71_1459.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _150_901; FStar_Syntax_Syntax.pos = _71_1459.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _71_1459.FStar_Syntax_Syntax.vars}))
end)))
in (
# 1077 "FStar.TypeChecker.Util.fst"
let env = (
# 1077 "FStar.TypeChecker.Util.fst"
let _71_1461 = env
in (let _150_902 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _71_1461.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _71_1461.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _71_1461.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _71_1461.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _71_1461.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _71_1461.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _71_1461.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _71_1461.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _71_1461.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _71_1461.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _71_1461.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _71_1461.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _71_1461.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _71_1461.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _71_1461.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _150_902; FStar_TypeChecker_Env.is_iface = _71_1461.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _71_1461.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _71_1461.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _71_1461.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _71_1461.FStar_TypeChecker_Env.use_bv_sorts}))
in (match ((check env t1 t2)) with
| None -> begin
(let _150_906 = (let _150_905 = (let _150_904 = (FStar_TypeChecker_Errors.expected_expression_of_type env t2 e t1)
in (let _150_903 = (FStar_TypeChecker_Env.get_range env)
in (_150_904, _150_903)))
in FStar_Syntax_Syntax.Error (_150_905))
in (Prims.raise _150_906))
end
| Some (g) -> begin
(
# 1081 "FStar.TypeChecker.Util.fst"
let _71_1467 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _150_907 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _150_907))
end else begin
()
end
in (let _150_908 = (decorate e t2)
in (_150_908, g)))
end)))))))

# 1086 "FStar.TypeChecker.Util.fst"
let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (
# 1087 "FStar.TypeChecker.Util.fst"
let discharge = (fun g -> (
# 1088 "FStar.TypeChecker.Util.fst"
let _71_1474 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (
# 1090 "FStar.TypeChecker.Util.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _150_918 = (discharge g)
in (let _150_917 = (lc.FStar_Syntax_Syntax.comp ())
in (_150_918, _150_917)))
end else begin
(
# 1093 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 1094 "FStar.TypeChecker.Util.fst"
let steps = (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.DeltaComp)::[]
in (
# 1095 "FStar.TypeChecker.Util.fst"
let c = (let _150_919 = (FStar_TypeChecker_Normalize.normalize_comp steps env c)
in (FStar_All.pipe_right _150_919 FStar_Syntax_Util.comp_to_comp_typ))
in (
# 1096 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 1097 "FStar.TypeChecker.Util.fst"
let _71_1485 = (destruct_comp c)
in (match (_71_1485) with
| (t, wp, _71_1484) -> begin
(
# 1098 "FStar.TypeChecker.Util.fst"
let vc = (let _150_925 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.trivial)
in (let _150_924 = (let _150_922 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_921 = (let _150_920 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_920)::[])
in (_150_922)::_150_921))
in (let _150_923 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk_Tm_app _150_925 _150_924 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _150_923))))
in (
# 1099 "FStar.TypeChecker.Util.fst"
let _71_1487 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _150_926 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _150_926))
end else begin
()
end
in (
# 1101 "FStar.TypeChecker.Util.fst"
let g = (let _150_927 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _150_927))
in (let _150_929 = (discharge g)
in (let _150_928 = (FStar_Syntax_Syntax.mk_Comp c)
in (_150_929, _150_928))))))
end))))))
end)))

# 1107 "FStar.TypeChecker.Util.fst"
let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (
# 1108 "FStar.TypeChecker.Util.fst"
let short_bin_op = (fun f _71_7 -> (match (_71_7) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (fst, _71_1498)::[] -> begin
(f fst)
end
| _71_1502 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (
# 1113 "FStar.TypeChecker.Util.fst"
let op_and_e = (fun e -> (let _150_950 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _150_950 (fun _150_949 -> FStar_TypeChecker_Common.NonTrivial (_150_949)))))
in (
# 1114 "FStar.TypeChecker.Util.fst"
let op_or_e = (fun e -> (let _150_955 = (let _150_953 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _150_953))
in (FStar_All.pipe_right _150_955 (fun _150_954 -> FStar_TypeChecker_Common.NonTrivial (_150_954)))))
in (
# 1115 "FStar.TypeChecker.Util.fst"
let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _150_958 -> FStar_TypeChecker_Common.NonTrivial (_150_958))))
in (
# 1116 "FStar.TypeChecker.Util.fst"
let op_or_t = (fun t -> (let _150_962 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _150_962 (fun _150_961 -> FStar_TypeChecker_Common.NonTrivial (_150_961)))))
in (
# 1117 "FStar.TypeChecker.Util.fst"
let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _150_965 -> FStar_TypeChecker_Common.NonTrivial (_150_965))))
in (
# 1119 "FStar.TypeChecker.Util.fst"
let short_op_ite = (fun _71_8 -> (match (_71_8) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (guard, _71_1517)::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| _then::(guard, _71_1522)::[] -> begin
(let _150_969 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _150_969 (fun _150_968 -> FStar_TypeChecker_Common.NonTrivial (_150_968))))
end
| _71_1527 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (
# 1124 "FStar.TypeChecker.Util.fst"
let table = ((FStar_Syntax_Const.op_And, (short_bin_op op_and_e)))::((FStar_Syntax_Const.op_Or, (short_bin_op op_or_e)))::((FStar_Syntax_Const.and_lid, (short_bin_op op_and_t)))::((FStar_Syntax_Const.or_lid, (short_bin_op op_or_t)))::((FStar_Syntax_Const.imp_lid, (short_bin_op op_imp_t)))::((FStar_Syntax_Const.ite_lid, short_op_ite))::[]
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _71_1532) -> begin
(
# 1134 "FStar.TypeChecker.Util.fst"
let lid = fv.FStar_Syntax_Syntax.v
in (match ((FStar_Util.find_map table (fun _71_1538 -> (match (_71_1538) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _150_1002 = (mk seen_args)
in Some (_150_1002))
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
| _71_1543 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))

# 1141 "FStar.TypeChecker.Util.fst"
let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (match ((let _150_1005 = (FStar_Syntax_Subst.compress l)
in _150_1005.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (v, _71_1547) -> begin
(FStar_Util.for_some (FStar_Ident.lid_equals v.FStar_Syntax_Syntax.v) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| _71_1551 -> begin
false
end))

# 1162 "FStar.TypeChecker.Util.fst"
let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (
# 1163 "FStar.TypeChecker.Util.fst"
let pos = (fun bs -> (match (bs) with
| (hd, _71_1560)::_71_1557 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| _71_1564 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| (_71_1568, Some (FStar_Syntax_Syntax.Implicit))::_71_1566 -> begin
bs
end
| _71_1574 -> begin
(match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
bs
end
| Some (t) -> begin
(match ((let _150_1012 = (FStar_Syntax_Subst.compress t)
in _150_1012.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', _71_1580) -> begin
(match ((FStar_Util.prefix_until (fun _71_9 -> (match (_71_9) with
| (_71_1585, Some (FStar_Syntax_Syntax.Implicit)) -> begin
false
end
| _71_1590 -> begin
true
end)) bs')) with
| None -> begin
bs
end
| Some ([], _71_1594, _71_1596) -> begin
bs
end
| Some (imps, _71_1601, _71_1603) -> begin
if (FStar_All.pipe_right imps (FStar_Util.for_all (fun _71_1609 -> (match (_71_1609) with
| (x, _71_1608) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end)))) then begin
(
# 1179 "FStar.TypeChecker.Util.fst"
let r = (pos bs)
in (
# 1180 "FStar.TypeChecker.Util.fst"
let imps = (FStar_All.pipe_right imps (FStar_List.map (fun _71_1613 -> (match (_71_1613) with
| (x, i) -> begin
(let _150_1016 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in (_150_1016, i))
end))))
in (FStar_List.append imps bs)))
end else begin
bs
end
end)
end
| _71_1616 -> begin
bs
end)
end)
end)))




