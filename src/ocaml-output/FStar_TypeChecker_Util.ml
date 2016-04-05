
open Prims
# 29 "FStar.TypeChecker.Util.fst"
type lcomp_with_binder =
(FStar_Syntax_Syntax.bv Prims.option * FStar_Syntax_Syntax.lcomp)

# 75 "FStar.TypeChecker.Util.fst"
let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _156_6 = (FStar_TypeChecker_Env.get_range env)
in (let _156_5 = (FStar_TypeChecker_Errors.failed_to_prove_specification errs)
in (FStar_TypeChecker_Errors.report _156_6 _156_5))))

# 80 "FStar.TypeChecker.Util.fst"
let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _156_9 = (FStar_Syntax_Subst.compress t)
in _156_9.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_67_12) -> begin
true
end
| _67_15 -> begin
false
end))

# 87 "FStar.TypeChecker.Util.fst"
let t_binders : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env -> (let _156_13 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right _156_13 (FStar_List.filter (fun _67_20 -> (match (_67_20) with
| (x, _67_19) -> begin
(is_type x.FStar_Syntax_Syntax.sort)
end))))))

# 90 "FStar.TypeChecker.Util.fst"
let new_uvar_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun env k -> (
# 94 "FStar.TypeChecker.Util.fst"
let bs = if ((FStar_ST.read FStar_Options.full_context_dependency) || (let _156_18 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _156_18))) then begin
(FStar_TypeChecker_Env.all_binders env)
end else begin
(t_binders env)
end
in (let _156_19 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Rel.new_uvar _156_19 bs k))))

# 98 "FStar.TypeChecker.Util.fst"
let new_uvar : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env k -> (let _156_24 = (new_uvar_aux env k)
in (Prims.fst _156_24)))

# 100 "FStar.TypeChecker.Util.fst"
let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun _67_1 -> (match (_67_1) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, _67_35); FStar_Syntax_Syntax.tk = _67_32; FStar_Syntax_Syntax.pos = _67_30; FStar_Syntax_Syntax.vars = _67_28} -> begin
uv
end
| _67_40 -> begin
(FStar_All.failwith "Impossible")
end))

# 104 "FStar.TypeChecker.Util.fst"
let new_implicit_var : Prims.string  ->  FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.uvar * FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t) = (fun reason r env k -> (match ((FStar_Syntax_Util.destruct k FStar_Syntax_Const.range_of_lid)) with
| Some (_67_50::(tm, _67_47)::[]) -> begin
(
# 109 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))) None tm.FStar_Syntax_Syntax.pos)
in (t, [], FStar_TypeChecker_Rel.trivial_guard))
end
| _67_55 -> begin
(
# 113 "FStar.TypeChecker.Util.fst"
let _67_58 = (new_uvar_aux env k)
in (match (_67_58) with
| (t, u) -> begin
(
# 114 "FStar.TypeChecker.Util.fst"
let g = (
# 114 "FStar.TypeChecker.Util.fst"
let _67_59 = FStar_TypeChecker_Rel.trivial_guard
in (let _156_37 = (let _156_36 = (let _156_35 = (as_uvar u)
in (reason, env, _156_35, t, k, r))
in (_156_36)::[])
in {FStar_TypeChecker_Env.guard_f = _67_59.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _67_59.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _67_59.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _156_37}))
in (let _156_40 = (let _156_39 = (let _156_38 = (as_uvar u)
in (_156_38, r))
in (_156_39)::[])
in (t, _156_40, g)))
end))
end))

# 115 "FStar.TypeChecker.Util.fst"
let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun r t -> (
# 118 "FStar.TypeChecker.Util.fst"
let uvs = (FStar_Syntax_Free.uvars t)
in if (not ((FStar_Util.set_is_empty uvs))) then begin
(
# 121 "FStar.TypeChecker.Util.fst"
let us = (let _156_47 = (let _156_46 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun _67_68 -> (match (_67_68) with
| (x, _67_67) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) _156_46))
in (FStar_All.pipe_right _156_47 (FStar_String.concat ", ")))
in (
# 123 "FStar.TypeChecker.Util.fst"
let hide_uvar_nums_saved = (FStar_ST.read FStar_Options.hide_uvar_nums)
in (
# 124 "FStar.TypeChecker.Util.fst"
let print_implicits_saved = (FStar_ST.read FStar_Options.print_implicits)
in (
# 125 "FStar.TypeChecker.Util.fst"
let _67_72 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums false)
in (
# 126 "FStar.TypeChecker.Util.fst"
let _67_74 = (FStar_ST.op_Colon_Equals FStar_Options.print_implicits true)
in (
# 127 "FStar.TypeChecker.Util.fst"
let _67_76 = (let _156_49 = (let _156_48 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us _156_48))
in (FStar_TypeChecker_Errors.report r _156_49))
in (
# 130 "FStar.TypeChecker.Util.fst"
let _67_78 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums hide_uvar_nums_saved)
in (FStar_ST.op_Colon_Equals FStar_Options.print_implicits print_implicits_saved))))))))
end else begin
()
end))

# 131 "FStar.TypeChecker.Util.fst"
let force_sort' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' = (fun s -> (match ((FStar_ST.read s.FStar_Syntax_Syntax.tk)) with
| None -> begin
(let _156_54 = (let _156_53 = (FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos)
in (let _156_52 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s" _156_53 _156_52)))
in (FStar_All.failwith _156_54))
end
| Some (tk) -> begin
tk
end))

# 139 "FStar.TypeChecker.Util.fst"
let force_sort = (fun s -> (let _156_56 = (force_sort' s)
in (FStar_Syntax_Syntax.mk _156_56 None s.FStar_Syntax_Syntax.pos)))

# 141 "FStar.TypeChecker.Util.fst"
let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env _67_93 -> (match (_67_93) with
| {FStar_Syntax_Syntax.lbname = _67_92; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _67_88; FStar_Syntax_Syntax.lbdef = e} -> begin
(
# 144 "FStar.TypeChecker.Util.fst"
let rng = t.FStar_Syntax_Syntax.pos
in (
# 145 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 148 "FStar.TypeChecker.Util.fst"
let _67_97 = if (univ_vars <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (
# 149 "FStar.TypeChecker.Util.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 150 "FStar.TypeChecker.Util.fst"
let mk_binder = (fun scope a -> (match (a.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 152 "FStar.TypeChecker.Util.fst"
let _67_107 = (FStar_Syntax_Util.type_u ())
in (match (_67_107) with
| (k, _67_106) -> begin
(
# 153 "FStar.TypeChecker.Util.fst"
let t = (let _156_65 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right _156_65 Prims.fst))
in ((
# 154 "FStar.TypeChecker.Util.fst"
let _67_109 = a
in {FStar_Syntax_Syntax.ppname = _67_109.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _67_109.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), false))
end))
end
| _67_112 -> begin
(a, true)
end))
in (
# 157 "FStar.TypeChecker.Util.fst"
let rec aux = (fun vars e -> (
# 158 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, _67_119) -> begin
(aux vars e)
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _67_125) -> begin
(t, true)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _67_131) -> begin
(
# 164 "FStar.TypeChecker.Util.fst"
let _67_150 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _67_137 _67_140 -> (match ((_67_137, _67_140)) with
| ((scope, bs, check), (a, imp)) -> begin
(
# 165 "FStar.TypeChecker.Util.fst"
let _67_143 = (mk_binder scope a)
in (match (_67_143) with
| (tb, c) -> begin
(
# 166 "FStar.TypeChecker.Util.fst"
let b = (tb, imp)
in (
# 167 "FStar.TypeChecker.Util.fst"
let bs = (FStar_List.append bs ((b)::[]))
in (
# 168 "FStar.TypeChecker.Util.fst"
let scope = (FStar_List.append scope ((b)::[]))
in (scope, bs, (c || check)))))
end))
end)) (vars, [], false)))
in (match (_67_150) with
| (scope, bs, check) -> begin
(
# 172 "FStar.TypeChecker.Util.fst"
let _67_153 = (aux scope body)
in (match (_67_153) with
| (res, check_res) -> begin
(
# 173 "FStar.TypeChecker.Util.fst"
let c = (match (res) with
| FStar_Util.Inl (t) -> begin
(FStar_Syntax_Util.ml_comp t r)
end
| FStar_Util.Inr (c) -> begin
c
end)
in (
# 176 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Util.arrow bs c)
in (
# 177 "FStar.TypeChecker.Util.fst"
let _67_160 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _156_73 = (FStar_Range.string_of_range r)
in (let _156_72 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _156_73 _156_72)))
end else begin
()
end
in (FStar_Util.Inl (t), (check_res || check)))))
end))
end))
end
| _67_163 -> begin
(let _156_76 = (let _156_75 = (let _156_74 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _156_74 Prims.fst))
in FStar_Util.Inl (_156_75))
in (_156_76, false))
end)))
in (
# 182 "FStar.TypeChecker.Util.fst"
let _67_166 = (let _156_77 = (t_binders env)
in (aux _156_77 e))
in (match (_67_166) with
| (t, b) -> begin
(
# 183 "FStar.TypeChecker.Util.fst"
let t = (match (t) with
| FStar_Util.Inr (c) -> begin
(let _156_81 = (let _156_80 = (let _156_79 = (let _156_78 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" _156_78))
in (_156_79, rng))
in FStar_Syntax_Syntax.Error (_156_80))
in (Prims.raise _156_81))
end
| FStar_Util.Inl (t) -> begin
t
end)
in ([], t, b))
end))))))
end
| _67_173 -> begin
(
# 192 "FStar.TypeChecker.Util.fst"
let _67_176 = (FStar_Syntax_Subst.open_univ_vars univ_vars t)
in (match (_67_176) with
| (univ_vars, t) -> begin
(univ_vars, t, false)
end))
end)))
end))

# 193 "FStar.TypeChecker.Util.fst"
let pat_as_exps : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term Prims.list * FStar_Syntax_Syntax.pat) = (fun allow_implicits env p -> (
# 208 "FStar.TypeChecker.Util.fst"
let rec pat_as_arg_with_env = (fun allow_wc_dependence env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(
# 217 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) None p.FStar_Syntax_Syntax.p)
in ([], [], [], env, e, p))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _67_189) -> begin
(
# 221 "FStar.TypeChecker.Util.fst"
let _67_195 = (FStar_Syntax_Util.type_u ())
in (match (_67_195) with
| (k, _67_194) -> begin
(
# 222 "FStar.TypeChecker.Util.fst"
let t = (new_uvar env k)
in (
# 223 "FStar.TypeChecker.Util.fst"
let x = (
# 223 "FStar.TypeChecker.Util.fst"
let _67_197 = x
in {FStar_Syntax_Syntax.ppname = _67_197.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _67_197.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (
# 224 "FStar.TypeChecker.Util.fst"
let _67_202 = (let _156_94 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _156_94 t))
in (match (_67_202) with
| (e, u) -> begin
(
# 225 "FStar.TypeChecker.Util.fst"
let p = (
# 225 "FStar.TypeChecker.Util.fst"
let _67_203 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, e)); FStar_Syntax_Syntax.ty = _67_203.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _67_203.FStar_Syntax_Syntax.p})
in ([], [], [], env, e, p))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 229 "FStar.TypeChecker.Util.fst"
let _67_211 = (FStar_Syntax_Util.type_u ())
in (match (_67_211) with
| (t, _67_210) -> begin
(
# 230 "FStar.TypeChecker.Util.fst"
let x = (
# 230 "FStar.TypeChecker.Util.fst"
let _67_212 = x
in (let _156_95 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _67_212.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _67_212.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _156_95}))
in (
# 231 "FStar.TypeChecker.Util.fst"
let env = if allow_wc_dependence then begin
(FStar_TypeChecker_Env.push_bv env x)
end else begin
env
end
in (
# 232 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in ((x)::[], [], (x)::[], env, e, p))))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 236 "FStar.TypeChecker.Util.fst"
let _67_222 = (FStar_Syntax_Util.type_u ())
in (match (_67_222) with
| (t, _67_221) -> begin
(
# 237 "FStar.TypeChecker.Util.fst"
let x = (
# 237 "FStar.TypeChecker.Util.fst"
let _67_223 = x
in (let _156_96 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _67_223.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _67_223.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _156_96}))
in (
# 238 "FStar.TypeChecker.Util.fst"
let env = (FStar_TypeChecker_Env.push_bv env x)
in (
# 239 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in ((x)::[], (x)::[], [], env, e, p))))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 243 "FStar.TypeChecker.Util.fst"
let _67_256 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _67_238 _67_241 -> (match ((_67_238, _67_241)) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(
# 244 "FStar.TypeChecker.Util.fst"
let _67_248 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_67_248) with
| (b', a', w', env, te, pat) -> begin
(
# 245 "FStar.TypeChecker.Util.fst"
let arg = if imp then begin
(FStar_Syntax_Syntax.iarg te)
end else begin
(FStar_Syntax_Syntax.as_arg te)
end
in ((b')::b, (a')::a, (w')::w, env, (arg)::args, ((pat, imp))::pats))
end))
end)) ([], [], [], env, [], [])))
in (match (_67_256) with
| (b, a, w, env, args, pats) -> begin
(
# 248 "FStar.TypeChecker.Util.fst"
let e = (let _156_103 = (let _156_102 = (let _156_101 = (let _156_100 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (let _156_99 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app _156_100 _156_99 None p.FStar_Syntax_Syntax.p)))
in (_156_101, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))
in FStar_Syntax_Syntax.Tm_meta (_156_102))
in (FStar_Syntax_Syntax.mk _156_103 None p.FStar_Syntax_Syntax.p))
in (let _156_106 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _156_105 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _156_104 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in (_156_106, _156_105, _156_104, env, e, (
# 254 "FStar.TypeChecker.Util.fst"
let _67_258 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _67_258.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _67_258.FStar_Syntax_Syntax.p}))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (_67_261) -> begin
(FStar_All.failwith "impossible")
end))
in (
# 258 "FStar.TypeChecker.Util.fst"
let rec elaborate_pat = (fun env p -> (
# 259 "FStar.TypeChecker.Util.fst"
let maybe_dot = (fun inaccessible a r -> if (allow_implicits && inaccessible) then begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term ((a, FStar_Syntax_Syntax.tun))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end else begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var (a)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end)
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 265 "FStar.TypeChecker.Util.fst"
let pats = (FStar_List.map (fun _67_276 -> (match (_67_276) with
| (p, imp) -> begin
(let _156_118 = (elaborate_pat env p)
in (_156_118, imp))
end)) pats)
in (
# 266 "FStar.TypeChecker.Util.fst"
let _67_281 = (FStar_TypeChecker_Env.lookup_datacon env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_67_281) with
| (_67_279, t) -> begin
(
# 267 "FStar.TypeChecker.Util.fst"
let _67_285 = (FStar_Syntax_Util.arrow_formals t)
in (match (_67_285) with
| (f, _67_284) -> begin
(
# 268 "FStar.TypeChecker.Util.fst"
let rec aux = (fun formals pats -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _67_296::_67_294) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))))
end
| (_67_302::_67_300, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun _67_308 -> (match (_67_308) with
| (t, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(
# 274 "FStar.TypeChecker.Util.fst"
let a = (let _156_125 = (let _156_124 = (FStar_Syntax_Syntax.range_of_bv t)
in Some (_156_124))
in (FStar_Syntax_Syntax.new_bv _156_125 FStar_Syntax_Syntax.tun))
in (
# 275 "FStar.TypeChecker.Util.fst"
let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (let _156_126 = (maybe_dot inaccessible a r)
in (_156_126, true))))
end
| _67_315 -> begin
(let _156_130 = (let _156_129 = (let _156_128 = (let _156_127 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _156_127))
in (_156_128, (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in FStar_Syntax_Syntax.Error (_156_129))
in (Prims.raise _156_130))
end)
end))))
end
| (f::formals', (p, p_imp)::pats') -> begin
(match (f) with
| (_67_326, Some (FStar_Syntax_Syntax.Implicit (_67_328))) when p_imp -> begin
(let _156_131 = (aux formals' pats')
in ((p, true))::_156_131)
end
| (_67_333, Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(
# 287 "FStar.TypeChecker.Util.fst"
let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (
# 288 "FStar.TypeChecker.Util.fst"
let p = (maybe_dot inaccessible a (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
in (let _156_132 = (aux formals' pats)
in ((p, true))::_156_132)))
end
| (_67_341, imp) -> begin
(let _156_135 = (let _156_133 = (FStar_Syntax_Syntax.is_implicit imp)
in (p, _156_133))
in (let _156_134 = (aux formals' pats')
in (_156_135)::_156_134))
end)
end))
in (
# 294 "FStar.TypeChecker.Util.fst"
let _67_344 = p
in (let _156_138 = (let _156_137 = (let _156_136 = (aux f pats)
in (fv, _156_136))
in FStar_Syntax_Syntax.Pat_cons (_156_137))
in {FStar_Syntax_Syntax.v = _156_138; FStar_Syntax_Syntax.ty = _67_344.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _67_344.FStar_Syntax_Syntax.p})))
end))
end)))
end
| _67_347 -> begin
p
end)))
in (
# 298 "FStar.TypeChecker.Util.fst"
let one_pat = (fun allow_wc_dependence env p -> (
# 299 "FStar.TypeChecker.Util.fst"
let p = (elaborate_pat env p)
in (
# 300 "FStar.TypeChecker.Util.fst"
let _67_359 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_67_359) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))) with
| Some (x) -> begin
(let _156_147 = (let _156_146 = (let _156_145 = (FStar_TypeChecker_Errors.nonlinear_pattern_variable x)
in (_156_145, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_156_146))
in (Prims.raise _156_147))
end
| _67_363 -> begin
(b, a, w, arg, p)
end)
end))))
in (
# 305 "FStar.TypeChecker.Util.fst"
let top_level_pat_as_args = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_disj (q::pats) -> begin
(
# 312 "FStar.TypeChecker.Util.fst"
let _67_379 = (one_pat false env q)
in (match (_67_379) with
| (b, a, _67_376, te, q) -> begin
(
# 313 "FStar.TypeChecker.Util.fst"
let _67_394 = (FStar_List.fold_right (fun p _67_384 -> (match (_67_384) with
| (w, args, pats) -> begin
(
# 314 "FStar.TypeChecker.Util.fst"
let _67_390 = (one_pat false env p)
in (match (_67_390) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv FStar_Syntax_Syntax.bv_eq a a'))) then begin
(let _156_157 = (let _156_156 = (let _156_155 = (FStar_TypeChecker_Errors.disjunctive_pattern_vars a a')
in (let _156_154 = (FStar_TypeChecker_Env.get_range env)
in (_156_155, _156_154)))
in FStar_Syntax_Syntax.Error (_156_156))
in (Prims.raise _156_157))
end else begin
(let _156_159 = (let _156_158 = (FStar_Syntax_Syntax.as_arg arg)
in (_156_158)::args)
in ((FStar_List.append w' w), _156_159, (p)::pats))
end
end))
end)) pats ([], [], []))
in (match (_67_394) with
| (w, args, pats) -> begin
(let _156_161 = (let _156_160 = (FStar_Syntax_Syntax.as_arg te)
in (_156_160)::args)
in ((FStar_List.append b w), _156_161, (
# 319 "FStar.TypeChecker.Util.fst"
let _67_395 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((q)::pats); FStar_Syntax_Syntax.ty = _67_395.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _67_395.FStar_Syntax_Syntax.p})))
end))
end))
end
| _67_398 -> begin
(
# 322 "FStar.TypeChecker.Util.fst"
let _67_406 = (one_pat true env p)
in (match (_67_406) with
| (b, _67_401, _67_403, arg, p) -> begin
(let _156_163 = (let _156_162 = (FStar_Syntax_Syntax.as_arg arg)
in (_156_162)::[])
in (b, _156_163, p))
end))
end))
in (
# 325 "FStar.TypeChecker.Util.fst"
let _67_410 = (top_level_pat_as_args env p)
in (match (_67_410) with
| (b, args, p) -> begin
(
# 326 "FStar.TypeChecker.Util.fst"
let exps = (FStar_All.pipe_right args (FStar_List.map Prims.fst))
in (b, exps, p))
end)))))))

# 327 "FStar.TypeChecker.Util.fst"
let decorate_pattern : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.pat = (fun env p exps -> (
# 330 "FStar.TypeChecker.Util.fst"
let qq = p
in (
# 331 "FStar.TypeChecker.Util.fst"
let rec aux = (fun p e -> (
# 332 "FStar.TypeChecker.Util.fst"
let pkg = (fun q t -> (FStar_Syntax_Syntax.withinfo q t p.FStar_Syntax_Syntax.p))
in (
# 333 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Util.unmeta e)
in (match ((p.FStar_Syntax_Syntax.v, e.FStar_Syntax_Syntax.n)) with
| (_67_424, FStar_Syntax_Syntax.Tm_uinst (e, _67_427)) -> begin
(aux p e)
end
| (FStar_Syntax_Syntax.Pat_constant (_67_432), FStar_Syntax_Syntax.Tm_constant (_67_435)) -> begin
(let _156_178 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v _156_178))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(
# 341 "FStar.TypeChecker.Util.fst"
let _67_443 = if (not ((FStar_Syntax_Syntax.bv_eq x y))) then begin
(let _156_181 = (let _156_180 = (FStar_Syntax_Print.bv_to_string x)
in (let _156_179 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _156_180 _156_179)))
in (FStar_All.failwith _156_181))
end else begin
()
end
in (
# 343 "FStar.TypeChecker.Util.fst"
let _67_445 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _156_183 = (FStar_Syntax_Print.bv_to_string x)
in (let _156_182 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _156_183 _156_182)))
end else begin
()
end
in (
# 345 "FStar.TypeChecker.Util.fst"
let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (
# 346 "FStar.TypeChecker.Util.fst"
let x = (
# 346 "FStar.TypeChecker.Util.fst"
let _67_448 = x
in {FStar_Syntax_Syntax.ppname = _67_448.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _67_448.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x)) s.FStar_Syntax_Syntax.n)))))
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(
# 350 "FStar.TypeChecker.Util.fst"
let _67_456 = if (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation) then begin
(let _156_186 = (let _156_185 = (FStar_Syntax_Print.bv_to_string x)
in (let _156_184 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _156_185 _156_184)))
in (FStar_All.failwith _156_186))
end else begin
()
end
in (
# 352 "FStar.TypeChecker.Util.fst"
let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (
# 353 "FStar.TypeChecker.Util.fst"
let x = (
# 353 "FStar.TypeChecker.Util.fst"
let _67_459 = x
in {FStar_Syntax_Syntax.ppname = _67_459.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _67_459.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x)) s.FStar_Syntax_Syntax.n))))
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _67_464), _67_468) -> begin
(
# 357 "FStar.TypeChecker.Util.fst"
let s = (force_sort e)
in (
# 358 "FStar.TypeChecker.Util.fst"
let x = (
# 358 "FStar.TypeChecker.Util.fst"
let _67_471 = x
in {FStar_Syntax_Syntax.ppname = _67_471.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _67_471.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
(
# 362 "FStar.TypeChecker.Util.fst"
let _67_481 = if (not ((FStar_Syntax_Syntax.fv_eq fv fv'))) then begin
(let _156_187 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _156_187))
end else begin
()
end
in (let _156_188 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv', []))) _156_188)))
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
(
# 369 "FStar.TypeChecker.Util.fst"
let _67_524 = if (let _156_189 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right _156_189 Prims.op_Negation)) then begin
(let _156_190 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _156_190))
end else begin
()
end
in (
# 372 "FStar.TypeChecker.Util.fst"
let fv = fv'
in (
# 373 "FStar.TypeChecker.Util.fst"
let rec match_args = (fun matched_pats args argpats -> (match ((args, argpats)) with
| ([], []) -> begin
(let _156_197 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev matched_pats)))) _156_197))
end
| (arg::args, (argpat, _67_540)::argpats) -> begin
(match ((arg, argpat.FStar_Syntax_Syntax.v)) with
| ((e, Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (_67_550)) -> begin
(
# 378 "FStar.TypeChecker.Util.fst"
let x = (let _156_198 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _156_198))
in (
# 379 "FStar.TypeChecker.Util.fst"
let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((e, imp), _67_559) -> begin
(
# 383 "FStar.TypeChecker.Util.fst"
let pat = (let _156_200 = (aux argpat e)
in (let _156_199 = (FStar_Syntax_Syntax.is_implicit imp)
in (_156_200, _156_199)))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _67_563 -> begin
(let _156_203 = (let _156_202 = (FStar_Syntax_Print.pat_to_string p)
in (let _156_201 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _156_202 _156_201)))
in (FStar_All.failwith _156_203))
end))
in (match_args [] args argpats))))
end
| _67_565 -> begin
(let _156_208 = (let _156_207 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (let _156_206 = (FStar_Syntax_Print.pat_to_string qq)
in (let _156_205 = (let _156_204 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right _156_204 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _156_207 _156_206 _156_205))))
in (FStar_All.failwith _156_208))
end))))
in (match ((p.FStar_Syntax_Syntax.v, exps)) with
| (FStar_Syntax_Syntax.Pat_disj (ps), _67_569) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(
# 396 "FStar.TypeChecker.Util.fst"
let ps = (FStar_List.map2 aux ps exps)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj (ps)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p))
end
| (_67_573, e::[]) -> begin
(aux p e)
end
| _67_578 -> begin
(FStar_All.failwith "Unexpected number of patterns")
end))))

# 402 "FStar.TypeChecker.Util.fst"
let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (
# 405 "FStar.TypeChecker.Util.fst"
let topt = Some (pat.FStar_Syntax_Syntax.ty)
in (
# 406 "FStar.TypeChecker.Util.fst"
let mk = (fun f -> (FStar_Syntax_Syntax.mk f topt pat.FStar_Syntax_Syntax.p))
in (
# 408 "FStar.TypeChecker.Util.fst"
let pat_as_arg = (fun _67_586 -> (match (_67_586) with
| (p, i) -> begin
(
# 409 "FStar.TypeChecker.Util.fst"
let _67_589 = (decorated_pattern_as_term p)
in (match (_67_589) with
| (vars, te) -> begin
(let _156_216 = (let _156_215 = (FStar_Syntax_Syntax.as_implicit i)
in (te, _156_215))
in (vars, _156_216))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_67_591) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _156_217 = (mk (FStar_Syntax_Syntax.Tm_constant (c)))
in ([], _156_217))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(let _156_218 = (mk (FStar_Syntax_Syntax.Tm_name (x)))
in ((x)::[], _156_218))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 423 "FStar.TypeChecker.Util.fst"
let _67_604 = (let _156_219 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _156_219 FStar_List.unzip))
in (match (_67_604) with
| (vars, args) -> begin
(
# 424 "FStar.TypeChecker.Util.fst"
let vars = (FStar_List.flatten vars)
in (let _156_223 = (let _156_222 = (let _156_221 = (let _156_220 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (_156_220, args))
in FStar_Syntax_Syntax.Tm_app (_156_221))
in (mk _156_222))
in (vars, _156_223)))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
([], e)
end)))))

# 428 "FStar.TypeChecker.Util.fst"
let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (
# 435 "FStar.TypeChecker.Util.fst"
let _67_628 = (match (c.FStar_Syntax_Syntax.effect_args) with
| (wp, _67_617)::(wlp, _67_613)::[] -> begin
(wp, wlp)
end
| _67_621 -> begin
(let _156_229 = (let _156_228 = (let _156_227 = (FStar_List.map (fun _67_625 -> (match (_67_625) with
| (x, _67_624) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right _156_227 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str _156_228))
in (FStar_All.failwith _156_229))
end)
in (match (_67_628) with
| (wp, wlp) -> begin
(c.FStar_Syntax_Syntax.result_typ, wp, wlp)
end)))

# 439 "FStar.TypeChecker.Util.fst"
let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (
# 442 "FStar.TypeChecker.Util.fst"
let _67_636 = (destruct_comp c)
in (match (_67_636) with
| (_67_633, wp, wlp) -> begin
(let _156_251 = (let _156_250 = (let _156_246 = (lift c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _156_246))
in (let _156_249 = (let _156_248 = (let _156_247 = (lift c.FStar_Syntax_Syntax.result_typ wlp)
in (FStar_Syntax_Syntax.as_arg _156_247))
in (_156_248)::[])
in (_156_250)::_156_249))
in {FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _156_251; FStar_Syntax_Syntax.flags = []})
end)))

# 446 "FStar.TypeChecker.Util.fst"
let norm_eff_name : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (
# 449 "FStar.TypeChecker.Util.fst"
let cache = (FStar_Util.smap_create 20)
in (fun env l -> (
# 451 "FStar.TypeChecker.Util.fst"
let rec find = (fun l -> (match ((FStar_TypeChecker_Env.lookup_effect_abbrev env FStar_Syntax_Syntax.U_unknown l)) with
| None -> begin
None
end
| Some (_67_644, c) -> begin
(
# 455 "FStar.TypeChecker.Util.fst"
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
# 459 "FStar.TypeChecker.Util.fst"
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
# 464 "FStar.TypeChecker.Util.fst"
let _67_658 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))

# 467 "FStar.TypeChecker.Util.fst"
let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (
# 471 "FStar.TypeChecker.Util.fst"
let _67_669 = (let _156_265 = (norm_eff_name env l1)
in (let _156_264 = (norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _156_265 _156_264)))
in (match (_67_669) with
| (m, _67_666, _67_668) -> begin
m
end)))

# 472 "FStar.TypeChecker.Util.fst"
let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> if ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2)) then begin
FStar_Syntax_Const.effect_Tot_lid
end else begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)

# 478 "FStar.TypeChecker.Util.fst"
let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)) = (fun env c1 c2 -> (
# 481 "FStar.TypeChecker.Util.fst"
let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (
# 482 "FStar.TypeChecker.Util.fst"
let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (
# 483 "FStar.TypeChecker.Util.fst"
let _67_681 = (FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (_67_681) with
| (m, lift1, lift2) -> begin
(
# 484 "FStar.TypeChecker.Util.fst"
let m1 = (lift_comp c1 m lift1)
in (
# 485 "FStar.TypeChecker.Util.fst"
let m2 = (lift_comp c2 m lift2)
in (
# 486 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (
# 487 "FStar.TypeChecker.Util.fst"
let _67_687 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (_67_687) with
| (a, kwp) -> begin
(let _156_279 = (destruct_comp m1)
in (let _156_278 = (destruct_comp m2)
in ((md, a, kwp), _156_279, _156_278)))
end)))))
end)))))

# 488 "FStar.TypeChecker.Util.fst"
let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (
# 491 "FStar.TypeChecker.Util.fst"
let l = (norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)))

# 492 "FStar.TypeChecker.Util.fst"
let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (
# 495 "FStar.TypeChecker.Util.fst"
let l = (norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid))))

# 497 "FStar.TypeChecker.Util.fst"
let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md result wp wlp flags -> (let _156_302 = (let _156_301 = (let _156_300 = (FStar_Syntax_Syntax.as_arg wp)
in (let _156_299 = (let _156_298 = (FStar_Syntax_Syntax.as_arg wlp)
in (_156_298)::[])
in (_156_300)::_156_299))
in {FStar_Syntax_Syntax.effect_name = md.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = _156_301; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp _156_302)))

# 503 "FStar.TypeChecker.Util.fst"
let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (
# 506 "FStar.TypeChecker.Util.fst"
let _67_701 = lc
in (let _156_309 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _67_701.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _156_309; FStar_Syntax_Syntax.cflags = _67_701.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _67_703 -> (match (()) with
| () -> begin
(let _156_308 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _156_308))
end))})))

# 507 "FStar.TypeChecker.Util.fst"
let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _156_312 = (FStar_Syntax_Subst.compress t)
in _156_312.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_67_706) -> begin
true
end
| _67_709 -> begin
false
end))

# 511 "FStar.TypeChecker.Util.fst"
let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v -> (
# 515 "FStar.TypeChecker.Util.fst"
let c = if (let _156_319 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation _156_319)) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(
# 518 "FStar.TypeChecker.Util.fst"
let m = (let _156_320 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must _156_320))
in (
# 519 "FStar.TypeChecker.Util.fst"
let _67_716 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_67_716) with
| (a, kwp) -> begin
(
# 520 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 521 "FStar.TypeChecker.Util.fst"
let wp = (let _156_328 = (let _156_327 = (let _156_322 = (let _156_321 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_156_321)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _156_322 env m m.FStar_Syntax_Syntax.ret))
in (let _156_326 = (let _156_325 = (FStar_Syntax_Syntax.as_arg t)
in (let _156_324 = (let _156_323 = (FStar_Syntax_Syntax.as_arg v)
in (_156_323)::[])
in (_156_325)::_156_324))
in (FStar_Syntax_Syntax.mk_Tm_app _156_327 _156_326 (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _156_328))
in (
# 522 "FStar.TypeChecker.Util.fst"
let wlp = wp
in (mk_comp m t wp wlp ((FStar_Syntax_Syntax.RETURN)::[])))))
end)))
end
in (
# 524 "FStar.TypeChecker.Util.fst"
let _67_721 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return"))) then begin
(let _156_331 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _156_330 = (FStar_Syntax_Print.term_to_string v)
in (let _156_329 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _156_331 _156_330 _156_329))))
end else begin
()
end
in c)))

# 527 "FStar.TypeChecker.Util.fst"
let bind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun env e1opt lc1 _67_728 -> (match (_67_728) with
| (b, lc2) -> begin
(
# 530 "FStar.TypeChecker.Util.fst"
let _67_736 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(
# 532 "FStar.TypeChecker.Util.fst"
let bstr = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _156_342 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (let _156_341 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _156_340 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" _156_342 _156_341 bstr _156_340)))))
end else begin
()
end
in (
# 538 "FStar.TypeChecker.Util.fst"
let bind_it = (fun _67_739 -> (match (()) with
| () -> begin
(
# 539 "FStar.TypeChecker.Util.fst"
let c1 = (lc1.FStar_Syntax_Syntax.comp ())
in (
# 540 "FStar.TypeChecker.Util.fst"
let c2 = (lc2.FStar_Syntax_Syntax.comp ())
in (
# 541 "FStar.TypeChecker.Util.fst"
let _67_745 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _156_349 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _156_348 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _156_347 = (FStar_Syntax_Print.comp_to_string c1)
in (let _156_346 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (let _156_345 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" _156_349 _156_348 _156_347 _156_346 _156_345))))))
end else begin
()
end
in (
# 550 "FStar.TypeChecker.Util.fst"
let try_simplify = (fun _67_748 -> (match (()) with
| () -> begin
(
# 551 "FStar.TypeChecker.Util.fst"
let aux = (fun _67_750 -> (match (()) with
| () -> begin
if (FStar_Syntax_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some ((c2, "trivial no binder"))
end
| Some (_67_753) -> begin
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
# 562 "FStar.TypeChecker.Util.fst"
let subst_c2 = (fun reason -> (match ((e1opt, b)) with
| (Some (e), Some (x)) -> begin
(let _156_357 = (let _156_356 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT ((x, e)))::[]) c2)
in (_156_356, reason))
in Some (_156_357))
end
| _67_763 -> begin
(aux ())
end))
in if ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2)) then begin
(subst_c2 "both total")
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2)) then begin
(let _156_359 = (let _156_358 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in (_156_358, "both gtot"))
in Some (_156_359))
end else begin
(match ((e1opt, b)) with
| (Some (e), Some (x)) -> begin
if ((FStar_Syntax_Util.is_total_comp c1) && (not ((FStar_Syntax_Syntax.is_null_bv x)))) then begin
(subst_c2 "substituted e")
end else begin
(aux ())
end
end
| _67_770 -> begin
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
# 583 "FStar.TypeChecker.Util.fst"
let _67_788 = (lift_and_destruct env c1 c2)
in (match (_67_788) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(
# 584 "FStar.TypeChecker.Util.fst"
let bs = (match (b) with
| None -> begin
(let _156_360 = (FStar_Syntax_Syntax.null_binder t1)
in (_156_360)::[])
end
| Some (x) -> begin
(let _156_361 = (FStar_Syntax_Syntax.mk_binder x)
in (_156_361)::[])
end)
in (
# 587 "FStar.TypeChecker.Util.fst"
let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp None))
in (
# 588 "FStar.TypeChecker.Util.fst"
let wp_args = (let _156_376 = (FStar_Syntax_Syntax.as_arg t1)
in (let _156_375 = (let _156_374 = (FStar_Syntax_Syntax.as_arg t2)
in (let _156_373 = (let _156_372 = (FStar_Syntax_Syntax.as_arg wp1)
in (let _156_371 = (let _156_370 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _156_369 = (let _156_368 = (let _156_364 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg _156_364))
in (let _156_367 = (let _156_366 = (let _156_365 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _156_365))
in (_156_366)::[])
in (_156_368)::_156_367))
in (_156_370)::_156_369))
in (_156_372)::_156_371))
in (_156_374)::_156_373))
in (_156_376)::_156_375))
in (
# 589 "FStar.TypeChecker.Util.fst"
let wlp_args = (let _156_384 = (FStar_Syntax_Syntax.as_arg t1)
in (let _156_383 = (let _156_382 = (FStar_Syntax_Syntax.as_arg t2)
in (let _156_381 = (let _156_380 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _156_379 = (let _156_378 = (let _156_377 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _156_377))
in (_156_378)::[])
in (_156_380)::_156_379))
in (_156_382)::_156_381))
in (_156_384)::_156_383))
in (
# 590 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t2)))::[]) kwp)
in (
# 591 "FStar.TypeChecker.Util.fst"
let us = (let _156_387 = (env.FStar_TypeChecker_Env.universe_of env t1)
in (let _156_386 = (let _156_385 = (env.FStar_TypeChecker_Env.universe_of env t2)
in (_156_385)::[])
in (_156_387)::_156_386))
in (
# 592 "FStar.TypeChecker.Util.fst"
let wp = (let _156_388 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _156_388 wp_args None t2.FStar_Syntax_Syntax.pos))
in (
# 593 "FStar.TypeChecker.Util.fst"
let wlp = (let _156_389 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wlp)
in (FStar_Syntax_Syntax.mk_Tm_app _156_389 wlp_args None t2.FStar_Syntax_Syntax.pos))
in (
# 594 "FStar.TypeChecker.Util.fst"
let c = (mk_comp md t2 wp wlp [])
in c)))))))))
end))
end)))))
end))
in (let _156_390 = (join_lcomp env lc1 lc2)
in {FStar_Syntax_Syntax.eff_name = _156_390; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it})))
end))

# 599 "FStar.TypeChecker.Util.fst"
let lift_formula : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t mk_wp mk_wlp f -> (
# 602 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 603 "FStar.TypeChecker.Util.fst"
let _67_810 = (FStar_TypeChecker_Env.wp_signature env md_pure.FStar_Syntax_Syntax.mname)
in (match (_67_810) with
| (a, kwp) -> begin
(
# 604 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 605 "FStar.TypeChecker.Util.fst"
let wp = (let _156_404 = (let _156_403 = (FStar_Syntax_Syntax.as_arg t)
in (let _156_402 = (let _156_401 = (FStar_Syntax_Syntax.as_arg f)
in (_156_401)::[])
in (_156_403)::_156_402))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wp _156_404 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (
# 606 "FStar.TypeChecker.Util.fst"
let wlp = (let _156_408 = (let _156_407 = (FStar_Syntax_Syntax.as_arg t)
in (let _156_406 = (let _156_405 = (FStar_Syntax_Syntax.as_arg f)
in (_156_405)::[])
in (_156_407)::_156_406))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wlp _156_408 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (mk_comp md_pure FStar_TypeChecker_Common.t_unit wp wlp []))))
end))))

# 607 "FStar.TypeChecker.Util.fst"
let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((f, FStar_Syntax_Syntax.Meta_labeled ((reason, r, false))))) None f.FStar_Syntax_Syntax.pos))

# 610 "FStar.TypeChecker.Util.fst"
let label_opt : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _156_432 = (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)
in (FStar_All.pipe_left Prims.op_Negation _156_432)) then begin
f
end else begin
(let _156_433 = (reason ())
in (label _156_433 r f))
end
end))

# 617 "FStar.TypeChecker.Util.fst"
let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 621 "FStar.TypeChecker.Util.fst"
let _67_830 = g
in (let _156_441 = (let _156_440 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_156_440))
in {FStar_TypeChecker_Env.guard_f = _156_441; FStar_TypeChecker_Env.deferred = _67_830.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _67_830.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _67_830.FStar_TypeChecker_Env.implicits}))
end))

# 621 "FStar.TypeChecker.Util.fst"
let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(
# 625 "FStar.TypeChecker.Util.fst"
let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| _67_841 -> begin
g2
end))

# 627 "FStar.TypeChecker.Util.fst"
let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (
# 630 "FStar.TypeChecker.Util.fst"
let weaken = (fun _67_846 -> (match (()) with
| () -> begin
(
# 631 "FStar.TypeChecker.Util.fst"
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
# 637 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 638 "FStar.TypeChecker.Util.fst"
let _67_855 = (destruct_comp c)
in (match (_67_855) with
| (res_t, wp, wlp) -> begin
(
# 639 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 640 "FStar.TypeChecker.Util.fst"
let us = (let _156_454 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_156_454)::[])
in (
# 641 "FStar.TypeChecker.Util.fst"
let wp = (let _156_461 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _156_460 = (let _156_459 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _156_458 = (let _156_457 = (FStar_Syntax_Syntax.as_arg f)
in (let _156_456 = (let _156_455 = (FStar_Syntax_Syntax.as_arg wp)
in (_156_455)::[])
in (_156_457)::_156_456))
in (_156_459)::_156_458))
in (FStar_Syntax_Syntax.mk_Tm_app _156_461 _156_460 None wp.FStar_Syntax_Syntax.pos)))
in (
# 642 "FStar.TypeChecker.Util.fst"
let wlp = (let _156_468 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _156_467 = (let _156_466 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _156_465 = (let _156_464 = (FStar_Syntax_Syntax.as_arg f)
in (let _156_463 = (let _156_462 = (FStar_Syntax_Syntax.as_arg wlp)
in (_156_462)::[])
in (_156_464)::_156_463))
in (_156_466)::_156_465))
in (FStar_Syntax_Syntax.mk_Tm_app _156_468 _156_467 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp c.FStar_Syntax_Syntax.flags)))))
end)))
end
end))
end))
in (
# 644 "FStar.TypeChecker.Util.fst"
let _67_860 = lc
in {FStar_Syntax_Syntax.eff_name = _67_860.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _67_860.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _67_860.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))

# 644 "FStar.TypeChecker.Util.fst"
let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> if (FStar_TypeChecker_Rel.is_trivial g0) then begin
(lc, g0)
end else begin
(
# 650 "FStar.TypeChecker.Util.fst"
let _67_867 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _156_488 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _156_487 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _156_488 _156_487)))
end else begin
()
end
in (
# 654 "FStar.TypeChecker.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _67_2 -> (match (_67_2) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _67_873 -> begin
[]
end))))
in (
# 655 "FStar.TypeChecker.Util.fst"
let strengthen = (fun _67_876 -> (match (()) with
| () -> begin
(
# 656 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 657 "FStar.TypeChecker.Util.fst"
let g0 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (match ((FStar_TypeChecker_Rel.guard_form g0)) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 661 "FStar.TypeChecker.Util.fst"
let c = if ((FStar_Syntax_Util.is_pure_or_ghost_comp c) && (not ((FStar_Syntax_Util.is_partial_return c)))) then begin
(
# 664 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.gen_bv "strengthen_pre_x" None (FStar_Syntax_Util.comp_result c))
in (
# 665 "FStar.TypeChecker.Util.fst"
let xret = (let _156_493 = (let _156_492 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _156_492))
in (FStar_Syntax_Util.comp_set_flags _156_493 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (
# 666 "FStar.TypeChecker.Util.fst"
let lc = (bind env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), (FStar_Syntax_Util.lcomp_of_comp xret)))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (
# 670 "FStar.TypeChecker.Util.fst"
let _67_886 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _156_495 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _156_494 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _156_495 _156_494)))
end else begin
()
end
in (
# 675 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 676 "FStar.TypeChecker.Util.fst"
let _67_892 = (destruct_comp c)
in (match (_67_892) with
| (res_t, wp, wlp) -> begin
(
# 677 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 678 "FStar.TypeChecker.Util.fst"
let us = (let _156_496 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_156_496)::[])
in (
# 679 "FStar.TypeChecker.Util.fst"
let wp = (let _156_505 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assert_p)
in (let _156_504 = (let _156_503 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _156_502 = (let _156_501 = (let _156_498 = (let _156_497 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason _156_497 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _156_498))
in (let _156_500 = (let _156_499 = (FStar_Syntax_Syntax.as_arg wp)
in (_156_499)::[])
in (_156_501)::_156_500))
in (_156_503)::_156_502))
in (FStar_Syntax_Syntax.mk_Tm_app _156_505 _156_504 None wp.FStar_Syntax_Syntax.pos)))
in (
# 680 "FStar.TypeChecker.Util.fst"
let wlp = (let _156_512 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _156_511 = (let _156_510 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _156_509 = (let _156_508 = (FStar_Syntax_Syntax.as_arg f)
in (let _156_507 = (let _156_506 = (FStar_Syntax_Syntax.as_arg wlp)
in (_156_506)::[])
in (_156_508)::_156_507))
in (_156_510)::_156_509))
in (FStar_Syntax_Syntax.mk_Tm_app _156_512 _156_511 None wlp.FStar_Syntax_Syntax.pos)))
in (
# 682 "FStar.TypeChecker.Util.fst"
let _67_897 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _156_513 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _156_513))
end else begin
()
end
in (
# 686 "FStar.TypeChecker.Util.fst"
let c2 = (mk_comp md res_t wp wlp flags)
in c2))))))
end)))))
end)))
end))
in (let _156_517 = (
# 688 "FStar.TypeChecker.Util.fst"
let _67_900 = lc
in (let _156_516 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _156_515 = if ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _156_514 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _156_514))) then begin
flags
end else begin
[]
end
in {FStar_Syntax_Syntax.eff_name = _156_516; FStar_Syntax_Syntax.res_typ = _67_900.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _156_515; FStar_Syntax_Syntax.comp = strengthen})))
in (_156_517, (
# 691 "FStar.TypeChecker.Util.fst"
let _67_902 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _67_902.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _67_902.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _67_902.FStar_TypeChecker_Env.implicits}))))))
end)

# 691 "FStar.TypeChecker.Util.fst"
let record_application_site : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (
# 694 "FStar.TypeChecker.Util.fst"
let comp = (fun _67_908 -> (match (()) with
| () -> begin
(
# 695 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 696 "FStar.TypeChecker.Util.fst"
let res_t = (FStar_Syntax_Util.comp_result c)
in if (((FStar_Syntax_Util.is_trivial_wp c) || (let _156_526 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals _156_526 FStar_Syntax_Const.prims_lid))) || (FStar_Syntax_Syntax.is_teff res_t)) then begin
c
end else begin
(
# 701 "FStar.TypeChecker.Util.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (FStar_TypeChecker_Common.t_unit)))
in (
# 702 "FStar.TypeChecker.Util.fst"
let _67_916 = (strengthen_precondition (Some ((fun _67_912 -> (match (()) with
| () -> begin
"push"
end)))) env e (FStar_Syntax_Util.lcomp_of_comp c) g)
in (match (_67_916) with
| (c, _67_915) -> begin
(
# 703 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 704 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 705 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 706 "FStar.TypeChecker.Util.fst"
let us = (let _156_530 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_156_530)::[])
in (
# 707 "FStar.TypeChecker.Util.fst"
let xret = (let _156_535 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _156_534 = (let _156_533 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _156_532 = (let _156_531 = (FStar_Syntax_Syntax.as_arg xexp)
in (_156_531)::[])
in (_156_533)::_156_532))
in (FStar_Syntax_Syntax.mk_Tm_app _156_535 _156_534 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 708 "FStar.TypeChecker.Util.fst"
let xret_comp = (let _156_536 = (mk_comp md_pure res_t xret xret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _156_536))
in (
# 709 "FStar.TypeChecker.Util.fst"
let lc = (let _156_542 = (let _156_541 = (let _156_540 = (strengthen_precondition (Some ((fun _67_923 -> (match (()) with
| () -> begin
"pop"
end)))) env xexp xret_comp g)
in (FStar_All.pipe_left Prims.fst _156_540))
in (Some (x), _156_541))
in (bind env None c _156_542))
in (lc.FStar_Syntax_Syntax.comp ()))))))))
end)))
end))
end))
in (
# 711 "FStar.TypeChecker.Util.fst"
let _67_925 = lc
in {FStar_Syntax_Syntax.eff_name = _67_925.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _67_925.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _67_925.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = comp})))

# 711 "FStar.TypeChecker.Util.fst"
let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env comp res_t -> (
# 714 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 715 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 716 "FStar.TypeChecker.Util.fst"
let y = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 717 "FStar.TypeChecker.Util.fst"
let _67_935 = (let _156_550 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _156_549 = (FStar_Syntax_Syntax.bv_to_name y)
in (_156_550, _156_549)))
in (match (_67_935) with
| (xexp, yexp) -> begin
(
# 718 "FStar.TypeChecker.Util.fst"
let us = (let _156_551 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_156_551)::[])
in (
# 719 "FStar.TypeChecker.Util.fst"
let yret = (let _156_556 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _156_555 = (let _156_554 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _156_553 = (let _156_552 = (FStar_Syntax_Syntax.as_arg yexp)
in (_156_552)::[])
in (_156_554)::_156_553))
in (FStar_Syntax_Syntax.mk_Tm_app _156_556 _156_555 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 720 "FStar.TypeChecker.Util.fst"
let x_eq_y_yret = (let _156_564 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _156_563 = (let _156_562 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _156_561 = (let _156_560 = (let _156_557 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _156_557))
in (let _156_559 = (let _156_558 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_156_558)::[])
in (_156_560)::_156_559))
in (_156_562)::_156_561))
in (FStar_Syntax_Syntax.mk_Tm_app _156_564 _156_563 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 721 "FStar.TypeChecker.Util.fst"
let forall_y_x_eq_y_yret = (let _156_574 = (FStar_TypeChecker_Env.inst_effect_fun_with (FStar_List.append us us) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _156_573 = (let _156_572 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _156_571 = (let _156_570 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _156_569 = (let _156_568 = (let _156_567 = (let _156_566 = (let _156_565 = (FStar_Syntax_Syntax.mk_binder y)
in (_156_565)::[])
in (FStar_Syntax_Util.abs _156_566 x_eq_y_yret None))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _156_567))
in (_156_568)::[])
in (_156_570)::_156_569))
in (_156_572)::_156_571))
in (FStar_Syntax_Syntax.mk_Tm_app _156_574 _156_573 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 722 "FStar.TypeChecker.Util.fst"
let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (
# 723 "FStar.TypeChecker.Util.fst"
let lc = (bind env None (FStar_Syntax_Util.lcomp_of_comp comp) (Some (x), (FStar_Syntax_Util.lcomp_of_comp lc2)))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))

# 724 "FStar.TypeChecker.Util.fst"
let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (
# 727 "FStar.TypeChecker.Util.fst"
let comp = (fun _67_947 -> (match (()) with
| () -> begin
(
# 728 "FStar.TypeChecker.Util.fst"
let _67_963 = (let _156_586 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _156_585 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _156_586 _156_585)))
in (match (_67_963) with
| ((md, _67_950, _67_952), (res_t, wp_then, wlp_then), (_67_959, wp_else, wlp_else)) -> begin
(
# 729 "FStar.TypeChecker.Util.fst"
let us = (let _156_587 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_156_587)::[])
in (
# 730 "FStar.TypeChecker.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _156_607 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _156_606 = (let _156_604 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _156_603 = (let _156_602 = (FStar_Syntax_Syntax.as_arg g)
in (let _156_601 = (let _156_600 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _156_599 = (let _156_598 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_156_598)::[])
in (_156_600)::_156_599))
in (_156_602)::_156_601))
in (_156_604)::_156_603))
in (let _156_605 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _156_607 _156_606 None _156_605)))))
in (
# 731 "FStar.TypeChecker.Util.fst"
let wp = (ifthenelse md res_t guard wp_then wp_else)
in (
# 732 "FStar.TypeChecker.Util.fst"
let wlp = (ifthenelse md res_t guard wlp_then wlp_else)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(
# 734 "FStar.TypeChecker.Util.fst"
let comp = (mk_comp md res_t wp wlp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(
# 736 "FStar.TypeChecker.Util.fst"
let wp = (let _156_614 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _156_613 = (let _156_612 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _156_611 = (let _156_610 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _156_609 = (let _156_608 = (FStar_Syntax_Syntax.as_arg wp)
in (_156_608)::[])
in (_156_610)::_156_609))
in (_156_612)::_156_611))
in (FStar_Syntax_Syntax.mk_Tm_app _156_614 _156_613 None wp.FStar_Syntax_Syntax.pos)))
in (
# 737 "FStar.TypeChecker.Util.fst"
let wlp = (let _156_619 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _156_618 = (let _156_617 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _156_616 = (let _156_615 = (FStar_Syntax_Syntax.as_arg wlp)
in (_156_615)::[])
in (_156_617)::_156_616))
in (FStar_Syntax_Syntax.mk_Tm_app _156_619 _156_618 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end))))
end))
end))
in (let _156_620 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _156_620; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp})))

# 742 "FStar.TypeChecker.Util.fst"
let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (let _156_626 = (let _156_625 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid _156_625))
in (FStar_Syntax_Syntax.fvar _156_626 FStar_Syntax_Syntax.Delta_constant None)))

# 744 "FStar.TypeChecker.Util.fst"
let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (
# 747 "FStar.TypeChecker.Util.fst"
let eff = (FStar_List.fold_left (fun eff _67_985 -> (match (_67_985) with
| (_67_983, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (
# 748 "FStar.TypeChecker.Util.fst"
let bind_cases = (fun _67_988 -> (match (()) with
| () -> begin
(
# 749 "FStar.TypeChecker.Util.fst"
let us = (let _156_637 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_156_637)::[])
in (
# 750 "FStar.TypeChecker.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _156_657 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _156_656 = (let _156_654 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _156_653 = (let _156_652 = (FStar_Syntax_Syntax.as_arg g)
in (let _156_651 = (let _156_650 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _156_649 = (let _156_648 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_156_648)::[])
in (_156_650)::_156_649))
in (_156_652)::_156_651))
in (_156_654)::_156_653))
in (let _156_655 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _156_657 _156_656 None _156_655)))))
in (
# 752 "FStar.TypeChecker.Util.fst"
let default_case = (
# 753 "FStar.TypeChecker.Util.fst"
let post_k = (let _156_660 = (let _156_658 = (FStar_Syntax_Syntax.null_binder res_t)
in (_156_658)::[])
in (let _156_659 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _156_660 _156_659)))
in (
# 754 "FStar.TypeChecker.Util.fst"
let kwp = (let _156_663 = (let _156_661 = (FStar_Syntax_Syntax.null_binder post_k)
in (_156_661)::[])
in (let _156_662 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _156_663 _156_662)))
in (
# 755 "FStar.TypeChecker.Util.fst"
let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (
# 756 "FStar.TypeChecker.Util.fst"
let wp = (let _156_669 = (let _156_664 = (FStar_Syntax_Syntax.mk_binder post)
in (_156_664)::[])
in (let _156_668 = (let _156_667 = (let _156_665 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Errors.exhaustiveness_check _156_665))
in (let _156_666 = (fvar_const env FStar_Syntax_Const.false_lid)
in (FStar_All.pipe_left _156_667 _156_666)))
in (FStar_Syntax_Util.abs _156_669 _156_668 None)))
in (
# 757 "FStar.TypeChecker.Util.fst"
let wlp = (let _156_672 = (let _156_670 = (FStar_Syntax_Syntax.mk_binder post)
in (_156_670)::[])
in (let _156_671 = (fvar_const env FStar_Syntax_Const.true_lid)
in (FStar_Syntax_Util.abs _156_672 _156_671 None)))
in (
# 758 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (
# 760 "FStar.TypeChecker.Util.fst"
let comp = (FStar_List.fold_right (fun _67_1005 celse -> (match (_67_1005) with
| (g, cthen) -> begin
(
# 761 "FStar.TypeChecker.Util.fst"
let _67_1023 = (let _156_675 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _156_675 celse))
in (match (_67_1023) with
| ((md, _67_1009, _67_1011), (_67_1014, wp_then, wlp_then), (_67_1019, wp_else, wlp_else)) -> begin
(let _156_677 = (ifthenelse md res_t g wp_then wp_else)
in (let _156_676 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _156_677 _156_676 [])))
end))
end)) lcases default_case)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(add_equality_to_post_condition env comp res_t)
end else begin
(
# 765 "FStar.TypeChecker.Util.fst"
let comp = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (
# 766 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env comp.FStar_Syntax_Syntax.effect_name)
in (
# 767 "FStar.TypeChecker.Util.fst"
let _67_1031 = (destruct_comp comp)
in (match (_67_1031) with
| (_67_1028, wp, wlp) -> begin
(
# 768 "FStar.TypeChecker.Util.fst"
let wp = (let _156_684 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _156_683 = (let _156_682 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _156_681 = (let _156_680 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _156_679 = (let _156_678 = (FStar_Syntax_Syntax.as_arg wp)
in (_156_678)::[])
in (_156_680)::_156_679))
in (_156_682)::_156_681))
in (FStar_Syntax_Syntax.mk_Tm_app _156_684 _156_683 None wp.FStar_Syntax_Syntax.pos)))
in (
# 769 "FStar.TypeChecker.Util.fst"
let wlp = (let _156_689 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _156_688 = (let _156_687 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _156_686 = (let _156_685 = (FStar_Syntax_Syntax.as_arg wlp)
in (_156_685)::[])
in (_156_687)::_156_686))
in (FStar_Syntax_Syntax.mk_Tm_app _156_689 _156_688 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end))))
end))))
end))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))

# 774 "FStar.TypeChecker.Util.fst"
let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (
# 777 "FStar.TypeChecker.Util.fst"
let close = (fun _67_1038 -> (match (()) with
| () -> begin
(
# 778 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in if (FStar_Syntax_Util.is_ml_comp c) then begin
c
end else begin
(
# 781 "FStar.TypeChecker.Util.fst"
let close_wp = (fun u_res md res_t bvs wp0 -> (FStar_List.fold_right (fun x wp -> (
# 783 "FStar.TypeChecker.Util.fst"
let bs = (let _156_710 = (FStar_Syntax_Syntax.mk_binder x)
in (_156_710)::[])
in (
# 784 "FStar.TypeChecker.Util.fst"
let us = (let _156_712 = (let _156_711 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (_156_711)::[])
in (u_res)::_156_712)
in (
# 785 "FStar.TypeChecker.Util.fst"
let wp = (FStar_Syntax_Util.abs bs wp None)
in (let _156_719 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (let _156_718 = (let _156_717 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _156_716 = (let _156_715 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _156_714 = (let _156_713 = (FStar_Syntax_Syntax.as_arg wp)
in (_156_713)::[])
in (_156_715)::_156_714))
in (_156_717)::_156_716))
in (FStar_Syntax_Syntax.mk_Tm_app _156_719 _156_718 None wp0.FStar_Syntax_Syntax.pos))))))) bvs wp0))
in (
# 788 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 789 "FStar.TypeChecker.Util.fst"
let _67_1055 = (destruct_comp c)
in (match (_67_1055) with
| (t, wp, wlp) -> begin
(
# 790 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 791 "FStar.TypeChecker.Util.fst"
let u_res = (env.FStar_TypeChecker_Env.universe_of env c.FStar_Syntax_Syntax.result_typ)
in (
# 792 "FStar.TypeChecker.Util.fst"
let wp = (close_wp u_res md c.FStar_Syntax_Syntax.result_typ bvs wp)
in (
# 793 "FStar.TypeChecker.Util.fst"
let wlp = (close_wp u_res md c.FStar_Syntax_Syntax.result_typ bvs wlp)
in (mk_comp md c.FStar_Syntax_Syntax.result_typ wp wlp c.FStar_Syntax_Syntax.flags)))))
end))))
end)
end))
in (
# 795 "FStar.TypeChecker.Util.fst"
let _67_1060 = lc
in {FStar_Syntax_Syntax.eff_name = _67_1060.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _67_1060.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _67_1060.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))

# 795 "FStar.TypeChecker.Util.fst"
let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (
# 798 "FStar.TypeChecker.Util.fst"
let refine = (fun _67_1066 -> (match (()) with
| () -> begin
(
# 799 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in if (not ((is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name))) then begin
c
end else begin
if (FStar_Syntax_Util.is_partial_return c) then begin
c
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c) && (not ((FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)))) then begin
(let _156_730 = (let _156_729 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _156_728 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _156_729 _156_728)))
in (FStar_All.failwith _156_730))
end else begin
(
# 807 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 808 "FStar.TypeChecker.Util.fst"
let t = c.FStar_Syntax_Syntax.result_typ
in (
# 809 "FStar.TypeChecker.Util.fst"
let c = (FStar_Syntax_Syntax.mk_Comp c)
in (
# 810 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (
# 811 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 812 "FStar.TypeChecker.Util.fst"
let ret = (let _156_732 = (let _156_731 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _156_731 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _156_732))
in (
# 813 "FStar.TypeChecker.Util.fst"
let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (
# 814 "FStar.TypeChecker.Util.fst"
let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (
# 816 "FStar.TypeChecker.Util.fst"
let c = (let _156_734 = (let _156_733 = (bind env None (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), eq_ret))
in (_156_733.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _156_734 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
in c)))))))))
end
end
end)
end))
in (
# 819 "FStar.TypeChecker.Util.fst"
let flags = if (((not ((FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)) && (not ((FStar_Syntax_Util.is_lcomp_partial_return lc)))) then begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_Syntax_Syntax.cflags
end else begin
lc.FStar_Syntax_Syntax.cflags
end
in (
# 825 "FStar.TypeChecker.Util.fst"
let _67_1078 = lc
in {FStar_Syntax_Syntax.eff_name = _67_1078.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _67_1078.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))

# 825 "FStar.TypeChecker.Util.fst"
let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (match ((FStar_TypeChecker_Rel.sub_comp env c c')) with
| None -> begin
(let _156_746 = (let _156_745 = (let _156_744 = (FStar_TypeChecker_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _156_743 = (FStar_TypeChecker_Env.get_range env)
in (_156_744, _156_743)))
in FStar_Syntax_Syntax.Error (_156_745))
in (Prims.raise _156_746))
end
| Some (g) -> begin
(e, c', g)
end))

# 831 "FStar.TypeChecker.Util.fst"
let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match ((let _156_755 = (FStar_Syntax_Subst.compress t)
in _156_755.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_67_1092) -> begin
(match ((let _156_756 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _156_756.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid) -> begin
(
# 838 "FStar.TypeChecker.Util.fst"
let _67_1096 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (
# 839 "FStar.TypeChecker.Util.fst"
let b2t = (let _156_757 = (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar _156_757 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (
# 840 "FStar.TypeChecker.Util.fst"
let lc = (let _156_760 = (let _156_759 = (let _156_758 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _156_758))
in (None, _156_759))
in (bind env (Some (e)) lc _156_760))
in (
# 841 "FStar.TypeChecker.Util.fst"
let e = (let _156_762 = (let _156_761 = (FStar_Syntax_Syntax.as_arg e)
in (_156_761)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _156_762 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (e, lc)))))
end
| _67_1102 -> begin
(e, lc)
end)
end
| _67_1104 -> begin
(e, lc)
end))

# 846 "FStar.TypeChecker.Util.fst"
let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (
# 849 "FStar.TypeChecker.Util.fst"
let gopt = if env.FStar_TypeChecker_Env.use_eq then begin
(let _156_771 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in (_156_771, false))
end else begin
(let _156_772 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in (_156_772, true))
end
in (match (gopt) with
| (None, _67_1112) -> begin
(FStar_TypeChecker_Rel.subtype_fail env lc.FStar_Syntax_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(match ((FStar_TypeChecker_Rel.guard_form g)) with
| FStar_TypeChecker_Common.Trivial -> begin
(
# 857 "FStar.TypeChecker.Util.fst"
let lc = (
# 857 "FStar.TypeChecker.Util.fst"
let _67_1119 = lc
in {FStar_Syntax_Syntax.eff_name = _67_1119.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _67_1119.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _67_1119.FStar_Syntax_Syntax.comp})
in (e, lc, g))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 861 "FStar.TypeChecker.Util.fst"
let g = (
# 861 "FStar.TypeChecker.Util.fst"
let _67_1124 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _67_1124.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _67_1124.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _67_1124.FStar_TypeChecker_Env.implicits})
in (
# 862 "FStar.TypeChecker.Util.fst"
let strengthen = (fun _67_1128 -> (match (()) with
| () -> begin
(
# 864 "FStar.TypeChecker.Util.fst"
let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (match ((let _156_775 = (FStar_Syntax_Subst.compress f)
in _156_775.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_67_1131, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _67_1137; FStar_Syntax_Syntax.pos = _67_1135; FStar_Syntax_Syntax.vars = _67_1133}, _67_1142) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
(
# 868 "FStar.TypeChecker.Util.fst"
let lc = (
# 868 "FStar.TypeChecker.Util.fst"
let _67_1145 = lc
in {FStar_Syntax_Syntax.eff_name = _67_1145.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _67_1145.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _67_1145.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| _67_1149 -> begin
(
# 872 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 873 "FStar.TypeChecker.Util.fst"
let _67_1151 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _156_779 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _156_778 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _156_777 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _156_776 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _156_779 _156_778 _156_777 _156_776)))))
end else begin
()
end
in (
# 880 "FStar.TypeChecker.Util.fst"
let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 881 "FStar.TypeChecker.Util.fst"
let _67_1156 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_67_1156) with
| (a, kwp) -> begin
(
# 882 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 883 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env ct.FStar_Syntax_Syntax.effect_name)
in (
# 884 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (
# 885 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 886 "FStar.TypeChecker.Util.fst"
let us = (let _156_780 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_156_780)::[])
in (
# 887 "FStar.TypeChecker.Util.fst"
let wp = (let _156_785 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ret)
in (let _156_784 = (let _156_783 = (FStar_Syntax_Syntax.as_arg t)
in (let _156_782 = (let _156_781 = (FStar_Syntax_Syntax.as_arg xexp)
in (_156_781)::[])
in (_156_783)::_156_782))
in (FStar_Syntax_Syntax.mk_Tm_app _156_785 _156_784 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)))
in (
# 888 "FStar.TypeChecker.Util.fst"
let cret = (let _156_786 = (mk_comp md t wp wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _156_786))
in (
# 889 "FStar.TypeChecker.Util.fst"
let guard = if apply_guard then begin
(let _156_788 = (let _156_787 = (FStar_Syntax_Syntax.as_arg xexp)
in (_156_787)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _156_788 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end else begin
f
end
in (
# 890 "FStar.TypeChecker.Util.fst"
let _67_1167 = (let _156_796 = (FStar_All.pipe_left (fun _156_793 -> Some (_156_793)) (FStar_TypeChecker_Errors.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _156_795 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _156_794 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _156_796 _156_795 e cret _156_794))))
in (match (_67_1167) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(
# 894 "FStar.TypeChecker.Util.fst"
let x = (
# 894 "FStar.TypeChecker.Util.fst"
let _67_1168 = x
in {FStar_Syntax_Syntax.ppname = _67_1168.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _67_1168.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (
# 895 "FStar.TypeChecker.Util.fst"
let c = (let _156_798 = (let _156_797 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _156_797))
in (bind env (Some (e)) _156_798 (Some (x), eq_ret)))
in (
# 896 "FStar.TypeChecker.Util.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 897 "FStar.TypeChecker.Util.fst"
let _67_1173 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _156_799 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _156_799))
end else begin
()
end
in c))))
end))))))))))
end)))))
end))
end))
in (
# 900 "FStar.TypeChecker.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _67_3 -> (match (_67_3) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _67_1179 -> begin
[]
end))))
in (
# 901 "FStar.TypeChecker.Util.fst"
let lc = (
# 901 "FStar.TypeChecker.Util.fst"
let _67_1181 = lc
in (let _156_801 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _156_801; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (
# 902 "FStar.TypeChecker.Util.fst"
let g = (
# 902 "FStar.TypeChecker.Util.fst"
let _67_1184 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _67_1184.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _67_1184.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _67_1184.FStar_TypeChecker_Env.implicits})
in (e, lc, g))))))
end)
end)))

# 903 "FStar.TypeChecker.Util.fst"
let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (
# 906 "FStar.TypeChecker.Util.fst"
let mk_post_type = (fun res_t ens -> (
# 907 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _156_813 = (let _156_812 = (let _156_811 = (let _156_810 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _156_810))
in (_156_811)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _156_812 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _156_813))))
in (
# 909 "FStar.TypeChecker.Util.fst"
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
| (req, _67_1212)::(ens, _67_1207)::_67_1204 -> begin
(let _156_819 = (let _156_816 = (norm req)
in Some (_156_816))
in (let _156_818 = (let _156_817 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _156_817))
in (_156_819, _156_818)))
end
| _67_1216 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 923 "FStar.TypeChecker.Util.fst"
let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (wp, _67_1227)::(wlp, _67_1222)::_67_1219 -> begin
(
# 926 "FStar.TypeChecker.Util.fst"
let _67_1233 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (_67_1233) with
| (us_r, _67_1232) -> begin
(
# 927 "FStar.TypeChecker.Util.fst"
let _67_1237 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (_67_1237) with
| (us_e, _67_1236) -> begin
(
# 928 "FStar.TypeChecker.Util.fst"
let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (
# 929 "FStar.TypeChecker.Util.fst"
let as_req = (let _156_821 = (let _156_820 = (FStar_Ident.set_lid_range FStar_Syntax_Const.as_requires r)
in (FStar_Syntax_Syntax.fvar _156_820 FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _156_821 us_r))
in (
# 930 "FStar.TypeChecker.Util.fst"
let as_ens = (let _156_823 = (let _156_822 = (FStar_Ident.set_lid_range FStar_Syntax_Const.as_ensures r)
in (FStar_Syntax_Syntax.fvar _156_822 FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _156_823 us_e))
in (
# 931 "FStar.TypeChecker.Util.fst"
let req = (let _156_826 = (let _156_825 = (let _156_824 = (FStar_Syntax_Syntax.as_arg wp)
in (_156_824)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.imp_tag)))::_156_825)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _156_826 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 932 "FStar.TypeChecker.Util.fst"
let ens = (let _156_829 = (let _156_828 = (let _156_827 = (FStar_Syntax_Syntax.as_arg wlp)
in (_156_827)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.imp_tag)))::_156_828)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _156_829 None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _156_833 = (let _156_830 = (norm req)
in Some (_156_830))
in (let _156_832 = (let _156_831 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm _156_831))
in (_156_833, _156_832))))))))
end))
end))
end
| _67_1244 -> begin
(FStar_All.failwith "Impossible")
end))
end
end)
end)))

# 937 "FStar.TypeChecker.Util.fst"
let maybe_instantiate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (
# 943 "FStar.TypeChecker.Util.fst"
let torig = (FStar_Syntax_Subst.compress t)
in if (not (env.FStar_TypeChecker_Env.instantiate_imp)) then begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end else begin
(match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 948 "FStar.TypeChecker.Util.fst"
let _67_1255 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_67_1255) with
| (bs, c) -> begin
(
# 949 "FStar.TypeChecker.Util.fst"
let rec aux = (fun subst _67_4 -> (match (_67_4) with
| (x, Some (FStar_Syntax_Syntax.Implicit (dot)))::rest -> begin
(
# 951 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 952 "FStar.TypeChecker.Util.fst"
let _67_1271 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t)
in (match (_67_1271) with
| (v, _67_1269, g) -> begin
(
# 953 "FStar.TypeChecker.Util.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, v)))::subst
in (
# 954 "FStar.TypeChecker.Util.fst"
let _67_1277 = (aux subst rest)
in (match (_67_1277) with
| (args, bs, subst, g') -> begin
(let _156_844 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((v, Some (FStar_Syntax_Syntax.Implicit (dot))))::args, bs, subst, _156_844))
end)))
end)))
end
| bs -> begin
([], bs, subst, FStar_TypeChecker_Rel.trivial_guard)
end))
in (
# 958 "FStar.TypeChecker.Util.fst"
let _67_1283 = (aux [] bs)
in (match (_67_1283) with
| (args, bs, subst, guard) -> begin
(match ((args, bs)) with
| ([], _67_1286) -> begin
(e, torig, guard)
end
| (_67_1289, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end
| _67_1293 -> begin
(
# 969 "FStar.TypeChecker.Util.fst"
let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _67_1296 -> begin
(FStar_Syntax_Util.arrow bs c)
end)
in (
# 972 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.subst subst t)
in (
# 973 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk_Tm_app e args (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (e, t, guard))))
end)
end)))
end))
end
| _67_1301 -> begin
(e, t, FStar_TypeChecker_Rel.trivial_guard)
end)
end))

# 977 "FStar.TypeChecker.Util.fst"
let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(
# 985 "FStar.TypeChecker.Util.fst"
let s = (let _156_850 = (let _156_849 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _156_849))
in (FStar_All.pipe_right _156_850 FStar_Util.set_elements))
in (
# 986 "FStar.TypeChecker.Util.fst"
let r = (let _156_851 = (FStar_TypeChecker_Env.get_range env)
in Some (_156_851))
in (
# 987 "FStar.TypeChecker.Util.fst"
let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (
# 988 "FStar.TypeChecker.Util.fst"
let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (
# 989 "FStar.TypeChecker.Util.fst"
let _67_1308 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _156_856 = (let _156_853 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _156_853))
in (let _156_855 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _156_854 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _156_856 _156_855 _156_854))))
end else begin
()
end
in (
# 991 "FStar.TypeChecker.Util.fst"
let _67_1310 = (FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))))
in u_name))))))
in u_names)))
end)

# 993 "FStar.TypeChecker.Util.fst"
let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t -> (
# 996 "FStar.TypeChecker.Util.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (
# 997 "FStar.TypeChecker.Util.fst"
let univs = (FStar_Syntax_Free.univs t)
in (
# 998 "FStar.TypeChecker.Util.fst"
let _67_1318 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _156_865 = (let _156_864 = (let _156_863 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _156_863 (FStar_List.map (fun u -> (let _156_862 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _156_862 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _156_864 (FStar_String.concat ", ")))
in (FStar_Util.print1 "univs to gen : %s\n" _156_865))
end else begin
()
end
in (
# 1002 "FStar.TypeChecker.Util.fst"
let gen = (gen_univs env univs)
in (
# 1003 "FStar.TypeChecker.Util.fst"
let _67_1321 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _156_866 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _156_866))
end else begin
()
end
in (
# 1005 "FStar.TypeChecker.Util.fst"
let ts = (FStar_Syntax_Subst.close_univ_vars gen t)
in (gen, ts))))))))

# 1006 "FStar.TypeChecker.Util.fst"
let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> if (let _156_872 = (FStar_Util.for_all (fun _67_1329 -> (match (_67_1329) with
| (_67_1327, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _156_872)) then begin
None
end else begin
(
# 1012 "FStar.TypeChecker.Util.fst"
let norm = (fun c -> (
# 1013 "FStar.TypeChecker.Util.fst"
let _67_1332 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _156_875 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _156_875))
end else begin
()
end
in (
# 1015 "FStar.TypeChecker.Util.fst"
let c = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.Eta)::[]) env c)
end else begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env c)
end
in (
# 1018 "FStar.TypeChecker.Util.fst"
let _67_1335 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _156_876 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _156_876))
end else begin
()
end
in c))))
in (
# 1021 "FStar.TypeChecker.Util.fst"
let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (
# 1022 "FStar.TypeChecker.Util.fst"
let gen_uvars = (fun uvs -> (let _156_879 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _156_879 FStar_Util.set_elements)))
in (
# 1023 "FStar.TypeChecker.Util.fst"
let _67_1352 = (let _156_881 = (FStar_All.pipe_right ecs (FStar_List.map (fun _67_1342 -> (match (_67_1342) with
| (e, c) -> begin
(
# 1024 "FStar.TypeChecker.Util.fst"
let t = (FStar_All.pipe_right (FStar_Syntax_Util.comp_result c) FStar_Syntax_Subst.compress)
in (
# 1025 "FStar.TypeChecker.Util.fst"
let c = (norm c)
in (
# 1026 "FStar.TypeChecker.Util.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (
# 1027 "FStar.TypeChecker.Util.fst"
let t = ct.FStar_Syntax_Syntax.result_typ
in (
# 1028 "FStar.TypeChecker.Util.fst"
let univs = (FStar_Syntax_Free.univs t)
in (
# 1029 "FStar.TypeChecker.Util.fst"
let uvt = (FStar_Syntax_Free.uvars t)
in (
# 1030 "FStar.TypeChecker.Util.fst"
let uvs = (gen_uvars uvt)
in (univs, (uvs, e, c)))))))))
end))))
in (FStar_All.pipe_right _156_881 FStar_List.unzip))
in (match (_67_1352) with
| (univs, uvars) -> begin
(
# 1033 "FStar.TypeChecker.Util.fst"
let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (
# 1034 "FStar.TypeChecker.Util.fst"
let gen_univs = (gen_univs env univs)
in (
# 1035 "FStar.TypeChecker.Util.fst"
let _67_1356 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end else begin
()
end
in (
# 1037 "FStar.TypeChecker.Util.fst"
let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _67_1361 -> (match (_67_1361) with
| (uvs, e, c) -> begin
(
# 1038 "FStar.TypeChecker.Util.fst"
let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _67_1364 -> (match (_67_1364) with
| (u, k) -> begin
(match ((FStar_Unionfind.find u)) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(a, Some (FStar_Syntax_Syntax.imp_tag))
end
| FStar_Syntax_Syntax.Fixed (_67_1398) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _67_1401 -> begin
(
# 1044 "FStar.TypeChecker.Util.fst"
let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (
# 1045 "FStar.TypeChecker.Util.fst"
let _67_1405 = (FStar_Syntax_Util.arrow_formals k)
in (match (_67_1405) with
| (bs, kres) -> begin
(
# 1046 "FStar.TypeChecker.Util.fst"
let a = (let _156_887 = (let _156_886 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _156_885 -> Some (_156_885)) _156_886))
in (FStar_Syntax_Syntax.new_bv _156_887 kres))
in (
# 1047 "FStar.TypeChecker.Util.fst"
let t = (let _156_891 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _156_890 = (let _156_889 = (let _156_888 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _156_888))
in Some (_156_889))
in (FStar_Syntax_Util.abs bs _156_891 _156_890)))
in (
# 1048 "FStar.TypeChecker.Util.fst"
let _67_1408 = (FStar_Syntax_Util.set_uvar u t)
in (a, Some (FStar_Syntax_Syntax.imp_tag)))))
end)))
end)
end))))
in (
# 1052 "FStar.TypeChecker.Util.fst"
let _67_1432 = (match (tvars) with
| [] -> begin
(e, c)
end
| _67_1413 -> begin
(
# 1058 "FStar.TypeChecker.Util.fst"
let _67_1416 = (e, c)
in (match (_67_1416) with
| (e0, c0) -> begin
(
# 1059 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.BetaUVars)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::[]) env c)
in (
# 1060 "FStar.TypeChecker.Util.fst"
let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.BetaUVars)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::[]) env e)
in (
# 1062 "FStar.TypeChecker.Util.fst"
let t = (match ((let _156_892 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _156_892.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(
# 1064 "FStar.TypeChecker.Util.fst"
let _67_1425 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (_67_1425) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| _67_1427 -> begin
(FStar_Syntax_Util.arrow tvars c)
end)
in (
# 1069 "FStar.TypeChecker.Util.fst"
let e' = (FStar_Syntax_Util.abs tvars e None)
in (let _156_893 = (FStar_Syntax_Syntax.mk_Total t)
in (e', _156_893))))))
end))
end)
in (match (_67_1432) with
| (e, c) -> begin
(gen_univs, e, c)
end)))
end))))
in Some (ecs)))))
end)))))
end)

# 1072 "FStar.TypeChecker.Util.fst"
let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> (
# 1075 "FStar.TypeChecker.Util.fst"
let _67_1442 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _156_900 = (let _156_899 = (FStar_List.map (fun _67_1441 -> (match (_67_1441) with
| (lb, _67_1438, _67_1440) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _156_899 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _156_900))
end else begin
()
end
in (match ((let _156_902 = (FStar_All.pipe_right lecs (FStar_List.map (fun _67_1448 -> (match (_67_1448) with
| (_67_1445, e, c) -> begin
(e, c)
end))))
in (gen env _156_902))) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun _67_1453 -> (match (_67_1453) with
| (l, t, c) -> begin
(l, [], t, c)
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _67_1461 _67_1465 -> (match ((_67_1461, _67_1465)) with
| ((l, _67_1458, _67_1460), (us, e, c)) -> begin
(
# 1082 "FStar.TypeChecker.Util.fst"
let _67_1466 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _156_908 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _156_907 = (FStar_Syntax_Print.lbname_to_string l)
in (let _156_906 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.print3 "(%s) Generalized %s to %s\n" _156_908 _156_907 _156_906))))
end else begin
()
end
in (l, us, e, c))
end)) lecs ecs)
end)))

# 1087 "FStar.TypeChecker.Util.fst"
let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (
# 1096 "FStar.TypeChecker.Util.fst"
let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (
# 1097 "FStar.TypeChecker.Util.fst"
let check = (fun env t1 t2 -> if env.FStar_TypeChecker_Env.use_eq then begin
(FStar_TypeChecker_Rel.try_teq env t1 t2)
end else begin
(match ((FStar_TypeChecker_Rel.try_subtype env t1 t2)) with
| None -> begin
None
end
| Some (f) -> begin
(let _156_924 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _156_923 -> Some (_156_923)) _156_924))
end)
end)
in (
# 1103 "FStar.TypeChecker.Util.fst"
let is_var = (fun e -> (match ((let _156_927 = (FStar_Syntax_Subst.compress e)
in _156_927.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (_67_1483) -> begin
true
end
| _67_1486 -> begin
false
end))
in (
# 1106 "FStar.TypeChecker.Util.fst"
let decorate = (fun e t -> (
# 1107 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((
# 1109 "FStar.TypeChecker.Util.fst"
let _67_1493 = x
in {FStar_Syntax_Syntax.ppname = _67_1493.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _67_1493.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| _67_1496 -> begin
(
# 1110 "FStar.TypeChecker.Util.fst"
let _67_1497 = e
in (let _156_932 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _67_1497.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _156_932; FStar_Syntax_Syntax.pos = _67_1497.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _67_1497.FStar_Syntax_Syntax.vars}))
end)))
in (
# 1111 "FStar.TypeChecker.Util.fst"
let env = (
# 1111 "FStar.TypeChecker.Util.fst"
let _67_1499 = env
in (let _156_933 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _67_1499.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _67_1499.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _67_1499.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _67_1499.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _67_1499.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _67_1499.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _67_1499.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _67_1499.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _67_1499.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _67_1499.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _67_1499.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _67_1499.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _67_1499.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _67_1499.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _67_1499.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _156_933; FStar_TypeChecker_Env.is_iface = _67_1499.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _67_1499.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _67_1499.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _67_1499.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _67_1499.FStar_TypeChecker_Env.use_bv_sorts}))
in (match ((check env t1 t2)) with
| None -> begin
(let _156_937 = (let _156_936 = (let _156_935 = (FStar_TypeChecker_Errors.expected_expression_of_type env t2 e t1)
in (let _156_934 = (FStar_TypeChecker_Env.get_range env)
in (_156_935, _156_934)))
in FStar_Syntax_Syntax.Error (_156_936))
in (Prims.raise _156_937))
end
| Some (g) -> begin
(
# 1115 "FStar.TypeChecker.Util.fst"
let _67_1505 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _156_938 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _156_938))
end else begin
()
end
in (let _156_939 = (decorate e t2)
in (_156_939, g)))
end)))))))

# 1117 "FStar.TypeChecker.Util.fst"
let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (
# 1121 "FStar.TypeChecker.Util.fst"
let discharge = (fun g -> (
# 1122 "FStar.TypeChecker.Util.fst"
let _67_1512 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (
# 1124 "FStar.TypeChecker.Util.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _156_949 = (discharge g)
in (let _156_948 = (lc.FStar_Syntax_Syntax.comp ())
in (_156_949, _156_948)))
end else begin
(
# 1127 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 1128 "FStar.TypeChecker.Util.fst"
let steps = (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.DeltaComp)::[]
in (
# 1129 "FStar.TypeChecker.Util.fst"
let c = (let _156_950 = (FStar_TypeChecker_Normalize.normalize_comp steps env c)
in (FStar_All.pipe_right _156_950 FStar_Syntax_Util.comp_to_comp_typ))
in (
# 1130 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 1131 "FStar.TypeChecker.Util.fst"
let _67_1523 = (destruct_comp c)
in (match (_67_1523) with
| (t, wp, _67_1522) -> begin
(
# 1132 "FStar.TypeChecker.Util.fst"
let vc = (let _156_958 = (let _156_952 = (let _156_951 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_156_951)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _156_952 env md md.FStar_Syntax_Syntax.trivial))
in (let _156_957 = (let _156_955 = (FStar_Syntax_Syntax.as_arg t)
in (let _156_954 = (let _156_953 = (FStar_Syntax_Syntax.as_arg wp)
in (_156_953)::[])
in (_156_955)::_156_954))
in (let _156_956 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk_Tm_app _156_958 _156_957 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _156_956))))
in (
# 1133 "FStar.TypeChecker.Util.fst"
let _67_1525 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _156_959 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _156_959))
end else begin
()
end
in (
# 1135 "FStar.TypeChecker.Util.fst"
let g = (let _156_960 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _156_960))
in (let _156_962 = (discharge g)
in (let _156_961 = (FStar_Syntax_Syntax.mk_Comp c)
in (_156_962, _156_961))))))
end))))))
end)))

# 1136 "FStar.TypeChecker.Util.fst"
let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (
# 1142 "FStar.TypeChecker.Util.fst"
let short_bin_op = (fun f _67_5 -> (match (_67_5) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (fst, _67_1536)::[] -> begin
(f fst)
end
| _67_1540 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (
# 1147 "FStar.TypeChecker.Util.fst"
let op_and_e = (fun e -> (let _156_983 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _156_983 (fun _156_982 -> FStar_TypeChecker_Common.NonTrivial (_156_982)))))
in (
# 1148 "FStar.TypeChecker.Util.fst"
let op_or_e = (fun e -> (let _156_988 = (let _156_986 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _156_986))
in (FStar_All.pipe_right _156_988 (fun _156_987 -> FStar_TypeChecker_Common.NonTrivial (_156_987)))))
in (
# 1149 "FStar.TypeChecker.Util.fst"
let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _156_991 -> FStar_TypeChecker_Common.NonTrivial (_156_991))))
in (
# 1150 "FStar.TypeChecker.Util.fst"
let op_or_t = (fun t -> (let _156_995 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _156_995 (fun _156_994 -> FStar_TypeChecker_Common.NonTrivial (_156_994)))))
in (
# 1151 "FStar.TypeChecker.Util.fst"
let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _156_998 -> FStar_TypeChecker_Common.NonTrivial (_156_998))))
in (
# 1153 "FStar.TypeChecker.Util.fst"
let short_op_ite = (fun _67_6 -> (match (_67_6) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (guard, _67_1555)::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| _then::(guard, _67_1560)::[] -> begin
(let _156_1002 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _156_1002 (fun _156_1001 -> FStar_TypeChecker_Common.NonTrivial (_156_1001))))
end
| _67_1565 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (
# 1158 "FStar.TypeChecker.Util.fst"
let table = ((FStar_Syntax_Const.op_And, (short_bin_op op_and_e)))::((FStar_Syntax_Const.op_Or, (short_bin_op op_or_e)))::((FStar_Syntax_Const.and_lid, (short_bin_op op_and_t)))::((FStar_Syntax_Const.or_lid, (short_bin_op op_or_t)))::((FStar_Syntax_Const.imp_lid, (short_bin_op op_imp_t)))::((FStar_Syntax_Const.ite_lid, short_op_ite))::[]
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(
# 1168 "FStar.TypeChecker.Util.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((FStar_Util.find_map table (fun _67_1573 -> (match (_67_1573) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _156_1035 = (mk seen_args)
in Some (_156_1035))
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
| _67_1578 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))

# 1173 "FStar.TypeChecker.Util.fst"
let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (match ((let _156_1038 = (FStar_Syntax_Util.un_uinst l)
in _156_1038.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| _67_1583 -> begin
false
end))

# 1185 "FStar.TypeChecker.Util.fst"
let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (
# 1197 "FStar.TypeChecker.Util.fst"
let pos = (fun bs -> (match (bs) with
| (hd, _67_1592)::_67_1589 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| _67_1596 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| (_67_1600, Some (FStar_Syntax_Syntax.Implicit (_67_1602)))::_67_1598 -> begin
bs
end
| _67_1608 -> begin
(match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
bs
end
| Some (t) -> begin
(match ((let _156_1045 = (FStar_Syntax_Subst.compress t)
in _156_1045.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', _67_1614) -> begin
(match ((FStar_Util.prefix_until (fun _67_7 -> (match (_67_7) with
| (_67_1619, Some (FStar_Syntax_Syntax.Implicit (_67_1621))) -> begin
false
end
| _67_1626 -> begin
true
end)) bs')) with
| None -> begin
bs
end
| Some ([], _67_1630, _67_1632) -> begin
bs
end
| Some (imps, _67_1637, _67_1639) -> begin
if (FStar_All.pipe_right imps (FStar_Util.for_all (fun _67_1645 -> (match (_67_1645) with
| (x, _67_1644) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end)))) then begin
(
# 1213 "FStar.TypeChecker.Util.fst"
let r = (pos bs)
in (
# 1214 "FStar.TypeChecker.Util.fst"
let imps = (FStar_All.pipe_right imps (FStar_List.map (fun _67_1649 -> (match (_67_1649) with
| (x, i) -> begin
(let _156_1049 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in (_156_1049, i))
end))))
in (FStar_List.append imps bs)))
end else begin
bs
end
end)
end
| _67_1652 -> begin
bs
end)
end)
end)))




