
open Prims
# 31 "FStar.TypeChecker.Util.fst"
type lcomp_with_binder =
(FStar_Syntax_Syntax.bv Prims.option * FStar_Syntax_Syntax.lcomp)

# 78 "FStar.TypeChecker.Util.fst"
let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _145_6 = (FStar_TypeChecker_Env.get_range env)
in (let _145_5 = (FStar_TypeChecker_Errors.failed_to_prove_specification errs)
in (FStar_TypeChecker_Errors.report _145_6 _145_5))))

# 85 "FStar.TypeChecker.Util.fst"
let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _145_9 = (FStar_Syntax_Subst.compress t)
in _145_9.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_56_12) -> begin
true
end
| _56_15 -> begin
false
end))

# 89 "FStar.TypeChecker.Util.fst"
let t_binders : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env -> (let _145_13 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right _145_13 (FStar_List.filter (fun _56_20 -> (match (_56_20) with
| (x, _56_19) -> begin
(is_type x.FStar_Syntax_Syntax.sort)
end))))))

# 93 "FStar.TypeChecker.Util.fst"
let new_uvar_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun env k -> (
# 94 "FStar.TypeChecker.Util.fst"
let bs = if ((FStar_ST.read FStar_Options.full_context_dependency) || (let _145_18 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _145_18))) then begin
(FStar_TypeChecker_Env.all_binders env)
end else begin
(t_binders env)
end
in (let _145_19 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Rel.new_uvar _145_19 bs k))))

# 100 "FStar.TypeChecker.Util.fst"
let new_uvar : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env k -> (let _145_24 = (new_uvar_aux env k)
in (Prims.fst _145_24)))

# 102 "FStar.TypeChecker.Util.fst"
let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun _56_1 -> (match (_56_1) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, _56_35); FStar_Syntax_Syntax.tk = _56_32; FStar_Syntax_Syntax.pos = _56_30; FStar_Syntax_Syntax.vars = _56_28} -> begin
uv
end
| _56_40 -> begin
(FStar_All.failwith "Impossible")
end))

# 106 "FStar.TypeChecker.Util.fst"
let new_implicit_var : Prims.string  ->  FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.uvar * FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t) = (fun reason r env k -> (match ((FStar_Syntax_Util.destruct k FStar_Syntax_Const.range_of_lid)) with
| Some (_56_50::(tm, _56_47)::[]) -> begin
(
# 109 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))) None tm.FStar_Syntax_Syntax.pos)
in (t, [], FStar_TypeChecker_Rel.trivial_guard))
end
| _56_55 -> begin
(
# 113 "FStar.TypeChecker.Util.fst"
let _56_58 = (new_uvar_aux env k)
in (match (_56_58) with
| (t, u) -> begin
(
# 114 "FStar.TypeChecker.Util.fst"
let g = (
# 114 "FStar.TypeChecker.Util.fst"
let _56_59 = FStar_TypeChecker_Rel.trivial_guard
in (let _145_37 = (let _145_36 = (let _145_35 = (as_uvar u)
in (reason, env, _145_35, t, k, r))
in (_145_36)::[])
in {FStar_TypeChecker_Env.guard_f = _56_59.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _56_59.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_59.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _145_37}))
in (let _145_40 = (let _145_39 = (let _145_38 = (as_uvar u)
in (_145_38, r))
in (_145_39)::[])
in (t, _145_40, g)))
end))
end))

# 117 "FStar.TypeChecker.Util.fst"
let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun r t -> (
# 118 "FStar.TypeChecker.Util.fst"
let uvs = (FStar_Syntax_Free.uvars t)
in if (not ((FStar_Util.set_is_empty uvs))) then begin
(
# 121 "FStar.TypeChecker.Util.fst"
let us = (let _145_47 = (let _145_46 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun _56_68 -> (match (_56_68) with
| (x, _56_67) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) _145_46))
in (FStar_All.pipe_right _145_47 (FStar_String.concat ", ")))
in (
# 123 "FStar.TypeChecker.Util.fst"
let hide_uvar_nums_saved = (FStar_ST.read FStar_Options.hide_uvar_nums)
in (
# 124 "FStar.TypeChecker.Util.fst"
let print_implicits_saved = (FStar_ST.read FStar_Options.print_implicits)
in (
# 125 "FStar.TypeChecker.Util.fst"
let _56_72 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums false)
in (
# 126 "FStar.TypeChecker.Util.fst"
let _56_74 = (FStar_ST.op_Colon_Equals FStar_Options.print_implicits true)
in (
# 127 "FStar.TypeChecker.Util.fst"
let _56_76 = (let _145_49 = (let _145_48 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us _145_48))
in (FStar_TypeChecker_Errors.report r _145_49))
in (
# 130 "FStar.TypeChecker.Util.fst"
let _56_78 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums hide_uvar_nums_saved)
in (FStar_ST.op_Colon_Equals FStar_Options.print_implicits print_implicits_saved))))))))
end else begin
()
end))

# 137 "FStar.TypeChecker.Util.fst"
let force_sort' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' = (fun s -> (match ((FStar_ST.read s.FStar_Syntax_Syntax.tk)) with
| None -> begin
(let _145_54 = (let _145_53 = (FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos)
in (let _145_52 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s" _145_53 _145_52)))
in (FStar_All.failwith _145_54))
end
| Some (tk) -> begin
tk
end))

# 141 "FStar.TypeChecker.Util.fst"
let force_sort = (fun s -> (let _145_56 = (force_sort' s)
in (FStar_Syntax_Syntax.mk _145_56 None s.FStar_Syntax_Syntax.pos)))

# 143 "FStar.TypeChecker.Util.fst"
let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env _56_93 -> (match (_56_93) with
| {FStar_Syntax_Syntax.lbname = _56_92; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _56_88; FStar_Syntax_Syntax.lbdef = e} -> begin
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
let _56_97 = if (univ_vars <> []) then begin
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
let _56_107 = (FStar_Syntax_Util.type_u ())
in (match (_56_107) with
| (k, _56_106) -> begin
(
# 153 "FStar.TypeChecker.Util.fst"
let t = (let _145_65 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right _145_65 Prims.fst))
in ((
# 154 "FStar.TypeChecker.Util.fst"
let _56_109 = a
in {FStar_Syntax_Syntax.ppname = _56_109.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_109.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), false))
end))
end
| _56_112 -> begin
(a, true)
end))
in (
# 157 "FStar.TypeChecker.Util.fst"
let rec aux = (fun vars e -> (
# 158 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, _56_119) -> begin
(aux vars e)
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _56_125) -> begin
(t, true)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _56_131) -> begin
(
# 164 "FStar.TypeChecker.Util.fst"
let _56_150 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _56_137 _56_140 -> (match ((_56_137, _56_140)) with
| ((scope, bs, check), (a, imp)) -> begin
(
# 165 "FStar.TypeChecker.Util.fst"
let _56_143 = (mk_binder scope a)
in (match (_56_143) with
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
in (match (_56_150) with
| (scope, bs, check) -> begin
(
# 172 "FStar.TypeChecker.Util.fst"
let _56_153 = (aux scope body)
in (match (_56_153) with
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
let _56_160 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _145_73 = (FStar_Range.string_of_range r)
in (let _145_72 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _145_73 _145_72)))
end else begin
()
end
in (FStar_Util.Inl (t), (check_res || check)))))
end))
end))
end
| _56_163 -> begin
(let _145_76 = (let _145_75 = (let _145_74 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _145_74 Prims.fst))
in FStar_Util.Inl (_145_75))
in (_145_76, false))
end)))
in (
# 182 "FStar.TypeChecker.Util.fst"
let _56_166 = (let _145_77 = (t_binders env)
in (aux _145_77 e))
in (match (_56_166) with
| (t, b) -> begin
(
# 183 "FStar.TypeChecker.Util.fst"
let t = (match (t) with
| FStar_Util.Inr (c) -> begin
(let _145_81 = (let _145_80 = (let _145_79 = (let _145_78 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" _145_78))
in (_145_79, rng))
in FStar_Syntax_Syntax.Error (_145_80))
in (Prims.raise _145_81))
end
| FStar_Util.Inl (t) -> begin
t
end)
in ([], t, b))
end))))))
end
| _56_173 -> begin
(
# 192 "FStar.TypeChecker.Util.fst"
let _56_176 = (FStar_Syntax_Subst.open_univ_vars univ_vars t)
in (match (_56_176) with
| (univ_vars, t) -> begin
(univ_vars, t, false)
end))
end)))
end))

# 203 "FStar.TypeChecker.Util.fst"
let pat_as_exps : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term Prims.list * FStar_Syntax_Syntax.pat) = (fun allow_implicits env p -> (
# 208 "FStar.TypeChecker.Util.fst"
let rec pat_as_arg_with_env = (fun allow_wc_dependence env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(
# 217 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) None p.FStar_Syntax_Syntax.p)
in ([], [], [], env, e, p))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _56_189) -> begin
(
# 221 "FStar.TypeChecker.Util.fst"
let _56_195 = (FStar_Syntax_Util.type_u ())
in (match (_56_195) with
| (k, _56_194) -> begin
(
# 222 "FStar.TypeChecker.Util.fst"
let t = (new_uvar env k)
in (
# 223 "FStar.TypeChecker.Util.fst"
let x = (
# 223 "FStar.TypeChecker.Util.fst"
let _56_197 = x
in {FStar_Syntax_Syntax.ppname = _56_197.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_197.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (
# 224 "FStar.TypeChecker.Util.fst"
let _56_202 = (let _145_94 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _145_94 t))
in (match (_56_202) with
| (e, u) -> begin
(
# 225 "FStar.TypeChecker.Util.fst"
let p = (
# 225 "FStar.TypeChecker.Util.fst"
let _56_203 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, e)); FStar_Syntax_Syntax.ty = _56_203.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_203.FStar_Syntax_Syntax.p})
in ([], [], [], env, e, p))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 229 "FStar.TypeChecker.Util.fst"
let _56_211 = (FStar_Syntax_Util.type_u ())
in (match (_56_211) with
| (t, _56_210) -> begin
(
# 230 "FStar.TypeChecker.Util.fst"
let x = (
# 230 "FStar.TypeChecker.Util.fst"
let _56_212 = x
in (let _145_95 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _56_212.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_212.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_95}))
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
let _56_222 = (FStar_Syntax_Util.type_u ())
in (match (_56_222) with
| (t, _56_221) -> begin
(
# 237 "FStar.TypeChecker.Util.fst"
let x = (
# 237 "FStar.TypeChecker.Util.fst"
let _56_223 = x
in (let _145_96 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _56_223.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_223.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_96}))
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
let _56_256 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _56_238 _56_241 -> (match ((_56_238, _56_241)) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(
# 244 "FStar.TypeChecker.Util.fst"
let _56_248 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_56_248) with
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
in (match (_56_256) with
| (b, a, w, env, args, pats) -> begin
(
# 248 "FStar.TypeChecker.Util.fst"
let e = (let _145_103 = (let _145_102 = (let _145_101 = (let _145_100 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (let _145_99 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app _145_100 _145_99 None p.FStar_Syntax_Syntax.p)))
in (_145_101, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))
in FStar_Syntax_Syntax.Tm_meta (_145_102))
in (FStar_Syntax_Syntax.mk _145_103 None p.FStar_Syntax_Syntax.p))
in (let _145_106 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _145_105 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _145_104 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in (_145_106, _145_105, _145_104, env, e, (
# 254 "FStar.TypeChecker.Util.fst"
let _56_258 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _56_258.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_258.FStar_Syntax_Syntax.p}))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (_56_261) -> begin
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
let pats = (FStar_List.map (fun _56_276 -> (match (_56_276) with
| (p, imp) -> begin
(let _145_118 = (elaborate_pat env p)
in (_145_118, imp))
end)) pats)
in (
# 266 "FStar.TypeChecker.Util.fst"
let _56_281 = (FStar_TypeChecker_Env.lookup_datacon env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_56_281) with
| (_56_279, t) -> begin
(
# 267 "FStar.TypeChecker.Util.fst"
let _56_285 = (FStar_Syntax_Util.arrow_formals t)
in (match (_56_285) with
| (f, _56_284) -> begin
(
# 268 "FStar.TypeChecker.Util.fst"
let rec aux = (fun formals pats -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _56_296::_56_294) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))))
end
| (_56_302::_56_300, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun _56_308 -> (match (_56_308) with
| (t, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(
# 274 "FStar.TypeChecker.Util.fst"
let a = (let _145_125 = (let _145_124 = (FStar_Syntax_Syntax.range_of_bv t)
in Some (_145_124))
in (FStar_Syntax_Syntax.new_bv _145_125 FStar_Syntax_Syntax.tun))
in (
# 275 "FStar.TypeChecker.Util.fst"
let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (let _145_126 = (maybe_dot inaccessible a r)
in (_145_126, true))))
end
| _56_315 -> begin
(let _145_130 = (let _145_129 = (let _145_128 = (let _145_127 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _145_127))
in (_145_128, (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in FStar_Syntax_Syntax.Error (_145_129))
in (Prims.raise _145_130))
end)
end))))
end
| (f::formals', (p, p_imp)::pats') -> begin
(match (f) with
| (_56_326, Some (FStar_Syntax_Syntax.Implicit (_56_328))) when p_imp -> begin
(let _145_131 = (aux formals' pats')
in ((p, true))::_145_131)
end
| (_56_333, Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(
# 287 "FStar.TypeChecker.Util.fst"
let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (
# 288 "FStar.TypeChecker.Util.fst"
let p = (maybe_dot inaccessible a (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
in (let _145_132 = (aux formals' pats)
in ((p, true))::_145_132)))
end
| (_56_341, imp) -> begin
(let _145_135 = (let _145_133 = (FStar_Syntax_Syntax.is_implicit imp)
in (p, _145_133))
in (let _145_134 = (aux formals' pats')
in (_145_135)::_145_134))
end)
end))
in (
# 294 "FStar.TypeChecker.Util.fst"
let _56_344 = p
in (let _145_138 = (let _145_137 = (let _145_136 = (aux f pats)
in (fv, _145_136))
in FStar_Syntax_Syntax.Pat_cons (_145_137))
in {FStar_Syntax_Syntax.v = _145_138; FStar_Syntax_Syntax.ty = _56_344.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_344.FStar_Syntax_Syntax.p})))
end))
end)))
end
| _56_347 -> begin
p
end)))
in (
# 298 "FStar.TypeChecker.Util.fst"
let one_pat = (fun allow_wc_dependence env p -> (
# 299 "FStar.TypeChecker.Util.fst"
let p = (elaborate_pat env p)
in (
# 300 "FStar.TypeChecker.Util.fst"
let _56_359 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_56_359) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))) with
| Some (x) -> begin
(let _145_147 = (let _145_146 = (let _145_145 = (FStar_TypeChecker_Errors.nonlinear_pattern_variable x)
in (_145_145, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_145_146))
in (Prims.raise _145_147))
end
| _56_363 -> begin
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
let _56_379 = (one_pat false env q)
in (match (_56_379) with
| (b, a, _56_376, te, q) -> begin
(
# 313 "FStar.TypeChecker.Util.fst"
let _56_394 = (FStar_List.fold_right (fun p _56_384 -> (match (_56_384) with
| (w, args, pats) -> begin
(
# 314 "FStar.TypeChecker.Util.fst"
let _56_390 = (one_pat false env p)
in (match (_56_390) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv FStar_Syntax_Syntax.bv_eq a a'))) then begin
(let _145_157 = (let _145_156 = (let _145_155 = (FStar_TypeChecker_Errors.disjunctive_pattern_vars a a')
in (let _145_154 = (FStar_TypeChecker_Env.get_range env)
in (_145_155, _145_154)))
in FStar_Syntax_Syntax.Error (_145_156))
in (Prims.raise _145_157))
end else begin
(let _145_159 = (let _145_158 = (FStar_Syntax_Syntax.as_arg arg)
in (_145_158)::args)
in ((FStar_List.append w' w), _145_159, (p)::pats))
end
end))
end)) pats ([], [], []))
in (match (_56_394) with
| (w, args, pats) -> begin
(let _145_161 = (let _145_160 = (FStar_Syntax_Syntax.as_arg te)
in (_145_160)::args)
in ((FStar_List.append b w), _145_161, (
# 319 "FStar.TypeChecker.Util.fst"
let _56_395 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((q)::pats); FStar_Syntax_Syntax.ty = _56_395.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_395.FStar_Syntax_Syntax.p})))
end))
end))
end
| _56_398 -> begin
(
# 322 "FStar.TypeChecker.Util.fst"
let _56_406 = (one_pat true env p)
in (match (_56_406) with
| (b, _56_401, _56_403, arg, p) -> begin
(let _145_163 = (let _145_162 = (FStar_Syntax_Syntax.as_arg arg)
in (_145_162)::[])
in (b, _145_163, p))
end))
end))
in (
# 325 "FStar.TypeChecker.Util.fst"
let _56_410 = (top_level_pat_as_args env p)
in (match (_56_410) with
| (b, args, p) -> begin
(
# 326 "FStar.TypeChecker.Util.fst"
let exps = (FStar_All.pipe_right args (FStar_List.map Prims.fst))
in (b, exps, p))
end)))))))

# 329 "FStar.TypeChecker.Util.fst"
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
| (_56_424, FStar_Syntax_Syntax.Tm_uinst (e, _56_427)) -> begin
(aux p e)
end
| (FStar_Syntax_Syntax.Pat_constant (_56_432), FStar_Syntax_Syntax.Tm_constant (_56_435)) -> begin
(let _145_178 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v _145_178))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(
# 341 "FStar.TypeChecker.Util.fst"
let _56_443 = if (not ((FStar_Syntax_Syntax.bv_eq x y))) then begin
(let _145_181 = (let _145_180 = (FStar_Syntax_Print.bv_to_string x)
in (let _145_179 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _145_180 _145_179)))
in (FStar_All.failwith _145_181))
end else begin
()
end
in (
# 343 "FStar.TypeChecker.Util.fst"
let _56_445 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _145_183 = (FStar_Syntax_Print.bv_to_string x)
in (let _145_182 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _145_183 _145_182)))
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
let _56_448 = x
in {FStar_Syntax_Syntax.ppname = _56_448.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_448.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x)) s.FStar_Syntax_Syntax.n)))))
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(
# 350 "FStar.TypeChecker.Util.fst"
let _56_456 = if (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation) then begin
(let _145_186 = (let _145_185 = (FStar_Syntax_Print.bv_to_string x)
in (let _145_184 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _145_185 _145_184)))
in (FStar_All.failwith _145_186))
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
let _56_459 = x
in {FStar_Syntax_Syntax.ppname = _56_459.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_459.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x)) s.FStar_Syntax_Syntax.n))))
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _56_464), _56_468) -> begin
(
# 357 "FStar.TypeChecker.Util.fst"
let s = (force_sort e)
in (
# 358 "FStar.TypeChecker.Util.fst"
let x = (
# 358 "FStar.TypeChecker.Util.fst"
let _56_471 = x
in {FStar_Syntax_Syntax.ppname = _56_471.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_471.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
(
# 362 "FStar.TypeChecker.Util.fst"
let _56_481 = if (not ((FStar_Syntax_Syntax.fv_eq fv fv'))) then begin
(let _145_187 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _145_187))
end else begin
()
end
in (let _145_188 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv', []))) _145_188)))
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
(
# 369 "FStar.TypeChecker.Util.fst"
let _56_524 = if (let _145_189 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right _145_189 Prims.op_Negation)) then begin
(let _145_190 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _145_190))
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
(let _145_197 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev matched_pats)))) _145_197))
end
| (arg::args, (argpat, _56_540)::argpats) -> begin
(match ((arg, argpat.FStar_Syntax_Syntax.v)) with
| ((e, Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (_56_550)) -> begin
(
# 378 "FStar.TypeChecker.Util.fst"
let x = (let _145_198 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _145_198))
in (
# 379 "FStar.TypeChecker.Util.fst"
let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((e, imp), _56_559) -> begin
(
# 383 "FStar.TypeChecker.Util.fst"
let pat = (let _145_200 = (aux argpat e)
in (let _145_199 = (FStar_Syntax_Syntax.is_implicit imp)
in (_145_200, _145_199)))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _56_563 -> begin
(let _145_203 = (let _145_202 = (FStar_Syntax_Print.pat_to_string p)
in (let _145_201 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _145_202 _145_201)))
in (FStar_All.failwith _145_203))
end))
in (match_args [] args argpats))))
end
| _56_565 -> begin
(let _145_208 = (let _145_207 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (let _145_206 = (FStar_Syntax_Print.pat_to_string qq)
in (let _145_205 = (let _145_204 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right _145_204 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _145_207 _145_206 _145_205))))
in (FStar_All.failwith _145_208))
end))))
in (match ((p.FStar_Syntax_Syntax.v, exps)) with
| (FStar_Syntax_Syntax.Pat_disj (ps), _56_569) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(
# 396 "FStar.TypeChecker.Util.fst"
let ps = (FStar_List.map2 aux ps exps)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj (ps)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p))
end
| (_56_573, e::[]) -> begin
(aux p e)
end
| _56_578 -> begin
(FStar_All.failwith "Unexpected number of patterns")
end))))

# 404 "FStar.TypeChecker.Util.fst"
let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (
# 405 "FStar.TypeChecker.Util.fst"
let topt = Some (pat.FStar_Syntax_Syntax.ty)
in (
# 406 "FStar.TypeChecker.Util.fst"
let mk = (fun f -> (FStar_Syntax_Syntax.mk f topt pat.FStar_Syntax_Syntax.p))
in (
# 408 "FStar.TypeChecker.Util.fst"
let pat_as_arg = (fun _56_586 -> (match (_56_586) with
| (p, i) -> begin
(
# 409 "FStar.TypeChecker.Util.fst"
let _56_589 = (decorated_pattern_as_term p)
in (match (_56_589) with
| (vars, te) -> begin
(let _145_216 = (let _145_215 = (FStar_Syntax_Syntax.as_implicit i)
in (te, _145_215))
in (vars, _145_216))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_56_591) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _145_217 = (mk (FStar_Syntax_Syntax.Tm_constant (c)))
in ([], _145_217))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(let _145_218 = (mk (FStar_Syntax_Syntax.Tm_name (x)))
in ((x)::[], _145_218))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 423 "FStar.TypeChecker.Util.fst"
let _56_604 = (let _145_219 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _145_219 FStar_List.unzip))
in (match (_56_604) with
| (vars, args) -> begin
(
# 424 "FStar.TypeChecker.Util.fst"
let vars = (FStar_List.flatten vars)
in (let _145_223 = (let _145_222 = (let _145_221 = (let _145_220 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (_145_220, args))
in FStar_Syntax_Syntax.Tm_app (_145_221))
in (mk _145_222))
in (vars, _145_223)))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
([], e)
end)))))

# 434 "FStar.TypeChecker.Util.fst"
let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (
# 435 "FStar.TypeChecker.Util.fst"
let _56_628 = (match (c.FStar_Syntax_Syntax.effect_args) with
| (wp, _56_617)::(wlp, _56_613)::[] -> begin
(wp, wlp)
end
| _56_621 -> begin
(let _145_229 = (let _145_228 = (let _145_227 = (FStar_List.map (fun _56_625 -> (match (_56_625) with
| (x, _56_624) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right _145_227 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str _145_228))
in (FStar_All.failwith _145_229))
end)
in (match (_56_628) with
| (wp, wlp) -> begin
(c.FStar_Syntax_Syntax.result_typ, wp, wlp)
end)))

# 441 "FStar.TypeChecker.Util.fst"
let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (
# 442 "FStar.TypeChecker.Util.fst"
let _56_636 = (destruct_comp c)
in (match (_56_636) with
| (_56_633, wp, wlp) -> begin
(let _145_251 = (let _145_250 = (let _145_246 = (lift c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _145_246))
in (let _145_249 = (let _145_248 = (let _145_247 = (lift c.FStar_Syntax_Syntax.result_typ wlp)
in (FStar_Syntax_Syntax.as_arg _145_247))
in (_145_248)::[])
in (_145_250)::_145_249))
in {FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _145_251; FStar_Syntax_Syntax.flags = []})
end)))

# 448 "FStar.TypeChecker.Util.fst"
let norm_eff_name : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (
# 449 "FStar.TypeChecker.Util.fst"
let cache = (FStar_Util.smap_create 20)
in (fun env l -> (
# 451 "FStar.TypeChecker.Util.fst"
let rec find = (fun l -> (match ((FStar_TypeChecker_Env.lookup_effect_abbrev env FStar_Syntax_Syntax.U_unknown l)) with
| None -> begin
None
end
| Some (_56_644, c) -> begin
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
let _56_658 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))

# 470 "FStar.TypeChecker.Util.fst"
let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (
# 471 "FStar.TypeChecker.Util.fst"
let _56_669 = (let _145_265 = (norm_eff_name env l1)
in (let _145_264 = (norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _145_265 _145_264)))
in (match (_56_669) with
| (m, _56_666, _56_668) -> begin
m
end)))

# 474 "FStar.TypeChecker.Util.fst"
let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> if ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2)) then begin
FStar_Syntax_Const.effect_Tot_lid
end else begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)

# 480 "FStar.TypeChecker.Util.fst"
let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)) = (fun env c1 c2 -> (
# 481 "FStar.TypeChecker.Util.fst"
let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (
# 482 "FStar.TypeChecker.Util.fst"
let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (
# 483 "FStar.TypeChecker.Util.fst"
let _56_681 = (FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (_56_681) with
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
let _56_687 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (_56_687) with
| (a, kwp) -> begin
(let _145_279 = (destruct_comp m1)
in (let _145_278 = (destruct_comp m2)
in ((md, a, kwp), _145_279, _145_278)))
end)))))
end)))))

# 490 "FStar.TypeChecker.Util.fst"
let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (
# 491 "FStar.TypeChecker.Util.fst"
let l = (norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)))

# 494 "FStar.TypeChecker.Util.fst"
let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (
# 495 "FStar.TypeChecker.Util.fst"
let l = (norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid))))

# 499 "FStar.TypeChecker.Util.fst"
let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md result wp wlp flags -> (let _145_302 = (let _145_301 = (let _145_300 = (FStar_Syntax_Syntax.as_arg wp)
in (let _145_299 = (let _145_298 = (FStar_Syntax_Syntax.as_arg wlp)
in (_145_298)::[])
in (_145_300)::_145_299))
in {FStar_Syntax_Syntax.effect_name = md.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = _145_301; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp _145_302)))

# 505 "FStar.TypeChecker.Util.fst"
let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (
# 506 "FStar.TypeChecker.Util.fst"
let _56_701 = lc
in (let _145_309 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _56_701.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _145_309; FStar_Syntax_Syntax.cflags = _56_701.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _56_703 -> (match (()) with
| () -> begin
(let _145_308 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _145_308))
end))})))

# 509 "FStar.TypeChecker.Util.fst"
let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _145_312 = (FStar_Syntax_Subst.compress t)
in _145_312.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_56_706) -> begin
true
end
| _56_709 -> begin
false
end))

# 513 "FStar.TypeChecker.Util.fst"
let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v -> (
# 515 "FStar.TypeChecker.Util.fst"
let c = if (let _145_319 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation _145_319)) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(
# 518 "FStar.TypeChecker.Util.fst"
let m = (let _145_320 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must _145_320))
in (
# 519 "FStar.TypeChecker.Util.fst"
let _56_716 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_56_716) with
| (a, kwp) -> begin
(
# 520 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 521 "FStar.TypeChecker.Util.fst"
let wp = (let _145_328 = (let _145_327 = (let _145_322 = (let _145_321 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_145_321)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _145_322 env m m.FStar_Syntax_Syntax.ret))
in (let _145_326 = (let _145_325 = (FStar_Syntax_Syntax.as_arg t)
in (let _145_324 = (let _145_323 = (FStar_Syntax_Syntax.as_arg v)
in (_145_323)::[])
in (_145_325)::_145_324))
in (FStar_Syntax_Syntax.mk_Tm_app _145_327 _145_326 (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _145_328))
in (
# 522 "FStar.TypeChecker.Util.fst"
let wlp = wp
in (mk_comp m t wp wlp ((FStar_Syntax_Syntax.RETURN)::[])))))
end)))
end
in (
# 524 "FStar.TypeChecker.Util.fst"
let _56_721 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return"))) then begin
(let _145_331 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _145_330 = (FStar_Syntax_Print.term_to_string v)
in (let _145_329 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _145_331 _145_330 _145_329))))
end else begin
()
end
in c)))

# 529 "FStar.TypeChecker.Util.fst"
let bind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun env e1opt lc1 _56_728 -> (match (_56_728) with
| (b, lc2) -> begin
(
# 530 "FStar.TypeChecker.Util.fst"
let _56_736 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(
# 532 "FStar.TypeChecker.Util.fst"
let bstr = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _145_342 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (let _145_341 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _145_340 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" _145_342 _145_341 bstr _145_340)))))
end else begin
()
end
in (
# 538 "FStar.TypeChecker.Util.fst"
let bind_it = (fun _56_739 -> (match (()) with
| () -> begin
(
# 539 "FStar.TypeChecker.Util.fst"
let c1 = (lc1.FStar_Syntax_Syntax.comp ())
in (
# 540 "FStar.TypeChecker.Util.fst"
let c2 = (lc2.FStar_Syntax_Syntax.comp ())
in (
# 541 "FStar.TypeChecker.Util.fst"
let _56_745 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _145_349 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _145_348 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _145_347 = (FStar_Syntax_Print.comp_to_string c1)
in (let _145_346 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (let _145_345 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" _145_349 _145_348 _145_347 _145_346 _145_345))))))
end else begin
()
end
in (
# 550 "FStar.TypeChecker.Util.fst"
let try_simplify = (fun _56_748 -> (match (()) with
| () -> begin
(
# 551 "FStar.TypeChecker.Util.fst"
let aux = (fun _56_750 -> (match (()) with
| () -> begin
if (FStar_Syntax_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some ((c2, "trivial no binder"))
end
| Some (_56_753) -> begin
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
(let _145_357 = (let _145_356 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT ((x, e)))::[]) c2)
in (_145_356, reason))
in Some (_145_357))
end
| _56_763 -> begin
(aux ())
end))
in if ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2)) then begin
(subst_c2 "both total")
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2)) then begin
(let _145_359 = (let _145_358 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in (_145_358, "both gtot"))
in Some (_145_359))
end else begin
(match ((e1opt, b)) with
| (Some (e), Some (x)) -> begin
if ((FStar_Syntax_Util.is_total_comp c1) && (not ((FStar_Syntax_Syntax.is_null_bv x)))) then begin
(subst_c2 "substituted e")
end else begin
(aux ())
end
end
| _56_770 -> begin
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
let _56_788 = (lift_and_destruct env c1 c2)
in (match (_56_788) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(
# 584 "FStar.TypeChecker.Util.fst"
let bs = (match (b) with
| None -> begin
(let _145_360 = (FStar_Syntax_Syntax.null_binder t1)
in (_145_360)::[])
end
| Some (x) -> begin
(let _145_361 = (FStar_Syntax_Syntax.mk_binder x)
in (_145_361)::[])
end)
in (
# 587 "FStar.TypeChecker.Util.fst"
let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp None))
in (
# 588 "FStar.TypeChecker.Util.fst"
let wp_args = (let _145_376 = (FStar_Syntax_Syntax.as_arg t1)
in (let _145_375 = (let _145_374 = (FStar_Syntax_Syntax.as_arg t2)
in (let _145_373 = (let _145_372 = (FStar_Syntax_Syntax.as_arg wp1)
in (let _145_371 = (let _145_370 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _145_369 = (let _145_368 = (let _145_364 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg _145_364))
in (let _145_367 = (let _145_366 = (let _145_365 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _145_365))
in (_145_366)::[])
in (_145_368)::_145_367))
in (_145_370)::_145_369))
in (_145_372)::_145_371))
in (_145_374)::_145_373))
in (_145_376)::_145_375))
in (
# 589 "FStar.TypeChecker.Util.fst"
let wlp_args = (let _145_384 = (FStar_Syntax_Syntax.as_arg t1)
in (let _145_383 = (let _145_382 = (FStar_Syntax_Syntax.as_arg t2)
in (let _145_381 = (let _145_380 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _145_379 = (let _145_378 = (let _145_377 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _145_377))
in (_145_378)::[])
in (_145_380)::_145_379))
in (_145_382)::_145_381))
in (_145_384)::_145_383))
in (
# 590 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t2)))::[]) kwp)
in (
# 591 "FStar.TypeChecker.Util.fst"
let us = (let _145_387 = (env.FStar_TypeChecker_Env.universe_of env t1)
in (let _145_386 = (let _145_385 = (env.FStar_TypeChecker_Env.universe_of env t2)
in (_145_385)::[])
in (_145_387)::_145_386))
in (
# 592 "FStar.TypeChecker.Util.fst"
let wp = (let _145_388 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _145_388 wp_args None t2.FStar_Syntax_Syntax.pos))
in (
# 593 "FStar.TypeChecker.Util.fst"
let wlp = (let _145_389 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wlp)
in (FStar_Syntax_Syntax.mk_Tm_app _145_389 wlp_args None t2.FStar_Syntax_Syntax.pos))
in (
# 594 "FStar.TypeChecker.Util.fst"
let c = (mk_comp md t2 wp wlp [])
in c)))))))))
end))
end)))))
end))
in (let _145_390 = (join_lcomp env lc1 lc2)
in {FStar_Syntax_Syntax.eff_name = _145_390; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it})))
end))

# 601 "FStar.TypeChecker.Util.fst"
let lift_formula : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t mk_wp mk_wlp f -> (
# 602 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 603 "FStar.TypeChecker.Util.fst"
let _56_810 = (FStar_TypeChecker_Env.wp_signature env md_pure.FStar_Syntax_Syntax.mname)
in (match (_56_810) with
| (a, kwp) -> begin
(
# 604 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 605 "FStar.TypeChecker.Util.fst"
let wp = (let _145_404 = (let _145_403 = (FStar_Syntax_Syntax.as_arg t)
in (let _145_402 = (let _145_401 = (FStar_Syntax_Syntax.as_arg f)
in (_145_401)::[])
in (_145_403)::_145_402))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wp _145_404 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (
# 606 "FStar.TypeChecker.Util.fst"
let wlp = (let _145_408 = (let _145_407 = (FStar_Syntax_Syntax.as_arg t)
in (let _145_406 = (let _145_405 = (FStar_Syntax_Syntax.as_arg f)
in (_145_405)::[])
in (_145_407)::_145_406))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wlp _145_408 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (mk_comp md_pure FStar_TypeChecker_Common.t_unit wp wlp []))))
end))))

# 609 "FStar.TypeChecker.Util.fst"
let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((f, FStar_Syntax_Syntax.Meta_labeled ((reason, r, false))))) None f.FStar_Syntax_Syntax.pos))

# 612 "FStar.TypeChecker.Util.fst"
let label_opt : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _145_432 = (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)
in (FStar_All.pipe_left Prims.op_Negation _145_432)) then begin
f
end else begin
(let _145_433 = (reason ())
in (label _145_433 r f))
end
end))

# 619 "FStar.TypeChecker.Util.fst"
let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 621 "FStar.TypeChecker.Util.fst"
let _56_830 = g
in (let _145_441 = (let _145_440 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_145_440))
in {FStar_TypeChecker_Env.guard_f = _145_441; FStar_TypeChecker_Env.deferred = _56_830.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_830.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_830.FStar_TypeChecker_Env.implicits}))
end))

# 623 "FStar.TypeChecker.Util.fst"
let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(
# 625 "FStar.TypeChecker.Util.fst"
let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| _56_841 -> begin
g2
end))

# 629 "FStar.TypeChecker.Util.fst"
let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (
# 630 "FStar.TypeChecker.Util.fst"
let weaken = (fun _56_846 -> (match (()) with
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
let _56_855 = (destruct_comp c)
in (match (_56_855) with
| (res_t, wp, wlp) -> begin
(
# 639 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 640 "FStar.TypeChecker.Util.fst"
let us = (let _145_454 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_145_454)::[])
in (
# 641 "FStar.TypeChecker.Util.fst"
let wp = (let _145_461 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _145_460 = (let _145_459 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_458 = (let _145_457 = (FStar_Syntax_Syntax.as_arg f)
in (let _145_456 = (let _145_455 = (FStar_Syntax_Syntax.as_arg wp)
in (_145_455)::[])
in (_145_457)::_145_456))
in (_145_459)::_145_458))
in (FStar_Syntax_Syntax.mk_Tm_app _145_461 _145_460 None wp.FStar_Syntax_Syntax.pos)))
in (
# 642 "FStar.TypeChecker.Util.fst"
let wlp = (let _145_468 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _145_467 = (let _145_466 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_465 = (let _145_464 = (FStar_Syntax_Syntax.as_arg f)
in (let _145_463 = (let _145_462 = (FStar_Syntax_Syntax.as_arg wlp)
in (_145_462)::[])
in (_145_464)::_145_463))
in (_145_466)::_145_465))
in (FStar_Syntax_Syntax.mk_Tm_app _145_468 _145_467 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp c.FStar_Syntax_Syntax.flags)))))
end)))
end
end))
end))
in (
# 644 "FStar.TypeChecker.Util.fst"
let _56_860 = lc
in {FStar_Syntax_Syntax.eff_name = _56_860.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _56_860.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _56_860.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))

# 646 "FStar.TypeChecker.Util.fst"
let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> if (FStar_TypeChecker_Rel.is_trivial g0) then begin
(lc, g0)
end else begin
(
# 650 "FStar.TypeChecker.Util.fst"
let _56_867 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _145_488 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _145_487 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _145_488 _145_487)))
end else begin
()
end
in (
# 654 "FStar.TypeChecker.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _56_2 -> (match (_56_2) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _56_873 -> begin
[]
end))))
in (
# 655 "FStar.TypeChecker.Util.fst"
let strengthen = (fun _56_876 -> (match (()) with
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
let xret = (let _145_493 = (let _145_492 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _145_492))
in (FStar_Syntax_Util.comp_set_flags _145_493 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (
# 666 "FStar.TypeChecker.Util.fst"
let lc = (bind env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), (FStar_Syntax_Util.lcomp_of_comp xret)))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (
# 670 "FStar.TypeChecker.Util.fst"
let _56_886 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _145_495 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _145_494 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _145_495 _145_494)))
end else begin
()
end
in (
# 675 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 676 "FStar.TypeChecker.Util.fst"
let _56_892 = (destruct_comp c)
in (match (_56_892) with
| (res_t, wp, wlp) -> begin
(
# 677 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 678 "FStar.TypeChecker.Util.fst"
let us = (let _145_496 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_145_496)::[])
in (
# 679 "FStar.TypeChecker.Util.fst"
let wp = (let _145_505 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assert_p)
in (let _145_504 = (let _145_503 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_502 = (let _145_501 = (let _145_498 = (let _145_497 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason _145_497 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _145_498))
in (let _145_500 = (let _145_499 = (FStar_Syntax_Syntax.as_arg wp)
in (_145_499)::[])
in (_145_501)::_145_500))
in (_145_503)::_145_502))
in (FStar_Syntax_Syntax.mk_Tm_app _145_505 _145_504 None wp.FStar_Syntax_Syntax.pos)))
in (
# 680 "FStar.TypeChecker.Util.fst"
let wlp = (let _145_512 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _145_511 = (let _145_510 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_509 = (let _145_508 = (FStar_Syntax_Syntax.as_arg f)
in (let _145_507 = (let _145_506 = (FStar_Syntax_Syntax.as_arg wlp)
in (_145_506)::[])
in (_145_508)::_145_507))
in (_145_510)::_145_509))
in (FStar_Syntax_Syntax.mk_Tm_app _145_512 _145_511 None wlp.FStar_Syntax_Syntax.pos)))
in (
# 682 "FStar.TypeChecker.Util.fst"
let _56_897 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _145_513 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _145_513))
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
in (let _145_517 = (
# 688 "FStar.TypeChecker.Util.fst"
let _56_900 = lc
in (let _145_516 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _145_515 = if ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _145_514 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _145_514))) then begin
flags
end else begin
[]
end
in {FStar_Syntax_Syntax.eff_name = _145_516; FStar_Syntax_Syntax.res_typ = _56_900.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _145_515; FStar_Syntax_Syntax.comp = strengthen})))
in (_145_517, (
# 691 "FStar.TypeChecker.Util.fst"
let _56_902 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _56_902.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_902.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_902.FStar_TypeChecker_Env.implicits}))))))
end)

# 693 "FStar.TypeChecker.Util.fst"
let record_application_site : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (
# 694 "FStar.TypeChecker.Util.fst"
let comp = (fun _56_908 -> (match (()) with
| () -> begin
(
# 695 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 696 "FStar.TypeChecker.Util.fst"
let res_t = (FStar_Syntax_Util.comp_result c)
in if (((FStar_Syntax_Util.is_trivial_wp c) || (let _145_526 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals _145_526 FStar_Syntax_Const.prims_lid))) || (FStar_Syntax_Syntax.is_teff res_t)) then begin
c
end else begin
(
# 701 "FStar.TypeChecker.Util.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (FStar_TypeChecker_Common.t_unit)))
in (
# 702 "FStar.TypeChecker.Util.fst"
let _56_916 = (strengthen_precondition (Some ((fun _56_912 -> (match (()) with
| () -> begin
"push"
end)))) env e (FStar_Syntax_Util.lcomp_of_comp c) g)
in (match (_56_916) with
| (c, _56_915) -> begin
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
let us = (let _145_530 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_145_530)::[])
in (
# 707 "FStar.TypeChecker.Util.fst"
let xret = (let _145_535 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _145_534 = (let _145_533 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_532 = (let _145_531 = (FStar_Syntax_Syntax.as_arg xexp)
in (_145_531)::[])
in (_145_533)::_145_532))
in (FStar_Syntax_Syntax.mk_Tm_app _145_535 _145_534 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 708 "FStar.TypeChecker.Util.fst"
let xret_comp = (let _145_536 = (mk_comp md_pure res_t xret xret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _145_536))
in (
# 709 "FStar.TypeChecker.Util.fst"
let lc = (let _145_542 = (let _145_541 = (let _145_540 = (strengthen_precondition (Some ((fun _56_923 -> (match (()) with
| () -> begin
"pop"
end)))) env xexp xret_comp g)
in (FStar_All.pipe_left Prims.fst _145_540))
in (Some (x), _145_541))
in (bind env None c _145_542))
in (lc.FStar_Syntax_Syntax.comp ()))))))))
end)))
end))
end))
in (
# 711 "FStar.TypeChecker.Util.fst"
let _56_925 = lc
in {FStar_Syntax_Syntax.eff_name = _56_925.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _56_925.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _56_925.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = comp})))

# 713 "FStar.TypeChecker.Util.fst"
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
let _56_935 = (let _145_550 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _145_549 = (FStar_Syntax_Syntax.bv_to_name y)
in (_145_550, _145_549)))
in (match (_56_935) with
| (xexp, yexp) -> begin
(
# 718 "FStar.TypeChecker.Util.fst"
let us = (let _145_551 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_145_551)::[])
in (
# 719 "FStar.TypeChecker.Util.fst"
let yret = (let _145_556 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _145_555 = (let _145_554 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_553 = (let _145_552 = (FStar_Syntax_Syntax.as_arg yexp)
in (_145_552)::[])
in (_145_554)::_145_553))
in (FStar_Syntax_Syntax.mk_Tm_app _145_556 _145_555 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 720 "FStar.TypeChecker.Util.fst"
let x_eq_y_yret = (let _145_564 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _145_563 = (let _145_562 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_561 = (let _145_560 = (let _145_557 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _145_557))
in (let _145_559 = (let _145_558 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_145_558)::[])
in (_145_560)::_145_559))
in (_145_562)::_145_561))
in (FStar_Syntax_Syntax.mk_Tm_app _145_564 _145_563 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 721 "FStar.TypeChecker.Util.fst"
let forall_y_x_eq_y_yret = (let _145_574 = (FStar_TypeChecker_Env.inst_effect_fun_with (FStar_List.append us us) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _145_573 = (let _145_572 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_571 = (let _145_570 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_569 = (let _145_568 = (let _145_567 = (let _145_566 = (let _145_565 = (FStar_Syntax_Syntax.mk_binder y)
in (_145_565)::[])
in (FStar_Syntax_Util.abs _145_566 x_eq_y_yret None))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _145_567))
in (_145_568)::[])
in (_145_570)::_145_569))
in (_145_572)::_145_571))
in (FStar_Syntax_Syntax.mk_Tm_app _145_574 _145_573 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 722 "FStar.TypeChecker.Util.fst"
let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (
# 723 "FStar.TypeChecker.Util.fst"
let lc = (bind env None (FStar_Syntax_Util.lcomp_of_comp comp) (Some (x), (FStar_Syntax_Util.lcomp_of_comp lc2)))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))

# 726 "FStar.TypeChecker.Util.fst"
let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (
# 727 "FStar.TypeChecker.Util.fst"
let comp = (fun _56_947 -> (match (()) with
| () -> begin
(
# 728 "FStar.TypeChecker.Util.fst"
let _56_963 = (let _145_586 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _145_585 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _145_586 _145_585)))
in (match (_56_963) with
| ((md, _56_950, _56_952), (res_t, wp_then, wlp_then), (_56_959, wp_else, wlp_else)) -> begin
(
# 729 "FStar.TypeChecker.Util.fst"
let us = (let _145_587 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_145_587)::[])
in (
# 730 "FStar.TypeChecker.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _145_607 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _145_606 = (let _145_604 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_603 = (let _145_602 = (FStar_Syntax_Syntax.as_arg g)
in (let _145_601 = (let _145_600 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _145_599 = (let _145_598 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_145_598)::[])
in (_145_600)::_145_599))
in (_145_602)::_145_601))
in (_145_604)::_145_603))
in (let _145_605 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _145_607 _145_606 None _145_605)))))
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
let wp = (let _145_614 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _145_613 = (let _145_612 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_611 = (let _145_610 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _145_609 = (let _145_608 = (FStar_Syntax_Syntax.as_arg wp)
in (_145_608)::[])
in (_145_610)::_145_609))
in (_145_612)::_145_611))
in (FStar_Syntax_Syntax.mk_Tm_app _145_614 _145_613 None wp.FStar_Syntax_Syntax.pos)))
in (
# 737 "FStar.TypeChecker.Util.fst"
let wlp = (let _145_619 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _145_618 = (let _145_617 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_616 = (let _145_615 = (FStar_Syntax_Syntax.as_arg wlp)
in (_145_615)::[])
in (_145_617)::_145_616))
in (FStar_Syntax_Syntax.mk_Tm_app _145_619 _145_618 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end))))
end))
end))
in (let _145_620 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _145_620; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp})))

# 744 "FStar.TypeChecker.Util.fst"
let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (let _145_626 = (let _145_625 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid _145_625))
in (FStar_Syntax_Syntax.fvar _145_626 FStar_Syntax_Syntax.Delta_constant None)))

# 746 "FStar.TypeChecker.Util.fst"
let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (
# 747 "FStar.TypeChecker.Util.fst"
let eff = (FStar_List.fold_left (fun eff _56_985 -> (match (_56_985) with
| (_56_983, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (
# 748 "FStar.TypeChecker.Util.fst"
let bind_cases = (fun _56_988 -> (match (()) with
| () -> begin
(
# 749 "FStar.TypeChecker.Util.fst"
let us = (let _145_637 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_145_637)::[])
in (
# 750 "FStar.TypeChecker.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _145_657 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _145_656 = (let _145_654 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_653 = (let _145_652 = (FStar_Syntax_Syntax.as_arg g)
in (let _145_651 = (let _145_650 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _145_649 = (let _145_648 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_145_648)::[])
in (_145_650)::_145_649))
in (_145_652)::_145_651))
in (_145_654)::_145_653))
in (let _145_655 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _145_657 _145_656 None _145_655)))))
in (
# 752 "FStar.TypeChecker.Util.fst"
let default_case = (
# 753 "FStar.TypeChecker.Util.fst"
let post_k = (let _145_660 = (let _145_658 = (FStar_Syntax_Syntax.null_binder res_t)
in (_145_658)::[])
in (let _145_659 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _145_660 _145_659)))
in (
# 754 "FStar.TypeChecker.Util.fst"
let kwp = (let _145_663 = (let _145_661 = (FStar_Syntax_Syntax.null_binder post_k)
in (_145_661)::[])
in (let _145_662 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _145_663 _145_662)))
in (
# 755 "FStar.TypeChecker.Util.fst"
let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (
# 756 "FStar.TypeChecker.Util.fst"
let wp = (let _145_669 = (let _145_664 = (FStar_Syntax_Syntax.mk_binder post)
in (_145_664)::[])
in (let _145_668 = (let _145_667 = (let _145_665 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Errors.exhaustiveness_check _145_665))
in (let _145_666 = (fvar_const env FStar_Syntax_Const.false_lid)
in (FStar_All.pipe_left _145_667 _145_666)))
in (FStar_Syntax_Util.abs _145_669 _145_668 None)))
in (
# 757 "FStar.TypeChecker.Util.fst"
let wlp = (let _145_672 = (let _145_670 = (FStar_Syntax_Syntax.mk_binder post)
in (_145_670)::[])
in (let _145_671 = (fvar_const env FStar_Syntax_Const.true_lid)
in (FStar_Syntax_Util.abs _145_672 _145_671 None)))
in (
# 758 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (
# 760 "FStar.TypeChecker.Util.fst"
let comp = (FStar_List.fold_right (fun _56_1005 celse -> (match (_56_1005) with
| (g, cthen) -> begin
(
# 761 "FStar.TypeChecker.Util.fst"
let _56_1023 = (let _145_675 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _145_675 celse))
in (match (_56_1023) with
| ((md, _56_1009, _56_1011), (_56_1014, wp_then, wlp_then), (_56_1019, wp_else, wlp_else)) -> begin
(let _145_677 = (ifthenelse md res_t g wp_then wp_else)
in (let _145_676 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _145_677 _145_676 [])))
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
let _56_1031 = (destruct_comp comp)
in (match (_56_1031) with
| (_56_1028, wp, wlp) -> begin
(
# 768 "FStar.TypeChecker.Util.fst"
let wp = (let _145_684 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _145_683 = (let _145_682 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_681 = (let _145_680 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _145_679 = (let _145_678 = (FStar_Syntax_Syntax.as_arg wp)
in (_145_678)::[])
in (_145_680)::_145_679))
in (_145_682)::_145_681))
in (FStar_Syntax_Syntax.mk_Tm_app _145_684 _145_683 None wp.FStar_Syntax_Syntax.pos)))
in (
# 769 "FStar.TypeChecker.Util.fst"
let wlp = (let _145_689 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _145_688 = (let _145_687 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_686 = (let _145_685 = (FStar_Syntax_Syntax.as_arg wlp)
in (_145_685)::[])
in (_145_687)::_145_686))
in (FStar_Syntax_Syntax.mk_Tm_app _145_689 _145_688 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end))))
end))))
end))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))

# 776 "FStar.TypeChecker.Util.fst"
let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (
# 777 "FStar.TypeChecker.Util.fst"
let close = (fun _56_1038 -> (match (()) with
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
let bs = (let _145_710 = (FStar_Syntax_Syntax.mk_binder x)
in (_145_710)::[])
in (
# 784 "FStar.TypeChecker.Util.fst"
let us = (let _145_712 = (let _145_711 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (_145_711)::[])
in (u_res)::_145_712)
in (
# 785 "FStar.TypeChecker.Util.fst"
let wp = (FStar_Syntax_Util.abs bs wp None)
in (let _145_719 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (let _145_718 = (let _145_717 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_716 = (let _145_715 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _145_714 = (let _145_713 = (FStar_Syntax_Syntax.as_arg wp)
in (_145_713)::[])
in (_145_715)::_145_714))
in (_145_717)::_145_716))
in (FStar_Syntax_Syntax.mk_Tm_app _145_719 _145_718 None wp0.FStar_Syntax_Syntax.pos))))))) bvs wp0))
in (
# 788 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 789 "FStar.TypeChecker.Util.fst"
let _56_1055 = (destruct_comp c)
in (match (_56_1055) with
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
let _56_1060 = lc
in {FStar_Syntax_Syntax.eff_name = _56_1060.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _56_1060.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _56_1060.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))

# 797 "FStar.TypeChecker.Util.fst"
let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (
# 798 "FStar.TypeChecker.Util.fst"
let refine = (fun _56_1066 -> (match (()) with
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
(let _145_730 = (let _145_729 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _145_728 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _145_729 _145_728)))
in (FStar_All.failwith _145_730))
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
let ret = (let _145_732 = (let _145_731 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _145_731 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _145_732))
in (
# 813 "FStar.TypeChecker.Util.fst"
let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (
# 814 "FStar.TypeChecker.Util.fst"
let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (
# 816 "FStar.TypeChecker.Util.fst"
let c = (let _145_734 = (let _145_733 = (bind env None (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), eq_ret))
in (_145_733.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _145_734 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
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
let _56_1078 = lc
in {FStar_Syntax_Syntax.eff_name = _56_1078.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _56_1078.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))

# 827 "FStar.TypeChecker.Util.fst"
let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (match ((FStar_TypeChecker_Rel.sub_comp env c c')) with
| None -> begin
(let _145_746 = (let _145_745 = (let _145_744 = (FStar_TypeChecker_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _145_743 = (FStar_TypeChecker_Env.get_range env)
in (_145_744, _145_743)))
in FStar_Syntax_Syntax.Error (_145_745))
in (Prims.raise _145_746))
end
| Some (g) -> begin
(e, c', g)
end))

# 833 "FStar.TypeChecker.Util.fst"
let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match ((let _145_755 = (FStar_Syntax_Subst.compress t)
in _145_755.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_56_1092) -> begin
(match ((let _145_756 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _145_756.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid) -> begin
(
# 838 "FStar.TypeChecker.Util.fst"
let _56_1096 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (
# 839 "FStar.TypeChecker.Util.fst"
let b2t = (let _145_757 = (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar _145_757 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (
# 840 "FStar.TypeChecker.Util.fst"
let lc = (let _145_760 = (let _145_759 = (let _145_758 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _145_758))
in (None, _145_759))
in (bind env (Some (e)) lc _145_760))
in (
# 841 "FStar.TypeChecker.Util.fst"
let e = (let _145_762 = (let _145_761 = (FStar_Syntax_Syntax.as_arg e)
in (_145_761)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _145_762 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (e, lc)))))
end
| _56_1102 -> begin
(e, lc)
end)
end
| _56_1104 -> begin
(e, lc)
end))

# 848 "FStar.TypeChecker.Util.fst"
let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (
# 849 "FStar.TypeChecker.Util.fst"
let gopt = if env.FStar_TypeChecker_Env.use_eq then begin
(let _145_771 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in (_145_771, false))
end else begin
(let _145_772 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in (_145_772, true))
end
in (match (gopt) with
| (None, _56_1112) -> begin
(FStar_TypeChecker_Rel.subtype_fail env lc.FStar_Syntax_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(match ((FStar_TypeChecker_Rel.guard_form g)) with
| FStar_TypeChecker_Common.Trivial -> begin
(
# 857 "FStar.TypeChecker.Util.fst"
let lc = (
# 857 "FStar.TypeChecker.Util.fst"
let _56_1119 = lc
in {FStar_Syntax_Syntax.eff_name = _56_1119.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _56_1119.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _56_1119.FStar_Syntax_Syntax.comp})
in (e, lc, g))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 861 "FStar.TypeChecker.Util.fst"
let g = (
# 861 "FStar.TypeChecker.Util.fst"
let _56_1124 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _56_1124.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_1124.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_1124.FStar_TypeChecker_Env.implicits})
in (
# 862 "FStar.TypeChecker.Util.fst"
let strengthen = (fun _56_1128 -> (match (()) with
| () -> begin
(
# 864 "FStar.TypeChecker.Util.fst"
let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (match ((let _145_775 = (FStar_Syntax_Subst.compress f)
in _145_775.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_56_1131, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _56_1137; FStar_Syntax_Syntax.pos = _56_1135; FStar_Syntax_Syntax.vars = _56_1133}, _56_1142) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
(
# 868 "FStar.TypeChecker.Util.fst"
let lc = (
# 868 "FStar.TypeChecker.Util.fst"
let _56_1145 = lc
in {FStar_Syntax_Syntax.eff_name = _56_1145.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _56_1145.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _56_1145.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| _56_1149 -> begin
(
# 872 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 873 "FStar.TypeChecker.Util.fst"
let _56_1151 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _145_779 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _145_778 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _145_777 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _145_776 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _145_779 _145_778 _145_777 _145_776)))))
end else begin
()
end
in (
# 880 "FStar.TypeChecker.Util.fst"
let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 881 "FStar.TypeChecker.Util.fst"
let _56_1156 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_56_1156) with
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
let us = (let _145_780 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_145_780)::[])
in (
# 887 "FStar.TypeChecker.Util.fst"
let wp = (let _145_785 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ret)
in (let _145_784 = (let _145_783 = (FStar_Syntax_Syntax.as_arg t)
in (let _145_782 = (let _145_781 = (FStar_Syntax_Syntax.as_arg xexp)
in (_145_781)::[])
in (_145_783)::_145_782))
in (FStar_Syntax_Syntax.mk_Tm_app _145_785 _145_784 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)))
in (
# 888 "FStar.TypeChecker.Util.fst"
let cret = (let _145_786 = (mk_comp md t wp wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _145_786))
in (
# 889 "FStar.TypeChecker.Util.fst"
let guard = if apply_guard then begin
(let _145_788 = (let _145_787 = (FStar_Syntax_Syntax.as_arg xexp)
in (_145_787)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _145_788 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end else begin
f
end
in (
# 890 "FStar.TypeChecker.Util.fst"
let _56_1167 = (let _145_796 = (FStar_All.pipe_left (fun _145_793 -> Some (_145_793)) (FStar_TypeChecker_Errors.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _145_795 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _145_794 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _145_796 _145_795 e cret _145_794))))
in (match (_56_1167) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(
# 894 "FStar.TypeChecker.Util.fst"
let x = (
# 894 "FStar.TypeChecker.Util.fst"
let _56_1168 = x
in {FStar_Syntax_Syntax.ppname = _56_1168.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_1168.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (
# 895 "FStar.TypeChecker.Util.fst"
let c = (let _145_798 = (let _145_797 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _145_797))
in (bind env (Some (e)) _145_798 (Some (x), eq_ret)))
in (
# 896 "FStar.TypeChecker.Util.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 897 "FStar.TypeChecker.Util.fst"
let _56_1173 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _145_799 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _145_799))
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
let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _56_3 -> (match (_56_3) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _56_1179 -> begin
[]
end))))
in (
# 901 "FStar.TypeChecker.Util.fst"
let lc = (
# 901 "FStar.TypeChecker.Util.fst"
let _56_1181 = lc
in (let _145_801 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _145_801; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (
# 902 "FStar.TypeChecker.Util.fst"
let g = (
# 902 "FStar.TypeChecker.Util.fst"
let _56_1184 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _56_1184.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_1184.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_1184.FStar_TypeChecker_Env.implicits})
in (e, lc, g))))))
end)
end)))

# 905 "FStar.TypeChecker.Util.fst"
let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (
# 906 "FStar.TypeChecker.Util.fst"
let mk_post_type = (fun res_t ens -> (
# 907 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _145_813 = (let _145_812 = (let _145_811 = (let _145_810 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _145_810))
in (_145_811)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _145_812 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _145_813))))
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
| (req, _56_1212)::(ens, _56_1207)::_56_1204 -> begin
(let _145_819 = (let _145_816 = (norm req)
in Some (_145_816))
in (let _145_818 = (let _145_817 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _145_817))
in (_145_819, _145_818)))
end
| _56_1216 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 923 "FStar.TypeChecker.Util.fst"
let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (wp, _56_1227)::(wlp, _56_1222)::_56_1219 -> begin
(
# 926 "FStar.TypeChecker.Util.fst"
let _56_1233 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (_56_1233) with
| (us_r, _56_1232) -> begin
(
# 927 "FStar.TypeChecker.Util.fst"
let _56_1237 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (_56_1237) with
| (us_e, _56_1236) -> begin
(
# 928 "FStar.TypeChecker.Util.fst"
let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (
# 929 "FStar.TypeChecker.Util.fst"
let as_req = (let _145_821 = (let _145_820 = (FStar_Ident.set_lid_range FStar_Syntax_Const.as_requires r)
in (FStar_Syntax_Syntax.fvar _145_820 FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _145_821 us_r))
in (
# 930 "FStar.TypeChecker.Util.fst"
let as_ens = (let _145_823 = (let _145_822 = (FStar_Ident.set_lid_range FStar_Syntax_Const.as_ensures r)
in (FStar_Syntax_Syntax.fvar _145_822 FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _145_823 us_e))
in (
# 931 "FStar.TypeChecker.Util.fst"
let req = (let _145_826 = (let _145_825 = (let _145_824 = (FStar_Syntax_Syntax.as_arg wp)
in (_145_824)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.imp_tag)))::_145_825)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _145_826 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 932 "FStar.TypeChecker.Util.fst"
let ens = (let _145_829 = (let _145_828 = (let _145_827 = (FStar_Syntax_Syntax.as_arg wlp)
in (_145_827)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.imp_tag)))::_145_828)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _145_829 None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _145_833 = (let _145_830 = (norm req)
in Some (_145_830))
in (let _145_832 = (let _145_831 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm _145_831))
in (_145_833, _145_832))))))))
end))
end))
end
| _56_1244 -> begin
(FStar_All.failwith "Impossible")
end))
end
end)
end)))

# 942 "FStar.TypeChecker.Util.fst"
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
let _56_1255 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_56_1255) with
| (bs, c) -> begin
(
# 949 "FStar.TypeChecker.Util.fst"
let rec aux = (fun subst _56_4 -> (match (_56_4) with
| (x, Some (FStar_Syntax_Syntax.Implicit (dot)))::rest -> begin
(
# 951 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 952 "FStar.TypeChecker.Util.fst"
let _56_1271 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t)
in (match (_56_1271) with
| (v, _56_1269, g) -> begin
(
# 953 "FStar.TypeChecker.Util.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, v)))::subst
in (
# 954 "FStar.TypeChecker.Util.fst"
let _56_1277 = (aux subst rest)
in (match (_56_1277) with
| (args, bs, subst, g') -> begin
(let _145_844 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((v, Some (FStar_Syntax_Syntax.Implicit (dot))))::args, bs, subst, _145_844))
end)))
end)))
end
| bs -> begin
([], bs, subst, FStar_TypeChecker_Rel.trivial_guard)
end))
in (
# 958 "FStar.TypeChecker.Util.fst"
let _56_1283 = (aux [] bs)
in (match (_56_1283) with
| (args, bs, subst, guard) -> begin
(match ((args, bs)) with
| ([], _56_1286) -> begin
(e, torig, guard)
end
| (_56_1289, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end
| _56_1293 -> begin
(
# 969 "FStar.TypeChecker.Util.fst"
let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _56_1296 -> begin
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
| _56_1301 -> begin
(e, t, FStar_TypeChecker_Rel.trivial_guard)
end)
end))

# 983 "FStar.TypeChecker.Util.fst"
let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(
# 985 "FStar.TypeChecker.Util.fst"
let s = (let _145_850 = (let _145_849 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _145_849))
in (FStar_All.pipe_right _145_850 FStar_Util.set_elements))
in (
# 986 "FStar.TypeChecker.Util.fst"
let r = (let _145_851 = (FStar_TypeChecker_Env.get_range env)
in Some (_145_851))
in (
# 987 "FStar.TypeChecker.Util.fst"
let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (
# 988 "FStar.TypeChecker.Util.fst"
let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (
# 989 "FStar.TypeChecker.Util.fst"
let _56_1308 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _145_856 = (let _145_853 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _145_853))
in (let _145_855 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _145_854 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _145_856 _145_855 _145_854))))
end else begin
()
end
in (
# 991 "FStar.TypeChecker.Util.fst"
let _56_1310 = (FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))))
in u_name))))))
in u_names)))
end)

# 995 "FStar.TypeChecker.Util.fst"
let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t -> (
# 996 "FStar.TypeChecker.Util.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (
# 997 "FStar.TypeChecker.Util.fst"
let univs = (FStar_Syntax_Free.univs t)
in (
# 998 "FStar.TypeChecker.Util.fst"
let _56_1318 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _145_865 = (let _145_864 = (let _145_863 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _145_863 (FStar_List.map (fun u -> (let _145_862 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _145_862 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _145_864 (FStar_String.concat ", ")))
in (FStar_Util.print1 "univs to gen : %s\n" _145_865))
end else begin
()
end
in (
# 1002 "FStar.TypeChecker.Util.fst"
let gen = (gen_univs env univs)
in (
# 1003 "FStar.TypeChecker.Util.fst"
let _56_1321 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _145_866 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _145_866))
end else begin
()
end
in (
# 1005 "FStar.TypeChecker.Util.fst"
let ts = (FStar_Syntax_Subst.close_univ_vars gen t)
in (gen, ts))))))))

# 1008 "FStar.TypeChecker.Util.fst"
let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> if (let _145_872 = (FStar_Util.for_all (fun _56_1329 -> (match (_56_1329) with
| (_56_1327, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _145_872)) then begin
None
end else begin
(
# 1012 "FStar.TypeChecker.Util.fst"
let norm = (fun c -> (
# 1013 "FStar.TypeChecker.Util.fst"
let _56_1332 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _145_875 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _145_875))
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
let _56_1335 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _145_876 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _145_876))
end else begin
()
end
in c))))
in (
# 1021 "FStar.TypeChecker.Util.fst"
let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (
# 1022 "FStar.TypeChecker.Util.fst"
let gen_uvars = (fun uvs -> (let _145_879 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _145_879 FStar_Util.set_elements)))
in (
# 1023 "FStar.TypeChecker.Util.fst"
let _56_1352 = (let _145_881 = (FStar_All.pipe_right ecs (FStar_List.map (fun _56_1342 -> (match (_56_1342) with
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
in (FStar_All.pipe_right _145_881 FStar_List.unzip))
in (match (_56_1352) with
| (univs, uvars) -> begin
(
# 1033 "FStar.TypeChecker.Util.fst"
let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (
# 1034 "FStar.TypeChecker.Util.fst"
let gen_univs = (gen_univs env univs)
in (
# 1035 "FStar.TypeChecker.Util.fst"
let _56_1356 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end else begin
()
end
in (
# 1037 "FStar.TypeChecker.Util.fst"
let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _56_1361 -> (match (_56_1361) with
| (uvs, e, c) -> begin
(
# 1038 "FStar.TypeChecker.Util.fst"
let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _56_1364 -> (match (_56_1364) with
| (u, k) -> begin
(match ((FStar_Unionfind.find u)) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(a, Some (FStar_Syntax_Syntax.imp_tag))
end
| FStar_Syntax_Syntax.Fixed (_56_1398) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _56_1401 -> begin
(
# 1044 "FStar.TypeChecker.Util.fst"
let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (
# 1045 "FStar.TypeChecker.Util.fst"
let _56_1405 = (FStar_Syntax_Util.arrow_formals k)
in (match (_56_1405) with
| (bs, kres) -> begin
(
# 1046 "FStar.TypeChecker.Util.fst"
let a = (let _145_887 = (let _145_886 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _145_885 -> Some (_145_885)) _145_886))
in (FStar_Syntax_Syntax.new_bv _145_887 kres))
in (
# 1047 "FStar.TypeChecker.Util.fst"
let t = (let _145_891 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _145_890 = (let _145_889 = (let _145_888 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _145_888))
in Some (_145_889))
in (FStar_Syntax_Util.abs bs _145_891 _145_890)))
in (
# 1048 "FStar.TypeChecker.Util.fst"
let _56_1408 = (FStar_Syntax_Util.set_uvar u t)
in (a, Some (FStar_Syntax_Syntax.imp_tag)))))
end)))
end)
end))))
in (
# 1052 "FStar.TypeChecker.Util.fst"
let _56_1432 = (match (tvars) with
| [] -> begin
(e, c)
end
| _56_1413 -> begin
(
# 1058 "FStar.TypeChecker.Util.fst"
let _56_1416 = (e, c)
in (match (_56_1416) with
| (e0, c0) -> begin
(
# 1059 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.BetaUVars)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::[]) env c)
in (
# 1060 "FStar.TypeChecker.Util.fst"
let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.BetaUVars)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::[]) env e)
in (
# 1062 "FStar.TypeChecker.Util.fst"
let t = (match ((let _145_892 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _145_892.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(
# 1064 "FStar.TypeChecker.Util.fst"
let _56_1425 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (_56_1425) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| _56_1427 -> begin
(FStar_Syntax_Util.arrow tvars c)
end)
in (
# 1069 "FStar.TypeChecker.Util.fst"
let e' = (FStar_Syntax_Util.abs tvars e None)
in (let _145_893 = (FStar_Syntax_Syntax.mk_Total t)
in (e', _145_893))))))
end))
end)
in (match (_56_1432) with
| (e, c) -> begin
(gen_univs, e, c)
end)))
end))))
in Some (ecs)))))
end)))))
end)

# 1074 "FStar.TypeChecker.Util.fst"
let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> (
# 1075 "FStar.TypeChecker.Util.fst"
let _56_1442 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _145_900 = (let _145_899 = (FStar_List.map (fun _56_1441 -> (match (_56_1441) with
| (lb, _56_1438, _56_1440) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _145_899 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _145_900))
end else begin
()
end
in (match ((let _145_902 = (FStar_All.pipe_right lecs (FStar_List.map (fun _56_1448 -> (match (_56_1448) with
| (_56_1445, e, c) -> begin
(e, c)
end))))
in (gen env _145_902))) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun _56_1453 -> (match (_56_1453) with
| (l, t, c) -> begin
(l, [], t, c)
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _56_1461 _56_1465 -> (match ((_56_1461, _56_1465)) with
| ((l, _56_1458, _56_1460), (us, e, c)) -> begin
(
# 1082 "FStar.TypeChecker.Util.fst"
let _56_1466 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _145_908 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _145_907 = (FStar_Syntax_Print.lbname_to_string l)
in (let _145_906 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.print3 "(%s) Generalized %s to %s\n" _145_908 _145_907 _145_906))))
end else begin
()
end
in (l, us, e, c))
end)) lecs ecs)
end)))

# 1095 "FStar.TypeChecker.Util.fst"
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
(let _145_924 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _145_923 -> Some (_145_923)) _145_924))
end)
end)
in (
# 1103 "FStar.TypeChecker.Util.fst"
let is_var = (fun e -> (match ((let _145_927 = (FStar_Syntax_Subst.compress e)
in _145_927.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (_56_1483) -> begin
true
end
| _56_1486 -> begin
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
let _56_1493 = x
in {FStar_Syntax_Syntax.ppname = _56_1493.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_1493.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| _56_1496 -> begin
(
# 1110 "FStar.TypeChecker.Util.fst"
let _56_1497 = e
in (let _145_932 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _56_1497.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _145_932; FStar_Syntax_Syntax.pos = _56_1497.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _56_1497.FStar_Syntax_Syntax.vars}))
end)))
in (
# 1111 "FStar.TypeChecker.Util.fst"
let env = (
# 1111 "FStar.TypeChecker.Util.fst"
let _56_1499 = env
in (let _145_933 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _56_1499.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _56_1499.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _56_1499.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _56_1499.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _56_1499.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _56_1499.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _56_1499.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _56_1499.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _56_1499.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _56_1499.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _56_1499.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _56_1499.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _56_1499.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _56_1499.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _56_1499.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _145_933; FStar_TypeChecker_Env.is_iface = _56_1499.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _56_1499.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _56_1499.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _56_1499.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _56_1499.FStar_TypeChecker_Env.use_bv_sorts}))
in (match ((check env t1 t2)) with
| None -> begin
(let _145_937 = (let _145_936 = (let _145_935 = (FStar_TypeChecker_Errors.expected_expression_of_type env t2 e t1)
in (let _145_934 = (FStar_TypeChecker_Env.get_range env)
in (_145_935, _145_934)))
in FStar_Syntax_Syntax.Error (_145_936))
in (Prims.raise _145_937))
end
| Some (g) -> begin
(
# 1115 "FStar.TypeChecker.Util.fst"
let _56_1505 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_938 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _145_938))
end else begin
()
end
in (let _145_939 = (decorate e t2)
in (_145_939, g)))
end)))))))

# 1120 "FStar.TypeChecker.Util.fst"
let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (
# 1121 "FStar.TypeChecker.Util.fst"
let discharge = (fun g -> (
# 1122 "FStar.TypeChecker.Util.fst"
let _56_1512 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (
# 1124 "FStar.TypeChecker.Util.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _145_949 = (discharge g)
in (let _145_948 = (lc.FStar_Syntax_Syntax.comp ())
in (_145_949, _145_948)))
end else begin
(
# 1127 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 1128 "FStar.TypeChecker.Util.fst"
let steps = (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.DeltaComp)::[]
in (
# 1129 "FStar.TypeChecker.Util.fst"
let c = (let _145_950 = (FStar_TypeChecker_Normalize.normalize_comp steps env c)
in (FStar_All.pipe_right _145_950 FStar_Syntax_Util.comp_to_comp_typ))
in (
# 1130 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 1131 "FStar.TypeChecker.Util.fst"
let _56_1523 = (destruct_comp c)
in (match (_56_1523) with
| (t, wp, _56_1522) -> begin
(
# 1132 "FStar.TypeChecker.Util.fst"
let vc = (let _145_958 = (let _145_952 = (let _145_951 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_145_951)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _145_952 env md md.FStar_Syntax_Syntax.trivial))
in (let _145_957 = (let _145_955 = (FStar_Syntax_Syntax.as_arg t)
in (let _145_954 = (let _145_953 = (FStar_Syntax_Syntax.as_arg wp)
in (_145_953)::[])
in (_145_955)::_145_954))
in (let _145_956 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk_Tm_app _145_958 _145_957 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _145_956))))
in (
# 1133 "FStar.TypeChecker.Util.fst"
let _56_1525 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _145_959 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _145_959))
end else begin
()
end
in (
# 1135 "FStar.TypeChecker.Util.fst"
let g = (let _145_960 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _145_960))
in (let _145_962 = (discharge g)
in (let _145_961 = (FStar_Syntax_Syntax.mk_Comp c)
in (_145_962, _145_961))))))
end))))))
end)))

# 1141 "FStar.TypeChecker.Util.fst"
let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (
# 1142 "FStar.TypeChecker.Util.fst"
let short_bin_op = (fun f _56_5 -> (match (_56_5) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (fst, _56_1536)::[] -> begin
(f fst)
end
| _56_1540 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (
# 1147 "FStar.TypeChecker.Util.fst"
let op_and_e = (fun e -> (let _145_983 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _145_983 (fun _145_982 -> FStar_TypeChecker_Common.NonTrivial (_145_982)))))
in (
# 1148 "FStar.TypeChecker.Util.fst"
let op_or_e = (fun e -> (let _145_988 = (let _145_986 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _145_986))
in (FStar_All.pipe_right _145_988 (fun _145_987 -> FStar_TypeChecker_Common.NonTrivial (_145_987)))))
in (
# 1149 "FStar.TypeChecker.Util.fst"
let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _145_991 -> FStar_TypeChecker_Common.NonTrivial (_145_991))))
in (
# 1150 "FStar.TypeChecker.Util.fst"
let op_or_t = (fun t -> (let _145_995 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _145_995 (fun _145_994 -> FStar_TypeChecker_Common.NonTrivial (_145_994)))))
in (
# 1151 "FStar.TypeChecker.Util.fst"
let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _145_998 -> FStar_TypeChecker_Common.NonTrivial (_145_998))))
in (
# 1153 "FStar.TypeChecker.Util.fst"
let short_op_ite = (fun _56_6 -> (match (_56_6) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (guard, _56_1555)::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| _then::(guard, _56_1560)::[] -> begin
(let _145_1002 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _145_1002 (fun _145_1001 -> FStar_TypeChecker_Common.NonTrivial (_145_1001))))
end
| _56_1565 -> begin
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
in (match ((FStar_Util.find_map table (fun _56_1573 -> (match (_56_1573) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _145_1035 = (mk seen_args)
in Some (_145_1035))
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
| _56_1578 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))

# 1175 "FStar.TypeChecker.Util.fst"
let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (match ((let _145_1038 = (FStar_Syntax_Util.un_uinst l)
in _145_1038.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| _56_1583 -> begin
false
end))

# 1196 "FStar.TypeChecker.Util.fst"
let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (
# 1197 "FStar.TypeChecker.Util.fst"
let pos = (fun bs -> (match (bs) with
| (hd, _56_1592)::_56_1589 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| _56_1596 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| (_56_1600, Some (FStar_Syntax_Syntax.Implicit (_56_1602)))::_56_1598 -> begin
bs
end
| _56_1608 -> begin
(match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
bs
end
| Some (t) -> begin
(match ((let _145_1045 = (FStar_Syntax_Subst.compress t)
in _145_1045.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', _56_1614) -> begin
(match ((FStar_Util.prefix_until (fun _56_7 -> (match (_56_7) with
| (_56_1619, Some (FStar_Syntax_Syntax.Implicit (_56_1621))) -> begin
false
end
| _56_1626 -> begin
true
end)) bs')) with
| None -> begin
bs
end
| Some ([], _56_1630, _56_1632) -> begin
bs
end
| Some (imps, _56_1637, _56_1639) -> begin
if (FStar_All.pipe_right imps (FStar_Util.for_all (fun _56_1645 -> (match (_56_1645) with
| (x, _56_1644) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end)))) then begin
(
# 1213 "FStar.TypeChecker.Util.fst"
let r = (pos bs)
in (
# 1214 "FStar.TypeChecker.Util.fst"
let imps = (FStar_All.pipe_right imps (FStar_List.map (fun _56_1649 -> (match (_56_1649) with
| (x, i) -> begin
(let _145_1049 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in (_145_1049, i))
end))))
in (FStar_List.append imps bs)))
end else begin
bs
end
end)
end
| _56_1652 -> begin
bs
end)
end)
end)))




