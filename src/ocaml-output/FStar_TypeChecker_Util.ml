
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
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 146 "FStar.TypeChecker.Util.fst"
let _63_94 = if (univ_vars <> []) then begin
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
let _63_104 = (FStar_Syntax_Util.type_u ())
in (match (_63_104) with
| (k, _63_103) -> begin
(
# 151 "FStar.TypeChecker.Util.fst"
let t = (let _148_60 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right _148_60 Prims.fst))
in ((
# 152 "FStar.TypeChecker.Util.fst"
let _63_106 = a
in {FStar_Syntax_Syntax.ppname = _63_106.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_106.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), false))
end))
end
| _63_109 -> begin
(a, true)
end))
in (
# 155 "FStar.TypeChecker.Util.fst"
let rec aux = (fun vars e -> (
# 156 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, _63_116) -> begin
(aux vars e)
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _63_122) -> begin
(t, true)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _63_128) -> begin
(
# 162 "FStar.TypeChecker.Util.fst"
let _63_147 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _63_134 _63_137 -> (match ((_63_134, _63_137)) with
| ((scope, bs, check), (a, imp)) -> begin
(
# 163 "FStar.TypeChecker.Util.fst"
let _63_140 = (mk_binder scope a)
in (match (_63_140) with
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
in (match (_63_147) with
| (scope, bs, check) -> begin
(
# 170 "FStar.TypeChecker.Util.fst"
let _63_150 = (aux scope body)
in (match (_63_150) with
| (res, check_res) -> begin
(
# 171 "FStar.TypeChecker.Util.fst"
let c = (FStar_Syntax_Util.ml_comp res r)
in (
# 172 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Util.arrow bs c)
in (
# 173 "FStar.TypeChecker.Util.fst"
let _63_153 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _148_68 = (FStar_Range.string_of_range r)
in (let _148_67 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _148_68 _148_67)))
end else begin
()
end
in (t, (check_res || check)))))
end))
end))
end
| _63_156 -> begin
(let _148_70 = (let _148_69 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _148_69 Prims.fst))
in (_148_70, false))
end)))
in (
# 178 "FStar.TypeChecker.Util.fst"
let _63_159 = (let _148_71 = (t_binders env)
in (aux _148_71 e))
in (match (_63_159) with
| (t, b) -> begin
([], t, b)
end))))))
end
| _63_161 -> begin
(
# 182 "FStar.TypeChecker.Util.fst"
let _63_164 = (FStar_Syntax_Subst.open_univ_vars univ_vars t)
in (match (_63_164) with
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
| FStar_Syntax_Syntax.Pat_dot_term (x, _63_177) -> begin
(
# 211 "FStar.TypeChecker.Util.fst"
let _63_183 = (FStar_Syntax_Util.type_u ())
in (match (_63_183) with
| (k, _63_182) -> begin
(
# 212 "FStar.TypeChecker.Util.fst"
let t = (new_uvar env k)
in (
# 213 "FStar.TypeChecker.Util.fst"
let x = (
# 213 "FStar.TypeChecker.Util.fst"
let _63_185 = x
in {FStar_Syntax_Syntax.ppname = _63_185.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_185.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (
# 214 "FStar.TypeChecker.Util.fst"
let _63_190 = (let _148_84 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _148_84 t))
in (match (_63_190) with
| (e, u) -> begin
(
# 215 "FStar.TypeChecker.Util.fst"
let p = (
# 215 "FStar.TypeChecker.Util.fst"
let _63_191 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, e)); FStar_Syntax_Syntax.ty = _63_191.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _63_191.FStar_Syntax_Syntax.p})
in ([], [], [], env, e, p))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 219 "FStar.TypeChecker.Util.fst"
let _63_199 = (FStar_Syntax_Util.type_u ())
in (match (_63_199) with
| (t, _63_198) -> begin
(
# 220 "FStar.TypeChecker.Util.fst"
let x = (
# 220 "FStar.TypeChecker.Util.fst"
let _63_200 = x
in (let _148_85 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _63_200.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_200.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_85}))
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
let _63_210 = (FStar_Syntax_Util.type_u ())
in (match (_63_210) with
| (t, _63_209) -> begin
(
# 227 "FStar.TypeChecker.Util.fst"
let x = (
# 227 "FStar.TypeChecker.Util.fst"
let _63_211 = x
in (let _148_86 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _63_211.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_211.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_86}))
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
let _63_244 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _63_226 _63_229 -> (match ((_63_226, _63_229)) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(
# 234 "FStar.TypeChecker.Util.fst"
let _63_236 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_63_236) with
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
in (match (_63_244) with
| (b, a, w, env, args, pats) -> begin
(
# 238 "FStar.TypeChecker.Util.fst"
let e = (let _148_93 = (let _148_92 = (let _148_91 = (let _148_90 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (let _148_89 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app _148_90 _148_89 None p.FStar_Syntax_Syntax.p)))
in (_148_91, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))
in FStar_Syntax_Syntax.Tm_meta (_148_92))
in (FStar_Syntax_Syntax.mk _148_93 None p.FStar_Syntax_Syntax.p))
in (let _148_96 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _148_95 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _148_94 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in (_148_96, _148_95, _148_94, env, e, (
# 244 "FStar.TypeChecker.Util.fst"
let _63_246 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _63_246.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _63_246.FStar_Syntax_Syntax.p}))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (_63_249) -> begin
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
let pats = (FStar_List.map (fun _63_264 -> (match (_63_264) with
| (p, imp) -> begin
(let _148_108 = (elaborate_pat env p)
in (_148_108, imp))
end)) pats)
in (
# 256 "FStar.TypeChecker.Util.fst"
let _63_269 = (FStar_TypeChecker_Env.lookup_datacon env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_63_269) with
| (_63_267, t) -> begin
(
# 257 "FStar.TypeChecker.Util.fst"
let _63_273 = (FStar_Syntax_Util.arrow_formals t)
in (match (_63_273) with
| (f, _63_272) -> begin
(
# 258 "FStar.TypeChecker.Util.fst"
let rec aux = (fun formals pats -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _63_284::_63_282) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))))
end
| (_63_290::_63_288, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun _63_296 -> (match (_63_296) with
| (t, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(
# 264 "FStar.TypeChecker.Util.fst"
let a = (let _148_115 = (let _148_114 = (FStar_Syntax_Syntax.range_of_bv t)
in Some (_148_114))
in (FStar_Syntax_Syntax.new_bv _148_115 FStar_Syntax_Syntax.tun))
in (
# 265 "FStar.TypeChecker.Util.fst"
let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (let _148_116 = (maybe_dot inaccessible a r)
in (_148_116, true))))
end
| _63_303 -> begin
(let _148_120 = (let _148_119 = (let _148_118 = (let _148_117 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _148_117))
in (_148_118, (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in FStar_Syntax_Syntax.Error (_148_119))
in (Prims.raise _148_120))
end)
end))))
end
| (f::formals', (p, p_imp)::pats') -> begin
(match (f) with
| (_63_314, Some (FStar_Syntax_Syntax.Implicit (_63_316))) when p_imp -> begin
(let _148_121 = (aux formals' pats')
in ((p, true))::_148_121)
end
| (_63_321, Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(
# 277 "FStar.TypeChecker.Util.fst"
let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (
# 278 "FStar.TypeChecker.Util.fst"
let p = (maybe_dot inaccessible a (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
in (let _148_122 = (aux formals' pats)
in ((p, true))::_148_122)))
end
| (_63_329, imp) -> begin
(let _148_125 = (let _148_123 = (FStar_Syntax_Syntax.is_implicit imp)
in (p, _148_123))
in (let _148_124 = (aux formals' pats')
in (_148_125)::_148_124))
end)
end))
in (
# 284 "FStar.TypeChecker.Util.fst"
let _63_332 = p
in (let _148_128 = (let _148_127 = (let _148_126 = (aux f pats)
in (fv, _148_126))
in FStar_Syntax_Syntax.Pat_cons (_148_127))
in {FStar_Syntax_Syntax.v = _148_128; FStar_Syntax_Syntax.ty = _63_332.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _63_332.FStar_Syntax_Syntax.p})))
end))
end)))
end
| _63_335 -> begin
p
end)))
in (
# 288 "FStar.TypeChecker.Util.fst"
let one_pat = (fun allow_wc_dependence env p -> (
# 289 "FStar.TypeChecker.Util.fst"
let p = (elaborate_pat env p)
in (
# 290 "FStar.TypeChecker.Util.fst"
let _63_347 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_63_347) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))) with
| Some (x) -> begin
(let _148_137 = (let _148_136 = (let _148_135 = (FStar_TypeChecker_Errors.nonlinear_pattern_variable x)
in (_148_135, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_148_136))
in (Prims.raise _148_137))
end
| _63_351 -> begin
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
let _63_367 = (one_pat false env q)
in (match (_63_367) with
| (b, a, _63_364, te, q) -> begin
(
# 303 "FStar.TypeChecker.Util.fst"
let _63_382 = (FStar_List.fold_right (fun p _63_372 -> (match (_63_372) with
| (w, args, pats) -> begin
(
# 304 "FStar.TypeChecker.Util.fst"
let _63_378 = (one_pat false env p)
in (match (_63_378) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv FStar_Syntax_Syntax.bv_eq a a'))) then begin
(let _148_147 = (let _148_146 = (let _148_145 = (FStar_TypeChecker_Errors.disjunctive_pattern_vars a a')
in (let _148_144 = (FStar_TypeChecker_Env.get_range env)
in (_148_145, _148_144)))
in FStar_Syntax_Syntax.Error (_148_146))
in (Prims.raise _148_147))
end else begin
(let _148_149 = (let _148_148 = (FStar_Syntax_Syntax.as_arg arg)
in (_148_148)::args)
in ((FStar_List.append w' w), _148_149, (p)::pats))
end
end))
end)) pats ([], [], []))
in (match (_63_382) with
| (w, args, pats) -> begin
(let _148_151 = (let _148_150 = (FStar_Syntax_Syntax.as_arg te)
in (_148_150)::args)
in ((FStar_List.append b w), _148_151, (
# 309 "FStar.TypeChecker.Util.fst"
let _63_383 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((q)::pats); FStar_Syntax_Syntax.ty = _63_383.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _63_383.FStar_Syntax_Syntax.p})))
end))
end))
end
| _63_386 -> begin
(
# 312 "FStar.TypeChecker.Util.fst"
let _63_394 = (one_pat true env p)
in (match (_63_394) with
| (b, _63_389, _63_391, arg, p) -> begin
(let _148_153 = (let _148_152 = (FStar_Syntax_Syntax.as_arg arg)
in (_148_152)::[])
in (b, _148_153, p))
end))
end))
in (
# 315 "FStar.TypeChecker.Util.fst"
let _63_398 = (top_level_pat_as_args env p)
in (match (_63_398) with
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
| (_63_412, FStar_Syntax_Syntax.Tm_uinst (e, _63_415)) -> begin
(aux p e)
end
| (FStar_Syntax_Syntax.Pat_constant (_63_420), FStar_Syntax_Syntax.Tm_constant (_63_423)) -> begin
(let _148_168 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v _148_168))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(
# 331 "FStar.TypeChecker.Util.fst"
let _63_431 = if (not ((FStar_Syntax_Syntax.bv_eq x y))) then begin
(let _148_171 = (let _148_170 = (FStar_Syntax_Print.bv_to_string x)
in (let _148_169 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _148_170 _148_169)))
in (FStar_All.failwith _148_171))
end else begin
()
end
in (
# 333 "FStar.TypeChecker.Util.fst"
let _63_433 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _148_173 = (FStar_Syntax_Print.bv_to_string x)
in (let _148_172 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _148_173 _148_172)))
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
let _63_436 = x
in {FStar_Syntax_Syntax.ppname = _63_436.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_436.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x)) s.FStar_Syntax_Syntax.n)))))
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(
# 340 "FStar.TypeChecker.Util.fst"
let _63_444 = if (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation) then begin
(let _148_176 = (let _148_175 = (FStar_Syntax_Print.bv_to_string x)
in (let _148_174 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _148_175 _148_174)))
in (FStar_All.failwith _148_176))
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
let _63_447 = x
in {FStar_Syntax_Syntax.ppname = _63_447.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_447.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x)) s.FStar_Syntax_Syntax.n))))
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _63_452), _63_456) -> begin
(
# 347 "FStar.TypeChecker.Util.fst"
let s = (force_sort e)
in (
# 348 "FStar.TypeChecker.Util.fst"
let x = (
# 348 "FStar.TypeChecker.Util.fst"
let _63_459 = x
in {FStar_Syntax_Syntax.ppname = _63_459.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_459.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
(
# 352 "FStar.TypeChecker.Util.fst"
let _63_469 = if (not ((FStar_Syntax_Syntax.fv_eq fv fv'))) then begin
(let _148_177 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _148_177))
end else begin
()
end
in (let _148_178 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv', []))) _148_178)))
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
(
# 359 "FStar.TypeChecker.Util.fst"
let _63_512 = if (let _148_179 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right _148_179 Prims.op_Negation)) then begin
(let _148_180 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _148_180))
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
(let _148_187 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev matched_pats)))) _148_187))
end
| (arg::args, (argpat, _63_528)::argpats) -> begin
(match ((arg, argpat.FStar_Syntax_Syntax.v)) with
| ((e, Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (_63_538)) -> begin
(
# 368 "FStar.TypeChecker.Util.fst"
let x = (let _148_188 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _148_188))
in (
# 369 "FStar.TypeChecker.Util.fst"
let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((e, imp), _63_547) -> begin
(
# 373 "FStar.TypeChecker.Util.fst"
let pat = (let _148_190 = (aux argpat e)
in (let _148_189 = (FStar_Syntax_Syntax.is_implicit imp)
in (_148_190, _148_189)))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _63_551 -> begin
(let _148_193 = (let _148_192 = (FStar_Syntax_Print.pat_to_string p)
in (let _148_191 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _148_192 _148_191)))
in (FStar_All.failwith _148_193))
end))
in (match_args [] args argpats))))
end
| _63_553 -> begin
(let _148_198 = (let _148_197 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (let _148_196 = (FStar_Syntax_Print.pat_to_string qq)
in (let _148_195 = (let _148_194 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right _148_194 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _148_197 _148_196 _148_195))))
in (FStar_All.failwith _148_198))
end))))
in (match ((p.FStar_Syntax_Syntax.v, exps)) with
| (FStar_Syntax_Syntax.Pat_disj (ps), _63_557) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(
# 386 "FStar.TypeChecker.Util.fst"
let ps = (FStar_List.map2 aux ps exps)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj (ps)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p))
end
| (_63_561, e::[]) -> begin
(aux p e)
end
| _63_566 -> begin
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
let pat_as_arg = (fun _63_574 -> (match (_63_574) with
| (p, i) -> begin
(
# 399 "FStar.TypeChecker.Util.fst"
let _63_577 = (decorated_pattern_as_term p)
in (match (_63_577) with
| (vars, te) -> begin
(let _148_206 = (let _148_205 = (FStar_Syntax_Syntax.as_implicit i)
in (te, _148_205))
in (vars, _148_206))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_63_579) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _148_207 = (mk (FStar_Syntax_Syntax.Tm_constant (c)))
in ([], _148_207))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(let _148_208 = (mk (FStar_Syntax_Syntax.Tm_name (x)))
in ((x)::[], _148_208))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 413 "FStar.TypeChecker.Util.fst"
let _63_592 = (let _148_209 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _148_209 FStar_List.unzip))
in (match (_63_592) with
| (vars, args) -> begin
(
# 414 "FStar.TypeChecker.Util.fst"
let vars = (FStar_List.flatten vars)
in (let _148_213 = (let _148_212 = (let _148_211 = (let _148_210 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (_148_210, args))
in FStar_Syntax_Syntax.Tm_app (_148_211))
in (mk _148_212))
in (vars, _148_213)))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
([], e)
end)))))

# 424 "FStar.TypeChecker.Util.fst"
let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (
# 425 "FStar.TypeChecker.Util.fst"
let _63_616 = (match (c.FStar_Syntax_Syntax.effect_args) with
| (wp, _63_605)::(wlp, _63_601)::[] -> begin
(wp, wlp)
end
| _63_609 -> begin
(let _148_219 = (let _148_218 = (let _148_217 = (FStar_List.map (fun _63_613 -> (match (_63_613) with
| (x, _63_612) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right _148_217 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str _148_218))
in (FStar_All.failwith _148_219))
end)
in (match (_63_616) with
| (wp, wlp) -> begin
(c.FStar_Syntax_Syntax.result_typ, wp, wlp)
end)))

# 431 "FStar.TypeChecker.Util.fst"
let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (
# 432 "FStar.TypeChecker.Util.fst"
let _63_624 = (destruct_comp c)
in (match (_63_624) with
| (_63_621, wp, wlp) -> begin
(let _148_241 = (let _148_240 = (let _148_236 = (lift c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _148_236))
in (let _148_239 = (let _148_238 = (let _148_237 = (lift c.FStar_Syntax_Syntax.result_typ wlp)
in (FStar_Syntax_Syntax.as_arg _148_237))
in (_148_238)::[])
in (_148_240)::_148_239))
in {FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _148_241; FStar_Syntax_Syntax.flags = []})
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
| Some (_63_632, c) -> begin
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
let _63_646 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))

# 460 "FStar.TypeChecker.Util.fst"
let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (
# 461 "FStar.TypeChecker.Util.fst"
let _63_657 = (let _148_255 = (norm_eff_name env l1)
in (let _148_254 = (norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _148_255 _148_254)))
in (match (_63_657) with
| (m, _63_654, _63_656) -> begin
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
let _63_669 = (FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (_63_669) with
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
let _63_675 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (_63_675) with
| (a, kwp) -> begin
(let _148_269 = (destruct_comp m1)
in (let _148_268 = (destruct_comp m2)
in ((md, a, kwp), _148_269, _148_268)))
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
let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md result wp wlp flags -> (let _148_292 = (let _148_291 = (let _148_290 = (FStar_Syntax_Syntax.as_arg wp)
in (let _148_289 = (let _148_288 = (FStar_Syntax_Syntax.as_arg wlp)
in (_148_288)::[])
in (_148_290)::_148_289))
in {FStar_Syntax_Syntax.effect_name = md.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = _148_291; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp _148_292)))

# 495 "FStar.TypeChecker.Util.fst"
let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (
# 496 "FStar.TypeChecker.Util.fst"
let _63_689 = lc
in (let _148_299 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _63_689.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _148_299; FStar_Syntax_Syntax.cflags = _63_689.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _63_691 -> (match (()) with
| () -> begin
(let _148_298 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _148_298))
end))})))

# 499 "FStar.TypeChecker.Util.fst"
let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _148_302 = (FStar_Syntax_Subst.compress t)
in _148_302.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_63_694) -> begin
true
end
| _63_697 -> begin
false
end))

# 503 "FStar.TypeChecker.Util.fst"
let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v -> (
# 505 "FStar.TypeChecker.Util.fst"
let c = if (let _148_309 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation _148_309)) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(
# 508 "FStar.TypeChecker.Util.fst"
let m = (let _148_310 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must _148_310))
in (
# 509 "FStar.TypeChecker.Util.fst"
let _63_704 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_63_704) with
| (a, kwp) -> begin
(
# 510 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 511 "FStar.TypeChecker.Util.fst"
let wp = (let _148_318 = (let _148_317 = (let _148_312 = (let _148_311 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_148_311)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _148_312 env m m.FStar_Syntax_Syntax.ret))
in (let _148_316 = (let _148_315 = (FStar_Syntax_Syntax.as_arg t)
in (let _148_314 = (let _148_313 = (FStar_Syntax_Syntax.as_arg v)
in (_148_313)::[])
in (_148_315)::_148_314))
in (FStar_Syntax_Syntax.mk_Tm_app _148_317 _148_316 (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _148_318))
in (
# 512 "FStar.TypeChecker.Util.fst"
let wlp = wp
in (mk_comp m t wp wlp ((FStar_Syntax_Syntax.RETURN)::[])))))
end)))
end
in (
# 514 "FStar.TypeChecker.Util.fst"
let _63_709 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return"))) then begin
(let _148_321 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _148_320 = (FStar_Syntax_Print.term_to_string v)
in (let _148_319 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _148_321 _148_320 _148_319))))
end else begin
()
end
in c)))

# 519 "FStar.TypeChecker.Util.fst"
let bind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun env e1opt lc1 _63_716 -> (match (_63_716) with
| (b, lc2) -> begin
(
# 520 "FStar.TypeChecker.Util.fst"
let _63_724 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(
# 522 "FStar.TypeChecker.Util.fst"
let bstr = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _148_332 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (let _148_331 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _148_330 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" _148_332 _148_331 bstr _148_330)))))
end else begin
()
end
in (
# 528 "FStar.TypeChecker.Util.fst"
let bind_it = (fun _63_727 -> (match (()) with
| () -> begin
(
# 529 "FStar.TypeChecker.Util.fst"
let c1 = (lc1.FStar_Syntax_Syntax.comp ())
in (
# 530 "FStar.TypeChecker.Util.fst"
let c2 = (lc2.FStar_Syntax_Syntax.comp ())
in (
# 531 "FStar.TypeChecker.Util.fst"
let _63_733 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _148_339 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _148_338 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _148_337 = (FStar_Syntax_Print.comp_to_string c1)
in (let _148_336 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (let _148_335 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" _148_339 _148_338 _148_337 _148_336 _148_335))))))
end else begin
()
end
in (
# 540 "FStar.TypeChecker.Util.fst"
let try_simplify = (fun _63_736 -> (match (()) with
| () -> begin
(
# 541 "FStar.TypeChecker.Util.fst"
let aux = (fun _63_738 -> (match (()) with
| () -> begin
if (FStar_Syntax_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some ((c2, "trivial no binder"))
end
| Some (_63_741) -> begin
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
# 552 "FStar.TypeChecker.Util.fst"
let subst_c2 = (fun reason -> (match ((e1opt, b)) with
| (Some (e), Some (x)) -> begin
(let _148_347 = (let _148_346 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT ((x, e)))::[]) c2)
in (_148_346, reason))
in Some (_148_347))
end
| _63_751 -> begin
(aux ())
end))
in if ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2)) then begin
(subst_c2 "both total")
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2)) then begin
(let _148_349 = (let _148_348 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in (_148_348, "both gtot"))
in Some (_148_349))
end else begin
(match ((e1opt, b)) with
| (Some (e), Some (x)) -> begin
if ((FStar_Syntax_Util.is_total_comp c1) && (not ((FStar_Syntax_Syntax.is_null_bv x)))) then begin
(subst_c2 "substituted e")
end else begin
(aux ())
end
end
| _63_758 -> begin
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
# 573 "FStar.TypeChecker.Util.fst"
let _63_776 = (lift_and_destruct env c1 c2)
in (match (_63_776) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(
# 574 "FStar.TypeChecker.Util.fst"
let bs = (match (b) with
| None -> begin
(let _148_350 = (FStar_Syntax_Syntax.null_binder t1)
in (_148_350)::[])
end
| Some (x) -> begin
(let _148_351 = (FStar_Syntax_Syntax.mk_binder x)
in (_148_351)::[])
end)
in (
# 577 "FStar.TypeChecker.Util.fst"
let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp None))
in (
# 578 "FStar.TypeChecker.Util.fst"
let wp_args = (let _148_366 = (FStar_Syntax_Syntax.as_arg t1)
in (let _148_365 = (let _148_364 = (FStar_Syntax_Syntax.as_arg t2)
in (let _148_363 = (let _148_362 = (FStar_Syntax_Syntax.as_arg wp1)
in (let _148_361 = (let _148_360 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _148_359 = (let _148_358 = (let _148_354 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg _148_354))
in (let _148_357 = (let _148_356 = (let _148_355 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _148_355))
in (_148_356)::[])
in (_148_358)::_148_357))
in (_148_360)::_148_359))
in (_148_362)::_148_361))
in (_148_364)::_148_363))
in (_148_366)::_148_365))
in (
# 579 "FStar.TypeChecker.Util.fst"
let wlp_args = (let _148_374 = (FStar_Syntax_Syntax.as_arg t1)
in (let _148_373 = (let _148_372 = (FStar_Syntax_Syntax.as_arg t2)
in (let _148_371 = (let _148_370 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _148_369 = (let _148_368 = (let _148_367 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _148_367))
in (_148_368)::[])
in (_148_370)::_148_369))
in (_148_372)::_148_371))
in (_148_374)::_148_373))
in (
# 580 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t2)))::[]) kwp)
in (
# 581 "FStar.TypeChecker.Util.fst"
let us = (let _148_377 = (env.FStar_TypeChecker_Env.universe_of env t1)
in (let _148_376 = (let _148_375 = (env.FStar_TypeChecker_Env.universe_of env t2)
in (_148_375)::[])
in (_148_377)::_148_376))
in (
# 582 "FStar.TypeChecker.Util.fst"
let wp = (let _148_378 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _148_378 wp_args None t2.FStar_Syntax_Syntax.pos))
in (
# 583 "FStar.TypeChecker.Util.fst"
let wlp = (let _148_379 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wlp)
in (FStar_Syntax_Syntax.mk_Tm_app _148_379 wlp_args None t2.FStar_Syntax_Syntax.pos))
in (
# 584 "FStar.TypeChecker.Util.fst"
let c = (mk_comp md t2 wp wlp [])
in c)))))))))
end))
end)))))
end))
in (let _148_380 = (join_lcomp env lc1 lc2)
in {FStar_Syntax_Syntax.eff_name = _148_380; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it})))
end))

# 591 "FStar.TypeChecker.Util.fst"
let lift_formula : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t mk_wp mk_wlp f -> (
# 592 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 593 "FStar.TypeChecker.Util.fst"
let _63_798 = (FStar_TypeChecker_Env.wp_signature env md_pure.FStar_Syntax_Syntax.mname)
in (match (_63_798) with
| (a, kwp) -> begin
(
# 594 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 595 "FStar.TypeChecker.Util.fst"
let wp = (let _148_394 = (let _148_393 = (FStar_Syntax_Syntax.as_arg t)
in (let _148_392 = (let _148_391 = (FStar_Syntax_Syntax.as_arg f)
in (_148_391)::[])
in (_148_393)::_148_392))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wp _148_394 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (
# 596 "FStar.TypeChecker.Util.fst"
let wlp = (let _148_398 = (let _148_397 = (FStar_Syntax_Syntax.as_arg t)
in (let _148_396 = (let _148_395 = (FStar_Syntax_Syntax.as_arg f)
in (_148_395)::[])
in (_148_397)::_148_396))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wlp _148_398 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (mk_comp md_pure FStar_TypeChecker_Common.t_unit wp wlp []))))
end))))

# 599 "FStar.TypeChecker.Util.fst"
let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((f, FStar_Syntax_Syntax.Meta_labeled ((reason, r, false))))) None f.FStar_Syntax_Syntax.pos))

# 602 "FStar.TypeChecker.Util.fst"
let label_opt : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _148_422 = (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)
in (FStar_All.pipe_left Prims.op_Negation _148_422)) then begin
f
end else begin
(let _148_423 = (reason ())
in (label _148_423 r f))
end
end))

# 609 "FStar.TypeChecker.Util.fst"
let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 611 "FStar.TypeChecker.Util.fst"
let _63_818 = g
in (let _148_431 = (let _148_430 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_148_430))
in {FStar_TypeChecker_Env.guard_f = _148_431; FStar_TypeChecker_Env.deferred = _63_818.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _63_818.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _63_818.FStar_TypeChecker_Env.implicits}))
end))

# 613 "FStar.TypeChecker.Util.fst"
let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(
# 615 "FStar.TypeChecker.Util.fst"
let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| _63_829 -> begin
g2
end))

# 619 "FStar.TypeChecker.Util.fst"
let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (
# 620 "FStar.TypeChecker.Util.fst"
let weaken = (fun _63_834 -> (match (()) with
| () -> begin
(
# 621 "FStar.TypeChecker.Util.fst"
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
# 627 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 628 "FStar.TypeChecker.Util.fst"
let _63_843 = (destruct_comp c)
in (match (_63_843) with
| (res_t, wp, wlp) -> begin
(
# 629 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 630 "FStar.TypeChecker.Util.fst"
let us = (let _148_444 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_148_444)::[])
in (
# 631 "FStar.TypeChecker.Util.fst"
let wp = (let _148_451 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _148_450 = (let _148_449 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_448 = (let _148_447 = (FStar_Syntax_Syntax.as_arg f)
in (let _148_446 = (let _148_445 = (FStar_Syntax_Syntax.as_arg wp)
in (_148_445)::[])
in (_148_447)::_148_446))
in (_148_449)::_148_448))
in (FStar_Syntax_Syntax.mk_Tm_app _148_451 _148_450 None wp.FStar_Syntax_Syntax.pos)))
in (
# 632 "FStar.TypeChecker.Util.fst"
let wlp = (let _148_458 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _148_457 = (let _148_456 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_455 = (let _148_454 = (FStar_Syntax_Syntax.as_arg f)
in (let _148_453 = (let _148_452 = (FStar_Syntax_Syntax.as_arg wlp)
in (_148_452)::[])
in (_148_454)::_148_453))
in (_148_456)::_148_455))
in (FStar_Syntax_Syntax.mk_Tm_app _148_458 _148_457 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp c.FStar_Syntax_Syntax.flags)))))
end)))
end
end))
end))
in (
# 634 "FStar.TypeChecker.Util.fst"
let _63_848 = lc
in {FStar_Syntax_Syntax.eff_name = _63_848.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _63_848.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _63_848.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))

# 636 "FStar.TypeChecker.Util.fst"
let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> if (FStar_TypeChecker_Rel.is_trivial g0) then begin
(lc, g0)
end else begin
(
# 640 "FStar.TypeChecker.Util.fst"
let _63_855 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _148_478 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _148_477 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _148_478 _148_477)))
end else begin
()
end
in (
# 644 "FStar.TypeChecker.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _63_2 -> (match (_63_2) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _63_861 -> begin
[]
end))))
in (
# 645 "FStar.TypeChecker.Util.fst"
let strengthen = (fun _63_864 -> (match (()) with
| () -> begin
(
# 646 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 647 "FStar.TypeChecker.Util.fst"
let g0 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (match ((FStar_TypeChecker_Rel.guard_form g0)) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 651 "FStar.TypeChecker.Util.fst"
let c = if ((FStar_Syntax_Util.is_pure_or_ghost_comp c) && (not ((FStar_Syntax_Util.is_partial_return c)))) then begin
(
# 654 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.gen_bv "strengthen_pre_x" None (FStar_Syntax_Util.comp_result c))
in (
# 655 "FStar.TypeChecker.Util.fst"
let xret = (let _148_483 = (let _148_482 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _148_482))
in (FStar_Syntax_Util.comp_set_flags _148_483 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (
# 656 "FStar.TypeChecker.Util.fst"
let lc = (bind env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), (FStar_Syntax_Util.lcomp_of_comp xret)))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (
# 660 "FStar.TypeChecker.Util.fst"
let _63_874 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _148_485 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _148_484 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _148_485 _148_484)))
end else begin
()
end
in (
# 665 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 666 "FStar.TypeChecker.Util.fst"
let _63_880 = (destruct_comp c)
in (match (_63_880) with
| (res_t, wp, wlp) -> begin
(
# 667 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 668 "FStar.TypeChecker.Util.fst"
let us = (let _148_486 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_148_486)::[])
in (
# 669 "FStar.TypeChecker.Util.fst"
let wp = (let _148_495 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assert_p)
in (let _148_494 = (let _148_493 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_492 = (let _148_491 = (let _148_488 = (let _148_487 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason _148_487 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _148_488))
in (let _148_490 = (let _148_489 = (FStar_Syntax_Syntax.as_arg wp)
in (_148_489)::[])
in (_148_491)::_148_490))
in (_148_493)::_148_492))
in (FStar_Syntax_Syntax.mk_Tm_app _148_495 _148_494 None wp.FStar_Syntax_Syntax.pos)))
in (
# 670 "FStar.TypeChecker.Util.fst"
let wlp = (let _148_502 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _148_501 = (let _148_500 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_499 = (let _148_498 = (FStar_Syntax_Syntax.as_arg f)
in (let _148_497 = (let _148_496 = (FStar_Syntax_Syntax.as_arg wlp)
in (_148_496)::[])
in (_148_498)::_148_497))
in (_148_500)::_148_499))
in (FStar_Syntax_Syntax.mk_Tm_app _148_502 _148_501 None wlp.FStar_Syntax_Syntax.pos)))
in (
# 672 "FStar.TypeChecker.Util.fst"
let _63_885 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _148_503 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _148_503))
end else begin
()
end
in (
# 676 "FStar.TypeChecker.Util.fst"
let c2 = (mk_comp md res_t wp wlp flags)
in c2))))))
end)))))
end)))
end))
in (let _148_507 = (
# 678 "FStar.TypeChecker.Util.fst"
let _63_888 = lc
in (let _148_506 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _148_505 = if ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _148_504 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _148_504))) then begin
flags
end else begin
[]
end
in {FStar_Syntax_Syntax.eff_name = _148_506; FStar_Syntax_Syntax.res_typ = _63_888.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _148_505; FStar_Syntax_Syntax.comp = strengthen})))
in (_148_507, (
# 681 "FStar.TypeChecker.Util.fst"
let _63_890 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _63_890.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _63_890.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _63_890.FStar_TypeChecker_Env.implicits}))))))
end)

# 683 "FStar.TypeChecker.Util.fst"
let record_application_site : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (
# 684 "FStar.TypeChecker.Util.fst"
let comp = (fun _63_896 -> (match (()) with
| () -> begin
(
# 685 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 686 "FStar.TypeChecker.Util.fst"
let res_t = (FStar_Syntax_Util.comp_result c)
in if (((FStar_Syntax_Util.is_trivial_wp c) || (let _148_516 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals _148_516 FStar_Syntax_Const.prims_lid))) || (FStar_Syntax_Syntax.is_teff res_t)) then begin
c
end else begin
(
# 691 "FStar.TypeChecker.Util.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (FStar_TypeChecker_Common.t_unit)))
in (
# 692 "FStar.TypeChecker.Util.fst"
let _63_904 = (strengthen_precondition (Some ((fun _63_900 -> (match (()) with
| () -> begin
"push"
end)))) env e (FStar_Syntax_Util.lcomp_of_comp c) g)
in (match (_63_904) with
| (c, _63_903) -> begin
(
# 693 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 694 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 695 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 696 "FStar.TypeChecker.Util.fst"
let us = (let _148_520 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_148_520)::[])
in (
# 697 "FStar.TypeChecker.Util.fst"
let xret = (let _148_525 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _148_524 = (let _148_523 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_522 = (let _148_521 = (FStar_Syntax_Syntax.as_arg xexp)
in (_148_521)::[])
in (_148_523)::_148_522))
in (FStar_Syntax_Syntax.mk_Tm_app _148_525 _148_524 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 698 "FStar.TypeChecker.Util.fst"
let xret_comp = (let _148_526 = (mk_comp md_pure res_t xret xret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_526))
in (
# 699 "FStar.TypeChecker.Util.fst"
let lc = (let _148_532 = (let _148_531 = (let _148_530 = (strengthen_precondition (Some ((fun _63_911 -> (match (()) with
| () -> begin
"pop"
end)))) env xexp xret_comp g)
in (FStar_All.pipe_left Prims.fst _148_530))
in (Some (x), _148_531))
in (bind env None c _148_532))
in (lc.FStar_Syntax_Syntax.comp ()))))))))
end)))
end))
end))
in (
# 701 "FStar.TypeChecker.Util.fst"
let _63_913 = lc
in {FStar_Syntax_Syntax.eff_name = _63_913.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _63_913.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _63_913.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = comp})))

# 703 "FStar.TypeChecker.Util.fst"
let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env comp res_t -> (
# 704 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 705 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 706 "FStar.TypeChecker.Util.fst"
let y = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 707 "FStar.TypeChecker.Util.fst"
let _63_923 = (let _148_540 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _148_539 = (FStar_Syntax_Syntax.bv_to_name y)
in (_148_540, _148_539)))
in (match (_63_923) with
| (xexp, yexp) -> begin
(
# 708 "FStar.TypeChecker.Util.fst"
let us = (let _148_541 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_148_541)::[])
in (
# 709 "FStar.TypeChecker.Util.fst"
let yret = (let _148_546 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _148_545 = (let _148_544 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_543 = (let _148_542 = (FStar_Syntax_Syntax.as_arg yexp)
in (_148_542)::[])
in (_148_544)::_148_543))
in (FStar_Syntax_Syntax.mk_Tm_app _148_546 _148_545 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 710 "FStar.TypeChecker.Util.fst"
let x_eq_y_yret = (let _148_554 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _148_553 = (let _148_552 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_551 = (let _148_550 = (let _148_547 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _148_547))
in (let _148_549 = (let _148_548 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_148_548)::[])
in (_148_550)::_148_549))
in (_148_552)::_148_551))
in (FStar_Syntax_Syntax.mk_Tm_app _148_554 _148_553 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 711 "FStar.TypeChecker.Util.fst"
let forall_y_x_eq_y_yret = (let _148_564 = (FStar_TypeChecker_Env.inst_effect_fun_with (FStar_List.append us us) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _148_563 = (let _148_562 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_561 = (let _148_560 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_559 = (let _148_558 = (let _148_557 = (let _148_556 = (let _148_555 = (FStar_Syntax_Syntax.mk_binder y)
in (_148_555)::[])
in (FStar_Syntax_Util.abs _148_556 x_eq_y_yret None))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _148_557))
in (_148_558)::[])
in (_148_560)::_148_559))
in (_148_562)::_148_561))
in (FStar_Syntax_Syntax.mk_Tm_app _148_564 _148_563 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 712 "FStar.TypeChecker.Util.fst"
let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (
# 713 "FStar.TypeChecker.Util.fst"
let lc = (bind env None (FStar_Syntax_Util.lcomp_of_comp comp) (Some (x), (FStar_Syntax_Util.lcomp_of_comp lc2)))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))

# 716 "FStar.TypeChecker.Util.fst"
let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (
# 717 "FStar.TypeChecker.Util.fst"
let comp = (fun _63_935 -> (match (()) with
| () -> begin
(
# 718 "FStar.TypeChecker.Util.fst"
let _63_951 = (let _148_576 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _148_575 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _148_576 _148_575)))
in (match (_63_951) with
| ((md, _63_938, _63_940), (res_t, wp_then, wlp_then), (_63_947, wp_else, wlp_else)) -> begin
(
# 719 "FStar.TypeChecker.Util.fst"
let us = (let _148_577 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_148_577)::[])
in (
# 720 "FStar.TypeChecker.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _148_597 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _148_596 = (let _148_594 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_593 = (let _148_592 = (FStar_Syntax_Syntax.as_arg g)
in (let _148_591 = (let _148_590 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _148_589 = (let _148_588 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_148_588)::[])
in (_148_590)::_148_589))
in (_148_592)::_148_591))
in (_148_594)::_148_593))
in (let _148_595 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _148_597 _148_596 None _148_595)))))
in (
# 721 "FStar.TypeChecker.Util.fst"
let wp = (ifthenelse md res_t guard wp_then wp_else)
in (
# 722 "FStar.TypeChecker.Util.fst"
let wlp = (ifthenelse md res_t guard wlp_then wlp_else)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(
# 724 "FStar.TypeChecker.Util.fst"
let comp = (mk_comp md res_t wp wlp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(
# 726 "FStar.TypeChecker.Util.fst"
let wp = (let _148_604 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _148_603 = (let _148_602 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_601 = (let _148_600 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _148_599 = (let _148_598 = (FStar_Syntax_Syntax.as_arg wp)
in (_148_598)::[])
in (_148_600)::_148_599))
in (_148_602)::_148_601))
in (FStar_Syntax_Syntax.mk_Tm_app _148_604 _148_603 None wp.FStar_Syntax_Syntax.pos)))
in (
# 727 "FStar.TypeChecker.Util.fst"
let wlp = (let _148_609 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _148_608 = (let _148_607 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_606 = (let _148_605 = (FStar_Syntax_Syntax.as_arg wlp)
in (_148_605)::[])
in (_148_607)::_148_606))
in (FStar_Syntax_Syntax.mk_Tm_app _148_609 _148_608 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end))))
end))
end))
in (let _148_610 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _148_610; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp})))

# 734 "FStar.TypeChecker.Util.fst"
let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (let _148_616 = (let _148_615 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid _148_615))
in (FStar_Syntax_Syntax.fvar _148_616 FStar_Syntax_Syntax.Delta_constant None)))

# 736 "FStar.TypeChecker.Util.fst"
let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (
# 737 "FStar.TypeChecker.Util.fst"
let eff = (FStar_List.fold_left (fun eff _63_973 -> (match (_63_973) with
| (_63_971, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (
# 738 "FStar.TypeChecker.Util.fst"
let bind_cases = (fun _63_976 -> (match (()) with
| () -> begin
(
# 739 "FStar.TypeChecker.Util.fst"
let us = (let _148_627 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_148_627)::[])
in (
# 740 "FStar.TypeChecker.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _148_647 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _148_646 = (let _148_644 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_643 = (let _148_642 = (FStar_Syntax_Syntax.as_arg g)
in (let _148_641 = (let _148_640 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _148_639 = (let _148_638 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_148_638)::[])
in (_148_640)::_148_639))
in (_148_642)::_148_641))
in (_148_644)::_148_643))
in (let _148_645 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _148_647 _148_646 None _148_645)))))
in (
# 742 "FStar.TypeChecker.Util.fst"
let default_case = (
# 743 "FStar.TypeChecker.Util.fst"
let post_k = (let _148_650 = (let _148_648 = (FStar_Syntax_Syntax.null_binder res_t)
in (_148_648)::[])
in (let _148_649 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _148_650 _148_649)))
in (
# 744 "FStar.TypeChecker.Util.fst"
let kwp = (let _148_653 = (let _148_651 = (FStar_Syntax_Syntax.null_binder post_k)
in (_148_651)::[])
in (let _148_652 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _148_653 _148_652)))
in (
# 745 "FStar.TypeChecker.Util.fst"
let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (
# 746 "FStar.TypeChecker.Util.fst"
let wp = (let _148_659 = (let _148_654 = (FStar_Syntax_Syntax.mk_binder post)
in (_148_654)::[])
in (let _148_658 = (let _148_657 = (let _148_655 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Errors.exhaustiveness_check _148_655))
in (let _148_656 = (fvar_const env FStar_Syntax_Const.false_lid)
in (FStar_All.pipe_left _148_657 _148_656)))
in (FStar_Syntax_Util.abs _148_659 _148_658 None)))
in (
# 747 "FStar.TypeChecker.Util.fst"
let wlp = (let _148_662 = (let _148_660 = (FStar_Syntax_Syntax.mk_binder post)
in (_148_660)::[])
in (let _148_661 = (fvar_const env FStar_Syntax_Const.true_lid)
in (FStar_Syntax_Util.abs _148_662 _148_661 None)))
in (
# 748 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (
# 750 "FStar.TypeChecker.Util.fst"
let comp = (FStar_List.fold_right (fun _63_993 celse -> (match (_63_993) with
| (g, cthen) -> begin
(
# 751 "FStar.TypeChecker.Util.fst"
let _63_1011 = (let _148_665 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _148_665 celse))
in (match (_63_1011) with
| ((md, _63_997, _63_999), (_63_1002, wp_then, wlp_then), (_63_1007, wp_else, wlp_else)) -> begin
(let _148_667 = (ifthenelse md res_t g wp_then wp_else)
in (let _148_666 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _148_667 _148_666 [])))
end))
end)) lcases default_case)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(add_equality_to_post_condition env comp res_t)
end else begin
(
# 755 "FStar.TypeChecker.Util.fst"
let comp = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (
# 756 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env comp.FStar_Syntax_Syntax.effect_name)
in (
# 757 "FStar.TypeChecker.Util.fst"
let _63_1019 = (destruct_comp comp)
in (match (_63_1019) with
| (_63_1016, wp, wlp) -> begin
(
# 758 "FStar.TypeChecker.Util.fst"
let wp = (let _148_674 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _148_673 = (let _148_672 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_671 = (let _148_670 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _148_669 = (let _148_668 = (FStar_Syntax_Syntax.as_arg wp)
in (_148_668)::[])
in (_148_670)::_148_669))
in (_148_672)::_148_671))
in (FStar_Syntax_Syntax.mk_Tm_app _148_674 _148_673 None wp.FStar_Syntax_Syntax.pos)))
in (
# 759 "FStar.TypeChecker.Util.fst"
let wlp = (let _148_679 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _148_678 = (let _148_677 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_676 = (let _148_675 = (FStar_Syntax_Syntax.as_arg wlp)
in (_148_675)::[])
in (_148_677)::_148_676))
in (FStar_Syntax_Syntax.mk_Tm_app _148_679 _148_678 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end))))
end))))
end))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))

# 766 "FStar.TypeChecker.Util.fst"
let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (
# 767 "FStar.TypeChecker.Util.fst"
let close = (fun _63_1026 -> (match (()) with
| () -> begin
(
# 768 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in if (FStar_Syntax_Util.is_ml_comp c) then begin
c
end else begin
(
# 771 "FStar.TypeChecker.Util.fst"
let close_wp = (fun u_res md res_t bvs wp0 -> (FStar_List.fold_right (fun x wp -> (
# 773 "FStar.TypeChecker.Util.fst"
let bs = (let _148_700 = (FStar_Syntax_Syntax.mk_binder x)
in (_148_700)::[])
in (
# 774 "FStar.TypeChecker.Util.fst"
let us = (let _148_702 = (let _148_701 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (_148_701)::[])
in (u_res)::_148_702)
in (
# 775 "FStar.TypeChecker.Util.fst"
let wp = (FStar_Syntax_Util.abs bs wp None)
in (let _148_709 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (let _148_708 = (let _148_707 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_706 = (let _148_705 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _148_704 = (let _148_703 = (FStar_Syntax_Syntax.as_arg wp)
in (_148_703)::[])
in (_148_705)::_148_704))
in (_148_707)::_148_706))
in (FStar_Syntax_Syntax.mk_Tm_app _148_709 _148_708 None wp0.FStar_Syntax_Syntax.pos))))))) bvs wp0))
in (
# 778 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 779 "FStar.TypeChecker.Util.fst"
let _63_1043 = (destruct_comp c)
in (match (_63_1043) with
| (t, wp, wlp) -> begin
(
# 780 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 781 "FStar.TypeChecker.Util.fst"
let u_res = (env.FStar_TypeChecker_Env.universe_of env c.FStar_Syntax_Syntax.result_typ)
in (
# 782 "FStar.TypeChecker.Util.fst"
let wp = (close_wp u_res md c.FStar_Syntax_Syntax.result_typ bvs wp)
in (
# 783 "FStar.TypeChecker.Util.fst"
let wlp = (close_wp u_res md c.FStar_Syntax_Syntax.result_typ bvs wlp)
in (mk_comp md c.FStar_Syntax_Syntax.result_typ wp wlp c.FStar_Syntax_Syntax.flags)))))
end))))
end)
end))
in (
# 785 "FStar.TypeChecker.Util.fst"
let _63_1048 = lc
in {FStar_Syntax_Syntax.eff_name = _63_1048.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _63_1048.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _63_1048.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))

# 787 "FStar.TypeChecker.Util.fst"
let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (
# 788 "FStar.TypeChecker.Util.fst"
let refine = (fun _63_1054 -> (match (()) with
| () -> begin
(
# 789 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in if (not ((is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name))) then begin
c
end else begin
if (FStar_Syntax_Util.is_partial_return c) then begin
c
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c) && (not ((FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)))) then begin
(let _148_720 = (let _148_719 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _148_718 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _148_719 _148_718)))
in (FStar_All.failwith _148_720))
end else begin
(
# 797 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 798 "FStar.TypeChecker.Util.fst"
let t = c.FStar_Syntax_Syntax.result_typ
in (
# 799 "FStar.TypeChecker.Util.fst"
let c = (FStar_Syntax_Syntax.mk_Comp c)
in (
# 800 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (
# 801 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 802 "FStar.TypeChecker.Util.fst"
let ret = (let _148_722 = (let _148_721 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _148_721 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_722))
in (
# 803 "FStar.TypeChecker.Util.fst"
let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (
# 804 "FStar.TypeChecker.Util.fst"
let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (
# 806 "FStar.TypeChecker.Util.fst"
let c = (let _148_724 = (let _148_723 = (bind env None (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), eq_ret))
in (_148_723.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _148_724 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
in c)))))))))
end
end
end)
end))
in (
# 809 "FStar.TypeChecker.Util.fst"
let flags = if (((not ((FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)) && (not ((FStar_Syntax_Util.is_lcomp_partial_return lc)))) then begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_Syntax_Syntax.cflags
end else begin
lc.FStar_Syntax_Syntax.cflags
end
in (
# 815 "FStar.TypeChecker.Util.fst"
let _63_1066 = lc
in {FStar_Syntax_Syntax.eff_name = _63_1066.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _63_1066.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))

# 817 "FStar.TypeChecker.Util.fst"
let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (match ((FStar_TypeChecker_Rel.sub_comp env c c')) with
| None -> begin
(let _148_736 = (let _148_735 = (let _148_734 = (FStar_TypeChecker_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _148_733 = (FStar_TypeChecker_Env.get_range env)
in (_148_734, _148_733)))
in FStar_Syntax_Syntax.Error (_148_735))
in (Prims.raise _148_736))
end
| Some (g) -> begin
(e, c', g)
end))

# 823 "FStar.TypeChecker.Util.fst"
let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match ((let _148_745 = (FStar_Syntax_Subst.compress t)
in _148_745.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_63_1080) -> begin
(match ((let _148_746 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _148_746.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid) -> begin
(
# 828 "FStar.TypeChecker.Util.fst"
let _63_1084 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (
# 829 "FStar.TypeChecker.Util.fst"
let b2t = (let _148_747 = (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar _148_747 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (
# 830 "FStar.TypeChecker.Util.fst"
let lc = (let _148_750 = (let _148_749 = (let _148_748 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_748))
in (None, _148_749))
in (bind env (Some (e)) lc _148_750))
in (
# 831 "FStar.TypeChecker.Util.fst"
let e = (let _148_752 = (let _148_751 = (FStar_Syntax_Syntax.as_arg e)
in (_148_751)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _148_752 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (e, lc)))))
end
| _63_1090 -> begin
(e, lc)
end)
end
| _63_1092 -> begin
(e, lc)
end))

# 838 "FStar.TypeChecker.Util.fst"
let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (
# 839 "FStar.TypeChecker.Util.fst"
let gopt = if env.FStar_TypeChecker_Env.use_eq then begin
(let _148_761 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in (_148_761, false))
end else begin
(let _148_762 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in (_148_762, true))
end
in (match (gopt) with
| (None, _63_1100) -> begin
(FStar_TypeChecker_Rel.subtype_fail env lc.FStar_Syntax_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(match ((FStar_TypeChecker_Rel.guard_form g)) with
| FStar_TypeChecker_Common.Trivial -> begin
(
# 847 "FStar.TypeChecker.Util.fst"
let lc = (
# 847 "FStar.TypeChecker.Util.fst"
let _63_1107 = lc
in {FStar_Syntax_Syntax.eff_name = _63_1107.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _63_1107.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _63_1107.FStar_Syntax_Syntax.comp})
in (e, lc, g))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 851 "FStar.TypeChecker.Util.fst"
let g = (
# 851 "FStar.TypeChecker.Util.fst"
let _63_1112 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _63_1112.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _63_1112.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _63_1112.FStar_TypeChecker_Env.implicits})
in (
# 852 "FStar.TypeChecker.Util.fst"
let strengthen = (fun _63_1116 -> (match (()) with
| () -> begin
(
# 854 "FStar.TypeChecker.Util.fst"
let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (match ((let _148_765 = (FStar_Syntax_Subst.compress f)
in _148_765.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_63_1119, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _63_1125; FStar_Syntax_Syntax.pos = _63_1123; FStar_Syntax_Syntax.vars = _63_1121}, _63_1130) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
(
# 858 "FStar.TypeChecker.Util.fst"
let lc = (
# 858 "FStar.TypeChecker.Util.fst"
let _63_1133 = lc
in {FStar_Syntax_Syntax.eff_name = _63_1133.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _63_1133.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _63_1133.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| _63_1137 -> begin
(
# 862 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 863 "FStar.TypeChecker.Util.fst"
let _63_1139 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _148_769 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _148_768 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _148_767 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _148_766 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _148_769 _148_768 _148_767 _148_766)))))
end else begin
()
end
in (
# 870 "FStar.TypeChecker.Util.fst"
let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 871 "FStar.TypeChecker.Util.fst"
let _63_1144 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_63_1144) with
| (a, kwp) -> begin
(
# 872 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 873 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env ct.FStar_Syntax_Syntax.effect_name)
in (
# 874 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (
# 875 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 876 "FStar.TypeChecker.Util.fst"
let us = (let _148_770 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_148_770)::[])
in (
# 877 "FStar.TypeChecker.Util.fst"
let wp = (let _148_775 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ret)
in (let _148_774 = (let _148_773 = (FStar_Syntax_Syntax.as_arg t)
in (let _148_772 = (let _148_771 = (FStar_Syntax_Syntax.as_arg xexp)
in (_148_771)::[])
in (_148_773)::_148_772))
in (FStar_Syntax_Syntax.mk_Tm_app _148_775 _148_774 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)))
in (
# 878 "FStar.TypeChecker.Util.fst"
let cret = (let _148_776 = (mk_comp md t wp wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_776))
in (
# 879 "FStar.TypeChecker.Util.fst"
let guard = if apply_guard then begin
(let _148_778 = (let _148_777 = (FStar_Syntax_Syntax.as_arg xexp)
in (_148_777)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _148_778 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end else begin
f
end
in (
# 880 "FStar.TypeChecker.Util.fst"
let _63_1155 = (let _148_786 = (FStar_All.pipe_left (fun _148_783 -> Some (_148_783)) (FStar_TypeChecker_Errors.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _148_785 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _148_784 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _148_786 _148_785 e cret _148_784))))
in (match (_63_1155) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(
# 884 "FStar.TypeChecker.Util.fst"
let x = (
# 884 "FStar.TypeChecker.Util.fst"
let _63_1156 = x
in {FStar_Syntax_Syntax.ppname = _63_1156.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_1156.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (
# 885 "FStar.TypeChecker.Util.fst"
let c = (let _148_788 = (let _148_787 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_787))
in (bind env (Some (e)) _148_788 (Some (x), eq_ret)))
in (
# 886 "FStar.TypeChecker.Util.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 887 "FStar.TypeChecker.Util.fst"
let _63_1161 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _148_789 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _148_789))
end else begin
()
end
in c))))
end))))))))))
end)))))
end))
end))
in (
# 890 "FStar.TypeChecker.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _63_3 -> (match (_63_3) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _63_1167 -> begin
[]
end))))
in (
# 891 "FStar.TypeChecker.Util.fst"
let lc = (
# 891 "FStar.TypeChecker.Util.fst"
let _63_1169 = lc
in (let _148_791 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _148_791; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (
# 892 "FStar.TypeChecker.Util.fst"
let g = (
# 892 "FStar.TypeChecker.Util.fst"
let _63_1172 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _63_1172.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _63_1172.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _63_1172.FStar_TypeChecker_Env.implicits})
in (e, lc, g))))))
end)
end)))

# 895 "FStar.TypeChecker.Util.fst"
let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (
# 896 "FStar.TypeChecker.Util.fst"
let mk_post_type = (fun res_t ens -> (
# 897 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _148_803 = (let _148_802 = (let _148_801 = (let _148_800 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _148_800))
in (_148_801)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _148_802 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _148_803))))
in (
# 899 "FStar.TypeChecker.Util.fst"
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
| (req, _63_1200)::(ens, _63_1195)::_63_1192 -> begin
(let _148_809 = (let _148_806 = (norm req)
in Some (_148_806))
in (let _148_808 = (let _148_807 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _148_807))
in (_148_809, _148_808)))
end
| _63_1204 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 913 "FStar.TypeChecker.Util.fst"
let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (wp, _63_1215)::(wlp, _63_1210)::_63_1207 -> begin
(
# 916 "FStar.TypeChecker.Util.fst"
let _63_1221 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (_63_1221) with
| (us_r, _63_1220) -> begin
(
# 917 "FStar.TypeChecker.Util.fst"
let _63_1225 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (_63_1225) with
| (us_e, _63_1224) -> begin
(
# 918 "FStar.TypeChecker.Util.fst"
let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (
# 919 "FStar.TypeChecker.Util.fst"
let as_req = (let _148_811 = (let _148_810 = (FStar_Ident.set_lid_range FStar_Syntax_Const.as_requires r)
in (FStar_Syntax_Syntax.fvar _148_810 FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _148_811 us_r))
in (
# 920 "FStar.TypeChecker.Util.fst"
let as_ens = (let _148_813 = (let _148_812 = (FStar_Ident.set_lid_range FStar_Syntax_Const.as_ensures r)
in (FStar_Syntax_Syntax.fvar _148_812 FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _148_813 us_e))
in (
# 921 "FStar.TypeChecker.Util.fst"
let req = (let _148_816 = (let _148_815 = (let _148_814 = (FStar_Syntax_Syntax.as_arg wp)
in (_148_814)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.imp_tag)))::_148_815)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _148_816 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 922 "FStar.TypeChecker.Util.fst"
let ens = (let _148_819 = (let _148_818 = (let _148_817 = (FStar_Syntax_Syntax.as_arg wlp)
in (_148_817)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.imp_tag)))::_148_818)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _148_819 None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _148_823 = (let _148_820 = (norm req)
in Some (_148_820))
in (let _148_822 = (let _148_821 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm _148_821))
in (_148_823, _148_822))))))))
end))
end))
end
| _63_1232 -> begin
(FStar_All.failwith "Impossible")
end))
end
end)
end)))

# 932 "FStar.TypeChecker.Util.fst"
let maybe_instantiate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (
# 933 "FStar.TypeChecker.Util.fst"
let torig = (FStar_Syntax_Subst.compress t)
in if (not (env.FStar_TypeChecker_Env.instantiate_imp)) then begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end else begin
(match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 938 "FStar.TypeChecker.Util.fst"
let _63_1243 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_63_1243) with
| (bs, c) -> begin
(
# 939 "FStar.TypeChecker.Util.fst"
let rec aux = (fun subst _63_4 -> (match (_63_4) with
| (x, Some (FStar_Syntax_Syntax.Implicit (dot)))::rest -> begin
(
# 941 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 942 "FStar.TypeChecker.Util.fst"
let _63_1259 = (new_implicit_var env t)
in (match (_63_1259) with
| (v, _63_1257, g) -> begin
(
# 943 "FStar.TypeChecker.Util.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, v)))::subst
in (
# 944 "FStar.TypeChecker.Util.fst"
let _63_1265 = (aux subst rest)
in (match (_63_1265) with
| (args, bs, subst, g') -> begin
(let _148_834 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((v, Some (FStar_Syntax_Syntax.Implicit (dot))))::args, bs, subst, _148_834))
end)))
end)))
end
| bs -> begin
([], bs, subst, FStar_TypeChecker_Rel.trivial_guard)
end))
in (
# 948 "FStar.TypeChecker.Util.fst"
let _63_1271 = (aux [] bs)
in (match (_63_1271) with
| (args, bs, subst, guard) -> begin
(match ((args, bs)) with
| ([], _63_1274) -> begin
(e, torig, guard)
end
| (_63_1277, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end
| _63_1281 -> begin
(
# 959 "FStar.TypeChecker.Util.fst"
let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _63_1284 -> begin
(FStar_Syntax_Util.arrow bs c)
end)
in (
# 962 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.subst subst t)
in (
# 963 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk_Tm_app e args (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (e, t, guard))))
end)
end)))
end))
end
| _63_1289 -> begin
(e, t, FStar_TypeChecker_Rel.trivial_guard)
end)
end))

# 973 "FStar.TypeChecker.Util.fst"
let gen_univs : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe_uvar Prims.list * (FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  Prims.bool))  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(
# 975 "FStar.TypeChecker.Util.fst"
let s = (let _148_846 = (let _148_845 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _148_845))
in (FStar_All.pipe_right _148_846 FStar_Util.set_elements))
in (
# 976 "FStar.TypeChecker.Util.fst"
let r = (let _148_847 = (FStar_TypeChecker_Env.get_range env)
in Some (_148_847))
in (
# 977 "FStar.TypeChecker.Util.fst"
let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (
# 978 "FStar.TypeChecker.Util.fst"
let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (
# 979 "FStar.TypeChecker.Util.fst"
let _63_1296 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _148_852 = (let _148_849 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _148_849))
in (let _148_851 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _148_850 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _148_852 _148_851 _148_850))))
end else begin
()
end
in (
# 981 "FStar.TypeChecker.Util.fst"
let _63_1298 = (FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))))
in u_name))))))
in u_names)))
end)

# 985 "FStar.TypeChecker.Util.fst"
let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t -> (
# 986 "FStar.TypeChecker.Util.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (
# 987 "FStar.TypeChecker.Util.fst"
let univs = (FStar_Syntax_Free.univs t)
in (
# 988 "FStar.TypeChecker.Util.fst"
let _63_1306 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _148_861 = (let _148_860 = (let _148_859 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _148_859 (FStar_List.map (fun u -> (let _148_858 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _148_858 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _148_860 (FStar_String.concat ", ")))
in (FStar_Util.print1 "univs to gen : %s\n" _148_861))
end else begin
()
end
in (
# 992 "FStar.TypeChecker.Util.fst"
let gen = (gen_univs env univs)
in (
# 993 "FStar.TypeChecker.Util.fst"
let _63_1309 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _148_862 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _148_862))
end else begin
()
end
in (
# 995 "FStar.TypeChecker.Util.fst"
let ts = (FStar_Syntax_Subst.close_univ_vars gen t)
in (gen, ts))))))))

# 998 "FStar.TypeChecker.Util.fst"
let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> if (let _148_868 = (FStar_Util.for_all (fun _63_1317 -> (match (_63_1317) with
| (_63_1315, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _148_868)) then begin
None
end else begin
(
# 1002 "FStar.TypeChecker.Util.fst"
let norm = (fun c -> (
# 1003 "FStar.TypeChecker.Util.fst"
let _63_1320 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _148_871 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _148_871))
end else begin
()
end
in (
# 1005 "FStar.TypeChecker.Util.fst"
let c = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.Eta)::[]) env c)
end else begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env c)
end
in (
# 1008 "FStar.TypeChecker.Util.fst"
let _63_1323 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _148_872 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _148_872))
end else begin
()
end
in c))))
in (
# 1011 "FStar.TypeChecker.Util.fst"
let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (
# 1012 "FStar.TypeChecker.Util.fst"
let gen_uvars = (fun uvs -> (let _148_875 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _148_875 FStar_Util.set_elements)))
in (
# 1013 "FStar.TypeChecker.Util.fst"
let _63_1340 = (let _148_877 = (FStar_All.pipe_right ecs (FStar_List.map (fun _63_1330 -> (match (_63_1330) with
| (e, c) -> begin
(
# 1014 "FStar.TypeChecker.Util.fst"
let t = (FStar_All.pipe_right (FStar_Syntax_Util.comp_result c) FStar_Syntax_Subst.compress)
in (
# 1015 "FStar.TypeChecker.Util.fst"
let c = (norm c)
in (
# 1016 "FStar.TypeChecker.Util.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (
# 1017 "FStar.TypeChecker.Util.fst"
let t = ct.FStar_Syntax_Syntax.result_typ
in (
# 1018 "FStar.TypeChecker.Util.fst"
let univs = (FStar_Syntax_Free.univs t)
in (
# 1019 "FStar.TypeChecker.Util.fst"
let uvt = (FStar_Syntax_Free.uvars t)
in (
# 1020 "FStar.TypeChecker.Util.fst"
let uvs = (gen_uvars uvt)
in (univs, (uvs, e, c)))))))))
end))))
in (FStar_All.pipe_right _148_877 FStar_List.unzip))
in (match (_63_1340) with
| (univs, uvars) -> begin
(
# 1023 "FStar.TypeChecker.Util.fst"
let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (
# 1024 "FStar.TypeChecker.Util.fst"
let gen_univs = (gen_univs env univs)
in (
# 1025 "FStar.TypeChecker.Util.fst"
let _63_1344 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end else begin
()
end
in (
# 1027 "FStar.TypeChecker.Util.fst"
let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _63_1349 -> (match (_63_1349) with
| (uvs, e, c) -> begin
(
# 1028 "FStar.TypeChecker.Util.fst"
let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _63_1352 -> (match (_63_1352) with
| (u, k) -> begin
(match ((FStar_Unionfind.find u)) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(a, Some (FStar_Syntax_Syntax.imp_tag))
end
| FStar_Syntax_Syntax.Fixed (_63_1386) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _63_1389 -> begin
(
# 1034 "FStar.TypeChecker.Util.fst"
let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (
# 1035 "FStar.TypeChecker.Util.fst"
let _63_1393 = (FStar_Syntax_Util.arrow_formals k)
in (match (_63_1393) with
| (bs, kres) -> begin
(
# 1036 "FStar.TypeChecker.Util.fst"
let a = (let _148_883 = (let _148_882 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _148_881 -> Some (_148_881)) _148_882))
in (FStar_Syntax_Syntax.new_bv _148_883 kres))
in (
# 1037 "FStar.TypeChecker.Util.fst"
let t = (let _148_887 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _148_886 = (let _148_885 = (let _148_884 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _148_884))
in Some (_148_885))
in (FStar_Syntax_Util.abs bs _148_887 _148_886)))
in (
# 1038 "FStar.TypeChecker.Util.fst"
let _63_1396 = (FStar_Syntax_Util.set_uvar u t)
in (a, Some (FStar_Syntax_Syntax.imp_tag)))))
end)))
end)
end))))
in (
# 1042 "FStar.TypeChecker.Util.fst"
let _63_1420 = (match (tvars) with
| [] -> begin
(e, c)
end
| _63_1401 -> begin
(
# 1048 "FStar.TypeChecker.Util.fst"
let _63_1404 = (e, c)
in (match (_63_1404) with
| (e0, c0) -> begin
(
# 1049 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.BetaUVars)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::[]) env c)
in (
# 1050 "FStar.TypeChecker.Util.fst"
let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.BetaUVars)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::[]) env e)
in (
# 1052 "FStar.TypeChecker.Util.fst"
let t = (match ((let _148_888 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _148_888.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(
# 1054 "FStar.TypeChecker.Util.fst"
let _63_1413 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (_63_1413) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| _63_1415 -> begin
(FStar_Syntax_Util.arrow tvars c)
end)
in (
# 1059 "FStar.TypeChecker.Util.fst"
let e' = (FStar_Syntax_Util.abs tvars e None)
in (let _148_889 = (FStar_Syntax_Syntax.mk_Total t)
in (e', _148_889))))))
end))
end)
in (match (_63_1420) with
| (e, c) -> begin
(gen_univs, e, c)
end)))
end))))
in Some (ecs)))))
end)))))
end)

# 1064 "FStar.TypeChecker.Util.fst"
let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> (
# 1065 "FStar.TypeChecker.Util.fst"
let _63_1430 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _148_896 = (let _148_895 = (FStar_List.map (fun _63_1429 -> (match (_63_1429) with
| (lb, _63_1426, _63_1428) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _148_895 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _148_896))
end else begin
()
end
in (match ((let _148_898 = (FStar_All.pipe_right lecs (FStar_List.map (fun _63_1436 -> (match (_63_1436) with
| (_63_1433, e, c) -> begin
(e, c)
end))))
in (gen env _148_898))) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun _63_1441 -> (match (_63_1441) with
| (l, t, c) -> begin
(l, [], t, c)
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _63_1449 _63_1453 -> (match ((_63_1449, _63_1453)) with
| ((l, _63_1446, _63_1448), (us, e, c)) -> begin
(
# 1072 "FStar.TypeChecker.Util.fst"
let _63_1454 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _148_904 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _148_903 = (FStar_Syntax_Print.lbname_to_string l)
in (let _148_902 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.print3 "(%s) Generalized %s to %s\n" _148_904 _148_903 _148_902))))
end else begin
()
end
in (l, us, e, c))
end)) lecs ecs)
end)))

# 1085 "FStar.TypeChecker.Util.fst"
let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (
# 1086 "FStar.TypeChecker.Util.fst"
let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (
# 1087 "FStar.TypeChecker.Util.fst"
let check = (fun env t1 t2 -> if env.FStar_TypeChecker_Env.use_eq then begin
(FStar_TypeChecker_Rel.try_teq env t1 t2)
end else begin
(match ((FStar_TypeChecker_Rel.try_subtype env t1 t2)) with
| None -> begin
None
end
| Some (f) -> begin
(let _148_920 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _148_919 -> Some (_148_919)) _148_920))
end)
end)
in (
# 1093 "FStar.TypeChecker.Util.fst"
let is_var = (fun e -> (match ((let _148_923 = (FStar_Syntax_Subst.compress e)
in _148_923.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (_63_1471) -> begin
true
end
| _63_1474 -> begin
false
end))
in (
# 1096 "FStar.TypeChecker.Util.fst"
let decorate = (fun e t -> (
# 1097 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((
# 1099 "FStar.TypeChecker.Util.fst"
let _63_1481 = x
in {FStar_Syntax_Syntax.ppname = _63_1481.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_1481.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| _63_1484 -> begin
(
# 1100 "FStar.TypeChecker.Util.fst"
let _63_1485 = e
in (let _148_928 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _63_1485.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _148_928; FStar_Syntax_Syntax.pos = _63_1485.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _63_1485.FStar_Syntax_Syntax.vars}))
end)))
in (
# 1101 "FStar.TypeChecker.Util.fst"
let env = (
# 1101 "FStar.TypeChecker.Util.fst"
let _63_1487 = env
in (let _148_929 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _63_1487.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _63_1487.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _63_1487.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _63_1487.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _63_1487.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _63_1487.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _63_1487.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _63_1487.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _63_1487.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _63_1487.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _63_1487.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _63_1487.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _63_1487.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _63_1487.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _63_1487.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _148_929; FStar_TypeChecker_Env.is_iface = _63_1487.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _63_1487.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _63_1487.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _63_1487.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _63_1487.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _63_1487.FStar_TypeChecker_Env.use_bv_sorts}))
in (match ((check env t1 t2)) with
| None -> begin
(let _148_933 = (let _148_932 = (let _148_931 = (FStar_TypeChecker_Errors.expected_expression_of_type env t2 e t1)
in (let _148_930 = (FStar_TypeChecker_Env.get_range env)
in (_148_931, _148_930)))
in FStar_Syntax_Syntax.Error (_148_932))
in (Prims.raise _148_933))
end
| Some (g) -> begin
(
# 1105 "FStar.TypeChecker.Util.fst"
let _63_1493 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _148_934 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _148_934))
end else begin
()
end
in (let _148_935 = (decorate e t2)
in (_148_935, g)))
end)))))))

# 1110 "FStar.TypeChecker.Util.fst"
let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (
# 1111 "FStar.TypeChecker.Util.fst"
let discharge = (fun g -> (
# 1112 "FStar.TypeChecker.Util.fst"
let _63_1500 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (
# 1114 "FStar.TypeChecker.Util.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _148_945 = (discharge g)
in (let _148_944 = (lc.FStar_Syntax_Syntax.comp ())
in (_148_945, _148_944)))
end else begin
(
# 1117 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 1118 "FStar.TypeChecker.Util.fst"
let steps = (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.DeltaComp)::[]
in (
# 1119 "FStar.TypeChecker.Util.fst"
let c = (let _148_946 = (FStar_TypeChecker_Normalize.normalize_comp steps env c)
in (FStar_All.pipe_right _148_946 FStar_Syntax_Util.comp_to_comp_typ))
in (
# 1120 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 1121 "FStar.TypeChecker.Util.fst"
let _63_1511 = (destruct_comp c)
in (match (_63_1511) with
| (t, wp, _63_1510) -> begin
(
# 1122 "FStar.TypeChecker.Util.fst"
let vc = (let _148_954 = (let _148_948 = (let _148_947 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_148_947)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _148_948 env md md.FStar_Syntax_Syntax.trivial))
in (let _148_953 = (let _148_951 = (FStar_Syntax_Syntax.as_arg t)
in (let _148_950 = (let _148_949 = (FStar_Syntax_Syntax.as_arg wp)
in (_148_949)::[])
in (_148_951)::_148_950))
in (let _148_952 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk_Tm_app _148_954 _148_953 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _148_952))))
in (
# 1123 "FStar.TypeChecker.Util.fst"
let _63_1513 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _148_955 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _148_955))
end else begin
()
end
in (
# 1125 "FStar.TypeChecker.Util.fst"
let g = (let _148_956 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _148_956))
in (let _148_958 = (discharge g)
in (let _148_957 = (FStar_Syntax_Syntax.mk_Comp c)
in (_148_958, _148_957))))))
end))))))
end)))

# 1131 "FStar.TypeChecker.Util.fst"
let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (
# 1132 "FStar.TypeChecker.Util.fst"
let short_bin_op = (fun f _63_5 -> (match (_63_5) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (fst, _63_1524)::[] -> begin
(f fst)
end
| _63_1528 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (
# 1137 "FStar.TypeChecker.Util.fst"
let op_and_e = (fun e -> (let _148_979 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _148_979 (fun _148_978 -> FStar_TypeChecker_Common.NonTrivial (_148_978)))))
in (
# 1138 "FStar.TypeChecker.Util.fst"
let op_or_e = (fun e -> (let _148_984 = (let _148_982 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _148_982))
in (FStar_All.pipe_right _148_984 (fun _148_983 -> FStar_TypeChecker_Common.NonTrivial (_148_983)))))
in (
# 1139 "FStar.TypeChecker.Util.fst"
let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _148_987 -> FStar_TypeChecker_Common.NonTrivial (_148_987))))
in (
# 1140 "FStar.TypeChecker.Util.fst"
let op_or_t = (fun t -> (let _148_991 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _148_991 (fun _148_990 -> FStar_TypeChecker_Common.NonTrivial (_148_990)))))
in (
# 1141 "FStar.TypeChecker.Util.fst"
let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _148_994 -> FStar_TypeChecker_Common.NonTrivial (_148_994))))
in (
# 1143 "FStar.TypeChecker.Util.fst"
let short_op_ite = (fun _63_6 -> (match (_63_6) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (guard, _63_1543)::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| _then::(guard, _63_1548)::[] -> begin
(let _148_998 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _148_998 (fun _148_997 -> FStar_TypeChecker_Common.NonTrivial (_148_997))))
end
| _63_1553 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (
# 1148 "FStar.TypeChecker.Util.fst"
let table = ((FStar_Syntax_Const.op_And, (short_bin_op op_and_e)))::((FStar_Syntax_Const.op_Or, (short_bin_op op_or_e)))::((FStar_Syntax_Const.and_lid, (short_bin_op op_and_t)))::((FStar_Syntax_Const.or_lid, (short_bin_op op_or_t)))::((FStar_Syntax_Const.imp_lid, (short_bin_op op_imp_t)))::((FStar_Syntax_Const.ite_lid, short_op_ite))::[]
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(
# 1158 "FStar.TypeChecker.Util.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((FStar_Util.find_map table (fun _63_1561 -> (match (_63_1561) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _148_1031 = (mk seen_args)
in Some (_148_1031))
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
| _63_1566 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))

# 1165 "FStar.TypeChecker.Util.fst"
let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (match ((let _148_1034 = (FStar_Syntax_Util.un_uinst l)
in _148_1034.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| _63_1571 -> begin
false
end))

# 1186 "FStar.TypeChecker.Util.fst"
let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (
# 1187 "FStar.TypeChecker.Util.fst"
let pos = (fun bs -> (match (bs) with
| (hd, _63_1580)::_63_1577 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| _63_1584 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| (_63_1588, Some (FStar_Syntax_Syntax.Implicit (_63_1590)))::_63_1586 -> begin
bs
end
| _63_1596 -> begin
(match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
bs
end
| Some (t) -> begin
(match ((let _148_1041 = (FStar_Syntax_Subst.compress t)
in _148_1041.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', _63_1602) -> begin
(match ((FStar_Util.prefix_until (fun _63_7 -> (match (_63_7) with
| (_63_1607, Some (FStar_Syntax_Syntax.Implicit (_63_1609))) -> begin
false
end
| _63_1614 -> begin
true
end)) bs')) with
| None -> begin
bs
end
| Some ([], _63_1618, _63_1620) -> begin
bs
end
| Some (imps, _63_1625, _63_1627) -> begin
if (FStar_All.pipe_right imps (FStar_Util.for_all (fun _63_1633 -> (match (_63_1633) with
| (x, _63_1632) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end)))) then begin
(
# 1203 "FStar.TypeChecker.Util.fst"
let r = (pos bs)
in (
# 1204 "FStar.TypeChecker.Util.fst"
let imps = (FStar_All.pipe_right imps (FStar_List.map (fun _63_1637 -> (match (_63_1637) with
| (x, i) -> begin
(let _148_1045 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in (_148_1045, i))
end))))
in (FStar_List.append imps bs)))
end else begin
bs
end
end)
end
| _63_1640 -> begin
bs
end)
end)
end)))




