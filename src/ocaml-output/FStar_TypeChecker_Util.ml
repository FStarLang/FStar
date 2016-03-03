
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
let new_implicit_var : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.uvar * FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env k -> (match ((FStar_Syntax_Util.destruct k FStar_Syntax_Const.range_of_lid)) with
| Some (_69_48::(tm, _69_45)::[]) -> begin
(
# 107 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))) None tm.FStar_Syntax_Syntax.pos)
in (t, [], FStar_TypeChecker_Rel.trivial_guard))
end
| _69_53 -> begin
(
# 111 "FStar.TypeChecker.Util.fst"
let _69_56 = (new_uvar_aux env k)
in (match (_69_56) with
| (t, u) -> begin
(
# 112 "FStar.TypeChecker.Util.fst"
let g = (
# 112 "FStar.TypeChecker.Util.fst"
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

# 115 "FStar.TypeChecker.Util.fst"
let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun r t -> (
# 116 "FStar.TypeChecker.Util.fst"
let uvs = (FStar_Syntax_Free.uvars t)
in if (not ((FStar_Util.set_is_empty uvs))) then begin
(
# 119 "FStar.TypeChecker.Util.fst"
let us = (let _150_42 = (let _150_41 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun _69_66 -> (match (_69_66) with
| (x, _69_65) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) _150_41))
in (FStar_All.pipe_right _150_42 (FStar_String.concat ", ")))
in (
# 121 "FStar.TypeChecker.Util.fst"
let hide_uvar_nums_saved = (FStar_ST.read FStar_Options.hide_uvar_nums)
in (
# 122 "FStar.TypeChecker.Util.fst"
let print_implicits_saved = (FStar_ST.read FStar_Options.print_implicits)
in (
# 123 "FStar.TypeChecker.Util.fst"
let _69_70 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums false)
in (
# 124 "FStar.TypeChecker.Util.fst"
let _69_72 = (FStar_ST.op_Colon_Equals FStar_Options.print_implicits true)
in (
# 125 "FStar.TypeChecker.Util.fst"
let _69_74 = (let _150_44 = (let _150_43 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us _150_43))
in (FStar_TypeChecker_Errors.report r _150_44))
in (
# 128 "FStar.TypeChecker.Util.fst"
let _69_76 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums hide_uvar_nums_saved)
in (FStar_ST.op_Colon_Equals FStar_Options.print_implicits print_implicits_saved))))))))
end else begin
()
end))

# 135 "FStar.TypeChecker.Util.fst"
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

# 139 "FStar.TypeChecker.Util.fst"
let force_sort = (fun s -> (let _150_51 = (force_sort' s)
in (FStar_Syntax_Syntax.mk _150_51 None s.FStar_Syntax_Syntax.pos)))

# 141 "FStar.TypeChecker.Util.fst"
let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env _69_91 -> (match (_69_91) with
| {FStar_Syntax_Syntax.lbname = _69_90; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _69_86; FStar_Syntax_Syntax.lbdef = e} -> begin
(
# 142 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 145 "FStar.TypeChecker.Util.fst"
let _69_94 = if (univ_vars <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (
# 146 "FStar.TypeChecker.Util.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 147 "FStar.TypeChecker.Util.fst"
let mk_binder = (fun scope a -> (match (a.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 149 "FStar.TypeChecker.Util.fst"
let _69_104 = (FStar_Syntax_Util.type_u ())
in (match (_69_104) with
| (k, _69_103) -> begin
(
# 150 "FStar.TypeChecker.Util.fst"
let t = (let _150_60 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right _150_60 Prims.fst))
in ((
# 151 "FStar.TypeChecker.Util.fst"
let _69_106 = a
in {FStar_Syntax_Syntax.ppname = _69_106.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_106.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), false))
end))
end
| _69_109 -> begin
(a, true)
end))
in (
# 154 "FStar.TypeChecker.Util.fst"
let rec aux = (fun vars e -> (
# 155 "FStar.TypeChecker.Util.fst"
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
# 161 "FStar.TypeChecker.Util.fst"
let _69_147 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _69_134 _69_137 -> (match ((_69_134, _69_137)) with
| ((scope, bs, check), (a, imp)) -> begin
(
# 162 "FStar.TypeChecker.Util.fst"
let _69_140 = (mk_binder scope a)
in (match (_69_140) with
| (tb, c) -> begin
(
# 163 "FStar.TypeChecker.Util.fst"
let b = (tb, imp)
in (
# 164 "FStar.TypeChecker.Util.fst"
let bs = (FStar_List.append bs ((b)::[]))
in (
# 165 "FStar.TypeChecker.Util.fst"
let scope = (FStar_List.append scope ((b)::[]))
in (scope, bs, (c || check)))))
end))
end)) (vars, [], false)))
in (match (_69_147) with
| (scope, bs, check) -> begin
(
# 169 "FStar.TypeChecker.Util.fst"
let _69_150 = (aux scope body)
in (match (_69_150) with
| (res, check_res) -> begin
(
# 170 "FStar.TypeChecker.Util.fst"
let c = (FStar_Syntax_Util.ml_comp res r)
in (
# 171 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Util.arrow bs c)
in (
# 172 "FStar.TypeChecker.Util.fst"
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
# 177 "FStar.TypeChecker.Util.fst"
let _69_159 = (let _150_71 = (t_binders env)
in (aux _150_71 e))
in (match (_69_159) with
| (t, b) -> begin
([], t, b)
end))))))
end
| _69_161 -> begin
(
# 181 "FStar.TypeChecker.Util.fst"
let _69_164 = (FStar_Syntax_Subst.open_univ_vars univ_vars t)
in (match (_69_164) with
| (univ_vars, t) -> begin
(univ_vars, t, false)
end))
end))
end))

# 192 "FStar.TypeChecker.Util.fst"
let pat_as_exps : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term Prims.list * FStar_Syntax_Syntax.pat) = (fun allow_implicits env p -> (
# 197 "FStar.TypeChecker.Util.fst"
let rec pat_as_arg_with_env = (fun allow_wc_dependence env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(
# 206 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) None p.FStar_Syntax_Syntax.p)
in ([], [], [], env, e, p))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _69_177) -> begin
(
# 210 "FStar.TypeChecker.Util.fst"
let _69_183 = (FStar_Syntax_Util.type_u ())
in (match (_69_183) with
| (k, _69_182) -> begin
(
# 211 "FStar.TypeChecker.Util.fst"
let t = (new_uvar env k)
in (
# 212 "FStar.TypeChecker.Util.fst"
let x = (
# 212 "FStar.TypeChecker.Util.fst"
let _69_185 = x
in {FStar_Syntax_Syntax.ppname = _69_185.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_185.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (
# 213 "FStar.TypeChecker.Util.fst"
let _69_190 = (let _150_84 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _150_84 t))
in (match (_69_190) with
| (e, u) -> begin
(
# 214 "FStar.TypeChecker.Util.fst"
let p = (
# 214 "FStar.TypeChecker.Util.fst"
let _69_191 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, e)); FStar_Syntax_Syntax.ty = _69_191.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _69_191.FStar_Syntax_Syntax.p})
in ([], [], [], env, e, p))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 218 "FStar.TypeChecker.Util.fst"
let _69_199 = (FStar_Syntax_Util.type_u ())
in (match (_69_199) with
| (t, _69_198) -> begin
(
# 219 "FStar.TypeChecker.Util.fst"
let x = (
# 219 "FStar.TypeChecker.Util.fst"
let _69_200 = x
in (let _150_85 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _69_200.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_200.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_85}))
in (
# 220 "FStar.TypeChecker.Util.fst"
let env = if allow_wc_dependence then begin
(FStar_TypeChecker_Env.push_bv env x)
end else begin
env
end
in (
# 221 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in ((x)::[], [], (x)::[], env, e, p))))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 225 "FStar.TypeChecker.Util.fst"
let _69_210 = (FStar_Syntax_Util.type_u ())
in (match (_69_210) with
| (t, _69_209) -> begin
(
# 226 "FStar.TypeChecker.Util.fst"
let x = (
# 226 "FStar.TypeChecker.Util.fst"
let _69_211 = x
in (let _150_86 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _69_211.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_211.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_86}))
in (
# 227 "FStar.TypeChecker.Util.fst"
let env = (FStar_TypeChecker_Env.push_bv env x)
in (
# 228 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in ((x)::[], (x)::[], [], env, e, p))))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 232 "FStar.TypeChecker.Util.fst"
let _69_244 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _69_226 _69_229 -> (match ((_69_226, _69_229)) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(
# 233 "FStar.TypeChecker.Util.fst"
let _69_236 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_69_236) with
| (b', a', w', env, te, pat) -> begin
(
# 234 "FStar.TypeChecker.Util.fst"
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
# 237 "FStar.TypeChecker.Util.fst"
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
# 243 "FStar.TypeChecker.Util.fst"
let _69_246 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _69_246.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _69_246.FStar_Syntax_Syntax.p}))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (_69_249) -> begin
(FStar_All.failwith "impossible")
end))
in (
# 247 "FStar.TypeChecker.Util.fst"
let rec elaborate_pat = (fun env p -> (
# 248 "FStar.TypeChecker.Util.fst"
let maybe_dot = (fun inaccessible a r -> if (allow_implicits && inaccessible) then begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term ((a, FStar_Syntax_Syntax.tun))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end else begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var (a)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end)
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 254 "FStar.TypeChecker.Util.fst"
let pats = (FStar_List.map (fun _69_264 -> (match (_69_264) with
| (p, imp) -> begin
(let _150_108 = (elaborate_pat env p)
in (_150_108, imp))
end)) pats)
in (
# 255 "FStar.TypeChecker.Util.fst"
let _69_269 = (FStar_TypeChecker_Env.lookup_datacon env (Prims.fst fv).FStar_Syntax_Syntax.v)
in (match (_69_269) with
| (_69_267, t) -> begin
(
# 256 "FStar.TypeChecker.Util.fst"
let _69_273 = (FStar_Syntax_Util.arrow_formals t)
in (match (_69_273) with
| (f, _69_272) -> begin
(
# 257 "FStar.TypeChecker.Util.fst"
let rec aux = (fun formals pats -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _69_284::_69_282) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v)))))
end
| (_69_290::_69_288, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun _69_296 -> (match (_69_296) with
| (t, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(
# 263 "FStar.TypeChecker.Util.fst"
let a = (let _150_115 = (let _150_114 = (FStar_Syntax_Syntax.range_of_bv t)
in Some (_150_114))
in (FStar_Syntax_Syntax.new_bv _150_115 FStar_Syntax_Syntax.tun))
in (
# 264 "FStar.TypeChecker.Util.fst"
let r = (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v)
in (let _150_116 = (maybe_dot inaccessible a r)
in (_150_116, true))))
end
| _69_303 -> begin
(let _150_120 = (let _150_119 = (let _150_118 = (let _150_117 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _150_117))
in (_150_118, (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v)))
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
# 276 "FStar.TypeChecker.Util.fst"
let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (
# 277 "FStar.TypeChecker.Util.fst"
let p = (maybe_dot inaccessible a (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v))
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
# 283 "FStar.TypeChecker.Util.fst"
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
# 287 "FStar.TypeChecker.Util.fst"
let one_pat = (fun allow_wc_dependence env p -> (
# 288 "FStar.TypeChecker.Util.fst"
let p = (elaborate_pat env p)
in (
# 289 "FStar.TypeChecker.Util.fst"
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
# 294 "FStar.TypeChecker.Util.fst"
let top_level_pat_as_args = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_disj (q::pats) -> begin
(
# 301 "FStar.TypeChecker.Util.fst"
let _69_367 = (one_pat false env q)
in (match (_69_367) with
| (b, a, _69_364, te, q) -> begin
(
# 302 "FStar.TypeChecker.Util.fst"
let _69_382 = (FStar_List.fold_right (fun p _69_372 -> (match (_69_372) with
| (w, args, pats) -> begin
(
# 303 "FStar.TypeChecker.Util.fst"
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
# 308 "FStar.TypeChecker.Util.fst"
let _69_383 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((q)::pats); FStar_Syntax_Syntax.ty = _69_383.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _69_383.FStar_Syntax_Syntax.p})))
end))
end))
end
| _69_386 -> begin
(
# 311 "FStar.TypeChecker.Util.fst"
let _69_394 = (one_pat true env p)
in (match (_69_394) with
| (b, _69_389, _69_391, arg, p) -> begin
(let _150_153 = (let _150_152 = (FStar_Syntax_Syntax.as_arg arg)
in (_150_152)::[])
in (b, _150_153, p))
end))
end))
in (
# 314 "FStar.TypeChecker.Util.fst"
let _69_398 = (top_level_pat_as_args env p)
in (match (_69_398) with
| (b, args, p) -> begin
(
# 315 "FStar.TypeChecker.Util.fst"
let exps = (FStar_All.pipe_right args (FStar_List.map Prims.fst))
in (b, exps, p))
end)))))))

# 318 "FStar.TypeChecker.Util.fst"
let decorate_pattern : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.pat = (fun env p exps -> (
# 319 "FStar.TypeChecker.Util.fst"
let qq = p
in (
# 320 "FStar.TypeChecker.Util.fst"
let rec aux = (fun p e -> (
# 321 "FStar.TypeChecker.Util.fst"
let pkg = (fun q t -> (FStar_Syntax_Syntax.withinfo q t p.FStar_Syntax_Syntax.p))
in (
# 322 "FStar.TypeChecker.Util.fst"
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
# 330 "FStar.TypeChecker.Util.fst"
let _69_431 = if (not ((FStar_Syntax_Syntax.bv_eq x y))) then begin
(let _150_171 = (let _150_170 = (FStar_Syntax_Print.bv_to_string x)
in (let _150_169 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _150_170 _150_169)))
in (FStar_All.failwith _150_171))
end else begin
()
end
in (
# 332 "FStar.TypeChecker.Util.fst"
let _69_433 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _150_173 = (FStar_Syntax_Print.bv_to_string x)
in (let _150_172 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _150_173 _150_172)))
end else begin
()
end
in (
# 334 "FStar.TypeChecker.Util.fst"
let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (
# 335 "FStar.TypeChecker.Util.fst"
let x = (
# 335 "FStar.TypeChecker.Util.fst"
let _69_436 = x
in {FStar_Syntax_Syntax.ppname = _69_436.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_436.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x)) s.FStar_Syntax_Syntax.n)))))
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(
# 339 "FStar.TypeChecker.Util.fst"
let _69_444 = if (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation) then begin
(let _150_176 = (let _150_175 = (FStar_Syntax_Print.bv_to_string x)
in (let _150_174 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _150_175 _150_174)))
in (FStar_All.failwith _150_176))
end else begin
()
end
in (
# 341 "FStar.TypeChecker.Util.fst"
let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (
# 342 "FStar.TypeChecker.Util.fst"
let x = (
# 342 "FStar.TypeChecker.Util.fst"
let _69_447 = x
in {FStar_Syntax_Syntax.ppname = _69_447.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_447.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x)) s.FStar_Syntax_Syntax.n))))
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _69_452), _69_456) -> begin
(
# 346 "FStar.TypeChecker.Util.fst"
let s = (force_sort e)
in (
# 347 "FStar.TypeChecker.Util.fst"
let x = (
# 347 "FStar.TypeChecker.Util.fst"
let _69_459 = x
in {FStar_Syntax_Syntax.ppname = _69_459.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_459.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
(
# 351 "FStar.TypeChecker.Util.fst"
let _69_469 = if (not ((FStar_Syntax_Syntax.fv_eq fv fv'))) then begin
(let _150_177 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" (Prims.fst fv).FStar_Syntax_Syntax.v.FStar_Ident.str (Prims.fst fv').FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _150_177))
end else begin
()
end
in (let _150_178 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv', []))) _150_178)))
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
(
# 358 "FStar.TypeChecker.Util.fst"
let _69_512 = if (let _150_179 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right _150_179 Prims.op_Negation)) then begin
(let _150_180 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" (Prims.fst fv).FStar_Syntax_Syntax.v.FStar_Ident.str (Prims.fst fv').FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _150_180))
end else begin
()
end
in (
# 361 "FStar.TypeChecker.Util.fst"
let fv = fv'
in (
# 362 "FStar.TypeChecker.Util.fst"
let rec match_args = (fun matched_pats args argpats -> (match ((args, argpats)) with
| ([], []) -> begin
(let _150_187 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev matched_pats)))) _150_187))
end
| (arg::args, (argpat, _69_528)::argpats) -> begin
(match ((arg, argpat.FStar_Syntax_Syntax.v)) with
| ((e, Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (_69_538)) -> begin
(
# 367 "FStar.TypeChecker.Util.fst"
let x = (let _150_188 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _150_188))
in (
# 368 "FStar.TypeChecker.Util.fst"
let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((e, imp), _69_547) -> begin
(
# 372 "FStar.TypeChecker.Util.fst"
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
# 385 "FStar.TypeChecker.Util.fst"
let ps = (FStar_List.map2 aux ps exps)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj (ps)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p))
end
| (_69_561, e::[]) -> begin
(aux p e)
end
| _69_566 -> begin
(FStar_All.failwith "Unexpected number of patterns")
end))))

# 393 "FStar.TypeChecker.Util.fst"
let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (
# 394 "FStar.TypeChecker.Util.fst"
let topt = Some (pat.FStar_Syntax_Syntax.ty)
in (
# 395 "FStar.TypeChecker.Util.fst"
let mk = (fun f -> (FStar_Syntax_Syntax.mk f topt pat.FStar_Syntax_Syntax.p))
in (
# 397 "FStar.TypeChecker.Util.fst"
let pat_as_arg = (fun _69_574 -> (match (_69_574) with
| (p, i) -> begin
(
# 398 "FStar.TypeChecker.Util.fst"
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
# 412 "FStar.TypeChecker.Util.fst"
let _69_592 = (let _150_209 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _150_209 FStar_List.unzip))
in (match (_69_592) with
| (vars, args) -> begin
(
# 413 "FStar.TypeChecker.Util.fst"
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

# 423 "FStar.TypeChecker.Util.fst"
let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (
# 424 "FStar.TypeChecker.Util.fst"
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

# 430 "FStar.TypeChecker.Util.fst"
let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (
# 431 "FStar.TypeChecker.Util.fst"
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

# 437 "FStar.TypeChecker.Util.fst"
let norm_eff_name : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (
# 438 "FStar.TypeChecker.Util.fst"
let cache = (FStar_Util.smap_create 20)
in (fun env l -> (
# 440 "FStar.TypeChecker.Util.fst"
let rec find = (fun l -> (match ((FStar_TypeChecker_Env.lookup_effect_abbrev env FStar_Syntax_Syntax.U_unknown l)) with
| None -> begin
None
end
| Some (_69_632, c) -> begin
(
# 444 "FStar.TypeChecker.Util.fst"
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
# 448 "FStar.TypeChecker.Util.fst"
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
# 453 "FStar.TypeChecker.Util.fst"
let _69_646 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))

# 459 "FStar.TypeChecker.Util.fst"
let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (
# 460 "FStar.TypeChecker.Util.fst"
let _69_657 = (let _150_255 = (norm_eff_name env l1)
in (let _150_254 = (norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _150_255 _150_254)))
in (match (_69_657) with
| (m, _69_654, _69_656) -> begin
m
end)))

# 463 "FStar.TypeChecker.Util.fst"
let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> if ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2)) then begin
FStar_Syntax_Const.effect_Tot_lid
end else begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)

# 469 "FStar.TypeChecker.Util.fst"
let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)) = (fun env c1 c2 -> (
# 470 "FStar.TypeChecker.Util.fst"
let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (
# 471 "FStar.TypeChecker.Util.fst"
let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (
# 472 "FStar.TypeChecker.Util.fst"
let _69_669 = (FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (_69_669) with
| (m, lift1, lift2) -> begin
(
# 473 "FStar.TypeChecker.Util.fst"
let m1 = (lift_comp c1 m lift1)
in (
# 474 "FStar.TypeChecker.Util.fst"
let m2 = (lift_comp c2 m lift2)
in (
# 475 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (
# 476 "FStar.TypeChecker.Util.fst"
let _69_675 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (_69_675) with
| (a, kwp) -> begin
(let _150_269 = (destruct_comp m1)
in (let _150_268 = (destruct_comp m2)
in ((md, a, kwp), _150_269, _150_268)))
end)))))
end)))))

# 479 "FStar.TypeChecker.Util.fst"
let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (
# 480 "FStar.TypeChecker.Util.fst"
let l = (norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)))

# 483 "FStar.TypeChecker.Util.fst"
let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (
# 484 "FStar.TypeChecker.Util.fst"
let l = (norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid))))

# 488 "FStar.TypeChecker.Util.fst"
let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md result wp wlp flags -> (let _150_292 = (let _150_291 = (let _150_290 = (FStar_Syntax_Syntax.as_arg wp)
in (let _150_289 = (let _150_288 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_288)::[])
in (_150_290)::_150_289))
in {FStar_Syntax_Syntax.effect_name = md.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = _150_291; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp _150_292)))

# 494 "FStar.TypeChecker.Util.fst"
let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (
# 495 "FStar.TypeChecker.Util.fst"
let _69_689 = lc
in (let _150_299 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _69_689.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _150_299; FStar_Syntax_Syntax.cflags = _69_689.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _69_691 -> (match (()) with
| () -> begin
(let _150_298 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _150_298))
end))})))

# 498 "FStar.TypeChecker.Util.fst"
let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _150_302 = (FStar_Syntax_Subst.compress t)
in _150_302.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_69_694) -> begin
true
end
| _69_697 -> begin
false
end))

# 502 "FStar.TypeChecker.Util.fst"
let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v -> (
# 504 "FStar.TypeChecker.Util.fst"
let c = if (let _150_309 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation _150_309)) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(
# 507 "FStar.TypeChecker.Util.fst"
let m = (let _150_310 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must _150_310))
in (
# 508 "FStar.TypeChecker.Util.fst"
let _69_704 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_69_704) with
| (a, kwp) -> begin
(
# 509 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 510 "FStar.TypeChecker.Util.fst"
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
# 511 "FStar.TypeChecker.Util.fst"
let wlp = wp
in (mk_comp m t wp wlp ((FStar_Syntax_Syntax.RETURN)::[])))))
end)))
end
in (
# 513 "FStar.TypeChecker.Util.fst"
let _69_709 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return"))) then begin
(let _150_321 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _150_320 = (FStar_Syntax_Print.term_to_string v)
in (let _150_319 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _150_321 _150_320 _150_319))))
end else begin
()
end
in c)))

# 518 "FStar.TypeChecker.Util.fst"
let bind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun env e1opt lc1 _69_716 -> (match (_69_716) with
| (b, lc2) -> begin
(
# 519 "FStar.TypeChecker.Util.fst"
let _69_724 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(
# 521 "FStar.TypeChecker.Util.fst"
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
# 527 "FStar.TypeChecker.Util.fst"
let bind_it = (fun _69_727 -> (match (()) with
| () -> begin
(
# 528 "FStar.TypeChecker.Util.fst"
let c1 = (lc1.FStar_Syntax_Syntax.comp ())
in (
# 529 "FStar.TypeChecker.Util.fst"
let c2 = (lc2.FStar_Syntax_Syntax.comp ())
in (
# 530 "FStar.TypeChecker.Util.fst"
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
# 539 "FStar.TypeChecker.Util.fst"
let try_simplify = (fun _69_736 -> (match (()) with
| () -> begin
(
# 540 "FStar.TypeChecker.Util.fst"
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
# 567 "FStar.TypeChecker.Util.fst"
let _69_767 = (lift_and_destruct env c1 c2)
in (match (_69_767) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(
# 568 "FStar.TypeChecker.Util.fst"
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
# 571 "FStar.TypeChecker.Util.fst"
let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp None))
in (
# 572 "FStar.TypeChecker.Util.fst"
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
# 573 "FStar.TypeChecker.Util.fst"
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
# 574 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t2)))::[]) kwp)
in (
# 575 "FStar.TypeChecker.Util.fst"
let us = (let _150_375 = (env.FStar_TypeChecker_Env.universe_of env t1)
in (let _150_374 = (let _150_373 = (env.FStar_TypeChecker_Env.universe_of env t2)
in (_150_373)::[])
in (_150_375)::_150_374))
in (
# 576 "FStar.TypeChecker.Util.fst"
let wp = (let _150_376 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _150_376 wp_args None t2.FStar_Syntax_Syntax.pos))
in (
# 577 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_377 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wlp)
in (FStar_Syntax_Syntax.mk_Tm_app _150_377 wlp_args None t2.FStar_Syntax_Syntax.pos))
in (
# 578 "FStar.TypeChecker.Util.fst"
let c = (mk_comp md t2 wp wlp [])
in c)))))))))
end))
end)))))
end))
in (let _150_378 = (join_lcomp env lc1 lc2)
in {FStar_Syntax_Syntax.eff_name = _150_378; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it})))
end))

# 585 "FStar.TypeChecker.Util.fst"
let lift_formula : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t mk_wp mk_wlp f -> (
# 586 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 587 "FStar.TypeChecker.Util.fst"
let _69_789 = (FStar_TypeChecker_Env.wp_signature env md_pure.FStar_Syntax_Syntax.mname)
in (match (_69_789) with
| (a, kwp) -> begin
(
# 588 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 589 "FStar.TypeChecker.Util.fst"
let wp = (let _150_392 = (let _150_391 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_390 = (let _150_389 = (FStar_Syntax_Syntax.as_arg f)
in (_150_389)::[])
in (_150_391)::_150_390))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wp _150_392 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (
# 590 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_396 = (let _150_395 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_394 = (let _150_393 = (FStar_Syntax_Syntax.as_arg f)
in (_150_393)::[])
in (_150_395)::_150_394))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wlp _150_396 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (mk_comp md_pure FStar_TypeChecker_Common.t_unit wp wlp []))))
end))))

# 593 "FStar.TypeChecker.Util.fst"
let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((f, FStar_Syntax_Syntax.Meta_labeled ((reason, r, false))))) None f.FStar_Syntax_Syntax.pos))

# 596 "FStar.TypeChecker.Util.fst"
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

# 603 "FStar.TypeChecker.Util.fst"
let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 605 "FStar.TypeChecker.Util.fst"
let _69_809 = g
in (let _150_429 = (let _150_428 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_150_428))
in {FStar_TypeChecker_Env.guard_f = _150_429; FStar_TypeChecker_Env.deferred = _69_809.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _69_809.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _69_809.FStar_TypeChecker_Env.implicits}))
end))

# 607 "FStar.TypeChecker.Util.fst"
let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(
# 609 "FStar.TypeChecker.Util.fst"
let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| _69_820 -> begin
g2
end))

# 613 "FStar.TypeChecker.Util.fst"
let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (
# 614 "FStar.TypeChecker.Util.fst"
let weaken = (fun _69_825 -> (match (()) with
| () -> begin
(
# 615 "FStar.TypeChecker.Util.fst"
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
# 621 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 622 "FStar.TypeChecker.Util.fst"
let _69_834 = (destruct_comp c)
in (match (_69_834) with
| (res_t, wp, wlp) -> begin
(
# 623 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 624 "FStar.TypeChecker.Util.fst"
let us = (let _150_442 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_442)::[])
in (
# 625 "FStar.TypeChecker.Util.fst"
let wp = (let _150_449 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _150_448 = (let _150_447 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_446 = (let _150_445 = (FStar_Syntax_Syntax.as_arg f)
in (let _150_444 = (let _150_443 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_443)::[])
in (_150_445)::_150_444))
in (_150_447)::_150_446))
in (FStar_Syntax_Syntax.mk_Tm_app _150_449 _150_448 None wp.FStar_Syntax_Syntax.pos)))
in (
# 626 "FStar.TypeChecker.Util.fst"
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
# 628 "FStar.TypeChecker.Util.fst"
let _69_839 = lc
in {FStar_Syntax_Syntax.eff_name = _69_839.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _69_839.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _69_839.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))

# 630 "FStar.TypeChecker.Util.fst"
let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> if (FStar_TypeChecker_Rel.is_trivial g0) then begin
(lc, g0)
end else begin
(
# 634 "FStar.TypeChecker.Util.fst"
let _69_846 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_476 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _150_475 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _150_476 _150_475)))
end else begin
()
end
in (
# 638 "FStar.TypeChecker.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _69_2 -> (match (_69_2) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _69_852 -> begin
[]
end))))
in (
# 639 "FStar.TypeChecker.Util.fst"
let strengthen = (fun _69_855 -> (match (()) with
| () -> begin
(
# 640 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 641 "FStar.TypeChecker.Util.fst"
let g0 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (match ((FStar_TypeChecker_Rel.guard_form g0)) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 645 "FStar.TypeChecker.Util.fst"
let c = if ((FStar_Syntax_Util.is_pure_or_ghost_comp c) && (not ((FStar_Syntax_Util.is_partial_return c)))) then begin
(
# 648 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.gen_bv "strengthen_pre_x" None (FStar_Syntax_Util.comp_result c))
in (
# 649 "FStar.TypeChecker.Util.fst"
let xret = (let _150_481 = (let _150_480 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _150_480))
in (FStar_Syntax_Util.comp_set_flags _150_481 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (
# 650 "FStar.TypeChecker.Util.fst"
let lc = (bind env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), (FStar_Syntax_Util.lcomp_of_comp xret)))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (
# 654 "FStar.TypeChecker.Util.fst"
let _69_865 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_483 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _150_482 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _150_483 _150_482)))
end else begin
()
end
in (
# 659 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 660 "FStar.TypeChecker.Util.fst"
let _69_871 = (destruct_comp c)
in (match (_69_871) with
| (res_t, wp, wlp) -> begin
(
# 661 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 662 "FStar.TypeChecker.Util.fst"
let us = (let _150_484 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_484)::[])
in (
# 663 "FStar.TypeChecker.Util.fst"
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
# 664 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_500 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _150_499 = (let _150_498 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_497 = (let _150_496 = (FStar_Syntax_Syntax.as_arg f)
in (let _150_495 = (let _150_494 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_494)::[])
in (_150_496)::_150_495))
in (_150_498)::_150_497))
in (FStar_Syntax_Syntax.mk_Tm_app _150_500 _150_499 None wlp.FStar_Syntax_Syntax.pos)))
in (
# 666 "FStar.TypeChecker.Util.fst"
let _69_876 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_501 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _150_501))
end else begin
()
end
in (
# 670 "FStar.TypeChecker.Util.fst"
let c2 = (mk_comp md res_t wp wlp flags)
in c2))))))
end)))))
end)))
end))
in (let _150_505 = (
# 672 "FStar.TypeChecker.Util.fst"
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
# 675 "FStar.TypeChecker.Util.fst"
let _69_881 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _69_881.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _69_881.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _69_881.FStar_TypeChecker_Env.implicits}))))))
end)

# 677 "FStar.TypeChecker.Util.fst"
let record_application_site : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (
# 678 "FStar.TypeChecker.Util.fst"
let comp = (fun _69_887 -> (match (()) with
| () -> begin
(
# 679 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 680 "FStar.TypeChecker.Util.fst"
let res_t = (FStar_Syntax_Util.comp_result c)
in if (((FStar_Syntax_Util.is_trivial_wp c) || (let _150_514 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals _150_514 FStar_Syntax_Const.prims_lid))) || (FStar_Syntax_Syntax.is_teff res_t)) then begin
c
end else begin
(
# 685 "FStar.TypeChecker.Util.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (FStar_TypeChecker_Common.t_unit)))
in (
# 686 "FStar.TypeChecker.Util.fst"
let _69_895 = (strengthen_precondition (Some ((fun _69_891 -> (match (()) with
| () -> begin
"push"
end)))) env e (FStar_Syntax_Util.lcomp_of_comp c) g)
in (match (_69_895) with
| (c, _69_894) -> begin
(
# 687 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 688 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 689 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 690 "FStar.TypeChecker.Util.fst"
let us = (let _150_518 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_518)::[])
in (
# 691 "FStar.TypeChecker.Util.fst"
let xret = (let _150_523 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _150_522 = (let _150_521 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_520 = (let _150_519 = (FStar_Syntax_Syntax.as_arg xexp)
in (_150_519)::[])
in (_150_521)::_150_520))
in (FStar_Syntax_Syntax.mk_Tm_app _150_523 _150_522 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 692 "FStar.TypeChecker.Util.fst"
let xret_comp = (let _150_524 = (mk_comp md_pure res_t xret xret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_524))
in (
# 693 "FStar.TypeChecker.Util.fst"
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
# 695 "FStar.TypeChecker.Util.fst"
let _69_904 = lc
in {FStar_Syntax_Syntax.eff_name = _69_904.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _69_904.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _69_904.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = comp})))

# 697 "FStar.TypeChecker.Util.fst"
let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env comp res_t -> (
# 698 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 699 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 700 "FStar.TypeChecker.Util.fst"
let y = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 701 "FStar.TypeChecker.Util.fst"
let _69_914 = (let _150_538 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _150_537 = (FStar_Syntax_Syntax.bv_to_name y)
in (_150_538, _150_537)))
in (match (_69_914) with
| (xexp, yexp) -> begin
(
# 702 "FStar.TypeChecker.Util.fst"
let us = (let _150_539 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_539)::[])
in (
# 703 "FStar.TypeChecker.Util.fst"
let yret = (let _150_544 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _150_543 = (let _150_542 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_541 = (let _150_540 = (FStar_Syntax_Syntax.as_arg yexp)
in (_150_540)::[])
in (_150_542)::_150_541))
in (FStar_Syntax_Syntax.mk_Tm_app _150_544 _150_543 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 704 "FStar.TypeChecker.Util.fst"
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
# 705 "FStar.TypeChecker.Util.fst"
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
# 706 "FStar.TypeChecker.Util.fst"
let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (
# 707 "FStar.TypeChecker.Util.fst"
let lc = (bind env None (FStar_Syntax_Util.lcomp_of_comp comp) (Some (x), (FStar_Syntax_Util.lcomp_of_comp lc2)))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))

# 710 "FStar.TypeChecker.Util.fst"
let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (
# 711 "FStar.TypeChecker.Util.fst"
let comp = (fun _69_926 -> (match (()) with
| () -> begin
(
# 712 "FStar.TypeChecker.Util.fst"
let _69_942 = (let _150_574 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _150_573 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _150_574 _150_573)))
in (match (_69_942) with
| ((md, _69_929, _69_931), (res_t, wp_then, wlp_then), (_69_938, wp_else, wlp_else)) -> begin
(
# 713 "FStar.TypeChecker.Util.fst"
let us = (let _150_575 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_575)::[])
in (
# 714 "FStar.TypeChecker.Util.fst"
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
# 715 "FStar.TypeChecker.Util.fst"
let wp = (ifthenelse md res_t guard wp_then wp_else)
in (
# 716 "FStar.TypeChecker.Util.fst"
let wlp = (ifthenelse md res_t guard wlp_then wlp_else)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(
# 718 "FStar.TypeChecker.Util.fst"
let comp = (mk_comp md res_t wp wlp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(
# 720 "FStar.TypeChecker.Util.fst"
let wp = (let _150_602 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _150_601 = (let _150_600 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_599 = (let _150_598 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _150_597 = (let _150_596 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_596)::[])
in (_150_598)::_150_597))
in (_150_600)::_150_599))
in (FStar_Syntax_Syntax.mk_Tm_app _150_602 _150_601 None wp.FStar_Syntax_Syntax.pos)))
in (
# 721 "FStar.TypeChecker.Util.fst"
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

# 728 "FStar.TypeChecker.Util.fst"
let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (
# 729 "FStar.TypeChecker.Util.fst"
let eff = (FStar_List.fold_left (fun eff _69_962 -> (match (_69_962) with
| (_69_960, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (
# 730 "FStar.TypeChecker.Util.fst"
let bind_cases = (fun _69_965 -> (match (()) with
| () -> begin
(
# 731 "FStar.TypeChecker.Util.fst"
let us = (let _150_619 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_619)::[])
in (
# 732 "FStar.TypeChecker.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _150_639 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _150_638 = (let _150_636 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_635 = (let _150_634 = (FStar_Syntax_Syntax.as_arg g)
in (let _150_633 = (let _150_632 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _150_631 = (let _150_630 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_150_630)::[])
in (_150_632)::_150_631))
in (_150_634)::_150_633))
in (_150_636)::_150_635))
in (let _150_637 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _150_639 _150_638 None _150_637)))))
in (
# 734 "FStar.TypeChecker.Util.fst"
let default_case = (
# 735 "FStar.TypeChecker.Util.fst"
let post_k = (let _150_642 = (let _150_640 = (FStar_Syntax_Syntax.null_binder res_t)
in (_150_640)::[])
in (let _150_641 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _150_642 _150_641)))
in (
# 736 "FStar.TypeChecker.Util.fst"
let kwp = (let _150_645 = (let _150_643 = (FStar_Syntax_Syntax.null_binder post_k)
in (_150_643)::[])
in (let _150_644 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _150_645 _150_644)))
in (
# 737 "FStar.TypeChecker.Util.fst"
let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (
# 738 "FStar.TypeChecker.Util.fst"
let wp = (let _150_652 = (let _150_646 = (FStar_Syntax_Syntax.mk_binder post)
in (_150_646)::[])
in (let _150_651 = (let _150_650 = (let _150_647 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Errors.exhaustiveness_check _150_647))
in (let _150_649 = (let _150_648 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.false_lid _150_648))
in (FStar_All.pipe_left _150_650 _150_649)))
in (FStar_Syntax_Util.abs _150_652 _150_651 None)))
in (
# 739 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_656 = (let _150_653 = (FStar_Syntax_Syntax.mk_binder post)
in (_150_653)::[])
in (let _150_655 = (let _150_654 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid _150_654))
in (FStar_Syntax_Util.abs _150_656 _150_655 None)))
in (
# 740 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (
# 742 "FStar.TypeChecker.Util.fst"
let comp = (FStar_List.fold_right (fun _69_982 celse -> (match (_69_982) with
| (g, cthen) -> begin
(
# 743 "FStar.TypeChecker.Util.fst"
let _69_1000 = (let _150_659 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _150_659 celse))
in (match (_69_1000) with
| ((md, _69_986, _69_988), (_69_991, wp_then, wlp_then), (_69_996, wp_else, wlp_else)) -> begin
(let _150_661 = (ifthenelse md res_t g wp_then wp_else)
in (let _150_660 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _150_661 _150_660 [])))
end))
end)) lcases default_case)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(add_equality_to_post_condition env comp res_t)
end else begin
(
# 747 "FStar.TypeChecker.Util.fst"
let comp = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (
# 748 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env comp.FStar_Syntax_Syntax.effect_name)
in (
# 749 "FStar.TypeChecker.Util.fst"
let _69_1008 = (destruct_comp comp)
in (match (_69_1008) with
| (_69_1005, wp, wlp) -> begin
(
# 750 "FStar.TypeChecker.Util.fst"
let wp = (let _150_668 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _150_667 = (let _150_666 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_665 = (let _150_664 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _150_663 = (let _150_662 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_662)::[])
in (_150_664)::_150_663))
in (_150_666)::_150_665))
in (FStar_Syntax_Syntax.mk_Tm_app _150_668 _150_667 None wp.FStar_Syntax_Syntax.pos)))
in (
# 751 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_673 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _150_672 = (let _150_671 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_670 = (let _150_669 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_669)::[])
in (_150_671)::_150_670))
in (FStar_Syntax_Syntax.mk_Tm_app _150_673 _150_672 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end))))
end))))
end))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))

# 758 "FStar.TypeChecker.Util.fst"
let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (
# 759 "FStar.TypeChecker.Util.fst"
let close = (fun _69_1015 -> (match (()) with
| () -> begin
(
# 760 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in if (FStar_Syntax_Util.is_ml_comp c) then begin
c
end else begin
(
# 763 "FStar.TypeChecker.Util.fst"
let close_wp = (fun u_res md res_t bvs wp0 -> (FStar_List.fold_right (fun x wp -> (
# 765 "FStar.TypeChecker.Util.fst"
let bs = (let _150_694 = (FStar_Syntax_Syntax.mk_binder x)
in (_150_694)::[])
in (
# 766 "FStar.TypeChecker.Util.fst"
let us = (let _150_696 = (let _150_695 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (_150_695)::[])
in (u_res)::_150_696)
in (
# 767 "FStar.TypeChecker.Util.fst"
let wp = (FStar_Syntax_Util.abs bs wp None)
in (let _150_703 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (let _150_702 = (let _150_701 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_700 = (let _150_699 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _150_698 = (let _150_697 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_697)::[])
in (_150_699)::_150_698))
in (_150_701)::_150_700))
in (FStar_Syntax_Syntax.mk_Tm_app _150_703 _150_702 None wp0.FStar_Syntax_Syntax.pos))))))) bvs wp0))
in (
# 770 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 771 "FStar.TypeChecker.Util.fst"
let _69_1032 = (destruct_comp c)
in (match (_69_1032) with
| (t, wp, wlp) -> begin
(
# 772 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 773 "FStar.TypeChecker.Util.fst"
let u_res = (env.FStar_TypeChecker_Env.universe_of env c.FStar_Syntax_Syntax.result_typ)
in (
# 774 "FStar.TypeChecker.Util.fst"
let wp = (close_wp u_res md c.FStar_Syntax_Syntax.result_typ bvs wp)
in (
# 775 "FStar.TypeChecker.Util.fst"
let wlp = (close_wp u_res md c.FStar_Syntax_Syntax.result_typ bvs wlp)
in (mk_comp md c.FStar_Syntax_Syntax.result_typ wp wlp c.FStar_Syntax_Syntax.flags)))))
end))))
end)
end))
in (
# 777 "FStar.TypeChecker.Util.fst"
let _69_1037 = lc
in {FStar_Syntax_Syntax.eff_name = _69_1037.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _69_1037.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _69_1037.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))

# 779 "FStar.TypeChecker.Util.fst"
let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (
# 780 "FStar.TypeChecker.Util.fst"
let refine = (fun _69_1043 -> (match (()) with
| () -> begin
(
# 781 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in if (not ((is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name))) then begin
c
end else begin
if (FStar_Syntax_Util.is_partial_return c) then begin
c
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c) && (not ((FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)))) then begin
(let _150_714 = (let _150_713 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _150_712 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _150_713 _150_712)))
in (FStar_All.failwith _150_714))
end else begin
(
# 789 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 790 "FStar.TypeChecker.Util.fst"
let t = c.FStar_Syntax_Syntax.result_typ
in (
# 791 "FStar.TypeChecker.Util.fst"
let c = (FStar_Syntax_Syntax.mk_Comp c)
in (
# 792 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (
# 793 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 794 "FStar.TypeChecker.Util.fst"
let ret = (let _150_716 = (let _150_715 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _150_715 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_716))
in (
# 795 "FStar.TypeChecker.Util.fst"
let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (
# 796 "FStar.TypeChecker.Util.fst"
let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (
# 798 "FStar.TypeChecker.Util.fst"
let c = (let _150_718 = (let _150_717 = (bind env None (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), eq_ret))
in (_150_717.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _150_718 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
in c)))))))))
end
end
end)
end))
in (
# 801 "FStar.TypeChecker.Util.fst"
let flags = if (((not ((FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)) && (not ((FStar_Syntax_Util.is_lcomp_partial_return lc)))) then begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_Syntax_Syntax.cflags
end else begin
lc.FStar_Syntax_Syntax.cflags
end
in (
# 807 "FStar.TypeChecker.Util.fst"
let _69_1055 = lc
in {FStar_Syntax_Syntax.eff_name = _69_1055.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _69_1055.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))

# 809 "FStar.TypeChecker.Util.fst"
let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (match ((FStar_TypeChecker_Rel.sub_comp env c c')) with
| None -> begin
(let _150_730 = (let _150_729 = (let _150_728 = (FStar_TypeChecker_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _150_727 = (FStar_TypeChecker_Env.get_range env)
in (_150_728, _150_727)))
in FStar_Syntax_Syntax.Error (_150_729))
in (Prims.raise _150_730))
end
| Some (g) -> begin
(e, c', g)
end))

# 815 "FStar.TypeChecker.Util.fst"
let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match ((let _150_739 = (FStar_Syntax_Subst.compress t)
in _150_739.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_69_1069) -> begin
(match ((let _150_740 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _150_740.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _69_1073) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.bool_lid) -> begin
(
# 820 "FStar.TypeChecker.Util.fst"
let _69_1076 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (
# 821 "FStar.TypeChecker.Util.fst"
let b2t = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos)
in (
# 822 "FStar.TypeChecker.Util.fst"
let lc = (let _150_743 = (let _150_742 = (let _150_741 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_741))
in (None, _150_742))
in (bind env (Some (e)) lc _150_743))
in (
# 823 "FStar.TypeChecker.Util.fst"
let e = (let _150_745 = (let _150_744 = (FStar_Syntax_Syntax.as_arg e)
in (_150_744)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _150_745 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (e, lc)))))
end
| _69_1082 -> begin
(e, lc)
end)
end
| _69_1084 -> begin
(e, lc)
end))

# 830 "FStar.TypeChecker.Util.fst"
let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (
# 831 "FStar.TypeChecker.Util.fst"
let gopt = if env.FStar_TypeChecker_Env.use_eq then begin
(let _150_754 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in (_150_754, false))
end else begin
(let _150_755 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in (_150_755, true))
end
in (match (gopt) with
| (None, _69_1092) -> begin
(FStar_TypeChecker_Rel.subtype_fail env lc.FStar_Syntax_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(match ((FStar_TypeChecker_Rel.guard_form g)) with
| FStar_TypeChecker_Common.Trivial -> begin
(
# 839 "FStar.TypeChecker.Util.fst"
let lc = (
# 839 "FStar.TypeChecker.Util.fst"
let _69_1099 = lc
in {FStar_Syntax_Syntax.eff_name = _69_1099.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _69_1099.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _69_1099.FStar_Syntax_Syntax.comp})
in (e, lc, g))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 843 "FStar.TypeChecker.Util.fst"
let g = (
# 843 "FStar.TypeChecker.Util.fst"
let _69_1104 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _69_1104.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _69_1104.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _69_1104.FStar_TypeChecker_Env.implicits})
in (
# 844 "FStar.TypeChecker.Util.fst"
let strengthen = (fun _69_1108 -> (match (()) with
| () -> begin
(
# 846 "FStar.TypeChecker.Util.fst"
let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (match ((let _150_758 = (FStar_Syntax_Subst.compress f)
in _150_758.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_69_1111, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _69_1120); FStar_Syntax_Syntax.tk = _69_1117; FStar_Syntax_Syntax.pos = _69_1115; FStar_Syntax_Syntax.vars = _69_1113}, _69_1125) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) -> begin
(
# 850 "FStar.TypeChecker.Util.fst"
let lc = (
# 850 "FStar.TypeChecker.Util.fst"
let _69_1128 = lc
in {FStar_Syntax_Syntax.eff_name = _69_1128.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _69_1128.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _69_1128.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| _69_1132 -> begin
(
# 854 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 855 "FStar.TypeChecker.Util.fst"
let _69_1134 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_762 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _150_761 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _150_760 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _150_759 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _150_762 _150_761 _150_760 _150_759)))))
end else begin
()
end
in (
# 862 "FStar.TypeChecker.Util.fst"
let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 863 "FStar.TypeChecker.Util.fst"
let _69_1139 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_69_1139) with
| (a, kwp) -> begin
(
# 864 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 865 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env ct.FStar_Syntax_Syntax.effect_name)
in (
# 866 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (
# 867 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 868 "FStar.TypeChecker.Util.fst"
let us = (let _150_763 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_150_763)::[])
in (
# 869 "FStar.TypeChecker.Util.fst"
let wp = (let _150_768 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ret)
in (let _150_767 = (let _150_766 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_765 = (let _150_764 = (FStar_Syntax_Syntax.as_arg xexp)
in (_150_764)::[])
in (_150_766)::_150_765))
in (FStar_Syntax_Syntax.mk_Tm_app _150_768 _150_767 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)))
in (
# 870 "FStar.TypeChecker.Util.fst"
let cret = (let _150_769 = (mk_comp md t wp wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_769))
in (
# 871 "FStar.TypeChecker.Util.fst"
let guard = if apply_guard then begin
(let _150_771 = (let _150_770 = (FStar_Syntax_Syntax.as_arg xexp)
in (_150_770)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _150_771 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end else begin
f
end
in (
# 872 "FStar.TypeChecker.Util.fst"
let _69_1150 = (let _150_779 = (FStar_All.pipe_left (fun _150_776 -> Some (_150_776)) (FStar_TypeChecker_Errors.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _150_778 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _150_777 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _150_779 _150_778 e cret _150_777))))
in (match (_69_1150) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(
# 876 "FStar.TypeChecker.Util.fst"
let x = (
# 876 "FStar.TypeChecker.Util.fst"
let _69_1151 = x
in {FStar_Syntax_Syntax.ppname = _69_1151.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_1151.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (
# 877 "FStar.TypeChecker.Util.fst"
let c = (let _150_781 = (let _150_780 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_780))
in (bind env (Some (e)) _150_781 (Some (x), eq_ret)))
in (
# 878 "FStar.TypeChecker.Util.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 879 "FStar.TypeChecker.Util.fst"
let _69_1156 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_782 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _150_782))
end else begin
()
end
in c))))
end))))))))))
end)))))
end))
end))
in (
# 882 "FStar.TypeChecker.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _69_3 -> (match (_69_3) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _69_1162 -> begin
[]
end))))
in (
# 883 "FStar.TypeChecker.Util.fst"
let lc = (
# 883 "FStar.TypeChecker.Util.fst"
let _69_1164 = lc
in (let _150_784 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _150_784; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (
# 884 "FStar.TypeChecker.Util.fst"
let g = (
# 884 "FStar.TypeChecker.Util.fst"
let _69_1167 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _69_1167.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _69_1167.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _69_1167.FStar_TypeChecker_Env.implicits})
in (e, lc, g))))))
end)
end)))

# 887 "FStar.TypeChecker.Util.fst"
let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (
# 888 "FStar.TypeChecker.Util.fst"
let mk_post_type = (fun res_t ens -> (
# 889 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _150_796 = (let _150_795 = (let _150_794 = (let _150_793 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _150_793))
in (_150_794)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _150_795 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _150_796))))
in (
# 891 "FStar.TypeChecker.Util.fst"
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
| (req, _69_1195)::(ens, _69_1190)::_69_1187 -> begin
(let _150_802 = (let _150_799 = (norm req)
in Some (_150_799))
in (let _150_801 = (let _150_800 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _150_800))
in (_150_802, _150_801)))
end
| _69_1199 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 905 "FStar.TypeChecker.Util.fst"
let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (wp, _69_1210)::(wlp, _69_1205)::_69_1202 -> begin
(
# 908 "FStar.TypeChecker.Util.fst"
let _69_1216 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (_69_1216) with
| (us_r, _69_1215) -> begin
(
# 909 "FStar.TypeChecker.Util.fst"
let _69_1220 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (_69_1220) with
| (us_e, _69_1219) -> begin
(
# 910 "FStar.TypeChecker.Util.fst"
let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (
# 911 "FStar.TypeChecker.Util.fst"
let as_req = (let _150_803 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.as_requires r)
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_803 us_r))
in (
# 912 "FStar.TypeChecker.Util.fst"
let as_ens = (let _150_804 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.as_ensures r)
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_804 us_e))
in (
# 913 "FStar.TypeChecker.Util.fst"
let req = (let _150_807 = (let _150_806 = (let _150_805 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_805)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.imp_tag)))::_150_806)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _150_807 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 914 "FStar.TypeChecker.Util.fst"
let ens = (let _150_810 = (let _150_809 = (let _150_808 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_808)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.imp_tag)))::_150_809)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _150_810 None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _150_814 = (let _150_811 = (norm req)
in Some (_150_811))
in (let _150_813 = (let _150_812 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm _150_812))
in (_150_814, _150_813))))))))
end))
end))
end
| _69_1227 -> begin
(FStar_All.failwith "Impossible")
end))
end
end)
end)))

# 924 "FStar.TypeChecker.Util.fst"
let maybe_instantiate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (
# 925 "FStar.TypeChecker.Util.fst"
let torig = (FStar_Syntax_Subst.compress t)
in if (not (env.FStar_TypeChecker_Env.instantiate_imp)) then begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end else begin
(match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 930 "FStar.TypeChecker.Util.fst"
let _69_1238 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_69_1238) with
| (bs, c) -> begin
(
# 931 "FStar.TypeChecker.Util.fst"
let rec aux = (fun subst _69_4 -> (match (_69_4) with
| (x, Some (FStar_Syntax_Syntax.Implicit (dot)))::rest -> begin
(
# 933 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 934 "FStar.TypeChecker.Util.fst"
let _69_1254 = (new_implicit_var env t)
in (match (_69_1254) with
| (v, _69_1252, g) -> begin
(
# 935 "FStar.TypeChecker.Util.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, v)))::subst
in (
# 936 "FStar.TypeChecker.Util.fst"
let _69_1260 = (aux subst rest)
in (match (_69_1260) with
| (args, bs, subst, g') -> begin
(let _150_825 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((v, Some (FStar_Syntax_Syntax.Implicit (dot))))::args, bs, subst, _150_825))
end)))
end)))
end
| bs -> begin
([], bs, subst, FStar_TypeChecker_Rel.trivial_guard)
end))
in (
# 940 "FStar.TypeChecker.Util.fst"
let _69_1266 = (aux [] bs)
in (match (_69_1266) with
| (args, bs, subst, guard) -> begin
(match ((args, bs)) with
| ([], _69_1269) -> begin
(e, torig, guard)
end
| (_69_1272, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end
| _69_1276 -> begin
(
# 951 "FStar.TypeChecker.Util.fst"
let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _69_1279 -> begin
(FStar_Syntax_Util.arrow bs c)
end)
in (
# 954 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.subst subst t)
in (
# 955 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk_Tm_app e args (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (e, t, guard))))
end)
end)))
end))
end
| _69_1284 -> begin
(e, t, FStar_TypeChecker_Rel.trivial_guard)
end)
end))

# 965 "FStar.TypeChecker.Util.fst"
let gen_univs : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe_uvar Prims.list * (FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  Prims.bool))  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(
# 967 "FStar.TypeChecker.Util.fst"
let s = (let _150_837 = (let _150_836 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _150_836))
in (FStar_All.pipe_right _150_837 FStar_Util.set_elements))
in (
# 968 "FStar.TypeChecker.Util.fst"
let r = (let _150_838 = (FStar_TypeChecker_Env.get_range env)
in Some (_150_838))
in (
# 969 "FStar.TypeChecker.Util.fst"
let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (
# 970 "FStar.TypeChecker.Util.fst"
let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (
# 971 "FStar.TypeChecker.Util.fst"
let _69_1291 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _150_843 = (let _150_840 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _150_840))
in (let _150_842 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _150_841 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _150_843 _150_842 _150_841))))
end else begin
()
end
in (
# 973 "FStar.TypeChecker.Util.fst"
let _69_1293 = (FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))))
in u_name))))))
in u_names)))
end)

# 977 "FStar.TypeChecker.Util.fst"
let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t -> (
# 978 "FStar.TypeChecker.Util.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (
# 979 "FStar.TypeChecker.Util.fst"
let univs = (FStar_Syntax_Free.univs t)
in (
# 980 "FStar.TypeChecker.Util.fst"
let _69_1301 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _150_852 = (let _150_851 = (let _150_850 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _150_850 (FStar_List.map (fun u -> (let _150_849 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _150_849 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _150_851 (FStar_String.concat ", ")))
in (FStar_Util.print1 "univs to gen : %s\n" _150_852))
end else begin
()
end
in (
# 984 "FStar.TypeChecker.Util.fst"
let gen = (gen_univs env univs)
in (
# 985 "FStar.TypeChecker.Util.fst"
let _69_1304 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _150_853 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _150_853))
end else begin
()
end
in (
# 987 "FStar.TypeChecker.Util.fst"
let ts = (FStar_Syntax_Subst.close_univ_vars gen t)
in (gen, ts))))))))

# 990 "FStar.TypeChecker.Util.fst"
let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> if (let _150_859 = (FStar_Util.for_all (fun _69_1312 -> (match (_69_1312) with
| (_69_1310, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _150_859)) then begin
None
end else begin
(
# 994 "FStar.TypeChecker.Util.fst"
let norm = (fun c -> (
# 995 "FStar.TypeChecker.Util.fst"
let _69_1315 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _150_862 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _150_862))
end else begin
()
end
in (
# 997 "FStar.TypeChecker.Util.fst"
let c = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.Eta)::[]) env c)
end else begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env c)
end
in (
# 1000 "FStar.TypeChecker.Util.fst"
let _69_1318 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _150_863 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _150_863))
end else begin
()
end
in c))))
in (
# 1003 "FStar.TypeChecker.Util.fst"
let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (
# 1004 "FStar.TypeChecker.Util.fst"
let gen_uvars = (fun uvs -> (let _150_866 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _150_866 FStar_Util.set_elements)))
in (
# 1005 "FStar.TypeChecker.Util.fst"
let _69_1335 = (let _150_868 = (FStar_All.pipe_right ecs (FStar_List.map (fun _69_1325 -> (match (_69_1325) with
| (e, c) -> begin
(
# 1006 "FStar.TypeChecker.Util.fst"
let t = (FStar_All.pipe_right (FStar_Syntax_Util.comp_result c) FStar_Syntax_Subst.compress)
in (
# 1007 "FStar.TypeChecker.Util.fst"
let c = (norm c)
in (
# 1008 "FStar.TypeChecker.Util.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (
# 1009 "FStar.TypeChecker.Util.fst"
let t = ct.FStar_Syntax_Syntax.result_typ
in (
# 1010 "FStar.TypeChecker.Util.fst"
let univs = (FStar_Syntax_Free.univs t)
in (
# 1011 "FStar.TypeChecker.Util.fst"
let uvt = (FStar_Syntax_Free.uvars t)
in (
# 1012 "FStar.TypeChecker.Util.fst"
let uvs = (gen_uvars uvt)
in (univs, (uvs, e, c)))))))))
end))))
in (FStar_All.pipe_right _150_868 FStar_List.unzip))
in (match (_69_1335) with
| (univs, uvars) -> begin
(
# 1015 "FStar.TypeChecker.Util.fst"
let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (
# 1016 "FStar.TypeChecker.Util.fst"
let gen_univs = (gen_univs env univs)
in (
# 1017 "FStar.TypeChecker.Util.fst"
let _69_1339 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end else begin
()
end
in (
# 1019 "FStar.TypeChecker.Util.fst"
let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _69_1344 -> (match (_69_1344) with
| (uvs, e, c) -> begin
(
# 1020 "FStar.TypeChecker.Util.fst"
let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _69_1347 -> (match (_69_1347) with
| (u, k) -> begin
(match ((FStar_Unionfind.find u)) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(a, Some (FStar_Syntax_Syntax.imp_tag))
end
| FStar_Syntax_Syntax.Fixed (_69_1381) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _69_1384 -> begin
(
# 1026 "FStar.TypeChecker.Util.fst"
let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (
# 1027 "FStar.TypeChecker.Util.fst"
let _69_1388 = (FStar_Syntax_Util.arrow_formals k)
in (match (_69_1388) with
| (bs, kres) -> begin
(
# 1028 "FStar.TypeChecker.Util.fst"
let a = (let _150_874 = (let _150_873 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _150_872 -> Some (_150_872)) _150_873))
in (FStar_Syntax_Syntax.new_bv _150_874 kres))
in (
# 1029 "FStar.TypeChecker.Util.fst"
let t = (let _150_878 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _150_877 = (let _150_876 = (let _150_875 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _150_875))
in Some (_150_876))
in (FStar_Syntax_Util.abs bs _150_878 _150_877)))
in (
# 1030 "FStar.TypeChecker.Util.fst"
let _69_1391 = (FStar_Syntax_Util.set_uvar u t)
in (a, Some (FStar_Syntax_Syntax.imp_tag)))))
end)))
end)
end))))
in (
# 1034 "FStar.TypeChecker.Util.fst"
let _69_1415 = (match (tvars) with
| [] -> begin
(e, c)
end
| _69_1396 -> begin
(
# 1040 "FStar.TypeChecker.Util.fst"
let _69_1399 = (e, c)
in (match (_69_1399) with
| (e0, c0) -> begin
(
# 1041 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.BetaUVars)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::[]) env c)
in (
# 1042 "FStar.TypeChecker.Util.fst"
let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.BetaUVars)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::[]) env e)
in (
# 1044 "FStar.TypeChecker.Util.fst"
let t = (match ((let _150_879 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _150_879.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(
# 1046 "FStar.TypeChecker.Util.fst"
let _69_1408 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (_69_1408) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| _69_1410 -> begin
(FStar_Syntax_Util.arrow tvars c)
end)
in (
# 1051 "FStar.TypeChecker.Util.fst"
let e' = (FStar_Syntax_Util.abs tvars e None)
in (let _150_880 = (FStar_Syntax_Syntax.mk_Total t)
in (e', _150_880))))))
end))
end)
in (match (_69_1415) with
| (e, c) -> begin
(gen_univs, e, c)
end)))
end))))
in Some (ecs)))))
end)))))
end)

# 1056 "FStar.TypeChecker.Util.fst"
let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> (
# 1057 "FStar.TypeChecker.Util.fst"
let _69_1425 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_887 = (let _150_886 = (FStar_List.map (fun _69_1424 -> (match (_69_1424) with
| (lb, _69_1421, _69_1423) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _150_886 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _150_887))
end else begin
()
end
in (match ((let _150_889 = (FStar_All.pipe_right lecs (FStar_List.map (fun _69_1431 -> (match (_69_1431) with
| (_69_1428, e, c) -> begin
(e, c)
end))))
in (gen env _150_889))) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun _69_1436 -> (match (_69_1436) with
| (l, t, c) -> begin
(l, [], t, c)
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _69_1444 _69_1448 -> (match ((_69_1444, _69_1448)) with
| ((l, _69_1441, _69_1443), (us, e, c)) -> begin
(
# 1064 "FStar.TypeChecker.Util.fst"
let _69_1449 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _150_895 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _150_894 = (FStar_Syntax_Print.lbname_to_string l)
in (let _150_893 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.print3 "(%s) Generalized %s to %s\n" _150_895 _150_894 _150_893))))
end else begin
()
end
in (l, us, e, c))
end)) lecs ecs)
end)))

# 1077 "FStar.TypeChecker.Util.fst"
let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (
# 1078 "FStar.TypeChecker.Util.fst"
let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (
# 1079 "FStar.TypeChecker.Util.fst"
let check = (fun env t1 t2 -> if env.FStar_TypeChecker_Env.use_eq then begin
(FStar_TypeChecker_Rel.try_teq env t1 t2)
end else begin
(match ((FStar_TypeChecker_Rel.try_subtype env t1 t2)) with
| None -> begin
None
end
| Some (f) -> begin
(let _150_911 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _150_910 -> Some (_150_910)) _150_911))
end)
end)
in (
# 1085 "FStar.TypeChecker.Util.fst"
let is_var = (fun e -> (match ((let _150_914 = (FStar_Syntax_Subst.compress e)
in _150_914.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (_69_1466) -> begin
true
end
| _69_1469 -> begin
false
end))
in (
# 1088 "FStar.TypeChecker.Util.fst"
let decorate = (fun e t -> (
# 1089 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((
# 1091 "FStar.TypeChecker.Util.fst"
let _69_1476 = x
in {FStar_Syntax_Syntax.ppname = _69_1476.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_1476.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| _69_1479 -> begin
(
# 1092 "FStar.TypeChecker.Util.fst"
let _69_1480 = e
in (let _150_919 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _69_1480.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _150_919; FStar_Syntax_Syntax.pos = _69_1480.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _69_1480.FStar_Syntax_Syntax.vars}))
end)))
in (
# 1093 "FStar.TypeChecker.Util.fst"
let env = (
# 1093 "FStar.TypeChecker.Util.fst"
let _69_1482 = env
in (let _150_920 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _69_1482.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _69_1482.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _69_1482.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _69_1482.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _69_1482.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _69_1482.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _69_1482.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _69_1482.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _69_1482.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _69_1482.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _69_1482.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _69_1482.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _69_1482.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _69_1482.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _69_1482.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _150_920; FStar_TypeChecker_Env.is_iface = _69_1482.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _69_1482.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _69_1482.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _69_1482.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _69_1482.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _69_1482.FStar_TypeChecker_Env.use_bv_sorts}))
in (match ((check env t1 t2)) with
| None -> begin
(let _150_924 = (let _150_923 = (let _150_922 = (FStar_TypeChecker_Errors.expected_expression_of_type env t2 e t1)
in (let _150_921 = (FStar_TypeChecker_Env.get_range env)
in (_150_922, _150_921)))
in FStar_Syntax_Syntax.Error (_150_923))
in (Prims.raise _150_924))
end
| Some (g) -> begin
(
# 1097 "FStar.TypeChecker.Util.fst"
let _69_1488 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _150_925 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _150_925))
end else begin
()
end
in (let _150_926 = (decorate e t2)
in (_150_926, g)))
end)))))))

# 1102 "FStar.TypeChecker.Util.fst"
let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (
# 1103 "FStar.TypeChecker.Util.fst"
let discharge = (fun g -> (
# 1104 "FStar.TypeChecker.Util.fst"
let _69_1495 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (
# 1106 "FStar.TypeChecker.Util.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _150_936 = (discharge g)
in (let _150_935 = (lc.FStar_Syntax_Syntax.comp ())
in (_150_936, _150_935)))
end else begin
(
# 1109 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 1110 "FStar.TypeChecker.Util.fst"
let steps = (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.DeltaComp)::[]
in (
# 1111 "FStar.TypeChecker.Util.fst"
let c = (let _150_937 = (FStar_TypeChecker_Normalize.normalize_comp steps env c)
in (FStar_All.pipe_right _150_937 FStar_Syntax_Util.comp_to_comp_typ))
in (
# 1112 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 1113 "FStar.TypeChecker.Util.fst"
let _69_1506 = (destruct_comp c)
in (match (_69_1506) with
| (t, wp, _69_1505) -> begin
(
# 1114 "FStar.TypeChecker.Util.fst"
let vc = (let _150_945 = (let _150_939 = (let _150_938 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_150_938)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _150_939 env md md.FStar_Syntax_Syntax.trivial))
in (let _150_944 = (let _150_942 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_941 = (let _150_940 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_940)::[])
in (_150_942)::_150_941))
in (let _150_943 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk_Tm_app _150_945 _150_944 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _150_943))))
in (
# 1115 "FStar.TypeChecker.Util.fst"
let _69_1508 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _150_946 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _150_946))
end else begin
()
end
in (
# 1117 "FStar.TypeChecker.Util.fst"
let g = (let _150_947 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _150_947))
in (let _150_949 = (discharge g)
in (let _150_948 = (FStar_Syntax_Syntax.mk_Comp c)
in (_150_949, _150_948))))))
end))))))
end)))

# 1123 "FStar.TypeChecker.Util.fst"
let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (
# 1124 "FStar.TypeChecker.Util.fst"
let short_bin_op = (fun f _69_5 -> (match (_69_5) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (fst, _69_1519)::[] -> begin
(f fst)
end
| _69_1523 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (
# 1129 "FStar.TypeChecker.Util.fst"
let op_and_e = (fun e -> (let _150_970 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _150_970 (fun _150_969 -> FStar_TypeChecker_Common.NonTrivial (_150_969)))))
in (
# 1130 "FStar.TypeChecker.Util.fst"
let op_or_e = (fun e -> (let _150_975 = (let _150_973 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _150_973))
in (FStar_All.pipe_right _150_975 (fun _150_974 -> FStar_TypeChecker_Common.NonTrivial (_150_974)))))
in (
# 1131 "FStar.TypeChecker.Util.fst"
let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _150_978 -> FStar_TypeChecker_Common.NonTrivial (_150_978))))
in (
# 1132 "FStar.TypeChecker.Util.fst"
let op_or_t = (fun t -> (let _150_982 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _150_982 (fun _150_981 -> FStar_TypeChecker_Common.NonTrivial (_150_981)))))
in (
# 1133 "FStar.TypeChecker.Util.fst"
let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _150_985 -> FStar_TypeChecker_Common.NonTrivial (_150_985))))
in (
# 1135 "FStar.TypeChecker.Util.fst"
let short_op_ite = (fun _69_6 -> (match (_69_6) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (guard, _69_1538)::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| _then::(guard, _69_1543)::[] -> begin
(let _150_989 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _150_989 (fun _150_988 -> FStar_TypeChecker_Common.NonTrivial (_150_988))))
end
| _69_1548 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (
# 1140 "FStar.TypeChecker.Util.fst"
let table = ((FStar_Syntax_Const.op_And, (short_bin_op op_and_e)))::((FStar_Syntax_Const.op_Or, (short_bin_op op_or_e)))::((FStar_Syntax_Const.and_lid, (short_bin_op op_and_t)))::((FStar_Syntax_Const.or_lid, (short_bin_op op_or_t)))::((FStar_Syntax_Const.imp_lid, (short_bin_op op_imp_t)))::((FStar_Syntax_Const.ite_lid, short_op_ite))::[]
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _69_1553) -> begin
(
# 1150 "FStar.TypeChecker.Util.fst"
let lid = fv.FStar_Syntax_Syntax.v
in (match ((FStar_Util.find_map table (fun _69_1559 -> (match (_69_1559) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _150_1022 = (mk seen_args)
in Some (_150_1022))
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
| _69_1564 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))

# 1157 "FStar.TypeChecker.Util.fst"
let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (match ((let _150_1025 = (FStar_Syntax_Subst.compress l)
in _150_1025.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (v, _69_1568) -> begin
(FStar_Util.for_some (FStar_Ident.lid_equals v.FStar_Syntax_Syntax.v) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| _69_1572 -> begin
false
end))

# 1178 "FStar.TypeChecker.Util.fst"
let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (
# 1179 "FStar.TypeChecker.Util.fst"
let pos = (fun bs -> (match (bs) with
| (hd, _69_1581)::_69_1578 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| _69_1585 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| (_69_1589, Some (FStar_Syntax_Syntax.Implicit (_69_1591)))::_69_1587 -> begin
bs
end
| _69_1597 -> begin
(match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
bs
end
| Some (t) -> begin
(match ((let _150_1032 = (FStar_Syntax_Subst.compress t)
in _150_1032.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', _69_1603) -> begin
(match ((FStar_Util.prefix_until (fun _69_7 -> (match (_69_7) with
| (_69_1608, Some (FStar_Syntax_Syntax.Implicit (_69_1610))) -> begin
false
end
| _69_1615 -> begin
true
end)) bs')) with
| None -> begin
bs
end
| Some ([], _69_1619, _69_1621) -> begin
bs
end
| Some (imps, _69_1626, _69_1628) -> begin
if (FStar_All.pipe_right imps (FStar_Util.for_all (fun _69_1634 -> (match (_69_1634) with
| (x, _69_1633) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end)))) then begin
(
# 1195 "FStar.TypeChecker.Util.fst"
let r = (pos bs)
in (
# 1196 "FStar.TypeChecker.Util.fst"
let imps = (FStar_All.pipe_right imps (FStar_List.map (fun _69_1638 -> (match (_69_1638) with
| (x, i) -> begin
(let _150_1036 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in (_150_1036, i))
end))))
in (FStar_List.append imps bs)))
end else begin
bs
end
end)
end
| _69_1641 -> begin
bs
end)
end)
end)))




