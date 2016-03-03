
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
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 144 "FStar.TypeChecker.Util.fst"
let _69_93 = if (univ_vars <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (
# 145 "FStar.TypeChecker.Util.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 146 "FStar.TypeChecker.Util.fst"
let mk_binder = (fun scope a -> (match (a.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 148 "FStar.TypeChecker.Util.fst"
let _69_103 = (FStar_Syntax_Util.type_u ())
in (match (_69_103) with
| (k, _69_102) -> begin
(
# 149 "FStar.TypeChecker.Util.fst"
let t = (let _150_60 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right _150_60 Prims.fst))
in ((
# 150 "FStar.TypeChecker.Util.fst"
let _69_105 = a
in {FStar_Syntax_Syntax.ppname = _69_105.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_105.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), false))
end))
end
| _69_108 -> begin
(a, true)
end))
in (
# 153 "FStar.TypeChecker.Util.fst"
let rec aux = (fun vars e -> (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, _69_114) -> begin
(aux vars e)
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _69_120) -> begin
(t, true)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _69_126) -> begin
(
# 159 "FStar.TypeChecker.Util.fst"
let _69_145 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _69_132 _69_135 -> (match ((_69_132, _69_135)) with
| ((scope, bs, check), (a, imp)) -> begin
(
# 160 "FStar.TypeChecker.Util.fst"
let _69_138 = (mk_binder scope a)
in (match (_69_138) with
| (tb, c) -> begin
(
# 161 "FStar.TypeChecker.Util.fst"
let b = (tb, imp)
in (
# 162 "FStar.TypeChecker.Util.fst"
let bs = (FStar_List.append bs ((b)::[]))
in (
# 163 "FStar.TypeChecker.Util.fst"
let scope = (FStar_List.append scope ((b)::[]))
in (scope, bs, (c || check)))))
end))
end)) (vars, [], false)))
in (match (_69_145) with
| (scope, bs, check) -> begin
(
# 167 "FStar.TypeChecker.Util.fst"
let _69_148 = (aux scope body)
in (match (_69_148) with
| (res, check_res) -> begin
(
# 168 "FStar.TypeChecker.Util.fst"
let c = (FStar_Syntax_Util.ml_comp res r)
in (
# 169 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Util.arrow bs c)
in (
# 170 "FStar.TypeChecker.Util.fst"
let _69_151 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
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
| _69_154 -> begin
(let _150_70 = (let _150_69 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _150_69 Prims.fst))
in (_150_70, false))
end))
in (
# 175 "FStar.TypeChecker.Util.fst"
let _69_157 = (let _150_71 = (t_binders env)
in (aux _150_71 e))
in (match (_69_157) with
| (t, b) -> begin
([], t, b)
end))))))
end
| _69_159 -> begin
(
# 179 "FStar.TypeChecker.Util.fst"
let _69_162 = (FStar_Syntax_Subst.open_univ_vars univ_vars t)
in (match (_69_162) with
| (univ_vars, t) -> begin
(univ_vars, t, false)
end))
end)
end))

# 190 "FStar.TypeChecker.Util.fst"
let pat_as_exps : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term Prims.list * FStar_Syntax_Syntax.pat) = (fun allow_implicits env p -> (
# 195 "FStar.TypeChecker.Util.fst"
let rec pat_as_arg_with_env = (fun allow_wc_dependence env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(
# 204 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) None p.FStar_Syntax_Syntax.p)
in ([], [], [], env, e, p))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _69_175) -> begin
(
# 208 "FStar.TypeChecker.Util.fst"
let _69_181 = (FStar_Syntax_Util.type_u ())
in (match (_69_181) with
| (k, _69_180) -> begin
(
# 209 "FStar.TypeChecker.Util.fst"
let t = (new_uvar env k)
in (
# 210 "FStar.TypeChecker.Util.fst"
let x = (
# 210 "FStar.TypeChecker.Util.fst"
let _69_183 = x
in {FStar_Syntax_Syntax.ppname = _69_183.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_183.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (
# 211 "FStar.TypeChecker.Util.fst"
let _69_188 = (let _150_84 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _150_84 t))
in (match (_69_188) with
| (e, u) -> begin
(
# 212 "FStar.TypeChecker.Util.fst"
let p = (
# 212 "FStar.TypeChecker.Util.fst"
let _69_189 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, e)); FStar_Syntax_Syntax.ty = _69_189.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _69_189.FStar_Syntax_Syntax.p})
in ([], [], [], env, e, p))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 216 "FStar.TypeChecker.Util.fst"
let _69_197 = (FStar_Syntax_Util.type_u ())
in (match (_69_197) with
| (t, _69_196) -> begin
(
# 217 "FStar.TypeChecker.Util.fst"
let x = (
# 217 "FStar.TypeChecker.Util.fst"
let _69_198 = x
in (let _150_85 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _69_198.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_198.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_85}))
in (
# 218 "FStar.TypeChecker.Util.fst"
let env = if allow_wc_dependence then begin
(FStar_TypeChecker_Env.push_bv env x)
end else begin
env
end
in (
# 219 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in ((x)::[], [], (x)::[], env, e, p))))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 223 "FStar.TypeChecker.Util.fst"
let _69_208 = (FStar_Syntax_Util.type_u ())
in (match (_69_208) with
| (t, _69_207) -> begin
(
# 224 "FStar.TypeChecker.Util.fst"
let x = (
# 224 "FStar.TypeChecker.Util.fst"
let _69_209 = x
in (let _150_86 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _69_209.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_209.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_86}))
in (
# 225 "FStar.TypeChecker.Util.fst"
let env = (FStar_TypeChecker_Env.push_bv env x)
in (
# 226 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in ((x)::[], (x)::[], [], env, e, p))))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 230 "FStar.TypeChecker.Util.fst"
let _69_242 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _69_224 _69_227 -> (match ((_69_224, _69_227)) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(
# 231 "FStar.TypeChecker.Util.fst"
let _69_234 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_69_234) with
| (b', a', w', env, te, pat) -> begin
(
# 232 "FStar.TypeChecker.Util.fst"
let arg = if imp then begin
(FStar_Syntax_Syntax.iarg te)
end else begin
(FStar_Syntax_Syntax.as_arg te)
end
in ((b')::b, (a')::a, (w')::w, env, (arg)::args, ((pat, imp))::pats))
end))
end)) ([], [], [], env, [], [])))
in (match (_69_242) with
| (b, a, w, env, args, pats) -> begin
(
# 235 "FStar.TypeChecker.Util.fst"
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
# 241 "FStar.TypeChecker.Util.fst"
let _69_244 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _69_244.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _69_244.FStar_Syntax_Syntax.p}))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (_69_247) -> begin
(FStar_All.failwith "impossible")
end))
in (
# 245 "FStar.TypeChecker.Util.fst"
let rec elaborate_pat = (fun env p -> (
# 246 "FStar.TypeChecker.Util.fst"
let maybe_dot = (fun inaccessible a r -> if (allow_implicits && inaccessible) then begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term ((a, FStar_Syntax_Syntax.tun))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end else begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var (a)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end)
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 252 "FStar.TypeChecker.Util.fst"
let pats = (FStar_List.map (fun _69_262 -> (match (_69_262) with
| (p, imp) -> begin
(let _150_108 = (elaborate_pat env p)
in (_150_108, imp))
end)) pats)
in (
# 253 "FStar.TypeChecker.Util.fst"
let _69_267 = (FStar_TypeChecker_Env.lookup_datacon env (Prims.fst fv).FStar_Syntax_Syntax.v)
in (match (_69_267) with
| (_69_265, t) -> begin
(
# 254 "FStar.TypeChecker.Util.fst"
let _69_271 = (FStar_Syntax_Util.arrow_formals t)
in (match (_69_271) with
| (f, _69_270) -> begin
(
# 255 "FStar.TypeChecker.Util.fst"
let rec aux = (fun formals pats -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _69_282::_69_280) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v)))))
end
| (_69_288::_69_286, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun _69_294 -> (match (_69_294) with
| (t, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(
# 261 "FStar.TypeChecker.Util.fst"
let a = (let _150_115 = (let _150_114 = (FStar_Syntax_Syntax.range_of_bv t)
in Some (_150_114))
in (FStar_Syntax_Syntax.new_bv _150_115 FStar_Syntax_Syntax.tun))
in (
# 262 "FStar.TypeChecker.Util.fst"
let r = (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v)
in (let _150_116 = (maybe_dot inaccessible a r)
in (_150_116, true))))
end
| _69_301 -> begin
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
| (_69_312, Some (FStar_Syntax_Syntax.Implicit (_69_314))) when p_imp -> begin
(let _150_121 = (aux formals' pats')
in ((p, true))::_150_121)
end
| (_69_319, Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(
# 274 "FStar.TypeChecker.Util.fst"
let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (
# 275 "FStar.TypeChecker.Util.fst"
let p = (maybe_dot inaccessible a (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v))
in (let _150_122 = (aux formals' pats)
in ((p, true))::_150_122)))
end
| (_69_327, imp) -> begin
(let _150_125 = (let _150_123 = (FStar_Syntax_Syntax.is_implicit imp)
in (p, _150_123))
in (let _150_124 = (aux formals' pats')
in (_150_125)::_150_124))
end)
end))
in (
# 281 "FStar.TypeChecker.Util.fst"
let _69_330 = p
in (let _150_128 = (let _150_127 = (let _150_126 = (aux f pats)
in (fv, _150_126))
in FStar_Syntax_Syntax.Pat_cons (_150_127))
in {FStar_Syntax_Syntax.v = _150_128; FStar_Syntax_Syntax.ty = _69_330.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _69_330.FStar_Syntax_Syntax.p})))
end))
end)))
end
| _69_333 -> begin
p
end)))
in (
# 285 "FStar.TypeChecker.Util.fst"
let one_pat = (fun allow_wc_dependence env p -> (
# 286 "FStar.TypeChecker.Util.fst"
let p = (elaborate_pat env p)
in (
# 287 "FStar.TypeChecker.Util.fst"
let _69_345 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_69_345) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))) with
| Some (x) -> begin
(let _150_137 = (let _150_136 = (let _150_135 = (FStar_TypeChecker_Errors.nonlinear_pattern_variable x)
in (_150_135, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_150_136))
in (Prims.raise _150_137))
end
| _69_349 -> begin
(b, a, w, arg, p)
end)
end))))
in (
# 292 "FStar.TypeChecker.Util.fst"
let top_level_pat_as_args = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_disj (q::pats) -> begin
(
# 299 "FStar.TypeChecker.Util.fst"
let _69_365 = (one_pat false env q)
in (match (_69_365) with
| (b, a, _69_362, te, q) -> begin
(
# 300 "FStar.TypeChecker.Util.fst"
let _69_380 = (FStar_List.fold_right (fun p _69_370 -> (match (_69_370) with
| (w, args, pats) -> begin
(
# 301 "FStar.TypeChecker.Util.fst"
let _69_376 = (one_pat false env p)
in (match (_69_376) with
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
in (match (_69_380) with
| (w, args, pats) -> begin
(let _150_151 = (let _150_150 = (FStar_Syntax_Syntax.as_arg te)
in (_150_150)::args)
in ((FStar_List.append b w), _150_151, (
# 306 "FStar.TypeChecker.Util.fst"
let _69_381 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((q)::pats); FStar_Syntax_Syntax.ty = _69_381.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _69_381.FStar_Syntax_Syntax.p})))
end))
end))
end
| _69_384 -> begin
(
# 309 "FStar.TypeChecker.Util.fst"
let _69_392 = (one_pat true env p)
in (match (_69_392) with
| (b, _69_387, _69_389, arg, p) -> begin
(let _150_153 = (let _150_152 = (FStar_Syntax_Syntax.as_arg arg)
in (_150_152)::[])
in (b, _150_153, p))
end))
end))
in (
# 312 "FStar.TypeChecker.Util.fst"
let _69_396 = (top_level_pat_as_args env p)
in (match (_69_396) with
| (b, args, p) -> begin
(
# 313 "FStar.TypeChecker.Util.fst"
let exps = (FStar_All.pipe_right args (FStar_List.map Prims.fst))
in (b, exps, p))
end)))))))

# 316 "FStar.TypeChecker.Util.fst"
let decorate_pattern : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.pat = (fun env p exps -> (
# 317 "FStar.TypeChecker.Util.fst"
let qq = p
in (
# 318 "FStar.TypeChecker.Util.fst"
let rec aux = (fun p e -> (
# 319 "FStar.TypeChecker.Util.fst"
let pkg = (fun q t -> (FStar_Syntax_Syntax.withinfo q t p.FStar_Syntax_Syntax.p))
in (
# 320 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Util.unmeta e)
in (match ((p.FStar_Syntax_Syntax.v, e.FStar_Syntax_Syntax.n)) with
| (_69_410, FStar_Syntax_Syntax.Tm_uinst (e, _69_413)) -> begin
(aux p e)
end
| (FStar_Syntax_Syntax.Pat_constant (_69_418), FStar_Syntax_Syntax.Tm_constant (_69_421)) -> begin
(let _150_168 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v _150_168))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(
# 328 "FStar.TypeChecker.Util.fst"
let _69_429 = if (not ((FStar_Syntax_Syntax.bv_eq x y))) then begin
(let _150_171 = (let _150_170 = (FStar_Syntax_Print.bv_to_string x)
in (let _150_169 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _150_170 _150_169)))
in (FStar_All.failwith _150_171))
end else begin
()
end
in (
# 330 "FStar.TypeChecker.Util.fst"
let _69_431 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _150_173 = (FStar_Syntax_Print.bv_to_string x)
in (let _150_172 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _150_173 _150_172)))
end else begin
()
end
in (
# 332 "FStar.TypeChecker.Util.fst"
let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (
# 333 "FStar.TypeChecker.Util.fst"
let x = (
# 333 "FStar.TypeChecker.Util.fst"
let _69_434 = x
in {FStar_Syntax_Syntax.ppname = _69_434.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_434.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x)) s.FStar_Syntax_Syntax.n)))))
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(
# 337 "FStar.TypeChecker.Util.fst"
let _69_442 = if (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation) then begin
(let _150_176 = (let _150_175 = (FStar_Syntax_Print.bv_to_string x)
in (let _150_174 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _150_175 _150_174)))
in (FStar_All.failwith _150_176))
end else begin
()
end
in (
# 339 "FStar.TypeChecker.Util.fst"
let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (
# 340 "FStar.TypeChecker.Util.fst"
let x = (
# 340 "FStar.TypeChecker.Util.fst"
let _69_445 = x
in {FStar_Syntax_Syntax.ppname = _69_445.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_445.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x)) s.FStar_Syntax_Syntax.n))))
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _69_450), _69_454) -> begin
(
# 344 "FStar.TypeChecker.Util.fst"
let s = (force_sort e)
in (
# 345 "FStar.TypeChecker.Util.fst"
let x = (
# 345 "FStar.TypeChecker.Util.fst"
let _69_457 = x
in {FStar_Syntax_Syntax.ppname = _69_457.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_457.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
(
# 349 "FStar.TypeChecker.Util.fst"
let _69_467 = if (not ((FStar_Syntax_Syntax.fv_eq fv fv'))) then begin
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
# 356 "FStar.TypeChecker.Util.fst"
let _69_510 = if (let _150_179 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right _150_179 Prims.op_Negation)) then begin
(let _150_180 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" (Prims.fst fv).FStar_Syntax_Syntax.v.FStar_Ident.str (Prims.fst fv').FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _150_180))
end else begin
()
end
in (
# 359 "FStar.TypeChecker.Util.fst"
let fv = fv'
in (
# 360 "FStar.TypeChecker.Util.fst"
let rec match_args = (fun matched_pats args argpats -> (match ((args, argpats)) with
| ([], []) -> begin
(let _150_187 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev matched_pats)))) _150_187))
end
| (arg::args, (argpat, _69_526)::argpats) -> begin
(match ((arg, argpat.FStar_Syntax_Syntax.v)) with
| ((e, Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (_69_536)) -> begin
(
# 365 "FStar.TypeChecker.Util.fst"
let x = (let _150_188 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _150_188))
in (
# 366 "FStar.TypeChecker.Util.fst"
let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((e, imp), _69_545) -> begin
(
# 370 "FStar.TypeChecker.Util.fst"
let pat = (let _150_190 = (aux argpat e)
in (let _150_189 = (FStar_Syntax_Syntax.is_implicit imp)
in (_150_190, _150_189)))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _69_549 -> begin
(let _150_193 = (let _150_192 = (FStar_Syntax_Print.pat_to_string p)
in (let _150_191 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _150_192 _150_191)))
in (FStar_All.failwith _150_193))
end))
in (match_args [] args argpats))))
end
| _69_551 -> begin
(let _150_198 = (let _150_197 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (let _150_196 = (FStar_Syntax_Print.pat_to_string qq)
in (let _150_195 = (let _150_194 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right _150_194 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _150_197 _150_196 _150_195))))
in (FStar_All.failwith _150_198))
end))))
in (match ((p.FStar_Syntax_Syntax.v, exps)) with
| (FStar_Syntax_Syntax.Pat_disj (ps), _69_555) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(
# 383 "FStar.TypeChecker.Util.fst"
let ps = (FStar_List.map2 aux ps exps)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj (ps)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p))
end
| (_69_559, e::[]) -> begin
(aux p e)
end
| _69_564 -> begin
(FStar_All.failwith "Unexpected number of patterns")
end))))

# 391 "FStar.TypeChecker.Util.fst"
let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (
# 392 "FStar.TypeChecker.Util.fst"
let topt = Some (pat.FStar_Syntax_Syntax.ty)
in (
# 393 "FStar.TypeChecker.Util.fst"
let mk = (fun f -> (FStar_Syntax_Syntax.mk f topt pat.FStar_Syntax_Syntax.p))
in (
# 395 "FStar.TypeChecker.Util.fst"
let pat_as_arg = (fun _69_572 -> (match (_69_572) with
| (p, i) -> begin
(
# 396 "FStar.TypeChecker.Util.fst"
let _69_575 = (decorated_pattern_as_term p)
in (match (_69_575) with
| (vars, te) -> begin
(let _150_206 = (let _150_205 = (FStar_Syntax_Syntax.as_implicit i)
in (te, _150_205))
in (vars, _150_206))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_69_577) -> begin
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
# 410 "FStar.TypeChecker.Util.fst"
let _69_590 = (let _150_209 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _150_209 FStar_List.unzip))
in (match (_69_590) with
| (vars, args) -> begin
(
# 411 "FStar.TypeChecker.Util.fst"
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

# 421 "FStar.TypeChecker.Util.fst"
let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (
# 422 "FStar.TypeChecker.Util.fst"
let _69_614 = (match (c.FStar_Syntax_Syntax.effect_args) with
| (wp, _69_603)::(wlp, _69_599)::[] -> begin
(wp, wlp)
end
| _69_607 -> begin
(let _150_219 = (let _150_218 = (let _150_217 = (FStar_List.map (fun _69_611 -> (match (_69_611) with
| (x, _69_610) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right _150_217 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str _150_218))
in (FStar_All.failwith _150_219))
end)
in (match (_69_614) with
| (wp, wlp) -> begin
(c.FStar_Syntax_Syntax.result_typ, wp, wlp)
end)))

# 428 "FStar.TypeChecker.Util.fst"
let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (
# 429 "FStar.TypeChecker.Util.fst"
let _69_622 = (destruct_comp c)
in (match (_69_622) with
| (_69_619, wp, wlp) -> begin
(let _150_241 = (let _150_240 = (let _150_236 = (lift c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _150_236))
in (let _150_239 = (let _150_238 = (let _150_237 = (lift c.FStar_Syntax_Syntax.result_typ wlp)
in (FStar_Syntax_Syntax.as_arg _150_237))
in (_150_238)::[])
in (_150_240)::_150_239))
in {FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _150_241; FStar_Syntax_Syntax.flags = []})
end)))

# 435 "FStar.TypeChecker.Util.fst"
let norm_eff_name : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (
# 436 "FStar.TypeChecker.Util.fst"
let cache = (FStar_Util.smap_create 20)
in (fun env l -> (
# 438 "FStar.TypeChecker.Util.fst"
let rec find = (fun l -> (match ((FStar_TypeChecker_Env.lookup_effect_abbrev env FStar_Syntax_Syntax.U_unknown l)) with
| None -> begin
None
end
| Some (_69_630, c) -> begin
(
# 442 "FStar.TypeChecker.Util.fst"
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
# 446 "FStar.TypeChecker.Util.fst"
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
# 451 "FStar.TypeChecker.Util.fst"
let _69_644 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))

# 457 "FStar.TypeChecker.Util.fst"
let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (
# 458 "FStar.TypeChecker.Util.fst"
let _69_655 = (let _150_255 = (norm_eff_name env l1)
in (let _150_254 = (norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _150_255 _150_254)))
in (match (_69_655) with
| (m, _69_652, _69_654) -> begin
m
end)))

# 461 "FStar.TypeChecker.Util.fst"
let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> if ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2)) then begin
FStar_Syntax_Const.effect_Tot_lid
end else begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)

# 467 "FStar.TypeChecker.Util.fst"
let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)) = (fun env c1 c2 -> (
# 468 "FStar.TypeChecker.Util.fst"
let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (
# 469 "FStar.TypeChecker.Util.fst"
let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (
# 470 "FStar.TypeChecker.Util.fst"
let _69_667 = (FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (_69_667) with
| (m, lift1, lift2) -> begin
(
# 471 "FStar.TypeChecker.Util.fst"
let m1 = (lift_comp c1 m lift1)
in (
# 472 "FStar.TypeChecker.Util.fst"
let m2 = (lift_comp c2 m lift2)
in (
# 473 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (
# 474 "FStar.TypeChecker.Util.fst"
let _69_673 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (_69_673) with
| (a, kwp) -> begin
(let _150_269 = (destruct_comp m1)
in (let _150_268 = (destruct_comp m2)
in ((md, a, kwp), _150_269, _150_268)))
end)))))
end)))))

# 477 "FStar.TypeChecker.Util.fst"
let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (
# 478 "FStar.TypeChecker.Util.fst"
let l = (norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)))

# 481 "FStar.TypeChecker.Util.fst"
let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (
# 482 "FStar.TypeChecker.Util.fst"
let l = (norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid))))

# 486 "FStar.TypeChecker.Util.fst"
let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md result wp wlp flags -> (let _150_292 = (let _150_291 = (let _150_290 = (FStar_Syntax_Syntax.as_arg wp)
in (let _150_289 = (let _150_288 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_288)::[])
in (_150_290)::_150_289))
in {FStar_Syntax_Syntax.effect_name = md.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = _150_291; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp _150_292)))

# 492 "FStar.TypeChecker.Util.fst"
let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (
# 493 "FStar.TypeChecker.Util.fst"
let _69_687 = lc
in (let _150_299 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _69_687.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _150_299; FStar_Syntax_Syntax.cflags = _69_687.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _69_689 -> (match (()) with
| () -> begin
(let _150_298 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _150_298))
end))})))

# 496 "FStar.TypeChecker.Util.fst"
let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _150_302 = (FStar_Syntax_Subst.compress t)
in _150_302.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_69_692) -> begin
true
end
| _69_695 -> begin
false
end))

# 500 "FStar.TypeChecker.Util.fst"
let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v -> (
# 502 "FStar.TypeChecker.Util.fst"
let c = if (let _150_309 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation _150_309)) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(
# 505 "FStar.TypeChecker.Util.fst"
let m = (let _150_310 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must _150_310))
in (
# 506 "FStar.TypeChecker.Util.fst"
let _69_702 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_69_702) with
| (a, kwp) -> begin
(
# 507 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 508 "FStar.TypeChecker.Util.fst"
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
# 509 "FStar.TypeChecker.Util.fst"
let wlp = wp
in (mk_comp m t wp wlp ((FStar_Syntax_Syntax.RETURN)::[])))))
end)))
end
in (
# 511 "FStar.TypeChecker.Util.fst"
let _69_707 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return"))) then begin
(let _150_321 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _150_320 = (FStar_Syntax_Print.term_to_string v)
in (let _150_319 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _150_321 _150_320 _150_319))))
end else begin
()
end
in c)))

# 516 "FStar.TypeChecker.Util.fst"
let bind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun env e1opt lc1 _69_714 -> (match (_69_714) with
| (b, lc2) -> begin
(
# 517 "FStar.TypeChecker.Util.fst"
let _69_722 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(
# 519 "FStar.TypeChecker.Util.fst"
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
# 525 "FStar.TypeChecker.Util.fst"
let bind_it = (fun _69_725 -> (match (()) with
| () -> begin
(
# 526 "FStar.TypeChecker.Util.fst"
let c1 = (lc1.FStar_Syntax_Syntax.comp ())
in (
# 527 "FStar.TypeChecker.Util.fst"
let c2 = (lc2.FStar_Syntax_Syntax.comp ())
in (
# 528 "FStar.TypeChecker.Util.fst"
let _69_731 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
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
# 537 "FStar.TypeChecker.Util.fst"
let try_simplify = (fun _69_734 -> (match (()) with
| () -> begin
(
# 538 "FStar.TypeChecker.Util.fst"
let aux = (fun _69_736 -> (match (()) with
| () -> begin
if (FStar_Syntax_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some ((c2, "trivial no binder"))
end
| Some (_69_739) -> begin
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
| _69_747 -> begin
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
# 565 "FStar.TypeChecker.Util.fst"
let _69_765 = (lift_and_destruct env c1 c2)
in (match (_69_765) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(
# 566 "FStar.TypeChecker.Util.fst"
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
# 569 "FStar.TypeChecker.Util.fst"
let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp None))
in (
# 570 "FStar.TypeChecker.Util.fst"
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
# 571 "FStar.TypeChecker.Util.fst"
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
# 572 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t2)))::[]) kwp)
in (
# 573 "FStar.TypeChecker.Util.fst"
let us = (let _150_375 = (env.FStar_TypeChecker_Env.universe_of env t1)
in (let _150_374 = (let _150_373 = (env.FStar_TypeChecker_Env.universe_of env t2)
in (_150_373)::[])
in (_150_375)::_150_374))
in (
# 574 "FStar.TypeChecker.Util.fst"
let wp = (let _150_376 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _150_376 wp_args None t2.FStar_Syntax_Syntax.pos))
in (
# 575 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_377 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wlp)
in (FStar_Syntax_Syntax.mk_Tm_app _150_377 wlp_args None t2.FStar_Syntax_Syntax.pos))
in (
# 576 "FStar.TypeChecker.Util.fst"
let c = (mk_comp md t2 wp wlp [])
in c)))))))))
end))
end)))))
end))
in (let _150_378 = (join_lcomp env lc1 lc2)
in {FStar_Syntax_Syntax.eff_name = _150_378; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it})))
end))

# 583 "FStar.TypeChecker.Util.fst"
let lift_formula : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t mk_wp mk_wlp f -> (
# 584 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 585 "FStar.TypeChecker.Util.fst"
let _69_787 = (FStar_TypeChecker_Env.wp_signature env md_pure.FStar_Syntax_Syntax.mname)
in (match (_69_787) with
| (a, kwp) -> begin
(
# 586 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 587 "FStar.TypeChecker.Util.fst"
let wp = (let _150_392 = (let _150_391 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_390 = (let _150_389 = (FStar_Syntax_Syntax.as_arg f)
in (_150_389)::[])
in (_150_391)::_150_390))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wp _150_392 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (
# 588 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_396 = (let _150_395 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_394 = (let _150_393 = (FStar_Syntax_Syntax.as_arg f)
in (_150_393)::[])
in (_150_395)::_150_394))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wlp _150_396 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (mk_comp md_pure FStar_TypeChecker_Common.t_unit wp wlp []))))
end))))

# 591 "FStar.TypeChecker.Util.fst"
let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((f, FStar_Syntax_Syntax.Meta_labeled ((reason, r, false))))) None f.FStar_Syntax_Syntax.pos))

# 594 "FStar.TypeChecker.Util.fst"
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

# 601 "FStar.TypeChecker.Util.fst"
let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 603 "FStar.TypeChecker.Util.fst"
let _69_807 = g
in (let _150_429 = (let _150_428 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_150_428))
in {FStar_TypeChecker_Env.guard_f = _150_429; FStar_TypeChecker_Env.deferred = _69_807.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _69_807.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _69_807.FStar_TypeChecker_Env.implicits}))
end))

# 605 "FStar.TypeChecker.Util.fst"
let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(
# 607 "FStar.TypeChecker.Util.fst"
let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| _69_818 -> begin
g2
end))

# 611 "FStar.TypeChecker.Util.fst"
let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (
# 612 "FStar.TypeChecker.Util.fst"
let weaken = (fun _69_823 -> (match (()) with
| () -> begin
(
# 613 "FStar.TypeChecker.Util.fst"
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
# 619 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 620 "FStar.TypeChecker.Util.fst"
let _69_832 = (destruct_comp c)
in (match (_69_832) with
| (res_t, wp, wlp) -> begin
(
# 621 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 622 "FStar.TypeChecker.Util.fst"
let us = (let _150_442 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_442)::[])
in (
# 623 "FStar.TypeChecker.Util.fst"
let wp = (let _150_449 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _150_448 = (let _150_447 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_446 = (let _150_445 = (FStar_Syntax_Syntax.as_arg f)
in (let _150_444 = (let _150_443 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_443)::[])
in (_150_445)::_150_444))
in (_150_447)::_150_446))
in (FStar_Syntax_Syntax.mk_Tm_app _150_449 _150_448 None wp.FStar_Syntax_Syntax.pos)))
in (
# 624 "FStar.TypeChecker.Util.fst"
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
# 626 "FStar.TypeChecker.Util.fst"
let _69_837 = lc
in {FStar_Syntax_Syntax.eff_name = _69_837.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _69_837.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _69_837.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))

# 628 "FStar.TypeChecker.Util.fst"
let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> if (FStar_TypeChecker_Rel.is_trivial g0) then begin
(lc, g0)
end else begin
(
# 632 "FStar.TypeChecker.Util.fst"
let _69_844 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_476 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _150_475 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _150_476 _150_475)))
end else begin
()
end
in (
# 636 "FStar.TypeChecker.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _69_2 -> (match (_69_2) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _69_850 -> begin
[]
end))))
in (
# 637 "FStar.TypeChecker.Util.fst"
let strengthen = (fun _69_853 -> (match (()) with
| () -> begin
(
# 638 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 639 "FStar.TypeChecker.Util.fst"
let g0 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (match ((FStar_TypeChecker_Rel.guard_form g0)) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 643 "FStar.TypeChecker.Util.fst"
let c = if ((FStar_Syntax_Util.is_pure_or_ghost_comp c) && (not ((FStar_Syntax_Util.is_partial_return c)))) then begin
(
# 646 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.gen_bv "strengthen_pre_x" None (FStar_Syntax_Util.comp_result c))
in (
# 647 "FStar.TypeChecker.Util.fst"
let xret = (let _150_481 = (let _150_480 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _150_480))
in (FStar_Syntax_Util.comp_set_flags _150_481 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (
# 648 "FStar.TypeChecker.Util.fst"
let lc = (bind env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), (FStar_Syntax_Util.lcomp_of_comp xret)))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (
# 652 "FStar.TypeChecker.Util.fst"
let _69_863 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_483 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _150_482 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _150_483 _150_482)))
end else begin
()
end
in (
# 657 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 658 "FStar.TypeChecker.Util.fst"
let _69_869 = (destruct_comp c)
in (match (_69_869) with
| (res_t, wp, wlp) -> begin
(
# 659 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 660 "FStar.TypeChecker.Util.fst"
let us = (let _150_484 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_484)::[])
in (
# 661 "FStar.TypeChecker.Util.fst"
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
# 662 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_500 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _150_499 = (let _150_498 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_497 = (let _150_496 = (FStar_Syntax_Syntax.as_arg f)
in (let _150_495 = (let _150_494 = (FStar_Syntax_Syntax.as_arg wlp)
in (_150_494)::[])
in (_150_496)::_150_495))
in (_150_498)::_150_497))
in (FStar_Syntax_Syntax.mk_Tm_app _150_500 _150_499 None wlp.FStar_Syntax_Syntax.pos)))
in (
# 664 "FStar.TypeChecker.Util.fst"
let _69_874 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_501 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _150_501))
end else begin
()
end
in (
# 668 "FStar.TypeChecker.Util.fst"
let c2 = (mk_comp md res_t wp wlp flags)
in c2))))))
end)))))
end)))
end))
in (let _150_505 = (
# 670 "FStar.TypeChecker.Util.fst"
let _69_877 = lc
in (let _150_504 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _150_503 = if ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _150_502 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _150_502))) then begin
flags
end else begin
[]
end
in {FStar_Syntax_Syntax.eff_name = _150_504; FStar_Syntax_Syntax.res_typ = _69_877.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _150_503; FStar_Syntax_Syntax.comp = strengthen})))
in (_150_505, (
# 673 "FStar.TypeChecker.Util.fst"
let _69_879 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _69_879.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _69_879.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _69_879.FStar_TypeChecker_Env.implicits}))))))
end)

# 675 "FStar.TypeChecker.Util.fst"
let record_application_site : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (
# 676 "FStar.TypeChecker.Util.fst"
let comp = (fun _69_885 -> (match (()) with
| () -> begin
(
# 677 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 678 "FStar.TypeChecker.Util.fst"
let res_t = (FStar_Syntax_Util.comp_result c)
in if (((FStar_Syntax_Util.is_trivial_wp c) || (let _150_514 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals _150_514 FStar_Syntax_Const.prims_lid))) || (FStar_Syntax_Syntax.is_teff res_t)) then begin
c
end else begin
(
# 683 "FStar.TypeChecker.Util.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (FStar_TypeChecker_Common.t_unit)))
in (
# 684 "FStar.TypeChecker.Util.fst"
let _69_893 = (strengthen_precondition (Some ((fun _69_889 -> (match (()) with
| () -> begin
"push"
end)))) env e (FStar_Syntax_Util.lcomp_of_comp c) g)
in (match (_69_893) with
| (c, _69_892) -> begin
(
# 685 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 686 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 687 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 688 "FStar.TypeChecker.Util.fst"
let us = (let _150_518 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_518)::[])
in (
# 689 "FStar.TypeChecker.Util.fst"
let xret = (let _150_523 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _150_522 = (let _150_521 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_520 = (let _150_519 = (FStar_Syntax_Syntax.as_arg xexp)
in (_150_519)::[])
in (_150_521)::_150_520))
in (FStar_Syntax_Syntax.mk_Tm_app _150_523 _150_522 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 690 "FStar.TypeChecker.Util.fst"
let xret_comp = (let _150_524 = (mk_comp md_pure res_t xret xret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_524))
in (
# 691 "FStar.TypeChecker.Util.fst"
let lc = (let _150_530 = (let _150_529 = (let _150_528 = (strengthen_precondition (Some ((fun _69_900 -> (match (()) with
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
# 693 "FStar.TypeChecker.Util.fst"
let _69_902 = lc
in {FStar_Syntax_Syntax.eff_name = _69_902.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _69_902.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _69_902.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = comp})))

# 695 "FStar.TypeChecker.Util.fst"
let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env comp res_t -> (
# 696 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 697 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 698 "FStar.TypeChecker.Util.fst"
let y = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 699 "FStar.TypeChecker.Util.fst"
let _69_912 = (let _150_538 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _150_537 = (FStar_Syntax_Syntax.bv_to_name y)
in (_150_538, _150_537)))
in (match (_69_912) with
| (xexp, yexp) -> begin
(
# 700 "FStar.TypeChecker.Util.fst"
let us = (let _150_539 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_539)::[])
in (
# 701 "FStar.TypeChecker.Util.fst"
let yret = (let _150_544 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _150_543 = (let _150_542 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_541 = (let _150_540 = (FStar_Syntax_Syntax.as_arg yexp)
in (_150_540)::[])
in (_150_542)::_150_541))
in (FStar_Syntax_Syntax.mk_Tm_app _150_544 _150_543 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 702 "FStar.TypeChecker.Util.fst"
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
# 703 "FStar.TypeChecker.Util.fst"
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
# 704 "FStar.TypeChecker.Util.fst"
let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (
# 705 "FStar.TypeChecker.Util.fst"
let lc = (bind env None (FStar_Syntax_Util.lcomp_of_comp comp) (Some (x), (FStar_Syntax_Util.lcomp_of_comp lc2)))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))

# 708 "FStar.TypeChecker.Util.fst"
let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (
# 709 "FStar.TypeChecker.Util.fst"
let comp = (fun _69_924 -> (match (()) with
| () -> begin
(
# 710 "FStar.TypeChecker.Util.fst"
let _69_940 = (let _150_574 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _150_573 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _150_574 _150_573)))
in (match (_69_940) with
| ((md, _69_927, _69_929), (res_t, wp_then, wlp_then), (_69_936, wp_else, wlp_else)) -> begin
(
# 711 "FStar.TypeChecker.Util.fst"
let us = (let _150_575 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_575)::[])
in (
# 712 "FStar.TypeChecker.Util.fst"
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
# 713 "FStar.TypeChecker.Util.fst"
let wp = (ifthenelse md res_t guard wp_then wp_else)
in (
# 714 "FStar.TypeChecker.Util.fst"
let wlp = (ifthenelse md res_t guard wlp_then wlp_else)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(
# 716 "FStar.TypeChecker.Util.fst"
let comp = (mk_comp md res_t wp wlp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(
# 718 "FStar.TypeChecker.Util.fst"
let wp = (let _150_602 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _150_601 = (let _150_600 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_599 = (let _150_598 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _150_597 = (let _150_596 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_596)::[])
in (_150_598)::_150_597))
in (_150_600)::_150_599))
in (FStar_Syntax_Syntax.mk_Tm_app _150_602 _150_601 None wp.FStar_Syntax_Syntax.pos)))
in (
# 719 "FStar.TypeChecker.Util.fst"
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

# 726 "FStar.TypeChecker.Util.fst"
let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (
# 727 "FStar.TypeChecker.Util.fst"
let eff = (FStar_List.fold_left (fun eff _69_960 -> (match (_69_960) with
| (_69_958, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (
# 728 "FStar.TypeChecker.Util.fst"
let bind_cases = (fun _69_963 -> (match (()) with
| () -> begin
(
# 729 "FStar.TypeChecker.Util.fst"
let us = (let _150_619 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_150_619)::[])
in (
# 730 "FStar.TypeChecker.Util.fst"
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
# 732 "FStar.TypeChecker.Util.fst"
let default_case = (
# 733 "FStar.TypeChecker.Util.fst"
let post_k = (let _150_642 = (let _150_640 = (FStar_Syntax_Syntax.null_binder res_t)
in (_150_640)::[])
in (let _150_641 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _150_642 _150_641)))
in (
# 734 "FStar.TypeChecker.Util.fst"
let kwp = (let _150_645 = (let _150_643 = (FStar_Syntax_Syntax.null_binder post_k)
in (_150_643)::[])
in (let _150_644 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _150_645 _150_644)))
in (
# 735 "FStar.TypeChecker.Util.fst"
let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (
# 736 "FStar.TypeChecker.Util.fst"
let wp = (let _150_652 = (let _150_646 = (FStar_Syntax_Syntax.mk_binder post)
in (_150_646)::[])
in (let _150_651 = (let _150_650 = (let _150_647 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Errors.exhaustiveness_check _150_647))
in (let _150_649 = (let _150_648 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.false_lid _150_648))
in (FStar_All.pipe_left _150_650 _150_649)))
in (FStar_Syntax_Util.abs _150_652 _150_651 None)))
in (
# 737 "FStar.TypeChecker.Util.fst"
let wlp = (let _150_656 = (let _150_653 = (FStar_Syntax_Syntax.mk_binder post)
in (_150_653)::[])
in (let _150_655 = (let _150_654 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid _150_654))
in (FStar_Syntax_Util.abs _150_656 _150_655 None)))
in (
# 738 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (
# 740 "FStar.TypeChecker.Util.fst"
let comp = (FStar_List.fold_right (fun _69_980 celse -> (match (_69_980) with
| (g, cthen) -> begin
(
# 741 "FStar.TypeChecker.Util.fst"
let _69_998 = (let _150_659 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _150_659 celse))
in (match (_69_998) with
| ((md, _69_984, _69_986), (_69_989, wp_then, wlp_then), (_69_994, wp_else, wlp_else)) -> begin
(let _150_661 = (ifthenelse md res_t g wp_then wp_else)
in (let _150_660 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _150_661 _150_660 [])))
end))
end)) lcases default_case)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(add_equality_to_post_condition env comp res_t)
end else begin
(
# 745 "FStar.TypeChecker.Util.fst"
let comp = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (
# 746 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env comp.FStar_Syntax_Syntax.effect_name)
in (
# 747 "FStar.TypeChecker.Util.fst"
let _69_1006 = (destruct_comp comp)
in (match (_69_1006) with
| (_69_1003, wp, wlp) -> begin
(
# 748 "FStar.TypeChecker.Util.fst"
let wp = (let _150_668 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _150_667 = (let _150_666 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_665 = (let _150_664 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _150_663 = (let _150_662 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_662)::[])
in (_150_664)::_150_663))
in (_150_666)::_150_665))
in (FStar_Syntax_Syntax.mk_Tm_app _150_668 _150_667 None wp.FStar_Syntax_Syntax.pos)))
in (
# 749 "FStar.TypeChecker.Util.fst"
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

# 756 "FStar.TypeChecker.Util.fst"
let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (
# 757 "FStar.TypeChecker.Util.fst"
let close = (fun _69_1013 -> (match (()) with
| () -> begin
(
# 758 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in if (FStar_Syntax_Util.is_ml_comp c) then begin
c
end else begin
(
# 761 "FStar.TypeChecker.Util.fst"
let close_wp = (fun u_res md res_t bvs wp0 -> (FStar_List.fold_right (fun x wp -> (
# 763 "FStar.TypeChecker.Util.fst"
let bs = (let _150_694 = (FStar_Syntax_Syntax.mk_binder x)
in (_150_694)::[])
in (
# 764 "FStar.TypeChecker.Util.fst"
let us = (let _150_696 = (let _150_695 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (_150_695)::[])
in (u_res)::_150_696)
in (
# 765 "FStar.TypeChecker.Util.fst"
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
# 768 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 769 "FStar.TypeChecker.Util.fst"
let _69_1030 = (destruct_comp c)
in (match (_69_1030) with
| (t, wp, wlp) -> begin
(
# 770 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 771 "FStar.TypeChecker.Util.fst"
let u_res = (env.FStar_TypeChecker_Env.universe_of env c.FStar_Syntax_Syntax.result_typ)
in (
# 772 "FStar.TypeChecker.Util.fst"
let wp = (close_wp u_res md c.FStar_Syntax_Syntax.result_typ bvs wp)
in (
# 773 "FStar.TypeChecker.Util.fst"
let wlp = (close_wp u_res md c.FStar_Syntax_Syntax.result_typ bvs wlp)
in (mk_comp md c.FStar_Syntax_Syntax.result_typ wp wlp c.FStar_Syntax_Syntax.flags)))))
end))))
end)
end))
in (
# 775 "FStar.TypeChecker.Util.fst"
let _69_1035 = lc
in {FStar_Syntax_Syntax.eff_name = _69_1035.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _69_1035.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _69_1035.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))

# 777 "FStar.TypeChecker.Util.fst"
let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (
# 778 "FStar.TypeChecker.Util.fst"
let refine = (fun _69_1041 -> (match (()) with
| () -> begin
(
# 779 "FStar.TypeChecker.Util.fst"
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
# 787 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 788 "FStar.TypeChecker.Util.fst"
let t = c.FStar_Syntax_Syntax.result_typ
in (
# 789 "FStar.TypeChecker.Util.fst"
let c = (FStar_Syntax_Syntax.mk_Comp c)
in (
# 790 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (
# 791 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 792 "FStar.TypeChecker.Util.fst"
let ret = (let _150_716 = (let _150_715 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _150_715 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_716))
in (
# 793 "FStar.TypeChecker.Util.fst"
let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (
# 794 "FStar.TypeChecker.Util.fst"
let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (
# 796 "FStar.TypeChecker.Util.fst"
let c = (let _150_718 = (let _150_717 = (bind env None (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), eq_ret))
in (_150_717.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _150_718 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
in c)))))))))
end
end
end)
end))
in (
# 799 "FStar.TypeChecker.Util.fst"
let flags = if (((not ((FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)) && (not ((FStar_Syntax_Util.is_lcomp_partial_return lc)))) then begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_Syntax_Syntax.cflags
end else begin
lc.FStar_Syntax_Syntax.cflags
end
in (
# 805 "FStar.TypeChecker.Util.fst"
let _69_1053 = lc
in {FStar_Syntax_Syntax.eff_name = _69_1053.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _69_1053.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))

# 807 "FStar.TypeChecker.Util.fst"
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

# 813 "FStar.TypeChecker.Util.fst"
let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match ((let _150_739 = (FStar_Syntax_Subst.compress t)
in _150_739.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_69_1067) -> begin
(match ((let _150_740 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _150_740.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _69_1071) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.bool_lid) -> begin
(
# 818 "FStar.TypeChecker.Util.fst"
let _69_1074 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (
# 819 "FStar.TypeChecker.Util.fst"
let b2t = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos)
in (
# 820 "FStar.TypeChecker.Util.fst"
let lc = (let _150_743 = (let _150_742 = (let _150_741 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_741))
in (None, _150_742))
in (bind env (Some (e)) lc _150_743))
in (
# 821 "FStar.TypeChecker.Util.fst"
let e = (let _150_745 = (let _150_744 = (FStar_Syntax_Syntax.as_arg e)
in (_150_744)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _150_745 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (e, lc)))))
end
| _69_1080 -> begin
(e, lc)
end)
end
| _69_1082 -> begin
(e, lc)
end))

# 828 "FStar.TypeChecker.Util.fst"
let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (
# 829 "FStar.TypeChecker.Util.fst"
let gopt = if env.FStar_TypeChecker_Env.use_eq then begin
(let _150_754 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in (_150_754, false))
end else begin
(let _150_755 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in (_150_755, true))
end
in (match (gopt) with
| (None, _69_1090) -> begin
(FStar_TypeChecker_Rel.subtype_fail env lc.FStar_Syntax_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(match ((FStar_TypeChecker_Rel.guard_form g)) with
| FStar_TypeChecker_Common.Trivial -> begin
(
# 837 "FStar.TypeChecker.Util.fst"
let lc = (
# 837 "FStar.TypeChecker.Util.fst"
let _69_1097 = lc
in {FStar_Syntax_Syntax.eff_name = _69_1097.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _69_1097.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _69_1097.FStar_Syntax_Syntax.comp})
in (e, lc, g))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 841 "FStar.TypeChecker.Util.fst"
let g = (
# 841 "FStar.TypeChecker.Util.fst"
let _69_1102 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _69_1102.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _69_1102.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _69_1102.FStar_TypeChecker_Env.implicits})
in (
# 842 "FStar.TypeChecker.Util.fst"
let strengthen = (fun _69_1106 -> (match (()) with
| () -> begin
(
# 844 "FStar.TypeChecker.Util.fst"
let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (match ((let _150_758 = (FStar_Syntax_Subst.compress f)
in _150_758.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_69_1109, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _69_1118); FStar_Syntax_Syntax.tk = _69_1115; FStar_Syntax_Syntax.pos = _69_1113; FStar_Syntax_Syntax.vars = _69_1111}, _69_1123) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) -> begin
(
# 848 "FStar.TypeChecker.Util.fst"
let lc = (
# 848 "FStar.TypeChecker.Util.fst"
let _69_1126 = lc
in {FStar_Syntax_Syntax.eff_name = _69_1126.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _69_1126.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _69_1126.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| _69_1130 -> begin
(
# 852 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 853 "FStar.TypeChecker.Util.fst"
let _69_1132 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_762 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _150_761 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _150_760 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _150_759 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _150_762 _150_761 _150_760 _150_759)))))
end else begin
()
end
in (
# 860 "FStar.TypeChecker.Util.fst"
let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 861 "FStar.TypeChecker.Util.fst"
let _69_1137 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_69_1137) with
| (a, kwp) -> begin
(
# 862 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 863 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env ct.FStar_Syntax_Syntax.effect_name)
in (
# 864 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (
# 865 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 866 "FStar.TypeChecker.Util.fst"
let us = (let _150_763 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_150_763)::[])
in (
# 867 "FStar.TypeChecker.Util.fst"
let wp = (let _150_768 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ret)
in (let _150_767 = (let _150_766 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_765 = (let _150_764 = (FStar_Syntax_Syntax.as_arg xexp)
in (_150_764)::[])
in (_150_766)::_150_765))
in (FStar_Syntax_Syntax.mk_Tm_app _150_768 _150_767 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)))
in (
# 868 "FStar.TypeChecker.Util.fst"
let cret = (let _150_769 = (mk_comp md t wp wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_769))
in (
# 869 "FStar.TypeChecker.Util.fst"
let guard = if apply_guard then begin
(let _150_771 = (let _150_770 = (FStar_Syntax_Syntax.as_arg xexp)
in (_150_770)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _150_771 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end else begin
f
end
in (
# 870 "FStar.TypeChecker.Util.fst"
let _69_1148 = (let _150_779 = (FStar_All.pipe_left (fun _150_776 -> Some (_150_776)) (FStar_TypeChecker_Errors.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _150_778 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _150_777 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _150_779 _150_778 e cret _150_777))))
in (match (_69_1148) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(
# 874 "FStar.TypeChecker.Util.fst"
let x = (
# 874 "FStar.TypeChecker.Util.fst"
let _69_1149 = x
in {FStar_Syntax_Syntax.ppname = _69_1149.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_1149.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (
# 875 "FStar.TypeChecker.Util.fst"
let c = (let _150_781 = (let _150_780 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_780))
in (bind env (Some (e)) _150_781 (Some (x), eq_ret)))
in (
# 876 "FStar.TypeChecker.Util.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 877 "FStar.TypeChecker.Util.fst"
let _69_1154 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
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
# 880 "FStar.TypeChecker.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _69_3 -> (match (_69_3) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _69_1160 -> begin
[]
end))))
in (
# 881 "FStar.TypeChecker.Util.fst"
let lc = (
# 881 "FStar.TypeChecker.Util.fst"
let _69_1162 = lc
in (let _150_784 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _150_784; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (
# 882 "FStar.TypeChecker.Util.fst"
let g = (
# 882 "FStar.TypeChecker.Util.fst"
let _69_1165 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _69_1165.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _69_1165.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _69_1165.FStar_TypeChecker_Env.implicits})
in (e, lc, g))))))
end)
end)))

# 885 "FStar.TypeChecker.Util.fst"
let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (
# 886 "FStar.TypeChecker.Util.fst"
let mk_post_type = (fun res_t ens -> (
# 887 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _150_796 = (let _150_795 = (let _150_794 = (let _150_793 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _150_793))
in (_150_794)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _150_795 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _150_796))))
in (
# 889 "FStar.TypeChecker.Util.fst"
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
| (req, _69_1193)::(ens, _69_1188)::_69_1185 -> begin
(let _150_802 = (let _150_799 = (norm req)
in Some (_150_799))
in (let _150_801 = (let _150_800 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _150_800))
in (_150_802, _150_801)))
end
| _69_1197 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 903 "FStar.TypeChecker.Util.fst"
let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (wp, _69_1208)::(wlp, _69_1203)::_69_1200 -> begin
(
# 906 "FStar.TypeChecker.Util.fst"
let _69_1214 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (_69_1214) with
| (us_r, _69_1213) -> begin
(
# 907 "FStar.TypeChecker.Util.fst"
let _69_1218 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (_69_1218) with
| (us_e, _69_1217) -> begin
(
# 908 "FStar.TypeChecker.Util.fst"
let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (
# 909 "FStar.TypeChecker.Util.fst"
let as_req = (let _150_803 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.as_requires r)
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_803 us_r))
in (
# 910 "FStar.TypeChecker.Util.fst"
let as_ens = (let _150_804 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.as_ensures r)
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_804 us_e))
in (
# 911 "FStar.TypeChecker.Util.fst"
let req = (let _150_807 = (let _150_806 = (let _150_805 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_805)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.imp_tag)))::_150_806)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _150_807 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 912 "FStar.TypeChecker.Util.fst"
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
| _69_1225 -> begin
(FStar_All.failwith "Impossible")
end))
end
end)
end)))

# 922 "FStar.TypeChecker.Util.fst"
let maybe_instantiate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (
# 923 "FStar.TypeChecker.Util.fst"
let torig = (FStar_Syntax_Subst.compress t)
in if (not (env.FStar_TypeChecker_Env.instantiate_imp)) then begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end else begin
(match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 928 "FStar.TypeChecker.Util.fst"
let _69_1236 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_69_1236) with
| (bs, c) -> begin
(
# 929 "FStar.TypeChecker.Util.fst"
let rec aux = (fun subst _69_4 -> (match (_69_4) with
| (x, Some (FStar_Syntax_Syntax.Implicit (dot)))::rest -> begin
(
# 931 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 932 "FStar.TypeChecker.Util.fst"
let _69_1252 = (new_implicit_var env t)
in (match (_69_1252) with
| (v, _69_1250, g) -> begin
(
# 933 "FStar.TypeChecker.Util.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, v)))::subst
in (
# 934 "FStar.TypeChecker.Util.fst"
let _69_1258 = (aux subst rest)
in (match (_69_1258) with
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
# 938 "FStar.TypeChecker.Util.fst"
let _69_1264 = (aux [] bs)
in (match (_69_1264) with
| (args, bs, subst, guard) -> begin
(match ((args, bs)) with
| ([], _69_1267) -> begin
(e, torig, guard)
end
| (_69_1270, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end
| _69_1274 -> begin
(
# 949 "FStar.TypeChecker.Util.fst"
let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _69_1277 -> begin
(FStar_Syntax_Util.arrow bs c)
end)
in (
# 952 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.subst subst t)
in (
# 953 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk_Tm_app e args (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (e, t, guard))))
end)
end)))
end))
end
| _69_1282 -> begin
(e, t, FStar_TypeChecker_Rel.trivial_guard)
end)
end))

# 963 "FStar.TypeChecker.Util.fst"
let gen_univs : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe_uvar Prims.list * (FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  Prims.bool))  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(
# 965 "FStar.TypeChecker.Util.fst"
let s = (let _150_837 = (let _150_836 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _150_836))
in (FStar_All.pipe_right _150_837 FStar_Util.set_elements))
in (
# 966 "FStar.TypeChecker.Util.fst"
let r = (let _150_838 = (FStar_TypeChecker_Env.get_range env)
in Some (_150_838))
in (
# 967 "FStar.TypeChecker.Util.fst"
let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (
# 968 "FStar.TypeChecker.Util.fst"
let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (
# 969 "FStar.TypeChecker.Util.fst"
let _69_1289 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _150_843 = (let _150_840 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _150_840))
in (let _150_842 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _150_841 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _150_843 _150_842 _150_841))))
end else begin
()
end
in (
# 971 "FStar.TypeChecker.Util.fst"
let _69_1291 = (FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))))
in u_name))))))
in u_names)))
end)

# 975 "FStar.TypeChecker.Util.fst"
let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t -> (
# 976 "FStar.TypeChecker.Util.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (
# 977 "FStar.TypeChecker.Util.fst"
let univs = (FStar_Syntax_Free.univs t)
in (
# 978 "FStar.TypeChecker.Util.fst"
let _69_1299 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _150_852 = (let _150_851 = (let _150_850 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _150_850 (FStar_List.map (fun u -> (let _150_849 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _150_849 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _150_851 (FStar_String.concat ", ")))
in (FStar_Util.print1 "univs to gen : %s\n" _150_852))
end else begin
()
end
in (
# 982 "FStar.TypeChecker.Util.fst"
let gen = (gen_univs env univs)
in (
# 983 "FStar.TypeChecker.Util.fst"
let _69_1302 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _150_853 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _150_853))
end else begin
()
end
in (
# 985 "FStar.TypeChecker.Util.fst"
let ts = (FStar_Syntax_Subst.close_univ_vars gen t)
in (gen, ts))))))))

# 988 "FStar.TypeChecker.Util.fst"
let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> if (let _150_859 = (FStar_Util.for_all (fun _69_1310 -> (match (_69_1310) with
| (_69_1308, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _150_859)) then begin
None
end else begin
(
# 992 "FStar.TypeChecker.Util.fst"
let norm = (fun c -> (
# 993 "FStar.TypeChecker.Util.fst"
let _69_1313 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _150_862 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _150_862))
end else begin
()
end
in (
# 995 "FStar.TypeChecker.Util.fst"
let c = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.Eta)::[]) env c)
end else begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env c)
end
in (
# 998 "FStar.TypeChecker.Util.fst"
let _69_1316 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _150_863 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _150_863))
end else begin
()
end
in c))))
in (
# 1001 "FStar.TypeChecker.Util.fst"
let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (
# 1002 "FStar.TypeChecker.Util.fst"
let gen_uvars = (fun uvs -> (let _150_866 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _150_866 FStar_Util.set_elements)))
in (
# 1003 "FStar.TypeChecker.Util.fst"
let _69_1333 = (let _150_868 = (FStar_All.pipe_right ecs (FStar_List.map (fun _69_1323 -> (match (_69_1323) with
| (e, c) -> begin
(
# 1004 "FStar.TypeChecker.Util.fst"
let t = (FStar_All.pipe_right (FStar_Syntax_Util.comp_result c) FStar_Syntax_Subst.compress)
in (
# 1005 "FStar.TypeChecker.Util.fst"
let c = (norm c)
in (
# 1006 "FStar.TypeChecker.Util.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (
# 1007 "FStar.TypeChecker.Util.fst"
let t = ct.FStar_Syntax_Syntax.result_typ
in (
# 1008 "FStar.TypeChecker.Util.fst"
let univs = (FStar_Syntax_Free.univs t)
in (
# 1009 "FStar.TypeChecker.Util.fst"
let uvt = (FStar_Syntax_Free.uvars t)
in (
# 1010 "FStar.TypeChecker.Util.fst"
let uvs = (gen_uvars uvt)
in (univs, (uvs, e, c)))))))))
end))))
in (FStar_All.pipe_right _150_868 FStar_List.unzip))
in (match (_69_1333) with
| (univs, uvars) -> begin
(
# 1013 "FStar.TypeChecker.Util.fst"
let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (
# 1014 "FStar.TypeChecker.Util.fst"
let gen_univs = (gen_univs env univs)
in (
# 1015 "FStar.TypeChecker.Util.fst"
let _69_1337 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end else begin
()
end
in (
# 1017 "FStar.TypeChecker.Util.fst"
let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _69_1342 -> (match (_69_1342) with
| (uvs, e, c) -> begin
(
# 1018 "FStar.TypeChecker.Util.fst"
let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _69_1345 -> (match (_69_1345) with
| (u, k) -> begin
(match ((FStar_Unionfind.find u)) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(a, Some (FStar_Syntax_Syntax.imp_tag))
end
| FStar_Syntax_Syntax.Fixed (_69_1379) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _69_1382 -> begin
(
# 1024 "FStar.TypeChecker.Util.fst"
let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (
# 1025 "FStar.TypeChecker.Util.fst"
let _69_1386 = (FStar_Syntax_Util.arrow_formals k)
in (match (_69_1386) with
| (bs, kres) -> begin
(
# 1026 "FStar.TypeChecker.Util.fst"
let a = (let _150_874 = (let _150_873 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _150_872 -> Some (_150_872)) _150_873))
in (FStar_Syntax_Syntax.new_bv _150_874 kres))
in (
# 1027 "FStar.TypeChecker.Util.fst"
let t = (let _150_878 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _150_877 = (let _150_876 = (let _150_875 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _150_875))
in Some (_150_876))
in (FStar_Syntax_Util.abs bs _150_878 _150_877)))
in (
# 1028 "FStar.TypeChecker.Util.fst"
let _69_1389 = (FStar_Syntax_Util.set_uvar u t)
in (a, Some (FStar_Syntax_Syntax.imp_tag)))))
end)))
end)
end))))
in (
# 1032 "FStar.TypeChecker.Util.fst"
let _69_1410 = (match (tvars) with
| [] -> begin
(e, c)
end
| _69_1394 -> begin
(
# 1038 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]) env c)
in (
# 1039 "FStar.TypeChecker.Util.fst"
let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]) env e)
in (
# 1041 "FStar.TypeChecker.Util.fst"
let t = (match ((let _150_879 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _150_879.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(
# 1043 "FStar.TypeChecker.Util.fst"
let _69_1403 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (_69_1403) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| _69_1405 -> begin
(FStar_Syntax_Util.arrow tvars c)
end)
in (
# 1048 "FStar.TypeChecker.Util.fst"
let e' = (FStar_Syntax_Util.abs tvars e None)
in (let _150_880 = (FStar_Syntax_Syntax.mk_Total t)
in (e', _150_880))))))
end)
in (match (_69_1410) with
| (e, c) -> begin
(gen_univs, e, c)
end)))
end))))
in Some (ecs)))))
end)))))
end)

# 1053 "FStar.TypeChecker.Util.fst"
let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> (
# 1054 "FStar.TypeChecker.Util.fst"
let _69_1420 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_887 = (let _150_886 = (FStar_List.map (fun _69_1419 -> (match (_69_1419) with
| (lb, _69_1416, _69_1418) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _150_886 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _150_887))
end else begin
()
end
in (match ((let _150_889 = (FStar_All.pipe_right lecs (FStar_List.map (fun _69_1426 -> (match (_69_1426) with
| (_69_1423, e, c) -> begin
(e, c)
end))))
in (gen env _150_889))) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun _69_1431 -> (match (_69_1431) with
| (l, t, c) -> begin
(l, [], t, c)
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _69_1439 _69_1443 -> (match ((_69_1439, _69_1443)) with
| ((l, _69_1436, _69_1438), (us, e, c)) -> begin
(
# 1061 "FStar.TypeChecker.Util.fst"
let _69_1444 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
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

# 1074 "FStar.TypeChecker.Util.fst"
let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (
# 1075 "FStar.TypeChecker.Util.fst"
let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (
# 1076 "FStar.TypeChecker.Util.fst"
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
# 1082 "FStar.TypeChecker.Util.fst"
let is_var = (fun e -> (match ((let _150_914 = (FStar_Syntax_Subst.compress e)
in _150_914.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (_69_1461) -> begin
true
end
| _69_1464 -> begin
false
end))
in (
# 1085 "FStar.TypeChecker.Util.fst"
let decorate = (fun e t -> (
# 1086 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((
# 1088 "FStar.TypeChecker.Util.fst"
let _69_1471 = x
in {FStar_Syntax_Syntax.ppname = _69_1471.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_1471.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| _69_1474 -> begin
(
# 1089 "FStar.TypeChecker.Util.fst"
let _69_1475 = e
in (let _150_919 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _69_1475.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _150_919; FStar_Syntax_Syntax.pos = _69_1475.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _69_1475.FStar_Syntax_Syntax.vars}))
end)))
in (
# 1090 "FStar.TypeChecker.Util.fst"
let env = (
# 1090 "FStar.TypeChecker.Util.fst"
let _69_1477 = env
in (let _150_920 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _69_1477.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _69_1477.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _69_1477.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _69_1477.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _69_1477.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _69_1477.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _69_1477.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _69_1477.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _69_1477.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _69_1477.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _69_1477.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _69_1477.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _69_1477.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _69_1477.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _69_1477.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _150_920; FStar_TypeChecker_Env.is_iface = _69_1477.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _69_1477.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _69_1477.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _69_1477.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _69_1477.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _69_1477.FStar_TypeChecker_Env.use_bv_sorts}))
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
# 1094 "FStar.TypeChecker.Util.fst"
let _69_1483 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _150_925 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _150_925))
end else begin
()
end
in (let _150_926 = (decorate e t2)
in (_150_926, g)))
end)))))))

# 1099 "FStar.TypeChecker.Util.fst"
let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (
# 1100 "FStar.TypeChecker.Util.fst"
let discharge = (fun g -> (
# 1101 "FStar.TypeChecker.Util.fst"
let _69_1490 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (
# 1103 "FStar.TypeChecker.Util.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _150_936 = (discharge g)
in (let _150_935 = (lc.FStar_Syntax_Syntax.comp ())
in (_150_936, _150_935)))
end else begin
(
# 1106 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 1107 "FStar.TypeChecker.Util.fst"
let steps = (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.DeltaComp)::[]
in (
# 1108 "FStar.TypeChecker.Util.fst"
let c = (let _150_937 = (FStar_TypeChecker_Normalize.normalize_comp steps env c)
in (FStar_All.pipe_right _150_937 FStar_Syntax_Util.comp_to_comp_typ))
in (
# 1109 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 1110 "FStar.TypeChecker.Util.fst"
let _69_1501 = (destruct_comp c)
in (match (_69_1501) with
| (t, wp, _69_1500) -> begin
(
# 1111 "FStar.TypeChecker.Util.fst"
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
# 1112 "FStar.TypeChecker.Util.fst"
let _69_1503 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _150_946 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _150_946))
end else begin
()
end
in (
# 1114 "FStar.TypeChecker.Util.fst"
let g = (let _150_947 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _150_947))
in (let _150_949 = (discharge g)
in (let _150_948 = (FStar_Syntax_Syntax.mk_Comp c)
in (_150_949, _150_948))))))
end))))))
end)))

# 1120 "FStar.TypeChecker.Util.fst"
let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (
# 1121 "FStar.TypeChecker.Util.fst"
let short_bin_op = (fun f _69_5 -> (match (_69_5) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (fst, _69_1514)::[] -> begin
(f fst)
end
| _69_1518 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (
# 1126 "FStar.TypeChecker.Util.fst"
let op_and_e = (fun e -> (let _150_970 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _150_970 (fun _150_969 -> FStar_TypeChecker_Common.NonTrivial (_150_969)))))
in (
# 1127 "FStar.TypeChecker.Util.fst"
let op_or_e = (fun e -> (let _150_975 = (let _150_973 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _150_973))
in (FStar_All.pipe_right _150_975 (fun _150_974 -> FStar_TypeChecker_Common.NonTrivial (_150_974)))))
in (
# 1128 "FStar.TypeChecker.Util.fst"
let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _150_978 -> FStar_TypeChecker_Common.NonTrivial (_150_978))))
in (
# 1129 "FStar.TypeChecker.Util.fst"
let op_or_t = (fun t -> (let _150_982 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _150_982 (fun _150_981 -> FStar_TypeChecker_Common.NonTrivial (_150_981)))))
in (
# 1130 "FStar.TypeChecker.Util.fst"
let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _150_985 -> FStar_TypeChecker_Common.NonTrivial (_150_985))))
in (
# 1132 "FStar.TypeChecker.Util.fst"
let short_op_ite = (fun _69_6 -> (match (_69_6) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (guard, _69_1533)::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| _then::(guard, _69_1538)::[] -> begin
(let _150_989 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _150_989 (fun _150_988 -> FStar_TypeChecker_Common.NonTrivial (_150_988))))
end
| _69_1543 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (
# 1137 "FStar.TypeChecker.Util.fst"
let table = ((FStar_Syntax_Const.op_And, (short_bin_op op_and_e)))::((FStar_Syntax_Const.op_Or, (short_bin_op op_or_e)))::((FStar_Syntax_Const.and_lid, (short_bin_op op_and_t)))::((FStar_Syntax_Const.or_lid, (short_bin_op op_or_t)))::((FStar_Syntax_Const.imp_lid, (short_bin_op op_imp_t)))::((FStar_Syntax_Const.ite_lid, short_op_ite))::[]
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _69_1548) -> begin
(
# 1147 "FStar.TypeChecker.Util.fst"
let lid = fv.FStar_Syntax_Syntax.v
in (match ((FStar_Util.find_map table (fun _69_1554 -> (match (_69_1554) with
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
| _69_1559 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))

# 1154 "FStar.TypeChecker.Util.fst"
let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (match ((let _150_1025 = (FStar_Syntax_Subst.compress l)
in _150_1025.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (v, _69_1563) -> begin
(FStar_Util.for_some (FStar_Ident.lid_equals v.FStar_Syntax_Syntax.v) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| _69_1567 -> begin
false
end))

# 1175 "FStar.TypeChecker.Util.fst"
let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (
# 1176 "FStar.TypeChecker.Util.fst"
let pos = (fun bs -> (match (bs) with
| (hd, _69_1576)::_69_1573 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| _69_1580 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| (_69_1584, Some (FStar_Syntax_Syntax.Implicit (_69_1586)))::_69_1582 -> begin
bs
end
| _69_1592 -> begin
(match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
bs
end
| Some (t) -> begin
(match ((let _150_1032 = (FStar_Syntax_Subst.compress t)
in _150_1032.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', _69_1598) -> begin
(match ((FStar_Util.prefix_until (fun _69_7 -> (match (_69_7) with
| (_69_1603, Some (FStar_Syntax_Syntax.Implicit (_69_1605))) -> begin
false
end
| _69_1610 -> begin
true
end)) bs')) with
| None -> begin
bs
end
| Some ([], _69_1614, _69_1616) -> begin
bs
end
| Some (imps, _69_1621, _69_1623) -> begin
if (FStar_All.pipe_right imps (FStar_Util.for_all (fun _69_1629 -> (match (_69_1629) with
| (x, _69_1628) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end)))) then begin
(
# 1192 "FStar.TypeChecker.Util.fst"
let r = (pos bs)
in (
# 1193 "FStar.TypeChecker.Util.fst"
let imps = (FStar_All.pipe_right imps (FStar_List.map (fun _69_1633 -> (match (_69_1633) with
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
| _69_1636 -> begin
bs
end)
end)
end)))




