
open Prims
# 31 "FStar.TypeChecker.Util.fst"
type lcomp_with_binder =
(FStar_Syntax_Syntax.bv Prims.option * FStar_Syntax_Syntax.lcomp)

# 78 "FStar.TypeChecker.Util.fst"
let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _146_6 = (FStar_TypeChecker_Env.get_range env)
in (let _146_5 = (FStar_TypeChecker_Errors.failed_to_prove_specification errs)
in (FStar_TypeChecker_Errors.report _146_6 _146_5))))

# 85 "FStar.TypeChecker.Util.fst"
let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _146_9 = (FStar_Syntax_Subst.compress t)
in _146_9.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_62_12) -> begin
true
end
| _62_15 -> begin
false
end))

# 89 "FStar.TypeChecker.Util.fst"
let t_binders : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env -> (let _146_13 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right _146_13 (FStar_List.filter (fun _62_20 -> (match (_62_20) with
| (x, _62_19) -> begin
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
in (let _146_18 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Rel.new_uvar _146_18 bs k))))

# 99 "FStar.TypeChecker.Util.fst"
let new_uvar : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env k -> (let _146_23 = (new_uvar_aux env k)
in (Prims.fst _146_23)))

# 101 "FStar.TypeChecker.Util.fst"
let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun _62_1 -> (match (_62_1) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, _62_35); FStar_Syntax_Syntax.tk = _62_32; FStar_Syntax_Syntax.pos = _62_30; FStar_Syntax_Syntax.vars = _62_28} -> begin
uv
end
| _62_40 -> begin
(FStar_All.failwith "Impossible")
end))

# 105 "FStar.TypeChecker.Util.fst"
let new_implicit_var : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.uvar * FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env k -> (match ((FStar_Syntax_Util.destruct k FStar_Syntax_Const.range_of_lid)) with
| Some (_62_48::(tm, _62_45)::[]) -> begin
(
# 108 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))) None tm.FStar_Syntax_Syntax.pos)
in (t, [], FStar_TypeChecker_Rel.trivial_guard))
end
| _62_53 -> begin
(
# 112 "FStar.TypeChecker.Util.fst"
let _62_56 = (new_uvar_aux env k)
in (match (_62_56) with
| (t, u) -> begin
(
# 113 "FStar.TypeChecker.Util.fst"
let g = (
# 113 "FStar.TypeChecker.Util.fst"
let _62_57 = FStar_TypeChecker_Rel.trivial_guard
in (let _146_32 = (let _146_31 = (let _146_30 = (as_uvar u)
in (env, _146_30, t, k, u.FStar_Syntax_Syntax.pos))
in (_146_31)::[])
in {FStar_TypeChecker_Env.guard_f = _62_57.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _62_57.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _62_57.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _146_32}))
in (let _146_35 = (let _146_34 = (let _146_33 = (as_uvar u)
in (_146_33, u.FStar_Syntax_Syntax.pos))
in (_146_34)::[])
in (t, _146_35, g)))
end))
end))

# 116 "FStar.TypeChecker.Util.fst"
let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun r t -> (
# 117 "FStar.TypeChecker.Util.fst"
let uvs = (FStar_Syntax_Free.uvars t)
in if (not ((FStar_Util.set_is_empty uvs))) then begin
(
# 120 "FStar.TypeChecker.Util.fst"
let us = (let _146_42 = (let _146_41 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun _62_66 -> (match (_62_66) with
| (x, _62_65) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) _146_41))
in (FStar_All.pipe_right _146_42 (FStar_String.concat ", ")))
in (
# 122 "FStar.TypeChecker.Util.fst"
let hide_uvar_nums_saved = (FStar_ST.read FStar_Options.hide_uvar_nums)
in (
# 123 "FStar.TypeChecker.Util.fst"
let print_implicits_saved = (FStar_ST.read FStar_Options.print_implicits)
in (
# 124 "FStar.TypeChecker.Util.fst"
let _62_70 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums false)
in (
# 125 "FStar.TypeChecker.Util.fst"
let _62_72 = (FStar_ST.op_Colon_Equals FStar_Options.print_implicits true)
in (
# 126 "FStar.TypeChecker.Util.fst"
let _62_74 = (let _146_44 = (let _146_43 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us _146_43))
in (FStar_TypeChecker_Errors.report r _146_44))
in (
# 129 "FStar.TypeChecker.Util.fst"
let _62_76 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums hide_uvar_nums_saved)
in (FStar_ST.op_Colon_Equals FStar_Options.print_implicits print_implicits_saved))))))))
end else begin
()
end))

# 136 "FStar.TypeChecker.Util.fst"
let force_sort' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' = (fun s -> (match ((FStar_ST.read s.FStar_Syntax_Syntax.tk)) with
| None -> begin
(let _146_49 = (let _146_48 = (FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos)
in (let _146_47 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s" _146_48 _146_47)))
in (FStar_All.failwith _146_49))
end
| Some (tk) -> begin
tk
end))

# 140 "FStar.TypeChecker.Util.fst"
let force_sort = (fun s -> (let _146_51 = (force_sort' s)
in (FStar_Syntax_Syntax.mk _146_51 None s.FStar_Syntax_Syntax.pos)))

# 142 "FStar.TypeChecker.Util.fst"
let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env _62_91 -> (match (_62_91) with
| {FStar_Syntax_Syntax.lbname = _62_90; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _62_86; FStar_Syntax_Syntax.lbdef = e} -> begin
(
# 143 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(
# 146 "FStar.TypeChecker.Util.fst"
let _62_94 = if (univ_vars <> []) then begin
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
let _62_104 = (FStar_Syntax_Util.type_u ())
in (match (_62_104) with
| (k, _62_103) -> begin
(
# 151 "FStar.TypeChecker.Util.fst"
let t = (let _146_60 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right _146_60 Prims.fst))
in ((
# 152 "FStar.TypeChecker.Util.fst"
let _62_106 = a
in {FStar_Syntax_Syntax.ppname = _62_106.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _62_106.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), false))
end))
end
| _62_109 -> begin
(a, true)
end))
in (
# 155 "FStar.TypeChecker.Util.fst"
let rec aux = (fun vars e -> (
# 156 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, _62_116) -> begin
(aux vars e)
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _62_122) -> begin
(t, true)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _62_128) -> begin
(
# 162 "FStar.TypeChecker.Util.fst"
let _62_147 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _62_134 _62_137 -> (match ((_62_134, _62_137)) with
| ((scope, bs, check), (a, imp)) -> begin
(
# 163 "FStar.TypeChecker.Util.fst"
let _62_140 = (mk_binder scope a)
in (match (_62_140) with
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
in (match (_62_147) with
| (scope, bs, check) -> begin
(
# 170 "FStar.TypeChecker.Util.fst"
let _62_150 = (aux scope body)
in (match (_62_150) with
| (res, check_res) -> begin
(
# 171 "FStar.TypeChecker.Util.fst"
let c = (FStar_Syntax_Util.ml_comp res r)
in (
# 172 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Util.arrow bs c)
in (
# 173 "FStar.TypeChecker.Util.fst"
let _62_153 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _146_68 = (FStar_Range.string_of_range r)
in (let _146_67 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _146_68 _146_67)))
end else begin
()
end
in (t, (check_res || check)))))
end))
end))
end
| _62_156 -> begin
(let _146_70 = (let _146_69 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _146_69 Prims.fst))
in (_146_70, false))
end)))
in (
# 178 "FStar.TypeChecker.Util.fst"
let _62_159 = (let _146_71 = (t_binders env)
in (aux _146_71 e))
in (match (_62_159) with
| (t, b) -> begin
([], t, b)
end))))))
end
| _62_161 -> begin
(
# 182 "FStar.TypeChecker.Util.fst"
let _62_164 = (FStar_Syntax_Subst.open_univ_vars univ_vars t)
in (match (_62_164) with
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
| FStar_Syntax_Syntax.Pat_dot_term (x, _62_177) -> begin
(
# 211 "FStar.TypeChecker.Util.fst"
let _62_183 = (FStar_Syntax_Util.type_u ())
in (match (_62_183) with
| (k, _62_182) -> begin
(
# 212 "FStar.TypeChecker.Util.fst"
let t = (new_uvar env k)
in (
# 213 "FStar.TypeChecker.Util.fst"
let x = (
# 213 "FStar.TypeChecker.Util.fst"
let _62_185 = x
in {FStar_Syntax_Syntax.ppname = _62_185.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _62_185.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (
# 214 "FStar.TypeChecker.Util.fst"
let _62_190 = (let _146_84 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _146_84 t))
in (match (_62_190) with
| (e, u) -> begin
(
# 215 "FStar.TypeChecker.Util.fst"
let p = (
# 215 "FStar.TypeChecker.Util.fst"
let _62_191 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, e)); FStar_Syntax_Syntax.ty = _62_191.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _62_191.FStar_Syntax_Syntax.p})
in ([], [], [], env, e, p))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 219 "FStar.TypeChecker.Util.fst"
let _62_199 = (FStar_Syntax_Util.type_u ())
in (match (_62_199) with
| (t, _62_198) -> begin
(
# 220 "FStar.TypeChecker.Util.fst"
let x = (
# 220 "FStar.TypeChecker.Util.fst"
let _62_200 = x
in (let _146_85 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _62_200.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _62_200.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_85}))
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
let _62_210 = (FStar_Syntax_Util.type_u ())
in (match (_62_210) with
| (t, _62_209) -> begin
(
# 227 "FStar.TypeChecker.Util.fst"
let x = (
# 227 "FStar.TypeChecker.Util.fst"
let _62_211 = x
in (let _146_86 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _62_211.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _62_211.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_86}))
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
let _62_244 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _62_226 _62_229 -> (match ((_62_226, _62_229)) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(
# 234 "FStar.TypeChecker.Util.fst"
let _62_236 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_62_236) with
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
in (match (_62_244) with
| (b, a, w, env, args, pats) -> begin
(
# 238 "FStar.TypeChecker.Util.fst"
let e = (let _146_93 = (let _146_92 = (let _146_91 = (let _146_90 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (let _146_89 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app _146_90 _146_89 None p.FStar_Syntax_Syntax.p)))
in (_146_91, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))
in FStar_Syntax_Syntax.Tm_meta (_146_92))
in (FStar_Syntax_Syntax.mk _146_93 None p.FStar_Syntax_Syntax.p))
in (let _146_96 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _146_95 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _146_94 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in (_146_96, _146_95, _146_94, env, e, (
# 244 "FStar.TypeChecker.Util.fst"
let _62_246 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _62_246.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _62_246.FStar_Syntax_Syntax.p}))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (_62_249) -> begin
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
let pats = (FStar_List.map (fun _62_264 -> (match (_62_264) with
| (p, imp) -> begin
(let _146_108 = (elaborate_pat env p)
in (_146_108, imp))
end)) pats)
in (
# 256 "FStar.TypeChecker.Util.fst"
let _62_269 = (FStar_TypeChecker_Env.lookup_datacon env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_62_269) with
| (_62_267, t) -> begin
(
# 257 "FStar.TypeChecker.Util.fst"
let _62_273 = (FStar_Syntax_Util.arrow_formals t)
in (match (_62_273) with
| (f, _62_272) -> begin
(
# 258 "FStar.TypeChecker.Util.fst"
let rec aux = (fun formals pats -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _62_284::_62_282) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))))
end
| (_62_290::_62_288, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun _62_296 -> (match (_62_296) with
| (t, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(
# 264 "FStar.TypeChecker.Util.fst"
let a = (let _146_115 = (let _146_114 = (FStar_Syntax_Syntax.range_of_bv t)
in Some (_146_114))
in (FStar_Syntax_Syntax.new_bv _146_115 FStar_Syntax_Syntax.tun))
in (
# 265 "FStar.TypeChecker.Util.fst"
let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (let _146_116 = (maybe_dot inaccessible a r)
in (_146_116, true))))
end
| _62_303 -> begin
(let _146_120 = (let _146_119 = (let _146_118 = (let _146_117 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _146_117))
in (_146_118, (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in FStar_Syntax_Syntax.Error (_146_119))
in (Prims.raise _146_120))
end)
end))))
end
| (f::formals', (p, p_imp)::pats') -> begin
(match (f) with
| (_62_314, Some (FStar_Syntax_Syntax.Implicit (_62_316))) when p_imp -> begin
(let _146_121 = (aux formals' pats')
in ((p, true))::_146_121)
end
| (_62_321, Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(
# 277 "FStar.TypeChecker.Util.fst"
let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (
# 278 "FStar.TypeChecker.Util.fst"
let p = (maybe_dot inaccessible a (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
in (let _146_122 = (aux formals' pats)
in ((p, true))::_146_122)))
end
| (_62_329, imp) -> begin
(let _146_125 = (let _146_123 = (FStar_Syntax_Syntax.is_implicit imp)
in (p, _146_123))
in (let _146_124 = (aux formals' pats')
in (_146_125)::_146_124))
end)
end))
in (
# 284 "FStar.TypeChecker.Util.fst"
let _62_332 = p
in (let _146_128 = (let _146_127 = (let _146_126 = (aux f pats)
in (fv, _146_126))
in FStar_Syntax_Syntax.Pat_cons (_146_127))
in {FStar_Syntax_Syntax.v = _146_128; FStar_Syntax_Syntax.ty = _62_332.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _62_332.FStar_Syntax_Syntax.p})))
end))
end)))
end
| _62_335 -> begin
p
end)))
in (
# 288 "FStar.TypeChecker.Util.fst"
let one_pat = (fun allow_wc_dependence env p -> (
# 289 "FStar.TypeChecker.Util.fst"
let p = (elaborate_pat env p)
in (
# 290 "FStar.TypeChecker.Util.fst"
let _62_347 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_62_347) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))) with
| Some (x) -> begin
(let _146_137 = (let _146_136 = (let _146_135 = (FStar_TypeChecker_Errors.nonlinear_pattern_variable x)
in (_146_135, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_146_136))
in (Prims.raise _146_137))
end
| _62_351 -> begin
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
let _62_367 = (one_pat false env q)
in (match (_62_367) with
| (b, a, _62_364, te, q) -> begin
(
# 303 "FStar.TypeChecker.Util.fst"
let _62_382 = (FStar_List.fold_right (fun p _62_372 -> (match (_62_372) with
| (w, args, pats) -> begin
(
# 304 "FStar.TypeChecker.Util.fst"
let _62_378 = (one_pat false env p)
in (match (_62_378) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv FStar_Syntax_Syntax.bv_eq a a'))) then begin
(let _146_147 = (let _146_146 = (let _146_145 = (FStar_TypeChecker_Errors.disjunctive_pattern_vars a a')
in (let _146_144 = (FStar_TypeChecker_Env.get_range env)
in (_146_145, _146_144)))
in FStar_Syntax_Syntax.Error (_146_146))
in (Prims.raise _146_147))
end else begin
(let _146_149 = (let _146_148 = (FStar_Syntax_Syntax.as_arg arg)
in (_146_148)::args)
in ((FStar_List.append w' w), _146_149, (p)::pats))
end
end))
end)) pats ([], [], []))
in (match (_62_382) with
| (w, args, pats) -> begin
(let _146_151 = (let _146_150 = (FStar_Syntax_Syntax.as_arg te)
in (_146_150)::args)
in ((FStar_List.append b w), _146_151, (
# 309 "FStar.TypeChecker.Util.fst"
let _62_383 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((q)::pats); FStar_Syntax_Syntax.ty = _62_383.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _62_383.FStar_Syntax_Syntax.p})))
end))
end))
end
| _62_386 -> begin
(
# 312 "FStar.TypeChecker.Util.fst"
let _62_394 = (one_pat true env p)
in (match (_62_394) with
| (b, _62_389, _62_391, arg, p) -> begin
(let _146_153 = (let _146_152 = (FStar_Syntax_Syntax.as_arg arg)
in (_146_152)::[])
in (b, _146_153, p))
end))
end))
in (
# 315 "FStar.TypeChecker.Util.fst"
let _62_398 = (top_level_pat_as_args env p)
in (match (_62_398) with
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
| (_62_412, FStar_Syntax_Syntax.Tm_uinst (e, _62_415)) -> begin
(aux p e)
end
| (FStar_Syntax_Syntax.Pat_constant (_62_420), FStar_Syntax_Syntax.Tm_constant (_62_423)) -> begin
(let _146_168 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v _146_168))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(
# 331 "FStar.TypeChecker.Util.fst"
let _62_431 = if (not ((FStar_Syntax_Syntax.bv_eq x y))) then begin
(let _146_171 = (let _146_170 = (FStar_Syntax_Print.bv_to_string x)
in (let _146_169 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _146_170 _146_169)))
in (FStar_All.failwith _146_171))
end else begin
()
end
in (
# 333 "FStar.TypeChecker.Util.fst"
let _62_433 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _146_173 = (FStar_Syntax_Print.bv_to_string x)
in (let _146_172 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _146_173 _146_172)))
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
let _62_436 = x
in {FStar_Syntax_Syntax.ppname = _62_436.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _62_436.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x)) s.FStar_Syntax_Syntax.n)))))
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(
# 340 "FStar.TypeChecker.Util.fst"
let _62_444 = if (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation) then begin
(let _146_176 = (let _146_175 = (FStar_Syntax_Print.bv_to_string x)
in (let _146_174 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _146_175 _146_174)))
in (FStar_All.failwith _146_176))
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
let _62_447 = x
in {FStar_Syntax_Syntax.ppname = _62_447.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _62_447.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x)) s.FStar_Syntax_Syntax.n))))
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _62_452), _62_456) -> begin
(
# 347 "FStar.TypeChecker.Util.fst"
let s = (force_sort e)
in (
# 348 "FStar.TypeChecker.Util.fst"
let x = (
# 348 "FStar.TypeChecker.Util.fst"
let _62_459 = x
in {FStar_Syntax_Syntax.ppname = _62_459.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _62_459.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
(
# 352 "FStar.TypeChecker.Util.fst"
let _62_469 = if (not ((FStar_Syntax_Syntax.fv_eq fv fv'))) then begin
(let _146_177 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _146_177))
end else begin
()
end
in (let _146_178 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv', []))) _146_178)))
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
(
# 359 "FStar.TypeChecker.Util.fst"
let _62_512 = if (let _146_179 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right _146_179 Prims.op_Negation)) then begin
(let _146_180 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _146_180))
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
(let _146_187 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev matched_pats)))) _146_187))
end
| (arg::args, (argpat, _62_528)::argpats) -> begin
(match ((arg, argpat.FStar_Syntax_Syntax.v)) with
| ((e, Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (_62_538)) -> begin
(
# 368 "FStar.TypeChecker.Util.fst"
let x = (let _146_188 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _146_188))
in (
# 369 "FStar.TypeChecker.Util.fst"
let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((e, imp), _62_547) -> begin
(
# 373 "FStar.TypeChecker.Util.fst"
let pat = (let _146_190 = (aux argpat e)
in (let _146_189 = (FStar_Syntax_Syntax.is_implicit imp)
in (_146_190, _146_189)))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _62_551 -> begin
(let _146_193 = (let _146_192 = (FStar_Syntax_Print.pat_to_string p)
in (let _146_191 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _146_192 _146_191)))
in (FStar_All.failwith _146_193))
end))
in (match_args [] args argpats))))
end
| _62_553 -> begin
(let _146_198 = (let _146_197 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (let _146_196 = (FStar_Syntax_Print.pat_to_string qq)
in (let _146_195 = (let _146_194 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right _146_194 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _146_197 _146_196 _146_195))))
in (FStar_All.failwith _146_198))
end))))
in (match ((p.FStar_Syntax_Syntax.v, exps)) with
| (FStar_Syntax_Syntax.Pat_disj (ps), _62_557) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(
# 386 "FStar.TypeChecker.Util.fst"
let ps = (FStar_List.map2 aux ps exps)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj (ps)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p))
end
| (_62_561, e::[]) -> begin
(aux p e)
end
| _62_566 -> begin
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
let pat_as_arg = (fun _62_574 -> (match (_62_574) with
| (p, i) -> begin
(
# 399 "FStar.TypeChecker.Util.fst"
let _62_577 = (decorated_pattern_as_term p)
in (match (_62_577) with
| (vars, te) -> begin
(let _146_206 = (let _146_205 = (FStar_Syntax_Syntax.as_implicit i)
in (te, _146_205))
in (vars, _146_206))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_62_579) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _146_207 = (mk (FStar_Syntax_Syntax.Tm_constant (c)))
in ([], _146_207))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(let _146_208 = (mk (FStar_Syntax_Syntax.Tm_name (x)))
in ((x)::[], _146_208))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 413 "FStar.TypeChecker.Util.fst"
let _62_592 = (let _146_209 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _146_209 FStar_List.unzip))
in (match (_62_592) with
| (vars, args) -> begin
(
# 414 "FStar.TypeChecker.Util.fst"
let vars = (FStar_List.flatten vars)
in (let _146_213 = (let _146_212 = (let _146_211 = (let _146_210 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (_146_210, args))
in FStar_Syntax_Syntax.Tm_app (_146_211))
in (mk _146_212))
in (vars, _146_213)))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
([], e)
end)))))

# 424 "FStar.TypeChecker.Util.fst"
let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (
# 425 "FStar.TypeChecker.Util.fst"
let _62_616 = (match (c.FStar_Syntax_Syntax.effect_args) with
| (wp, _62_605)::(wlp, _62_601)::[] -> begin
(wp, wlp)
end
| _62_609 -> begin
(let _146_219 = (let _146_218 = (let _146_217 = (FStar_List.map (fun _62_613 -> (match (_62_613) with
| (x, _62_612) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right _146_217 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str _146_218))
in (FStar_All.failwith _146_219))
end)
in (match (_62_616) with
| (wp, wlp) -> begin
(c.FStar_Syntax_Syntax.result_typ, wp, wlp)
end)))

# 431 "FStar.TypeChecker.Util.fst"
let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (
# 432 "FStar.TypeChecker.Util.fst"
let _62_624 = (destruct_comp c)
in (match (_62_624) with
| (_62_621, wp, wlp) -> begin
(let _146_241 = (let _146_240 = (let _146_236 = (lift c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _146_236))
in (let _146_239 = (let _146_238 = (let _146_237 = (lift c.FStar_Syntax_Syntax.result_typ wlp)
in (FStar_Syntax_Syntax.as_arg _146_237))
in (_146_238)::[])
in (_146_240)::_146_239))
in {FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _146_241; FStar_Syntax_Syntax.flags = []})
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
| Some (_62_632, c) -> begin
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
let _62_646 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))

# 460 "FStar.TypeChecker.Util.fst"
let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (
# 461 "FStar.TypeChecker.Util.fst"
let _62_657 = (let _146_255 = (norm_eff_name env l1)
in (let _146_254 = (norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _146_255 _146_254)))
in (match (_62_657) with
| (m, _62_654, _62_656) -> begin
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
let _62_669 = (FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (_62_669) with
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
let _62_675 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (_62_675) with
| (a, kwp) -> begin
(let _146_269 = (destruct_comp m1)
in (let _146_268 = (destruct_comp m2)
in ((md, a, kwp), _146_269, _146_268)))
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
let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md result wp wlp flags -> (let _146_292 = (let _146_291 = (let _146_290 = (FStar_Syntax_Syntax.as_arg wp)
in (let _146_289 = (let _146_288 = (FStar_Syntax_Syntax.as_arg wlp)
in (_146_288)::[])
in (_146_290)::_146_289))
in {FStar_Syntax_Syntax.effect_name = md.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = _146_291; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp _146_292)))

# 495 "FStar.TypeChecker.Util.fst"
let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (
# 496 "FStar.TypeChecker.Util.fst"
let _62_689 = lc
in (let _146_299 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _62_689.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _146_299; FStar_Syntax_Syntax.cflags = _62_689.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _62_691 -> (match (()) with
| () -> begin
(let _146_298 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _146_298))
end))})))

# 499 "FStar.TypeChecker.Util.fst"
let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _146_302 = (FStar_Syntax_Subst.compress t)
in _146_302.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_62_694) -> begin
true
end
| _62_697 -> begin
false
end))

# 503 "FStar.TypeChecker.Util.fst"
let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v -> (
# 505 "FStar.TypeChecker.Util.fst"
let c = if (let _146_309 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation _146_309)) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(
# 508 "FStar.TypeChecker.Util.fst"
let m = (let _146_310 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must _146_310))
in (
# 509 "FStar.TypeChecker.Util.fst"
let _62_704 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_62_704) with
| (a, kwp) -> begin
(
# 510 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 511 "FStar.TypeChecker.Util.fst"
let wp = (let _146_318 = (let _146_317 = (let _146_312 = (let _146_311 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_146_311)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _146_312 env m m.FStar_Syntax_Syntax.ret))
in (let _146_316 = (let _146_315 = (FStar_Syntax_Syntax.as_arg t)
in (let _146_314 = (let _146_313 = (FStar_Syntax_Syntax.as_arg v)
in (_146_313)::[])
in (_146_315)::_146_314))
in (FStar_Syntax_Syntax.mk_Tm_app _146_317 _146_316 (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _146_318))
in (
# 512 "FStar.TypeChecker.Util.fst"
let wlp = wp
in (mk_comp m t wp wlp ((FStar_Syntax_Syntax.RETURN)::[])))))
end)))
end
in (
# 514 "FStar.TypeChecker.Util.fst"
let _62_709 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return"))) then begin
(let _146_321 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _146_320 = (FStar_Syntax_Print.term_to_string v)
in (let _146_319 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _146_321 _146_320 _146_319))))
end else begin
()
end
in c)))

# 519 "FStar.TypeChecker.Util.fst"
let bind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun env e1opt lc1 _62_716 -> (match (_62_716) with
| (b, lc2) -> begin
(
# 520 "FStar.TypeChecker.Util.fst"
let _62_724 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(
# 522 "FStar.TypeChecker.Util.fst"
let bstr = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _146_332 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (let _146_331 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _146_330 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" _146_332 _146_331 bstr _146_330)))))
end else begin
()
end
in (
# 528 "FStar.TypeChecker.Util.fst"
let bind_it = (fun _62_727 -> (match (()) with
| () -> begin
(
# 529 "FStar.TypeChecker.Util.fst"
let c1 = (lc1.FStar_Syntax_Syntax.comp ())
in (
# 530 "FStar.TypeChecker.Util.fst"
let c2 = (lc2.FStar_Syntax_Syntax.comp ())
in (
# 531 "FStar.TypeChecker.Util.fst"
let _62_733 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _146_339 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _146_338 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _146_337 = (FStar_Syntax_Print.comp_to_string c1)
in (let _146_336 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (let _146_335 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" _146_339 _146_338 _146_337 _146_336 _146_335))))))
end else begin
()
end
in (
# 540 "FStar.TypeChecker.Util.fst"
let try_simplify = (fun _62_736 -> (match (()) with
| () -> begin
(
# 541 "FStar.TypeChecker.Util.fst"
let aux = (fun _62_738 -> (match (()) with
| () -> begin
if (FStar_Syntax_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some ((c2, "trivial no binder"))
end
| Some (_62_741) -> begin
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
(let _146_347 = (let _146_346 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT ((x, e)))::[]) c2)
in (_146_346, reason))
in Some (_146_347))
end
| _62_751 -> begin
(aux ())
end))
in if ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2)) then begin
(subst_c2 "both total")
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2)) then begin
(let _146_349 = (let _146_348 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in (_146_348, "both gtot"))
in Some (_146_349))
end else begin
(match ((e1opt, b)) with
| (Some (e), Some (x)) -> begin
if ((FStar_Syntax_Util.is_total_comp c1) && (not ((FStar_Syntax_Syntax.is_null_bv x)))) then begin
(subst_c2 "substituted e")
end else begin
(aux ())
end
end
| _62_758 -> begin
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
let _62_776 = (lift_and_destruct env c1 c2)
in (match (_62_776) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(
# 574 "FStar.TypeChecker.Util.fst"
let bs = (match (b) with
| None -> begin
(let _146_350 = (FStar_Syntax_Syntax.null_binder t1)
in (_146_350)::[])
end
| Some (x) -> begin
(let _146_351 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_351)::[])
end)
in (
# 577 "FStar.TypeChecker.Util.fst"
let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp None))
in (
# 578 "FStar.TypeChecker.Util.fst"
let wp_args = (let _146_366 = (FStar_Syntax_Syntax.as_arg t1)
in (let _146_365 = (let _146_364 = (FStar_Syntax_Syntax.as_arg t2)
in (let _146_363 = (let _146_362 = (FStar_Syntax_Syntax.as_arg wp1)
in (let _146_361 = (let _146_360 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _146_359 = (let _146_358 = (let _146_354 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg _146_354))
in (let _146_357 = (let _146_356 = (let _146_355 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _146_355))
in (_146_356)::[])
in (_146_358)::_146_357))
in (_146_360)::_146_359))
in (_146_362)::_146_361))
in (_146_364)::_146_363))
in (_146_366)::_146_365))
in (
# 579 "FStar.TypeChecker.Util.fst"
let wlp_args = (let _146_374 = (FStar_Syntax_Syntax.as_arg t1)
in (let _146_373 = (let _146_372 = (FStar_Syntax_Syntax.as_arg t2)
in (let _146_371 = (let _146_370 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _146_369 = (let _146_368 = (let _146_367 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _146_367))
in (_146_368)::[])
in (_146_370)::_146_369))
in (_146_372)::_146_371))
in (_146_374)::_146_373))
in (
# 580 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t2)))::[]) kwp)
in (
# 581 "FStar.TypeChecker.Util.fst"
let us = (let _146_377 = (env.FStar_TypeChecker_Env.universe_of env t1)
in (let _146_376 = (let _146_375 = (env.FStar_TypeChecker_Env.universe_of env t2)
in (_146_375)::[])
in (_146_377)::_146_376))
in (
# 582 "FStar.TypeChecker.Util.fst"
let wp = (let _146_378 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _146_378 wp_args None t2.FStar_Syntax_Syntax.pos))
in (
# 583 "FStar.TypeChecker.Util.fst"
let wlp = (let _146_379 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wlp)
in (FStar_Syntax_Syntax.mk_Tm_app _146_379 wlp_args None t2.FStar_Syntax_Syntax.pos))
in (
# 584 "FStar.TypeChecker.Util.fst"
let c = (mk_comp md t2 wp wlp [])
in c)))))))))
end))
end)))))
end))
in (let _146_380 = (join_lcomp env lc1 lc2)
in {FStar_Syntax_Syntax.eff_name = _146_380; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it})))
end))

# 591 "FStar.TypeChecker.Util.fst"
let lift_formula : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t mk_wp mk_wlp f -> (
# 592 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 593 "FStar.TypeChecker.Util.fst"
let _62_798 = (FStar_TypeChecker_Env.wp_signature env md_pure.FStar_Syntax_Syntax.mname)
in (match (_62_798) with
| (a, kwp) -> begin
(
# 594 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 595 "FStar.TypeChecker.Util.fst"
let wp = (let _146_394 = (let _146_393 = (FStar_Syntax_Syntax.as_arg t)
in (let _146_392 = (let _146_391 = (FStar_Syntax_Syntax.as_arg f)
in (_146_391)::[])
in (_146_393)::_146_392))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wp _146_394 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (
# 596 "FStar.TypeChecker.Util.fst"
let wlp = (let _146_398 = (let _146_397 = (FStar_Syntax_Syntax.as_arg t)
in (let _146_396 = (let _146_395 = (FStar_Syntax_Syntax.as_arg f)
in (_146_395)::[])
in (_146_397)::_146_396))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wlp _146_398 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
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
if (let _146_422 = (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)
in (FStar_All.pipe_left Prims.op_Negation _146_422)) then begin
f
end else begin
(let _146_423 = (reason ())
in (label _146_423 r f))
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
let _62_818 = g
in (let _146_431 = (let _146_430 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_146_430))
in {FStar_TypeChecker_Env.guard_f = _146_431; FStar_TypeChecker_Env.deferred = _62_818.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _62_818.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _62_818.FStar_TypeChecker_Env.implicits}))
end))

# 613 "FStar.TypeChecker.Util.fst"
let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(
# 615 "FStar.TypeChecker.Util.fst"
let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| _62_829 -> begin
g2
end))

# 619 "FStar.TypeChecker.Util.fst"
let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (
# 620 "FStar.TypeChecker.Util.fst"
let weaken = (fun _62_834 -> (match (()) with
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
let _62_843 = (destruct_comp c)
in (match (_62_843) with
| (res_t, wp, wlp) -> begin
(
# 629 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 630 "FStar.TypeChecker.Util.fst"
let us = (let _146_444 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_146_444)::[])
in (
# 631 "FStar.TypeChecker.Util.fst"
let wp = (let _146_451 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _146_450 = (let _146_449 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_448 = (let _146_447 = (FStar_Syntax_Syntax.as_arg f)
in (let _146_446 = (let _146_445 = (FStar_Syntax_Syntax.as_arg wp)
in (_146_445)::[])
in (_146_447)::_146_446))
in (_146_449)::_146_448))
in (FStar_Syntax_Syntax.mk_Tm_app _146_451 _146_450 None wp.FStar_Syntax_Syntax.pos)))
in (
# 632 "FStar.TypeChecker.Util.fst"
let wlp = (let _146_458 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _146_457 = (let _146_456 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_455 = (let _146_454 = (FStar_Syntax_Syntax.as_arg f)
in (let _146_453 = (let _146_452 = (FStar_Syntax_Syntax.as_arg wlp)
in (_146_452)::[])
in (_146_454)::_146_453))
in (_146_456)::_146_455))
in (FStar_Syntax_Syntax.mk_Tm_app _146_458 _146_457 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp c.FStar_Syntax_Syntax.flags)))))
end)))
end
end))
end))
in (
# 634 "FStar.TypeChecker.Util.fst"
let _62_848 = lc
in {FStar_Syntax_Syntax.eff_name = _62_848.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _62_848.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _62_848.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))

# 636 "FStar.TypeChecker.Util.fst"
let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> if (FStar_TypeChecker_Rel.is_trivial g0) then begin
(lc, g0)
end else begin
(
# 640 "FStar.TypeChecker.Util.fst"
let _62_855 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _146_478 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _146_477 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _146_478 _146_477)))
end else begin
()
end
in (
# 644 "FStar.TypeChecker.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _62_2 -> (match (_62_2) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _62_861 -> begin
[]
end))))
in (
# 645 "FStar.TypeChecker.Util.fst"
let strengthen = (fun _62_864 -> (match (()) with
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
let xret = (let _146_483 = (let _146_482 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _146_482))
in (FStar_Syntax_Util.comp_set_flags _146_483 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (
# 656 "FStar.TypeChecker.Util.fst"
let lc = (bind env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), (FStar_Syntax_Util.lcomp_of_comp xret)))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (
# 660 "FStar.TypeChecker.Util.fst"
let _62_874 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _146_485 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _146_484 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _146_485 _146_484)))
end else begin
()
end
in (
# 665 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 666 "FStar.TypeChecker.Util.fst"
let _62_880 = (destruct_comp c)
in (match (_62_880) with
| (res_t, wp, wlp) -> begin
(
# 667 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 668 "FStar.TypeChecker.Util.fst"
let us = (let _146_486 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_146_486)::[])
in (
# 669 "FStar.TypeChecker.Util.fst"
let wp = (let _146_495 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assert_p)
in (let _146_494 = (let _146_493 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_492 = (let _146_491 = (let _146_488 = (let _146_487 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason _146_487 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _146_488))
in (let _146_490 = (let _146_489 = (FStar_Syntax_Syntax.as_arg wp)
in (_146_489)::[])
in (_146_491)::_146_490))
in (_146_493)::_146_492))
in (FStar_Syntax_Syntax.mk_Tm_app _146_495 _146_494 None wp.FStar_Syntax_Syntax.pos)))
in (
# 670 "FStar.TypeChecker.Util.fst"
let wlp = (let _146_502 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _146_501 = (let _146_500 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_499 = (let _146_498 = (FStar_Syntax_Syntax.as_arg f)
in (let _146_497 = (let _146_496 = (FStar_Syntax_Syntax.as_arg wlp)
in (_146_496)::[])
in (_146_498)::_146_497))
in (_146_500)::_146_499))
in (FStar_Syntax_Syntax.mk_Tm_app _146_502 _146_501 None wlp.FStar_Syntax_Syntax.pos)))
in (
# 672 "FStar.TypeChecker.Util.fst"
let _62_885 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _146_503 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _146_503))
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
in (let _146_507 = (
# 678 "FStar.TypeChecker.Util.fst"
let _62_888 = lc
in (let _146_506 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _146_505 = if ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _146_504 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _146_504))) then begin
flags
end else begin
[]
end
in {FStar_Syntax_Syntax.eff_name = _146_506; FStar_Syntax_Syntax.res_typ = _62_888.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _146_505; FStar_Syntax_Syntax.comp = strengthen})))
in (_146_507, (
# 681 "FStar.TypeChecker.Util.fst"
let _62_890 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _62_890.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _62_890.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _62_890.FStar_TypeChecker_Env.implicits}))))))
end)

# 683 "FStar.TypeChecker.Util.fst"
let record_application_site : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (
# 684 "FStar.TypeChecker.Util.fst"
let comp = (fun _62_896 -> (match (()) with
| () -> begin
(
# 685 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 686 "FStar.TypeChecker.Util.fst"
let res_t = (FStar_Syntax_Util.comp_result c)
in if (((FStar_Syntax_Util.is_trivial_wp c) || (let _146_516 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals _146_516 FStar_Syntax_Const.prims_lid))) || (FStar_Syntax_Syntax.is_teff res_t)) then begin
c
end else begin
(
# 691 "FStar.TypeChecker.Util.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (FStar_TypeChecker_Common.t_unit)))
in (
# 692 "FStar.TypeChecker.Util.fst"
let _62_904 = (strengthen_precondition (Some ((fun _62_900 -> (match (()) with
| () -> begin
"push"
end)))) env e (FStar_Syntax_Util.lcomp_of_comp c) g)
in (match (_62_904) with
| (c, _62_903) -> begin
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
let us = (let _146_520 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_146_520)::[])
in (
# 697 "FStar.TypeChecker.Util.fst"
let xret = (let _146_525 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _146_524 = (let _146_523 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_522 = (let _146_521 = (FStar_Syntax_Syntax.as_arg xexp)
in (_146_521)::[])
in (_146_523)::_146_522))
in (FStar_Syntax_Syntax.mk_Tm_app _146_525 _146_524 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 698 "FStar.TypeChecker.Util.fst"
let xret_comp = (let _146_526 = (mk_comp md_pure res_t xret xret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_526))
in (
# 699 "FStar.TypeChecker.Util.fst"
let lc = (let _146_532 = (let _146_531 = (let _146_530 = (strengthen_precondition (Some ((fun _62_911 -> (match (()) with
| () -> begin
"pop"
end)))) env xexp xret_comp g)
in (FStar_All.pipe_left Prims.fst _146_530))
in (Some (x), _146_531))
in (bind env None c _146_532))
in (lc.FStar_Syntax_Syntax.comp ()))))))))
end)))
end))
end))
in (
# 701 "FStar.TypeChecker.Util.fst"
let _62_913 = lc
in {FStar_Syntax_Syntax.eff_name = _62_913.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _62_913.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _62_913.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = comp})))

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
let _62_923 = (let _146_540 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _146_539 = (FStar_Syntax_Syntax.bv_to_name y)
in (_146_540, _146_539)))
in (match (_62_923) with
| (xexp, yexp) -> begin
(
# 708 "FStar.TypeChecker.Util.fst"
let us = (let _146_541 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_146_541)::[])
in (
# 709 "FStar.TypeChecker.Util.fst"
let yret = (let _146_546 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _146_545 = (let _146_544 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_543 = (let _146_542 = (FStar_Syntax_Syntax.as_arg yexp)
in (_146_542)::[])
in (_146_544)::_146_543))
in (FStar_Syntax_Syntax.mk_Tm_app _146_546 _146_545 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 710 "FStar.TypeChecker.Util.fst"
let x_eq_y_yret = (let _146_554 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _146_553 = (let _146_552 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_551 = (let _146_550 = (let _146_547 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _146_547))
in (let _146_549 = (let _146_548 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_146_548)::[])
in (_146_550)::_146_549))
in (_146_552)::_146_551))
in (FStar_Syntax_Syntax.mk_Tm_app _146_554 _146_553 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 711 "FStar.TypeChecker.Util.fst"
let forall_y_x_eq_y_yret = (let _146_564 = (FStar_TypeChecker_Env.inst_effect_fun_with (FStar_List.append us us) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _146_563 = (let _146_562 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_561 = (let _146_560 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_559 = (let _146_558 = (let _146_557 = (let _146_556 = (let _146_555 = (FStar_Syntax_Syntax.mk_binder y)
in (_146_555)::[])
in (FStar_Syntax_Util.abs _146_556 x_eq_y_yret None))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _146_557))
in (_146_558)::[])
in (_146_560)::_146_559))
in (_146_562)::_146_561))
in (FStar_Syntax_Syntax.mk_Tm_app _146_564 _146_563 None res_t.FStar_Syntax_Syntax.pos)))
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
let comp = (fun _62_935 -> (match (()) with
| () -> begin
(
# 718 "FStar.TypeChecker.Util.fst"
let _62_951 = (let _146_576 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _146_575 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _146_576 _146_575)))
in (match (_62_951) with
| ((md, _62_938, _62_940), (res_t, wp_then, wlp_then), (_62_947, wp_else, wlp_else)) -> begin
(
# 719 "FStar.TypeChecker.Util.fst"
let us = (let _146_577 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_146_577)::[])
in (
# 720 "FStar.TypeChecker.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _146_597 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _146_596 = (let _146_594 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_593 = (let _146_592 = (FStar_Syntax_Syntax.as_arg g)
in (let _146_591 = (let _146_590 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _146_589 = (let _146_588 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_146_588)::[])
in (_146_590)::_146_589))
in (_146_592)::_146_591))
in (_146_594)::_146_593))
in (let _146_595 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _146_597 _146_596 None _146_595)))))
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
let wp = (let _146_604 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _146_603 = (let _146_602 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_601 = (let _146_600 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _146_599 = (let _146_598 = (FStar_Syntax_Syntax.as_arg wp)
in (_146_598)::[])
in (_146_600)::_146_599))
in (_146_602)::_146_601))
in (FStar_Syntax_Syntax.mk_Tm_app _146_604 _146_603 None wp.FStar_Syntax_Syntax.pos)))
in (
# 727 "FStar.TypeChecker.Util.fst"
let wlp = (let _146_609 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _146_608 = (let _146_607 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_606 = (let _146_605 = (FStar_Syntax_Syntax.as_arg wlp)
in (_146_605)::[])
in (_146_607)::_146_606))
in (FStar_Syntax_Syntax.mk_Tm_app _146_609 _146_608 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end))))
end))
end))
in (let _146_610 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _146_610; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp})))

# 734 "FStar.TypeChecker.Util.fst"
let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (let _146_616 = (let _146_615 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid _146_615))
in (FStar_Syntax_Syntax.fvar _146_616 FStar_Syntax_Syntax.Delta_constant None)))

# 736 "FStar.TypeChecker.Util.fst"
let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (
# 737 "FStar.TypeChecker.Util.fst"
let eff = (FStar_List.fold_left (fun eff _62_973 -> (match (_62_973) with
| (_62_971, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (
# 738 "FStar.TypeChecker.Util.fst"
let bind_cases = (fun _62_976 -> (match (()) with
| () -> begin
(
# 739 "FStar.TypeChecker.Util.fst"
let us = (let _146_627 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_146_627)::[])
in (
# 740 "FStar.TypeChecker.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _146_647 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _146_646 = (let _146_644 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_643 = (let _146_642 = (FStar_Syntax_Syntax.as_arg g)
in (let _146_641 = (let _146_640 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _146_639 = (let _146_638 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_146_638)::[])
in (_146_640)::_146_639))
in (_146_642)::_146_641))
in (_146_644)::_146_643))
in (let _146_645 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _146_647 _146_646 None _146_645)))))
in (
# 742 "FStar.TypeChecker.Util.fst"
let default_case = (
# 743 "FStar.TypeChecker.Util.fst"
let post_k = (let _146_650 = (let _146_648 = (FStar_Syntax_Syntax.null_binder res_t)
in (_146_648)::[])
in (let _146_649 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _146_650 _146_649)))
in (
# 744 "FStar.TypeChecker.Util.fst"
let kwp = (let _146_653 = (let _146_651 = (FStar_Syntax_Syntax.null_binder post_k)
in (_146_651)::[])
in (let _146_652 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _146_653 _146_652)))
in (
# 745 "FStar.TypeChecker.Util.fst"
let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (
# 746 "FStar.TypeChecker.Util.fst"
let wp = (let _146_659 = (let _146_654 = (FStar_Syntax_Syntax.mk_binder post)
in (_146_654)::[])
in (let _146_658 = (let _146_657 = (let _146_655 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Errors.exhaustiveness_check _146_655))
in (let _146_656 = (fvar_const env FStar_Syntax_Const.false_lid)
in (FStar_All.pipe_left _146_657 _146_656)))
in (FStar_Syntax_Util.abs _146_659 _146_658 None)))
in (
# 747 "FStar.TypeChecker.Util.fst"
let wlp = (let _146_662 = (let _146_660 = (FStar_Syntax_Syntax.mk_binder post)
in (_146_660)::[])
in (let _146_661 = (fvar_const env FStar_Syntax_Const.true_lid)
in (FStar_Syntax_Util.abs _146_662 _146_661 None)))
in (
# 748 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (
# 750 "FStar.TypeChecker.Util.fst"
let comp = (FStar_List.fold_right (fun _62_993 celse -> (match (_62_993) with
| (g, cthen) -> begin
(
# 751 "FStar.TypeChecker.Util.fst"
let _62_1011 = (let _146_665 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _146_665 celse))
in (match (_62_1011) with
| ((md, _62_997, _62_999), (_62_1002, wp_then, wlp_then), (_62_1007, wp_else, wlp_else)) -> begin
(let _146_667 = (ifthenelse md res_t g wp_then wp_else)
in (let _146_666 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _146_667 _146_666 [])))
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
let _62_1019 = (destruct_comp comp)
in (match (_62_1019) with
| (_62_1016, wp, wlp) -> begin
(
# 758 "FStar.TypeChecker.Util.fst"
let wp = (let _146_674 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _146_673 = (let _146_672 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_671 = (let _146_670 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _146_669 = (let _146_668 = (FStar_Syntax_Syntax.as_arg wp)
in (_146_668)::[])
in (_146_670)::_146_669))
in (_146_672)::_146_671))
in (FStar_Syntax_Syntax.mk_Tm_app _146_674 _146_673 None wp.FStar_Syntax_Syntax.pos)))
in (
# 759 "FStar.TypeChecker.Util.fst"
let wlp = (let _146_679 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _146_678 = (let _146_677 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_676 = (let _146_675 = (FStar_Syntax_Syntax.as_arg wlp)
in (_146_675)::[])
in (_146_677)::_146_676))
in (FStar_Syntax_Syntax.mk_Tm_app _146_679 _146_678 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end))))
end))))
end))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))

# 766 "FStar.TypeChecker.Util.fst"
let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (
# 767 "FStar.TypeChecker.Util.fst"
let close = (fun _62_1026 -> (match (()) with
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
let bs = (let _146_700 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_700)::[])
in (
# 774 "FStar.TypeChecker.Util.fst"
let us = (let _146_702 = (let _146_701 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (_146_701)::[])
in (u_res)::_146_702)
in (
# 775 "FStar.TypeChecker.Util.fst"
let wp = (FStar_Syntax_Util.abs bs wp None)
in (let _146_709 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (let _146_708 = (let _146_707 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_706 = (let _146_705 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _146_704 = (let _146_703 = (FStar_Syntax_Syntax.as_arg wp)
in (_146_703)::[])
in (_146_705)::_146_704))
in (_146_707)::_146_706))
in (FStar_Syntax_Syntax.mk_Tm_app _146_709 _146_708 None wp0.FStar_Syntax_Syntax.pos))))))) bvs wp0))
in (
# 778 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 779 "FStar.TypeChecker.Util.fst"
let _62_1043 = (destruct_comp c)
in (match (_62_1043) with
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
let _62_1048 = lc
in {FStar_Syntax_Syntax.eff_name = _62_1048.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _62_1048.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _62_1048.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))

# 787 "FStar.TypeChecker.Util.fst"
let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (
# 788 "FStar.TypeChecker.Util.fst"
let refine = (fun _62_1054 -> (match (()) with
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
(let _146_720 = (let _146_719 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _146_718 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _146_719 _146_718)))
in (FStar_All.failwith _146_720))
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
let ret = (let _146_722 = (let _146_721 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _146_721 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_722))
in (
# 803 "FStar.TypeChecker.Util.fst"
let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (
# 804 "FStar.TypeChecker.Util.fst"
let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (
# 806 "FStar.TypeChecker.Util.fst"
let c = (let _146_724 = (let _146_723 = (bind env None (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), eq_ret))
in (_146_723.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _146_724 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
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
let _62_1066 = lc
in {FStar_Syntax_Syntax.eff_name = _62_1066.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _62_1066.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))

# 817 "FStar.TypeChecker.Util.fst"
let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (match ((FStar_TypeChecker_Rel.sub_comp env c c')) with
| None -> begin
(let _146_736 = (let _146_735 = (let _146_734 = (FStar_TypeChecker_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _146_733 = (FStar_TypeChecker_Env.get_range env)
in (_146_734, _146_733)))
in FStar_Syntax_Syntax.Error (_146_735))
in (Prims.raise _146_736))
end
| Some (g) -> begin
(e, c', g)
end))

# 823 "FStar.TypeChecker.Util.fst"
let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match ((let _146_745 = (FStar_Syntax_Subst.compress t)
in _146_745.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_62_1080) -> begin
(match ((let _146_746 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _146_746.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid) -> begin
(
# 828 "FStar.TypeChecker.Util.fst"
let _62_1084 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (
# 829 "FStar.TypeChecker.Util.fst"
let b2t = (let _146_747 = (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar _146_747 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (
# 830 "FStar.TypeChecker.Util.fst"
let lc = (let _146_750 = (let _146_749 = (let _146_748 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_748))
in (None, _146_749))
in (bind env (Some (e)) lc _146_750))
in (
# 831 "FStar.TypeChecker.Util.fst"
let e = (let _146_752 = (let _146_751 = (FStar_Syntax_Syntax.as_arg e)
in (_146_751)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _146_752 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (e, lc)))))
end
| _62_1090 -> begin
(e, lc)
end)
end
| _62_1092 -> begin
(e, lc)
end))

# 838 "FStar.TypeChecker.Util.fst"
let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (
# 839 "FStar.TypeChecker.Util.fst"
let gopt = if env.FStar_TypeChecker_Env.use_eq then begin
(let _146_761 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in (_146_761, false))
end else begin
(let _146_762 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in (_146_762, true))
end
in (match (gopt) with
| (None, _62_1100) -> begin
(FStar_TypeChecker_Rel.subtype_fail env lc.FStar_Syntax_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(match ((FStar_TypeChecker_Rel.guard_form g)) with
| FStar_TypeChecker_Common.Trivial -> begin
(
# 847 "FStar.TypeChecker.Util.fst"
let lc = (
# 847 "FStar.TypeChecker.Util.fst"
let _62_1107 = lc
in {FStar_Syntax_Syntax.eff_name = _62_1107.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _62_1107.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _62_1107.FStar_Syntax_Syntax.comp})
in (e, lc, g))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 851 "FStar.TypeChecker.Util.fst"
let g = (
# 851 "FStar.TypeChecker.Util.fst"
let _62_1112 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _62_1112.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _62_1112.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _62_1112.FStar_TypeChecker_Env.implicits})
in (
# 852 "FStar.TypeChecker.Util.fst"
let strengthen = (fun _62_1116 -> (match (()) with
| () -> begin
(
# 854 "FStar.TypeChecker.Util.fst"
let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (match ((let _146_765 = (FStar_Syntax_Subst.compress f)
in _146_765.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_62_1119, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _62_1125; FStar_Syntax_Syntax.pos = _62_1123; FStar_Syntax_Syntax.vars = _62_1121}, _62_1130) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
(
# 858 "FStar.TypeChecker.Util.fst"
let lc = (
# 858 "FStar.TypeChecker.Util.fst"
let _62_1133 = lc
in {FStar_Syntax_Syntax.eff_name = _62_1133.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _62_1133.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _62_1133.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| _62_1137 -> begin
(
# 862 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 863 "FStar.TypeChecker.Util.fst"
let _62_1139 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _146_769 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _146_768 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _146_767 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _146_766 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _146_769 _146_768 _146_767 _146_766)))))
end else begin
()
end
in (
# 870 "FStar.TypeChecker.Util.fst"
let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 871 "FStar.TypeChecker.Util.fst"
let _62_1144 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_62_1144) with
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
let us = (let _146_770 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_146_770)::[])
in (
# 877 "FStar.TypeChecker.Util.fst"
let wp = (let _146_775 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ret)
in (let _146_774 = (let _146_773 = (FStar_Syntax_Syntax.as_arg t)
in (let _146_772 = (let _146_771 = (FStar_Syntax_Syntax.as_arg xexp)
in (_146_771)::[])
in (_146_773)::_146_772))
in (FStar_Syntax_Syntax.mk_Tm_app _146_775 _146_774 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)))
in (
# 878 "FStar.TypeChecker.Util.fst"
let cret = (let _146_776 = (mk_comp md t wp wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_776))
in (
# 879 "FStar.TypeChecker.Util.fst"
let guard = if apply_guard then begin
(let _146_778 = (let _146_777 = (FStar_Syntax_Syntax.as_arg xexp)
in (_146_777)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _146_778 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end else begin
f
end
in (
# 880 "FStar.TypeChecker.Util.fst"
let _62_1155 = (let _146_786 = (FStar_All.pipe_left (fun _146_783 -> Some (_146_783)) (FStar_TypeChecker_Errors.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _146_785 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _146_784 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _146_786 _146_785 e cret _146_784))))
in (match (_62_1155) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(
# 884 "FStar.TypeChecker.Util.fst"
let x = (
# 884 "FStar.TypeChecker.Util.fst"
let _62_1156 = x
in {FStar_Syntax_Syntax.ppname = _62_1156.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _62_1156.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (
# 885 "FStar.TypeChecker.Util.fst"
let c = (let _146_788 = (let _146_787 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_787))
in (bind env (Some (e)) _146_788 (Some (x), eq_ret)))
in (
# 886 "FStar.TypeChecker.Util.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 887 "FStar.TypeChecker.Util.fst"
let _62_1161 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _146_789 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _146_789))
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
let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _62_3 -> (match (_62_3) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _62_1167 -> begin
[]
end))))
in (
# 891 "FStar.TypeChecker.Util.fst"
let lc = (
# 891 "FStar.TypeChecker.Util.fst"
let _62_1169 = lc
in (let _146_791 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _146_791; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (
# 892 "FStar.TypeChecker.Util.fst"
let g = (
# 892 "FStar.TypeChecker.Util.fst"
let _62_1172 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _62_1172.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _62_1172.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _62_1172.FStar_TypeChecker_Env.implicits})
in (e, lc, g))))))
end)
end)))

# 895 "FStar.TypeChecker.Util.fst"
let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (
# 896 "FStar.TypeChecker.Util.fst"
let mk_post_type = (fun res_t ens -> (
# 897 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _146_803 = (let _146_802 = (let _146_801 = (let _146_800 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _146_800))
in (_146_801)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _146_802 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _146_803))))
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
| (req, _62_1200)::(ens, _62_1195)::_62_1192 -> begin
(let _146_809 = (let _146_806 = (norm req)
in Some (_146_806))
in (let _146_808 = (let _146_807 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _146_807))
in (_146_809, _146_808)))
end
| _62_1204 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 913 "FStar.TypeChecker.Util.fst"
let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (wp, _62_1215)::(wlp, _62_1210)::_62_1207 -> begin
(
# 916 "FStar.TypeChecker.Util.fst"
let _62_1221 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (_62_1221) with
| (us_r, _62_1220) -> begin
(
# 917 "FStar.TypeChecker.Util.fst"
let _62_1225 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (_62_1225) with
| (us_e, _62_1224) -> begin
(
# 918 "FStar.TypeChecker.Util.fst"
let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (
# 919 "FStar.TypeChecker.Util.fst"
let as_req = (let _146_811 = (let _146_810 = (FStar_Ident.set_lid_range FStar_Syntax_Const.as_requires r)
in (FStar_Syntax_Syntax.fvar _146_810 FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _146_811 us_r))
in (
# 920 "FStar.TypeChecker.Util.fst"
let as_ens = (let _146_813 = (let _146_812 = (FStar_Ident.set_lid_range FStar_Syntax_Const.as_ensures r)
in (FStar_Syntax_Syntax.fvar _146_812 FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _146_813 us_e))
in (
# 921 "FStar.TypeChecker.Util.fst"
let req = (let _146_816 = (let _146_815 = (let _146_814 = (FStar_Syntax_Syntax.as_arg wp)
in (_146_814)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.imp_tag)))::_146_815)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _146_816 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 922 "FStar.TypeChecker.Util.fst"
let ens = (let _146_819 = (let _146_818 = (let _146_817 = (FStar_Syntax_Syntax.as_arg wlp)
in (_146_817)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.imp_tag)))::_146_818)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _146_819 None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _146_823 = (let _146_820 = (norm req)
in Some (_146_820))
in (let _146_822 = (let _146_821 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm _146_821))
in (_146_823, _146_822))))))))
end))
end))
end
| _62_1232 -> begin
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
let _62_1243 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_62_1243) with
| (bs, c) -> begin
(
# 939 "FStar.TypeChecker.Util.fst"
let rec aux = (fun subst _62_4 -> (match (_62_4) with
| (x, Some (FStar_Syntax_Syntax.Implicit (dot)))::rest -> begin
(
# 941 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 942 "FStar.TypeChecker.Util.fst"
let _62_1259 = (new_implicit_var env t)
in (match (_62_1259) with
| (v, _62_1257, g) -> begin
(
# 943 "FStar.TypeChecker.Util.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, v)))::subst
in (
# 944 "FStar.TypeChecker.Util.fst"
let _62_1265 = (aux subst rest)
in (match (_62_1265) with
| (args, bs, subst, g') -> begin
(let _146_834 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((v, Some (FStar_Syntax_Syntax.Implicit (dot))))::args, bs, subst, _146_834))
end)))
end)))
end
| bs -> begin
([], bs, subst, FStar_TypeChecker_Rel.trivial_guard)
end))
in (
# 948 "FStar.TypeChecker.Util.fst"
let _62_1271 = (aux [] bs)
in (match (_62_1271) with
| (args, bs, subst, guard) -> begin
(match ((args, bs)) with
| ([], _62_1274) -> begin
(e, torig, guard)
end
| (_62_1277, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end
| _62_1281 -> begin
(
# 959 "FStar.TypeChecker.Util.fst"
let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _62_1284 -> begin
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
| _62_1289 -> begin
(e, t, FStar_TypeChecker_Rel.trivial_guard)
end)
end))

# 973 "FStar.TypeChecker.Util.fst"
let gen_univs : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe_uvar Prims.list * (FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  Prims.bool))  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(
# 975 "FStar.TypeChecker.Util.fst"
let s = (let _146_846 = (let _146_845 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _146_845))
in (FStar_All.pipe_right _146_846 FStar_Util.set_elements))
in (
# 976 "FStar.TypeChecker.Util.fst"
let r = (let _146_847 = (FStar_TypeChecker_Env.get_range env)
in Some (_146_847))
in (
# 977 "FStar.TypeChecker.Util.fst"
let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (
# 978 "FStar.TypeChecker.Util.fst"
let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (
# 979 "FStar.TypeChecker.Util.fst"
let _62_1296 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _146_852 = (let _146_849 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _146_849))
in (let _146_851 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _146_850 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _146_852 _146_851 _146_850))))
end else begin
()
end
in (
# 981 "FStar.TypeChecker.Util.fst"
let _62_1298 = (FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))))
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
let _62_1306 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _146_861 = (let _146_860 = (let _146_859 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _146_859 (FStar_List.map (fun u -> (let _146_858 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _146_858 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _146_860 (FStar_String.concat ", ")))
in (FStar_Util.print1 "univs to gen : %s\n" _146_861))
end else begin
()
end
in (
# 992 "FStar.TypeChecker.Util.fst"
let gen = (gen_univs env univs)
in (
# 993 "FStar.TypeChecker.Util.fst"
let _62_1309 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _146_862 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _146_862))
end else begin
()
end
in (
# 995 "FStar.TypeChecker.Util.fst"
let ts = (FStar_Syntax_Subst.close_univ_vars gen t)
in (gen, ts))))))))

# 998 "FStar.TypeChecker.Util.fst"
let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> if (let _146_868 = (FStar_Util.for_all (fun _62_1317 -> (match (_62_1317) with
| (_62_1315, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _146_868)) then begin
None
end else begin
(
# 1002 "FStar.TypeChecker.Util.fst"
let norm = (fun c -> (
# 1003 "FStar.TypeChecker.Util.fst"
let _62_1320 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _146_871 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _146_871))
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
let _62_1323 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _146_872 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _146_872))
end else begin
()
end
in c))))
in (
# 1011 "FStar.TypeChecker.Util.fst"
let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (
# 1012 "FStar.TypeChecker.Util.fst"
let gen_uvars = (fun uvs -> (let _146_875 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _146_875 FStar_Util.set_elements)))
in (
# 1013 "FStar.TypeChecker.Util.fst"
let _62_1340 = (let _146_877 = (FStar_All.pipe_right ecs (FStar_List.map (fun _62_1330 -> (match (_62_1330) with
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
in (FStar_All.pipe_right _146_877 FStar_List.unzip))
in (match (_62_1340) with
| (univs, uvars) -> begin
(
# 1023 "FStar.TypeChecker.Util.fst"
let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (
# 1024 "FStar.TypeChecker.Util.fst"
let gen_univs = (gen_univs env univs)
in (
# 1025 "FStar.TypeChecker.Util.fst"
let _62_1344 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end else begin
()
end
in (
# 1027 "FStar.TypeChecker.Util.fst"
let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _62_1349 -> (match (_62_1349) with
| (uvs, e, c) -> begin
(
# 1028 "FStar.TypeChecker.Util.fst"
let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _62_1352 -> (match (_62_1352) with
| (u, k) -> begin
(match ((FStar_Unionfind.find u)) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(a, Some (FStar_Syntax_Syntax.imp_tag))
end
| FStar_Syntax_Syntax.Fixed (_62_1386) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _62_1389 -> begin
(
# 1034 "FStar.TypeChecker.Util.fst"
let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (
# 1035 "FStar.TypeChecker.Util.fst"
let _62_1393 = (FStar_Syntax_Util.arrow_formals k)
in (match (_62_1393) with
| (bs, kres) -> begin
(
# 1036 "FStar.TypeChecker.Util.fst"
let a = (let _146_883 = (let _146_882 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _146_881 -> Some (_146_881)) _146_882))
in (FStar_Syntax_Syntax.new_bv _146_883 kres))
in (
# 1037 "FStar.TypeChecker.Util.fst"
let t = (let _146_887 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _146_886 = (let _146_885 = (let _146_884 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _146_884))
in Some (_146_885))
in (FStar_Syntax_Util.abs bs _146_887 _146_886)))
in (
# 1038 "FStar.TypeChecker.Util.fst"
let _62_1396 = (FStar_Syntax_Util.set_uvar u t)
in (a, Some (FStar_Syntax_Syntax.imp_tag)))))
end)))
end)
end))))
in (
# 1042 "FStar.TypeChecker.Util.fst"
let _62_1420 = (match (tvars) with
| [] -> begin
(e, c)
end
| _62_1401 -> begin
(
# 1048 "FStar.TypeChecker.Util.fst"
let _62_1404 = (e, c)
in (match (_62_1404) with
| (e0, c0) -> begin
(
# 1049 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.BetaUVars)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::[]) env c)
in (
# 1050 "FStar.TypeChecker.Util.fst"
let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.BetaUVars)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::[]) env e)
in (
# 1052 "FStar.TypeChecker.Util.fst"
let t = (match ((let _146_888 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _146_888.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(
# 1054 "FStar.TypeChecker.Util.fst"
let _62_1413 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (_62_1413) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| _62_1415 -> begin
(FStar_Syntax_Util.arrow tvars c)
end)
in (
# 1059 "FStar.TypeChecker.Util.fst"
let e' = (FStar_Syntax_Util.abs tvars e None)
in (let _146_889 = (FStar_Syntax_Syntax.mk_Total t)
in (e', _146_889))))))
end))
end)
in (match (_62_1420) with
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
let _62_1430 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_896 = (let _146_895 = (FStar_List.map (fun _62_1429 -> (match (_62_1429) with
| (lb, _62_1426, _62_1428) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _146_895 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _146_896))
end else begin
()
end
in (match ((let _146_898 = (FStar_All.pipe_right lecs (FStar_List.map (fun _62_1436 -> (match (_62_1436) with
| (_62_1433, e, c) -> begin
(e, c)
end))))
in (gen env _146_898))) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun _62_1441 -> (match (_62_1441) with
| (l, t, c) -> begin
(l, [], t, c)
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _62_1449 _62_1453 -> (match ((_62_1449, _62_1453)) with
| ((l, _62_1446, _62_1448), (us, e, c)) -> begin
(
# 1072 "FStar.TypeChecker.Util.fst"
let _62_1454 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _146_904 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _146_903 = (FStar_Syntax_Print.lbname_to_string l)
in (let _146_902 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.print3 "(%s) Generalized %s to %s\n" _146_904 _146_903 _146_902))))
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
(let _146_920 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _146_919 -> Some (_146_919)) _146_920))
end)
end)
in (
# 1093 "FStar.TypeChecker.Util.fst"
let is_var = (fun e -> (match ((let _146_923 = (FStar_Syntax_Subst.compress e)
in _146_923.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (_62_1471) -> begin
true
end
| _62_1474 -> begin
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
let _62_1481 = x
in {FStar_Syntax_Syntax.ppname = _62_1481.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _62_1481.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| _62_1484 -> begin
(
# 1100 "FStar.TypeChecker.Util.fst"
let _62_1485 = e
in (let _146_928 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _62_1485.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _146_928; FStar_Syntax_Syntax.pos = _62_1485.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _62_1485.FStar_Syntax_Syntax.vars}))
end)))
in (
# 1101 "FStar.TypeChecker.Util.fst"
let env = (
# 1101 "FStar.TypeChecker.Util.fst"
let _62_1487 = env
in (let _146_929 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _62_1487.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _62_1487.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _62_1487.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _62_1487.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _62_1487.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _62_1487.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _62_1487.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _62_1487.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _62_1487.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _62_1487.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _62_1487.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _62_1487.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _62_1487.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _62_1487.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _62_1487.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _146_929; FStar_TypeChecker_Env.is_iface = _62_1487.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _62_1487.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _62_1487.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _62_1487.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _62_1487.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _62_1487.FStar_TypeChecker_Env.use_bv_sorts}))
in (match ((check env t1 t2)) with
| None -> begin
(let _146_933 = (let _146_932 = (let _146_931 = (FStar_TypeChecker_Errors.expected_expression_of_type env t2 e t1)
in (let _146_930 = (FStar_TypeChecker_Env.get_range env)
in (_146_931, _146_930)))
in FStar_Syntax_Syntax.Error (_146_932))
in (Prims.raise _146_933))
end
| Some (g) -> begin
(
# 1105 "FStar.TypeChecker.Util.fst"
let _62_1493 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _146_934 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _146_934))
end else begin
()
end
in (let _146_935 = (decorate e t2)
in (_146_935, g)))
end)))))))

# 1110 "FStar.TypeChecker.Util.fst"
let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (
# 1111 "FStar.TypeChecker.Util.fst"
let discharge = (fun g -> (
# 1112 "FStar.TypeChecker.Util.fst"
let _62_1500 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (
# 1114 "FStar.TypeChecker.Util.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _146_945 = (discharge g)
in (let _146_944 = (lc.FStar_Syntax_Syntax.comp ())
in (_146_945, _146_944)))
end else begin
(
# 1117 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 1118 "FStar.TypeChecker.Util.fst"
let steps = (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.DeltaComp)::[]
in (
# 1119 "FStar.TypeChecker.Util.fst"
let c = (let _146_946 = (FStar_TypeChecker_Normalize.normalize_comp steps env c)
in (FStar_All.pipe_right _146_946 FStar_Syntax_Util.comp_to_comp_typ))
in (
# 1120 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 1121 "FStar.TypeChecker.Util.fst"
let _62_1511 = (destruct_comp c)
in (match (_62_1511) with
| (t, wp, _62_1510) -> begin
(
# 1122 "FStar.TypeChecker.Util.fst"
let vc = (let _146_954 = (let _146_948 = (let _146_947 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_146_947)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _146_948 env md md.FStar_Syntax_Syntax.trivial))
in (let _146_953 = (let _146_951 = (FStar_Syntax_Syntax.as_arg t)
in (let _146_950 = (let _146_949 = (FStar_Syntax_Syntax.as_arg wp)
in (_146_949)::[])
in (_146_951)::_146_950))
in (let _146_952 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk_Tm_app _146_954 _146_953 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _146_952))))
in (
# 1123 "FStar.TypeChecker.Util.fst"
let _62_1513 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _146_955 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _146_955))
end else begin
()
end
in (
# 1125 "FStar.TypeChecker.Util.fst"
let g = (let _146_956 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _146_956))
in (let _146_958 = (discharge g)
in (let _146_957 = (FStar_Syntax_Syntax.mk_Comp c)
in (_146_958, _146_957))))))
end))))))
end)))

# 1131 "FStar.TypeChecker.Util.fst"
let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (
# 1132 "FStar.TypeChecker.Util.fst"
let short_bin_op = (fun f _62_5 -> (match (_62_5) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (fst, _62_1524)::[] -> begin
(f fst)
end
| _62_1528 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (
# 1137 "FStar.TypeChecker.Util.fst"
let op_and_e = (fun e -> (let _146_979 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _146_979 (fun _146_978 -> FStar_TypeChecker_Common.NonTrivial (_146_978)))))
in (
# 1138 "FStar.TypeChecker.Util.fst"
let op_or_e = (fun e -> (let _146_984 = (let _146_982 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _146_982))
in (FStar_All.pipe_right _146_984 (fun _146_983 -> FStar_TypeChecker_Common.NonTrivial (_146_983)))))
in (
# 1139 "FStar.TypeChecker.Util.fst"
let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _146_987 -> FStar_TypeChecker_Common.NonTrivial (_146_987))))
in (
# 1140 "FStar.TypeChecker.Util.fst"
let op_or_t = (fun t -> (let _146_991 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _146_991 (fun _146_990 -> FStar_TypeChecker_Common.NonTrivial (_146_990)))))
in (
# 1141 "FStar.TypeChecker.Util.fst"
let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _146_994 -> FStar_TypeChecker_Common.NonTrivial (_146_994))))
in (
# 1143 "FStar.TypeChecker.Util.fst"
let short_op_ite = (fun _62_6 -> (match (_62_6) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (guard, _62_1543)::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| _then::(guard, _62_1548)::[] -> begin
(let _146_998 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _146_998 (fun _146_997 -> FStar_TypeChecker_Common.NonTrivial (_146_997))))
end
| _62_1553 -> begin
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
in (match ((FStar_Util.find_map table (fun _62_1561 -> (match (_62_1561) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _146_1031 = (mk seen_args)
in Some (_146_1031))
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
| _62_1566 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))

# 1165 "FStar.TypeChecker.Util.fst"
let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (match ((let _146_1034 = (FStar_Syntax_Util.un_uinst l)
in _146_1034.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| _62_1571 -> begin
false
end))

# 1186 "FStar.TypeChecker.Util.fst"
let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (
# 1187 "FStar.TypeChecker.Util.fst"
let pos = (fun bs -> (match (bs) with
| (hd, _62_1580)::_62_1577 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| _62_1584 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| (_62_1588, Some (FStar_Syntax_Syntax.Implicit (_62_1590)))::_62_1586 -> begin
bs
end
| _62_1596 -> begin
(match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
bs
end
| Some (t) -> begin
(match ((let _146_1041 = (FStar_Syntax_Subst.compress t)
in _146_1041.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', _62_1602) -> begin
(match ((FStar_Util.prefix_until (fun _62_7 -> (match (_62_7) with
| (_62_1607, Some (FStar_Syntax_Syntax.Implicit (_62_1609))) -> begin
false
end
| _62_1614 -> begin
true
end)) bs')) with
| None -> begin
bs
end
| Some ([], _62_1618, _62_1620) -> begin
bs
end
| Some (imps, _62_1625, _62_1627) -> begin
if (FStar_All.pipe_right imps (FStar_Util.for_all (fun _62_1633 -> (match (_62_1633) with
| (x, _62_1632) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end)))) then begin
(
# 1203 "FStar.TypeChecker.Util.fst"
let r = (pos bs)
in (
# 1204 "FStar.TypeChecker.Util.fst"
let imps = (FStar_All.pipe_right imps (FStar_List.map (fun _62_1637 -> (match (_62_1637) with
| (x, i) -> begin
(let _146_1045 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in (_146_1045, i))
end))))
in (FStar_List.append imps bs)))
end else begin
bs
end
end)
end
| _62_1640 -> begin
bs
end)
end)
end)))




