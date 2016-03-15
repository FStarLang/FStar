
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
in if ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2)) then begin
Some ((c2, "both total"))
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2)) then begin
(let _146_345 = (let _146_344 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in (_146_344, "both gtot"))
in Some (_146_345))
end else begin
(match ((e1opt, b)) with
| (Some (e), Some (x)) -> begin
if ((FStar_Syntax_Util.is_total_comp c1) && (not ((FStar_Syntax_Syntax.is_null_bv x)))) then begin
(let _146_347 = (let _146_346 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT ((x, e)))::[]) c2)
in (_146_346, "substituted e"))
in Some (_146_347))
end else begin
(aux ())
end
end
| _62_749 -> begin
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
# 568 "FStar.TypeChecker.Util.fst"
let _62_767 = (lift_and_destruct env c1 c2)
in (match (_62_767) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(
# 569 "FStar.TypeChecker.Util.fst"
let bs = (match (b) with
| None -> begin
(let _146_348 = (FStar_Syntax_Syntax.null_binder t1)
in (_146_348)::[])
end
| Some (x) -> begin
(let _146_349 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_349)::[])
end)
in (
# 572 "FStar.TypeChecker.Util.fst"
let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp None))
in (
# 573 "FStar.TypeChecker.Util.fst"
let wp_args = (let _146_364 = (FStar_Syntax_Syntax.as_arg t1)
in (let _146_363 = (let _146_362 = (FStar_Syntax_Syntax.as_arg t2)
in (let _146_361 = (let _146_360 = (FStar_Syntax_Syntax.as_arg wp1)
in (let _146_359 = (let _146_358 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _146_357 = (let _146_356 = (let _146_352 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg _146_352))
in (let _146_355 = (let _146_354 = (let _146_353 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _146_353))
in (_146_354)::[])
in (_146_356)::_146_355))
in (_146_358)::_146_357))
in (_146_360)::_146_359))
in (_146_362)::_146_361))
in (_146_364)::_146_363))
in (
# 574 "FStar.TypeChecker.Util.fst"
let wlp_args = (let _146_372 = (FStar_Syntax_Syntax.as_arg t1)
in (let _146_371 = (let _146_370 = (FStar_Syntax_Syntax.as_arg t2)
in (let _146_369 = (let _146_368 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _146_367 = (let _146_366 = (let _146_365 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _146_365))
in (_146_366)::[])
in (_146_368)::_146_367))
in (_146_370)::_146_369))
in (_146_372)::_146_371))
in (
# 575 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t2)))::[]) kwp)
in (
# 576 "FStar.TypeChecker.Util.fst"
let us = (let _146_375 = (env.FStar_TypeChecker_Env.universe_of env t1)
in (let _146_374 = (let _146_373 = (env.FStar_TypeChecker_Env.universe_of env t2)
in (_146_373)::[])
in (_146_375)::_146_374))
in (
# 577 "FStar.TypeChecker.Util.fst"
let wp = (let _146_376 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _146_376 wp_args None t2.FStar_Syntax_Syntax.pos))
in (
# 578 "FStar.TypeChecker.Util.fst"
let wlp = (let _146_377 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wlp)
in (FStar_Syntax_Syntax.mk_Tm_app _146_377 wlp_args None t2.FStar_Syntax_Syntax.pos))
in (
# 579 "FStar.TypeChecker.Util.fst"
let c = (mk_comp md t2 wp wlp [])
in c)))))))))
end))
end)))))
end))
in (let _146_378 = (join_lcomp env lc1 lc2)
in {FStar_Syntax_Syntax.eff_name = _146_378; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it})))
end))

# 586 "FStar.TypeChecker.Util.fst"
let lift_formula : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t mk_wp mk_wlp f -> (
# 587 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 588 "FStar.TypeChecker.Util.fst"
let _62_789 = (FStar_TypeChecker_Env.wp_signature env md_pure.FStar_Syntax_Syntax.mname)
in (match (_62_789) with
| (a, kwp) -> begin
(
# 589 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 590 "FStar.TypeChecker.Util.fst"
let wp = (let _146_392 = (let _146_391 = (FStar_Syntax_Syntax.as_arg t)
in (let _146_390 = (let _146_389 = (FStar_Syntax_Syntax.as_arg f)
in (_146_389)::[])
in (_146_391)::_146_390))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wp _146_392 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (
# 591 "FStar.TypeChecker.Util.fst"
let wlp = (let _146_396 = (let _146_395 = (FStar_Syntax_Syntax.as_arg t)
in (let _146_394 = (let _146_393 = (FStar_Syntax_Syntax.as_arg f)
in (_146_393)::[])
in (_146_395)::_146_394))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wlp _146_396 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (mk_comp md_pure FStar_TypeChecker_Common.t_unit wp wlp []))))
end))))

# 594 "FStar.TypeChecker.Util.fst"
let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((f, FStar_Syntax_Syntax.Meta_labeled ((reason, r, false))))) None f.FStar_Syntax_Syntax.pos))

# 597 "FStar.TypeChecker.Util.fst"
let label_opt : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _146_420 = (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)
in (FStar_All.pipe_left Prims.op_Negation _146_420)) then begin
f
end else begin
(let _146_421 = (reason ())
in (label _146_421 r f))
end
end))

# 604 "FStar.TypeChecker.Util.fst"
let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 606 "FStar.TypeChecker.Util.fst"
let _62_809 = g
in (let _146_429 = (let _146_428 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_146_428))
in {FStar_TypeChecker_Env.guard_f = _146_429; FStar_TypeChecker_Env.deferred = _62_809.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _62_809.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _62_809.FStar_TypeChecker_Env.implicits}))
end))

# 608 "FStar.TypeChecker.Util.fst"
let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(
# 610 "FStar.TypeChecker.Util.fst"
let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| _62_820 -> begin
g2
end))

# 614 "FStar.TypeChecker.Util.fst"
let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (
# 615 "FStar.TypeChecker.Util.fst"
let weaken = (fun _62_825 -> (match (()) with
| () -> begin
(
# 616 "FStar.TypeChecker.Util.fst"
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
# 622 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 623 "FStar.TypeChecker.Util.fst"
let _62_834 = (destruct_comp c)
in (match (_62_834) with
| (res_t, wp, wlp) -> begin
(
# 624 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 625 "FStar.TypeChecker.Util.fst"
let us = (let _146_442 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_146_442)::[])
in (
# 626 "FStar.TypeChecker.Util.fst"
let wp = (let _146_449 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _146_448 = (let _146_447 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_446 = (let _146_445 = (FStar_Syntax_Syntax.as_arg f)
in (let _146_444 = (let _146_443 = (FStar_Syntax_Syntax.as_arg wp)
in (_146_443)::[])
in (_146_445)::_146_444))
in (_146_447)::_146_446))
in (FStar_Syntax_Syntax.mk_Tm_app _146_449 _146_448 None wp.FStar_Syntax_Syntax.pos)))
in (
# 627 "FStar.TypeChecker.Util.fst"
let wlp = (let _146_456 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _146_455 = (let _146_454 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_453 = (let _146_452 = (FStar_Syntax_Syntax.as_arg f)
in (let _146_451 = (let _146_450 = (FStar_Syntax_Syntax.as_arg wlp)
in (_146_450)::[])
in (_146_452)::_146_451))
in (_146_454)::_146_453))
in (FStar_Syntax_Syntax.mk_Tm_app _146_456 _146_455 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp c.FStar_Syntax_Syntax.flags)))))
end)))
end
end))
end))
in (
# 629 "FStar.TypeChecker.Util.fst"
let _62_839 = lc
in {FStar_Syntax_Syntax.eff_name = _62_839.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _62_839.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _62_839.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))

# 631 "FStar.TypeChecker.Util.fst"
let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> if (FStar_TypeChecker_Rel.is_trivial g0) then begin
(lc, g0)
end else begin
(
# 635 "FStar.TypeChecker.Util.fst"
let _62_846 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _146_476 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _146_475 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _146_476 _146_475)))
end else begin
()
end
in (
# 639 "FStar.TypeChecker.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _62_2 -> (match (_62_2) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _62_852 -> begin
[]
end))))
in (
# 640 "FStar.TypeChecker.Util.fst"
let strengthen = (fun _62_855 -> (match (()) with
| () -> begin
(
# 641 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 642 "FStar.TypeChecker.Util.fst"
let g0 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (match ((FStar_TypeChecker_Rel.guard_form g0)) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 646 "FStar.TypeChecker.Util.fst"
let c = if ((FStar_Syntax_Util.is_pure_or_ghost_comp c) && (not ((FStar_Syntax_Util.is_partial_return c)))) then begin
(
# 649 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.gen_bv "strengthen_pre_x" None (FStar_Syntax_Util.comp_result c))
in (
# 650 "FStar.TypeChecker.Util.fst"
let xret = (let _146_481 = (let _146_480 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _146_480))
in (FStar_Syntax_Util.comp_set_flags _146_481 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (
# 651 "FStar.TypeChecker.Util.fst"
let lc = (bind env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), (FStar_Syntax_Util.lcomp_of_comp xret)))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (
# 655 "FStar.TypeChecker.Util.fst"
let _62_865 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _146_483 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _146_482 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _146_483 _146_482)))
end else begin
()
end
in (
# 660 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 661 "FStar.TypeChecker.Util.fst"
let _62_871 = (destruct_comp c)
in (match (_62_871) with
| (res_t, wp, wlp) -> begin
(
# 662 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 663 "FStar.TypeChecker.Util.fst"
let us = (let _146_484 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_146_484)::[])
in (
# 664 "FStar.TypeChecker.Util.fst"
let wp = (let _146_493 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assert_p)
in (let _146_492 = (let _146_491 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_490 = (let _146_489 = (let _146_486 = (let _146_485 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason _146_485 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _146_486))
in (let _146_488 = (let _146_487 = (FStar_Syntax_Syntax.as_arg wp)
in (_146_487)::[])
in (_146_489)::_146_488))
in (_146_491)::_146_490))
in (FStar_Syntax_Syntax.mk_Tm_app _146_493 _146_492 None wp.FStar_Syntax_Syntax.pos)))
in (
# 665 "FStar.TypeChecker.Util.fst"
let wlp = (let _146_500 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _146_499 = (let _146_498 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_497 = (let _146_496 = (FStar_Syntax_Syntax.as_arg f)
in (let _146_495 = (let _146_494 = (FStar_Syntax_Syntax.as_arg wlp)
in (_146_494)::[])
in (_146_496)::_146_495))
in (_146_498)::_146_497))
in (FStar_Syntax_Syntax.mk_Tm_app _146_500 _146_499 None wlp.FStar_Syntax_Syntax.pos)))
in (
# 667 "FStar.TypeChecker.Util.fst"
let _62_876 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _146_501 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _146_501))
end else begin
()
end
in (
# 671 "FStar.TypeChecker.Util.fst"
let c2 = (mk_comp md res_t wp wlp flags)
in c2))))))
end)))))
end)))
end))
in (let _146_505 = (
# 673 "FStar.TypeChecker.Util.fst"
let _62_879 = lc
in (let _146_504 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _146_503 = if ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _146_502 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _146_502))) then begin
flags
end else begin
[]
end
in {FStar_Syntax_Syntax.eff_name = _146_504; FStar_Syntax_Syntax.res_typ = _62_879.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _146_503; FStar_Syntax_Syntax.comp = strengthen})))
in (_146_505, (
# 676 "FStar.TypeChecker.Util.fst"
let _62_881 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _62_881.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _62_881.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _62_881.FStar_TypeChecker_Env.implicits}))))))
end)

# 678 "FStar.TypeChecker.Util.fst"
let record_application_site : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (
# 679 "FStar.TypeChecker.Util.fst"
let comp = (fun _62_887 -> (match (()) with
| () -> begin
(
# 680 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 681 "FStar.TypeChecker.Util.fst"
let res_t = (FStar_Syntax_Util.comp_result c)
in if (((FStar_Syntax_Util.is_trivial_wp c) || (let _146_514 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals _146_514 FStar_Syntax_Const.prims_lid))) || (FStar_Syntax_Syntax.is_teff res_t)) then begin
c
end else begin
(
# 686 "FStar.TypeChecker.Util.fst"
let g = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (FStar_TypeChecker_Common.t_unit)))
in (
# 687 "FStar.TypeChecker.Util.fst"
let _62_895 = (strengthen_precondition (Some ((fun _62_891 -> (match (()) with
| () -> begin
"push"
end)))) env e (FStar_Syntax_Util.lcomp_of_comp c) g)
in (match (_62_895) with
| (c, _62_894) -> begin
(
# 688 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 689 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 690 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 691 "FStar.TypeChecker.Util.fst"
let us = (let _146_518 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_146_518)::[])
in (
# 692 "FStar.TypeChecker.Util.fst"
let xret = (let _146_523 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _146_522 = (let _146_521 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_520 = (let _146_519 = (FStar_Syntax_Syntax.as_arg xexp)
in (_146_519)::[])
in (_146_521)::_146_520))
in (FStar_Syntax_Syntax.mk_Tm_app _146_523 _146_522 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 693 "FStar.TypeChecker.Util.fst"
let xret_comp = (let _146_524 = (mk_comp md_pure res_t xret xret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_524))
in (
# 694 "FStar.TypeChecker.Util.fst"
let lc = (let _146_530 = (let _146_529 = (let _146_528 = (strengthen_precondition (Some ((fun _62_902 -> (match (()) with
| () -> begin
"pop"
end)))) env xexp xret_comp g)
in (FStar_All.pipe_left Prims.fst _146_528))
in (Some (x), _146_529))
in (bind env None c _146_530))
in (lc.FStar_Syntax_Syntax.comp ()))))))))
end)))
end))
end))
in (
# 696 "FStar.TypeChecker.Util.fst"
let _62_904 = lc
in {FStar_Syntax_Syntax.eff_name = _62_904.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _62_904.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _62_904.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = comp})))

# 698 "FStar.TypeChecker.Util.fst"
let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env comp res_t -> (
# 699 "FStar.TypeChecker.Util.fst"
let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (
# 700 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 701 "FStar.TypeChecker.Util.fst"
let y = (FStar_Syntax_Syntax.new_bv None res_t)
in (
# 702 "FStar.TypeChecker.Util.fst"
let _62_914 = (let _146_538 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _146_537 = (FStar_Syntax_Syntax.bv_to_name y)
in (_146_538, _146_537)))
in (match (_62_914) with
| (xexp, yexp) -> begin
(
# 703 "FStar.TypeChecker.Util.fst"
let us = (let _146_539 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_146_539)::[])
in (
# 704 "FStar.TypeChecker.Util.fst"
let yret = (let _146_544 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _146_543 = (let _146_542 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_541 = (let _146_540 = (FStar_Syntax_Syntax.as_arg yexp)
in (_146_540)::[])
in (_146_542)::_146_541))
in (FStar_Syntax_Syntax.mk_Tm_app _146_544 _146_543 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 705 "FStar.TypeChecker.Util.fst"
let x_eq_y_yret = (let _146_552 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _146_551 = (let _146_550 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_549 = (let _146_548 = (let _146_545 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _146_545))
in (let _146_547 = (let _146_546 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_146_546)::[])
in (_146_548)::_146_547))
in (_146_550)::_146_549))
in (FStar_Syntax_Syntax.mk_Tm_app _146_552 _146_551 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 706 "FStar.TypeChecker.Util.fst"
let forall_y_x_eq_y_yret = (let _146_562 = (FStar_TypeChecker_Env.inst_effect_fun_with (FStar_List.append us us) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _146_561 = (let _146_560 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_559 = (let _146_558 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_557 = (let _146_556 = (let _146_555 = (let _146_554 = (let _146_553 = (FStar_Syntax_Syntax.mk_binder y)
in (_146_553)::[])
in (FStar_Syntax_Util.abs _146_554 x_eq_y_yret None))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _146_555))
in (_146_556)::[])
in (_146_558)::_146_557))
in (_146_560)::_146_559))
in (FStar_Syntax_Syntax.mk_Tm_app _146_562 _146_561 None res_t.FStar_Syntax_Syntax.pos)))
in (
# 707 "FStar.TypeChecker.Util.fst"
let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (
# 708 "FStar.TypeChecker.Util.fst"
let lc = (bind env None (FStar_Syntax_Util.lcomp_of_comp comp) (Some (x), (FStar_Syntax_Util.lcomp_of_comp lc2)))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))

# 711 "FStar.TypeChecker.Util.fst"
let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (
# 712 "FStar.TypeChecker.Util.fst"
let comp = (fun _62_926 -> (match (()) with
| () -> begin
(
# 713 "FStar.TypeChecker.Util.fst"
let _62_942 = (let _146_574 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _146_573 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _146_574 _146_573)))
in (match (_62_942) with
| ((md, _62_929, _62_931), (res_t, wp_then, wlp_then), (_62_938, wp_else, wlp_else)) -> begin
(
# 714 "FStar.TypeChecker.Util.fst"
let us = (let _146_575 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_146_575)::[])
in (
# 715 "FStar.TypeChecker.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _146_595 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _146_594 = (let _146_592 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_591 = (let _146_590 = (FStar_Syntax_Syntax.as_arg g)
in (let _146_589 = (let _146_588 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _146_587 = (let _146_586 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_146_586)::[])
in (_146_588)::_146_587))
in (_146_590)::_146_589))
in (_146_592)::_146_591))
in (let _146_593 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _146_595 _146_594 None _146_593)))))
in (
# 716 "FStar.TypeChecker.Util.fst"
let wp = (ifthenelse md res_t guard wp_then wp_else)
in (
# 717 "FStar.TypeChecker.Util.fst"
let wlp = (ifthenelse md res_t guard wlp_then wlp_else)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(
# 719 "FStar.TypeChecker.Util.fst"
let comp = (mk_comp md res_t wp wlp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(
# 721 "FStar.TypeChecker.Util.fst"
let wp = (let _146_602 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _146_601 = (let _146_600 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_599 = (let _146_598 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _146_597 = (let _146_596 = (FStar_Syntax_Syntax.as_arg wp)
in (_146_596)::[])
in (_146_598)::_146_597))
in (_146_600)::_146_599))
in (FStar_Syntax_Syntax.mk_Tm_app _146_602 _146_601 None wp.FStar_Syntax_Syntax.pos)))
in (
# 722 "FStar.TypeChecker.Util.fst"
let wlp = (let _146_607 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _146_606 = (let _146_605 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_604 = (let _146_603 = (FStar_Syntax_Syntax.as_arg wlp)
in (_146_603)::[])
in (_146_605)::_146_604))
in (FStar_Syntax_Syntax.mk_Tm_app _146_607 _146_606 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end))))
end))
end))
in (let _146_608 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _146_608; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp})))

# 729 "FStar.TypeChecker.Util.fst"
let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (let _146_614 = (let _146_613 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid _146_613))
in (FStar_Syntax_Syntax.fvar _146_614 FStar_Syntax_Syntax.Delta_constant None)))

# 731 "FStar.TypeChecker.Util.fst"
let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (
# 732 "FStar.TypeChecker.Util.fst"
let eff = (FStar_List.fold_left (fun eff _62_964 -> (match (_62_964) with
| (_62_962, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (
# 733 "FStar.TypeChecker.Util.fst"
let bind_cases = (fun _62_967 -> (match (()) with
| () -> begin
(
# 734 "FStar.TypeChecker.Util.fst"
let us = (let _146_625 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_146_625)::[])
in (
# 735 "FStar.TypeChecker.Util.fst"
let ifthenelse = (fun md res_t g wp_t wp_e -> (let _146_645 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _146_644 = (let _146_642 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_641 = (let _146_640 = (FStar_Syntax_Syntax.as_arg g)
in (let _146_639 = (let _146_638 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _146_637 = (let _146_636 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_146_636)::[])
in (_146_638)::_146_637))
in (_146_640)::_146_639))
in (_146_642)::_146_641))
in (let _146_643 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _146_645 _146_644 None _146_643)))))
in (
# 737 "FStar.TypeChecker.Util.fst"
let default_case = (
# 738 "FStar.TypeChecker.Util.fst"
let post_k = (let _146_648 = (let _146_646 = (FStar_Syntax_Syntax.null_binder res_t)
in (_146_646)::[])
in (let _146_647 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _146_648 _146_647)))
in (
# 739 "FStar.TypeChecker.Util.fst"
let kwp = (let _146_651 = (let _146_649 = (FStar_Syntax_Syntax.null_binder post_k)
in (_146_649)::[])
in (let _146_650 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _146_651 _146_650)))
in (
# 740 "FStar.TypeChecker.Util.fst"
let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (
# 741 "FStar.TypeChecker.Util.fst"
let wp = (let _146_657 = (let _146_652 = (FStar_Syntax_Syntax.mk_binder post)
in (_146_652)::[])
in (let _146_656 = (let _146_655 = (let _146_653 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Errors.exhaustiveness_check _146_653))
in (let _146_654 = (fvar_const env FStar_Syntax_Const.false_lid)
in (FStar_All.pipe_left _146_655 _146_654)))
in (FStar_Syntax_Util.abs _146_657 _146_656 None)))
in (
# 742 "FStar.TypeChecker.Util.fst"
let wlp = (let _146_660 = (let _146_658 = (FStar_Syntax_Syntax.mk_binder post)
in (_146_658)::[])
in (let _146_659 = (fvar_const env FStar_Syntax_Const.true_lid)
in (FStar_Syntax_Util.abs _146_660 _146_659 None)))
in (
# 743 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (
# 745 "FStar.TypeChecker.Util.fst"
let comp = (FStar_List.fold_right (fun _62_984 celse -> (match (_62_984) with
| (g, cthen) -> begin
(
# 746 "FStar.TypeChecker.Util.fst"
let _62_1002 = (let _146_663 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _146_663 celse))
in (match (_62_1002) with
| ((md, _62_988, _62_990), (_62_993, wp_then, wlp_then), (_62_998, wp_else, wlp_else)) -> begin
(let _146_665 = (ifthenelse md res_t g wp_then wp_else)
in (let _146_664 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _146_665 _146_664 [])))
end))
end)) lcases default_case)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(add_equality_to_post_condition env comp res_t)
end else begin
(
# 750 "FStar.TypeChecker.Util.fst"
let comp = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (
# 751 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env comp.FStar_Syntax_Syntax.effect_name)
in (
# 752 "FStar.TypeChecker.Util.fst"
let _62_1010 = (destruct_comp comp)
in (match (_62_1010) with
| (_62_1007, wp, wlp) -> begin
(
# 753 "FStar.TypeChecker.Util.fst"
let wp = (let _146_672 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _146_671 = (let _146_670 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_669 = (let _146_668 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _146_667 = (let _146_666 = (FStar_Syntax_Syntax.as_arg wp)
in (_146_666)::[])
in (_146_668)::_146_667))
in (_146_670)::_146_669))
in (FStar_Syntax_Syntax.mk_Tm_app _146_672 _146_671 None wp.FStar_Syntax_Syntax.pos)))
in (
# 754 "FStar.TypeChecker.Util.fst"
let wlp = (let _146_677 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _146_676 = (let _146_675 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_674 = (let _146_673 = (FStar_Syntax_Syntax.as_arg wlp)
in (_146_673)::[])
in (_146_675)::_146_674))
in (FStar_Syntax_Syntax.mk_Tm_app _146_677 _146_676 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end))))
end))))
end))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))

# 761 "FStar.TypeChecker.Util.fst"
let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (
# 762 "FStar.TypeChecker.Util.fst"
let close = (fun _62_1017 -> (match (()) with
| () -> begin
(
# 763 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in if (FStar_Syntax_Util.is_ml_comp c) then begin
c
end else begin
(
# 766 "FStar.TypeChecker.Util.fst"
let close_wp = (fun u_res md res_t bvs wp0 -> (FStar_List.fold_right (fun x wp -> (
# 768 "FStar.TypeChecker.Util.fst"
let bs = (let _146_698 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_698)::[])
in (
# 769 "FStar.TypeChecker.Util.fst"
let us = (let _146_700 = (let _146_699 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (_146_699)::[])
in (u_res)::_146_700)
in (
# 770 "FStar.TypeChecker.Util.fst"
let wp = (FStar_Syntax_Util.abs bs wp None)
in (let _146_707 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (let _146_706 = (let _146_705 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_704 = (let _146_703 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _146_702 = (let _146_701 = (FStar_Syntax_Syntax.as_arg wp)
in (_146_701)::[])
in (_146_703)::_146_702))
in (_146_705)::_146_704))
in (FStar_Syntax_Syntax.mk_Tm_app _146_707 _146_706 None wp0.FStar_Syntax_Syntax.pos))))))) bvs wp0))
in (
# 773 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 774 "FStar.TypeChecker.Util.fst"
let _62_1034 = (destruct_comp c)
in (match (_62_1034) with
| (t, wp, wlp) -> begin
(
# 775 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 776 "FStar.TypeChecker.Util.fst"
let u_res = (env.FStar_TypeChecker_Env.universe_of env c.FStar_Syntax_Syntax.result_typ)
in (
# 777 "FStar.TypeChecker.Util.fst"
let wp = (close_wp u_res md c.FStar_Syntax_Syntax.result_typ bvs wp)
in (
# 778 "FStar.TypeChecker.Util.fst"
let wlp = (close_wp u_res md c.FStar_Syntax_Syntax.result_typ bvs wlp)
in (mk_comp md c.FStar_Syntax_Syntax.result_typ wp wlp c.FStar_Syntax_Syntax.flags)))))
end))))
end)
end))
in (
# 780 "FStar.TypeChecker.Util.fst"
let _62_1039 = lc
in {FStar_Syntax_Syntax.eff_name = _62_1039.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _62_1039.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _62_1039.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))

# 782 "FStar.TypeChecker.Util.fst"
let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (
# 783 "FStar.TypeChecker.Util.fst"
let refine = (fun _62_1045 -> (match (()) with
| () -> begin
(
# 784 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in if (not ((is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name))) then begin
c
end else begin
if (FStar_Syntax_Util.is_partial_return c) then begin
c
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c) && (not ((FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)))) then begin
(let _146_718 = (let _146_717 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _146_716 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _146_717 _146_716)))
in (FStar_All.failwith _146_718))
end else begin
(
# 792 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 793 "FStar.TypeChecker.Util.fst"
let t = c.FStar_Syntax_Syntax.result_typ
in (
# 794 "FStar.TypeChecker.Util.fst"
let c = (FStar_Syntax_Syntax.mk_Comp c)
in (
# 795 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (
# 796 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 797 "FStar.TypeChecker.Util.fst"
let ret = (let _146_720 = (let _146_719 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _146_719 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_720))
in (
# 798 "FStar.TypeChecker.Util.fst"
let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (
# 799 "FStar.TypeChecker.Util.fst"
let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (
# 801 "FStar.TypeChecker.Util.fst"
let c = (let _146_722 = (let _146_721 = (bind env None (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), eq_ret))
in (_146_721.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _146_722 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
in c)))))))))
end
end
end)
end))
in (
# 804 "FStar.TypeChecker.Util.fst"
let flags = if (((not ((FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)) && (not ((FStar_Syntax_Util.is_lcomp_partial_return lc)))) then begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_Syntax_Syntax.cflags
end else begin
lc.FStar_Syntax_Syntax.cflags
end
in (
# 810 "FStar.TypeChecker.Util.fst"
let _62_1057 = lc
in {FStar_Syntax_Syntax.eff_name = _62_1057.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _62_1057.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))

# 812 "FStar.TypeChecker.Util.fst"
let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (match ((FStar_TypeChecker_Rel.sub_comp env c c')) with
| None -> begin
(let _146_734 = (let _146_733 = (let _146_732 = (FStar_TypeChecker_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _146_731 = (FStar_TypeChecker_Env.get_range env)
in (_146_732, _146_731)))
in FStar_Syntax_Syntax.Error (_146_733))
in (Prims.raise _146_734))
end
| Some (g) -> begin
(e, c', g)
end))

# 818 "FStar.TypeChecker.Util.fst"
let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match ((let _146_743 = (FStar_Syntax_Subst.compress t)
in _146_743.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_62_1071) -> begin
(match ((let _146_744 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _146_744.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid) -> begin
(
# 823 "FStar.TypeChecker.Util.fst"
let _62_1075 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (
# 824 "FStar.TypeChecker.Util.fst"
let b2t = (let _146_745 = (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar _146_745 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (
# 825 "FStar.TypeChecker.Util.fst"
let lc = (let _146_748 = (let _146_747 = (let _146_746 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_746))
in (None, _146_747))
in (bind env (Some (e)) lc _146_748))
in (
# 826 "FStar.TypeChecker.Util.fst"
let e = (let _146_750 = (let _146_749 = (FStar_Syntax_Syntax.as_arg e)
in (_146_749)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _146_750 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (e, lc)))))
end
| _62_1081 -> begin
(e, lc)
end)
end
| _62_1083 -> begin
(e, lc)
end))

# 833 "FStar.TypeChecker.Util.fst"
let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (
# 834 "FStar.TypeChecker.Util.fst"
let gopt = if env.FStar_TypeChecker_Env.use_eq then begin
(let _146_759 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in (_146_759, false))
end else begin
(let _146_760 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in (_146_760, true))
end
in (match (gopt) with
| (None, _62_1091) -> begin
(FStar_TypeChecker_Rel.subtype_fail env lc.FStar_Syntax_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(match ((FStar_TypeChecker_Rel.guard_form g)) with
| FStar_TypeChecker_Common.Trivial -> begin
(
# 842 "FStar.TypeChecker.Util.fst"
let lc = (
# 842 "FStar.TypeChecker.Util.fst"
let _62_1098 = lc
in {FStar_Syntax_Syntax.eff_name = _62_1098.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _62_1098.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _62_1098.FStar_Syntax_Syntax.comp})
in (e, lc, g))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 846 "FStar.TypeChecker.Util.fst"
let g = (
# 846 "FStar.TypeChecker.Util.fst"
let _62_1103 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _62_1103.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _62_1103.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _62_1103.FStar_TypeChecker_Env.implicits})
in (
# 847 "FStar.TypeChecker.Util.fst"
let strengthen = (fun _62_1107 -> (match (()) with
| () -> begin
(
# 849 "FStar.TypeChecker.Util.fst"
let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (match ((let _146_763 = (FStar_Syntax_Subst.compress f)
in _146_763.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_62_1110, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _62_1116; FStar_Syntax_Syntax.pos = _62_1114; FStar_Syntax_Syntax.vars = _62_1112}, _62_1121) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
(
# 853 "FStar.TypeChecker.Util.fst"
let lc = (
# 853 "FStar.TypeChecker.Util.fst"
let _62_1124 = lc
in {FStar_Syntax_Syntax.eff_name = _62_1124.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _62_1124.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _62_1124.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| _62_1128 -> begin
(
# 857 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 858 "FStar.TypeChecker.Util.fst"
let _62_1130 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _146_767 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _146_766 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _146_765 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _146_764 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _146_767 _146_766 _146_765 _146_764)))))
end else begin
()
end
in (
# 865 "FStar.TypeChecker.Util.fst"
let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (
# 866 "FStar.TypeChecker.Util.fst"
let _62_1135 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_62_1135) with
| (a, kwp) -> begin
(
# 867 "FStar.TypeChecker.Util.fst"
let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (
# 868 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env ct.FStar_Syntax_Syntax.effect_name)
in (
# 869 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (
# 870 "FStar.TypeChecker.Util.fst"
let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (
# 871 "FStar.TypeChecker.Util.fst"
let us = (let _146_768 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_146_768)::[])
in (
# 872 "FStar.TypeChecker.Util.fst"
let wp = (let _146_773 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ret)
in (let _146_772 = (let _146_771 = (FStar_Syntax_Syntax.as_arg t)
in (let _146_770 = (let _146_769 = (FStar_Syntax_Syntax.as_arg xexp)
in (_146_769)::[])
in (_146_771)::_146_770))
in (FStar_Syntax_Syntax.mk_Tm_app _146_773 _146_772 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)))
in (
# 873 "FStar.TypeChecker.Util.fst"
let cret = (let _146_774 = (mk_comp md t wp wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_774))
in (
# 874 "FStar.TypeChecker.Util.fst"
let guard = if apply_guard then begin
(let _146_776 = (let _146_775 = (FStar_Syntax_Syntax.as_arg xexp)
in (_146_775)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _146_776 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end else begin
f
end
in (
# 875 "FStar.TypeChecker.Util.fst"
let _62_1146 = (let _146_784 = (FStar_All.pipe_left (fun _146_781 -> Some (_146_781)) (FStar_TypeChecker_Errors.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _146_783 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _146_782 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _146_784 _146_783 e cret _146_782))))
in (match (_62_1146) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(
# 879 "FStar.TypeChecker.Util.fst"
let x = (
# 879 "FStar.TypeChecker.Util.fst"
let _62_1147 = x
in {FStar_Syntax_Syntax.ppname = _62_1147.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _62_1147.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (
# 880 "FStar.TypeChecker.Util.fst"
let c = (let _146_786 = (let _146_785 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_785))
in (bind env (Some (e)) _146_786 (Some (x), eq_ret)))
in (
# 881 "FStar.TypeChecker.Util.fst"
let c = (c.FStar_Syntax_Syntax.comp ())
in (
# 882 "FStar.TypeChecker.Util.fst"
let _62_1152 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _146_787 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _146_787))
end else begin
()
end
in c))))
end))))))))))
end)))))
end))
end))
in (
# 885 "FStar.TypeChecker.Util.fst"
let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _62_3 -> (match (_62_3) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _62_1158 -> begin
[]
end))))
in (
# 886 "FStar.TypeChecker.Util.fst"
let lc = (
# 886 "FStar.TypeChecker.Util.fst"
let _62_1160 = lc
in (let _146_789 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _146_789; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (
# 887 "FStar.TypeChecker.Util.fst"
let g = (
# 887 "FStar.TypeChecker.Util.fst"
let _62_1163 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _62_1163.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _62_1163.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _62_1163.FStar_TypeChecker_Env.implicits})
in (e, lc, g))))))
end)
end)))

# 890 "FStar.TypeChecker.Util.fst"
let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (
# 891 "FStar.TypeChecker.Util.fst"
let mk_post_type = (fun res_t ens -> (
# 892 "FStar.TypeChecker.Util.fst"
let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _146_801 = (let _146_800 = (let _146_799 = (let _146_798 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _146_798))
in (_146_799)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _146_800 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _146_801))))
in (
# 894 "FStar.TypeChecker.Util.fst"
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
| (req, _62_1191)::(ens, _62_1186)::_62_1183 -> begin
(let _146_807 = (let _146_804 = (norm req)
in Some (_146_804))
in (let _146_806 = (let _146_805 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _146_805))
in (_146_807, _146_806)))
end
| _62_1195 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 908 "FStar.TypeChecker.Util.fst"
let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (wp, _62_1206)::(wlp, _62_1201)::_62_1198 -> begin
(
# 911 "FStar.TypeChecker.Util.fst"
let _62_1212 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (_62_1212) with
| (us_r, _62_1211) -> begin
(
# 912 "FStar.TypeChecker.Util.fst"
let _62_1216 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (_62_1216) with
| (us_e, _62_1215) -> begin
(
# 913 "FStar.TypeChecker.Util.fst"
let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (
# 914 "FStar.TypeChecker.Util.fst"
let as_req = (let _146_809 = (let _146_808 = (FStar_Ident.set_lid_range FStar_Syntax_Const.as_requires r)
in (FStar_Syntax_Syntax.fvar _146_808 FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _146_809 us_r))
in (
# 915 "FStar.TypeChecker.Util.fst"
let as_ens = (let _146_811 = (let _146_810 = (FStar_Ident.set_lid_range FStar_Syntax_Const.as_ensures r)
in (FStar_Syntax_Syntax.fvar _146_810 FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _146_811 us_e))
in (
# 916 "FStar.TypeChecker.Util.fst"
let req = (let _146_814 = (let _146_813 = (let _146_812 = (FStar_Syntax_Syntax.as_arg wp)
in (_146_812)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.imp_tag)))::_146_813)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _146_814 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (
# 917 "FStar.TypeChecker.Util.fst"
let ens = (let _146_817 = (let _146_816 = (let _146_815 = (FStar_Syntax_Syntax.as_arg wlp)
in (_146_815)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.imp_tag)))::_146_816)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _146_817 None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _146_821 = (let _146_818 = (norm req)
in Some (_146_818))
in (let _146_820 = (let _146_819 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm _146_819))
in (_146_821, _146_820))))))))
end))
end))
end
| _62_1223 -> begin
(FStar_All.failwith "Impossible")
end))
end
end)
end)))

# 927 "FStar.TypeChecker.Util.fst"
let maybe_instantiate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (
# 928 "FStar.TypeChecker.Util.fst"
let torig = (FStar_Syntax_Subst.compress t)
in if (not (env.FStar_TypeChecker_Env.instantiate_imp)) then begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end else begin
(match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 933 "FStar.TypeChecker.Util.fst"
let _62_1234 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_62_1234) with
| (bs, c) -> begin
(
# 934 "FStar.TypeChecker.Util.fst"
let rec aux = (fun subst _62_4 -> (match (_62_4) with
| (x, Some (FStar_Syntax_Syntax.Implicit (dot)))::rest -> begin
(
# 936 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (
# 937 "FStar.TypeChecker.Util.fst"
let _62_1250 = (new_implicit_var env t)
in (match (_62_1250) with
| (v, _62_1248, g) -> begin
(
# 938 "FStar.TypeChecker.Util.fst"
let subst = (FStar_Syntax_Syntax.NT ((x, v)))::subst
in (
# 939 "FStar.TypeChecker.Util.fst"
let _62_1256 = (aux subst rest)
in (match (_62_1256) with
| (args, bs, subst, g') -> begin
(let _146_832 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((v, Some (FStar_Syntax_Syntax.Implicit (dot))))::args, bs, subst, _146_832))
end)))
end)))
end
| bs -> begin
([], bs, subst, FStar_TypeChecker_Rel.trivial_guard)
end))
in (
# 943 "FStar.TypeChecker.Util.fst"
let _62_1262 = (aux [] bs)
in (match (_62_1262) with
| (args, bs, subst, guard) -> begin
(match ((args, bs)) with
| ([], _62_1265) -> begin
(e, torig, guard)
end
| (_62_1268, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end
| _62_1272 -> begin
(
# 954 "FStar.TypeChecker.Util.fst"
let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _62_1275 -> begin
(FStar_Syntax_Util.arrow bs c)
end)
in (
# 957 "FStar.TypeChecker.Util.fst"
let t = (FStar_Syntax_Subst.subst subst t)
in (
# 958 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Syntax.mk_Tm_app e args (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (e, t, guard))))
end)
end)))
end))
end
| _62_1280 -> begin
(e, t, FStar_TypeChecker_Rel.trivial_guard)
end)
end))

# 968 "FStar.TypeChecker.Util.fst"
let gen_univs : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe_uvar Prims.list * (FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  Prims.bool))  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(
# 970 "FStar.TypeChecker.Util.fst"
let s = (let _146_844 = (let _146_843 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _146_843))
in (FStar_All.pipe_right _146_844 FStar_Util.set_elements))
in (
# 971 "FStar.TypeChecker.Util.fst"
let r = (let _146_845 = (FStar_TypeChecker_Env.get_range env)
in Some (_146_845))
in (
# 972 "FStar.TypeChecker.Util.fst"
let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (
# 973 "FStar.TypeChecker.Util.fst"
let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (
# 974 "FStar.TypeChecker.Util.fst"
let _62_1287 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _146_850 = (let _146_847 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _146_847))
in (let _146_849 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _146_848 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _146_850 _146_849 _146_848))))
end else begin
()
end
in (
# 976 "FStar.TypeChecker.Util.fst"
let _62_1289 = (FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))))
in u_name))))))
in u_names)))
end)

# 980 "FStar.TypeChecker.Util.fst"
let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t -> (
# 981 "FStar.TypeChecker.Util.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (
# 982 "FStar.TypeChecker.Util.fst"
let univs = (FStar_Syntax_Free.univs t)
in (
# 983 "FStar.TypeChecker.Util.fst"
let _62_1297 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _146_859 = (let _146_858 = (let _146_857 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _146_857 (FStar_List.map (fun u -> (let _146_856 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _146_856 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _146_858 (FStar_String.concat ", ")))
in (FStar_Util.print1 "univs to gen : %s\n" _146_859))
end else begin
()
end
in (
# 987 "FStar.TypeChecker.Util.fst"
let gen = (gen_univs env univs)
in (
# 988 "FStar.TypeChecker.Util.fst"
let _62_1300 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _146_860 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _146_860))
end else begin
()
end
in (
# 990 "FStar.TypeChecker.Util.fst"
let ts = (FStar_Syntax_Subst.close_univ_vars gen t)
in (gen, ts))))))))

# 993 "FStar.TypeChecker.Util.fst"
let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> if (let _146_866 = (FStar_Util.for_all (fun _62_1308 -> (match (_62_1308) with
| (_62_1306, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _146_866)) then begin
None
end else begin
(
# 997 "FStar.TypeChecker.Util.fst"
let norm = (fun c -> (
# 998 "FStar.TypeChecker.Util.fst"
let _62_1311 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _146_869 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _146_869))
end else begin
()
end
in (
# 1000 "FStar.TypeChecker.Util.fst"
let c = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.Eta)::[]) env c)
end else begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env c)
end
in (
# 1003 "FStar.TypeChecker.Util.fst"
let _62_1314 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _146_870 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _146_870))
end else begin
()
end
in c))))
in (
# 1006 "FStar.TypeChecker.Util.fst"
let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (
# 1007 "FStar.TypeChecker.Util.fst"
let gen_uvars = (fun uvs -> (let _146_873 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _146_873 FStar_Util.set_elements)))
in (
# 1008 "FStar.TypeChecker.Util.fst"
let _62_1331 = (let _146_875 = (FStar_All.pipe_right ecs (FStar_List.map (fun _62_1321 -> (match (_62_1321) with
| (e, c) -> begin
(
# 1009 "FStar.TypeChecker.Util.fst"
let t = (FStar_All.pipe_right (FStar_Syntax_Util.comp_result c) FStar_Syntax_Subst.compress)
in (
# 1010 "FStar.TypeChecker.Util.fst"
let c = (norm c)
in (
# 1011 "FStar.TypeChecker.Util.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (
# 1012 "FStar.TypeChecker.Util.fst"
let t = ct.FStar_Syntax_Syntax.result_typ
in (
# 1013 "FStar.TypeChecker.Util.fst"
let univs = (FStar_Syntax_Free.univs t)
in (
# 1014 "FStar.TypeChecker.Util.fst"
let uvt = (FStar_Syntax_Free.uvars t)
in (
# 1015 "FStar.TypeChecker.Util.fst"
let uvs = (gen_uvars uvt)
in (univs, (uvs, e, c)))))))))
end))))
in (FStar_All.pipe_right _146_875 FStar_List.unzip))
in (match (_62_1331) with
| (univs, uvars) -> begin
(
# 1018 "FStar.TypeChecker.Util.fst"
let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (
# 1019 "FStar.TypeChecker.Util.fst"
let gen_univs = (gen_univs env univs)
in (
# 1020 "FStar.TypeChecker.Util.fst"
let _62_1335 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end else begin
()
end
in (
# 1022 "FStar.TypeChecker.Util.fst"
let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _62_1340 -> (match (_62_1340) with
| (uvs, e, c) -> begin
(
# 1023 "FStar.TypeChecker.Util.fst"
let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _62_1343 -> (match (_62_1343) with
| (u, k) -> begin
(match ((FStar_Unionfind.find u)) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(a, Some (FStar_Syntax_Syntax.imp_tag))
end
| FStar_Syntax_Syntax.Fixed (_62_1377) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _62_1380 -> begin
(
# 1029 "FStar.TypeChecker.Util.fst"
let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (
# 1030 "FStar.TypeChecker.Util.fst"
let _62_1384 = (FStar_Syntax_Util.arrow_formals k)
in (match (_62_1384) with
| (bs, kres) -> begin
(
# 1031 "FStar.TypeChecker.Util.fst"
let a = (let _146_881 = (let _146_880 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _146_879 -> Some (_146_879)) _146_880))
in (FStar_Syntax_Syntax.new_bv _146_881 kres))
in (
# 1032 "FStar.TypeChecker.Util.fst"
let t = (let _146_885 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _146_884 = (let _146_883 = (let _146_882 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _146_882))
in Some (_146_883))
in (FStar_Syntax_Util.abs bs _146_885 _146_884)))
in (
# 1033 "FStar.TypeChecker.Util.fst"
let _62_1387 = (FStar_Syntax_Util.set_uvar u t)
in (a, Some (FStar_Syntax_Syntax.imp_tag)))))
end)))
end)
end))))
in (
# 1037 "FStar.TypeChecker.Util.fst"
let _62_1411 = (match (tvars) with
| [] -> begin
(e, c)
end
| _62_1392 -> begin
(
# 1043 "FStar.TypeChecker.Util.fst"
let _62_1395 = (e, c)
in (match (_62_1395) with
| (e0, c0) -> begin
(
# 1044 "FStar.TypeChecker.Util.fst"
let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.BetaUVars)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::[]) env c)
in (
# 1045 "FStar.TypeChecker.Util.fst"
let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.BetaUVars)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::[]) env e)
in (
# 1047 "FStar.TypeChecker.Util.fst"
let t = (match ((let _146_886 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _146_886.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(
# 1049 "FStar.TypeChecker.Util.fst"
let _62_1404 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (_62_1404) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| _62_1406 -> begin
(FStar_Syntax_Util.arrow tvars c)
end)
in (
# 1054 "FStar.TypeChecker.Util.fst"
let e' = (FStar_Syntax_Util.abs tvars e None)
in (let _146_887 = (FStar_Syntax_Syntax.mk_Total t)
in (e', _146_887))))))
end))
end)
in (match (_62_1411) with
| (e, c) -> begin
(gen_univs, e, c)
end)))
end))))
in Some (ecs)))))
end)))))
end)

# 1059 "FStar.TypeChecker.Util.fst"
let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> (
# 1060 "FStar.TypeChecker.Util.fst"
let _62_1421 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_894 = (let _146_893 = (FStar_List.map (fun _62_1420 -> (match (_62_1420) with
| (lb, _62_1417, _62_1419) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _146_893 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _146_894))
end else begin
()
end
in (match ((let _146_896 = (FStar_All.pipe_right lecs (FStar_List.map (fun _62_1427 -> (match (_62_1427) with
| (_62_1424, e, c) -> begin
(e, c)
end))))
in (gen env _146_896))) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun _62_1432 -> (match (_62_1432) with
| (l, t, c) -> begin
(l, [], t, c)
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _62_1440 _62_1444 -> (match ((_62_1440, _62_1444)) with
| ((l, _62_1437, _62_1439), (us, e, c)) -> begin
(
# 1067 "FStar.TypeChecker.Util.fst"
let _62_1445 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _146_902 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _146_901 = (FStar_Syntax_Print.lbname_to_string l)
in (let _146_900 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.print3 "(%s) Generalized %s to %s\n" _146_902 _146_901 _146_900))))
end else begin
()
end
in (l, us, e, c))
end)) lecs ecs)
end)))

# 1080 "FStar.TypeChecker.Util.fst"
let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (
# 1081 "FStar.TypeChecker.Util.fst"
let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (
# 1082 "FStar.TypeChecker.Util.fst"
let check = (fun env t1 t2 -> if env.FStar_TypeChecker_Env.use_eq then begin
(FStar_TypeChecker_Rel.try_teq env t1 t2)
end else begin
(match ((FStar_TypeChecker_Rel.try_subtype env t1 t2)) with
| None -> begin
None
end
| Some (f) -> begin
(let _146_918 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _146_917 -> Some (_146_917)) _146_918))
end)
end)
in (
# 1088 "FStar.TypeChecker.Util.fst"
let is_var = (fun e -> (match ((let _146_921 = (FStar_Syntax_Subst.compress e)
in _146_921.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (_62_1462) -> begin
true
end
| _62_1465 -> begin
false
end))
in (
# 1091 "FStar.TypeChecker.Util.fst"
let decorate = (fun e t -> (
# 1092 "FStar.TypeChecker.Util.fst"
let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((
# 1094 "FStar.TypeChecker.Util.fst"
let _62_1472 = x
in {FStar_Syntax_Syntax.ppname = _62_1472.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _62_1472.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| _62_1475 -> begin
(
# 1095 "FStar.TypeChecker.Util.fst"
let _62_1476 = e
in (let _146_926 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _62_1476.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _146_926; FStar_Syntax_Syntax.pos = _62_1476.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _62_1476.FStar_Syntax_Syntax.vars}))
end)))
in (
# 1096 "FStar.TypeChecker.Util.fst"
let env = (
# 1096 "FStar.TypeChecker.Util.fst"
let _62_1478 = env
in (let _146_927 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _62_1478.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _62_1478.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _62_1478.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _62_1478.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _62_1478.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _62_1478.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _62_1478.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _62_1478.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _62_1478.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _62_1478.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _62_1478.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _62_1478.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _62_1478.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _62_1478.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _62_1478.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _146_927; FStar_TypeChecker_Env.is_iface = _62_1478.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _62_1478.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _62_1478.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _62_1478.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _62_1478.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _62_1478.FStar_TypeChecker_Env.use_bv_sorts}))
in (match ((check env t1 t2)) with
| None -> begin
(let _146_931 = (let _146_930 = (let _146_929 = (FStar_TypeChecker_Errors.expected_expression_of_type env t2 e t1)
in (let _146_928 = (FStar_TypeChecker_Env.get_range env)
in (_146_929, _146_928)))
in FStar_Syntax_Syntax.Error (_146_930))
in (Prims.raise _146_931))
end
| Some (g) -> begin
(
# 1100 "FStar.TypeChecker.Util.fst"
let _62_1484 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _146_932 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _146_932))
end else begin
()
end
in (let _146_933 = (decorate e t2)
in (_146_933, g)))
end)))))))

# 1105 "FStar.TypeChecker.Util.fst"
let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (
# 1106 "FStar.TypeChecker.Util.fst"
let discharge = (fun g -> (
# 1107 "FStar.TypeChecker.Util.fst"
let _62_1491 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (
# 1109 "FStar.TypeChecker.Util.fst"
let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _146_943 = (discharge g)
in (let _146_942 = (lc.FStar_Syntax_Syntax.comp ())
in (_146_943, _146_942)))
end else begin
(
# 1112 "FStar.TypeChecker.Util.fst"
let c = (lc.FStar_Syntax_Syntax.comp ())
in (
# 1113 "FStar.TypeChecker.Util.fst"
let steps = (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.DeltaComp)::[]
in (
# 1114 "FStar.TypeChecker.Util.fst"
let c = (let _146_944 = (FStar_TypeChecker_Normalize.normalize_comp steps env c)
in (FStar_All.pipe_right _146_944 FStar_Syntax_Util.comp_to_comp_typ))
in (
# 1115 "FStar.TypeChecker.Util.fst"
let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (
# 1116 "FStar.TypeChecker.Util.fst"
let _62_1502 = (destruct_comp c)
in (match (_62_1502) with
| (t, wp, _62_1501) -> begin
(
# 1117 "FStar.TypeChecker.Util.fst"
let vc = (let _146_952 = (let _146_946 = (let _146_945 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_146_945)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _146_946 env md md.FStar_Syntax_Syntax.trivial))
in (let _146_951 = (let _146_949 = (FStar_Syntax_Syntax.as_arg t)
in (let _146_948 = (let _146_947 = (FStar_Syntax_Syntax.as_arg wp)
in (_146_947)::[])
in (_146_949)::_146_948))
in (let _146_950 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk_Tm_app _146_952 _146_951 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _146_950))))
in (
# 1118 "FStar.TypeChecker.Util.fst"
let _62_1504 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _146_953 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _146_953))
end else begin
()
end
in (
# 1120 "FStar.TypeChecker.Util.fst"
let g = (let _146_954 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _146_954))
in (let _146_956 = (discharge g)
in (let _146_955 = (FStar_Syntax_Syntax.mk_Comp c)
in (_146_956, _146_955))))))
end))))))
end)))

# 1126 "FStar.TypeChecker.Util.fst"
let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (
# 1127 "FStar.TypeChecker.Util.fst"
let short_bin_op = (fun f _62_5 -> (match (_62_5) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (fst, _62_1515)::[] -> begin
(f fst)
end
| _62_1519 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (
# 1132 "FStar.TypeChecker.Util.fst"
let op_and_e = (fun e -> (let _146_977 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _146_977 (fun _146_976 -> FStar_TypeChecker_Common.NonTrivial (_146_976)))))
in (
# 1133 "FStar.TypeChecker.Util.fst"
let op_or_e = (fun e -> (let _146_982 = (let _146_980 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _146_980))
in (FStar_All.pipe_right _146_982 (fun _146_981 -> FStar_TypeChecker_Common.NonTrivial (_146_981)))))
in (
# 1134 "FStar.TypeChecker.Util.fst"
let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _146_985 -> FStar_TypeChecker_Common.NonTrivial (_146_985))))
in (
# 1135 "FStar.TypeChecker.Util.fst"
let op_or_t = (fun t -> (let _146_989 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _146_989 (fun _146_988 -> FStar_TypeChecker_Common.NonTrivial (_146_988)))))
in (
# 1136 "FStar.TypeChecker.Util.fst"
let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _146_992 -> FStar_TypeChecker_Common.NonTrivial (_146_992))))
in (
# 1138 "FStar.TypeChecker.Util.fst"
let short_op_ite = (fun _62_6 -> (match (_62_6) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (guard, _62_1534)::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| _then::(guard, _62_1539)::[] -> begin
(let _146_996 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _146_996 (fun _146_995 -> FStar_TypeChecker_Common.NonTrivial (_146_995))))
end
| _62_1544 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (
# 1143 "FStar.TypeChecker.Util.fst"
let table = ((FStar_Syntax_Const.op_And, (short_bin_op op_and_e)))::((FStar_Syntax_Const.op_Or, (short_bin_op op_or_e)))::((FStar_Syntax_Const.and_lid, (short_bin_op op_and_t)))::((FStar_Syntax_Const.or_lid, (short_bin_op op_or_t)))::((FStar_Syntax_Const.imp_lid, (short_bin_op op_imp_t)))::((FStar_Syntax_Const.ite_lid, short_op_ite))::[]
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(
# 1153 "FStar.TypeChecker.Util.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((FStar_Util.find_map table (fun _62_1552 -> (match (_62_1552) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _146_1029 = (mk seen_args)
in Some (_146_1029))
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
| _62_1557 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))

# 1160 "FStar.TypeChecker.Util.fst"
let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (match ((let _146_1032 = (FStar_Syntax_Util.un_uinst l)
in _146_1032.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| _62_1562 -> begin
false
end))

# 1181 "FStar.TypeChecker.Util.fst"
let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (
# 1182 "FStar.TypeChecker.Util.fst"
let pos = (fun bs -> (match (bs) with
| (hd, _62_1571)::_62_1568 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| _62_1575 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| (_62_1579, Some (FStar_Syntax_Syntax.Implicit (_62_1581)))::_62_1577 -> begin
bs
end
| _62_1587 -> begin
(match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
bs
end
| Some (t) -> begin
(match ((let _146_1039 = (FStar_Syntax_Subst.compress t)
in _146_1039.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', _62_1593) -> begin
(match ((FStar_Util.prefix_until (fun _62_7 -> (match (_62_7) with
| (_62_1598, Some (FStar_Syntax_Syntax.Implicit (_62_1600))) -> begin
false
end
| _62_1605 -> begin
true
end)) bs')) with
| None -> begin
bs
end
| Some ([], _62_1609, _62_1611) -> begin
bs
end
| Some (imps, _62_1616, _62_1618) -> begin
if (FStar_All.pipe_right imps (FStar_Util.for_all (fun _62_1624 -> (match (_62_1624) with
| (x, _62_1623) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end)))) then begin
(
# 1198 "FStar.TypeChecker.Util.fst"
let r = (pos bs)
in (
# 1199 "FStar.TypeChecker.Util.fst"
let imps = (FStar_All.pipe_right imps (FStar_List.map (fun _62_1628 -> (match (_62_1628) with
| (x, i) -> begin
(let _146_1043 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in (_146_1043, i))
end))))
in (FStar_List.append imps bs)))
end else begin
bs
end
end)
end
| _62_1631 -> begin
bs
end)
end)
end)))




