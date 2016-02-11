
open Prims
# 38 "util.fs"

let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _194_5 = (FStar_TypeChecker_Errors.failed_to_prove_specification errs)
in (FStar_TypeChecker_Errors.report (FStar_TypeChecker_Env.get_range env) _194_5)))

# 45 "util.fs"

let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _194_8 = (FStar_Syntax_Subst.compress t)
in _194_8.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_92_14) -> begin
true
end
| _92_17 -> begin
false
end))

# 49 "util.fs"

let t_binders : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env -> (let _194_12 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right _194_12 (FStar_List.filter (fun _92_22 -> (match (_92_22) with
| (x, _92_21) -> begin
(is_type x.FStar_Syntax_Syntax.sort)
end))))))

# 53 "util.fs"

let new_uvar_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun env k -> (let bs = if (FStar_ST.read FStar_Options.full_context_dependency) then begin
(FStar_TypeChecker_Env.all_binders env)
end else begin
(t_binders env)
end
in (FStar_TypeChecker_Rel.new_uvar (FStar_TypeChecker_Env.get_range env) bs k)))

# 59 "util.fs"

let new_uvar : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun env k -> (let _194_21 = (new_uvar_aux env k)
in (Prims.fst _194_21)))

# 61 "util.fs"

let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun _92_1 -> (match (_92_1) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, _92_37); FStar_Syntax_Syntax.tk = _92_34; FStar_Syntax_Syntax.pos = _92_32; FStar_Syntax_Syntax.vars = _92_30} -> begin
uv
end
| _92_42 -> begin
(FStar_All.failwith "Impossible")
end))

# 65 "util.fs"

let new_implicit_var : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.uvar * FStar_Range.range) * FStar_TypeChecker_Env.guard_t) = (fun env k -> (let _92_47 = (new_uvar_aux env k)
in (match (_92_47) with
| (t, u) -> begin
(let g = (let _92_48 = FStar_TypeChecker_Rel.trivial_guard
in (let _194_30 = (let _194_29 = (let _194_28 = (as_uvar u)
in (env, _194_28, t, k, u.FStar_Syntax_Syntax.pos))
in (_194_29)::[])
in {FStar_TypeChecker_Env.guard_f = _92_48.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _92_48.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _92_48.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _194_30}))
in (let _194_32 = (let _194_31 = (as_uvar u)
in (_194_31, u.FStar_Syntax_Syntax.pos))
in (t, _194_32, g)))
end)))

# 70 "util.fs"

let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun r t -> (let uvs = (FStar_Syntax_Free.uvars t)
in if (not ((FStar_Util.set_is_empty uvs))) then begin
(let us = (let _194_39 = (let _194_38 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun _92_57 -> (match (_92_57) with
| (x, _92_56) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) _194_38))
in (FStar_All.pipe_right _194_39 (FStar_String.concat ", ")))
in (let hide_uvar_nums_saved = (FStar_ST.read FStar_Options.hide_uvar_nums)
in (let print_implicits_saved = (FStar_ST.read FStar_Options.print_implicits)
in (let _92_61 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums false)
in (let _92_63 = (FStar_ST.op_Colon_Equals FStar_Options.print_implicits true)
in (let _92_65 = (let _194_41 = (let _194_40 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us _194_40))
in (FStar_TypeChecker_Errors.report r _194_41))
in (let _92_67 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums hide_uvar_nums_saved)
in (FStar_ST.op_Colon_Equals FStar_Options.print_implicits print_implicits_saved))))))))
end else begin
()
end))

# 90 "util.fs"

let force_sort' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' = (fun s -> (match ((FStar_ST.read s.FStar_Syntax_Syntax.tk)) with
| None -> begin
(let _194_46 = (let _194_45 = (FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos)
in (let _194_44 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s" _194_45 _194_44)))
in (FStar_All.failwith _194_46))
end
| Some (tk) -> begin
tk
end))

# 94 "util.fs"

let force_sort = (fun s -> (let _194_48 = (force_sort' s)
in (FStar_Syntax_Syntax.mk _194_48 None s.FStar_Syntax_Syntax.pos)))

# 96 "util.fs"

let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env _92_82 -> (match (_92_82) with
| {FStar_Syntax_Syntax.lbname = _92_81; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _92_77; FStar_Syntax_Syntax.lbdef = e} -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _92_84 = if (univ_vars <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (let r = (FStar_TypeChecker_Env.get_range env)
in (let mk_binder = (fun scope a -> (match (a.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _92_94 = (FStar_Syntax_Util.type_u ())
in (match (_92_94) with
| (k, _92_93) -> begin
(let t = (let _194_57 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right _194_57 Prims.fst))
in ((let _92_96 = a
in {FStar_Syntax_Syntax.ppname = _92_96.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _92_96.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), false))
end))
end
| _92_99 -> begin
(a, true)
end))
in (let rec aux = (fun vars e -> (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, _92_105) -> begin
(aux vars e)
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _92_111) -> begin
(t, true)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _92_117) -> begin
(let _92_136 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _92_123 _92_126 -> (match ((_92_123, _92_126)) with
| ((scope, bs, check), (a, imp)) -> begin
(let _92_129 = (mk_binder scope a)
in (match (_92_129) with
| (tb, c) -> begin
(let b = (tb, imp)
in (let bs = (FStar_List.append bs ((b)::[]))
in (let scope = (FStar_List.append scope ((b)::[]))
in (scope, bs, (c || check)))))
end))
end)) (vars, [], false)))
in (match (_92_136) with
| (scope, bs, check) -> begin
(let _92_139 = (aux scope body)
in (match (_92_139) with
| (res, check_res) -> begin
(let c = (FStar_Syntax_Util.ml_comp res r)
in (let t = (FStar_Syntax_Util.arrow bs c)
in (let _92_142 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _194_65 = (FStar_Range.string_of_range r)
in (let _194_64 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _194_65 _194_64)))
end else begin
()
end
in (t, (check_res || check)))))
end))
end))
end
| _92_145 -> begin
(let _194_67 = (let _194_66 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _194_66 Prims.fst))
in (_194_67, false))
end))
in (let _92_148 = (let _194_68 = (t_binders env)
in (aux _194_68 e))
in (match (_92_148) with
| (t, b) -> begin
([], t, b)
end))))))
end
| _92_150 -> begin
(let _92_153 = (FStar_Syntax_Subst.open_univ_vars univ_vars t)
in (match (_92_153) with
| (univ_vars, t) -> begin
(univ_vars, t, false)
end))
end)
end))

# 140 "util.fs"

let is_implicit : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _92_2 -> (match (_92_2) with
| Some (FStar_Syntax_Syntax.Implicit) -> begin
true
end
| _92_158 -> begin
false
end))

# 141 "util.fs"

let as_imp : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _92_3 -> (match (_92_3) with
| Some (FStar_Syntax_Syntax.Implicit) -> begin
true
end
| _92_163 -> begin
false
end))

# 148 "util.fs"

let pat_as_exps : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term Prims.list * FStar_Syntax_Syntax.pat) = (fun allow_implicits env p -> (let rec pat_as_arg_with_env = (fun allow_wc_dependence env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) None p.FStar_Syntax_Syntax.p)
in ([], [], [], env, e, p))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _92_176) -> begin
(let _92_182 = (FStar_Syntax_Util.type_u ())
in (match (_92_182) with
| (k, _92_181) -> begin
(let t = (new_uvar env k)
in (let x = (let _92_184 = x
in {FStar_Syntax_Syntax.ppname = _92_184.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _92_184.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (let _92_189 = (let _194_85 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _194_85 t))
in (match (_92_189) with
| (e, u) -> begin
(let p = (let _92_190 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, e)); FStar_Syntax_Syntax.ty = _92_190.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _92_190.FStar_Syntax_Syntax.p})
in ([], [], [], env, e, p))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(let _92_198 = (FStar_Syntax_Util.type_u ())
in (match (_92_198) with
| (t, _92_197) -> begin
(let x = (let _92_199 = x
in (let _194_86 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _92_199.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _92_199.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _194_86}))
in (let env = if allow_wc_dependence then begin
(FStar_TypeChecker_Env.push_bv env x)
end else begin
env
end
in (let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in ((x)::[], [], (x)::[], env, e, p))))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(let _92_209 = (FStar_Syntax_Util.type_u ())
in (match (_92_209) with
| (t, _92_208) -> begin
(let x = (let _92_210 = x
in (let _194_87 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _92_210.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _92_210.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _194_87}))
in (let env = (FStar_TypeChecker_Env.push_bv env x)
in (let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in ((x)::[], (x)::[], [], env, e, p))))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(let _92_243 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _92_225 _92_228 -> (match ((_92_225, _92_228)) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(let _92_235 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_92_235) with
| (b', a', w', env, te, pat) -> begin
(let arg = if imp then begin
(FStar_Syntax_Syntax.iarg te)
end else begin
(FStar_Syntax_Syntax.as_arg te)
end
in ((b')::b, (a')::a, (w')::w, env, (arg)::args, ((pat, imp))::pats))
end))
end)) ([], [], [], env, [], [])))
in (match (_92_243) with
| (b, a, w, env, args, pats) -> begin
(let e = (let _194_94 = (let _194_93 = (let _194_92 = (let _194_91 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (let _194_90 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app _194_91 _194_90 None p.FStar_Syntax_Syntax.p)))
in (_194_92, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))
in FStar_Syntax_Syntax.Tm_meta (_194_93))
in (FStar_Syntax_Syntax.mk _194_94 None p.FStar_Syntax_Syntax.p))
in (let _194_97 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _194_96 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _194_95 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in (_194_97, _194_96, _194_95, env, e, (let _92_245 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _92_245.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _92_245.FStar_Syntax_Syntax.p}))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (_92_248) -> begin
(FStar_All.failwith "impossible")
end))
in (let rec elaborate_pat = (fun env p -> (let maybe_dot = (fun a r -> if allow_implicits then begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term ((a, FStar_Syntax_Syntax.tun))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end else begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var (a)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end)
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(let pats = (FStar_List.map (fun _92_262 -> (match (_92_262) with
| (p, imp) -> begin
(let _194_107 = (elaborate_pat env p)
in (_194_107, imp))
end)) pats)
in (let _92_267 = (FStar_TypeChecker_Env.lookup_datacon env (Prims.fst fv).FStar_Syntax_Syntax.v)
in (match (_92_267) with
| (_92_265, t) -> begin
(let _92_271 = (FStar_Syntax_Util.arrow_formals t)
in (match (_92_271) with
| (f, _92_270) -> begin
(let rec aux = (fun formals pats -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _92_282::_92_280) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v)))))
end
| (_92_288::_92_286, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun _92_294 -> (match (_92_294) with
| (t, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit) -> begin
(let a = (FStar_Syntax_Syntax.new_bv (Some ((FStar_Syntax_Syntax.range_of_bv t))) FStar_Syntax_Syntax.tun)
in (let r = (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v)
in ((maybe_dot a r), true)))
end
| _92_300 -> begin
(let _194_116 = (let _194_115 = (let _194_114 = (let _194_113 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _194_113))
in (_194_114, (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v)))
in FStar_Syntax_Syntax.Error (_194_115))
in (Prims.raise _194_116))
end)
end))))
end
| (f::formals', (p, p_imp)::pats') -> begin
(match (f) with
| (_92_311, Some (FStar_Syntax_Syntax.Implicit)) when p_imp -> begin
(let _194_117 = (aux formals' pats')
in ((p, true))::_194_117)
end
| (_92_316, Some (FStar_Syntax_Syntax.Implicit)) -> begin
(let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (let p = (maybe_dot a (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v))
in (let _194_118 = (aux formals' pats)
in ((p, true))::_194_118)))
end
| (_92_323, imp) -> begin
(let _194_119 = (aux formals' pats')
in ((p, (as_imp imp)))::_194_119)
end)
end))
in (let _92_326 = p
in (let _194_122 = (let _194_121 = (let _194_120 = (aux f pats)
in (fv, _194_120))
in FStar_Syntax_Syntax.Pat_cons (_194_121))
in {FStar_Syntax_Syntax.v = _194_122; FStar_Syntax_Syntax.ty = _92_326.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _92_326.FStar_Syntax_Syntax.p})))
end))
end)))
end
| _92_329 -> begin
p
end)))
in (let one_pat = (fun allow_wc_dependence env p -> (let p = (elaborate_pat env p)
in (let _92_341 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_92_341) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))) with
| Some (x) -> begin
(let _194_131 = (let _194_130 = (let _194_129 = (FStar_TypeChecker_Errors.nonlinear_pattern_variable x)
in (_194_129, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_194_130))
in (Prims.raise _194_131))
end
| _92_345 -> begin
(b, a, w, arg, p)
end)
end))))
in (let top_level_pat_as_args = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_disj (q::pats) -> begin
(let _92_361 = (one_pat false env q)
in (match (_92_361) with
| (b, a, _92_358, te, q) -> begin
(let _92_376 = (FStar_List.fold_right (fun p _92_366 -> (match (_92_366) with
| (w, args, pats) -> begin
(let _92_372 = (one_pat false env p)
in (match (_92_372) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv FStar_Syntax_Syntax.bv_eq a a'))) then begin
(let _194_140 = (let _194_139 = (let _194_138 = (FStar_TypeChecker_Errors.disjunctive_pattern_vars a a')
in (_194_138, (FStar_TypeChecker_Env.get_range env)))
in FStar_Syntax_Syntax.Error (_194_139))
in (Prims.raise _194_140))
end else begin
((FStar_List.append w' w), ((FStar_Syntax_Syntax.as_arg arg))::args, (p)::pats)
end
end))
end)) pats ([], [], []))
in (match (_92_376) with
| (w, args, pats) -> begin
((FStar_List.append b w), ((FStar_Syntax_Syntax.as_arg te))::args, (let _92_377 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((q)::pats); FStar_Syntax_Syntax.ty = _92_377.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _92_377.FStar_Syntax_Syntax.p}))
end))
end))
end
| _92_380 -> begin
(let _92_388 = (one_pat true env p)
in (match (_92_388) with
| (b, _92_383, _92_385, arg, p) -> begin
(b, ((FStar_Syntax_Syntax.as_arg arg))::[], p)
end))
end))
in (let _92_392 = (top_level_pat_as_args env p)
in (match (_92_392) with
| (b, args, p) -> begin
(let exps = (FStar_All.pipe_right args (FStar_List.map Prims.fst))
in (b, exps, p))
end)))))))

# 274 "util.fs"

let decorate_pattern : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  FStar_Syntax_Syntax.term Prims.list  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t = (fun env p exps -> (let qq = p
in (let rec aux = (fun p e -> (let pkg = (fun q t -> (FStar_Syntax_Syntax.withinfo q t p.FStar_Syntax_Syntax.p))
in (let e = (FStar_Syntax_Util.unmeta e)
in (match ((p.FStar_Syntax_Syntax.v, e.FStar_Syntax_Syntax.n)) with
| (_92_406, FStar_Syntax_Syntax.Tm_uinst (e, _92_409)) -> begin
(aux p e)
end
| (FStar_Syntax_Syntax.Pat_constant (_92_414), FStar_Syntax_Syntax.Tm_constant (_92_417)) -> begin
(let _194_155 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v _194_155))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(let _92_425 = if (not ((FStar_Syntax_Syntax.bv_eq x y))) then begin
(let _194_158 = (let _194_157 = (FStar_Syntax_Print.bv_to_string x)
in (let _194_156 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _194_157 _194_156)))
in (FStar_All.failwith _194_158))
end else begin
()
end
in (let _92_427 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _194_160 = (FStar_Syntax_Print.bv_to_string x)
in (let _194_159 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _194_160 _194_159)))
end else begin
()
end
in (let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (let x = (let _92_430 = x
in {FStar_Syntax_Syntax.ppname = _92_430.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _92_430.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x)) s.FStar_Syntax_Syntax.n)))))
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(let _92_438 = if (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation) then begin
(let _194_163 = (let _194_162 = (FStar_Syntax_Print.bv_to_string x)
in (let _194_161 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _194_162 _194_161)))
in (FStar_All.failwith _194_163))
end else begin
()
end
in (let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (let x = (let _92_441 = x
in {FStar_Syntax_Syntax.ppname = _92_441.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _92_441.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x)) s.FStar_Syntax_Syntax.n))))
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _92_446), _92_450) -> begin
(let s = (force_sort e)
in (let x = (let _92_453 = x
in {FStar_Syntax_Syntax.ppname = _92_453.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _92_453.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
(let _92_463 = if (not ((FStar_Syntax_Syntax.fv_eq fv fv'))) then begin
(let _194_164 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" (Prims.fst fv).FStar_Syntax_Syntax.v.FStar_Ident.str (Prims.fst fv').FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _194_164))
end else begin
()
end
in (let _194_165 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv', []))) _194_165)))
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
(let _92_506 = if (FStar_All.pipe_right (FStar_Syntax_Syntax.fv_eq fv fv') Prims.op_Negation) then begin
(let _194_166 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" (Prims.fst fv).FStar_Syntax_Syntax.v.FStar_Ident.str (Prims.fst fv').FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _194_166))
end else begin
()
end
in (let fv = fv'
in (let rec match_args = (fun matched_pats args argpats -> (match ((args, argpats)) with
| ([], []) -> begin
(let _194_173 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev matched_pats)))) _194_173))
end
| (arg::args, (argpat, _92_522)::argpats) -> begin
(match ((arg, argpat.FStar_Syntax_Syntax.v)) with
| ((e, Some (FStar_Syntax_Syntax.Implicit)), FStar_Syntax_Syntax.Pat_dot_term (_92_531)) -> begin
(let x = (let _194_174 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _194_174))
in (let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((e, imp), _92_540) -> begin
(let pat = (let _194_175 = (aux argpat e)
in (_194_175, (as_imp imp)))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _92_544 -> begin
(let _194_178 = (let _194_177 = (FStar_Syntax_Print.pat_to_string p)
in (let _194_176 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _194_177 _194_176)))
in (FStar_All.failwith _194_178))
end))
in (match_args [] args argpats))))
end
| _92_546 -> begin
(let _194_183 = (let _194_182 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (let _194_181 = (FStar_Syntax_Print.pat_to_string qq)
in (let _194_180 = (let _194_179 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right _194_179 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _194_182 _194_181 _194_180))))
in (FStar_All.failwith _194_183))
end))))
in (match ((p.FStar_Syntax_Syntax.v, exps)) with
| (FStar_Syntax_Syntax.Pat_disj (ps), _92_550) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(let ps = (FStar_List.map2 aux ps exps)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj (ps)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p))
end
| (_92_554, e::[]) -> begin
(aux p e)
end
| _92_559 -> begin
(FStar_All.failwith "Unexpected number of patterns")
end))))

# 349 "util.fs"

let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (let topt = Some (pat.FStar_Syntax_Syntax.ty)
in (let mk = (fun f -> (FStar_Syntax_Syntax.mk f topt pat.FStar_Syntax_Syntax.p))
in (let pat_as_arg = (fun _92_567 -> (match (_92_567) with
| (p, i) -> begin
(let _92_570 = (decorated_pattern_as_term p)
in (match (_92_570) with
| (vars, te) -> begin
(vars, (te, (FStar_Syntax_Syntax.as_implicit i)))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_92_572) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _194_190 = (mk (FStar_Syntax_Syntax.Tm_constant (c)))
in ([], _194_190))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(let _194_191 = (mk (FStar_Syntax_Syntax.Tm_name (x)))
in ((x)::[], _194_191))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(let _92_585 = (let _194_192 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _194_192 FStar_List.unzip))
in (match (_92_585) with
| (vars, args) -> begin
(let vars = (FStar_List.flatten vars)
in (let _194_196 = (let _194_195 = (let _194_194 = (let _194_193 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (_194_193, args))
in FStar_Syntax_Syntax.Tm_app (_194_194))
in (mk _194_195))
in (vars, _194_196)))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
([], e)
end)))))

# 379 "util.fs"

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv Prims.option * FStar_Syntax_Syntax.lcomp)

# 381 "util.fs"

let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (let _92_609 = (match (c.FStar_Syntax_Syntax.effect_args) with
| (wp, _92_598)::(wlp, _92_594)::[] -> begin
(wp, wlp)
end
| _92_602 -> begin
(let _194_202 = (let _194_201 = (let _194_200 = (FStar_List.map (fun _92_606 -> (match (_92_606) with
| (x, _92_605) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right _194_200 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str _194_201))
in (FStar_All.failwith _194_202))
end)
in (match (_92_609) with
| (wp, wlp) -> begin
(c.FStar_Syntax_Syntax.result_typ, wp, wlp)
end)))

# 388 "util.fs"

let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (let _92_617 = (destruct_comp c)
in (match (_92_617) with
| (_92_614, wp, wlp) -> begin
(let _194_224 = (let _194_223 = (let _194_219 = (lift c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _194_219))
in (let _194_222 = (let _194_221 = (let _194_220 = (lift c.FStar_Syntax_Syntax.result_typ wlp)
in (FStar_Syntax_Syntax.as_arg _194_220))
in (_194_221)::[])
in (_194_223)::_194_222))
in {FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _194_224; FStar_Syntax_Syntax.flags = []})
end)))

# 395 "util.fs"

let norm_eff_name : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (let cache = (FStar_Util.smap_create 20)
in (fun env l -> (let rec find = (fun l -> (match ((FStar_TypeChecker_Env.lookup_effect_abbrev env l)) with
| None -> begin
None
end
| Some (_92_625, c) -> begin
(let l = (FStar_Syntax_Util.comp_to_comp_typ c).FStar_Syntax_Syntax.effect_name
in (match ((find l)) with
| None -> begin
Some (l)
end
| Some (l') -> begin
Some (l')
end))
end))
in (let res = (match ((FStar_Util.smap_try_find cache l.FStar_Ident.str)) with
| Some (l) -> begin
l
end
| None -> begin
(match ((find l)) with
| None -> begin
l
end
| Some (m) -> begin
(let _92_639 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))

# 417 "util.fs"

let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (let _92_650 = (let _194_246 = (norm_eff_name env l1)
in (let _194_245 = (norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _194_246 _194_245)))
in (match (_92_650) with
| (m, _92_647, _92_649) -> begin
m
end)))

# 421 "util.fs"

let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> if ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2)) then begin
FStar_Syntax_Const.effect_Tot_lid
end else begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)

# 427 "util.fs"

let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)) = (fun env c1 c2 -> (let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (let _92_662 = (FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (_92_662) with
| (m, lift1, lift2) -> begin
(let m1 = (lift_comp c1 m lift1)
in (let m2 = (lift_comp c2 m lift2)
in (let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (let _92_668 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (_92_668) with
| (a, kwp) -> begin
(let _194_276 = (destruct_comp m1)
in (let _194_275 = (destruct_comp m2)
in ((md, a, kwp), _194_276, _194_275)))
end)))))
end)))))

# 437 "util.fs"

let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (let l = (norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)))

# 441 "util.fs"

let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (let l = (norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid))))

# 446 "util.fs"

let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun md result wp wlp flags -> (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.effect_name = md.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = ((FStar_Syntax_Syntax.as_arg wp))::((FStar_Syntax_Syntax.as_arg wlp))::[]; FStar_Syntax_Syntax.flags = flags}))

# 452 "util.fs"

let subst_lcomp : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (let _92_682 = lc
in (let _194_301 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _92_682.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _194_301; FStar_Syntax_Syntax.cflags = _92_682.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _92_684 -> (match (()) with
| () -> begin
(let _194_300 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _194_300))
end))})))

# 456 "util.fs"

let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _194_304 = (FStar_Syntax_Subst.compress t)
in _194_304.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_92_687) -> begin
true
end
| _92_690 -> begin
false
end))

# 460 "util.fs"

let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun env t v -> (let c = (match ((FStar_TypeChecker_Env.lookup_effect_abbrev env FStar_Syntax_Const.effect_GTot_lid)) with
| None -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| _92_696 -> begin
(let m = (let _194_311 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must _194_311))
in (let _92_700 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_92_700) with
| (a, kwp) -> begin
(let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (let wp = (let _194_313 = (let _194_312 = (FStar_TypeChecker_Env.inst_effect_fun env m m.FStar_Syntax_Syntax.ret)
in (FStar_Syntax_Syntax.mk_Tm_app _194_312 (((FStar_Syntax_Syntax.as_arg t))::((FStar_Syntax_Syntax.as_arg v))::[]) (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _194_313))
in (let wlp = wp
in (mk_comp m t wp wlp ((FStar_Syntax_Syntax.RETURN)::[])))))
end)))
end)
in (let _92_705 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return"))) then begin
(let _194_316 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _194_315 = (FStar_Syntax_Print.term_to_string v)
in (let _194_314 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _194_316 _194_315 _194_314))))
end else begin
()
end
in c)))

# 476 "util.fs"

let bind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun env e1opt lc1 _92_712 -> (match (_92_712) with
| (b, lc2) -> begin
(let _92_720 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let bstr = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _194_327 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (let _194_326 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _194_325 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" _194_327 _194_326 bstr _194_325)))))
end else begin
()
end
in (let bind_it = (fun _92_723 -> (match (()) with
| () -> begin
(let c1 = (lc1.FStar_Syntax_Syntax.comp ())
in (let c2 = (lc2.FStar_Syntax_Syntax.comp ())
in (let _92_729 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _194_334 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _194_333 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _194_332 = (FStar_Syntax_Print.comp_to_string c1)
in (let _194_331 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (let _194_330 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" _194_334 _194_333 _194_332 _194_331 _194_330))))))
end else begin
()
end
in (let try_simplify = (fun _92_732 -> (match (()) with
| () -> begin
(let aux = (fun _92_734 -> (match (()) with
| () -> begin
if (FStar_Syntax_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some ((c2, "trivial no binder"))
end
| Some (_92_737) -> begin
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
(let _194_340 = (let _194_339 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in (_194_339, "both gtot"))
in Some (_194_340))
end else begin
(match ((e1opt, b)) with
| (Some (e), Some (x)) -> begin
if ((FStar_Syntax_Util.is_total_comp c1) && (not ((FStar_Syntax_Syntax.is_null_bv x)))) then begin
(let _194_342 = (let _194_341 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT ((x, e)))::[]) c2)
in (_194_341, "substituted e"))
in Some (_194_342))
end else begin
(aux ())
end
end
| _92_745 -> begin
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
(let _92_763 = (lift_and_destruct env c1 c2)
in (match (_92_763) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(let bs = (match (b) with
| None -> begin
((FStar_Syntax_Syntax.null_binder t1))::[]
end
| Some (x) -> begin
((FStar_Syntax_Syntax.mk_binder x))::[]
end)
in (let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp None))
in (let wp_args = (let _194_353 = (let _194_352 = (let _194_351 = (let _194_350 = (let _194_349 = (let _194_345 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg _194_345))
in (let _194_348 = (let _194_347 = (let _194_346 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _194_346))
in (_194_347)::[])
in (_194_349)::_194_348))
in ((FStar_Syntax_Syntax.as_arg wlp1))::_194_350)
in ((FStar_Syntax_Syntax.as_arg wp1))::_194_351)
in ((FStar_Syntax_Syntax.as_arg t2))::_194_352)
in ((FStar_Syntax_Syntax.as_arg t1))::_194_353)
in (let wlp_args = (let _194_358 = (let _194_357 = (let _194_356 = (let _194_355 = (let _194_354 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _194_354))
in (_194_355)::[])
in ((FStar_Syntax_Syntax.as_arg wlp1))::_194_356)
in ((FStar_Syntax_Syntax.as_arg t2))::_194_357)
in ((FStar_Syntax_Syntax.as_arg t1))::_194_358)
in (let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t2)))::[]) kwp)
in (let wp = (let _194_359 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _194_359 wp_args None t2.FStar_Syntax_Syntax.pos))
in (let wlp = (let _194_360 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.bind_wlp)
in (FStar_Syntax_Syntax.mk_Tm_app _194_360 wlp_args None t2.FStar_Syntax_Syntax.pos))
in (let c = (mk_comp md t2 wp wlp [])
in c))))))))
end))
end)))))
end))
in (let _194_361 = (join_lcomp env lc1 lc2)
in {FStar_Syntax_Syntax.eff_name = _194_361; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it})))
end))

# 542 "util.fs"

let lift_formula : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun env t mk_wp mk_wlp f -> (let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (let _92_784 = (FStar_TypeChecker_Env.wp_signature env md_pure.FStar_Syntax_Syntax.mname)
in (match (_92_784) with
| (a, kwp) -> begin
(let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (let wp = (FStar_Syntax_Syntax.mk_Tm_app mk_wp (((FStar_Syntax_Syntax.as_arg t))::((FStar_Syntax_Syntax.as_arg f))::[]) (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos)
in (let wlp = (FStar_Syntax_Syntax.mk_Tm_app mk_wlp (((FStar_Syntax_Syntax.as_arg t))::((FStar_Syntax_Syntax.as_arg f))::[]) (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos)
in (mk_comp md_pure FStar_TypeChecker_Recheck.t_unit wp wlp []))))
end))))

# 550 "util.fs"

let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((f, FStar_Syntax_Syntax.Meta_labeled ((reason, r, false))))) None f.FStar_Syntax_Syntax.pos))

# 553 "util.fs"

let label_opt : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _194_395 = (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)
in (FStar_All.pipe_left Prims.op_Negation _194_395)) then begin
f
end else begin
(let _194_396 = (reason ())
in (label _194_396 r f))
end
end))

# 560 "util.fs"

let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _92_804 = g
in (let _194_404 = (let _194_403 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_194_403))
in {FStar_TypeChecker_Env.guard_f = _194_404; FStar_TypeChecker_Env.deferred = _92_804.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _92_804.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _92_804.FStar_TypeChecker_Env.implicits}))
end))

# 564 "util.fs"

let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| _92_815 -> begin
g2
end))

# 570 "util.fs"

let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (let weaken = (fun _92_820 -> (match (()) with
| () -> begin
(let c = (lc.FStar_Syntax_Syntax.comp ())
in (match (f) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
if (FStar_Syntax_Util.is_ml_comp c) then begin
c
end else begin
(let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (let _92_829 = (destruct_comp c)
in (match (_92_829) with
| (res_t, wp, wlp) -> begin
(let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (let wp = (let _194_417 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.assume_p)
in (FStar_Syntax_Syntax.mk_Tm_app _194_417 (((FStar_Syntax_Syntax.as_arg res_t))::((FStar_Syntax_Syntax.as_arg f))::((FStar_Syntax_Syntax.as_arg wp))::[]) None wp.FStar_Syntax_Syntax.pos))
in (let wlp = (let _194_418 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.assume_p)
in (FStar_Syntax_Syntax.mk_Tm_app _194_418 (((FStar_Syntax_Syntax.as_arg res_t))::((FStar_Syntax_Syntax.as_arg f))::((FStar_Syntax_Syntax.as_arg wlp))::[]) None wlp.FStar_Syntax_Syntax.pos))
in (mk_comp md res_t wp wlp c.FStar_Syntax_Syntax.flags))))
end)))
end
end))
end))
in (let _92_833 = lc
in {FStar_Syntax_Syntax.eff_name = _92_833.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _92_833.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _92_833.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))

# 586 "util.fs"

let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> if (FStar_TypeChecker_Rel.is_trivial g0) then begin
(lc, g0)
end else begin
(let _92_840 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _194_438 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _194_437 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _194_438 _194_437)))
end else begin
()
end
in (let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _92_4 -> (match (_92_4) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _92_846 -> begin
[]
end))))
in (let strengthen = (fun _92_849 -> (match (()) with
| () -> begin
(let c = (lc.FStar_Syntax_Syntax.comp ())
in (let g0 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (match ((FStar_TypeChecker_Rel.guard_form g0)) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let c = if (true || (((FStar_Syntax_Util.is_pure_or_ghost_comp c) && (not ((is_function (FStar_Syntax_Util.comp_result c))))) && (not ((FStar_Syntax_Util.is_partial_return c))))) then begin
(let x = (FStar_Syntax_Syntax.gen_bv "strengthen_pre_x" None (FStar_Syntax_Util.comp_result c))
in (let xret = (let _194_443 = (let _194_442 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _194_442))
in (FStar_Syntax_Util.comp_set_flags _194_443 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (let lc = (bind env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), (FStar_Syntax_Util.lcomp_of_comp xret)))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (let _92_859 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _194_445 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _194_444 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _194_445 _194_444)))
end else begin
()
end
in (let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (let _92_865 = (destruct_comp c)
in (match (_92_865) with
| (res_t, wp, wlp) -> begin
(let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (let wp = (let _194_450 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.assert_p)
in (let _194_449 = (let _194_448 = (let _194_447 = (let _194_446 = (label_opt env reason (FStar_TypeChecker_Env.get_range env) f)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _194_446))
in (_194_447)::((FStar_Syntax_Syntax.as_arg wp))::[])
in ((FStar_Syntax_Syntax.as_arg res_t))::_194_448)
in (FStar_Syntax_Syntax.mk_Tm_app _194_450 _194_449 None wp.FStar_Syntax_Syntax.pos)))
in (let wlp = (let _194_451 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.assume_p)
in (FStar_Syntax_Syntax.mk_Tm_app _194_451 (((FStar_Syntax_Syntax.as_arg res_t))::((FStar_Syntax_Syntax.as_arg f))::((FStar_Syntax_Syntax.as_arg wlp))::[]) None wlp.FStar_Syntax_Syntax.pos))
in (let _92_869 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _194_452 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _194_452))
end else begin
()
end
in (let c2 = (mk_comp md res_t wp wlp flags)
in c2)))))
end)))))
end)))
end))
in (let _194_456 = (let _92_872 = lc
in (let _194_455 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _194_454 = if ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _194_453 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _194_453))) then begin
flags
end else begin
[]
end
in {FStar_Syntax_Syntax.eff_name = _194_455; FStar_Syntax_Syntax.res_typ = _92_872.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _194_454; FStar_Syntax_Syntax.comp = strengthen})))
in (_194_456, (let _92_874 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _92_874.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _92_874.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _92_874.FStar_TypeChecker_Env.implicits}))))))
end)

# 634 "util.fs"

let record_application_site : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (let comp = (fun _92_880 -> (match (()) with
| () -> begin
(let c = (lc.FStar_Syntax_Syntax.comp ())
in (let res_t = (FStar_Syntax_Util.comp_result c)
in if (((FStar_Syntax_Util.is_trivial_wp c) || (FStar_Ident.lid_equals (FStar_TypeChecker_Env.current_module env) FStar_Syntax_Const.prims_lid)) || (FStar_Syntax_Syntax.is_teff res_t)) then begin
c
end else begin
(let g = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (FStar_TypeChecker_Recheck.t_unit)))
in (let _92_888 = (strengthen_precondition (Some ((fun _92_884 -> (match (()) with
| () -> begin
"push"
end)))) env e (FStar_Syntax_Util.lcomp_of_comp c) g)
in (match (_92_888) with
| (c, _92_887) -> begin
(let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (let xret = (let _194_468 = (FStar_TypeChecker_Env.inst_effect_fun env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (FStar_Syntax_Syntax.mk_Tm_app _194_468 (((FStar_Syntax_Syntax.as_arg res_t))::((FStar_Syntax_Syntax.as_arg xexp))::[]) None res_t.FStar_Syntax_Syntax.pos))
in (let xret_comp = (let _194_469 = (mk_comp md_pure res_t xret xret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _194_469))
in (let lc = (let _194_475 = (let _194_474 = (let _194_473 = (strengthen_precondition (Some ((fun _92_894 -> (match (()) with
| () -> begin
"pop"
end)))) env xexp xret_comp g)
in (FStar_All.pipe_left Prims.fst _194_473))
in (Some (x), _194_474))
in (bind env None c _194_475))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end)))
end))
end))
in (let _92_896 = lc
in {FStar_Syntax_Syntax.eff_name = _92_896.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _92_896.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _92_896.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = comp})))

# 653 "util.fs"

let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env comp res_t -> (let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let y = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _92_906 = (let _194_483 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _194_482 = (FStar_Syntax_Syntax.bv_to_name y)
in (_194_483, _194_482)))
in (match (_92_906) with
| (xexp, yexp) -> begin
(let yret = (let _194_484 = (FStar_TypeChecker_Env.inst_effect_fun env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (FStar_Syntax_Syntax.mk_Tm_app _194_484 (((FStar_Syntax_Syntax.as_arg res_t))::((FStar_Syntax_Syntax.as_arg yexp))::[]) None res_t.FStar_Syntax_Syntax.pos))
in (let x_eq_y_yret = (let _194_491 = (FStar_TypeChecker_Env.inst_effect_fun env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _194_490 = (let _194_489 = (let _194_488 = (let _194_485 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _194_485))
in (let _194_487 = (let _194_486 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_194_486)::[])
in (_194_488)::_194_487))
in ((FStar_Syntax_Syntax.as_arg res_t))::_194_489)
in (FStar_Syntax_Syntax.mk_Tm_app _194_491 _194_490 None res_t.FStar_Syntax_Syntax.pos)))
in (let forall_y_x_eq_y_yret = (let _194_497 = (FStar_TypeChecker_Env.inst_effect_fun env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _194_496 = (let _194_495 = (let _194_494 = (let _194_493 = (let _194_492 = (FStar_Syntax_Util.abs (((FStar_Syntax_Syntax.mk_binder y))::[]) x_eq_y_yret None)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _194_492))
in (_194_493)::[])
in ((FStar_Syntax_Syntax.as_arg res_t))::_194_494)
in ((FStar_Syntax_Syntax.as_arg res_t))::_194_495)
in (FStar_Syntax_Syntax.mk_Tm_app _194_497 _194_496 None res_t.FStar_Syntax_Syntax.pos)))
in (let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (let lc = (bind env None (FStar_Syntax_Util.lcomp_of_comp comp) (Some (x), (FStar_Syntax_Util.lcomp_of_comp lc2)))
in (lc.FStar_Syntax_Syntax.comp ()))))))
end))))))

# 665 "util.fs"

let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (let comp = (fun _92_917 -> (match (()) with
| () -> begin
(let _92_933 = (let _194_509 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _194_508 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _194_509 _194_508)))
in (match (_92_933) with
| ((md, _92_920, _92_922), (res_t, wp_then, wlp_then), (_92_929, wp_else, wlp_else)) -> begin
(let ifthenelse = (fun md res_t g wp_t wp_e -> (let _194_521 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.if_then_else)
in (let _194_520 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _194_521 (((FStar_Syntax_Syntax.as_arg res_t))::((FStar_Syntax_Syntax.as_arg g))::((FStar_Syntax_Syntax.as_arg wp_t))::((FStar_Syntax_Syntax.as_arg wp_e))::[]) None _194_520))))
in (let wp = (ifthenelse md res_t guard wp_then wp_else)
in (let wlp = (ifthenelse md res_t guard wlp_then wlp_else)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(let comp = (mk_comp md res_t wp wlp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(let wp = (let _194_522 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.ite_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _194_522 (((FStar_Syntax_Syntax.as_arg res_t))::((FStar_Syntax_Syntax.as_arg wlp))::((FStar_Syntax_Syntax.as_arg wp))::[]) None wp.FStar_Syntax_Syntax.pos))
in (let wlp = (let _194_523 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.ite_wlp)
in (FStar_Syntax_Syntax.mk_Tm_app _194_523 (((FStar_Syntax_Syntax.as_arg res_t))::((FStar_Syntax_Syntax.as_arg wlp))::[]) None wlp.FStar_Syntax_Syntax.pos))
in (mk_comp md res_t wp wlp [])))
end)))
end))
end))
in (let _194_524 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _194_524; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp})))

# 682 "util.fs"

let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.formula * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (let eff = (FStar_List.fold_left (fun eff _92_952 -> (match (_92_952) with
| (_92_950, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (let bind_cases = (fun _92_955 -> (match (()) with
| () -> begin
(let ifthenelse = (fun md res_t g wp_t wp_e -> (let _194_546 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.if_then_else)
in (let _194_545 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _194_546 (((FStar_Syntax_Syntax.as_arg res_t))::((FStar_Syntax_Syntax.as_arg g))::((FStar_Syntax_Syntax.as_arg wp_t))::((FStar_Syntax_Syntax.as_arg wp_e))::[]) None _194_545))))
in (let default_case = (let post_k = (let _194_547 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow (((FStar_Syntax_Syntax.null_binder res_t))::[]) _194_547))
in (let kwp = (let _194_548 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow (((FStar_Syntax_Syntax.null_binder post_k))::[]) _194_548))
in (let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (let wp = (let _194_550 = (let _194_549 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.false_lid (FStar_TypeChecker_Env.get_range env))
in (FStar_All.pipe_left (label FStar_TypeChecker_Errors.exhaustiveness_check (FStar_TypeChecker_Env.get_range env)) _194_549))
in (FStar_Syntax_Util.abs (((FStar_Syntax_Syntax.mk_binder post))::[]) _194_550 None))
in (let wlp = (let _194_551 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid (FStar_TypeChecker_Env.get_range env))
in (FStar_Syntax_Util.abs (((FStar_Syntax_Syntax.mk_binder post))::[]) _194_551 None))
in (let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (let comp = (FStar_List.fold_right (fun _92_971 celse -> (match (_92_971) with
| (g, cthen) -> begin
(let _92_989 = (let _194_554 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _194_554 celse))
in (match (_92_989) with
| ((md, _92_975, _92_977), (_92_980, wp_then, wlp_then), (_92_985, wp_else, wlp_else)) -> begin
(let _194_556 = (ifthenelse md res_t g wp_then wp_else)
in (let _194_555 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _194_556 _194_555 [])))
end))
end)) lcases default_case)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(add_equality_to_post_condition env comp res_t)
end else begin
(let comp = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (let md = (FStar_TypeChecker_Env.get_effect_decl env comp.FStar_Syntax_Syntax.effect_name)
in (let _92_997 = (destruct_comp comp)
in (match (_92_997) with
| (_92_994, wp, wlp) -> begin
(let wp = (let _194_557 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.ite_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _194_557 (((FStar_Syntax_Syntax.as_arg res_t))::((FStar_Syntax_Syntax.as_arg wlp))::((FStar_Syntax_Syntax.as_arg wp))::[]) None wp.FStar_Syntax_Syntax.pos))
in (let wlp = (let _194_558 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.ite_wlp)
in (FStar_Syntax_Syntax.mk_Tm_app _194_558 (((FStar_Syntax_Syntax.as_arg res_t))::((FStar_Syntax_Syntax.as_arg wlp))::[]) None wlp.FStar_Syntax_Syntax.pos))
in (mk_comp md res_t wp wlp [])))
end))))
end)))
end))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))

# 711 "util.fs"

let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (let close = (fun _92_1004 -> (match (()) with
| () -> begin
(let c = (lc.FStar_Syntax_Syntax.comp ())
in if (FStar_Syntax_Util.is_ml_comp c) then begin
c
end else begin
(let close_wp = (fun md res_t bvs wp0 -> (FStar_List.fold_right (fun x wp -> (let bs = ((FStar_Syntax_Syntax.mk_binder x))::[]
in (let wp = (FStar_Syntax_Util.abs bs wp None)
in (let _194_577 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.close_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _194_577 (((FStar_Syntax_Syntax.as_arg res_t))::((FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort))::((FStar_Syntax_Syntax.as_arg wp))::[]) None wp0.FStar_Syntax_Syntax.pos))))) bvs wp0))
in (let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (let _92_1019 = (destruct_comp c)
in (match (_92_1019) with
| (t, wp, wlp) -> begin
(let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (let wp = (close_wp md c.FStar_Syntax_Syntax.result_typ bvs wp)
in (let wlp = (close_wp md c.FStar_Syntax_Syntax.result_typ bvs wlp)
in (mk_comp md c.FStar_Syntax_Syntax.result_typ wp wlp c.FStar_Syntax_Syntax.flags))))
end))))
end)
end))
in (let _92_1023 = lc
in {FStar_Syntax_Syntax.eff_name = _92_1023.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _92_1023.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _92_1023.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))

# 730 "util.fs"

let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (let refine = (fun _92_1029 -> (match (()) with
| () -> begin
(let c = (lc.FStar_Syntax_Syntax.comp ())
in if (not ((is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name))) then begin
c
end else begin
if (FStar_Syntax_Util.is_partial_return c) then begin
c
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c) && (let _194_586 = (FStar_TypeChecker_Env.lookup_effect_abbrev env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left FStar_Option.isNone _194_586))) then begin
(let _194_589 = (let _194_588 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _194_587 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _194_588 _194_587)))
in (FStar_All.failwith _194_589))
end else begin
(let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (let t = c.FStar_Syntax_Syntax.result_typ
in (let c = (FStar_Syntax_Syntax.mk_Comp c)
in (let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (let ret = (let _194_591 = (let _194_590 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _194_590 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _194_591))
in (let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (let c = (let _194_593 = (let _194_592 = (bind env None (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), eq_ret))
in (_194_592.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _194_593 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
in c)))))))))
end
end
end)
end))
in (let flags = if (((not ((FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)) && (not ((FStar_Syntax_Util.is_lcomp_partial_return lc)))) then begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_Syntax_Syntax.cflags
end else begin
lc.FStar_Syntax_Syntax.cflags
end
in (let _92_1041 = lc
in {FStar_Syntax_Syntax.eff_name = _92_1041.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _92_1041.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))

# 759 "util.fs"

let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (match ((FStar_TypeChecker_Rel.sub_comp env c c')) with
| None -> begin
(let _194_604 = (let _194_603 = (let _194_602 = (FStar_TypeChecker_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (_194_602, (FStar_TypeChecker_Env.get_range env)))
in FStar_Syntax_Syntax.Error (_194_603))
in (Prims.raise _194_604))
end
| Some (g) -> begin
(e, c', g)
end))

# 765 "util.fs"

let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match ((let _194_613 = (FStar_Syntax_Subst.compress t)
in _194_613.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_92_1055) -> begin
(match ((let _194_614 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _194_614.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _92_1059) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.bool_lid) -> begin
(let _92_1062 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (let b2t = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos)
in (let lc = (let _194_617 = (let _194_616 = (let _194_615 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _194_615))
in (None, _194_616))
in (bind env (Some (e)) lc _194_617))
in (let e = (FStar_Syntax_Syntax.mk_Tm_app b2t (((FStar_Syntax_Syntax.as_arg e))::[]) (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (e, lc)))))
end
| _92_1068 -> begin
(e, lc)
end)
end
| _92_1070 -> begin
(e, lc)
end))

# 780 "util.fs"

let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (let gopt = if env.FStar_TypeChecker_Env.use_eq then begin
(let _194_626 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in (_194_626, false))
end else begin
(let _194_627 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in (_194_627, true))
end
in (match (gopt) with
| (None, _92_1078) -> begin
(FStar_TypeChecker_Rel.subtype_fail env lc.FStar_Syntax_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(match ((FStar_TypeChecker_Rel.guard_form g)) with
| FStar_TypeChecker_Common.Trivial -> begin
(let lc = (let _92_1085 = lc
in {FStar_Syntax_Syntax.eff_name = _92_1085.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _92_1085.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _92_1085.FStar_Syntax_Syntax.comp})
in (e, lc, g))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let g = (let _92_1090 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _92_1090.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _92_1090.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _92_1090.FStar_TypeChecker_Env.implicits})
in (let strengthen = (fun _92_1094 -> (match (()) with
| () -> begin
(let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (match ((let _194_630 = (FStar_Syntax_Subst.compress f)
in _194_630.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_92_1097, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _92_1106); FStar_Syntax_Syntax.tk = _92_1103; FStar_Syntax_Syntax.pos = _92_1101; FStar_Syntax_Syntax.vars = _92_1099}, _92_1111) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) -> begin
(let lc = (let _92_1114 = lc
in {FStar_Syntax_Syntax.eff_name = _92_1114.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _92_1114.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _92_1114.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| _92_1118 -> begin
(let c = (lc.FStar_Syntax_Syntax.comp ())
in (let _92_1120 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _194_634 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _194_633 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _194_632 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _194_631 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _194_634 _194_633 _194_632 _194_631)))))
end else begin
()
end
in (let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (let _92_1125 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_92_1125) with
| (a, kwp) -> begin
(let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (let md = (FStar_TypeChecker_Env.get_effect_decl env ct.FStar_Syntax_Syntax.effect_name)
in (let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (let wp = (let _194_635 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.ret)
in (FStar_Syntax_Syntax.mk_Tm_app _194_635 (((FStar_Syntax_Syntax.as_arg t))::((FStar_Syntax_Syntax.as_arg xexp))::[]) (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos))
in (let cret = (let _194_636 = (mk_comp md t wp wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _194_636))
in (let guard = if apply_guard then begin
(FStar_Syntax_Syntax.mk_Tm_app f (((FStar_Syntax_Syntax.as_arg xexp))::[]) (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos)
end else begin
f
end
in (let _92_1135 = (let _194_643 = (FStar_All.pipe_left (fun _194_641 -> Some (_194_641)) (FStar_TypeChecker_Errors.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _194_642 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _194_643 (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos) e cret _194_642)))
in (match (_92_1135) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(let x = (let _92_1136 = x
in {FStar_Syntax_Syntax.ppname = _92_1136.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _92_1136.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (let c = (let _194_645 = (let _194_644 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _194_644))
in (bind env (Some (e)) _194_645 (Some (x), eq_ret)))
in (let c = (c.FStar_Syntax_Syntax.comp ())
in (let _92_1141 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _194_646 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _194_646))
end else begin
()
end
in c))))
end)))))))))
end)))))
end))
end))
in (let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _92_5 -> (match (_92_5) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _92_1147 -> begin
[]
end))))
in (let lc = (let _92_1149 = lc
in (let _194_648 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _194_648; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (let g = (let _92_1152 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _92_1152.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _92_1152.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _92_1152.FStar_TypeChecker_Env.implicits})
in (e, lc, g))))))
end)
end)))

# 836 "util.fs"

let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (let mk_post_type = (fun res_t ens -> (let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _194_660 = (let _194_659 = (let _194_658 = (let _194_657 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _194_657))
in (_194_658)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _194_659 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _194_660))))
in (let norm = (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Unlabel)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env t))
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
| (req, _92_1180)::(ens, _92_1175)::_92_1172 -> begin
(let _194_666 = (let _194_663 = (norm req)
in Some (_194_663))
in (let _194_665 = (let _194_664 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _194_664))
in (_194_666, _194_665)))
end
| _92_1184 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (wp, _92_1195)::(wlp, _92_1190)::_92_1187 -> begin
(let _92_1201 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (_92_1201) with
| (us_r, _92_1200) -> begin
(let _92_1205 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (_92_1205) with
| (us_e, _92_1204) -> begin
(let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (let as_req = (let _194_667 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.as_requires r)
in (FStar_Syntax_Syntax.mk_Tm_uinst _194_667 us_r))
in (let as_ens = (let _194_668 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.as_ensures r)
in (FStar_Syntax_Syntax.mk_Tm_uinst _194_668 us_e))
in (let req = (FStar_Syntax_Syntax.mk_Tm_app as_req (((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.Implicit)))::((FStar_Syntax_Syntax.as_arg wp))::[]) (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos)
in (let ens = (FStar_Syntax_Syntax.mk_Tm_app as_ens (((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.Implicit)))::((FStar_Syntax_Syntax.as_arg wlp))::[]) None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos)
in (let _194_672 = (let _194_669 = (norm req)
in Some (_194_669))
in (let _194_671 = (let _194_670 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm _194_670))
in (_194_672, _194_671))))))))
end))
end))
end
| _92_1212 -> begin
(FStar_All.failwith "Impossible")
end))
end
end)
end)))

# 873 "util.fs"

let maybe_instantiate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (let torig = (FStar_Syntax_Subst.compress t)
in if (not (env.FStar_TypeChecker_Env.instantiate_imp)) then begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end else begin
(match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _92_1223 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_92_1223) with
| (bs, c) -> begin
(let rec aux = (fun subst _92_6 -> (match (_92_6) with
| (x, Some (FStar_Syntax_Syntax.Implicit))::rest -> begin
(let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (let _92_1237 = (new_implicit_var env t)
in (match (_92_1237) with
| (v, u, g) -> begin
(let subst = (FStar_Syntax_Syntax.NT ((x, v)))::subst
in (let _92_1243 = (aux subst rest)
in (match (_92_1243) with
| (args, bs, subst, g') -> begin
(let _194_683 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((v, Some (FStar_Syntax_Syntax.Implicit)))::args, bs, subst, _194_683))
end)))
end)))
end
| bs -> begin
([], bs, subst, FStar_TypeChecker_Rel.trivial_guard)
end))
in (let _92_1249 = (aux [] bs)
in (match (_92_1249) with
| (args, bs, subst, guard) -> begin
(match ((args, bs)) with
| ([], _92_1252) -> begin
(e, torig, guard)
end
| (_92_1255, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end
| _92_1259 -> begin
(let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _92_1262 -> begin
(FStar_Syntax_Util.arrow bs c)
end)
in (let t = (FStar_Syntax_Subst.subst subst t)
in (let e = (FStar_Syntax_Syntax.mk_Tm_app e args (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (e, t, guard))))
end)
end)))
end))
end
| _92_1267 -> begin
(e, t, FStar_TypeChecker_Rel.trivial_guard)
end)
end))

# 914 "util.fs"

let gen_univs : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe_uvar Prims.list * (FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  Prims.bool))  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(let s = (let _194_695 = (let _194_694 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _194_694))
in (FStar_All.pipe_right _194_695 FStar_Util.set_elements))
in (let r = Some ((FStar_TypeChecker_Env.get_range env))
in (let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (let _92_1274 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _194_700 = (let _194_697 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _194_697))
in (let _194_699 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _194_698 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _194_700 _194_699 _194_698))))
end else begin
()
end
in (let _92_1276 = (FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))))
in u_name))))))
in u_names)))
end)

# 926 "util.fs"

let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.univ_name Prims.list * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun env t -> (let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (let univs = (FStar_Syntax_Free.univs t)
in (let _92_1284 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _194_713 = (let _194_712 = (let _194_711 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _194_711 (FStar_List.map (fun u -> (let _194_710 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _194_710 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _194_712 (FStar_String.concat ", ")))
in (FStar_Util.print1 "univs to gen : %s\n" _194_713))
end else begin
()
end
in (let gen = (gen_univs env univs)
in (let _92_1287 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _194_714 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _194_714))
end else begin
()
end
in (let ts = (FStar_Syntax_Subst.close_univ_vars gen t)
in (gen, ts))))))))

# 939 "util.fs"

let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> if (let _194_720 = (FStar_Util.for_all (fun _92_1295 -> (match (_92_1295) with
| (_92_1293, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _194_720)) then begin
None
end else begin
(let norm = (fun c -> (let _92_1298 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _194_723 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _194_723))
end else begin
()
end
in (let c = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.Eta)::[]) env c)
end else begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env c)
end
in (let _92_1301 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _194_724 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _194_724))
end else begin
()
end
in c))))
in (let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (let gen_uvars = (fun uvs -> (let _194_731 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _194_731 FStar_Util.set_elements)))
in (let _92_1318 = (let _194_797 = (FStar_All.pipe_right ecs (FStar_List.map (fun _92_1308 -> (match (_92_1308) with
| (e, c) -> begin
(let t = (FStar_All.pipe_right (FStar_Syntax_Util.comp_result c) FStar_Syntax_Subst.compress)
in (let c = (norm c)
in (let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (let t = ct.FStar_Syntax_Syntax.result_typ
in (let univs = (FStar_Syntax_Free.univs t)
in (let uvt = (FStar_Syntax_Free.uvars t)
in (let uvs = (gen_uvars uvt)
in (univs, (uvs, e, c)))))))))
end))))
in (FStar_All.pipe_right _194_797 FStar_List.unzip))
in (match (_92_1318) with
| (univs, uvars) -> begin
(let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (let gen_univs = (gen_univs env univs)
in (let _92_1322 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end else begin
()
end
in (let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _92_1327 -> (match (_92_1327) with
| (uvs, e, c) -> begin
(let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _92_1330 -> (match (_92_1330) with
| (u, k) -> begin
(match ((FStar_Unionfind.find u)) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(a, Some (FStar_Syntax_Syntax.Implicit))
end
| FStar_Syntax_Syntax.Fixed (_92_1364) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _92_1367 -> begin
(let _92_1370 = (FStar_Syntax_Util.arrow_formals k)
in (match (_92_1370) with
| (bs, kres) -> begin
(let a = (let _194_808 = (FStar_All.pipe_left (fun _194_807 -> Some (_194_807)) (FStar_TypeChecker_Env.get_range env))
in (FStar_Syntax_Syntax.new_bv _194_808 kres))
in (let t = (let _194_812 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _194_811 = (let _194_810 = (let _194_809 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _194_809))
in Some (_194_810))
in (FStar_Syntax_Util.abs bs _194_812 _194_811)))
in (let _92_1373 = (FStar_Syntax_Util.set_uvar u t)
in (a, Some (FStar_Syntax_Syntax.Implicit)))))
end))
end)
end))))
in (let _92_1394 = (match (tvars) with
| [] -> begin
(e, c)
end
| _92_1378 -> begin
(let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]) env c)
in (let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]) env e)
in (let t = (match ((let _194_813 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _194_813.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(let _92_1387 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (_92_1387) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| _92_1389 -> begin
(FStar_Syntax_Util.arrow tvars c)
end)
in (let e' = (FStar_Syntax_Util.abs tvars e None)
in (let _194_814 = (FStar_Syntax_Syntax.mk_Total t)
in (e', _194_814))))))
end)
in (match (_92_1394) with
| (e, c) -> begin
(gen_univs, e, c)
end)))
end))))
in Some (ecs)))))
end)))))
end)

# 1003 "util.fs"

let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> (let _92_1404 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _194_821 = (let _194_820 = (FStar_List.map (fun _92_1403 -> (match (_92_1403) with
| (lb, _92_1400, _92_1402) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _194_820 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _194_821))
end else begin
()
end
in (match ((let _194_823 = (FStar_All.pipe_right lecs (FStar_List.map (fun _92_1410 -> (match (_92_1410) with
| (_92_1407, e, c) -> begin
(e, c)
end))))
in (gen env _194_823))) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun _92_1415 -> (match (_92_1415) with
| (l, t, c) -> begin
(l, [], t, c)
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _92_1423 _92_1427 -> (match ((_92_1423, _92_1427)) with
| ((l, _92_1420, _92_1422), (us, e, c)) -> begin
(let _92_1428 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _194_829 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _194_828 = (FStar_Syntax_Print.lbname_to_string l)
in (let _194_827 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.print3 "(%s) Generalized %s to %s\n" _194_829 _194_828 _194_827))))
end else begin
()
end
in (l, us, e, c))
end)) lecs ecs)
end)))

# 1024 "util.fs"

let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let check = (fun env t1 t2 -> if env.FStar_TypeChecker_Env.use_eq then begin
(FStar_TypeChecker_Rel.try_teq env t1 t2)
end else begin
(match ((FStar_TypeChecker_Rel.try_subtype env t1 t2)) with
| None -> begin
None
end
| Some (f) -> begin
(let _194_845 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _194_844 -> Some (_194_844)) _194_845))
end)
end)
in (let is_var = (fun e -> (match ((let _194_848 = (FStar_Syntax_Subst.compress e)
in _194_848.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (_92_1445) -> begin
true
end
| _92_1448 -> begin
false
end))
in (let decorate = (fun e t -> (let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((let _92_1455 = x
in {FStar_Syntax_Syntax.ppname = _92_1455.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _92_1455.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| _92_1458 -> begin
(let _92_1459 = e
in (let _194_853 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _92_1459.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _194_853; FStar_Syntax_Syntax.pos = _92_1459.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _92_1459.FStar_Syntax_Syntax.vars}))
end)))
in (let env = (let _92_1461 = env
in (let _194_854 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _92_1461.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _92_1461.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _92_1461.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _92_1461.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _92_1461.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _92_1461.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _92_1461.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _92_1461.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _92_1461.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _92_1461.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _92_1461.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _92_1461.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _92_1461.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _92_1461.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _92_1461.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _194_854; FStar_TypeChecker_Env.is_iface = _92_1461.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _92_1461.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _92_1461.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _92_1461.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _92_1461.FStar_TypeChecker_Env.use_bv_sorts}))
in (match ((check env t1 t2)) with
| None -> begin
(let _194_857 = (let _194_856 = (let _194_855 = (FStar_TypeChecker_Errors.expected_expression_of_type env t2 e t1)
in (_194_855, (FStar_TypeChecker_Env.get_range env)))
in FStar_Syntax_Syntax.Error (_194_856))
in (Prims.raise _194_857))
end
| Some (g) -> begin
(let _92_1467 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _194_858 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _194_858))
end else begin
()
end
in (let _194_859 = (decorate e t2)
in (_194_859, g)))
end)))))))

# 1049 "util.fs"

let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (let discharge = (fun g -> (let _92_1474 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _194_869 = (discharge g)
in (let _194_868 = (lc.FStar_Syntax_Syntax.comp ())
in (_194_869, _194_868)))
end else begin
(let c = (lc.FStar_Syntax_Syntax.comp ())
in (let steps = (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.DeltaComp)::[]
in (let c = (let _194_870 = (FStar_TypeChecker_Normalize.normalize_comp steps env c)
in (FStar_All.pipe_right _194_870 FStar_Syntax_Util.comp_to_comp_typ))
in (let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (let _92_1485 = (destruct_comp c)
in (match (_92_1485) with
| (t, wp, _92_1484) -> begin
(let vc = (let _194_871 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.trivial)
in (FStar_Syntax_Syntax.mk_Tm_app _194_871 (((FStar_Syntax_Syntax.as_arg t))::((FStar_Syntax_Syntax.as_arg wp))::[]) (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) (FStar_TypeChecker_Env.get_range env)))
in (let _92_1487 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _194_872 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _194_872))
end else begin
()
end
in (let g = (let _194_873 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _194_873))
in (let _194_875 = (discharge g)
in (let _194_874 = (FStar_Syntax_Syntax.mk_Comp c)
in (_194_875, _194_874))))))
end))))))
end)))

# 1070 "util.fs"

let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (let short_bin_op = (fun f _92_7 -> (match (_92_7) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (fst, _92_1498)::[] -> begin
(f fst)
end
| _92_1502 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (let op_and_e = (fun e -> (let _194_896 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _194_896 (fun _194_895 -> FStar_TypeChecker_Common.NonTrivial (_194_895)))))
in (let op_or_e = (fun e -> (let _194_901 = (let _194_899 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _194_899))
in (FStar_All.pipe_right _194_901 (fun _194_900 -> FStar_TypeChecker_Common.NonTrivial (_194_900)))))
in (let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _194_904 -> FStar_TypeChecker_Common.NonTrivial (_194_904))))
in (let op_or_t = (fun t -> (let _194_908 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _194_908 (fun _194_907 -> FStar_TypeChecker_Common.NonTrivial (_194_907)))))
in (let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _194_911 -> FStar_TypeChecker_Common.NonTrivial (_194_911))))
in (let short_op_ite = (fun _92_8 -> (match (_92_8) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (guard, _92_1517)::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| _then::(guard, _92_1522)::[] -> begin
(let _194_915 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _194_915 (fun _194_914 -> FStar_TypeChecker_Common.NonTrivial (_194_914))))
end
| _92_1527 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (let table = ((FStar_Syntax_Const.op_And, (short_bin_op op_and_e)))::((FStar_Syntax_Const.op_Or, (short_bin_op op_or_e)))::((FStar_Syntax_Const.and_lid, (short_bin_op op_and_t)))::((FStar_Syntax_Const.or_lid, (short_bin_op op_or_t)))::((FStar_Syntax_Const.imp_lid, (short_bin_op op_imp_t)))::((FStar_Syntax_Const.ite_lid, short_op_ite))::[]
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _92_1532) -> begin
(let lid = fv.FStar_Syntax_Syntax.v
in (match ((FStar_Util.find_map table (fun _92_1538 -> (match (_92_1538) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _194_948 = (mk seen_args)
in Some (_194_948))
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
| _92_1543 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))

# 1104 "util.fs"

let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (match ((let _194_951 = (FStar_Syntax_Subst.compress l)
in _194_951.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (v, _92_1547) -> begin
(FStar_Util.for_some (FStar_Ident.lid_equals v.FStar_Syntax_Syntax.v) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| _92_1551 -> begin
false
end))

# 1125 "util.fs"

let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (let pos = (fun bs -> (match (bs) with
| (hd, _92_1560)::_92_1557 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| _92_1564 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| (_92_1568, Some (FStar_Syntax_Syntax.Implicit))::_92_1566 -> begin
bs
end
| _92_1574 -> begin
(match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
bs
end
| Some (t) -> begin
(match ((let _194_958 = (FStar_Syntax_Subst.compress t)
in _194_958.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', _92_1580) -> begin
(match ((FStar_Util.prefix_until (fun _92_9 -> (match (_92_9) with
| (_92_1585, Some (FStar_Syntax_Syntax.Implicit)) -> begin
false
end
| _92_1590 -> begin
true
end)) bs')) with
| None -> begin
bs
end
| Some ([], _92_1594, _92_1596) -> begin
bs
end
| Some (imps, _92_1601, _92_1603) -> begin
if (FStar_All.pipe_right imps (FStar_Util.for_all (fun _92_1609 -> (match (_92_1609) with
| (x, _92_1608) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end)))) then begin
(let r = (pos bs)
in (let imps = (FStar_All.pipe_right imps (FStar_List.map (fun _92_1613 -> (match (_92_1613) with
| (x, i) -> begin
((FStar_Syntax_Syntax.set_range_of_bv x r), i)
end))))
in (FStar_List.append imps bs)))
end else begin
bs
end
end)
end
| _92_1616 -> begin
bs
end)
end)
end)))




