
open Prims
let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _196_6 = (FStar_TypeChecker_Env.get_range env)
in (let _196_5 = (FStar_TypeChecker_Errors.failed_to_prove_specification errs)
in (FStar_TypeChecker_Errors.report _196_6 _196_5))))

let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _196_9 = (FStar_Syntax_Subst.compress t)
in _196_9.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_93_14) -> begin
true
end
| _93_17 -> begin
false
end))

let t_binders : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env -> (let _196_13 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right _196_13 (FStar_List.filter (fun _93_22 -> (match (_93_22) with
| (x, _93_21) -> begin
(is_type x.FStar_Syntax_Syntax.sort)
end))))))

let new_uvar_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun env k -> (let bs = if (FStar_ST.read FStar_Options.full_context_dependency) then begin
(FStar_TypeChecker_Env.all_binders env)
end else begin
(t_binders env)
end
in (let _196_18 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Rel.new_uvar _196_18 bs k))))

let new_uvar : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env k -> (let _196_23 = (new_uvar_aux env k)
in (Prims.fst _196_23)))

let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun _93_1 -> (match (_93_1) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, _93_37); FStar_Syntax_Syntax.tk = _93_34; FStar_Syntax_Syntax.pos = _93_32; FStar_Syntax_Syntax.vars = _93_30} -> begin
uv
end
| _93_42 -> begin
(FStar_All.failwith "Impossible")
end))

let new_implicit_var : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.uvar * FStar_Range.range) * FStar_TypeChecker_Env.guard_t) = (fun env k -> (let _93_47 = (new_uvar_aux env k)
in (match (_93_47) with
| (t, u) -> begin
(let g = (let _93_48 = FStar_TypeChecker_Rel.trivial_guard
in (let _196_32 = (let _196_31 = (let _196_30 = (as_uvar u)
in (env, _196_30, t, k, u.FStar_Syntax_Syntax.pos))
in (_196_31)::[])
in {FStar_TypeChecker_Env.guard_f = _93_48.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _93_48.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _93_48.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _196_32}))
in (let _196_34 = (let _196_33 = (as_uvar u)
in (_196_33, u.FStar_Syntax_Syntax.pos))
in (t, _196_34, g)))
end)))

let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun r t -> (let uvs = (FStar_Syntax_Free.uvars t)
in if (not ((FStar_Util.set_is_empty uvs))) then begin
(let us = (let _196_41 = (let _196_40 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun _93_57 -> (match (_93_57) with
| (x, _93_56) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) _196_40))
in (FStar_All.pipe_right _196_41 (FStar_String.concat ", ")))
in (let hide_uvar_nums_saved = (FStar_ST.read FStar_Options.hide_uvar_nums)
in (let print_implicits_saved = (FStar_ST.read FStar_Options.print_implicits)
in (let _93_61 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums false)
in (let _93_63 = (FStar_ST.op_Colon_Equals FStar_Options.print_implicits true)
in (let _93_65 = (let _196_43 = (let _196_42 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us _196_42))
in (FStar_TypeChecker_Errors.report r _196_43))
in (let _93_67 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums hide_uvar_nums_saved)
in (FStar_ST.op_Colon_Equals FStar_Options.print_implicits print_implicits_saved))))))))
end else begin
()
end))

let force_sort' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' = (fun s -> (match ((FStar_ST.read s.FStar_Syntax_Syntax.tk)) with
| None -> begin
(let _196_48 = (let _196_47 = (FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos)
in (let _196_46 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s" _196_47 _196_46)))
in (FStar_All.failwith _196_48))
end
| Some (tk) -> begin
tk
end))

let force_sort = (fun s -> (let _196_50 = (force_sort' s)
in (FStar_Syntax_Syntax.mk _196_50 None s.FStar_Syntax_Syntax.pos)))

let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env _93_82 -> (match (_93_82) with
| {FStar_Syntax_Syntax.lbname = _93_81; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _93_77; FStar_Syntax_Syntax.lbdef = e} -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _93_84 = if (univ_vars <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (let r = (FStar_TypeChecker_Env.get_range env)
in (let mk_binder = (fun scope a -> (match (a.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _93_94 = (FStar_Syntax_Util.type_u ())
in (match (_93_94) with
| (k, _93_93) -> begin
(let t = (let _196_59 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right _196_59 Prims.fst))
in ((let _93_96 = a
in {FStar_Syntax_Syntax.ppname = _93_96.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _93_96.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), false))
end))
end
| _93_99 -> begin
(a, true)
end))
in (let rec aux = (fun vars e -> (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, _93_105) -> begin
(aux vars e)
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _93_111) -> begin
(t, true)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _93_117) -> begin
(let _93_136 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _93_123 _93_126 -> (match ((_93_123, _93_126)) with
| ((scope, bs, check), (a, imp)) -> begin
(let _93_129 = (mk_binder scope a)
in (match (_93_129) with
| (tb, c) -> begin
(let b = (tb, imp)
in (let bs = (FStar_List.append bs ((b)::[]))
in (let scope = (FStar_List.append scope ((b)::[]))
in (scope, bs, (c || check)))))
end))
end)) (vars, [], false)))
in (match (_93_136) with
| (scope, bs, check) -> begin
(let _93_139 = (aux scope body)
in (match (_93_139) with
| (res, check_res) -> begin
(let c = (FStar_Syntax_Util.ml_comp res r)
in (let t = (FStar_Syntax_Util.arrow bs c)
in (let _93_142 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _196_67 = (FStar_Range.string_of_range r)
in (let _196_66 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _196_67 _196_66)))
end else begin
()
end
in (t, (check_res || check)))))
end))
end))
end
| _93_145 -> begin
(let _196_69 = (let _196_68 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _196_68 Prims.fst))
in (_196_69, false))
end))
in (let _93_148 = (let _196_70 = (t_binders env)
in (aux _196_70 e))
in (match (_93_148) with
| (t, b) -> begin
([], t, b)
end))))))
end
| _93_150 -> begin
(let _93_153 = (FStar_Syntax_Subst.open_univ_vars univ_vars t)
in (match (_93_153) with
| (univ_vars, t) -> begin
(univ_vars, t, false)
end))
end)
end))

let is_implicit : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _93_2 -> (match (_93_2) with
| Some (FStar_Syntax_Syntax.Implicit) -> begin
true
end
| _93_158 -> begin
false
end))

let as_imp : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _93_3 -> (match (_93_3) with
| Some (FStar_Syntax_Syntax.Implicit) -> begin
true
end
| _93_163 -> begin
false
end))

let pat_as_exps : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term Prims.list * FStar_Syntax_Syntax.pat) = (fun allow_implicits env p -> (let rec pat_as_arg_with_env = (fun allow_wc_dependence env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) None p.FStar_Syntax_Syntax.p)
in ([], [], [], env, e, p))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _93_176) -> begin
(let _93_182 = (FStar_Syntax_Util.type_u ())
in (match (_93_182) with
| (k, _93_181) -> begin
(let t = (new_uvar env k)
in (let x = (let _93_184 = x
in {FStar_Syntax_Syntax.ppname = _93_184.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _93_184.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (let _93_189 = (let _196_87 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _196_87 t))
in (match (_93_189) with
| (e, u) -> begin
(let p = (let _93_190 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, e)); FStar_Syntax_Syntax.ty = _93_190.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _93_190.FStar_Syntax_Syntax.p})
in ([], [], [], env, e, p))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(let _93_198 = (FStar_Syntax_Util.type_u ())
in (match (_93_198) with
| (t, _93_197) -> begin
(let x = (let _93_199 = x
in (let _196_88 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _93_199.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _93_199.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _196_88}))
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
(let _93_209 = (FStar_Syntax_Util.type_u ())
in (match (_93_209) with
| (t, _93_208) -> begin
(let x = (let _93_210 = x
in (let _196_89 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _93_210.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _93_210.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _196_89}))
in (let env = (FStar_TypeChecker_Env.push_bv env x)
in (let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in ((x)::[], (x)::[], [], env, e, p))))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(let _93_243 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _93_225 _93_228 -> (match ((_93_225, _93_228)) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(let _93_235 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_93_235) with
| (b', a', w', env, te, pat) -> begin
(let arg = if imp then begin
(FStar_Syntax_Syntax.iarg te)
end else begin
(FStar_Syntax_Syntax.as_arg te)
end
in ((b')::b, (a')::a, (w')::w, env, (arg)::args, ((pat, imp))::pats))
end))
end)) ([], [], [], env, [], [])))
in (match (_93_243) with
| (b, a, w, env, args, pats) -> begin
(let e = (let _196_96 = (let _196_95 = (let _196_94 = (let _196_93 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (let _196_92 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app _196_93 _196_92 None p.FStar_Syntax_Syntax.p)))
in (_196_94, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))
in FStar_Syntax_Syntax.Tm_meta (_196_95))
in (FStar_Syntax_Syntax.mk _196_96 None p.FStar_Syntax_Syntax.p))
in (let _196_99 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _196_98 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _196_97 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in (_196_99, _196_98, _196_97, env, e, (let _93_245 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _93_245.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _93_245.FStar_Syntax_Syntax.p}))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (_93_248) -> begin
(FStar_All.failwith "impossible")
end))
in (let rec elaborate_pat = (fun env p -> (let maybe_dot = (fun a r -> if allow_implicits then begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term ((a, FStar_Syntax_Syntax.tun))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end else begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var (a)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end)
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(let pats = (FStar_List.map (fun _93_262 -> (match (_93_262) with
| (p, imp) -> begin
(let _196_109 = (elaborate_pat env p)
in (_196_109, imp))
end)) pats)
in (let _93_267 = (FStar_TypeChecker_Env.lookup_datacon env (Prims.fst fv).FStar_Syntax_Syntax.v)
in (match (_93_267) with
| (_93_265, t) -> begin
(let _93_271 = (FStar_Syntax_Util.arrow_formals t)
in (match (_93_271) with
| (f, _93_270) -> begin
(let rec aux = (fun formals pats -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _93_282::_93_280) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v)))))
end
| (_93_288::_93_286, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun _93_294 -> (match (_93_294) with
| (t, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit) -> begin
(let a = (let _196_116 = (let _196_115 = (FStar_Syntax_Syntax.range_of_bv t)
in Some (_196_115))
in (FStar_Syntax_Syntax.new_bv _196_116 FStar_Syntax_Syntax.tun))
in (let r = (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v)
in (let _196_117 = (maybe_dot a r)
in (_196_117, true))))
end
| _93_300 -> begin
(let _196_121 = (let _196_120 = (let _196_119 = (let _196_118 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _196_118))
in (_196_119, (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v)))
in FStar_Syntax_Syntax.Error (_196_120))
in (Prims.raise _196_121))
end)
end))))
end
| (f::formals', (p, p_imp)::pats') -> begin
(match (f) with
| (_93_311, Some (FStar_Syntax_Syntax.Implicit)) when p_imp -> begin
(let _196_122 = (aux formals' pats')
in ((p, true))::_196_122)
end
| (_93_316, Some (FStar_Syntax_Syntax.Implicit)) -> begin
(let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (let p = (maybe_dot a (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v))
in (let _196_123 = (aux formals' pats)
in ((p, true))::_196_123)))
end
| (_93_323, imp) -> begin
(let _196_124 = (aux formals' pats')
in ((p, (as_imp imp)))::_196_124)
end)
end))
in (let _93_326 = p
in (let _196_127 = (let _196_126 = (let _196_125 = (aux f pats)
in (fv, _196_125))
in FStar_Syntax_Syntax.Pat_cons (_196_126))
in {FStar_Syntax_Syntax.v = _196_127; FStar_Syntax_Syntax.ty = _93_326.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _93_326.FStar_Syntax_Syntax.p})))
end))
end)))
end
| _93_329 -> begin
p
end)))
in (let one_pat = (fun allow_wc_dependence env p -> (let p = (elaborate_pat env p)
in (let _93_341 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_93_341) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))) with
| Some (x) -> begin
(let _196_136 = (let _196_135 = (let _196_134 = (FStar_TypeChecker_Errors.nonlinear_pattern_variable x)
in (_196_134, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_196_135))
in (Prims.raise _196_136))
end
| _93_345 -> begin
(b, a, w, arg, p)
end)
end))))
in (let top_level_pat_as_args = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_disj (q::pats) -> begin
(let _93_361 = (one_pat false env q)
in (match (_93_361) with
| (b, a, _93_358, te, q) -> begin
(let _93_376 = (FStar_List.fold_right (fun p _93_366 -> (match (_93_366) with
| (w, args, pats) -> begin
(let _93_372 = (one_pat false env p)
in (match (_93_372) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv FStar_Syntax_Syntax.bv_eq a a'))) then begin
(let _196_146 = (let _196_145 = (let _196_144 = (FStar_TypeChecker_Errors.disjunctive_pattern_vars a a')
in (let _196_143 = (FStar_TypeChecker_Env.get_range env)
in (_196_144, _196_143)))
in FStar_Syntax_Syntax.Error (_196_145))
in (Prims.raise _196_146))
end else begin
(let _196_148 = (let _196_147 = (FStar_Syntax_Syntax.as_arg arg)
in (_196_147)::args)
in ((FStar_List.append w' w), _196_148, (p)::pats))
end
end))
end)) pats ([], [], []))
in (match (_93_376) with
| (w, args, pats) -> begin
(let _196_150 = (let _196_149 = (FStar_Syntax_Syntax.as_arg te)
in (_196_149)::args)
in ((FStar_List.append b w), _196_150, (let _93_377 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((q)::pats); FStar_Syntax_Syntax.ty = _93_377.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _93_377.FStar_Syntax_Syntax.p})))
end))
end))
end
| _93_380 -> begin
(let _93_388 = (one_pat true env p)
in (match (_93_388) with
| (b, _93_383, _93_385, arg, p) -> begin
(let _196_152 = (let _196_151 = (FStar_Syntax_Syntax.as_arg arg)
in (_196_151)::[])
in (b, _196_152, p))
end))
end))
in (let _93_392 = (top_level_pat_as_args env p)
in (match (_93_392) with
| (b, args, p) -> begin
(let exps = (FStar_All.pipe_right args (FStar_List.map Prims.fst))
in (b, exps, p))
end)))))))

let decorate_pattern : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.pat = (fun env p exps -> (let qq = p
in (let rec aux = (fun p e -> (let pkg = (fun q t -> (FStar_Syntax_Syntax.withinfo q t p.FStar_Syntax_Syntax.p))
in (let e = (FStar_Syntax_Util.unmeta e)
in (match ((p.FStar_Syntax_Syntax.v, e.FStar_Syntax_Syntax.n)) with
| (_93_406, FStar_Syntax_Syntax.Tm_uinst (e, _93_409)) -> begin
(aux p e)
end
| (FStar_Syntax_Syntax.Pat_constant (_93_414), FStar_Syntax_Syntax.Tm_constant (_93_417)) -> begin
(let _196_167 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v _196_167))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(let _93_425 = if (not ((FStar_Syntax_Syntax.bv_eq x y))) then begin
(let _196_170 = (let _196_169 = (FStar_Syntax_Print.bv_to_string x)
in (let _196_168 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _196_169 _196_168)))
in (FStar_All.failwith _196_170))
end else begin
()
end
in (let _93_427 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _196_172 = (FStar_Syntax_Print.bv_to_string x)
in (let _196_171 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _196_172 _196_171)))
end else begin
()
end
in (let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (let x = (let _93_430 = x
in {FStar_Syntax_Syntax.ppname = _93_430.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _93_430.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x)) s.FStar_Syntax_Syntax.n)))))
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(let _93_438 = if (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation) then begin
(let _196_175 = (let _196_174 = (FStar_Syntax_Print.bv_to_string x)
in (let _196_173 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _196_174 _196_173)))
in (FStar_All.failwith _196_175))
end else begin
()
end
in (let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (let x = (let _93_441 = x
in {FStar_Syntax_Syntax.ppname = _93_441.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _93_441.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x)) s.FStar_Syntax_Syntax.n))))
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _93_446), _93_450) -> begin
(let s = (force_sort e)
in (let x = (let _93_453 = x
in {FStar_Syntax_Syntax.ppname = _93_453.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _93_453.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
(let _93_463 = if (not ((FStar_Syntax_Syntax.fv_eq fv fv'))) then begin
(let _196_176 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" (Prims.fst fv).FStar_Syntax_Syntax.v.FStar_Ident.str (Prims.fst fv').FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _196_176))
end else begin
()
end
in (let _196_177 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv', []))) _196_177)))
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
(let _93_506 = if (let _196_178 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right _196_178 Prims.op_Negation)) then begin
(let _196_179 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" (Prims.fst fv).FStar_Syntax_Syntax.v.FStar_Ident.str (Prims.fst fv').FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _196_179))
end else begin
()
end
in (let fv = fv'
in (let rec match_args = (fun matched_pats args argpats -> (match ((args, argpats)) with
| ([], []) -> begin
(let _196_186 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev matched_pats)))) _196_186))
end
| (arg::args, (argpat, _93_522)::argpats) -> begin
(match ((arg, argpat.FStar_Syntax_Syntax.v)) with
| ((e, Some (FStar_Syntax_Syntax.Implicit)), FStar_Syntax_Syntax.Pat_dot_term (_93_531)) -> begin
(let x = (let _196_187 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _196_187))
in (let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((e, imp), _93_540) -> begin
(let pat = (let _196_188 = (aux argpat e)
in (_196_188, (as_imp imp)))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _93_544 -> begin
(let _196_191 = (let _196_190 = (FStar_Syntax_Print.pat_to_string p)
in (let _196_189 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _196_190 _196_189)))
in (FStar_All.failwith _196_191))
end))
in (match_args [] args argpats))))
end
| _93_546 -> begin
(let _196_196 = (let _196_195 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (let _196_194 = (FStar_Syntax_Print.pat_to_string qq)
in (let _196_193 = (let _196_192 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right _196_192 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _196_195 _196_194 _196_193))))
in (FStar_All.failwith _196_196))
end))))
in (match ((p.FStar_Syntax_Syntax.v, exps)) with
| (FStar_Syntax_Syntax.Pat_disj (ps), _93_550) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(let ps = (FStar_List.map2 aux ps exps)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj (ps)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p))
end
| (_93_554, e::[]) -> begin
(aux p e)
end
| _93_559 -> begin
(FStar_All.failwith "Unexpected number of patterns")
end))))

let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (let topt = Some (pat.FStar_Syntax_Syntax.ty)
in (let mk = (fun f -> (FStar_Syntax_Syntax.mk f topt pat.FStar_Syntax_Syntax.p))
in (let pat_as_arg = (fun _93_567 -> (match (_93_567) with
| (p, i) -> begin
(let _93_570 = (decorated_pattern_as_term p)
in (match (_93_570) with
| (vars, te) -> begin
(let _196_204 = (let _196_203 = (FStar_Syntax_Syntax.as_implicit i)
in (te, _196_203))
in (vars, _196_204))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_93_572) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _196_205 = (mk (FStar_Syntax_Syntax.Tm_constant (c)))
in ([], _196_205))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(let _196_206 = (mk (FStar_Syntax_Syntax.Tm_name (x)))
in ((x)::[], _196_206))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(let _93_585 = (let _196_207 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _196_207 FStar_List.unzip))
in (match (_93_585) with
| (vars, args) -> begin
(let vars = (FStar_List.flatten vars)
in (let _196_211 = (let _196_210 = (let _196_209 = (let _196_208 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (_196_208, args))
in FStar_Syntax_Syntax.Tm_app (_196_209))
in (mk _196_210))
in (vars, _196_211)))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
([], e)
end)))))

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv Prims.option * FStar_Syntax_Syntax.lcomp)

let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (let _93_609 = (match (c.FStar_Syntax_Syntax.effect_args) with
| (wp, _93_598)::(wlp, _93_594)::[] -> begin
(wp, wlp)
end
| _93_602 -> begin
(let _196_217 = (let _196_216 = (let _196_215 = (FStar_List.map (fun _93_606 -> (match (_93_606) with
| (x, _93_605) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right _196_215 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str _196_216))
in (FStar_All.failwith _196_217))
end)
in (match (_93_609) with
| (wp, wlp) -> begin
(c.FStar_Syntax_Syntax.result_typ, wp, wlp)
end)))

let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (let _93_617 = (destruct_comp c)
in (match (_93_617) with
| (_93_614, wp, wlp) -> begin
(let _196_239 = (let _196_238 = (let _196_234 = (lift c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _196_234))
in (let _196_237 = (let _196_236 = (let _196_235 = (lift c.FStar_Syntax_Syntax.result_typ wlp)
in (FStar_Syntax_Syntax.as_arg _196_235))
in (_196_236)::[])
in (_196_238)::_196_237))
in {FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _196_239; FStar_Syntax_Syntax.flags = []})
end)))

let norm_eff_name : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (let cache = (FStar_Util.smap_create 20)
in (fun env l -> (let rec find = (fun l -> (match ((FStar_TypeChecker_Env.lookup_effect_abbrev env l)) with
| None -> begin
None
end
| Some (_93_625, c) -> begin
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
(let _93_639 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))

let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (let _93_650 = (let _196_253 = (norm_eff_name env l1)
in (let _196_252 = (norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _196_253 _196_252)))
in (match (_93_650) with
| (m, _93_647, _93_649) -> begin
m
end)))

let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> if ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2)) then begin
FStar_Syntax_Const.effect_Tot_lid
end else begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)

let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)) = (fun env c1 c2 -> (let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (let _93_662 = (FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (_93_662) with
| (m, lift1, lift2) -> begin
(let m1 = (lift_comp c1 m lift1)
in (let m2 = (lift_comp c2 m lift2)
in (let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (let _93_668 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (_93_668) with
| (a, kwp) -> begin
(let _196_267 = (destruct_comp m1)
in (let _196_266 = (destruct_comp m2)
in ((md, a, kwp), _196_267, _196_266)))
end)))))
end)))))

let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (let l = (norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)))

let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (let l = (norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid))))

let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md result wp wlp flags -> (let _196_290 = (let _196_289 = (let _196_288 = (FStar_Syntax_Syntax.as_arg wp)
in (let _196_287 = (let _196_286 = (FStar_Syntax_Syntax.as_arg wlp)
in (_196_286)::[])
in (_196_288)::_196_287))
in {FStar_Syntax_Syntax.effect_name = md.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = _196_289; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp _196_290)))

let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (let _93_682 = lc
in (let _196_297 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _93_682.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _196_297; FStar_Syntax_Syntax.cflags = _93_682.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _93_684 -> (match (()) with
| () -> begin
(let _196_296 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _196_296))
end))})))

let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _196_300 = (FStar_Syntax_Subst.compress t)
in _196_300.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_93_687) -> begin
true
end
| _93_690 -> begin
false
end))

let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v -> (let c = (match ((FStar_TypeChecker_Env.lookup_effect_abbrev env FStar_Syntax_Const.effect_GTot_lid)) with
| None -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| _93_696 -> begin
(let m = (let _196_307 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must _196_307))
in (let _93_700 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_93_700) with
| (a, kwp) -> begin
(let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (let wp = (let _196_313 = (let _196_312 = (FStar_TypeChecker_Env.inst_effect_fun env m m.FStar_Syntax_Syntax.ret)
in (let _196_311 = (let _196_310 = (FStar_Syntax_Syntax.as_arg t)
in (let _196_309 = (let _196_308 = (FStar_Syntax_Syntax.as_arg v)
in (_196_308)::[])
in (_196_310)::_196_309))
in (FStar_Syntax_Syntax.mk_Tm_app _196_312 _196_311 (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _196_313))
in (let wlp = wp
in (mk_comp m t wp wlp ((FStar_Syntax_Syntax.RETURN)::[])))))
end)))
end)
in (let _93_705 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return"))) then begin
(let _196_316 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _196_315 = (FStar_Syntax_Print.term_to_string v)
in (let _196_314 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _196_316 _196_315 _196_314))))
end else begin
()
end
in c)))

let bind : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun env e1opt lc1 _93_712 -> (match (_93_712) with
| (b, lc2) -> begin
(let _93_720 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let bstr = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _196_327 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (let _196_326 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _196_325 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" _196_327 _196_326 bstr _196_325)))))
end else begin
()
end
in (let bind_it = (fun _93_723 -> (match (()) with
| () -> begin
(let c1 = (lc1.FStar_Syntax_Syntax.comp ())
in (let c2 = (lc2.FStar_Syntax_Syntax.comp ())
in (let _93_729 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _196_334 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _196_333 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _196_332 = (FStar_Syntax_Print.comp_to_string c1)
in (let _196_331 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (let _196_330 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" _196_334 _196_333 _196_332 _196_331 _196_330))))))
end else begin
()
end
in (let try_simplify = (fun _93_732 -> (match (()) with
| () -> begin
(let aux = (fun _93_734 -> (match (()) with
| () -> begin
if (FStar_Syntax_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some ((c2, "trivial no binder"))
end
| Some (_93_737) -> begin
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
(let _196_340 = (let _196_339 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in (_196_339, "both gtot"))
in Some (_196_340))
end else begin
(match ((e1opt, b)) with
| (Some (e), Some (x)) -> begin
if ((FStar_Syntax_Util.is_total_comp c1) && (not ((FStar_Syntax_Syntax.is_null_bv x)))) then begin
(let _196_342 = (let _196_341 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT ((x, e)))::[]) c2)
in (_196_341, "substituted e"))
in Some (_196_342))
end else begin
(aux ())
end
end
| _93_745 -> begin
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
(let _93_763 = (lift_and_destruct env c1 c2)
in (match (_93_763) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(let bs = (match (b) with
| None -> begin
(let _196_343 = (FStar_Syntax_Syntax.null_binder t1)
in (_196_343)::[])
end
| Some (x) -> begin
(let _196_344 = (FStar_Syntax_Syntax.mk_binder x)
in (_196_344)::[])
end)
in (let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp None))
in (let wp_args = (let _196_359 = (FStar_Syntax_Syntax.as_arg t1)
in (let _196_358 = (let _196_357 = (FStar_Syntax_Syntax.as_arg t2)
in (let _196_356 = (let _196_355 = (FStar_Syntax_Syntax.as_arg wp1)
in (let _196_354 = (let _196_353 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _196_352 = (let _196_351 = (let _196_347 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg _196_347))
in (let _196_350 = (let _196_349 = (let _196_348 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _196_348))
in (_196_349)::[])
in (_196_351)::_196_350))
in (_196_353)::_196_352))
in (_196_355)::_196_354))
in (_196_357)::_196_356))
in (_196_359)::_196_358))
in (let wlp_args = (let _196_367 = (FStar_Syntax_Syntax.as_arg t1)
in (let _196_366 = (let _196_365 = (FStar_Syntax_Syntax.as_arg t2)
in (let _196_364 = (let _196_363 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _196_362 = (let _196_361 = (let _196_360 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _196_360))
in (_196_361)::[])
in (_196_363)::_196_362))
in (_196_365)::_196_364))
in (_196_367)::_196_366))
in (let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t2)))::[]) kwp)
in (let wp = (let _196_368 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _196_368 wp_args None t2.FStar_Syntax_Syntax.pos))
in (let wlp = (let _196_369 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.bind_wlp)
in (FStar_Syntax_Syntax.mk_Tm_app _196_369 wlp_args None t2.FStar_Syntax_Syntax.pos))
in (let c = (mk_comp md t2 wp wlp [])
in c))))))))
end))
end)))))
end))
in (let _196_370 = (join_lcomp env lc1 lc2)
in {FStar_Syntax_Syntax.eff_name = _196_370; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it})))
end))

let lift_formula : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t mk_wp mk_wlp f -> (let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (let _93_784 = (FStar_TypeChecker_Env.wp_signature env md_pure.FStar_Syntax_Syntax.mname)
in (match (_93_784) with
| (a, kwp) -> begin
(let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (let wp = (let _196_384 = (let _196_383 = (FStar_Syntax_Syntax.as_arg t)
in (let _196_382 = (let _196_381 = (FStar_Syntax_Syntax.as_arg f)
in (_196_381)::[])
in (_196_383)::_196_382))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wp _196_384 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (let wlp = (let _196_388 = (let _196_387 = (FStar_Syntax_Syntax.as_arg t)
in (let _196_386 = (let _196_385 = (FStar_Syntax_Syntax.as_arg f)
in (_196_385)::[])
in (_196_387)::_196_386))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wlp _196_388 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (mk_comp md_pure FStar_TypeChecker_Recheck.t_unit wp wlp []))))
end))))

let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((f, FStar_Syntax_Syntax.Meta_labeled ((reason, r, false))))) None f.FStar_Syntax_Syntax.pos))

let label_opt : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _196_412 = (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)
in (FStar_All.pipe_left Prims.op_Negation _196_412)) then begin
f
end else begin
(let _196_413 = (reason ())
in (label _196_413 r f))
end
end))

let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _93_804 = g
in (let _196_421 = (let _196_420 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_196_420))
in {FStar_TypeChecker_Env.guard_f = _196_421; FStar_TypeChecker_Env.deferred = _93_804.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _93_804.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _93_804.FStar_TypeChecker_Env.implicits}))
end))

let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| _93_815 -> begin
g2
end))

let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (let weaken = (fun _93_820 -> (match (()) with
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
in (let _93_829 = (destruct_comp c)
in (match (_93_829) with
| (res_t, wp, wlp) -> begin
(let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (let wp = (let _196_440 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.assume_p)
in (let _196_439 = (let _196_438 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _196_437 = (let _196_436 = (FStar_Syntax_Syntax.as_arg f)
in (let _196_435 = (let _196_434 = (FStar_Syntax_Syntax.as_arg wp)
in (_196_434)::[])
in (_196_436)::_196_435))
in (_196_438)::_196_437))
in (FStar_Syntax_Syntax.mk_Tm_app _196_440 _196_439 None wp.FStar_Syntax_Syntax.pos)))
in (let wlp = (let _196_447 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.assume_p)
in (let _196_446 = (let _196_445 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _196_444 = (let _196_443 = (FStar_Syntax_Syntax.as_arg f)
in (let _196_442 = (let _196_441 = (FStar_Syntax_Syntax.as_arg wlp)
in (_196_441)::[])
in (_196_443)::_196_442))
in (_196_445)::_196_444))
in (FStar_Syntax_Syntax.mk_Tm_app _196_447 _196_446 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp c.FStar_Syntax_Syntax.flags))))
end)))
end
end))
end))
in (let _93_833 = lc
in {FStar_Syntax_Syntax.eff_name = _93_833.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _93_833.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _93_833.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))

let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> if (FStar_TypeChecker_Rel.is_trivial g0) then begin
(lc, g0)
end else begin
(let _93_840 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _196_467 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _196_466 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _196_467 _196_466)))
end else begin
()
end
in (let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _93_4 -> (match (_93_4) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _93_846 -> begin
[]
end))))
in (let strengthen = (fun _93_849 -> (match (()) with
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
in (let xret = (let _196_472 = (let _196_471 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _196_471))
in (FStar_Syntax_Util.comp_set_flags _196_472 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (let lc = (bind env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), (FStar_Syntax_Util.lcomp_of_comp xret)))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (let _93_859 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _196_474 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _196_473 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _196_474 _196_473)))
end else begin
()
end
in (let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (let _93_865 = (destruct_comp c)
in (match (_93_865) with
| (res_t, wp, wlp) -> begin
(let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (let wp = (let _196_483 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.assert_p)
in (let _196_482 = (let _196_481 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _196_480 = (let _196_479 = (let _196_476 = (let _196_475 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason _196_475 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _196_476))
in (let _196_478 = (let _196_477 = (FStar_Syntax_Syntax.as_arg wp)
in (_196_477)::[])
in (_196_479)::_196_478))
in (_196_481)::_196_480))
in (FStar_Syntax_Syntax.mk_Tm_app _196_483 _196_482 None wp.FStar_Syntax_Syntax.pos)))
in (let wlp = (let _196_490 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.assume_p)
in (let _196_489 = (let _196_488 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _196_487 = (let _196_486 = (FStar_Syntax_Syntax.as_arg f)
in (let _196_485 = (let _196_484 = (FStar_Syntax_Syntax.as_arg wlp)
in (_196_484)::[])
in (_196_486)::_196_485))
in (_196_488)::_196_487))
in (FStar_Syntax_Syntax.mk_Tm_app _196_490 _196_489 None wlp.FStar_Syntax_Syntax.pos)))
in (let _93_869 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _196_491 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _196_491))
end else begin
()
end
in (let c2 = (mk_comp md res_t wp wlp flags)
in c2)))))
end)))))
end)))
end))
in (let _196_495 = (let _93_872 = lc
in (let _196_494 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _196_493 = if ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _196_492 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _196_492))) then begin
flags
end else begin
[]
end
in {FStar_Syntax_Syntax.eff_name = _196_494; FStar_Syntax_Syntax.res_typ = _93_872.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _196_493; FStar_Syntax_Syntax.comp = strengthen})))
in (_196_495, (let _93_874 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _93_874.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _93_874.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _93_874.FStar_TypeChecker_Env.implicits}))))))
end)

let record_application_site : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (let comp = (fun _93_880 -> (match (()) with
| () -> begin
(let c = (lc.FStar_Syntax_Syntax.comp ())
in (let res_t = (FStar_Syntax_Util.comp_result c)
in if (((FStar_Syntax_Util.is_trivial_wp c) || (let _196_504 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals _196_504 FStar_Syntax_Const.prims_lid))) || (FStar_Syntax_Syntax.is_teff res_t)) then begin
c
end else begin
(let g = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (FStar_TypeChecker_Recheck.t_unit)))
in (let _93_888 = (strengthen_precondition (Some ((fun _93_884 -> (match (()) with
| () -> begin
"push"
end)))) env e (FStar_Syntax_Util.lcomp_of_comp c) g)
in (match (_93_888) with
| (c, _93_887) -> begin
(let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (let xret = (let _196_512 = (FStar_TypeChecker_Env.inst_effect_fun env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _196_511 = (let _196_510 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _196_509 = (let _196_508 = (FStar_Syntax_Syntax.as_arg xexp)
in (_196_508)::[])
in (_196_510)::_196_509))
in (FStar_Syntax_Syntax.mk_Tm_app _196_512 _196_511 None res_t.FStar_Syntax_Syntax.pos)))
in (let xret_comp = (let _196_513 = (mk_comp md_pure res_t xret xret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _196_513))
in (let lc = (let _196_519 = (let _196_518 = (let _196_517 = (strengthen_precondition (Some ((fun _93_894 -> (match (()) with
| () -> begin
"pop"
end)))) env xexp xret_comp g)
in (FStar_All.pipe_left Prims.fst _196_517))
in (Some (x), _196_518))
in (bind env None c _196_519))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end)))
end))
end))
in (let _93_896 = lc
in {FStar_Syntax_Syntax.eff_name = _93_896.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _93_896.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _93_896.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = comp})))

let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env comp res_t -> (let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let y = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _93_906 = (let _196_527 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _196_526 = (FStar_Syntax_Syntax.bv_to_name y)
in (_196_527, _196_526)))
in (match (_93_906) with
| (xexp, yexp) -> begin
(let yret = (let _196_532 = (FStar_TypeChecker_Env.inst_effect_fun env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _196_531 = (let _196_530 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _196_529 = (let _196_528 = (FStar_Syntax_Syntax.as_arg yexp)
in (_196_528)::[])
in (_196_530)::_196_529))
in (FStar_Syntax_Syntax.mk_Tm_app _196_532 _196_531 None res_t.FStar_Syntax_Syntax.pos)))
in (let x_eq_y_yret = (let _196_540 = (FStar_TypeChecker_Env.inst_effect_fun env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _196_539 = (let _196_538 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _196_537 = (let _196_536 = (let _196_533 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _196_533))
in (let _196_535 = (let _196_534 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_196_534)::[])
in (_196_536)::_196_535))
in (_196_538)::_196_537))
in (FStar_Syntax_Syntax.mk_Tm_app _196_540 _196_539 None res_t.FStar_Syntax_Syntax.pos)))
in (let forall_y_x_eq_y_yret = (let _196_550 = (FStar_TypeChecker_Env.inst_effect_fun env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _196_549 = (let _196_548 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _196_547 = (let _196_546 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _196_545 = (let _196_544 = (let _196_543 = (let _196_542 = (let _196_541 = (FStar_Syntax_Syntax.mk_binder y)
in (_196_541)::[])
in (FStar_Syntax_Util.abs _196_542 x_eq_y_yret None))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _196_543))
in (_196_544)::[])
in (_196_546)::_196_545))
in (_196_548)::_196_547))
in (FStar_Syntax_Syntax.mk_Tm_app _196_550 _196_549 None res_t.FStar_Syntax_Syntax.pos)))
in (let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (let lc = (bind env None (FStar_Syntax_Util.lcomp_of_comp comp) (Some (x), (FStar_Syntax_Util.lcomp_of_comp lc2)))
in (lc.FStar_Syntax_Syntax.comp ()))))))
end))))))

let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (let comp = (fun _93_917 -> (match (()) with
| () -> begin
(let _93_933 = (let _196_562 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _196_561 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _196_562 _196_561)))
in (match (_93_933) with
| ((md, _93_920, _93_922), (res_t, wp_then, wlp_then), (_93_929, wp_else, wlp_else)) -> begin
(let ifthenelse = (fun md res_t g wp_t wp_e -> (let _196_582 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.if_then_else)
in (let _196_581 = (let _196_579 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _196_578 = (let _196_577 = (FStar_Syntax_Syntax.as_arg g)
in (let _196_576 = (let _196_575 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _196_574 = (let _196_573 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_196_573)::[])
in (_196_575)::_196_574))
in (_196_577)::_196_576))
in (_196_579)::_196_578))
in (let _196_580 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _196_582 _196_581 None _196_580)))))
in (let wp = (ifthenelse md res_t guard wp_then wp_else)
in (let wlp = (ifthenelse md res_t guard wlp_then wlp_else)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(let comp = (mk_comp md res_t wp wlp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(let wp = (let _196_589 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.ite_wp)
in (let _196_588 = (let _196_587 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _196_586 = (let _196_585 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _196_584 = (let _196_583 = (FStar_Syntax_Syntax.as_arg wp)
in (_196_583)::[])
in (_196_585)::_196_584))
in (_196_587)::_196_586))
in (FStar_Syntax_Syntax.mk_Tm_app _196_589 _196_588 None wp.FStar_Syntax_Syntax.pos)))
in (let wlp = (let _196_594 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _196_593 = (let _196_592 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _196_591 = (let _196_590 = (FStar_Syntax_Syntax.as_arg wlp)
in (_196_590)::[])
in (_196_592)::_196_591))
in (FStar_Syntax_Syntax.mk_Tm_app _196_594 _196_593 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end)))
end))
end))
in (let _196_595 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _196_595; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp})))

let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (let eff = (FStar_List.fold_left (fun eff _93_952 -> (match (_93_952) with
| (_93_950, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (let bind_cases = (fun _93_955 -> (match (()) with
| () -> begin
(let ifthenelse = (fun md res_t g wp_t wp_e -> (let _196_625 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.if_then_else)
in (let _196_624 = (let _196_622 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _196_621 = (let _196_620 = (FStar_Syntax_Syntax.as_arg g)
in (let _196_619 = (let _196_618 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _196_617 = (let _196_616 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_196_616)::[])
in (_196_618)::_196_617))
in (_196_620)::_196_619))
in (_196_622)::_196_621))
in (let _196_623 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _196_625 _196_624 None _196_623)))))
in (let default_case = (let post_k = (let _196_628 = (let _196_626 = (FStar_Syntax_Syntax.null_binder res_t)
in (_196_626)::[])
in (let _196_627 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _196_628 _196_627)))
in (let kwp = (let _196_631 = (let _196_629 = (FStar_Syntax_Syntax.null_binder post_k)
in (_196_629)::[])
in (let _196_630 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _196_631 _196_630)))
in (let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (let wp = (let _196_638 = (let _196_632 = (FStar_Syntax_Syntax.mk_binder post)
in (_196_632)::[])
in (let _196_637 = (let _196_636 = (let _196_633 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Errors.exhaustiveness_check _196_633))
in (let _196_635 = (let _196_634 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.false_lid _196_634))
in (FStar_All.pipe_left _196_636 _196_635)))
in (FStar_Syntax_Util.abs _196_638 _196_637 None)))
in (let wlp = (let _196_642 = (let _196_639 = (FStar_Syntax_Syntax.mk_binder post)
in (_196_639)::[])
in (let _196_641 = (let _196_640 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid _196_640))
in (FStar_Syntax_Util.abs _196_642 _196_641 None)))
in (let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (let comp = (FStar_List.fold_right (fun _93_971 celse -> (match (_93_971) with
| (g, cthen) -> begin
(let _93_989 = (let _196_645 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _196_645 celse))
in (match (_93_989) with
| ((md, _93_975, _93_977), (_93_980, wp_then, wlp_then), (_93_985, wp_else, wlp_else)) -> begin
(let _196_647 = (ifthenelse md res_t g wp_then wp_else)
in (let _196_646 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _196_647 _196_646 [])))
end))
end)) lcases default_case)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(add_equality_to_post_condition env comp res_t)
end else begin
(let comp = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (let md = (FStar_TypeChecker_Env.get_effect_decl env comp.FStar_Syntax_Syntax.effect_name)
in (let _93_997 = (destruct_comp comp)
in (match (_93_997) with
| (_93_994, wp, wlp) -> begin
(let wp = (let _196_654 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.ite_wp)
in (let _196_653 = (let _196_652 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _196_651 = (let _196_650 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _196_649 = (let _196_648 = (FStar_Syntax_Syntax.as_arg wp)
in (_196_648)::[])
in (_196_650)::_196_649))
in (_196_652)::_196_651))
in (FStar_Syntax_Syntax.mk_Tm_app _196_654 _196_653 None wp.FStar_Syntax_Syntax.pos)))
in (let wlp = (let _196_659 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _196_658 = (let _196_657 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _196_656 = (let _196_655 = (FStar_Syntax_Syntax.as_arg wlp)
in (_196_655)::[])
in (_196_657)::_196_656))
in (FStar_Syntax_Syntax.mk_Tm_app _196_659 _196_658 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end))))
end)))
end))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))

let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (let close = (fun _93_1004 -> (match (()) with
| () -> begin
(let c = (lc.FStar_Syntax_Syntax.comp ())
in if (FStar_Syntax_Util.is_ml_comp c) then begin
c
end else begin
(let close_wp = (fun md res_t bvs wp0 -> (FStar_List.fold_right (fun x wp -> (let bs = (let _196_678 = (FStar_Syntax_Syntax.mk_binder x)
in (_196_678)::[])
in (let wp = (FStar_Syntax_Util.abs bs wp None)
in (let _196_685 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.close_wp)
in (let _196_684 = (let _196_683 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _196_682 = (let _196_681 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _196_680 = (let _196_679 = (FStar_Syntax_Syntax.as_arg wp)
in (_196_679)::[])
in (_196_681)::_196_680))
in (_196_683)::_196_682))
in (FStar_Syntax_Syntax.mk_Tm_app _196_685 _196_684 None wp0.FStar_Syntax_Syntax.pos)))))) bvs wp0))
in (let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (let _93_1019 = (destruct_comp c)
in (match (_93_1019) with
| (t, wp, wlp) -> begin
(let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (let wp = (close_wp md c.FStar_Syntax_Syntax.result_typ bvs wp)
in (let wlp = (close_wp md c.FStar_Syntax_Syntax.result_typ bvs wlp)
in (mk_comp md c.FStar_Syntax_Syntax.result_typ wp wlp c.FStar_Syntax_Syntax.flags))))
end))))
end)
end))
in (let _93_1023 = lc
in {FStar_Syntax_Syntax.eff_name = _93_1023.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _93_1023.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _93_1023.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))

let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (let refine = (fun _93_1029 -> (match (()) with
| () -> begin
(let c = (lc.FStar_Syntax_Syntax.comp ())
in if (not ((is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name))) then begin
c
end else begin
if (FStar_Syntax_Util.is_partial_return c) then begin
c
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c) && (let _196_694 = (FStar_TypeChecker_Env.lookup_effect_abbrev env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left FStar_Option.isNone _196_694))) then begin
(let _196_697 = (let _196_696 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _196_695 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _196_696 _196_695)))
in (FStar_All.failwith _196_697))
end else begin
(let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (let t = c.FStar_Syntax_Syntax.result_typ
in (let c = (FStar_Syntax_Syntax.mk_Comp c)
in (let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (let ret = (let _196_699 = (let _196_698 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _196_698 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _196_699))
in (let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (let c = (let _196_701 = (let _196_700 = (bind env None (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), eq_ret))
in (_196_700.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _196_701 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
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
in (let _93_1041 = lc
in {FStar_Syntax_Syntax.eff_name = _93_1041.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _93_1041.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))

let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (match ((FStar_TypeChecker_Rel.sub_comp env c c')) with
| None -> begin
(let _196_713 = (let _196_712 = (let _196_711 = (FStar_TypeChecker_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _196_710 = (FStar_TypeChecker_Env.get_range env)
in (_196_711, _196_710)))
in FStar_Syntax_Syntax.Error (_196_712))
in (Prims.raise _196_713))
end
| Some (g) -> begin
(e, c', g)
end))

let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match ((let _196_722 = (FStar_Syntax_Subst.compress t)
in _196_722.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_93_1055) -> begin
(match ((let _196_723 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _196_723.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _93_1059) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.bool_lid) -> begin
(let _93_1062 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (let b2t = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos)
in (let lc = (let _196_726 = (let _196_725 = (let _196_724 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _196_724))
in (None, _196_725))
in (bind env (Some (e)) lc _196_726))
in (let e = (let _196_728 = (let _196_727 = (FStar_Syntax_Syntax.as_arg e)
in (_196_727)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _196_728 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (e, lc)))))
end
| _93_1068 -> begin
(e, lc)
end)
end
| _93_1070 -> begin
(e, lc)
end))

let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (let gopt = if env.FStar_TypeChecker_Env.use_eq then begin
(let _196_737 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in (_196_737, false))
end else begin
(let _196_738 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in (_196_738, true))
end
in (match (gopt) with
| (None, _93_1078) -> begin
(FStar_TypeChecker_Rel.subtype_fail env lc.FStar_Syntax_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(match ((FStar_TypeChecker_Rel.guard_form g)) with
| FStar_TypeChecker_Common.Trivial -> begin
(let lc = (let _93_1085 = lc
in {FStar_Syntax_Syntax.eff_name = _93_1085.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _93_1085.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _93_1085.FStar_Syntax_Syntax.comp})
in (e, lc, g))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let g = (let _93_1090 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _93_1090.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _93_1090.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _93_1090.FStar_TypeChecker_Env.implicits})
in (let strengthen = (fun _93_1094 -> (match (()) with
| () -> begin
(let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (match ((let _196_741 = (FStar_Syntax_Subst.compress f)
in _196_741.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_93_1097, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _93_1106); FStar_Syntax_Syntax.tk = _93_1103; FStar_Syntax_Syntax.pos = _93_1101; FStar_Syntax_Syntax.vars = _93_1099}, _93_1111) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) -> begin
(let lc = (let _93_1114 = lc
in {FStar_Syntax_Syntax.eff_name = _93_1114.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _93_1114.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _93_1114.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| _93_1118 -> begin
(let c = (lc.FStar_Syntax_Syntax.comp ())
in (let _93_1120 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _196_745 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _196_744 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _196_743 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _196_742 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _196_745 _196_744 _196_743 _196_742)))))
end else begin
()
end
in (let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (let _93_1125 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_93_1125) with
| (a, kwp) -> begin
(let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (let md = (FStar_TypeChecker_Env.get_effect_decl env ct.FStar_Syntax_Syntax.effect_name)
in (let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (let wp = (let _196_750 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.ret)
in (let _196_749 = (let _196_748 = (FStar_Syntax_Syntax.as_arg t)
in (let _196_747 = (let _196_746 = (FStar_Syntax_Syntax.as_arg xexp)
in (_196_746)::[])
in (_196_748)::_196_747))
in (FStar_Syntax_Syntax.mk_Tm_app _196_750 _196_749 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)))
in (let cret = (let _196_751 = (mk_comp md t wp wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _196_751))
in (let guard = if apply_guard then begin
(let _196_753 = (let _196_752 = (FStar_Syntax_Syntax.as_arg xexp)
in (_196_752)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _196_753 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end else begin
f
end
in (let _93_1135 = (let _196_761 = (FStar_All.pipe_left (fun _196_758 -> Some (_196_758)) (FStar_TypeChecker_Errors.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _196_760 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _196_759 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _196_761 _196_760 e cret _196_759))))
in (match (_93_1135) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(let x = (let _93_1136 = x
in {FStar_Syntax_Syntax.ppname = _93_1136.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _93_1136.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (let c = (let _196_763 = (let _196_762 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _196_762))
in (bind env (Some (e)) _196_763 (Some (x), eq_ret)))
in (let c = (c.FStar_Syntax_Syntax.comp ())
in (let _93_1141 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _196_764 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _196_764))
end else begin
()
end
in c))))
end)))))))))
end)))))
end))
end))
in (let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _93_5 -> (match (_93_5) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _93_1147 -> begin
[]
end))))
in (let lc = (let _93_1149 = lc
in (let _196_766 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _196_766; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (let g = (let _93_1152 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _93_1152.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _93_1152.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _93_1152.FStar_TypeChecker_Env.implicits})
in (e, lc, g))))))
end)
end)))

let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (let mk_post_type = (fun res_t ens -> (let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _196_778 = (let _196_777 = (let _196_776 = (let _196_775 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _196_775))
in (_196_776)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _196_777 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _196_778))))
in (let norm = (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Unlabel)::[]) env t))
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
| (req, _93_1180)::(ens, _93_1175)::_93_1172 -> begin
(let _196_784 = (let _196_781 = (norm req)
in Some (_196_781))
in (let _196_783 = (let _196_782 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _196_782))
in (_196_784, _196_783)))
end
| _93_1184 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (wp, _93_1195)::(wlp, _93_1190)::_93_1187 -> begin
(let _93_1201 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (_93_1201) with
| (us_r, _93_1200) -> begin
(let _93_1205 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (_93_1205) with
| (us_e, _93_1204) -> begin
(let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (let as_req = (let _196_785 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.as_requires r)
in (FStar_Syntax_Syntax.mk_Tm_uinst _196_785 us_r))
in (let as_ens = (let _196_786 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.as_ensures r)
in (FStar_Syntax_Syntax.mk_Tm_uinst _196_786 us_e))
in (let req = (let _196_789 = (let _196_788 = (let _196_787 = (FStar_Syntax_Syntax.as_arg wp)
in (_196_787)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.Implicit)))::_196_788)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _196_789 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let ens = (let _196_792 = (let _196_791 = (let _196_790 = (FStar_Syntax_Syntax.as_arg wlp)
in (_196_790)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.Implicit)))::_196_791)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _196_792 None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _196_796 = (let _196_793 = (norm req)
in Some (_196_793))
in (let _196_795 = (let _196_794 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm _196_794))
in (_196_796, _196_795))))))))
end))
end))
end
| _93_1212 -> begin
(FStar_All.failwith "Impossible")
end))
end
end)
end)))

let maybe_instantiate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (let torig = (FStar_Syntax_Subst.compress t)
in if (not (env.FStar_TypeChecker_Env.instantiate_imp)) then begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end else begin
(match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _93_1223 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_93_1223) with
| (bs, c) -> begin
(let rec aux = (fun subst _93_6 -> (match (_93_6) with
| (x, Some (FStar_Syntax_Syntax.Implicit))::rest -> begin
(let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (let _93_1237 = (new_implicit_var env t)
in (match (_93_1237) with
| (v, u, g) -> begin
(let subst = (FStar_Syntax_Syntax.NT ((x, v)))::subst
in (let _93_1243 = (aux subst rest)
in (match (_93_1243) with
| (args, bs, subst, g') -> begin
(let _196_807 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((v, Some (FStar_Syntax_Syntax.Implicit)))::args, bs, subst, _196_807))
end)))
end)))
end
| bs -> begin
([], bs, subst, FStar_TypeChecker_Rel.trivial_guard)
end))
in (let _93_1249 = (aux [] bs)
in (match (_93_1249) with
| (args, bs, subst, guard) -> begin
(match ((args, bs)) with
| ([], _93_1252) -> begin
(e, torig, guard)
end
| (_93_1255, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end
| _93_1259 -> begin
(let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _93_1262 -> begin
(FStar_Syntax_Util.arrow bs c)
end)
in (let t = (FStar_Syntax_Subst.subst subst t)
in (let e = (FStar_Syntax_Syntax.mk_Tm_app e args (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (e, t, guard))))
end)
end)))
end))
end
| _93_1267 -> begin
(e, t, FStar_TypeChecker_Rel.trivial_guard)
end)
end))

let gen_univs : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe_uvar Prims.list * (FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.universe_uvar  ->  Prims.bool))  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(let s = (let _196_819 = (let _196_818 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _196_818))
in (FStar_All.pipe_right _196_819 FStar_Util.set_elements))
in (let r = (let _196_820 = (FStar_TypeChecker_Env.get_range env)
in Some (_196_820))
in (let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (let _93_1274 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _196_825 = (let _196_822 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _196_822))
in (let _196_824 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _196_823 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _196_825 _196_824 _196_823))))
end else begin
()
end
in (let _93_1276 = (FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))))
in u_name))))))
in u_names)))
end)

let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t -> (let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (let univs = (FStar_Syntax_Free.univs t)
in (let _93_1284 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _196_834 = (let _196_833 = (let _196_832 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _196_832 (FStar_List.map (fun u -> (let _196_831 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _196_831 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _196_833 (FStar_String.concat ", ")))
in (FStar_Util.print1 "univs to gen : %s\n" _196_834))
end else begin
()
end
in (let gen = (gen_univs env univs)
in (let _93_1287 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _196_835 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _196_835))
end else begin
()
end
in (let ts = (FStar_Syntax_Subst.close_univ_vars gen t)
in (gen, ts))))))))

let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> if (let _196_841 = (FStar_Util.for_all (fun _93_1295 -> (match (_93_1295) with
| (_93_1293, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _196_841)) then begin
None
end else begin
(let norm = (fun c -> (let _93_1298 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _196_844 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _196_844))
end else begin
()
end
in (let c = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.Eta)::[]) env c)
end else begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env c)
end
in (let _93_1301 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _196_845 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _196_845))
end else begin
()
end
in c))))
in (let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (let gen_uvars = (fun uvs -> (let _196_848 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _196_848 FStar_Util.set_elements)))
in (let _93_1318 = (let _196_850 = (FStar_All.pipe_right ecs (FStar_List.map (fun _93_1308 -> (match (_93_1308) with
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
in (FStar_All.pipe_right _196_850 FStar_List.unzip))
in (match (_93_1318) with
| (univs, uvars) -> begin
(let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (let gen_univs = (gen_univs env univs)
in (let _93_1322 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end else begin
()
end
in (let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _93_1327 -> (match (_93_1327) with
| (uvs, e, c) -> begin
(let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _93_1330 -> (match (_93_1330) with
| (u, k) -> begin
(match ((FStar_Unionfind.find u)) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(a, Some (FStar_Syntax_Syntax.Implicit))
end
| FStar_Syntax_Syntax.Fixed (_93_1364) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _93_1367 -> begin
(let _93_1370 = (FStar_Syntax_Util.arrow_formals k)
in (match (_93_1370) with
| (bs, kres) -> begin
(let a = (let _196_856 = (let _196_855 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _196_854 -> Some (_196_854)) _196_855))
in (FStar_Syntax_Syntax.new_bv _196_856 kres))
in (let t = (let _196_860 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _196_859 = (let _196_858 = (let _196_857 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _196_857))
in Some (_196_858))
in (FStar_Syntax_Util.abs bs _196_860 _196_859)))
in (let _93_1373 = (FStar_Syntax_Util.set_uvar u t)
in (a, Some (FStar_Syntax_Syntax.Implicit)))))
end))
end)
end))))
in (let _93_1394 = (match (tvars) with
| [] -> begin
(e, c)
end
| _93_1378 -> begin
(let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]) env c)
in (let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]) env e)
in (let t = (match ((let _196_861 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _196_861.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(let _93_1387 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (_93_1387) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| _93_1389 -> begin
(FStar_Syntax_Util.arrow tvars c)
end)
in (let e' = (FStar_Syntax_Util.abs tvars e None)
in (let _196_862 = (FStar_Syntax_Syntax.mk_Total t)
in (e', _196_862))))))
end)
in (match (_93_1394) with
| (e, c) -> begin
(gen_univs, e, c)
end)))
end))))
in Some (ecs)))))
end)))))
end)

let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> (let _93_1404 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _196_869 = (let _196_868 = (FStar_List.map (fun _93_1403 -> (match (_93_1403) with
| (lb, _93_1400, _93_1402) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _196_868 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _196_869))
end else begin
()
end
in (match ((let _196_871 = (FStar_All.pipe_right lecs (FStar_List.map (fun _93_1410 -> (match (_93_1410) with
| (_93_1407, e, c) -> begin
(e, c)
end))))
in (gen env _196_871))) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun _93_1415 -> (match (_93_1415) with
| (l, t, c) -> begin
(l, [], t, c)
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _93_1423 _93_1427 -> (match ((_93_1423, _93_1427)) with
| ((l, _93_1420, _93_1422), (us, e, c)) -> begin
(let _93_1428 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _196_877 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _196_876 = (FStar_Syntax_Print.lbname_to_string l)
in (let _196_875 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.print3 "(%s) Generalized %s to %s\n" _196_877 _196_876 _196_875))))
end else begin
()
end
in (l, us, e, c))
end)) lecs ecs)
end)))

let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let check = (fun env t1 t2 -> if env.FStar_TypeChecker_Env.use_eq then begin
(FStar_TypeChecker_Rel.try_teq env t1 t2)
end else begin
(match ((FStar_TypeChecker_Rel.try_subtype env t1 t2)) with
| None -> begin
None
end
| Some (f) -> begin
(let _196_893 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _196_892 -> Some (_196_892)) _196_893))
end)
end)
in (let is_var = (fun e -> (match ((let _196_896 = (FStar_Syntax_Subst.compress e)
in _196_896.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (_93_1445) -> begin
true
end
| _93_1448 -> begin
false
end))
in (let decorate = (fun e t -> (let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((let _93_1455 = x
in {FStar_Syntax_Syntax.ppname = _93_1455.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _93_1455.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| _93_1458 -> begin
(let _93_1459 = e
in (let _196_901 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _93_1459.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _196_901; FStar_Syntax_Syntax.pos = _93_1459.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _93_1459.FStar_Syntax_Syntax.vars}))
end)))
in (let env = (let _93_1461 = env
in (let _196_902 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _93_1461.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _93_1461.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _93_1461.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _93_1461.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _93_1461.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _93_1461.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _93_1461.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _93_1461.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _93_1461.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _93_1461.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _93_1461.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _93_1461.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _93_1461.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _93_1461.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _93_1461.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _196_902; FStar_TypeChecker_Env.is_iface = _93_1461.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _93_1461.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _93_1461.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _93_1461.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _93_1461.FStar_TypeChecker_Env.use_bv_sorts}))
in (match ((check env t1 t2)) with
| None -> begin
(let _196_906 = (let _196_905 = (let _196_904 = (FStar_TypeChecker_Errors.expected_expression_of_type env t2 e t1)
in (let _196_903 = (FStar_TypeChecker_Env.get_range env)
in (_196_904, _196_903)))
in FStar_Syntax_Syntax.Error (_196_905))
in (Prims.raise _196_906))
end
| Some (g) -> begin
(let _93_1467 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _196_907 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _196_907))
end else begin
()
end
in (let _196_908 = (decorate e t2)
in (_196_908, g)))
end)))))))

let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (let discharge = (fun g -> (let _93_1474 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _196_918 = (discharge g)
in (let _196_917 = (lc.FStar_Syntax_Syntax.comp ())
in (_196_918, _196_917)))
end else begin
(let c = (lc.FStar_Syntax_Syntax.comp ())
in (let steps = (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.DeltaComp)::[]
in (let c = (let _196_919 = (FStar_TypeChecker_Normalize.normalize_comp steps env c)
in (FStar_All.pipe_right _196_919 FStar_Syntax_Util.comp_to_comp_typ))
in (let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (let _93_1485 = (destruct_comp c)
in (match (_93_1485) with
| (t, wp, _93_1484) -> begin
(let vc = (let _196_925 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.trivial)
in (let _196_924 = (let _196_922 = (FStar_Syntax_Syntax.as_arg t)
in (let _196_921 = (let _196_920 = (FStar_Syntax_Syntax.as_arg wp)
in (_196_920)::[])
in (_196_922)::_196_921))
in (let _196_923 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk_Tm_app _196_925 _196_924 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _196_923))))
in (let _93_1487 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _196_926 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _196_926))
end else begin
()
end
in (let g = (let _196_927 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _196_927))
in (let _196_929 = (discharge g)
in (let _196_928 = (FStar_Syntax_Syntax.mk_Comp c)
in (_196_929, _196_928))))))
end))))))
end)))

let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (let short_bin_op = (fun f _93_7 -> (match (_93_7) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (fst, _93_1498)::[] -> begin
(f fst)
end
| _93_1502 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (let op_and_e = (fun e -> (let _196_950 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _196_950 (fun _196_949 -> FStar_TypeChecker_Common.NonTrivial (_196_949)))))
in (let op_or_e = (fun e -> (let _196_955 = (let _196_953 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _196_953))
in (FStar_All.pipe_right _196_955 (fun _196_954 -> FStar_TypeChecker_Common.NonTrivial (_196_954)))))
in (let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _196_958 -> FStar_TypeChecker_Common.NonTrivial (_196_958))))
in (let op_or_t = (fun t -> (let _196_962 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _196_962 (fun _196_961 -> FStar_TypeChecker_Common.NonTrivial (_196_961)))))
in (let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _196_965 -> FStar_TypeChecker_Common.NonTrivial (_196_965))))
in (let short_op_ite = (fun _93_8 -> (match (_93_8) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (guard, _93_1517)::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| _then::(guard, _93_1522)::[] -> begin
(let _196_969 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _196_969 (fun _196_968 -> FStar_TypeChecker_Common.NonTrivial (_196_968))))
end
| _93_1527 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (let table = ((FStar_Syntax_Const.op_And, (short_bin_op op_and_e)))::((FStar_Syntax_Const.op_Or, (short_bin_op op_or_e)))::((FStar_Syntax_Const.and_lid, (short_bin_op op_and_t)))::((FStar_Syntax_Const.or_lid, (short_bin_op op_or_t)))::((FStar_Syntax_Const.imp_lid, (short_bin_op op_imp_t)))::((FStar_Syntax_Const.ite_lid, short_op_ite))::[]
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _93_1532) -> begin
(let lid = fv.FStar_Syntax_Syntax.v
in (match ((FStar_Util.find_map table (fun _93_1538 -> (match (_93_1538) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _196_1002 = (mk seen_args)
in Some (_196_1002))
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
| _93_1543 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))

let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (match ((let _196_1005 = (FStar_Syntax_Subst.compress l)
in _196_1005.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (v, _93_1547) -> begin
(FStar_Util.for_some (FStar_Ident.lid_equals v.FStar_Syntax_Syntax.v) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| _93_1551 -> begin
false
end))

let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (let pos = (fun bs -> (match (bs) with
| (hd, _93_1560)::_93_1557 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| _93_1564 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| (_93_1568, Some (FStar_Syntax_Syntax.Implicit))::_93_1566 -> begin
bs
end
| _93_1574 -> begin
(match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
bs
end
| Some (t) -> begin
(match ((let _196_1012 = (FStar_Syntax_Subst.compress t)
in _196_1012.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', _93_1580) -> begin
(match ((FStar_Util.prefix_until (fun _93_9 -> (match (_93_9) with
| (_93_1585, Some (FStar_Syntax_Syntax.Implicit)) -> begin
false
end
| _93_1590 -> begin
true
end)) bs')) with
| None -> begin
bs
end
| Some ([], _93_1594, _93_1596) -> begin
bs
end
| Some (imps, _93_1601, _93_1603) -> begin
if (FStar_All.pipe_right imps (FStar_Util.for_all (fun _93_1609 -> (match (_93_1609) with
| (x, _93_1608) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end)))) then begin
(let r = (pos bs)
in (let imps = (FStar_All.pipe_right imps (FStar_List.map (fun _93_1613 -> (match (_93_1613) with
| (x, i) -> begin
(let _196_1016 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in (_196_1016, i))
end))))
in (FStar_List.append imps bs)))
end else begin
bs
end
end)
end
| _93_1616 -> begin
bs
end)
end)
end)))




