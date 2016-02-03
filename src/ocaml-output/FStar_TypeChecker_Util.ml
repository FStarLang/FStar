
open Prims
let report = (fun env errs -> (let _179_6 = (FStar_TypeChecker_Env.get_range env)
in (let _179_5 = (FStar_TypeChecker_Errors.failed_to_prove_specification errs)
in (FStar_TypeChecker_Errors.report _179_6 _179_5))))

let is_type = (fun t -> (match ((let _179_9 = (FStar_Syntax_Subst.compress t)
in _179_9.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_88_14) -> begin
true
end
| _88_17 -> begin
false
end))

let t_binders = (fun env -> (let _179_13 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right _179_13 (FStar_List.filter (fun _88_22 -> (match (_88_22) with
| (x, _88_21) -> begin
(is_type x.FStar_Syntax_Syntax.sort)
end))))))

let new_uvar_aux = (fun env k -> (let bs = if (FStar_ST.read FStar_Options.full_context_dependency) then begin
(FStar_TypeChecker_Env.all_binders env)
end else begin
(t_binders env)
end
in (let _179_18 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Rel.new_uvar _179_18 bs k))))

let new_uvar = (fun env k -> (let _179_23 = (new_uvar_aux env k)
in (Prims.fst _179_23)))

let as_uvar = (fun _88_1 -> (match (_88_1) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, _88_37); FStar_Syntax_Syntax.tk = _88_34; FStar_Syntax_Syntax.pos = _88_32; FStar_Syntax_Syntax.vars = _88_30} -> begin
uv
end
| _88_42 -> begin
(FStar_All.failwith "Impossible")
end))

let new_implicit_var = (fun env k -> (let _88_47 = (new_uvar_aux env k)
in (match (_88_47) with
| (t, u) -> begin
(let g = (let _88_48 = FStar_TypeChecker_Rel.trivial_guard
in (let _179_32 = (let _179_31 = (let _179_30 = (as_uvar u)
in (env, _179_30, t, k, u.FStar_Syntax_Syntax.pos))
in (_179_31)::[])
in {FStar_TypeChecker_Env.guard_f = _88_48.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _88_48.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _88_48.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _179_32}))
in (let _179_34 = (let _179_33 = (as_uvar u)
in (_179_33, u.FStar_Syntax_Syntax.pos))
in (t, _179_34, g)))
end)))

let check_uvars = (fun r t -> (let uvs = (FStar_Syntax_Free.uvars t)
in if (not ((FStar_Util.set_is_empty uvs))) then begin
(let us = (let _179_41 = (let _179_40 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun _88_57 -> (match (_88_57) with
| (x, _88_56) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) _179_40))
in (FStar_All.pipe_right _179_41 (FStar_String.concat ", ")))
in (let hide_uvar_nums_saved = (FStar_ST.read FStar_Options.hide_uvar_nums)
in (let print_implicits_saved = (FStar_ST.read FStar_Options.print_implicits)
in (let _88_61 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums false)
in (let _88_63 = (FStar_ST.op_Colon_Equals FStar_Options.print_implicits true)
in (let _88_65 = (let _179_43 = (let _179_42 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us _179_42))
in (FStar_TypeChecker_Errors.report r _179_43))
in (let _88_67 = (FStar_ST.op_Colon_Equals FStar_Options.hide_uvar_nums hide_uvar_nums_saved)
in (FStar_ST.op_Colon_Equals FStar_Options.print_implicits print_implicits_saved))))))))
end else begin
()
end))

let force_sort' = (fun s -> (match ((FStar_ST.read s.FStar_Syntax_Syntax.tk)) with
| None -> begin
(let _179_48 = (let _179_47 = (FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos)
in (let _179_46 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s" _179_47 _179_46)))
in (FStar_All.failwith _179_48))
end
| Some (tk) -> begin
tk
end))

let force_sort = (fun s -> (let _179_50 = (force_sort' s)
in (FStar_Syntax_Syntax.mk _179_50 None s.FStar_Syntax_Syntax.pos)))

let extract_let_rec_annotation = (fun env _88_82 -> (match (_88_82) with
| {FStar_Syntax_Syntax.lbname = _88_81; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _88_77; FStar_Syntax_Syntax.lbdef = e} -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _88_84 = if (univ_vars <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (let r = (FStar_TypeChecker_Env.get_range env)
in (let mk_binder = (fun scope a -> (match (a.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(let _88_94 = (FStar_Syntax_Util.type_u ())
in (match (_88_94) with
| (k, _88_93) -> begin
(let t = (let _179_59 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right _179_59 Prims.fst))
in ((let _88_96 = a
in {FStar_Syntax_Syntax.ppname = _88_96.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _88_96.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), false))
end))
end
| _88_99 -> begin
(a, true)
end))
in (let rec aux = (fun vars e -> (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, _88_105) -> begin
(aux vars e)
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _88_111) -> begin
(t, true)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _88_117) -> begin
(let _88_136 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _88_123 _88_126 -> (match ((_88_123, _88_126)) with
| ((scope, bs, check), (a, imp)) -> begin
(let _88_129 = (mk_binder scope a)
in (match (_88_129) with
| (tb, c) -> begin
(let b = (tb, imp)
in (let bs = (FStar_List.append bs ((b)::[]))
in (let scope = (FStar_List.append scope ((b)::[]))
in (scope, bs, (c || check)))))
end))
end)) (vars, [], false)))
in (match (_88_136) with
| (scope, bs, check) -> begin
(let _88_139 = (aux scope body)
in (match (_88_139) with
| (res, check_res) -> begin
(let c = (FStar_Syntax_Util.ml_comp res r)
in (let t = (FStar_Syntax_Util.arrow bs c)
in (let _88_142 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _179_67 = (FStar_Range.string_of_range r)
in (let _179_66 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _179_67 _179_66)))
end else begin
()
end
in (t, (check_res || check)))))
end))
end))
end
| _88_145 -> begin
(let _179_69 = (let _179_68 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _179_68 Prims.fst))
in (_179_69, false))
end))
in (let _88_148 = (let _179_70 = (t_binders env)
in (aux _179_70 e))
in (match (_88_148) with
| (t, b) -> begin
([], t, b)
end))))))
end
| _88_150 -> begin
(let _88_153 = (FStar_Syntax_Subst.open_univ_vars univ_vars t)
in (match (_88_153) with
| (univ_vars, t) -> begin
(univ_vars, t, false)
end))
end)
end))

let is_implicit = (fun _88_2 -> (match (_88_2) with
| Some (FStar_Syntax_Syntax.Implicit) -> begin
true
end
| _88_158 -> begin
false
end))

let as_imp = (fun _88_3 -> (match (_88_3) with
| Some (FStar_Syntax_Syntax.Implicit) -> begin
true
end
| _88_163 -> begin
false
end))

let pat_as_exps = (fun allow_implicits env p -> (let rec pat_as_arg_with_env = (fun allow_wc_dependence env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) None p.FStar_Syntax_Syntax.p)
in ([], [], [], env, e, p))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _88_176) -> begin
(let _88_182 = (FStar_Syntax_Util.type_u ())
in (match (_88_182) with
| (k, _88_181) -> begin
(let t = (new_uvar env k)
in (let x = (let _88_184 = x
in {FStar_Syntax_Syntax.ppname = _88_184.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _88_184.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (let _88_189 = (let _179_87 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _179_87 t))
in (match (_88_189) with
| (e, u) -> begin
(let p = (let _88_190 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, e)); FStar_Syntax_Syntax.ty = _88_190.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _88_190.FStar_Syntax_Syntax.p})
in ([], [], [], env, e, p))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(let _88_198 = (FStar_Syntax_Util.type_u ())
in (match (_88_198) with
| (t, _88_197) -> begin
(let x = (let _88_199 = x
in (let _179_88 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _88_199.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _88_199.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _179_88}))
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
(let _88_209 = (FStar_Syntax_Util.type_u ())
in (match (_88_209) with
| (t, _88_208) -> begin
(let x = (let _88_210 = x
in (let _179_89 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _88_210.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _88_210.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _179_89}))
in (let env = (FStar_TypeChecker_Env.push_bv env x)
in (let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in ((x)::[], (x)::[], [], env, e, p))))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(let _88_243 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _88_225 _88_228 -> (match ((_88_225, _88_228)) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(let _88_235 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_88_235) with
| (b', a', w', env, te, pat) -> begin
(let arg = if imp then begin
(FStar_Syntax_Syntax.iarg te)
end else begin
(FStar_Syntax_Syntax.as_arg te)
end
in ((b')::b, (a')::a, (w')::w, env, (arg)::args, ((pat, imp))::pats))
end))
end)) ([], [], [], env, [], [])))
in (match (_88_243) with
| (b, a, w, env, args, pats) -> begin
(let e = (let _179_96 = (let _179_95 = (let _179_94 = (let _179_93 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (let _179_92 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app _179_93 _179_92 None p.FStar_Syntax_Syntax.p)))
in (_179_94, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))
in FStar_Syntax_Syntax.Tm_meta (_179_95))
in (FStar_Syntax_Syntax.mk _179_96 None p.FStar_Syntax_Syntax.p))
in (let _179_99 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _179_98 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _179_97 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in (_179_99, _179_98, _179_97, env, e, (let _88_245 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _88_245.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _88_245.FStar_Syntax_Syntax.p}))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (_88_248) -> begin
(FStar_All.failwith "impossible")
end))
in (let rec elaborate_pat = (fun env p -> (let maybe_dot = (fun a r -> if allow_implicits then begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term ((a, FStar_Syntax_Syntax.tun))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end else begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var (a)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end)
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(let pats = (FStar_List.map (fun _88_262 -> (match (_88_262) with
| (p, imp) -> begin
(let _179_109 = (elaborate_pat env p)
in (_179_109, imp))
end)) pats)
in (let _88_267 = (FStar_TypeChecker_Env.lookup_datacon env (Prims.fst fv).FStar_Syntax_Syntax.v)
in (match (_88_267) with
| (_88_265, t) -> begin
(let _88_271 = (FStar_Syntax_Util.arrow_formals t)
in (match (_88_271) with
| (f, _88_270) -> begin
(let rec aux = (fun formals pats -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], _88_282::_88_280) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v)))))
end
| (_88_288::_88_286, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun _88_294 -> (match (_88_294) with
| (t, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit) -> begin
(let a = (let _179_116 = (let _179_115 = (FStar_Syntax_Syntax.range_of_bv t)
in Some (_179_115))
in (FStar_Syntax_Syntax.new_bv _179_116 FStar_Syntax_Syntax.tun))
in (let r = (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v)
in (let _179_117 = (maybe_dot a r)
in (_179_117, true))))
end
| _88_300 -> begin
(let _179_121 = (let _179_120 = (let _179_119 = (let _179_118 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _179_118))
in (_179_119, (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v)))
in FStar_Syntax_Syntax.Error (_179_120))
in (Prims.raise _179_121))
end)
end))))
end
| (f::formals', (p, p_imp)::pats') -> begin
(match (f) with
| (_88_311, Some (FStar_Syntax_Syntax.Implicit)) when p_imp -> begin
(let _179_122 = (aux formals' pats')
in ((p, true))::_179_122)
end
| (_88_316, Some (FStar_Syntax_Syntax.Implicit)) -> begin
(let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (let p = (maybe_dot a (FStar_Ident.range_of_lid (Prims.fst fv).FStar_Syntax_Syntax.v))
in (let _179_123 = (aux formals' pats)
in ((p, true))::_179_123)))
end
| (_88_323, imp) -> begin
(let _179_124 = (aux formals' pats')
in ((p, (as_imp imp)))::_179_124)
end)
end))
in (let _88_326 = p
in (let _179_127 = (let _179_126 = (let _179_125 = (aux f pats)
in (fv, _179_125))
in FStar_Syntax_Syntax.Pat_cons (_179_126))
in {FStar_Syntax_Syntax.v = _179_127; FStar_Syntax_Syntax.ty = _88_326.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _88_326.FStar_Syntax_Syntax.p})))
end))
end)))
end
| _88_329 -> begin
p
end)))
in (let one_pat = (fun allow_wc_dependence env p -> (let p = (elaborate_pat env p)
in (let _88_341 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_88_341) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))) with
| Some (x) -> begin
(let _179_136 = (let _179_135 = (let _179_134 = (FStar_TypeChecker_Errors.nonlinear_pattern_variable x)
in (_179_134, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_179_135))
in (Prims.raise _179_136))
end
| _88_345 -> begin
(b, a, w, arg, p)
end)
end))))
in (let top_level_pat_as_args = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_disj (q::pats) -> begin
(let _88_361 = (one_pat false env q)
in (match (_88_361) with
| (b, a, _88_358, te, q) -> begin
(let _88_376 = (FStar_List.fold_right (fun p _88_366 -> (match (_88_366) with
| (w, args, pats) -> begin
(let _88_372 = (one_pat false env p)
in (match (_88_372) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv FStar_Syntax_Syntax.bv_eq a a'))) then begin
(let _179_146 = (let _179_145 = (let _179_144 = (FStar_TypeChecker_Errors.disjunctive_pattern_vars a a')
in (let _179_143 = (FStar_TypeChecker_Env.get_range env)
in (_179_144, _179_143)))
in FStar_Syntax_Syntax.Error (_179_145))
in (Prims.raise _179_146))
end else begin
(let _179_148 = (let _179_147 = (FStar_Syntax_Syntax.as_arg arg)
in (_179_147)::args)
in ((FStar_List.append w' w), _179_148, (p)::pats))
end
end))
end)) pats ([], [], []))
in (match (_88_376) with
| (w, args, pats) -> begin
(let _179_150 = (let _179_149 = (FStar_Syntax_Syntax.as_arg te)
in (_179_149)::args)
in ((FStar_List.append b w), _179_150, (let _88_377 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((q)::pats); FStar_Syntax_Syntax.ty = _88_377.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _88_377.FStar_Syntax_Syntax.p})))
end))
end))
end
| _88_380 -> begin
(let _88_388 = (one_pat true env p)
in (match (_88_388) with
| (b, _88_383, _88_385, arg, p) -> begin
(let _179_152 = (let _179_151 = (FStar_Syntax_Syntax.as_arg arg)
in (_179_151)::[])
in (b, _179_152, p))
end))
end))
in (let _88_392 = (top_level_pat_as_args env p)
in (match (_88_392) with
| (b, args, p) -> begin
(let exps = (FStar_All.pipe_right args (FStar_List.map Prims.fst))
in (b, exps, p))
end)))))))

let decorate_pattern = (fun env p exps -> (let qq = p
in (let rec aux = (fun p e -> (let pkg = (fun q t -> (FStar_Syntax_Syntax.withinfo q t p.FStar_Syntax_Syntax.p))
in (let e = (FStar_Syntax_Util.unmeta e)
in (match ((p.FStar_Syntax_Syntax.v, e.FStar_Syntax_Syntax.n)) with
| (_88_406, FStar_Syntax_Syntax.Tm_uinst (e, _88_409)) -> begin
(aux p e)
end
| (FStar_Syntax_Syntax.Pat_constant (_88_414), FStar_Syntax_Syntax.Tm_constant (_88_417)) -> begin
(let _179_167 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v _179_167))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(let _88_425 = if (not ((FStar_Syntax_Syntax.bv_eq x y))) then begin
(let _179_170 = (let _179_169 = (FStar_Syntax_Print.bv_to_string x)
in (let _179_168 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _179_169 _179_168)))
in (FStar_All.failwith _179_170))
end else begin
()
end
in (let _88_427 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _179_172 = (FStar_Syntax_Print.bv_to_string x)
in (let _179_171 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _179_172 _179_171)))
end else begin
()
end
in (let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (let x = (let _88_430 = x
in {FStar_Syntax_Syntax.ppname = _88_430.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _88_430.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x)) s.FStar_Syntax_Syntax.n)))))
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(let _88_438 = if (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation) then begin
(let _179_175 = (let _179_174 = (FStar_Syntax_Print.bv_to_string x)
in (let _179_173 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _179_174 _179_173)))
in (FStar_All.failwith _179_175))
end else begin
()
end
in (let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (let x = (let _88_441 = x
in {FStar_Syntax_Syntax.ppname = _88_441.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _88_441.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x)) s.FStar_Syntax_Syntax.n))))
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _88_446), _88_450) -> begin
(let s = (force_sort e)
in (let x = (let _88_453 = x
in {FStar_Syntax_Syntax.ppname = _88_453.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _88_453.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
(let _88_463 = if (not ((FStar_Syntax_Syntax.fv_eq fv fv'))) then begin
(let _179_176 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" (Prims.fst fv).FStar_Syntax_Syntax.v.FStar_Ident.str (Prims.fst fv').FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _179_176))
end else begin
()
end
in (let _179_177 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv', []))) _179_177)))
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
(let _88_506 = if (let _179_178 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right _179_178 Prims.op_Negation)) then begin
(let _179_179 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" (Prims.fst fv).FStar_Syntax_Syntax.v.FStar_Ident.str (Prims.fst fv').FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _179_179))
end else begin
()
end
in (let fv = fv'
in (let rec match_args = (fun matched_pats args argpats -> (match ((args, argpats)) with
| ([], []) -> begin
(let _179_186 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev matched_pats)))) _179_186))
end
| (arg::args, (argpat, _88_522)::argpats) -> begin
(match ((arg, argpat.FStar_Syntax_Syntax.v)) with
| ((e, Some (FStar_Syntax_Syntax.Implicit)), FStar_Syntax_Syntax.Pat_dot_term (_88_531)) -> begin
(let x = (let _179_187 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _179_187))
in (let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((e, imp), _88_540) -> begin
(let pat = (let _179_188 = (aux argpat e)
in (_179_188, (as_imp imp)))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _88_544 -> begin
(let _179_191 = (let _179_190 = (FStar_Syntax_Print.pat_to_string p)
in (let _179_189 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _179_190 _179_189)))
in (FStar_All.failwith _179_191))
end))
in (match_args [] args argpats))))
end
| _88_546 -> begin
(let _179_196 = (let _179_195 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (let _179_194 = (FStar_Syntax_Print.pat_to_string qq)
in (let _179_193 = (let _179_192 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right _179_192 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _179_195 _179_194 _179_193))))
in (FStar_All.failwith _179_196))
end))))
in (match ((p.FStar_Syntax_Syntax.v, exps)) with
| (FStar_Syntax_Syntax.Pat_disj (ps), _88_550) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(let ps = (FStar_List.map2 aux ps exps)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj (ps)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p))
end
| (_88_554, e::[]) -> begin
(aux p e)
end
| _88_559 -> begin
(FStar_All.failwith "Unexpected number of patterns")
end))))

let rec decorated_pattern_as_term = (fun pat -> (let topt = Some (pat.FStar_Syntax_Syntax.ty)
in (let mk = (fun f -> (FStar_Syntax_Syntax.mk f topt pat.FStar_Syntax_Syntax.p))
in (let pat_as_arg = (fun _88_567 -> (match (_88_567) with
| (p, i) -> begin
(let _88_570 = (decorated_pattern_as_term p)
in (match (_88_570) with
| (vars, te) -> begin
(let _179_204 = (let _179_203 = (FStar_Syntax_Syntax.as_implicit i)
in (te, _179_203))
in (vars, _179_204))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_88_572) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _179_205 = (mk (FStar_Syntax_Syntax.Tm_constant (c)))
in ([], _179_205))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(let _179_206 = (mk (FStar_Syntax_Syntax.Tm_name (x)))
in ((x)::[], _179_206))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(let _88_585 = (let _179_207 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _179_207 FStar_List.unzip))
in (match (_88_585) with
| (vars, args) -> begin
(let vars = (FStar_List.flatten vars)
in (let _179_211 = (let _179_210 = (let _179_209 = (let _179_208 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (_179_208, args))
in FStar_Syntax_Syntax.Tm_app (_179_209))
in (mk _179_210))
in (vars, _179_211)))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
([], e)
end)))))

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv Prims.option * FStar_Syntax_Syntax.lcomp)

let destruct_comp = (fun c -> (let _88_609 = (match (c.FStar_Syntax_Syntax.effect_args) with
| (wp, _88_598)::(wlp, _88_594)::[] -> begin
(wp, wlp)
end
| _88_602 -> begin
(let _179_217 = (let _179_216 = (let _179_215 = (FStar_List.map (fun _88_606 -> (match (_88_606) with
| (x, _88_605) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right _179_215 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str _179_216))
in (FStar_All.failwith _179_217))
end)
in (match (_88_609) with
| (wp, wlp) -> begin
(c.FStar_Syntax_Syntax.result_typ, wp, wlp)
end)))

let lift_comp = (fun c m lift -> (let _88_617 = (destruct_comp c)
in (match (_88_617) with
| (_88_614, wp, wlp) -> begin
(let _179_239 = (let _179_238 = (let _179_234 = (lift c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _179_234))
in (let _179_237 = (let _179_236 = (let _179_235 = (lift c.FStar_Syntax_Syntax.result_typ wlp)
in (FStar_Syntax_Syntax.as_arg _179_235))
in (_179_236)::[])
in (_179_238)::_179_237))
in {FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _179_239; FStar_Syntax_Syntax.flags = []})
end)))

let norm_eff_name = (let cache = (FStar_Util.smap_create 20)
in (fun env l -> (let rec find = (fun l -> (match ((FStar_TypeChecker_Env.lookup_effect_abbrev env l)) with
| None -> begin
None
end
| Some (_88_625, c) -> begin
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
(let _88_639 = (FStar_Util.smap_add cache l.FStar_Ident.str m)
in m)
end)
end)
in res))))

let join_effects = (fun env l1 l2 -> (let _88_650 = (let _179_253 = (norm_eff_name env l1)
in (let _179_252 = (norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _179_253 _179_252)))
in (match (_88_650) with
| (m, _88_647, _88_649) -> begin
m
end)))

let join_lcomp = (fun env c1 c2 -> if ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2)) then begin
FStar_Syntax_Const.effect_Tot_lid
end else begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)

let lift_and_destruct = (fun env c1 c2 -> (let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (let _88_662 = (FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (_88_662) with
| (m, lift1, lift2) -> begin
(let m1 = (lift_comp c1 m lift1)
in (let m2 = (lift_comp c2 m lift2)
in (let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (let _88_668 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (_88_668) with
| (a, kwp) -> begin
(let _179_267 = (destruct_comp m1)
in (let _179_266 = (destruct_comp m2)
in ((md, a, kwp), _179_267, _179_266)))
end)))))
end)))))

let is_pure_effect = (fun env l -> (let l = (norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)))

let is_pure_or_ghost_effect = (fun env l -> (let l = (norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid))))

let mk_comp = (fun md result wp wlp flags -> (let _179_290 = (let _179_289 = (let _179_288 = (FStar_Syntax_Syntax.as_arg wp)
in (let _179_287 = (let _179_286 = (FStar_Syntax_Syntax.as_arg wlp)
in (_179_286)::[])
in (_179_288)::_179_287))
in {FStar_Syntax_Syntax.effect_name = md.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = _179_289; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp _179_290)))

let subst_lcomp = (fun subst lc -> (let _88_682 = lc
in (let _179_297 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _88_682.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _179_297; FStar_Syntax_Syntax.cflags = _88_682.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _88_684 -> (match (()) with
| () -> begin
(let _179_296 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _179_296))
end))})))

let is_function = (fun t -> (match ((let _179_300 = (FStar_Syntax_Subst.compress t)
in _179_300.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_88_687) -> begin
true
end
| _88_690 -> begin
false
end))

let return_value = (fun env t v -> (let c = (match ((FStar_TypeChecker_Env.lookup_effect_abbrev env FStar_Syntax_Const.effect_GTot_lid)) with
| None -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| _88_696 -> begin
(let m = (let _179_307 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must _179_307))
in (let _88_700 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_88_700) with
| (a, kwp) -> begin
(let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (let wp = (let _179_313 = (let _179_312 = (FStar_TypeChecker_Env.inst_effect_fun env m m.FStar_Syntax_Syntax.ret)
in (let _179_311 = (let _179_310 = (FStar_Syntax_Syntax.as_arg t)
in (let _179_309 = (let _179_308 = (FStar_Syntax_Syntax.as_arg v)
in (_179_308)::[])
in (_179_310)::_179_309))
in (FStar_Syntax_Syntax.mk_Tm_app _179_312 _179_311 (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _179_313))
in (let wlp = wp
in (mk_comp m t wp wlp ((FStar_Syntax_Syntax.RETURN)::[])))))
end)))
end)
in (let _88_705 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return"))) then begin
(let _179_316 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _179_315 = (FStar_Syntax_Print.term_to_string v)
in (let _179_314 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _179_316 _179_315 _179_314))))
end else begin
()
end
in c)))

let bind = (fun env e1opt lc1 _88_712 -> (match (_88_712) with
| (b, lc2) -> begin
(let _88_720 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let bstr = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _179_327 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (let _179_326 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _179_325 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" _179_327 _179_326 bstr _179_325)))))
end else begin
()
end
in (let bind_it = (fun _88_723 -> (match (()) with
| () -> begin
(let c1 = (lc1.FStar_Syntax_Syntax.comp ())
in (let c2 = (lc2.FStar_Syntax_Syntax.comp ())
in (let _88_729 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _179_334 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _179_333 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _179_332 = (FStar_Syntax_Print.comp_to_string c1)
in (let _179_331 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (let _179_330 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" _179_334 _179_333 _179_332 _179_331 _179_330))))))
end else begin
()
end
in (let try_simplify = (fun _88_732 -> (match (()) with
| () -> begin
(let aux = (fun _88_734 -> (match (()) with
| () -> begin
if (FStar_Syntax_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some ((c2, "trivial no binder"))
end
| Some (_88_737) -> begin
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
(let _179_340 = (let _179_339 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in (_179_339, "both gtot"))
in Some (_179_340))
end else begin
(match ((e1opt, b)) with
| (Some (e), Some (x)) -> begin
if ((FStar_Syntax_Util.is_total_comp c1) && (not ((FStar_Syntax_Syntax.is_null_bv x)))) then begin
(let _179_342 = (let _179_341 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT ((x, e)))::[]) c2)
in (_179_341, "substituted e"))
in Some (_179_342))
end else begin
(aux ())
end
end
| _88_745 -> begin
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
(let _88_763 = (lift_and_destruct env c1 c2)
in (match (_88_763) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(let bs = (match (b) with
| None -> begin
(let _179_343 = (FStar_Syntax_Syntax.null_binder t1)
in (_179_343)::[])
end
| Some (x) -> begin
(let _179_344 = (FStar_Syntax_Syntax.mk_binder x)
in (_179_344)::[])
end)
in (let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp None))
in (let wp_args = (let _179_359 = (FStar_Syntax_Syntax.as_arg t1)
in (let _179_358 = (let _179_357 = (FStar_Syntax_Syntax.as_arg t2)
in (let _179_356 = (let _179_355 = (FStar_Syntax_Syntax.as_arg wp1)
in (let _179_354 = (let _179_353 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _179_352 = (let _179_351 = (let _179_347 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg _179_347))
in (let _179_350 = (let _179_349 = (let _179_348 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _179_348))
in (_179_349)::[])
in (_179_351)::_179_350))
in (_179_353)::_179_352))
in (_179_355)::_179_354))
in (_179_357)::_179_356))
in (_179_359)::_179_358))
in (let wlp_args = (let _179_367 = (FStar_Syntax_Syntax.as_arg t1)
in (let _179_366 = (let _179_365 = (FStar_Syntax_Syntax.as_arg t2)
in (let _179_364 = (let _179_363 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _179_362 = (let _179_361 = (let _179_360 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _179_360))
in (_179_361)::[])
in (_179_363)::_179_362))
in (_179_365)::_179_364))
in (_179_367)::_179_366))
in (let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t2)))::[]) kwp)
in (let wp = (let _179_368 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _179_368 wp_args None t2.FStar_Syntax_Syntax.pos))
in (let wlp = (let _179_369 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.bind_wlp)
in (FStar_Syntax_Syntax.mk_Tm_app _179_369 wlp_args None t2.FStar_Syntax_Syntax.pos))
in (let c = (mk_comp md t2 wp wlp [])
in c))))))))
end))
end)))))
end))
in (let _179_370 = (join_lcomp env lc1 lc2)
in {FStar_Syntax_Syntax.eff_name = _179_370; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it})))
end))

let lift_formula = (fun env t mk_wp mk_wlp f -> (let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (let _88_784 = (FStar_TypeChecker_Env.wp_signature env md_pure.FStar_Syntax_Syntax.mname)
in (match (_88_784) with
| (a, kwp) -> begin
(let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (let wp = (let _179_384 = (let _179_383 = (FStar_Syntax_Syntax.as_arg t)
in (let _179_382 = (let _179_381 = (FStar_Syntax_Syntax.as_arg f)
in (_179_381)::[])
in (_179_383)::_179_382))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wp _179_384 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (let wlp = (let _179_388 = (let _179_387 = (FStar_Syntax_Syntax.as_arg t)
in (let _179_386 = (let _179_385 = (FStar_Syntax_Syntax.as_arg f)
in (_179_385)::[])
in (_179_387)::_179_386))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wlp _179_388 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (mk_comp md_pure FStar_TypeChecker_Recheck.t_unit wp wlp []))))
end))))

let label = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((f, FStar_Syntax_Syntax.Meta_labeled ((reason, r, false))))) None f.FStar_Syntax_Syntax.pos))

let label_opt = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _179_412 = (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)
in (FStar_All.pipe_left Prims.op_Negation _179_412)) then begin
f
end else begin
(let _179_413 = (reason ())
in (label _179_413 r f))
end
end))

let label_guard = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _88_804 = g
in (let _179_421 = (let _179_420 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_179_420))
in {FStar_TypeChecker_Env.guard_f = _179_421; FStar_TypeChecker_Env.deferred = _88_804.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _88_804.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _88_804.FStar_TypeChecker_Env.implicits}))
end))

let weaken_guard = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| _88_815 -> begin
g2
end))

let weaken_precondition = (fun env lc f -> (let weaken = (fun _88_820 -> (match (()) with
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
in (let _88_829 = (destruct_comp c)
in (match (_88_829) with
| (res_t, wp, wlp) -> begin
(let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (let wp = (let _179_440 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.assume_p)
in (let _179_439 = (let _179_438 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _179_437 = (let _179_436 = (FStar_Syntax_Syntax.as_arg f)
in (let _179_435 = (let _179_434 = (FStar_Syntax_Syntax.as_arg wp)
in (_179_434)::[])
in (_179_436)::_179_435))
in (_179_438)::_179_437))
in (FStar_Syntax_Syntax.mk_Tm_app _179_440 _179_439 None wp.FStar_Syntax_Syntax.pos)))
in (let wlp = (let _179_447 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.assume_p)
in (let _179_446 = (let _179_445 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _179_444 = (let _179_443 = (FStar_Syntax_Syntax.as_arg f)
in (let _179_442 = (let _179_441 = (FStar_Syntax_Syntax.as_arg wlp)
in (_179_441)::[])
in (_179_443)::_179_442))
in (_179_445)::_179_444))
in (FStar_Syntax_Syntax.mk_Tm_app _179_447 _179_446 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp c.FStar_Syntax_Syntax.flags))))
end)))
end
end))
end))
in (let _88_833 = lc
in {FStar_Syntax_Syntax.eff_name = _88_833.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _88_833.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _88_833.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))

let strengthen_precondition = (fun reason env e lc g0 -> if (FStar_TypeChecker_Rel.is_trivial g0) then begin
(lc, g0)
end else begin
(let _88_840 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _179_467 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _179_466 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _179_467 _179_466)))
end else begin
()
end
in (let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _88_4 -> (match (_88_4) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _88_846 -> begin
[]
end))))
in (let strengthen = (fun _88_849 -> (match (()) with
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
in (let xret = (let _179_472 = (let _179_471 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _179_471))
in (FStar_Syntax_Util.comp_set_flags _179_472 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (let lc = (bind env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), (FStar_Syntax_Util.lcomp_of_comp xret)))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (let _88_859 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _179_474 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _179_473 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _179_474 _179_473)))
end else begin
()
end
in (let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (let _88_865 = (destruct_comp c)
in (match (_88_865) with
| (res_t, wp, wlp) -> begin
(let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (let wp = (let _179_483 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.assert_p)
in (let _179_482 = (let _179_481 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _179_480 = (let _179_479 = (let _179_476 = (let _179_475 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason _179_475 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _179_476))
in (let _179_478 = (let _179_477 = (FStar_Syntax_Syntax.as_arg wp)
in (_179_477)::[])
in (_179_479)::_179_478))
in (_179_481)::_179_480))
in (FStar_Syntax_Syntax.mk_Tm_app _179_483 _179_482 None wp.FStar_Syntax_Syntax.pos)))
in (let wlp = (let _179_490 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.assume_p)
in (let _179_489 = (let _179_488 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _179_487 = (let _179_486 = (FStar_Syntax_Syntax.as_arg f)
in (let _179_485 = (let _179_484 = (FStar_Syntax_Syntax.as_arg wlp)
in (_179_484)::[])
in (_179_486)::_179_485))
in (_179_488)::_179_487))
in (FStar_Syntax_Syntax.mk_Tm_app _179_490 _179_489 None wlp.FStar_Syntax_Syntax.pos)))
in (let _88_869 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _179_491 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _179_491))
end else begin
()
end
in (let c2 = (mk_comp md res_t wp wlp flags)
in c2)))))
end)))))
end)))
end))
in (let _179_495 = (let _88_872 = lc
in (let _179_494 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _179_493 = if ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _179_492 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _179_492))) then begin
flags
end else begin
[]
end
in {FStar_Syntax_Syntax.eff_name = _179_494; FStar_Syntax_Syntax.res_typ = _88_872.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _179_493; FStar_Syntax_Syntax.comp = strengthen})))
in (_179_495, (let _88_874 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _88_874.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _88_874.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _88_874.FStar_TypeChecker_Env.implicits}))))))
end)

let record_application_site = (fun env e lc -> (let comp = (fun _88_880 -> (match (()) with
| () -> begin
(let c = (lc.FStar_Syntax_Syntax.comp ())
in (let res_t = (FStar_Syntax_Util.comp_result c)
in if (((FStar_Syntax_Util.is_trivial_wp c) || (let _179_504 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals _179_504 FStar_Syntax_Const.prims_lid))) || (FStar_Syntax_Syntax.is_teff res_t)) then begin
c
end else begin
(let g = (FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (FStar_TypeChecker_Recheck.t_unit)))
in (let _88_888 = (strengthen_precondition (Some ((fun _88_884 -> (match (()) with
| () -> begin
"push"
end)))) env e (FStar_Syntax_Util.lcomp_of_comp c) g)
in (match (_88_888) with
| (c, _88_887) -> begin
(let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (let xret = (let _179_512 = (FStar_TypeChecker_Env.inst_effect_fun env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _179_511 = (let _179_510 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _179_509 = (let _179_508 = (FStar_Syntax_Syntax.as_arg xexp)
in (_179_508)::[])
in (_179_510)::_179_509))
in (FStar_Syntax_Syntax.mk_Tm_app _179_512 _179_511 None res_t.FStar_Syntax_Syntax.pos)))
in (let xret_comp = (let _179_513 = (mk_comp md_pure res_t xret xret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _179_513))
in (let lc = (let _179_519 = (let _179_518 = (let _179_517 = (strengthen_precondition (Some ((fun _88_894 -> (match (()) with
| () -> begin
"pop"
end)))) env xexp xret_comp g)
in (FStar_All.pipe_left Prims.fst _179_517))
in (Some (x), _179_518))
in (bind env None c _179_519))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end)))
end))
end))
in (let _88_896 = lc
in {FStar_Syntax_Syntax.eff_name = _88_896.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _88_896.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _88_896.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = comp})))

let add_equality_to_post_condition = (fun env comp res_t -> (let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let y = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _88_906 = (let _179_527 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _179_526 = (FStar_Syntax_Syntax.bv_to_name y)
in (_179_527, _179_526)))
in (match (_88_906) with
| (xexp, yexp) -> begin
(let yret = (let _179_532 = (FStar_TypeChecker_Env.inst_effect_fun env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _179_531 = (let _179_530 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _179_529 = (let _179_528 = (FStar_Syntax_Syntax.as_arg yexp)
in (_179_528)::[])
in (_179_530)::_179_529))
in (FStar_Syntax_Syntax.mk_Tm_app _179_532 _179_531 None res_t.FStar_Syntax_Syntax.pos)))
in (let x_eq_y_yret = (let _179_540 = (FStar_TypeChecker_Env.inst_effect_fun env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _179_539 = (let _179_538 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _179_537 = (let _179_536 = (let _179_533 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _179_533))
in (let _179_535 = (let _179_534 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_179_534)::[])
in (_179_536)::_179_535))
in (_179_538)::_179_537))
in (FStar_Syntax_Syntax.mk_Tm_app _179_540 _179_539 None res_t.FStar_Syntax_Syntax.pos)))
in (let forall_y_x_eq_y_yret = (let _179_550 = (FStar_TypeChecker_Env.inst_effect_fun env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _179_549 = (let _179_548 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _179_547 = (let _179_546 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _179_545 = (let _179_544 = (let _179_543 = (let _179_542 = (let _179_541 = (FStar_Syntax_Syntax.mk_binder y)
in (_179_541)::[])
in (FStar_Syntax_Util.abs _179_542 x_eq_y_yret None))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _179_543))
in (_179_544)::[])
in (_179_546)::_179_545))
in (_179_548)::_179_547))
in (FStar_Syntax_Syntax.mk_Tm_app _179_550 _179_549 None res_t.FStar_Syntax_Syntax.pos)))
in (let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (let lc = (bind env None (FStar_Syntax_Util.lcomp_of_comp comp) (Some (x), (FStar_Syntax_Util.lcomp_of_comp lc2)))
in (lc.FStar_Syntax_Syntax.comp ()))))))
end))))))

let ite = (fun env guard lcomp_then lcomp_else -> (let comp = (fun _88_917 -> (match (()) with
| () -> begin
(let _88_933 = (let _179_562 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _179_561 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _179_562 _179_561)))
in (match (_88_933) with
| ((md, _88_920, _88_922), (res_t, wp_then, wlp_then), (_88_929, wp_else, wlp_else)) -> begin
(let ifthenelse = (fun md res_t g wp_t wp_e -> (let _179_582 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.if_then_else)
in (let _179_581 = (let _179_579 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _179_578 = (let _179_577 = (FStar_Syntax_Syntax.as_arg g)
in (let _179_576 = (let _179_575 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _179_574 = (let _179_573 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_179_573)::[])
in (_179_575)::_179_574))
in (_179_577)::_179_576))
in (_179_579)::_179_578))
in (let _179_580 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _179_582 _179_581 None _179_580)))))
in (let wp = (ifthenelse md res_t guard wp_then wp_else)
in (let wlp = (ifthenelse md res_t guard wlp_then wlp_else)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(let comp = (mk_comp md res_t wp wlp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(let wp = (let _179_589 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.ite_wp)
in (let _179_588 = (let _179_587 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _179_586 = (let _179_585 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _179_584 = (let _179_583 = (FStar_Syntax_Syntax.as_arg wp)
in (_179_583)::[])
in (_179_585)::_179_584))
in (_179_587)::_179_586))
in (FStar_Syntax_Syntax.mk_Tm_app _179_589 _179_588 None wp.FStar_Syntax_Syntax.pos)))
in (let wlp = (let _179_594 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _179_593 = (let _179_592 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _179_591 = (let _179_590 = (FStar_Syntax_Syntax.as_arg wlp)
in (_179_590)::[])
in (_179_592)::_179_591))
in (FStar_Syntax_Syntax.mk_Tm_app _179_594 _179_593 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end)))
end))
end))
in (let _179_595 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _179_595; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp})))

let bind_cases = (fun env res_t lcases -> (let eff = (FStar_List.fold_left (fun eff _88_952 -> (match (_88_952) with
| (_88_950, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (let bind_cases = (fun _88_955 -> (match (()) with
| () -> begin
(let ifthenelse = (fun md res_t g wp_t wp_e -> (let _179_625 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.if_then_else)
in (let _179_624 = (let _179_622 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _179_621 = (let _179_620 = (FStar_Syntax_Syntax.as_arg g)
in (let _179_619 = (let _179_618 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _179_617 = (let _179_616 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_179_616)::[])
in (_179_618)::_179_617))
in (_179_620)::_179_619))
in (_179_622)::_179_621))
in (let _179_623 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _179_625 _179_624 None _179_623)))))
in (let default_case = (let post_k = (let _179_628 = (let _179_626 = (FStar_Syntax_Syntax.null_binder res_t)
in (_179_626)::[])
in (let _179_627 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _179_628 _179_627)))
in (let kwp = (let _179_631 = (let _179_629 = (FStar_Syntax_Syntax.null_binder post_k)
in (_179_629)::[])
in (let _179_630 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _179_631 _179_630)))
in (let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (let wp = (let _179_638 = (let _179_632 = (FStar_Syntax_Syntax.mk_binder post)
in (_179_632)::[])
in (let _179_637 = (let _179_636 = (let _179_633 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Errors.exhaustiveness_check _179_633))
in (let _179_635 = (let _179_634 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.false_lid _179_634))
in (FStar_All.pipe_left _179_636 _179_635)))
in (FStar_Syntax_Util.abs _179_638 _179_637 None)))
in (let wlp = (let _179_642 = (let _179_639 = (FStar_Syntax_Syntax.mk_binder post)
in (_179_639)::[])
in (let _179_641 = (let _179_640 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid _179_640))
in (FStar_Syntax_Util.abs _179_642 _179_641 None)))
in (let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (let comp = (FStar_List.fold_right (fun _88_971 celse -> (match (_88_971) with
| (g, cthen) -> begin
(let _88_989 = (let _179_645 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _179_645 celse))
in (match (_88_989) with
| ((md, _88_975, _88_977), (_88_980, wp_then, wlp_then), (_88_985, wp_else, wlp_else)) -> begin
(let _179_647 = (ifthenelse md res_t g wp_then wp_else)
in (let _179_646 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _179_647 _179_646 [])))
end))
end)) lcases default_case)
in if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(add_equality_to_post_condition env comp res_t)
end else begin
(let comp = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (let md = (FStar_TypeChecker_Env.get_effect_decl env comp.FStar_Syntax_Syntax.effect_name)
in (let _88_997 = (destruct_comp comp)
in (match (_88_997) with
| (_88_994, wp, wlp) -> begin
(let wp = (let _179_654 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.ite_wp)
in (let _179_653 = (let _179_652 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _179_651 = (let _179_650 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _179_649 = (let _179_648 = (FStar_Syntax_Syntax.as_arg wp)
in (_179_648)::[])
in (_179_650)::_179_649))
in (_179_652)::_179_651))
in (FStar_Syntax_Syntax.mk_Tm_app _179_654 _179_653 None wp.FStar_Syntax_Syntax.pos)))
in (let wlp = (let _179_659 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _179_658 = (let _179_657 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _179_656 = (let _179_655 = (FStar_Syntax_Syntax.as_arg wlp)
in (_179_655)::[])
in (_179_657)::_179_656))
in (FStar_Syntax_Syntax.mk_Tm_app _179_659 _179_658 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end))))
end)))
end))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))

let close_comp = (fun env bvs lc -> (let close = (fun _88_1004 -> (match (()) with
| () -> begin
(let c = (lc.FStar_Syntax_Syntax.comp ())
in if (FStar_Syntax_Util.is_ml_comp c) then begin
c
end else begin
(let close_wp = (fun md res_t bvs wp0 -> (FStar_List.fold_right (fun x wp -> (let bs = (let _179_678 = (FStar_Syntax_Syntax.mk_binder x)
in (_179_678)::[])
in (let wp = (FStar_Syntax_Util.abs bs wp None)
in (let _179_685 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.close_wp)
in (let _179_684 = (let _179_683 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _179_682 = (let _179_681 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _179_680 = (let _179_679 = (FStar_Syntax_Syntax.as_arg wp)
in (_179_679)::[])
in (_179_681)::_179_680))
in (_179_683)::_179_682))
in (FStar_Syntax_Syntax.mk_Tm_app _179_685 _179_684 None wp0.FStar_Syntax_Syntax.pos)))))) bvs wp0))
in (let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (let _88_1019 = (destruct_comp c)
in (match (_88_1019) with
| (t, wp, wlp) -> begin
(let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (let wp = (close_wp md c.FStar_Syntax_Syntax.result_typ bvs wp)
in (let wlp = (close_wp md c.FStar_Syntax_Syntax.result_typ bvs wlp)
in (mk_comp md c.FStar_Syntax_Syntax.result_typ wp wlp c.FStar_Syntax_Syntax.flags))))
end))))
end)
end))
in (let _88_1023 = lc
in {FStar_Syntax_Syntax.eff_name = _88_1023.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _88_1023.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _88_1023.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))

let maybe_assume_result_eq_pure_term = (fun env e lc -> (let refine = (fun _88_1029 -> (match (()) with
| () -> begin
(let c = (lc.FStar_Syntax_Syntax.comp ())
in if (not ((is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name))) then begin
c
end else begin
if (FStar_Syntax_Util.is_partial_return c) then begin
c
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c) && (let _179_694 = (FStar_TypeChecker_Env.lookup_effect_abbrev env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left FStar_Option.isNone _179_694))) then begin
(let _179_697 = (let _179_696 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _179_695 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _179_696 _179_695)))
in (FStar_All.failwith _179_697))
end else begin
(let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (let t = c.FStar_Syntax_Syntax.result_typ
in (let c = (FStar_Syntax_Syntax.mk_Comp c)
in (let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (let ret = (let _179_699 = (let _179_698 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _179_698 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _179_699))
in (let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (let c = (let _179_701 = (let _179_700 = (bind env None (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), eq_ret))
in (_179_700.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _179_701 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
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
in (let _88_1041 = lc
in {FStar_Syntax_Syntax.eff_name = _88_1041.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _88_1041.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))

let check_comp = (fun env e c c' -> (match ((FStar_TypeChecker_Rel.sub_comp env c c')) with
| None -> begin
(let _179_713 = (let _179_712 = (let _179_711 = (FStar_TypeChecker_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _179_710 = (FStar_TypeChecker_Env.get_range env)
in (_179_711, _179_710)))
in FStar_Syntax_Syntax.Error (_179_712))
in (Prims.raise _179_713))
end
| Some (g) -> begin
(e, c', g)
end))

let maybe_coerce_bool_to_type = (fun env e lc t -> (match ((let _179_722 = (FStar_Syntax_Subst.compress t)
in _179_722.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_88_1055) -> begin
(match ((let _179_723 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _179_723.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _88_1059) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.bool_lid) -> begin
(let _88_1062 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (let b2t = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos)
in (let lc = (let _179_726 = (let _179_725 = (let _179_724 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _179_724))
in (None, _179_725))
in (bind env (Some (e)) lc _179_726))
in (let e = (let _179_728 = (let _179_727 = (FStar_Syntax_Syntax.as_arg e)
in (_179_727)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _179_728 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (e, lc)))))
end
| _88_1068 -> begin
(e, lc)
end)
end
| _88_1070 -> begin
(e, lc)
end))

let weaken_result_typ = (fun env e lc t -> (let gopt = if env.FStar_TypeChecker_Env.use_eq then begin
(let _179_737 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in (_179_737, false))
end else begin
(let _179_738 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in (_179_738, true))
end
in (match (gopt) with
| (None, _88_1078) -> begin
(FStar_TypeChecker_Rel.subtype_fail env lc.FStar_Syntax_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(match ((FStar_TypeChecker_Rel.guard_form g)) with
| FStar_TypeChecker_Common.Trivial -> begin
(let lc = (let _88_1085 = lc
in {FStar_Syntax_Syntax.eff_name = _88_1085.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _88_1085.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _88_1085.FStar_Syntax_Syntax.comp})
in (e, lc, g))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let g = (let _88_1090 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _88_1090.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _88_1090.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _88_1090.FStar_TypeChecker_Env.implicits})
in (let strengthen = (fun _88_1094 -> (match (()) with
| () -> begin
(let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (match ((let _179_741 = (FStar_Syntax_Subst.compress f)
in _179_741.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_88_1097, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _88_1106); FStar_Syntax_Syntax.tk = _88_1103; FStar_Syntax_Syntax.pos = _88_1101; FStar_Syntax_Syntax.vars = _88_1099}, _88_1111) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) -> begin
(let lc = (let _88_1114 = lc
in {FStar_Syntax_Syntax.eff_name = _88_1114.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _88_1114.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _88_1114.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| _88_1118 -> begin
(let c = (lc.FStar_Syntax_Syntax.comp ())
in (let _88_1120 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _179_745 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _179_744 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _179_743 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _179_742 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _179_745 _179_744 _179_743 _179_742)))))
end else begin
()
end
in (let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (let _88_1125 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_88_1125) with
| (a, kwp) -> begin
(let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (let md = (FStar_TypeChecker_Env.get_effect_decl env ct.FStar_Syntax_Syntax.effect_name)
in (let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (let wp = (let _179_750 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.ret)
in (let _179_749 = (let _179_748 = (FStar_Syntax_Syntax.as_arg t)
in (let _179_747 = (let _179_746 = (FStar_Syntax_Syntax.as_arg xexp)
in (_179_746)::[])
in (_179_748)::_179_747))
in (FStar_Syntax_Syntax.mk_Tm_app _179_750 _179_749 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)))
in (let cret = (let _179_751 = (mk_comp md t wp wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _179_751))
in (let guard = if apply_guard then begin
(let _179_753 = (let _179_752 = (FStar_Syntax_Syntax.as_arg xexp)
in (_179_752)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _179_753 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end else begin
f
end
in (let _88_1135 = (let _179_761 = (FStar_All.pipe_left (fun _179_758 -> Some (_179_758)) (FStar_TypeChecker_Errors.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _179_760 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _179_759 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _179_761 _179_760 e cret _179_759))))
in (match (_88_1135) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(let x = (let _88_1136 = x
in {FStar_Syntax_Syntax.ppname = _88_1136.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _88_1136.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (let c = (let _179_763 = (let _179_762 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _179_762))
in (bind env (Some (e)) _179_763 (Some (x), eq_ret)))
in (let c = (c.FStar_Syntax_Syntax.comp ())
in (let _88_1141 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _179_764 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _179_764))
end else begin
()
end
in c))))
end)))))))))
end)))))
end))
end))
in (let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _88_5 -> (match (_88_5) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _88_1147 -> begin
[]
end))))
in (let lc = (let _88_1149 = lc
in (let _179_766 = (norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _179_766; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (let g = (let _88_1152 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _88_1152.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _88_1152.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _88_1152.FStar_TypeChecker_Env.implicits})
in (e, lc, g))))))
end)
end)))

let pure_or_ghost_pre_and_post = (fun env comp -> (let mk_post_type = (fun res_t ens -> (let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _179_778 = (let _179_777 = (let _179_776 = (let _179_775 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _179_775))
in (_179_776)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _179_777 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _179_778))))
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
| (req, _88_1180)::(ens, _88_1175)::_88_1172 -> begin
(let _179_784 = (let _179_781 = (norm req)
in Some (_179_781))
in (let _179_783 = (let _179_782 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _179_782))
in (_179_784, _179_783)))
end
| _88_1184 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (wp, _88_1195)::(wlp, _88_1190)::_88_1187 -> begin
(let _88_1201 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (_88_1201) with
| (us_r, _88_1200) -> begin
(let _88_1205 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (_88_1205) with
| (us_e, _88_1204) -> begin
(let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (let as_req = (let _179_785 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.as_requires r)
in (FStar_Syntax_Syntax.mk_Tm_uinst _179_785 us_r))
in (let as_ens = (let _179_786 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.as_ensures r)
in (FStar_Syntax_Syntax.mk_Tm_uinst _179_786 us_e))
in (let req = (let _179_789 = (let _179_788 = (let _179_787 = (FStar_Syntax_Syntax.as_arg wp)
in (_179_787)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.Implicit)))::_179_788)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _179_789 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let ens = (let _179_792 = (let _179_791 = (let _179_790 = (FStar_Syntax_Syntax.as_arg wlp)
in (_179_790)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.Implicit)))::_179_791)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _179_792 None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _179_796 = (let _179_793 = (norm req)
in Some (_179_793))
in (let _179_795 = (let _179_794 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm _179_794))
in (_179_796, _179_795))))))))
end))
end))
end
| _88_1212 -> begin
(FStar_All.failwith "Impossible")
end))
end
end)
end)))

let maybe_instantiate = (fun env e t -> (let torig = (FStar_Syntax_Subst.compress t)
in if (not (env.FStar_TypeChecker_Env.instantiate_imp)) then begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end else begin
(match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _88_1223 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_88_1223) with
| (bs, c) -> begin
(let rec aux = (fun subst _88_6 -> (match (_88_6) with
| (x, Some (FStar_Syntax_Syntax.Implicit))::rest -> begin
(let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (let _88_1237 = (new_implicit_var env t)
in (match (_88_1237) with
| (v, u, g) -> begin
(let subst = (FStar_Syntax_Syntax.NT ((x, v)))::subst
in (let _88_1243 = (aux subst rest)
in (match (_88_1243) with
| (args, bs, subst, g') -> begin
(let _179_807 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((v, Some (FStar_Syntax_Syntax.Implicit)))::args, bs, subst, _179_807))
end)))
end)))
end
| bs -> begin
([], bs, subst, FStar_TypeChecker_Rel.trivial_guard)
end))
in (let _88_1249 = (aux [] bs)
in (match (_88_1249) with
| (args, bs, subst, guard) -> begin
(match ((args, bs)) with
| ([], _88_1252) -> begin
(e, torig, guard)
end
| (_88_1255, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end
| _88_1259 -> begin
(let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _88_1262 -> begin
(FStar_Syntax_Util.arrow bs c)
end)
in (let t = (FStar_Syntax_Subst.subst subst t)
in (let e = (FStar_Syntax_Syntax.mk_Tm_app e args (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (e, t, guard))))
end)
end)))
end))
end
| _88_1267 -> begin
(e, t, FStar_TypeChecker_Rel.trivial_guard)
end)
end))

let gen_univs = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(let s = (let _179_819 = (let _179_818 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _179_818))
in (FStar_All.pipe_right _179_819 FStar_Util.set_elements))
in (let r = (let _179_820 = (FStar_TypeChecker_Env.get_range env)
in Some (_179_820))
in (let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (let _88_1274 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _179_825 = (let _179_822 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _179_822))
in (let _179_824 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _179_823 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _179_825 _179_824 _179_823))))
end else begin
()
end
in (let _88_1276 = (FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))))
in u_name))))))
in u_names)))
end)

let generalize_universes = (fun env t -> (let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (let univs = (FStar_Syntax_Free.univs t)
in (let _88_1284 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _179_834 = (let _179_833 = (let _179_832 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _179_832 (FStar_List.map (fun u -> (let _179_831 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _179_831 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _179_833 (FStar_String.concat ", ")))
in (FStar_Util.print1 "univs to gen : %s\n" _179_834))
end else begin
()
end
in (let gen = (gen_univs env univs)
in (let _88_1287 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _179_835 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _179_835))
end else begin
()
end
in (let ts = (FStar_Syntax_Subst.close_univ_vars gen t)
in (gen, ts))))))))

let gen = (fun env ecs -> if (let _179_841 = (FStar_Util.for_all (fun _88_1295 -> (match (_88_1295) with
| (_88_1293, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _179_841)) then begin
None
end else begin
(let norm = (fun c -> (let _88_1298 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _179_844 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _179_844))
end else begin
()
end
in (let c = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.Eta)::[]) env c)
end else begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env c)
end
in (let _88_1301 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _179_845 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _179_845))
end else begin
()
end
in c))))
in (let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (let gen_uvars = (fun uvs -> (let _179_848 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _179_848 FStar_Util.set_elements)))
in (let _88_1318 = (let _179_850 = (FStar_All.pipe_right ecs (FStar_List.map (fun _88_1308 -> (match (_88_1308) with
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
in (FStar_All.pipe_right _179_850 FStar_List.unzip))
in (match (_88_1318) with
| (univs, uvars) -> begin
(let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (let gen_univs = (gen_univs env univs)
in (let _88_1322 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end else begin
()
end
in (let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _88_1327 -> (match (_88_1327) with
| (uvs, e, c) -> begin
(let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _88_1330 -> (match (_88_1330) with
| (u, k) -> begin
(match ((FStar_Unionfind.find u)) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(a, Some (FStar_Syntax_Syntax.Implicit))
end
| FStar_Syntax_Syntax.Fixed (_88_1364) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _88_1367 -> begin
(let _88_1370 = (FStar_Syntax_Util.arrow_formals k)
in (match (_88_1370) with
| (bs, kres) -> begin
(let a = (let _179_856 = (let _179_855 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _179_854 -> Some (_179_854)) _179_855))
in (FStar_Syntax_Syntax.new_bv _179_856 kres))
in (let t = (let _179_860 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _179_859 = (let _179_858 = (let _179_857 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _179_857))
in Some (_179_858))
in (FStar_Syntax_Util.abs bs _179_860 _179_859)))
in (let _88_1373 = (FStar_Syntax_Util.set_uvar u t)
in (a, Some (FStar_Syntax_Syntax.Implicit)))))
end))
end)
end))))
in (let _88_1394 = (match (tvars) with
| [] -> begin
(e, c)
end
| _88_1378 -> begin
(let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]) env c)
in (let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]) env e)
in (let t = (match ((let _179_861 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _179_861.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(let _88_1387 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (_88_1387) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| _88_1389 -> begin
(FStar_Syntax_Util.arrow tvars c)
end)
in (let e' = (FStar_Syntax_Util.abs tvars e None)
in (let _179_862 = (FStar_Syntax_Syntax.mk_Total t)
in (e', _179_862))))))
end)
in (match (_88_1394) with
| (e, c) -> begin
(gen_univs, e, c)
end)))
end))))
in Some (ecs)))))
end)))))
end)

let generalize = (fun env lecs -> (let _88_1404 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _179_869 = (let _179_868 = (FStar_List.map (fun _88_1403 -> (match (_88_1403) with
| (lb, _88_1400, _88_1402) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _179_868 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _179_869))
end else begin
()
end
in (match ((let _179_871 = (FStar_All.pipe_right lecs (FStar_List.map (fun _88_1410 -> (match (_88_1410) with
| (_88_1407, e, c) -> begin
(e, c)
end))))
in (gen env _179_871))) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun _88_1415 -> (match (_88_1415) with
| (l, t, c) -> begin
(l, [], t, c)
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _88_1423 _88_1427 -> (match ((_88_1423, _88_1427)) with
| ((l, _88_1420, _88_1422), (us, e, c)) -> begin
(let _88_1428 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _179_877 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _179_876 = (FStar_Syntax_Print.lbname_to_string l)
in (let _179_875 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.print3 "(%s) Generalized %s to %s\n" _179_877 _179_876 _179_875))))
end else begin
()
end
in (l, us, e, c))
end)) lecs ecs)
end)))

let check_and_ascribe = (fun env e t1 t2 -> (let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let check = (fun env t1 t2 -> if env.FStar_TypeChecker_Env.use_eq then begin
(FStar_TypeChecker_Rel.try_teq env t1 t2)
end else begin
(match ((FStar_TypeChecker_Rel.try_subtype env t1 t2)) with
| None -> begin
None
end
| Some (f) -> begin
(let _179_893 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _179_892 -> Some (_179_892)) _179_893))
end)
end)
in (let is_var = (fun e -> (match ((let _179_896 = (FStar_Syntax_Subst.compress e)
in _179_896.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (_88_1445) -> begin
true
end
| _88_1448 -> begin
false
end))
in (let decorate = (fun e t -> (let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((let _88_1455 = x
in {FStar_Syntax_Syntax.ppname = _88_1455.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _88_1455.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| _88_1458 -> begin
(let _88_1459 = e
in (let _179_901 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _88_1459.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _179_901; FStar_Syntax_Syntax.pos = _88_1459.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _88_1459.FStar_Syntax_Syntax.vars}))
end)))
in (let env = (let _88_1461 = env
in (let _179_902 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _88_1461.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _88_1461.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _88_1461.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _88_1461.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _88_1461.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _88_1461.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _88_1461.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _88_1461.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _88_1461.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _88_1461.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _88_1461.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _88_1461.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _88_1461.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _88_1461.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _88_1461.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _179_902; FStar_TypeChecker_Env.is_iface = _88_1461.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _88_1461.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _88_1461.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _88_1461.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = _88_1461.FStar_TypeChecker_Env.use_bv_sorts}))
in (match ((check env t1 t2)) with
| None -> begin
(let _179_906 = (let _179_905 = (let _179_904 = (FStar_TypeChecker_Errors.expected_expression_of_type env t2 e t1)
in (let _179_903 = (FStar_TypeChecker_Env.get_range env)
in (_179_904, _179_903)))
in FStar_Syntax_Syntax.Error (_179_905))
in (Prims.raise _179_906))
end
| Some (g) -> begin
(let _88_1467 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _179_907 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _179_907))
end else begin
()
end
in (let _179_908 = (decorate e t2)
in (_179_908, g)))
end)))))))

let check_top_level = (fun env g lc -> (let discharge = (fun g -> (let _88_1474 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _179_918 = (discharge g)
in (let _179_917 = (lc.FStar_Syntax_Syntax.comp ())
in (_179_918, _179_917)))
end else begin
(let c = (lc.FStar_Syntax_Syntax.comp ())
in (let steps = (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.DeltaComp)::[]
in (let c = (let _179_919 = (FStar_TypeChecker_Normalize.normalize_comp steps env c)
in (FStar_All.pipe_right _179_919 FStar_Syntax_Util.comp_to_comp_typ))
in (let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (let _88_1485 = (destruct_comp c)
in (match (_88_1485) with
| (t, wp, _88_1484) -> begin
(let vc = (let _179_925 = (FStar_TypeChecker_Env.inst_effect_fun env md md.FStar_Syntax_Syntax.trivial)
in (let _179_924 = (let _179_922 = (FStar_Syntax_Syntax.as_arg t)
in (let _179_921 = (let _179_920 = (FStar_Syntax_Syntax.as_arg wp)
in (_179_920)::[])
in (_179_922)::_179_921))
in (let _179_923 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk_Tm_app _179_925 _179_924 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _179_923))))
in (let _88_1487 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _179_926 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _179_926))
end else begin
()
end
in (let g = (let _179_927 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _179_927))
in (let _179_929 = (discharge g)
in (let _179_928 = (FStar_Syntax_Syntax.mk_Comp c)
in (_179_929, _179_928))))))
end))))))
end)))

let short_circuit = (fun head seen_args -> (let short_bin_op = (fun f _88_7 -> (match (_88_7) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (fst, _88_1498)::[] -> begin
(f fst)
end
| _88_1502 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (let op_and_e = (fun e -> (let _179_950 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _179_950 (fun _179_949 -> FStar_TypeChecker_Common.NonTrivial (_179_949)))))
in (let op_or_e = (fun e -> (let _179_955 = (let _179_953 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _179_953))
in (FStar_All.pipe_right _179_955 (fun _179_954 -> FStar_TypeChecker_Common.NonTrivial (_179_954)))))
in (let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _179_958 -> FStar_TypeChecker_Common.NonTrivial (_179_958))))
in (let op_or_t = (fun t -> (let _179_962 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _179_962 (fun _179_961 -> FStar_TypeChecker_Common.NonTrivial (_179_961)))))
in (let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _179_965 -> FStar_TypeChecker_Common.NonTrivial (_179_965))))
in (let short_op_ite = (fun _88_8 -> (match (_88_8) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (guard, _88_1517)::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| _then::(guard, _88_1522)::[] -> begin
(let _179_969 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _179_969 (fun _179_968 -> FStar_TypeChecker_Common.NonTrivial (_179_968))))
end
| _88_1527 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (let table = ((FStar_Syntax_Const.op_And, (short_bin_op op_and_e)))::((FStar_Syntax_Const.op_Or, (short_bin_op op_or_e)))::((FStar_Syntax_Const.and_lid, (short_bin_op op_and_t)))::((FStar_Syntax_Const.or_lid, (short_bin_op op_or_t)))::((FStar_Syntax_Const.imp_lid, (short_bin_op op_imp_t)))::((FStar_Syntax_Const.ite_lid, short_op_ite))::[]
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _88_1532) -> begin
(let lid = fv.FStar_Syntax_Syntax.v
in (match ((FStar_Util.find_map table (fun _88_1538 -> (match (_88_1538) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _179_1002 = (mk seen_args)
in Some (_179_1002))
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
| _88_1543 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))

let short_circuit_head = (fun l -> (match ((let _179_1005 = (FStar_Syntax_Subst.compress l)
in _179_1005.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (v, _88_1547) -> begin
(FStar_Util.for_some (FStar_Ident.lid_equals v.FStar_Syntax_Syntax.v) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| _88_1551 -> begin
false
end))

let maybe_add_implicit_binders = (fun env bs -> (let pos = (fun bs -> (match (bs) with
| (hd, _88_1560)::_88_1557 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| _88_1564 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| (_88_1568, Some (FStar_Syntax_Syntax.Implicit))::_88_1566 -> begin
bs
end
| _88_1574 -> begin
(match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
bs
end
| Some (t) -> begin
(match ((let _179_1012 = (FStar_Syntax_Subst.compress t)
in _179_1012.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', _88_1580) -> begin
(match ((FStar_Util.prefix_until (fun _88_9 -> (match (_88_9) with
| (_88_1585, Some (FStar_Syntax_Syntax.Implicit)) -> begin
false
end
| _88_1590 -> begin
true
end)) bs')) with
| None -> begin
bs
end
| Some ([], _88_1594, _88_1596) -> begin
bs
end
| Some (imps, _88_1601, _88_1603) -> begin
if (FStar_All.pipe_right imps (FStar_Util.for_all (fun _88_1609 -> (match (_88_1609) with
| (x, _88_1608) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end)))) then begin
(let r = (pos bs)
in (let imps = (FStar_All.pipe_right imps (FStar_List.map (fun _88_1613 -> (match (_88_1613) with
| (x, i) -> begin
(let _179_1016 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in (_179_1016, i))
end))))
in (FStar_List.append imps bs)))
end else begin
bs
end
end)
end
| _88_1616 -> begin
bs
end)
end)
end)))




