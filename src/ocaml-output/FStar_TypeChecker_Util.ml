
open Prims

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv Prims.option * FStar_Syntax_Syntax.lcomp)


let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _153_6 = (FStar_TypeChecker_Env.get_range env)
in (let _153_5 = (FStar_TypeChecker_Errors.failed_to_prove_specification errs)
in (FStar_TypeChecker_Errors.report _153_6 _153_5))))


let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _153_9 = (FStar_Syntax_Subst.compress t)
in _153_9.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_56_13) -> begin
true
end
| _56_16 -> begin
false
end))


let t_binders : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env -> (let _153_13 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right _153_13 (FStar_List.filter (fun _56_21 -> (match (_56_21) with
| (x, _56_20) -> begin
(is_type x.FStar_Syntax_Syntax.sort)
end))))))


let new_uvar_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun env k -> (

let bs = if ((FStar_Options.full_context_dependency ()) || (let _153_18 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _153_18))) then begin
(FStar_TypeChecker_Env.all_binders env)
end else begin
(t_binders env)
end
in (let _153_19 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Rel.new_uvar _153_19 bs k))))


let new_uvar : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env k -> (let _153_24 = (new_uvar_aux env k)
in (Prims.fst _153_24)))


let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun _56_1 -> (match (_56_1) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, _56_36); FStar_Syntax_Syntax.tk = _56_33; FStar_Syntax_Syntax.pos = _56_31; FStar_Syntax_Syntax.vars = _56_29} -> begin
uv
end
| _56_41 -> begin
(FStar_All.failwith "Impossible")
end))


let new_implicit_var : Prims.string  ->  FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.uvar * FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t) = (fun reason r env k -> (match ((FStar_Syntax_Util.destruct k FStar_Syntax_Const.range_of_lid)) with
| Some ((_56_51)::((tm, _56_48))::[]) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))) None tm.FStar_Syntax_Syntax.pos)
in ((t), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
end
| _56_56 -> begin
(

let _56_59 = (new_uvar_aux env k)
in (match (_56_59) with
| (t, u) -> begin
(

let g = (

let _56_60 = FStar_TypeChecker_Rel.trivial_guard
in (let _153_37 = (let _153_36 = (let _153_35 = (as_uvar u)
in ((reason), (env), (_153_35), (t), (k), (r)))
in (_153_36)::[])
in {FStar_TypeChecker_Env.guard_f = _56_60.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _56_60.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_60.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _153_37}))
in (let _153_40 = (let _153_39 = (let _153_38 = (as_uvar u)
in ((_153_38), (r)))
in (_153_39)::[])
in ((t), (_153_40), (g))))
end))
end))


let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun r t -> (

let uvs = (FStar_Syntax_Free.uvars t)
in if (not ((FStar_Util.set_is_empty uvs))) then begin
(

let us = (let _153_47 = (let _153_46 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun _56_69 -> (match (_56_69) with
| (x, _56_68) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) _153_46))
in (FStar_All.pipe_right _153_47 (FStar_String.concat ", ")))
in (

let _56_71 = (FStar_Options.push ())
in (

let _56_73 = (FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool (false)))
in (

let _56_75 = (FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)))
in (

let _56_77 = (let _153_49 = (let _153_48 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us _153_48))
in (FStar_TypeChecker_Errors.report r _153_49))
in (FStar_Options.pop ()))))))
end else begin
()
end))


let force_sort' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' = (fun s -> (match ((FStar_ST.read s.FStar_Syntax_Syntax.tk)) with
| None -> begin
(let _153_54 = (let _153_53 = (FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos)
in (let _153_52 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s" _153_53 _153_52)))
in (FStar_All.failwith _153_54))
end
| Some (tk) -> begin
tk
end))


let force_sort = (fun s -> (let _153_56 = (force_sort' s)
in (FStar_Syntax_Syntax.mk _153_56 None s.FStar_Syntax_Syntax.pos)))


let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env _56_92 -> (match (_56_92) with
| {FStar_Syntax_Syntax.lbname = _56_91; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _56_87; FStar_Syntax_Syntax.lbdef = e} -> begin
(

let rng = t.FStar_Syntax_Syntax.pos
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _56_96 = if (univ_vars <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let mk_binder = (fun scope a -> (match ((let _153_65 = (FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort)
in _153_65.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _56_106 = (FStar_Syntax_Util.type_u ())
in (match (_56_106) with
| (k, _56_105) -> begin
(

let t = (let _153_66 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right _153_66 Prims.fst))
in (((

let _56_108 = a
in {FStar_Syntax_Syntax.ppname = _56_108.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_108.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (false)))
end))
end
| _56_111 -> begin
((a), (true))
end))
in (

let rec aux = (fun vars e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, _56_118) -> begin
(aux vars e)
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _56_124) -> begin
((t), (true))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _56_130) -> begin
(

let _56_149 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _56_136 _56_139 -> (match (((_56_136), (_56_139))) with
| ((scope, bs, check), (a, imp)) -> begin
(

let _56_142 = (mk_binder scope a)
in (match (_56_142) with
| (tb, c) -> begin
(

let b = ((tb), (imp))
in (

let bs = (FStar_List.append bs ((b)::[]))
in (

let scope = (FStar_List.append scope ((b)::[]))
in ((scope), (bs), ((c || check))))))
end))
end)) ((vars), ([]), (false))))
in (match (_56_149) with
| (scope, bs, check) -> begin
(

let _56_152 = (aux scope body)
in (match (_56_152) with
| (res, check_res) -> begin
(

let c = (match (res) with
| FStar_Util.Inl (t) -> begin
(FStar_Syntax_Util.ml_comp t r)
end
| FStar_Util.Inr (c) -> begin
c
end)
in (

let t = (FStar_Syntax_Util.arrow bs c)
in (

let _56_159 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _153_74 = (FStar_Range.string_of_range r)
in (let _153_73 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _153_74 _153_73)))
end else begin
()
end
in ((FStar_Util.Inl (t)), ((check_res || check))))))
end))
end))
end
| _56_162 -> begin
(let _153_77 = (let _153_76 = (let _153_75 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _153_75 Prims.fst))
in FStar_Util.Inl (_153_76))
in ((_153_77), (false)))
end)))
in (

let _56_165 = (let _153_78 = (t_binders env)
in (aux _153_78 e))
in (match (_56_165) with
| (t, b) -> begin
(

let t = (match (t) with
| FStar_Util.Inr (c) -> begin
(let _153_82 = (let _153_81 = (let _153_80 = (let _153_79 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" _153_79))
in ((_153_80), (rng)))
in FStar_Syntax_Syntax.Error (_153_81))
in (Prims.raise _153_82))
end
| FStar_Util.Inl (t) -> begin
t
end)
in (([]), (t), (b)))
end))))))
end
| _56_172 -> begin
(

let _56_175 = (FStar_Syntax_Subst.open_univ_vars univ_vars t)
in (match (_56_175) with
| (univ_vars, t) -> begin
((univ_vars), (t), (false))
end))
end)))
end))


let pat_as_exps : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term Prims.list * FStar_Syntax_Syntax.pat) = (fun allow_implicits env p -> (

let rec pat_as_arg_with_env = (fun allow_wc_dependence env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) None p.FStar_Syntax_Syntax.p)
in (([]), ([]), ([]), (env), (e), (p)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, _56_188) -> begin
(

let _56_194 = (FStar_Syntax_Util.type_u ())
in (match (_56_194) with
| (k, _56_193) -> begin
(

let t = (new_uvar env k)
in (

let x = (

let _56_196 = x
in {FStar_Syntax_Syntax.ppname = _56_196.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_196.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let _56_201 = (let _153_95 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _153_95 t))
in (match (_56_201) with
| (e, u) -> begin
(

let p = (

let _56_202 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (e))); FStar_Syntax_Syntax.ty = _56_202.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_202.FStar_Syntax_Syntax.p})
in (([]), ([]), ([]), (env), (e), (p)))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let _56_210 = (FStar_Syntax_Util.type_u ())
in (match (_56_210) with
| (t, _56_209) -> begin
(

let x = (

let _56_211 = x
in (let _153_96 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _56_211.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_211.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _153_96}))
in (

let env = if allow_wc_dependence then begin
(FStar_TypeChecker_Env.push_bv env x)
end else begin
env
end
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in (((x)::[]), ([]), ((x)::[]), (env), (e), (p)))))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let _56_221 = (FStar_Syntax_Util.type_u ())
in (match (_56_221) with
| (t, _56_220) -> begin
(

let x = (

let _56_222 = x
in (let _153_97 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _56_222.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_222.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _153_97}))
in (

let env = (FStar_TypeChecker_Env.push_bv env x)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in (((x)::[]), ((x)::[]), ([]), (env), (e), (p)))))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _56_255 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _56_237 _56_240 -> (match (((_56_237), (_56_240))) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(

let _56_247 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_56_247) with
| (b', a', w', env, te, pat) -> begin
(

let arg = if imp then begin
(FStar_Syntax_Syntax.iarg te)
end else begin
(FStar_Syntax_Syntax.as_arg te)
end
in (((b')::b), ((a')::a), ((w')::w), (env), ((arg)::args), ((((pat), (imp)))::pats)))
end))
end)) (([]), ([]), ([]), (env), ([]), ([]))))
in (match (_56_255) with
| (b, a, w, env, args, pats) -> begin
(

let e = (let _153_104 = (let _153_103 = (let _153_102 = (let _153_101 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (let _153_100 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app _153_101 _153_100 None p.FStar_Syntax_Syntax.p)))
in ((_153_102), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))
in FStar_Syntax_Syntax.Tm_meta (_153_103))
in (FStar_Syntax_Syntax.mk _153_104 None p.FStar_Syntax_Syntax.p))
in (let _153_107 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _153_106 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _153_105 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in ((_153_107), (_153_106), (_153_105), (env), (e), ((

let _56_257 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _56_257.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_257.FStar_Syntax_Syntax.p})))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (_56_260) -> begin
(FStar_All.failwith "impossible")
end))
in (

let rec elaborate_pat = (fun env p -> (

let maybe_dot = (fun inaccessible a r -> if (allow_implicits && inaccessible) then begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((a), (FStar_Syntax_Syntax.tun)))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end else begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var (a)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end)
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let pats = (FStar_List.map (fun _56_275 -> (match (_56_275) with
| (p, imp) -> begin
(let _153_119 = (elaborate_pat env p)
in ((_153_119), (imp)))
end)) pats)
in (

let _56_280 = (FStar_TypeChecker_Env.lookup_datacon env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_56_280) with
| (_56_278, t) -> begin
(

let _56_284 = (FStar_Syntax_Util.arrow_formals t)
in (match (_56_284) with
| (f, _56_283) -> begin
(

let rec aux = (fun formals pats -> (match (((formals), (pats))) with
| ([], []) -> begin
[]
end
| ([], (_56_295)::_56_293) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Too many pattern arguments"), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))))
end
| ((_56_301)::_56_299, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun _56_307 -> (match (_56_307) with
| (t, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(

let a = (let _153_126 = (let _153_125 = (FStar_Syntax_Syntax.range_of_bv t)
in Some (_153_125))
in (FStar_Syntax_Syntax.new_bv _153_126 FStar_Syntax_Syntax.tun))
in (

let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (let _153_127 = (maybe_dot inaccessible a r)
in ((_153_127), (true)))))
end
| _56_314 -> begin
(let _153_131 = (let _153_130 = (let _153_129 = (let _153_128 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _153_128))
in ((_153_129), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))
in FStar_Syntax_Syntax.Error (_153_130))
in (Prims.raise _153_131))
end)
end))))
end
| ((f)::formals', ((p, p_imp))::pats') -> begin
(match (f) with
| (_56_325, Some (FStar_Syntax_Syntax.Implicit (_56_327))) when p_imp -> begin
(let _153_132 = (aux formals' pats')
in (((p), (true)))::_153_132)
end
| (_56_332, Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(

let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let p = (maybe_dot inaccessible a (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
in (let _153_133 = (aux formals' pats)
in (((p), (true)))::_153_133)))
end
| (_56_340, imp) -> begin
(let _153_136 = (let _153_134 = (FStar_Syntax_Syntax.is_implicit imp)
in ((p), (_153_134)))
in (let _153_135 = (aux formals' pats')
in (_153_136)::_153_135))
end)
end))
in (

let _56_343 = p
in (let _153_139 = (let _153_138 = (let _153_137 = (aux f pats)
in ((fv), (_153_137)))
in FStar_Syntax_Syntax.Pat_cons (_153_138))
in {FStar_Syntax_Syntax.v = _153_139; FStar_Syntax_Syntax.ty = _56_343.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_343.FStar_Syntax_Syntax.p})))
end))
end)))
end
| _56_346 -> begin
p
end)))
in (

let one_pat = (fun allow_wc_dependence env p -> (

let p = (elaborate_pat env p)
in (

let _56_358 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_56_358) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))) with
| Some (x) -> begin
(let _153_148 = (let _153_147 = (let _153_146 = (FStar_TypeChecker_Errors.nonlinear_pattern_variable x)
in ((_153_146), (p.FStar_Syntax_Syntax.p)))
in FStar_Syntax_Syntax.Error (_153_147))
in (Prims.raise _153_148))
end
| _56_362 -> begin
((b), (a), (w), (arg), (p))
end)
end))))
in (

let top_level_pat_as_args = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((q)::pats) -> begin
(

let _56_378 = (one_pat false env q)
in (match (_56_378) with
| (b, a, _56_375, te, q) -> begin
(

let _56_393 = (FStar_List.fold_right (fun p _56_383 -> (match (_56_383) with
| (w, args, pats) -> begin
(

let _56_389 = (one_pat false env p)
in (match (_56_389) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv FStar_Syntax_Syntax.bv_eq a a'))) then begin
(let _153_158 = (let _153_157 = (let _153_156 = (FStar_TypeChecker_Errors.disjunctive_pattern_vars a a')
in (let _153_155 = (FStar_TypeChecker_Env.get_range env)
in ((_153_156), (_153_155))))
in FStar_Syntax_Syntax.Error (_153_157))
in (Prims.raise _153_158))
end else begin
(let _153_160 = (let _153_159 = (FStar_Syntax_Syntax.as_arg arg)
in (_153_159)::args)
in (((FStar_List.append w' w)), (_153_160), ((p)::pats)))
end
end))
end)) pats (([]), ([]), ([])))
in (match (_56_393) with
| (w, args, pats) -> begin
(let _153_162 = (let _153_161 = (FStar_Syntax_Syntax.as_arg te)
in (_153_161)::args)
in (((FStar_List.append b w)), (_153_162), ((

let _56_394 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((q)::pats); FStar_Syntax_Syntax.ty = _56_394.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_394.FStar_Syntax_Syntax.p}))))
end))
end))
end
| _56_397 -> begin
(

let _56_405 = (one_pat true env p)
in (match (_56_405) with
| (b, _56_400, _56_402, arg, p) -> begin
(let _153_164 = (let _153_163 = (FStar_Syntax_Syntax.as_arg arg)
in (_153_163)::[])
in ((b), (_153_164), (p)))
end))
end))
in (

let _56_409 = (top_level_pat_as_args env p)
in (match (_56_409) with
| (b, args, p) -> begin
(

let exps = (FStar_All.pipe_right args (FStar_List.map Prims.fst))
in ((b), (exps), (p)))
end)))))))


let decorate_pattern : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.pat = (fun env p exps -> (

let qq = p
in (

let rec aux = (fun p e -> (

let pkg = (fun q t -> (FStar_Syntax_Syntax.withinfo q t p.FStar_Syntax_Syntax.p))
in (

let e = (FStar_Syntax_Util.unmeta e)
in (match (((p.FStar_Syntax_Syntax.v), (e.FStar_Syntax_Syntax.n))) with
| (_56_423, FStar_Syntax_Syntax.Tm_uinst (e, _56_426)) -> begin
(aux p e)
end
| (FStar_Syntax_Syntax.Pat_constant (_56_431), FStar_Syntax_Syntax.Tm_constant (_56_434)) -> begin
(let _153_179 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v _153_179))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(

let _56_442 = if (not ((FStar_Syntax_Syntax.bv_eq x y))) then begin
(let _153_182 = (let _153_181 = (FStar_Syntax_Print.bv_to_string x)
in (let _153_180 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _153_181 _153_180)))
in (FStar_All.failwith _153_182))
end else begin
()
end
in (

let _56_444 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _153_184 = (FStar_Syntax_Print.bv_to_string x)
in (let _153_183 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _153_184 _153_183)))
end else begin
()
end
in (

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x = (

let _56_447 = x
in {FStar_Syntax_Syntax.ppname = _56_447.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_447.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x)) s.FStar_Syntax_Syntax.n)))))
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(

let _56_455 = if (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation) then begin
(let _153_187 = (let _153_186 = (FStar_Syntax_Print.bv_to_string x)
in (let _153_185 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _153_186 _153_185)))
in (FStar_All.failwith _153_187))
end else begin
()
end
in (

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x = (

let _56_458 = x
in {FStar_Syntax_Syntax.ppname = _56_458.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_458.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x)) s.FStar_Syntax_Syntax.n))))
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _56_463), _56_467) -> begin
(

let s = (force_sort e)
in (

let x = (

let _56_470 = x
in {FStar_Syntax_Syntax.ppname = _56_470.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_470.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term (((x), (e)))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
(

let _56_480 = if (not ((FStar_Syntax_Syntax.fv_eq fv fv'))) then begin
(let _153_188 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _153_188))
end else begin
()
end
in (let _153_189 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv'), ([])))) _153_189)))
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
(

let _56_523 = if (let _153_190 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right _153_190 Prims.op_Negation)) then begin
(let _153_191 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _153_191))
end else begin
()
end
in (

let fv = fv'
in (

let rec match_args = (fun matched_pats args argpats -> (match (((args), (argpats))) with
| ([], []) -> begin
(let _153_198 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev matched_pats))))) _153_198))
end
| ((arg)::args, ((argpat, _56_539))::argpats) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e, Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (_56_549)) -> begin
(

let x = (let _153_199 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _153_199))
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e)))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args argpats)))
end
| ((e, imp), _56_558) -> begin
(

let pat = (let _153_201 = (aux argpat e)
in (let _153_200 = (FStar_Syntax_Syntax.is_implicit imp)
in ((_153_201), (_153_200))))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _56_562 -> begin
(let _153_204 = (let _153_203 = (FStar_Syntax_Print.pat_to_string p)
in (let _153_202 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _153_203 _153_202)))
in (FStar_All.failwith _153_204))
end))
in (match_args [] args argpats))))
end
| _56_564 -> begin
(let _153_209 = (let _153_208 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (let _153_207 = (FStar_Syntax_Print.pat_to_string qq)
in (let _153_206 = (let _153_205 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right _153_205 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _153_208 _153_207 _153_206))))
in (FStar_All.failwith _153_209))
end))))
in (match (((p.FStar_Syntax_Syntax.v), (exps))) with
| (FStar_Syntax_Syntax.Pat_disj (ps), _56_568) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(

let ps = (FStar_List.map2 aux ps exps)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj (ps)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p))
end
| (_56_572, (e)::[]) -> begin
(aux p e)
end
| _56_577 -> begin
(FStar_All.failwith "Unexpected number of patterns")
end))))


let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (

let topt = Some (pat.FStar_Syntax_Syntax.ty)
in (

let mk = (fun f -> (FStar_Syntax_Syntax.mk f topt pat.FStar_Syntax_Syntax.p))
in (

let pat_as_arg = (fun _56_585 -> (match (_56_585) with
| (p, i) -> begin
(

let _56_588 = (decorated_pattern_as_term p)
in (match (_56_588) with
| (vars, te) -> begin
(let _153_217 = (let _153_216 = (FStar_Syntax_Syntax.as_implicit i)
in ((te), (_153_216)))
in ((vars), (_153_217)))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_56_590) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _153_218 = (mk (FStar_Syntax_Syntax.Tm_constant (c)))
in (([]), (_153_218)))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(let _153_219 = (mk (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (_153_219)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _56_603 = (let _153_220 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _153_220 FStar_List.unzip))
in (match (_56_603) with
| (vars, args) -> begin
(

let vars = (FStar_List.flatten vars)
in (let _153_224 = (let _153_223 = (let _153_222 = (let _153_221 = (FStar_Syntax_Syntax.fv_to_tm fv)
in ((_153_221), (args)))
in FStar_Syntax_Syntax.Tm_app (_153_222))
in (mk _153_223))
in ((vars), (_153_224))))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
(([]), (e))
end)))))


let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun c -> (

let wp = (match (c.FStar_Syntax_Syntax.effect_args) with
| ((wp, _56_612))::[] -> begin
wp
end
| _56_616 -> begin
(let _153_230 = (let _153_229 = (let _153_228 = (FStar_List.map (fun _56_620 -> (match (_56_620) with
| (x, _56_619) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right _153_228 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str _153_229))
in (FStar_All.failwith _153_230))
end)
in (let _153_231 = (FStar_List.hd c.FStar_Syntax_Syntax.comp_univs)
in ((_153_231), (c.FStar_Syntax_Syntax.result_typ), (wp)))))


let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (

let _56_629 = (destruct_comp c)
in (match (_56_629) with
| (u, _56_627, wp) -> begin
(let _153_250 = (let _153_249 = (let _153_248 = (lift c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _153_248))
in (_153_249)::[])
in {FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _153_250; FStar_Syntax_Syntax.flags = []})
end)))


let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let _56_638 = (let _153_258 = (FStar_TypeChecker_Env.norm_eff_name env l1)
in (let _153_257 = (FStar_TypeChecker_Env.norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _153_258 _153_257)))
in (match (_56_638) with
| (m, _56_635, _56_637) -> begin
m
end)))


let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> if ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2)) then begin
FStar_Syntax_Const.effect_Tot_lid
end else begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)


let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) * (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)) = (fun env c1 c2 -> (

let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (

let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (

let _56_650 = (FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (_56_650) with
| (m, lift1, lift2) -> begin
(

let m1 = (lift_comp c1 m lift1)
in (

let m2 = (lift_comp c2 m lift2)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (

let _56_656 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (_56_656) with
| (a, kwp) -> begin
(let _153_272 = (destruct_comp m1)
in (let _153_271 = (destruct_comp m2)
in ((((md), (a), (kwp))), (_153_272), (_153_271))))
end)))))
end)))))


let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid))))


let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md u_result result wp flags -> (let _153_293 = (let _153_292 = (let _153_291 = (FStar_Syntax_Syntax.as_arg wp)
in (_153_291)::[])
in {FStar_Syntax_Syntax.comp_univs = (u_result)::[]; FStar_Syntax_Syntax.effect_name = md.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = _153_292; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp _153_293)))


let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (

let _56_670 = lc
in (let _153_300 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _56_670.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _153_300; FStar_Syntax_Syntax.cflags = _56_670.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _56_672 -> (match (()) with
| () -> begin
(let _153_299 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _153_299))
end))})))


let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _153_303 = (FStar_Syntax_Subst.compress t)
in _153_303.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_56_675) -> begin
true
end
| _56_678 -> begin
false
end))


let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v -> (

let c = if (let _153_310 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation _153_310)) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(

let m = (let _153_311 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must _153_311))
in (

let _56_685 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_56_685) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let u_t = (env.FStar_TypeChecker_Env.universe_of env t)
in (

let wp = (let _153_317 = (let _153_316 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env m m.FStar_Syntax_Syntax.ret_wp)
in (let _153_315 = (let _153_314 = (FStar_Syntax_Syntax.as_arg t)
in (let _153_313 = (let _153_312 = (FStar_Syntax_Syntax.as_arg v)
in (_153_312)::[])
in (_153_314)::_153_313))
in (FStar_Syntax_Syntax.mk_Tm_app _153_316 _153_315 (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _153_317))
in (mk_comp m u_t t wp ((FStar_Syntax_Syntax.RETURN)::[])))))
end)))
end
in (

let _56_690 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return"))) then begin
(let _153_320 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _153_319 = (FStar_Syntax_Print.term_to_string v)
in (let _153_318 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _153_320 _153_319 _153_318))))
end else begin
()
end
in c)))


let bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r1 env e1opt lc1 _56_698 -> (match (_56_698) with
| (b, lc2) -> begin
(

let lc1 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1)
in (

let lc2 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2)
in (

let _56_708 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(

let bstr = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _153_333 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (let _153_332 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _153_331 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" _153_333 _153_332 bstr _153_331)))))
end else begin
()
end
in (

let bind_it = (fun _56_711 -> (match (()) with
| () -> begin
(

let c1 = (lc1.FStar_Syntax_Syntax.comp ())
in (

let c2 = (lc2.FStar_Syntax_Syntax.comp ())
in (

let _56_717 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _153_340 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _153_339 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _153_338 = (FStar_Syntax_Print.comp_to_string c1)
in (let _153_337 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (let _153_336 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" _153_340 _153_339 _153_338 _153_337 _153_336))))))
end else begin
()
end
in (

let try_simplify = (fun _56_720 -> (match (()) with
| () -> begin
(

let aux = (fun _56_722 -> (match (()) with
| () -> begin
if (FStar_Syntax_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some (((c2), ("trivial no binder")))
end
| Some (_56_725) -> begin
if (FStar_Syntax_Util.is_ml_comp c2) then begin
Some (((c2), ("trivial ml")))
end else begin
None
end
end)
end else begin
if ((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) then begin
Some (((c2), ("both ml")))
end else begin
None
end
end
end))
in (

let subst_c2 = (fun reason -> (match (((e1opt), (b))) with
| (Some (e), Some (x)) -> begin
(let _153_348 = (let _153_347 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in ((_153_347), (reason)))
in Some (_153_348))
end
| _56_735 -> begin
(aux ())
end))
in if ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2)) then begin
(subst_c2 "both total")
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2)) then begin
(let _153_350 = (let _153_349 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((_153_349), ("both gtot")))
in Some (_153_350))
end else begin
(match (((e1opt), (b))) with
| (Some (e), Some (x)) -> begin
if ((FStar_Syntax_Util.is_total_comp c1) && (not ((FStar_Syntax_Syntax.is_null_bv x)))) then begin
(subst_c2 "substituted e")
end else begin
(aux ())
end
end
| _56_742 -> begin
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

let _56_760 = (lift_and_destruct env c1 c2)
in (match (_56_760) with
| ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) -> begin
(

let bs = (match (b) with
| None -> begin
(let _153_351 = (FStar_Syntax_Syntax.null_binder t1)
in (_153_351)::[])
end
| Some (x) -> begin
(let _153_352 = (FStar_Syntax_Syntax.mk_binder x)
in (_153_352)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid)))))
in (

let r1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1))) None r1)
in (

let wp_args = (let _153_364 = (FStar_Syntax_Syntax.as_arg r1)
in (let _153_363 = (let _153_362 = (FStar_Syntax_Syntax.as_arg t1)
in (let _153_361 = (let _153_360 = (FStar_Syntax_Syntax.as_arg t2)
in (let _153_359 = (let _153_358 = (FStar_Syntax_Syntax.as_arg wp1)
in (let _153_357 = (let _153_356 = (let _153_355 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg _153_355))
in (_153_356)::[])
in (_153_358)::_153_357))
in (_153_360)::_153_359))
in (_153_362)::_153_361))
in (_153_364)::_153_363))
in (

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t2))))::[]) kwp)
in (

let wp = (let _153_365 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t1)::(u_t2)::[]) env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _153_365 wp_args None t2.FStar_Syntax_Syntax.pos))
in (

let c = (mk_comp md u_t2 t2 wp [])
in c)))))))
end))
end)))))
end))
in (let _153_366 = (join_lcomp env lc1 lc2)
in {FStar_Syntax_Syntax.eff_name = _153_366; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it})))))
end))


let lift_formula : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t mk_wp f -> (

let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (

let _56_779 = (FStar_TypeChecker_Env.wp_signature env md_pure.FStar_Syntax_Syntax.mname)
in (match (_56_779) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let wp = (let _153_378 = (let _153_377 = (FStar_Syntax_Syntax.as_arg t)
in (let _153_376 = (let _153_375 = (FStar_Syntax_Syntax.as_arg f)
in (_153_375)::[])
in (_153_377)::_153_376))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wp _153_378 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (mk_comp md_pure FStar_Syntax_Syntax.U_zero FStar_TypeChecker_Common.t_unit wp [])))
end))))


let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((f), (FStar_Syntax_Syntax.Meta_labeled (((reason), (r), (false))))))) None f.FStar_Syntax_Syntax.pos))


let label_opt : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _153_402 = (FStar_TypeChecker_Env.should_verify env)
in (FStar_All.pipe_left Prims.op_Negation _153_402)) then begin
f
end else begin
(let _153_403 = (reason ())
in (label _153_403 r f))
end
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let _56_798 = g
in (let _153_411 = (let _153_410 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_153_410))
in {FStar_TypeChecker_Env.guard_f = _153_411; FStar_TypeChecker_Env.deferred = _56_798.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_798.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_798.FStar_TypeChecker_Env.implicits}))
end))


let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| _56_809 -> begin
g2
end))


let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun _56_814 -> (match (()) with
| () -> begin
(

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

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _56_823 = (destruct_comp c)
in (match (_56_823) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let wp = (let _153_430 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assume_p)
in (let _153_429 = (let _153_428 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _153_427 = (let _153_426 = (FStar_Syntax_Syntax.as_arg f)
in (let _153_425 = (let _153_424 = (FStar_Syntax_Syntax.as_arg wp)
in (_153_424)::[])
in (_153_426)::_153_425))
in (_153_428)::_153_427))
in (FStar_Syntax_Syntax.mk_Tm_app _153_430 _153_429 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md u_res_t res_t wp c.FStar_Syntax_Syntax.flags)))
end)))
end
end))
end))
in (

let _56_826 = lc
in {FStar_Syntax_Syntax.eff_name = _56_826.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _56_826.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _56_826.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))


let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> if (FStar_TypeChecker_Rel.is_trivial g0) then begin
((lc), (g0))
end else begin
(

let _56_833 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _153_450 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _153_449 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _153_450 _153_449)))
end else begin
()
end
in (

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _56_2 -> (match (_56_2) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _56_839 -> begin
[]
end))))
in (

let strengthen = (fun _56_842 -> (match (()) with
| () -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let g0 = (FStar_TypeChecker_Rel.simplify_guard env g0)
in (match ((FStar_TypeChecker_Rel.guard_form g0)) with
| FStar_TypeChecker_Common.Trivial -> begin
c
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let c = if ((FStar_Syntax_Util.is_pure_or_ghost_comp c) && (not ((FStar_Syntax_Util.is_partial_return c)))) then begin
(

let x = (FStar_Syntax_Syntax.gen_bv "strengthen_pre_x" None (FStar_Syntax_Util.comp_result c))
in (

let xret = (let _153_455 = (let _153_454 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _153_454))
in (FStar_Syntax_Util.comp_set_flags _153_455 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (

let lc = (bind e.FStar_Syntax_Syntax.pos env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) ((Some (x)), ((FStar_Syntax_Util.lcomp_of_comp xret))))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (

let _56_852 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _153_457 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _153_456 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _153_457 _153_456)))
end else begin
()
end
in (

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _56_858 = (destruct_comp c)
in (match (_56_858) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let wp = (let _153_466 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assert_p)
in (let _153_465 = (let _153_464 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _153_463 = (let _153_462 = (let _153_459 = (let _153_458 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason _153_458 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _153_459))
in (let _153_461 = (let _153_460 = (FStar_Syntax_Syntax.as_arg wp)
in (_153_460)::[])
in (_153_462)::_153_461))
in (_153_464)::_153_463))
in (FStar_Syntax_Syntax.mk_Tm_app _153_466 _153_465 None wp.FStar_Syntax_Syntax.pos)))
in (

let _56_861 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _153_467 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _153_467))
end else begin
()
end
in (

let c2 = (mk_comp md u_res_t res_t wp flags)
in c2))))
end)))))
end)))
end))
in (let _153_471 = (

let _56_864 = lc
in (let _153_470 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _153_469 = if ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _153_468 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _153_468))) then begin
flags
end else begin
[]
end
in {FStar_Syntax_Syntax.eff_name = _153_470; FStar_Syntax_Syntax.res_typ = _56_864.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _153_469; FStar_Syntax_Syntax.comp = strengthen})))
in ((_153_471), ((

let _56_866 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _56_866.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_866.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_866.FStar_TypeChecker_Env.implicits})))))))
end)


let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env comp res_t -> (

let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let y = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let _56_876 = (let _153_479 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _153_478 = (FStar_Syntax_Syntax.bv_to_name y)
in ((_153_479), (_153_478))))
in (match (_56_876) with
| (xexp, yexp) -> begin
(

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let yret = (let _153_484 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.ret_wp)
in (let _153_483 = (let _153_482 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _153_481 = (let _153_480 = (FStar_Syntax_Syntax.as_arg yexp)
in (_153_480)::[])
in (_153_482)::_153_481))
in (FStar_Syntax_Syntax.mk_Tm_app _153_484 _153_483 None res_t.FStar_Syntax_Syntax.pos)))
in (

let x_eq_y_yret = (let _153_492 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _153_491 = (let _153_490 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _153_489 = (let _153_488 = (let _153_485 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _153_485))
in (let _153_487 = (let _153_486 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_153_486)::[])
in (_153_488)::_153_487))
in (_153_490)::_153_489))
in (FStar_Syntax_Syntax.mk_Tm_app _153_492 _153_491 None res_t.FStar_Syntax_Syntax.pos)))
in (

let forall_y_x_eq_y_yret = (let _153_502 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::(u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _153_501 = (let _153_500 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _153_499 = (let _153_498 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _153_497 = (let _153_496 = (let _153_495 = (let _153_494 = (let _153_493 = (FStar_Syntax_Syntax.mk_binder y)
in (_153_493)::[])
in (FStar_Syntax_Util.abs _153_494 x_eq_y_yret (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid)))))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _153_495))
in (_153_496)::[])
in (_153_498)::_153_497))
in (_153_500)::_153_499))
in (FStar_Syntax_Syntax.mk_Tm_app _153_502 _153_501 None res_t.FStar_Syntax_Syntax.pos)))
in (

let lc2 = (mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (

let lc = (let _153_503 = (FStar_TypeChecker_Env.get_range env)
in (bind _153_503 env None (FStar_Syntax_Util.lcomp_of_comp comp) ((Some (x)), ((FStar_Syntax_Util.lcomp_of_comp lc2)))))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))


let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (

let comp = (fun _56_888 -> (match (()) with
| () -> begin
(

let _56_905 = (let _153_515 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _153_514 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _153_515 _153_514)))
in (match (_56_905) with
| ((md, _56_891, _56_893), (u_res_t, res_t, wp_then), (_56_900, _56_902, wp_else)) -> begin
(

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _153_535 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (let _153_534 = (let _153_532 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _153_531 = (let _153_530 = (FStar_Syntax_Syntax.as_arg g)
in (let _153_529 = (let _153_528 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _153_527 = (let _153_526 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_153_526)::[])
in (_153_528)::_153_527))
in (_153_530)::_153_529))
in (_153_532)::_153_531))
in (let _153_533 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _153_535 _153_534 None _153_533)))))
in (

let wp = (ifthenelse md res_t guard wp_then wp_else)
in if ((FStar_Options.split_cases ()) > (Prims.parse_int "0")) then begin
(

let comp = (mk_comp md u_res_t res_t wp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(

let wp = (let _153_540 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (let _153_539 = (let _153_538 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _153_537 = (let _153_536 = (FStar_Syntax_Syntax.as_arg wp)
in (_153_536)::[])
in (_153_538)::_153_537))
in (FStar_Syntax_Syntax.mk_Tm_app _153_540 _153_539 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md u_res_t res_t wp []))
end))
end))
end))
in (let _153_541 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _153_541; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp})))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (let _153_547 = (let _153_546 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid _153_546))
in (FStar_Syntax_Syntax.fvar _153_547 FStar_Syntax_Syntax.Delta_constant None)))


let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (FStar_List.fold_left (fun eff _56_924 -> (match (_56_924) with
| (_56_922, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (

let bind_cases = (fun _56_927 -> (match (()) with
| () -> begin
(

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _153_577 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (let _153_576 = (let _153_574 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _153_573 = (let _153_572 = (FStar_Syntax_Syntax.as_arg g)
in (let _153_571 = (let _153_570 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _153_569 = (let _153_568 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_153_568)::[])
in (_153_570)::_153_569))
in (_153_572)::_153_571))
in (_153_574)::_153_573))
in (let _153_575 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _153_577 _153_576 None _153_575)))))
in (

let default_case = (

let post_k = (let _153_580 = (let _153_578 = (FStar_Syntax_Syntax.null_binder res_t)
in (_153_578)::[])
in (let _153_579 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _153_580 _153_579)))
in (

let kwp = (let _153_583 = (let _153_581 = (FStar_Syntax_Syntax.null_binder post_k)
in (_153_581)::[])
in (let _153_582 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _153_583 _153_582)))
in (

let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (

let wp = (let _153_589 = (let _153_584 = (FStar_Syntax_Syntax.mk_binder post)
in (_153_584)::[])
in (let _153_588 = (let _153_587 = (let _153_585 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Errors.exhaustiveness_check _153_585))
in (let _153_586 = (fvar_const env FStar_Syntax_Const.false_lid)
in (FStar_All.pipe_left _153_587 _153_586)))
in (FStar_Syntax_Util.abs _153_589 _153_588 (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md u_res_t res_t wp []))))))
in (

let comp = (FStar_List.fold_right (fun _56_943 celse -> (match (_56_943) with
| (g, cthen) -> begin
(

let _56_963 = (let _153_592 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _153_592 celse))
in (match (_56_963) with
| ((md, _56_947, _56_949), (_56_952, _56_954, wp_then), (_56_958, _56_960, wp_else)) -> begin
(let _153_593 = (ifthenelse md res_t g wp_then wp_else)
in (mk_comp md u_res_t res_t _153_593 []))
end))
end)) lcases default_case)
in if ((FStar_Options.split_cases ()) > (Prims.parse_int "0")) then begin
(add_equality_to_post_condition env comp res_t)
end else begin
(

let comp = (FStar_TypeChecker_Normalize.comp_to_comp_typ env comp)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env comp.FStar_Syntax_Syntax.effect_name)
in (

let _56_972 = (destruct_comp comp)
in (match (_56_972) with
| (_56_968, _56_970, wp) -> begin
(

let wp = (let _153_598 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (let _153_597 = (let _153_596 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _153_595 = (let _153_594 = (FStar_Syntax_Syntax.as_arg wp)
in (_153_594)::[])
in (_153_596)::_153_595))
in (FStar_Syntax_Syntax.mk_Tm_app _153_598 _153_597 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md u_res_t res_t wp []))
end))))
end))))
end))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))


let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (

let close = (fun _56_978 -> (match (()) with
| () -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in if (FStar_Syntax_Util.is_ml_comp c) then begin
c
end else begin
(

let close_wp = (fun u_res md res_t bvs wp0 -> (FStar_List.fold_right (fun x wp -> (

let bs = (let _153_619 = (FStar_Syntax_Syntax.mk_binder x)
in (_153_619)::[])
in (

let us = (let _153_621 = (let _153_620 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (_153_620)::[])
in (u_res)::_153_621)
in (

let wp = (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid))))
in (let _153_628 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (let _153_627 = (let _153_626 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _153_625 = (let _153_624 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _153_623 = (let _153_622 = (FStar_Syntax_Syntax.as_arg wp)
in (_153_622)::[])
in (_153_624)::_153_623))
in (_153_626)::_153_625))
in (FStar_Syntax_Syntax.mk_Tm_app _153_628 _153_627 None wp0.FStar_Syntax_Syntax.pos))))))) bvs wp0))
in (

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _56_995 = (destruct_comp c)
in (match (_56_995) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let wp = (close_wp u_res_t md res_t bvs wp)
in (mk_comp md u_res_t c.FStar_Syntax_Syntax.result_typ wp c.FStar_Syntax_Syntax.flags)))
end))))
end)
end))
in (

let _56_998 = lc
in {FStar_Syntax_Syntax.eff_name = _56_998.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _56_998.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _56_998.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))


let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (

let refine = (fun _56_1004 -> (match (()) with
| () -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in if (not ((is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name))) then begin
c
end else begin
if (FStar_Syntax_Util.is_partial_return c) then begin
c
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c) && (not ((FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)))) then begin
(let _153_639 = (let _153_638 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _153_637 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _153_638 _153_637)))
in (FStar_All.failwith _153_639))
end else begin
(

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let t = c.FStar_Syntax_Syntax.result_typ
in (

let c = (FStar_Syntax_Syntax.mk_Comp c)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (

let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (

let ret = (let _153_641 = (let _153_640 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _153_640 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _153_641))
in (

let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (

let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (

let c = (let _153_643 = (let _153_642 = (bind e.FStar_Syntax_Syntax.pos env None (FStar_Syntax_Util.lcomp_of_comp c) ((Some (x)), (eq_ret)))
in (_153_642.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _153_643 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
in c)))))))))
end
end
end)
end))
in (

let flags = if (((not ((FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)) && (not ((FStar_Syntax_Util.is_lcomp_partial_return lc)))) then begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::lc.FStar_Syntax_Syntax.cflags
end else begin
lc.FStar_Syntax_Syntax.cflags
end
in (

let _56_1016 = lc
in {FStar_Syntax_Syntax.eff_name = _56_1016.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _56_1016.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))


let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (match ((FStar_TypeChecker_Rel.sub_comp env c c')) with
| None -> begin
(let _153_655 = (let _153_654 = (let _153_653 = (FStar_TypeChecker_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _153_652 = (FStar_TypeChecker_Env.get_range env)
in ((_153_653), (_153_652))))
in FStar_Syntax_Syntax.Error (_153_654))
in (Prims.raise _153_655))
end
| Some (g) -> begin
((e), (c'), (g))
end))


let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match ((let _153_664 = (FStar_Syntax_Subst.compress t)
in _153_664.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_56_1030) -> begin
(match ((let _153_665 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _153_665.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid) -> begin
(

let _56_1034 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (

let b2t = (let _153_666 = (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar _153_666 (FStar_Syntax_Syntax.Delta_unfoldable ((Prims.parse_int "1"))) None))
in (

let lc = (let _153_669 = (let _153_668 = (let _153_667 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _153_667))
in ((None), (_153_668)))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) lc _153_669))
in (

let e = (let _153_671 = (let _153_670 = (FStar_Syntax_Syntax.as_arg e)
in (_153_670)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _153_671 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in ((e), (lc))))))
end
| _56_1040 -> begin
((e), (lc))
end)
end
| _56_1042 -> begin
((e), (lc))
end))


let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (

let gopt = if env.FStar_TypeChecker_Env.use_eq then begin
(let _153_680 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in ((_153_680), (false)))
end else begin
(let _153_681 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in ((_153_681), (true)))
end
in (match (gopt) with
| (None, _56_1050) -> begin
(

let _56_1052 = (FStar_TypeChecker_Rel.subtype_fail env e lc.FStar_Syntax_Syntax.res_typ t)
in ((e), ((

let _56_1054 = lc
in {FStar_Syntax_Syntax.eff_name = _56_1054.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _56_1054.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _56_1054.FStar_Syntax_Syntax.comp})), (FStar_TypeChecker_Rel.trivial_guard)))
end
| (Some (g), apply_guard) -> begin
(match ((FStar_TypeChecker_Rel.guard_form g)) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let lc = (

let _56_1061 = lc
in {FStar_Syntax_Syntax.eff_name = _56_1061.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _56_1061.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _56_1061.FStar_Syntax_Syntax.comp})
in ((e), (lc), (g)))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let g = (

let _56_1066 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _56_1066.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_1066.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_1066.FStar_TypeChecker_Env.implicits})
in (

let strengthen = (fun _56_1070 -> (match (()) with
| () -> begin
(

let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (match ((let _153_684 = (FStar_Syntax_Subst.compress f)
in _153_684.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_56_1073, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _56_1079; FStar_Syntax_Syntax.pos = _56_1077; FStar_Syntax_Syntax.vars = _56_1075}, _56_1084) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
(

let lc = (

let _56_1087 = lc
in {FStar_Syntax_Syntax.eff_name = _56_1087.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _56_1087.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _56_1087.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| _56_1091 -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let _56_1093 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _153_688 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _153_687 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _153_686 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _153_685 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _153_688 _153_687 _153_686 _153_685)))))
end else begin
()
end
in (

let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _56_1098 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_56_1098) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env ct.FStar_Syntax_Syntax.effect_name)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (

let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (

let _56_1108 = (destruct_comp ct)
in (match (_56_1108) with
| (u_t, _56_1105, _56_1107) -> begin
(

let wp = (let _153_693 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.ret_wp)
in (let _153_692 = (let _153_691 = (FStar_Syntax_Syntax.as_arg t)
in (let _153_690 = (let _153_689 = (FStar_Syntax_Syntax.as_arg xexp)
in (_153_689)::[])
in (_153_691)::_153_690))
in (FStar_Syntax_Syntax.mk_Tm_app _153_693 _153_692 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)))
in (

let cret = (let _153_694 = (mk_comp md u_t t wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _153_694))
in (

let guard = if apply_guard then begin
(let _153_696 = (let _153_695 = (FStar_Syntax_Syntax.as_arg xexp)
in (_153_695)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _153_696 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end else begin
f
end
in (

let _56_1114 = (let _153_704 = (FStar_All.pipe_left (fun _153_701 -> Some (_153_701)) (FStar_TypeChecker_Errors.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _153_703 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _153_702 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _153_704 _153_703 e cret _153_702))))
in (match (_56_1114) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x = (

let _56_1115 = x
in {FStar_Syntax_Syntax.ppname = _56_1115.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_1115.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (

let c = (let _153_706 = (let _153_705 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _153_705))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) _153_706 ((Some (x)), (eq_ret))))
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let _56_1120 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _153_707 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _153_707))
end else begin
()
end
in c))))
end)))))
end))))))
end)))))
end))
end))
in (

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _56_3 -> (match (_56_3) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _56_1126 -> begin
[]
end))))
in (

let lc = (

let _56_1128 = lc
in (let _153_709 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _153_709; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (

let g = (

let _56_1131 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _56_1131.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_1131.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_1131.FStar_TypeChecker_Env.implicits})
in ((e), (lc), (g)))))))
end)
end)))


let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _153_721 = (let _153_720 = (let _153_719 = (let _153_718 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _153_718))
in (_153_719)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _153_720 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _153_721))))
in (

let norm = (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env t))
in if (FStar_Syntax_Util.is_tot_or_gtot_comp comp) then begin
((None), ((FStar_Syntax_Util.comp_result comp)))
end else begin
(match (comp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.GTotal (_)) | (FStar_Syntax_Syntax.Total (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
if ((FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Ghost_lid)) then begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| ((req, _56_1159))::((ens, _56_1154))::_56_1151 -> begin
(let _153_727 = (let _153_724 = (norm req)
in Some (_153_724))
in (let _153_726 = (let _153_725 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _153_725))
in ((_153_727), (_153_726))))
end
| _56_1163 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Effect constructor is not fully applied"), (comp.FStar_Syntax_Syntax.pos)))))
end)
end else begin
(

let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| ((wp, _56_1169))::_56_1166 -> begin
(

let _56_1175 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (_56_1175) with
| (us_r, _56_1174) -> begin
(

let _56_1179 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (_56_1179) with
| (us_e, _56_1178) -> begin
(

let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (

let as_req = (let _153_729 = (let _153_728 = (FStar_Ident.set_lid_range FStar_Syntax_Const.as_requires r)
in (FStar_Syntax_Syntax.fvar _153_728 FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _153_729 us_r))
in (

let as_ens = (let _153_731 = (let _153_730 = (FStar_Ident.set_lid_range FStar_Syntax_Const.as_ensures r)
in (FStar_Syntax_Syntax.fvar _153_730 FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _153_731 us_e))
in (

let req = (let _153_734 = (let _153_733 = (let _153_732 = (FStar_Syntax_Syntax.as_arg wp)
in (_153_732)::[])
in (((ct.FStar_Syntax_Syntax.result_typ), (Some (FStar_Syntax_Syntax.imp_tag))))::_153_733)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _153_734 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let ens = (let _153_737 = (let _153_736 = (let _153_735 = (FStar_Syntax_Syntax.as_arg wp)
in (_153_735)::[])
in (((ct.FStar_Syntax_Syntax.result_typ), (Some (FStar_Syntax_Syntax.imp_tag))))::_153_736)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _153_737 None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _153_741 = (let _153_738 = (norm req)
in Some (_153_738))
in (let _153_740 = (let _153_739 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm _153_739))
in ((_153_741), (_153_740)))))))))
end))
end))
end
| _56_1186 -> begin
(FStar_All.failwith "Impossible")
end))
end
end)
end)))


let maybe_instantiate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let torig = (FStar_Syntax_Subst.compress t)
in if (not (env.FStar_TypeChecker_Env.instantiate_imp)) then begin
((e), (torig), (FStar_TypeChecker_Rel.trivial_guard))
end else begin
(match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _56_1197 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_56_1197) with
| (bs, c) -> begin
(

let rec aux = (fun subst _56_4 -> (match (_56_4) with
| ((x, Some (FStar_Syntax_Syntax.Implicit (dot))))::rest -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let _56_1213 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t)
in (match (_56_1213) with
| (v, _56_1211, g) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (v))))::subst
in (

let _56_1219 = (aux subst rest)
in (match (_56_1219) with
| (args, bs, subst, g') -> begin
(let _153_752 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((v), (Some (FStar_Syntax_Syntax.Implicit (dot)))))::args), (bs), (subst), (_153_752)))
end)))
end)))
end
| bs -> begin
(([]), (bs), (subst), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (

let _56_1225 = (aux [] bs)
in (match (_56_1225) with
| (args, bs, subst, guard) -> begin
(match (((args), (bs))) with
| ([], _56_1228) -> begin
((e), (torig), (guard))
end
| (_56_1231, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
((e), (torig), (FStar_TypeChecker_Rel.trivial_guard))
end
| _56_1235 -> begin
(

let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _56_1238 -> begin
(FStar_Syntax_Util.arrow bs c)
end)
in (

let t = (FStar_Syntax_Subst.subst subst t)
in (

let e = (FStar_Syntax_Syntax.mk_Tm_app e args (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((e), (t), (guard)))))
end)
end)))
end))
end
| _56_1243 -> begin
((e), (t), (FStar_TypeChecker_Rel.trivial_guard))
end)
end))


let string_of_univs = (fun univs -> (let _153_757 = (let _153_756 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _153_756 (FStar_List.map (fun u -> (let _153_755 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _153_755 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _153_757 (FStar_String.concat ", "))))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(

let s = (let _153_763 = (let _153_762 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _153_762))
in (FStar_All.pipe_right _153_763 FStar_Util.set_elements))
in (

let _56_1249 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _153_765 = (let _153_764 = (FStar_TypeChecker_Env.univ_vars env)
in (string_of_univs _153_764))
in (FStar_Util.print1 "univ_vars in env: %s\n" _153_765))
end else begin
()
end
in (

let r = (let _153_766 = (FStar_TypeChecker_Env.get_range env)
in Some (_153_766))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (

let _56_1254 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _153_771 = (let _153_768 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _153_768))
in (let _153_770 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _153_769 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _153_771 _153_770 _153_769))))
end else begin
()
end
in (

let _56_1256 = (FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))))
in u_name))))))
in u_names))))
end)


let maybe_set_tk = (fun ts _56_5 -> (match (_56_5) with
| None -> begin
ts
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Syntax.mk t None FStar_Range.dummyRange)
in (

let t = (FStar_Syntax_Subst.close_univ_vars (Prims.fst ts) t)
in (

let _56_1266 = (FStar_ST.op_Colon_Equals (Prims.snd ts).FStar_Syntax_Syntax.tk (Some (t.FStar_Syntax_Syntax.n)))
in ts)))
end))


let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t0)
in (

let univs = (FStar_Syntax_Free.univs t)
in (

let _56_1272 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _153_778 = (string_of_univs univs)
in (FStar_Util.print1 "univs to gen : %s\n" _153_778))
end else begin
()
end
in (

let gen = (gen_univs env univs)
in (

let _56_1275 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _153_779 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _153_779))
end else begin
()
end
in (

let ts = (FStar_Syntax_Subst.close_univ_vars gen t)
in (let _153_780 = (FStar_ST.read t0.FStar_Syntax_Syntax.tk)
in (maybe_set_tk ((gen), (ts)) _153_780)))))))))


let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> if (let _153_786 = (FStar_Util.for_all (fun _56_1283 -> (match (_56_1283) with
| (_56_1281, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _153_786)) then begin
None
end else begin
(

let norm = (fun c -> (

let _56_1286 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _153_789 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _153_789))
end else begin
()
end
in (

let c = if (FStar_TypeChecker_Env.should_verify env) then begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::[]) env c)
end else begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env c)
end
in (

let _56_1289 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _153_790 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _153_790))
end else begin
()
end
in c))))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (let _153_793 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _153_793 FStar_Util.set_elements)))
in (

let _56_1305 = (let _153_795 = (FStar_All.pipe_right ecs (FStar_List.map (fun _56_1296 -> (match (_56_1296) with
| (e, c) -> begin
(

let t = (FStar_All.pipe_right (FStar_Syntax_Util.comp_result c) FStar_Syntax_Subst.compress)
in (

let c = (norm c)
in (

let t = (FStar_Syntax_Util.comp_result c)
in (

let univs = (FStar_Syntax_Free.univs t)
in (

let uvt = (FStar_Syntax_Free.uvars t)
in (

let uvs = (gen_uvars uvt)
in ((univs), (((uvs), (e), (c))))))))))
end))))
in (FStar_All.pipe_right _153_795 FStar_List.unzip))
in (match (_56_1305) with
| (univs, uvars) -> begin
(

let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (

let gen_univs = (gen_univs env univs)
in (

let _56_1309 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end else begin
()
end
in (

let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _56_1314 -> (match (_56_1314) with
| (uvs, e, c) -> begin
(

let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _56_1317 -> (match (_56_1317) with
| (u, k) -> begin
(match ((FStar_Unionfind.find u)) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
((a), (Some (FStar_Syntax_Syntax.imp_tag)))
end
| FStar_Syntax_Syntax.Fixed (_56_1351) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _56_1354 -> begin
(

let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (

let _56_1358 = (FStar_Syntax_Util.arrow_formals k)
in (match (_56_1358) with
| (bs, kres) -> begin
(

let a = (let _153_801 = (let _153_800 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _153_799 -> Some (_153_799)) _153_800))
in (FStar_Syntax_Syntax.new_bv _153_801 kres))
in (

let t = (let _153_806 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _153_805 = (let _153_804 = (let _153_803 = (let _153_802 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _153_802))
in FStar_Util.Inl (_153_803))
in Some (_153_804))
in (FStar_Syntax_Util.abs bs _153_806 _153_805)))
in (

let _56_1361 = (FStar_Syntax_Util.set_uvar u t)
in ((a), (Some (FStar_Syntax_Syntax.imp_tag))))))
end)))
end)
end))))
in (

let _56_1393 = (match (((tvars), (gen_univs))) with
| ([], []) -> begin
((e), (c))
end
| ([], _56_1369) -> begin
(

let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoInline)::[]) env c)
in (

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoInline)::[]) env e)
in ((e), (c))))
end
| _56_1374 -> begin
(

let _56_1377 = ((e), (c))
in (match (_56_1377) with
| (e0, c0) -> begin
(

let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoInline)::(FStar_TypeChecker_Normalize.CompressUvars)::[]) env c)
in (

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoInline)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Iota))::[]) env e)
in (

let t = (match ((let _153_807 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _153_807.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(

let _56_1386 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (_56_1386) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| _56_1388 -> begin
(FStar_Syntax_Util.arrow tvars c)
end)
in (

let e' = (FStar_Syntax_Util.abs tvars e (Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp c)))))
in (let _153_808 = (FStar_Syntax_Syntax.mk_Total t)
in ((e'), (_153_808)))))))
end))
end)
in (match (_56_1393) with
| (e, c) -> begin
((gen_univs), (e), (c))
end)))
end))))
in Some (ecs)))))
end)))))
end)


let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> (

let _56_1403 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _153_815 = (let _153_814 = (FStar_List.map (fun _56_1402 -> (match (_56_1402) with
| (lb, _56_1399, _56_1401) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _153_814 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _153_815))
end else begin
()
end
in (match ((let _153_817 = (FStar_All.pipe_right lecs (FStar_List.map (fun _56_1409 -> (match (_56_1409) with
| (_56_1406, e, c) -> begin
((e), (c))
end))))
in (gen env _153_817))) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun _56_1414 -> (match (_56_1414) with
| (l, t, c) -> begin
((l), ([]), (t), (c))
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _56_1422 _56_1426 -> (match (((_56_1422), (_56_1426))) with
| ((l, _56_1419, _56_1421), (us, e, c)) -> begin
(

let _56_1427 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _153_824 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _153_823 = (FStar_Syntax_Print.lbname_to_string l)
in (let _153_822 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (let _153_821 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print4 "(%s) Generalized %s at type %s\n%s\n" _153_824 _153_823 _153_822 _153_821)))))
end else begin
()
end
in ((l), (us), (e), (c)))
end)) lecs ecs)
end)))


let check_and_ascribe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t) = (fun env e t1 t2 -> (

let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let check = (fun env t1 t2 -> if env.FStar_TypeChecker_Env.use_eq then begin
(FStar_TypeChecker_Rel.try_teq env t1 t2)
end else begin
(match ((FStar_TypeChecker_Rel.try_subtype env t1 t2)) with
| None -> begin
None
end
| Some (f) -> begin
(let _153_840 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _153_839 -> Some (_153_839)) _153_840))
end)
end)
in (

let is_var = (fun e -> (match ((let _153_843 = (FStar_Syntax_Subst.compress e)
in _153_843.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (_56_1444) -> begin
true
end
| _56_1447 -> begin
false
end))
in (

let decorate = (fun e t -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((

let _56_1454 = x
in {FStar_Syntax_Syntax.ppname = _56_1454.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_1454.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| _56_1457 -> begin
(

let _56_1458 = e
in (let _153_848 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _56_1458.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _153_848; FStar_Syntax_Syntax.pos = _56_1458.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _56_1458.FStar_Syntax_Syntax.vars}))
end)))
in (

let env = (

let _56_1460 = env
in (let _153_849 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _56_1460.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _56_1460.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _56_1460.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _56_1460.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _56_1460.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _56_1460.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _56_1460.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _56_1460.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _56_1460.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _56_1460.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _56_1460.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _56_1460.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _56_1460.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _56_1460.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _56_1460.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _153_849; FStar_TypeChecker_Env.is_iface = _56_1460.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _56_1460.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _56_1460.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _56_1460.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _56_1460.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _56_1460.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _56_1460.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _56_1460.FStar_TypeChecker_Env.qname_and_index}))
in (match ((check env t1 t2)) with
| None -> begin
(let _153_853 = (let _153_852 = (let _153_851 = (FStar_TypeChecker_Errors.expected_expression_of_type env t2 e t1)
in (let _153_850 = (FStar_TypeChecker_Env.get_range env)
in ((_153_851), (_153_850))))
in FStar_Syntax_Syntax.Error (_153_852))
in (Prims.raise _153_853))
end
| Some (g) -> begin
(

let _56_1466 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _153_854 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _153_854))
end else begin
()
end
in (let _153_855 = (decorate e t2)
in ((_153_855), (g))))
end)))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (

let discharge = (fun g -> (

let _56_1473 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _153_865 = (discharge g)
in (let _153_864 = (lc.FStar_Syntax_Syntax.comp ())
in ((_153_865), (_153_864))))
end else begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let steps = (FStar_TypeChecker_Normalize.Beta)::[]
in (

let c = (let _153_868 = (let _153_867 = (let _153_866 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (FStar_All.pipe_right _153_866 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right _153_867 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (FStar_All.pipe_right _153_868 (FStar_TypeChecker_Normalize.comp_to_comp_typ env)))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let _56_1483 = (destruct_comp c)
in (match (_56_1483) with
| (u_t, t, wp) -> begin
(

let vc = (let _153_874 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.trivial)
in (let _153_873 = (let _153_871 = (FStar_Syntax_Syntax.as_arg t)
in (let _153_870 = (let _153_869 = (FStar_Syntax_Syntax.as_arg wp)
in (_153_869)::[])
in (_153_871)::_153_870))
in (let _153_872 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk_Tm_app _153_874 _153_873 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _153_872))))
in (

let _56_1485 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _153_875 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _153_875))
end else begin
()
end
in (

let g = (let _153_876 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _153_876))
in (let _153_878 = (discharge g)
in (let _153_877 = (FStar_Syntax_Syntax.mk_Comp c)
in ((_153_878), (_153_877)))))))
end))))))
end)))


let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (

let short_bin_op = (fun f _56_6 -> (match (_56_6) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((fst, _56_1496))::[] -> begin
(f fst)
end
| _56_1500 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (

let op_and_e = (fun e -> (let _153_899 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _153_899 (fun _153_898 -> FStar_TypeChecker_Common.NonTrivial (_153_898)))))
in (

let op_or_e = (fun e -> (let _153_904 = (let _153_902 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _153_902))
in (FStar_All.pipe_right _153_904 (fun _153_903 -> FStar_TypeChecker_Common.NonTrivial (_153_903)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _153_907 -> FStar_TypeChecker_Common.NonTrivial (_153_907))))
in (

let op_or_t = (fun t -> (let _153_911 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _153_911 (fun _153_910 -> FStar_TypeChecker_Common.NonTrivial (_153_910)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _153_914 -> FStar_TypeChecker_Common.NonTrivial (_153_914))))
in (

let short_op_ite = (fun _56_7 -> (match (_56_7) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((guard, _56_1515))::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| (_then)::((guard, _56_1520))::[] -> begin
(let _153_918 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _153_918 (fun _153_917 -> FStar_TypeChecker_Common.NonTrivial (_153_917))))
end
| _56_1525 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (

let table = (((FStar_Syntax_Const.op_And), ((short_bin_op op_and_e))))::(((FStar_Syntax_Const.op_Or), ((short_bin_op op_or_e))))::(((FStar_Syntax_Const.and_lid), ((short_bin_op op_and_t))))::(((FStar_Syntax_Const.or_lid), ((short_bin_op op_or_t))))::(((FStar_Syntax_Const.imp_lid), ((short_bin_op op_imp_t))))::(((FStar_Syntax_Const.ite_lid), (short_op_ite)))::[]
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((FStar_Util.find_map table (fun _56_1533 -> (match (_56_1533) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _153_951 = (mk seen_args)
in Some (_153_951))
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
| _56_1538 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (match ((let _153_954 = (FStar_Syntax_Util.un_uinst l)
in _153_954.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| _56_1543 -> begin
false
end))


let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (

let pos = (fun bs -> (match (bs) with
| ((hd, _56_1552))::_56_1549 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| _56_1556 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| ((_56_1560, Some (FStar_Syntax_Syntax.Implicit (_56_1562))))::_56_1558 -> begin
bs
end
| _56_1568 -> begin
(match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
bs
end
| Some (t) -> begin
(match ((let _153_961 = (FStar_Syntax_Subst.compress t)
in _153_961.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', _56_1574) -> begin
(match ((FStar_Util.prefix_until (fun _56_8 -> (match (_56_8) with
| (_56_1579, Some (FStar_Syntax_Syntax.Implicit (_56_1581))) -> begin
false
end
| _56_1586 -> begin
true
end)) bs')) with
| None -> begin
bs
end
| Some ([], _56_1590, _56_1592) -> begin
bs
end
| Some (imps, _56_1597, _56_1599) -> begin
if (FStar_All.pipe_right imps (FStar_Util.for_all (fun _56_1605 -> (match (_56_1605) with
| (x, _56_1604) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end)))) then begin
(

let r = (pos bs)
in (

let imps = (FStar_All.pipe_right imps (FStar_List.map (fun _56_1609 -> (match (_56_1609) with
| (x, i) -> begin
(let _153_965 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in ((_153_965), (i)))
end))))
in (FStar_List.append imps bs)))
end else begin
bs
end
end)
end
| _56_1612 -> begin
bs
end)
end)
end)))


let maybe_lift : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env e c1 c2 -> (

let m1 = (FStar_TypeChecker_Env.norm_eff_name env c1)
in (

let m2 = (FStar_TypeChecker_Env.norm_eff_name env c2)
in if ((FStar_Ident.lid_equals m1 m2) || (FStar_Syntax_Util.is_pure_effect c1)) then begin
e
end else begin
(let _153_974 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m2))))))) _153_974 e.FStar_Syntax_Syntax.pos))
end)))


let maybe_monadic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c t -> (

let m = (FStar_TypeChecker_Env.norm_eff_name env c)
in if (((is_pure_or_ghost_effect env m) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid)) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid)) then begin
e
end else begin
(let _153_983 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))) _153_983 e.FStar_Syntax_Syntax.pos))
end))


let effect_repr_aux = (fun only_reifiable env c u_c -> (match ((let _153_988 = (FStar_TypeChecker_Env.norm_eff_name env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_TypeChecker_Env.effect_decl_opt env _153_988))) with
| None -> begin
None
end
| Some (ed) -> begin
if (only_reifiable && (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))))) then begin
None
end else begin
(match (ed.FStar_Syntax_Syntax.repr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
None
end
| _56_1633 -> begin
(

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _56_1637 = (let _153_989 = (FStar_List.hd c.FStar_Syntax_Syntax.effect_args)
in ((c.FStar_Syntax_Syntax.result_typ), (_153_989)))
in (match (_56_1637) with
| (res_typ, wp) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_c)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (let _153_995 = (let _153_994 = (let _153_992 = (let _153_991 = (let _153_990 = (FStar_Syntax_Syntax.as_arg res_typ)
in (_153_990)::(wp)::[])
in ((repr), (_153_991)))
in FStar_Syntax_Syntax.Tm_app (_153_992))
in (let _153_993 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _153_994 None _153_993)))
in Some (_153_995)))
end)))
end)
end
end))


let effect_repr : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term Prims.option = (fun env c u_c -> (effect_repr_aux false env c u_c))


let reify_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term = (fun env c u_c -> (

let no_reify = (fun l -> (let _153_1013 = (let _153_1012 = (let _153_1011 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _153_1010 = (FStar_TypeChecker_Env.get_range env)
in ((_153_1011), (_153_1010))))
in FStar_Syntax_Syntax.Error (_153_1012))
in (Prims.raise _153_1013)))
in (match ((let _153_1014 = (c.FStar_Syntax_Syntax.comp ())
in (effect_repr_aux true env _153_1014 u_c))) with
| None -> begin
(no_reify c.FStar_Syntax_Syntax.eff_name)
end
| Some (tm) -> begin
tm
end)))


let d : Prims.string  ->  Prims.unit = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))


let mk_toplevel_definition : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term) = (fun env lident def -> (

let _56_1656 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _56_1654 = (d (FStar_Ident.text_of_lid lident))
in (let _153_1023 = (FStar_Syntax_Print.term_to_string def)
in (FStar_Util.print2 "Registering top-level definition: %s\n%s\n" (FStar_Ident.text_of_lid lident) _153_1023)))
end else begin
()
end
in (

let fv = (let _153_1024 = (FStar_Syntax_Util.incr_delta_qualifier def)
in (FStar_Syntax_Syntax.lid_as_fv lident _153_1024 None))
in (

let lbname = FStar_Util.Inr (fv)
in (

let lb = ((false), (({FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = def})::[]))
in (

let sig_ctx = FStar_Syntax_Syntax.Sig_let (((lb), (FStar_Range.dummyRange), ((lident)::[]), ((FStar_Syntax_Syntax.Inline)::[])))
in (let _153_1025 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) None FStar_Range.dummyRange)
in ((sig_ctx), (_153_1025)))))))))




