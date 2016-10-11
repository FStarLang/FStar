
open Prims

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv Prims.option * FStar_Syntax_Syntax.lcomp)


let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _150_6 = (FStar_TypeChecker_Env.get_range env)
in (let _150_5 = (FStar_TypeChecker_Errors.failed_to_prove_specification errs)
in (FStar_TypeChecker_Errors.report _150_6 _150_5))))


let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _150_9 = (FStar_Syntax_Subst.compress t)
in _150_9.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_56_19) -> begin
true
end
| _56_22 -> begin
false
end))


let t_binders : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env -> (let _150_13 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right _150_13 (FStar_List.filter (fun _56_27 -> (match (_56_27) with
| (x, _56_26) -> begin
(is_type x.FStar_Syntax_Syntax.sort)
end))))))


let new_uvar_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun env k -> (

let bs = if ((FStar_Options.full_context_dependency ()) || (let _150_18 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _150_18))) then begin
(FStar_TypeChecker_Env.all_binders env)
end else begin
(t_binders env)
end
in (let _150_19 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Rel.new_uvar _150_19 bs k))))


let new_uvar : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env k -> (let _150_24 = (new_uvar_aux env k)
in (Prims.fst _150_24)))


let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun _56_1 -> (match (_56_1) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, _56_42); FStar_Syntax_Syntax.tk = _56_39; FStar_Syntax_Syntax.pos = _56_37; FStar_Syntax_Syntax.vars = _56_35} -> begin
uv
end
| _56_47 -> begin
(FStar_All.failwith "Impossible")
end))


let new_implicit_var : Prims.string  ->  FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.uvar * FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t) = (fun reason r env k -> (match ((FStar_Syntax_Util.destruct k FStar_Syntax_Const.range_of_lid)) with
| Some ((_56_57)::((tm, _56_54))::[]) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))) None tm.FStar_Syntax_Syntax.pos)
in ((t), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
end
| _56_62 -> begin
(

let _56_65 = (new_uvar_aux env k)
in (match (_56_65) with
| (t, u) -> begin
(

let g = (

let _56_66 = FStar_TypeChecker_Rel.trivial_guard
in (let _150_37 = (let _150_36 = (let _150_35 = (as_uvar u)
in ((reason), (env), (_150_35), (t), (k), (r)))
in (_150_36)::[])
in {FStar_TypeChecker_Env.guard_f = _56_66.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _56_66.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_66.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _150_37}))
in (let _150_40 = (let _150_39 = (let _150_38 = (as_uvar u)
in ((_150_38), (r)))
in (_150_39)::[])
in ((t), (_150_40), (g))))
end))
end))


let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun r t -> (

let uvs = (FStar_Syntax_Free.uvars t)
in if (not ((FStar_Util.set_is_empty uvs))) then begin
(

let us = (let _150_47 = (let _150_46 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun _56_75 -> (match (_56_75) with
| (x, _56_74) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) _150_46))
in (FStar_All.pipe_right _150_47 (FStar_String.concat ", ")))
in (

let _56_77 = (FStar_Options.push ())
in (

let _56_79 = (FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool (false)))
in (

let _56_81 = (FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)))
in (

let _56_83 = (let _150_49 = (let _150_48 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us _150_48))
in (FStar_TypeChecker_Errors.report r _150_49))
in (FStar_Options.pop ()))))))
end else begin
()
end))


let force_sort' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' = (fun s -> (match ((FStar_ST.read s.FStar_Syntax_Syntax.tk)) with
| None -> begin
(let _150_54 = (let _150_53 = (FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos)
in (let _150_52 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s" _150_53 _150_52)))
in (FStar_All.failwith _150_54))
end
| Some (tk) -> begin
tk
end))


let force_sort = (fun s -> (let _150_56 = (force_sort' s)
in (FStar_Syntax_Syntax.mk _150_56 None s.FStar_Syntax_Syntax.pos)))


let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env _56_98 -> (match (_56_98) with
| {FStar_Syntax_Syntax.lbname = _56_97; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _56_93; FStar_Syntax_Syntax.lbdef = e} -> begin
(

let rng = t.FStar_Syntax_Syntax.pos
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _56_102 = if (univ_vars <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let mk_binder = (fun scope a -> (match ((let _150_65 = (FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort)
in _150_65.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _56_112 = (FStar_Syntax_Util.type_u ())
in (match (_56_112) with
| (k, _56_111) -> begin
(

let t = (let _150_66 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right _150_66 Prims.fst))
in (((

let _56_114 = a
in {FStar_Syntax_Syntax.ppname = _56_114.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_114.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (false)))
end))
end
| _56_117 -> begin
((a), (true))
end))
in (

let rec aux = (fun vars e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, _56_124) -> begin
(aux vars e)
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _56_130) -> begin
((t), (true))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _56_136) -> begin
(

let _56_155 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _56_142 _56_145 -> (match (((_56_142), (_56_145))) with
| ((scope, bs, check), (a, imp)) -> begin
(

let _56_148 = (mk_binder scope a)
in (match (_56_148) with
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
in (match (_56_155) with
| (scope, bs, check) -> begin
(

let _56_158 = (aux scope body)
in (match (_56_158) with
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

let _56_165 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _150_74 = (FStar_Range.string_of_range r)
in (let _150_73 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _150_74 _150_73)))
end else begin
()
end
in ((FStar_Util.Inl (t)), ((check_res || check))))))
end))
end))
end
| _56_168 -> begin
(let _150_77 = (let _150_76 = (let _150_75 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _150_75 Prims.fst))
in FStar_Util.Inl (_150_76))
in ((_150_77), (false)))
end)))
in (

let _56_171 = (let _150_78 = (t_binders env)
in (aux _150_78 e))
in (match (_56_171) with
| (t, b) -> begin
(

let t = (match (t) with
| FStar_Util.Inr (c) -> begin
(let _150_82 = (let _150_81 = (let _150_80 = (let _150_79 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" _150_79))
in ((_150_80), (rng)))
in FStar_Syntax_Syntax.Error (_150_81))
in (Prims.raise _150_82))
end
| FStar_Util.Inl (t) -> begin
t
end)
in (([]), (t), (b)))
end))))))
end
| _56_178 -> begin
(

let _56_181 = (FStar_Syntax_Subst.open_univ_vars univ_vars t)
in (match (_56_181) with
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
| FStar_Syntax_Syntax.Pat_dot_term (x, _56_194) -> begin
(

let _56_200 = (FStar_Syntax_Util.type_u ())
in (match (_56_200) with
| (k, _56_199) -> begin
(

let t = (new_uvar env k)
in (

let x = (

let _56_202 = x
in {FStar_Syntax_Syntax.ppname = _56_202.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_202.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let _56_207 = (let _150_95 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _150_95 t))
in (match (_56_207) with
| (e, u) -> begin
(

let p = (

let _56_208 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (e))); FStar_Syntax_Syntax.ty = _56_208.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_208.FStar_Syntax_Syntax.p})
in (([]), ([]), ([]), (env), (e), (p)))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let _56_216 = (FStar_Syntax_Util.type_u ())
in (match (_56_216) with
| (t, _56_215) -> begin
(

let x = (

let _56_217 = x
in (let _150_96 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _56_217.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_217.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_96}))
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

let _56_227 = (FStar_Syntax_Util.type_u ())
in (match (_56_227) with
| (t, _56_226) -> begin
(

let x = (

let _56_228 = x
in (let _150_97 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _56_228.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_228.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_97}))
in (

let env = (FStar_TypeChecker_Env.push_bv env x)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in (((x)::[]), ((x)::[]), ([]), (env), (e), (p)))))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _56_261 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _56_243 _56_246 -> (match (((_56_243), (_56_246))) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(

let _56_253 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_56_253) with
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
in (match (_56_261) with
| (b, a, w, env, args, pats) -> begin
(

let e = (let _150_104 = (let _150_103 = (let _150_102 = (let _150_101 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (let _150_100 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app _150_101 _150_100 None p.FStar_Syntax_Syntax.p)))
in ((_150_102), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))
in FStar_Syntax_Syntax.Tm_meta (_150_103))
in (FStar_Syntax_Syntax.mk _150_104 None p.FStar_Syntax_Syntax.p))
in (let _150_107 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _150_106 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _150_105 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in ((_150_107), (_150_106), (_150_105), (env), (e), ((

let _56_263 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _56_263.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_263.FStar_Syntax_Syntax.p})))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (_56_266) -> begin
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

let pats = (FStar_List.map (fun _56_281 -> (match (_56_281) with
| (p, imp) -> begin
(let _150_119 = (elaborate_pat env p)
in ((_150_119), (imp)))
end)) pats)
in (

let _56_286 = (FStar_TypeChecker_Env.lookup_datacon env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_56_286) with
| (_56_284, t) -> begin
(

let _56_290 = (FStar_Syntax_Util.arrow_formals t)
in (match (_56_290) with
| (f, _56_289) -> begin
(

let rec aux = (fun formals pats -> (match (((formals), (pats))) with
| ([], []) -> begin
[]
end
| ([], (_56_301)::_56_299) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Too many pattern arguments"), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))))
end
| ((_56_307)::_56_305, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun _56_313 -> (match (_56_313) with
| (t, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(

let a = (let _150_126 = (let _150_125 = (FStar_Syntax_Syntax.range_of_bv t)
in Some (_150_125))
in (FStar_Syntax_Syntax.new_bv _150_126 FStar_Syntax_Syntax.tun))
in (

let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (let _150_127 = (maybe_dot inaccessible a r)
in ((_150_127), (true)))))
end
| _56_320 -> begin
(let _150_131 = (let _150_130 = (let _150_129 = (let _150_128 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _150_128))
in ((_150_129), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))
in FStar_Syntax_Syntax.Error (_150_130))
in (Prims.raise _150_131))
end)
end))))
end
| ((f)::formals', ((p, p_imp))::pats') -> begin
(match (f) with
| (_56_331, Some (FStar_Syntax_Syntax.Implicit (_56_333))) when p_imp -> begin
(let _150_132 = (aux formals' pats')
in (((p), (true)))::_150_132)
end
| (_56_338, Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(

let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let p = (maybe_dot inaccessible a (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
in (let _150_133 = (aux formals' pats)
in (((p), (true)))::_150_133)))
end
| (_56_346, imp) -> begin
(let _150_136 = (let _150_134 = (FStar_Syntax_Syntax.is_implicit imp)
in ((p), (_150_134)))
in (let _150_135 = (aux formals' pats')
in (_150_136)::_150_135))
end)
end))
in (

let _56_349 = p
in (let _150_139 = (let _150_138 = (let _150_137 = (aux f pats)
in ((fv), (_150_137)))
in FStar_Syntax_Syntax.Pat_cons (_150_138))
in {FStar_Syntax_Syntax.v = _150_139; FStar_Syntax_Syntax.ty = _56_349.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_349.FStar_Syntax_Syntax.p})))
end))
end)))
end
| _56_352 -> begin
p
end)))
in (

let one_pat = (fun allow_wc_dependence env p -> (

let p = (elaborate_pat env p)
in (

let _56_364 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_56_364) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))) with
| Some (x) -> begin
(let _150_148 = (let _150_147 = (let _150_146 = (FStar_TypeChecker_Errors.nonlinear_pattern_variable x)
in ((_150_146), (p.FStar_Syntax_Syntax.p)))
in FStar_Syntax_Syntax.Error (_150_147))
in (Prims.raise _150_148))
end
| _56_368 -> begin
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

let _56_384 = (one_pat false env q)
in (match (_56_384) with
| (b, a, _56_381, te, q) -> begin
(

let _56_399 = (FStar_List.fold_right (fun p _56_389 -> (match (_56_389) with
| (w, args, pats) -> begin
(

let _56_395 = (one_pat false env p)
in (match (_56_395) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv FStar_Syntax_Syntax.bv_eq a a'))) then begin
(let _150_158 = (let _150_157 = (let _150_156 = (FStar_TypeChecker_Errors.disjunctive_pattern_vars a a')
in (let _150_155 = (FStar_TypeChecker_Env.get_range env)
in ((_150_156), (_150_155))))
in FStar_Syntax_Syntax.Error (_150_157))
in (Prims.raise _150_158))
end else begin
(let _150_160 = (let _150_159 = (FStar_Syntax_Syntax.as_arg arg)
in (_150_159)::args)
in (((FStar_List.append w' w)), (_150_160), ((p)::pats)))
end
end))
end)) pats (([]), ([]), ([])))
in (match (_56_399) with
| (w, args, pats) -> begin
(let _150_162 = (let _150_161 = (FStar_Syntax_Syntax.as_arg te)
in (_150_161)::args)
in (((FStar_List.append b w)), (_150_162), ((

let _56_400 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((q)::pats); FStar_Syntax_Syntax.ty = _56_400.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_400.FStar_Syntax_Syntax.p}))))
end))
end))
end
| _56_403 -> begin
(

let _56_411 = (one_pat true env p)
in (match (_56_411) with
| (b, _56_406, _56_408, arg, p) -> begin
(let _150_164 = (let _150_163 = (FStar_Syntax_Syntax.as_arg arg)
in (_150_163)::[])
in ((b), (_150_164), (p)))
end))
end))
in (

let _56_415 = (top_level_pat_as_args env p)
in (match (_56_415) with
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
| (_56_429, FStar_Syntax_Syntax.Tm_uinst (e, _56_432)) -> begin
(aux p e)
end
| (FStar_Syntax_Syntax.Pat_constant (_56_437), FStar_Syntax_Syntax.Tm_constant (_56_440)) -> begin
(let _150_179 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v _150_179))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(

let _56_448 = if (not ((FStar_Syntax_Syntax.bv_eq x y))) then begin
(let _150_182 = (let _150_181 = (FStar_Syntax_Print.bv_to_string x)
in (let _150_180 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _150_181 _150_180)))
in (FStar_All.failwith _150_182))
end else begin
()
end
in (

let _56_450 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _150_184 = (FStar_Syntax_Print.bv_to_string x)
in (let _150_183 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _150_184 _150_183)))
end else begin
()
end
in (

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x = (

let _56_453 = x
in {FStar_Syntax_Syntax.ppname = _56_453.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_453.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x)) s.FStar_Syntax_Syntax.n)))))
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(

let _56_461 = if (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation) then begin
(let _150_187 = (let _150_186 = (FStar_Syntax_Print.bv_to_string x)
in (let _150_185 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _150_186 _150_185)))
in (FStar_All.failwith _150_187))
end else begin
()
end
in (

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x = (

let _56_464 = x
in {FStar_Syntax_Syntax.ppname = _56_464.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_464.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x)) s.FStar_Syntax_Syntax.n))))
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _56_469), _56_473) -> begin
(

let s = (force_sort e)
in (

let x = (

let _56_476 = x
in {FStar_Syntax_Syntax.ppname = _56_476.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_476.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term (((x), (e)))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
(

let _56_486 = if (not ((FStar_Syntax_Syntax.fv_eq fv fv'))) then begin
(let _150_188 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _150_188))
end else begin
()
end
in (let _150_189 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv'), ([])))) _150_189)))
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
(

let _56_529 = if (let _150_190 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right _150_190 Prims.op_Negation)) then begin
(let _150_191 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _150_191))
end else begin
()
end
in (

let fv = fv'
in (

let rec match_args = (fun matched_pats args argpats -> (match (((args), (argpats))) with
| ([], []) -> begin
(let _150_198 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev matched_pats))))) _150_198))
end
| ((arg)::args, ((argpat, _56_545))::argpats) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e, Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (_56_555)) -> begin
(

let x = (let _150_199 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _150_199))
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e)))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args argpats)))
end
| ((e, imp), _56_564) -> begin
(

let pat = (let _150_201 = (aux argpat e)
in (let _150_200 = (FStar_Syntax_Syntax.is_implicit imp)
in ((_150_201), (_150_200))))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _56_568 -> begin
(let _150_204 = (let _150_203 = (FStar_Syntax_Print.pat_to_string p)
in (let _150_202 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _150_203 _150_202)))
in (FStar_All.failwith _150_204))
end))
in (match_args [] args argpats))))
end
| _56_570 -> begin
(let _150_209 = (let _150_208 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (let _150_207 = (FStar_Syntax_Print.pat_to_string qq)
in (let _150_206 = (let _150_205 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right _150_205 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _150_208 _150_207 _150_206))))
in (FStar_All.failwith _150_209))
end))))
in (match (((p.FStar_Syntax_Syntax.v), (exps))) with
| (FStar_Syntax_Syntax.Pat_disj (ps), _56_574) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(

let ps = (FStar_List.map2 aux ps exps)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj (ps)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p))
end
| (_56_578, (e)::[]) -> begin
(aux p e)
end
| _56_583 -> begin
(FStar_All.failwith "Unexpected number of patterns")
end))))


let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (

let topt = Some (pat.FStar_Syntax_Syntax.ty)
in (

let mk = (fun f -> (FStar_Syntax_Syntax.mk f topt pat.FStar_Syntax_Syntax.p))
in (

let pat_as_arg = (fun _56_591 -> (match (_56_591) with
| (p, i) -> begin
(

let _56_594 = (decorated_pattern_as_term p)
in (match (_56_594) with
| (vars, te) -> begin
(let _150_217 = (let _150_216 = (FStar_Syntax_Syntax.as_implicit i)
in ((te), (_150_216)))
in ((vars), (_150_217)))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_56_596) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _150_218 = (mk (FStar_Syntax_Syntax.Tm_constant (c)))
in (([]), (_150_218)))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(let _150_219 = (mk (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (_150_219)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _56_609 = (let _150_220 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _150_220 FStar_List.unzip))
in (match (_56_609) with
| (vars, args) -> begin
(

let vars = (FStar_List.flatten vars)
in (let _150_224 = (let _150_223 = (let _150_222 = (let _150_221 = (FStar_Syntax_Syntax.fv_to_tm fv)
in ((_150_221), (args)))
in FStar_Syntax_Syntax.Tm_app (_150_222))
in (mk _150_223))
in ((vars), (_150_224))))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
(([]), (e))
end)))))


let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun c -> (

let wp = (match (c.FStar_Syntax_Syntax.effect_args) with
| ((wp, _56_618))::[] -> begin
wp
end
| _56_622 -> begin
(let _150_230 = (let _150_229 = (let _150_228 = (FStar_List.map (fun _56_626 -> (match (_56_626) with
| (x, _56_625) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right _150_228 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str _150_229))
in (FStar_All.failwith _150_230))
end)
in (let _150_231 = (FStar_List.hd c.FStar_Syntax_Syntax.comp_univs)
in ((_150_231), (c.FStar_Syntax_Syntax.result_typ), (wp)))))


let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (

let _56_635 = (destruct_comp c)
in (match (_56_635) with
| (u, _56_633, wp) -> begin
(let _150_250 = (let _150_249 = (let _150_248 = (lift c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _150_248))
in (_150_249)::[])
in {FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _150_250; FStar_Syntax_Syntax.flags = []})
end)))


let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let _56_644 = (let _150_258 = (FStar_TypeChecker_Env.norm_eff_name env l1)
in (let _150_257 = (FStar_TypeChecker_Env.norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _150_258 _150_257)))
in (match (_56_644) with
| (m, _56_641, _56_643) -> begin
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

let _56_656 = (FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (_56_656) with
| (m, lift1, lift2) -> begin
(

let m1 = (lift_comp c1 m lift1)
in (

let m2 = (lift_comp c2 m lift2)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (

let _56_662 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (_56_662) with
| (a, kwp) -> begin
(let _150_272 = (destruct_comp m1)
in (let _150_271 = (destruct_comp m2)
in ((((md), (a), (kwp))), (_150_272), (_150_271))))
end)))))
end)))))


let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid))))


let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md u_result result wp flags -> (let _150_293 = (let _150_292 = (let _150_291 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_291)::[])
in {FStar_Syntax_Syntax.comp_univs = (u_result)::[]; FStar_Syntax_Syntax.effect_name = md.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = _150_292; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp _150_293)))


let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (

let _56_676 = lc
in (let _150_300 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _56_676.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _150_300; FStar_Syntax_Syntax.cflags = _56_676.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _56_678 -> (match (()) with
| () -> begin
(let _150_299 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _150_299))
end))})))


let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _150_303 = (FStar_Syntax_Subst.compress t)
in _150_303.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_56_681) -> begin
true
end
| _56_684 -> begin
false
end))


let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v -> (

let c = if (let _150_310 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation _150_310)) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(

let m = (let _150_311 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must _150_311))
in (

let _56_691 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_56_691) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let u_t = (env.FStar_TypeChecker_Env.universe_of env t)
in (

let wp = (let _150_317 = (let _150_316 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env m m.FStar_Syntax_Syntax.ret_wp)
in (let _150_315 = (let _150_314 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_313 = (let _150_312 = (FStar_Syntax_Syntax.as_arg v)
in (_150_312)::[])
in (_150_314)::_150_313))
in (FStar_Syntax_Syntax.mk_Tm_app _150_316 _150_315 (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _150_317))
in (mk_comp m u_t t wp ((FStar_Syntax_Syntax.RETURN)::[])))))
end)))
end
in (

let _56_696 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return"))) then begin
(let _150_320 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _150_319 = (FStar_Syntax_Print.term_to_string v)
in (let _150_318 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _150_320 _150_319 _150_318))))
end else begin
()
end
in c)))


let bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r1 env e1opt lc1 _56_704 -> (match (_56_704) with
| (b, lc2) -> begin
(

let lc1 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1)
in (

let lc2 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2)
in (

let _56_714 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(

let bstr = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _150_333 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (let _150_332 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _150_331 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" _150_333 _150_332 bstr _150_331)))))
end else begin
()
end
in (

let bind_it = (fun _56_717 -> (match (()) with
| () -> begin
(

let c1 = (lc1.FStar_Syntax_Syntax.comp ())
in (

let c2 = (lc2.FStar_Syntax_Syntax.comp ())
in (

let _56_723 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _150_340 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _150_339 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _150_338 = (FStar_Syntax_Print.comp_to_string c1)
in (let _150_337 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (let _150_336 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" _150_340 _150_339 _150_338 _150_337 _150_336))))))
end else begin
()
end
in (

let try_simplify = (fun _56_726 -> (match (()) with
| () -> begin
(

let aux = (fun _56_728 -> (match (()) with
| () -> begin
if (FStar_Syntax_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some (((c2), ("trivial no binder")))
end
| Some (_56_731) -> begin
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
(let _150_348 = (let _150_347 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in ((_150_347), (reason)))
in Some (_150_348))
end
| _56_741 -> begin
(aux ())
end))
in if ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2)) then begin
(subst_c2 "both total")
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2)) then begin
(let _150_350 = (let _150_349 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((_150_349), ("both gtot")))
in Some (_150_350))
end else begin
(match (((e1opt), (b))) with
| (Some (e), Some (x)) -> begin
if ((FStar_Syntax_Util.is_total_comp c1) && (not ((FStar_Syntax_Syntax.is_null_bv x)))) then begin
(subst_c2 "substituted e")
end else begin
(aux ())
end
end
| _56_748 -> begin
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

let _56_766 = (lift_and_destruct env c1 c2)
in (match (_56_766) with
| ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) -> begin
(

let bs = (match (b) with
| None -> begin
(let _150_351 = (FStar_Syntax_Syntax.null_binder t1)
in (_150_351)::[])
end
| Some (x) -> begin
(let _150_352 = (FStar_Syntax_Syntax.mk_binder x)
in (_150_352)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid)))))
in (

let r1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1))) None r1)
in (

let wp_args = (let _150_364 = (FStar_Syntax_Syntax.as_arg r1)
in (let _150_363 = (let _150_362 = (FStar_Syntax_Syntax.as_arg t1)
in (let _150_361 = (let _150_360 = (FStar_Syntax_Syntax.as_arg t2)
in (let _150_359 = (let _150_358 = (FStar_Syntax_Syntax.as_arg wp1)
in (let _150_357 = (let _150_356 = (let _150_355 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg _150_355))
in (_150_356)::[])
in (_150_358)::_150_357))
in (_150_360)::_150_359))
in (_150_362)::_150_361))
in (_150_364)::_150_363))
in (

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t2))))::[]) kwp)
in (

let wp = (let _150_365 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t1)::(u_t2)::[]) env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _150_365 wp_args None t2.FStar_Syntax_Syntax.pos))
in (

let c = (mk_comp md u_t2 t2 wp [])
in c)))))))
end))
end)))))
end))
in (let _150_366 = (join_lcomp env lc1 lc2)
in {FStar_Syntax_Syntax.eff_name = _150_366; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it})))))
end))


let lift_formula : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t mk_wp f -> (

let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (

let _56_785 = (FStar_TypeChecker_Env.wp_signature env md_pure.FStar_Syntax_Syntax.mname)
in (match (_56_785) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let wp = (let _150_378 = (let _150_377 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_376 = (let _150_375 = (FStar_Syntax_Syntax.as_arg f)
in (_150_375)::[])
in (_150_377)::_150_376))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wp _150_378 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (mk_comp md_pure FStar_Syntax_Syntax.U_zero FStar_TypeChecker_Common.t_unit wp [])))
end))))


let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((f), (FStar_Syntax_Syntax.Meta_labeled (((reason), (r), (false))))))) None f.FStar_Syntax_Syntax.pos))


let label_opt : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _150_402 = (FStar_TypeChecker_Env.should_verify env)
in (FStar_All.pipe_left Prims.op_Negation _150_402)) then begin
f
end else begin
(let _150_403 = (reason ())
in (label _150_403 r f))
end
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let _56_804 = g
in (let _150_411 = (let _150_410 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_150_410))
in {FStar_TypeChecker_Env.guard_f = _150_411; FStar_TypeChecker_Env.deferred = _56_804.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_804.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_804.FStar_TypeChecker_Env.implicits}))
end))


let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| _56_815 -> begin
g2
end))


let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun _56_820 -> (match (()) with
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

let _56_829 = (destruct_comp c)
in (match (_56_829) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let wp = (let _150_430 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assume_p)
in (let _150_429 = (let _150_428 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_427 = (let _150_426 = (FStar_Syntax_Syntax.as_arg f)
in (let _150_425 = (let _150_424 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_424)::[])
in (_150_426)::_150_425))
in (_150_428)::_150_427))
in (FStar_Syntax_Syntax.mk_Tm_app _150_430 _150_429 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md u_res_t res_t wp c.FStar_Syntax_Syntax.flags)))
end)))
end
end))
end))
in (

let _56_832 = lc
in {FStar_Syntax_Syntax.eff_name = _56_832.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _56_832.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _56_832.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))


let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> if (FStar_TypeChecker_Rel.is_trivial g0) then begin
((lc), (g0))
end else begin
(

let _56_839 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_450 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _150_449 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _150_450 _150_449)))
end else begin
()
end
in (

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _56_2 -> (match (_56_2) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _56_845 -> begin
[]
end))))
in (

let strengthen = (fun _56_848 -> (match (()) with
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

let xret = (let _150_455 = (let _150_454 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _150_454))
in (FStar_Syntax_Util.comp_set_flags _150_455 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (

let lc = (bind e.FStar_Syntax_Syntax.pos env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) ((Some (x)), ((FStar_Syntax_Util.lcomp_of_comp xret))))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (

let _56_858 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_457 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _150_456 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _150_457 _150_456)))
end else begin
()
end
in (

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _56_864 = (destruct_comp c)
in (match (_56_864) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let wp = (let _150_466 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assert_p)
in (let _150_465 = (let _150_464 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_463 = (let _150_462 = (let _150_459 = (let _150_458 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason _150_458 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _150_459))
in (let _150_461 = (let _150_460 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_460)::[])
in (_150_462)::_150_461))
in (_150_464)::_150_463))
in (FStar_Syntax_Syntax.mk_Tm_app _150_466 _150_465 None wp.FStar_Syntax_Syntax.pos)))
in (

let _56_867 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_467 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _150_467))
end else begin
()
end
in (

let c2 = (mk_comp md u_res_t res_t wp flags)
in c2))))
end)))))
end)))
end))
in (let _150_471 = (

let _56_870 = lc
in (let _150_470 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _150_469 = if ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _150_468 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _150_468))) then begin
flags
end else begin
[]
end
in {FStar_Syntax_Syntax.eff_name = _150_470; FStar_Syntax_Syntax.res_typ = _56_870.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _150_469; FStar_Syntax_Syntax.comp = strengthen})))
in ((_150_471), ((

let _56_872 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _56_872.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_872.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_872.FStar_TypeChecker_Env.implicits})))))))
end)


let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env comp res_t -> (

let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let y = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let _56_882 = (let _150_479 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _150_478 = (FStar_Syntax_Syntax.bv_to_name y)
in ((_150_479), (_150_478))))
in (match (_56_882) with
| (xexp, yexp) -> begin
(

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let yret = (let _150_484 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.ret_wp)
in (let _150_483 = (let _150_482 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_481 = (let _150_480 = (FStar_Syntax_Syntax.as_arg yexp)
in (_150_480)::[])
in (_150_482)::_150_481))
in (FStar_Syntax_Syntax.mk_Tm_app _150_484 _150_483 None res_t.FStar_Syntax_Syntax.pos)))
in (

let x_eq_y_yret = (let _150_492 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _150_491 = (let _150_490 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_489 = (let _150_488 = (let _150_485 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _150_485))
in (let _150_487 = (let _150_486 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_150_486)::[])
in (_150_488)::_150_487))
in (_150_490)::_150_489))
in (FStar_Syntax_Syntax.mk_Tm_app _150_492 _150_491 None res_t.FStar_Syntax_Syntax.pos)))
in (

let forall_y_x_eq_y_yret = (let _150_502 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::(u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _150_501 = (let _150_500 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_499 = (let _150_498 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_497 = (let _150_496 = (let _150_495 = (let _150_494 = (let _150_493 = (FStar_Syntax_Syntax.mk_binder y)
in (_150_493)::[])
in (FStar_Syntax_Util.abs _150_494 x_eq_y_yret (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid)))))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _150_495))
in (_150_496)::[])
in (_150_498)::_150_497))
in (_150_500)::_150_499))
in (FStar_Syntax_Syntax.mk_Tm_app _150_502 _150_501 None res_t.FStar_Syntax_Syntax.pos)))
in (

let lc2 = (mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (

let lc = (let _150_503 = (FStar_TypeChecker_Env.get_range env)
in (bind _150_503 env None (FStar_Syntax_Util.lcomp_of_comp comp) ((Some (x)), ((FStar_Syntax_Util.lcomp_of_comp lc2)))))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))


let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (

let comp = (fun _56_894 -> (match (()) with
| () -> begin
(

let _56_911 = (let _150_515 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _150_514 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _150_515 _150_514)))
in (match (_56_911) with
| ((md, _56_897, _56_899), (u_res_t, res_t, wp_then), (_56_906, _56_908, wp_else)) -> begin
(

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _150_535 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (let _150_534 = (let _150_532 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_531 = (let _150_530 = (FStar_Syntax_Syntax.as_arg g)
in (let _150_529 = (let _150_528 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _150_527 = (let _150_526 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_150_526)::[])
in (_150_528)::_150_527))
in (_150_530)::_150_529))
in (_150_532)::_150_531))
in (let _150_533 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _150_535 _150_534 None _150_533)))))
in (

let wp = (ifthenelse md res_t guard wp_then wp_else)
in if ((FStar_Options.split_cases ()) > (Prims.parse_int "0")) then begin
(

let comp = (mk_comp md u_res_t res_t wp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(

let wp = (let _150_540 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (let _150_539 = (let _150_538 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_537 = (let _150_536 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_536)::[])
in (_150_538)::_150_537))
in (FStar_Syntax_Syntax.mk_Tm_app _150_540 _150_539 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md u_res_t res_t wp []))
end))
end))
end))
in (let _150_541 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _150_541; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp})))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (let _150_547 = (let _150_546 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid _150_546))
in (FStar_Syntax_Syntax.fvar _150_547 FStar_Syntax_Syntax.Delta_constant None)))


let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (FStar_List.fold_left (fun eff _56_930 -> (match (_56_930) with
| (_56_928, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (

let bind_cases = (fun _56_933 -> (match (()) with
| () -> begin
(

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _150_577 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (let _150_576 = (let _150_574 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_573 = (let _150_572 = (FStar_Syntax_Syntax.as_arg g)
in (let _150_571 = (let _150_570 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _150_569 = (let _150_568 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_150_568)::[])
in (_150_570)::_150_569))
in (_150_572)::_150_571))
in (_150_574)::_150_573))
in (let _150_575 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _150_577 _150_576 None _150_575)))))
in (

let default_case = (

let post_k = (let _150_580 = (let _150_578 = (FStar_Syntax_Syntax.null_binder res_t)
in (_150_578)::[])
in (let _150_579 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _150_580 _150_579)))
in (

let kwp = (let _150_583 = (let _150_581 = (FStar_Syntax_Syntax.null_binder post_k)
in (_150_581)::[])
in (let _150_582 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _150_583 _150_582)))
in (

let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (

let wp = (let _150_589 = (let _150_584 = (FStar_Syntax_Syntax.mk_binder post)
in (_150_584)::[])
in (let _150_588 = (let _150_587 = (let _150_585 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Errors.exhaustiveness_check _150_585))
in (let _150_586 = (fvar_const env FStar_Syntax_Const.false_lid)
in (FStar_All.pipe_left _150_587 _150_586)))
in (FStar_Syntax_Util.abs _150_589 _150_588 (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md u_res_t res_t wp []))))))
in (

let comp = (FStar_List.fold_right (fun _56_949 celse -> (match (_56_949) with
| (g, cthen) -> begin
(

let _56_969 = (let _150_592 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _150_592 celse))
in (match (_56_969) with
| ((md, _56_953, _56_955), (_56_958, _56_960, wp_then), (_56_964, _56_966, wp_else)) -> begin
(let _150_593 = (ifthenelse md res_t g wp_then wp_else)
in (mk_comp md u_res_t res_t _150_593 []))
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

let _56_978 = (destruct_comp comp)
in (match (_56_978) with
| (_56_974, _56_976, wp) -> begin
(

let wp = (let _150_598 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (let _150_597 = (let _150_596 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_595 = (let _150_594 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_594)::[])
in (_150_596)::_150_595))
in (FStar_Syntax_Syntax.mk_Tm_app _150_598 _150_597 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md u_res_t res_t wp []))
end))))
end))))
end))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))


let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (

let close = (fun _56_984 -> (match (()) with
| () -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in if (FStar_Syntax_Util.is_ml_comp c) then begin
c
end else begin
(

let close_wp = (fun u_res md res_t bvs wp0 -> (FStar_List.fold_right (fun x wp -> (

let bs = (let _150_619 = (FStar_Syntax_Syntax.mk_binder x)
in (_150_619)::[])
in (

let us = (let _150_621 = (let _150_620 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (_150_620)::[])
in (u_res)::_150_621)
in (

let wp = (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid))))
in (let _150_628 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (let _150_627 = (let _150_626 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _150_625 = (let _150_624 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _150_623 = (let _150_622 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_622)::[])
in (_150_624)::_150_623))
in (_150_626)::_150_625))
in (FStar_Syntax_Syntax.mk_Tm_app _150_628 _150_627 None wp0.FStar_Syntax_Syntax.pos))))))) bvs wp0))
in (

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _56_1001 = (destruct_comp c)
in (match (_56_1001) with
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

let _56_1004 = lc
in {FStar_Syntax_Syntax.eff_name = _56_1004.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _56_1004.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _56_1004.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))


let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (

let refine = (fun _56_1010 -> (match (()) with
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
(let _150_639 = (let _150_638 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _150_637 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _150_638 _150_637)))
in (FStar_All.failwith _150_639))
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

let ret = (let _150_641 = (let _150_640 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _150_640 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_641))
in (

let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (

let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (

let c = (let _150_643 = (let _150_642 = (bind e.FStar_Syntax_Syntax.pos env None (FStar_Syntax_Util.lcomp_of_comp c) ((Some (x)), (eq_ret)))
in (_150_642.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _150_643 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
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

let _56_1022 = lc
in {FStar_Syntax_Syntax.eff_name = _56_1022.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _56_1022.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))


let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (match ((FStar_TypeChecker_Rel.sub_comp env c c')) with
| None -> begin
(let _150_655 = (let _150_654 = (let _150_653 = (FStar_TypeChecker_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _150_652 = (FStar_TypeChecker_Env.get_range env)
in ((_150_653), (_150_652))))
in FStar_Syntax_Syntax.Error (_150_654))
in (Prims.raise _150_655))
end
| Some (g) -> begin
((e), (c'), (g))
end))


let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match ((let _150_664 = (FStar_Syntax_Subst.compress t)
in _150_664.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_56_1036) -> begin
(match ((let _150_665 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _150_665.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid) -> begin
(

let _56_1040 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (

let b2t = (let _150_666 = (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar _150_666 (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None))
in (

let lc = (let _150_669 = (let _150_668 = (let _150_667 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_667))
in ((None), (_150_668)))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) lc _150_669))
in (

let e = (let _150_671 = (let _150_670 = (FStar_Syntax_Syntax.as_arg e)
in (_150_670)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _150_671 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in ((e), (lc))))))
end
| _56_1046 -> begin
((e), (lc))
end)
end
| _56_1048 -> begin
((e), (lc))
end))


let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (

let gopt = if env.FStar_TypeChecker_Env.use_eq then begin
(let _150_680 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in ((_150_680), (false)))
end else begin
(let _150_681 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in ((_150_681), (true)))
end
in (match (gopt) with
| (None, _56_1056) -> begin
(

let _56_1058 = (FStar_TypeChecker_Rel.subtype_fail env e lc.FStar_Syntax_Syntax.res_typ t)
in ((e), ((

let _56_1060 = lc
in {FStar_Syntax_Syntax.eff_name = _56_1060.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _56_1060.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _56_1060.FStar_Syntax_Syntax.comp})), (FStar_TypeChecker_Rel.trivial_guard)))
end
| (Some (g), apply_guard) -> begin
(match ((FStar_TypeChecker_Rel.guard_form g)) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let lc = (

let _56_1067 = lc
in {FStar_Syntax_Syntax.eff_name = _56_1067.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _56_1067.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _56_1067.FStar_Syntax_Syntax.comp})
in ((e), (lc), (g)))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let g = (

let _56_1072 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _56_1072.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_1072.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_1072.FStar_TypeChecker_Env.implicits})
in (

let strengthen = (fun _56_1076 -> (match (()) with
| () -> begin
(

let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (match ((let _150_684 = (FStar_Syntax_Subst.compress f)
in _150_684.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_56_1079, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _56_1085; FStar_Syntax_Syntax.pos = _56_1083; FStar_Syntax_Syntax.vars = _56_1081}, _56_1090) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
(

let lc = (

let _56_1093 = lc
in {FStar_Syntax_Syntax.eff_name = _56_1093.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _56_1093.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _56_1093.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| _56_1097 -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let _56_1099 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_688 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _150_687 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _150_686 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _150_685 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _150_688 _150_687 _150_686 _150_685)))))
end else begin
()
end
in (

let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _56_1104 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_56_1104) with
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

let _56_1114 = (destruct_comp ct)
in (match (_56_1114) with
| (u_t, _56_1111, _56_1113) -> begin
(

let wp = (let _150_693 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.ret_wp)
in (let _150_692 = (let _150_691 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_690 = (let _150_689 = (FStar_Syntax_Syntax.as_arg xexp)
in (_150_689)::[])
in (_150_691)::_150_690))
in (FStar_Syntax_Syntax.mk_Tm_app _150_693 _150_692 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)))
in (

let cret = (let _150_694 = (mk_comp md u_t t wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_694))
in (

let guard = if apply_guard then begin
(let _150_696 = (let _150_695 = (FStar_Syntax_Syntax.as_arg xexp)
in (_150_695)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _150_696 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end else begin
f
end
in (

let _56_1120 = (let _150_704 = (FStar_All.pipe_left (fun _150_701 -> Some (_150_701)) (FStar_TypeChecker_Errors.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _150_703 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _150_702 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _150_704 _150_703 e cret _150_702))))
in (match (_56_1120) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x = (

let _56_1121 = x
in {FStar_Syntax_Syntax.ppname = _56_1121.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_1121.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (

let c = (let _150_706 = (let _150_705 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _150_705))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) _150_706 ((Some (x)), (eq_ret))))
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let _56_1126 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _150_707 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _150_707))
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
| _56_1132 -> begin
[]
end))))
in (

let lc = (

let _56_1134 = lc
in (let _150_709 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _150_709; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (

let g = (

let _56_1137 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _56_1137.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_1137.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_1137.FStar_TypeChecker_Env.implicits})
in ((e), (lc), (g)))))))
end)
end)))


let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _150_721 = (let _150_720 = (let _150_719 = (let _150_718 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _150_718))
in (_150_719)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _150_720 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _150_721))))
in (

let norm = (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env t))
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
| ((req, _56_1165))::((ens, _56_1160))::_56_1157 -> begin
(let _150_727 = (let _150_724 = (norm req)
in Some (_150_724))
in (let _150_726 = (let _150_725 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _150_725))
in ((_150_727), (_150_726))))
end
| _56_1169 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Effect constructor is not fully applied"), (comp.FStar_Syntax_Syntax.pos)))))
end)
end else begin
(

let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| ((wp, _56_1175))::_56_1172 -> begin
(

let _56_1181 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (_56_1181) with
| (us_r, _56_1180) -> begin
(

let _56_1185 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (_56_1185) with
| (us_e, _56_1184) -> begin
(

let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (

let as_req = (let _150_729 = (let _150_728 = (FStar_Ident.set_lid_range FStar_Syntax_Const.as_requires r)
in (FStar_Syntax_Syntax.fvar _150_728 FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_729 us_r))
in (

let as_ens = (let _150_731 = (let _150_730 = (FStar_Ident.set_lid_range FStar_Syntax_Const.as_ensures r)
in (FStar_Syntax_Syntax.fvar _150_730 FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_731 us_e))
in (

let req = (let _150_734 = (let _150_733 = (let _150_732 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_732)::[])
in (((ct.FStar_Syntax_Syntax.result_typ), (Some (FStar_Syntax_Syntax.imp_tag))))::_150_733)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _150_734 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let ens = (let _150_737 = (let _150_736 = (let _150_735 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_735)::[])
in (((ct.FStar_Syntax_Syntax.result_typ), (Some (FStar_Syntax_Syntax.imp_tag))))::_150_736)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _150_737 None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _150_741 = (let _150_738 = (norm req)
in Some (_150_738))
in (let _150_740 = (let _150_739 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm _150_739))
in ((_150_741), (_150_740)))))))))
end))
end))
end
| _56_1192 -> begin
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

let _56_1203 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_56_1203) with
| (bs, c) -> begin
(

let rec aux = (fun subst _56_4 -> (match (_56_4) with
| ((x, Some (FStar_Syntax_Syntax.Implicit (dot))))::rest -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let _56_1219 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t)
in (match (_56_1219) with
| (v, _56_1217, g) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (v))))::subst
in (

let _56_1225 = (aux subst rest)
in (match (_56_1225) with
| (args, bs, subst, g') -> begin
(let _150_752 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((v), (Some (FStar_Syntax_Syntax.Implicit (dot)))))::args), (bs), (subst), (_150_752)))
end)))
end)))
end
| bs -> begin
(([]), (bs), (subst), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (

let _56_1231 = (aux [] bs)
in (match (_56_1231) with
| (args, bs, subst, guard) -> begin
(match (((args), (bs))) with
| ([], _56_1234) -> begin
((e), (torig), (guard))
end
| (_56_1237, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
((e), (torig), (FStar_TypeChecker_Rel.trivial_guard))
end
| _56_1241 -> begin
(

let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _56_1244 -> begin
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
| _56_1249 -> begin
((e), (t), (FStar_TypeChecker_Rel.trivial_guard))
end)
end))


let string_of_univs = (fun univs -> (let _150_757 = (let _150_756 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _150_756 (FStar_List.map (fun u -> (let _150_755 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _150_755 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _150_757 (FStar_String.concat ", "))))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(

let s = (let _150_763 = (let _150_762 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _150_762))
in (FStar_All.pipe_right _150_763 FStar_Util.set_elements))
in (

let _56_1255 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _150_765 = (let _150_764 = (FStar_TypeChecker_Env.univ_vars env)
in (string_of_univs _150_764))
in (FStar_Util.print1 "univ_vars in env: %s\n" _150_765))
end else begin
()
end
in (

let r = (let _150_766 = (FStar_TypeChecker_Env.get_range env)
in Some (_150_766))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (

let _56_1260 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _150_771 = (let _150_768 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _150_768))
in (let _150_770 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _150_769 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _150_771 _150_770 _150_769))))
end else begin
()
end
in (

let _56_1262 = (FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))))
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

let _56_1272 = (FStar_ST.op_Colon_Equals (Prims.snd ts).FStar_Syntax_Syntax.tk (Some (t.FStar_Syntax_Syntax.n)))
in ts)))
end))


let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t0)
in (

let univs = (FStar_Syntax_Free.univs t)
in (

let _56_1278 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _150_778 = (string_of_univs univs)
in (FStar_Util.print1 "univs to gen : %s\n" _150_778))
end else begin
()
end
in (

let gen = (gen_univs env univs)
in (

let _56_1281 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _150_779 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _150_779))
end else begin
()
end
in (

let ts = (FStar_Syntax_Subst.close_univ_vars gen t)
in (let _150_780 = (FStar_ST.read t0.FStar_Syntax_Syntax.tk)
in (maybe_set_tk ((gen), (ts)) _150_780)))))))))


let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> if (let _150_786 = (FStar_Util.for_all (fun _56_1289 -> (match (_56_1289) with
| (_56_1287, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _150_786)) then begin
None
end else begin
(

let norm = (fun c -> (

let _56_1292 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _150_789 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _150_789))
end else begin
()
end
in (

let c = if (FStar_TypeChecker_Env.should_verify env) then begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env c)
end else begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env c)
end
in (

let _56_1295 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _150_790 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _150_790))
end else begin
()
end
in c))))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (let _150_793 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _150_793 FStar_Util.set_elements)))
in (

let _56_1311 = (let _150_795 = (FStar_All.pipe_right ecs (FStar_List.map (fun _56_1302 -> (match (_56_1302) with
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
in (FStar_All.pipe_right _150_795 FStar_List.unzip))
in (match (_56_1311) with
| (univs, uvars) -> begin
(

let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (

let gen_univs = (gen_univs env univs)
in (

let _56_1315 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end else begin
()
end
in (

let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _56_1320 -> (match (_56_1320) with
| (uvs, e, c) -> begin
(

let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _56_1323 -> (match (_56_1323) with
| (u, k) -> begin
(match ((FStar_Unionfind.find u)) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
((a), (Some (FStar_Syntax_Syntax.imp_tag)))
end
| FStar_Syntax_Syntax.Fixed (_56_1357) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _56_1360 -> begin
(

let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (

let _56_1364 = (FStar_Syntax_Util.arrow_formals k)
in (match (_56_1364) with
| (bs, kres) -> begin
(

let a = (let _150_801 = (let _150_800 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _150_799 -> Some (_150_799)) _150_800))
in (FStar_Syntax_Syntax.new_bv _150_801 kres))
in (

let t = (let _150_806 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _150_805 = (let _150_804 = (let _150_803 = (let _150_802 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _150_802))
in FStar_Util.Inl (_150_803))
in Some (_150_804))
in (FStar_Syntax_Util.abs bs _150_806 _150_805)))
in (

let _56_1367 = (FStar_Syntax_Util.set_uvar u t)
in ((a), (Some (FStar_Syntax_Syntax.imp_tag))))))
end)))
end)
end))))
in (

let _56_1399 = (match (((tvars), (gen_univs))) with
| ([], []) -> begin
((e), (c))
end
| ([], _56_1375) -> begin
(

let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::[]) env c)
in (

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::[]) env e)
in ((e), (c))))
end
| _56_1380 -> begin
(

let _56_1383 = ((e), (c))
in (match (_56_1383) with
| (e0, c0) -> begin
(

let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::[]) env c)
in (

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Iota))::[]) env e)
in (

let t = (match ((let _150_807 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _150_807.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(

let _56_1392 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (_56_1392) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| _56_1394 -> begin
(FStar_Syntax_Util.arrow tvars c)
end)
in (

let e' = (FStar_Syntax_Util.abs tvars e (Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp c)))))
in (let _150_808 = (FStar_Syntax_Syntax.mk_Total t)
in ((e'), (_150_808)))))))
end))
end)
in (match (_56_1399) with
| (e, c) -> begin
((gen_univs), (e), (c))
end)))
end))))
in Some (ecs)))))
end)))))
end)


let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> (

let _56_1409 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _150_815 = (let _150_814 = (FStar_List.map (fun _56_1408 -> (match (_56_1408) with
| (lb, _56_1405, _56_1407) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _150_814 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _150_815))
end else begin
()
end
in (match ((let _150_817 = (FStar_All.pipe_right lecs (FStar_List.map (fun _56_1415 -> (match (_56_1415) with
| (_56_1412, e, c) -> begin
((e), (c))
end))))
in (gen env _150_817))) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun _56_1420 -> (match (_56_1420) with
| (l, t, c) -> begin
((l), ([]), (t), (c))
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _56_1428 _56_1432 -> (match (((_56_1428), (_56_1432))) with
| ((l, _56_1425, _56_1427), (us, e, c)) -> begin
(

let _56_1433 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _150_824 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _150_823 = (FStar_Syntax_Print.lbname_to_string l)
in (let _150_822 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (let _150_821 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print4 "(%s) Generalized %s at type %s\n%s\n" _150_824 _150_823 _150_822 _150_821)))))
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
(let _150_840 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _150_839 -> Some (_150_839)) _150_840))
end)
end)
in (

let is_var = (fun e -> (match ((let _150_843 = (FStar_Syntax_Subst.compress e)
in _150_843.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (_56_1450) -> begin
true
end
| _56_1453 -> begin
false
end))
in (

let decorate = (fun e t -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((

let _56_1460 = x
in {FStar_Syntax_Syntax.ppname = _56_1460.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_1460.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| _56_1463 -> begin
(

let _56_1464 = e
in (let _150_848 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _56_1464.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _150_848; FStar_Syntax_Syntax.pos = _56_1464.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _56_1464.FStar_Syntax_Syntax.vars}))
end)))
in (

let env = (

let _56_1466 = env
in (let _150_849 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _56_1466.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _56_1466.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _56_1466.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _56_1466.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _56_1466.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _56_1466.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _56_1466.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _56_1466.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _56_1466.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _56_1466.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _56_1466.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _56_1466.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _56_1466.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _56_1466.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _56_1466.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _150_849; FStar_TypeChecker_Env.is_iface = _56_1466.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _56_1466.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _56_1466.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _56_1466.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _56_1466.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _56_1466.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _56_1466.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _56_1466.FStar_TypeChecker_Env.qname_and_index}))
in (match ((check env t1 t2)) with
| None -> begin
(let _150_853 = (let _150_852 = (let _150_851 = (FStar_TypeChecker_Errors.expected_expression_of_type env t2 e t1)
in (let _150_850 = (FStar_TypeChecker_Env.get_range env)
in ((_150_851), (_150_850))))
in FStar_Syntax_Syntax.Error (_150_852))
in (Prims.raise _150_853))
end
| Some (g) -> begin
(

let _56_1472 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _150_854 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _150_854))
end else begin
()
end
in (let _150_855 = (decorate e t2)
in ((_150_855), (g))))
end)))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (

let discharge = (fun g -> (

let _56_1479 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _150_865 = (discharge g)
in (let _150_864 = (lc.FStar_Syntax_Syntax.comp ())
in ((_150_865), (_150_864))))
end else begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let steps = (FStar_TypeChecker_Normalize.Beta)::[]
in (

let c = (let _150_868 = (let _150_867 = (let _150_866 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (FStar_All.pipe_right _150_866 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right _150_867 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (FStar_All.pipe_right _150_868 (FStar_TypeChecker_Normalize.comp_to_comp_typ env)))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let _56_1489 = (destruct_comp c)
in (match (_56_1489) with
| (u_t, t, wp) -> begin
(

let vc = (let _150_874 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.trivial)
in (let _150_873 = (let _150_871 = (FStar_Syntax_Syntax.as_arg t)
in (let _150_870 = (let _150_869 = (FStar_Syntax_Syntax.as_arg wp)
in (_150_869)::[])
in (_150_871)::_150_870))
in (let _150_872 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk_Tm_app _150_874 _150_873 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _150_872))))
in (

let _56_1491 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _150_875 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _150_875))
end else begin
()
end
in (

let g = (let _150_876 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _150_876))
in (let _150_878 = (discharge g)
in (let _150_877 = (FStar_Syntax_Syntax.mk_Comp c)
in ((_150_878), (_150_877)))))))
end))))))
end)))


let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (

let short_bin_op = (fun f _56_6 -> (match (_56_6) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((fst, _56_1502))::[] -> begin
(f fst)
end
| _56_1506 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (

let op_and_e = (fun e -> (let _150_899 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _150_899 (fun _150_898 -> FStar_TypeChecker_Common.NonTrivial (_150_898)))))
in (

let op_or_e = (fun e -> (let _150_904 = (let _150_902 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _150_902))
in (FStar_All.pipe_right _150_904 (fun _150_903 -> FStar_TypeChecker_Common.NonTrivial (_150_903)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _150_907 -> FStar_TypeChecker_Common.NonTrivial (_150_907))))
in (

let op_or_t = (fun t -> (let _150_911 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _150_911 (fun _150_910 -> FStar_TypeChecker_Common.NonTrivial (_150_910)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _150_914 -> FStar_TypeChecker_Common.NonTrivial (_150_914))))
in (

let short_op_ite = (fun _56_7 -> (match (_56_7) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((guard, _56_1521))::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| (_then)::((guard, _56_1526))::[] -> begin
(let _150_918 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _150_918 (fun _150_917 -> FStar_TypeChecker_Common.NonTrivial (_150_917))))
end
| _56_1531 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (

let table = (((FStar_Syntax_Const.op_And), ((short_bin_op op_and_e))))::(((FStar_Syntax_Const.op_Or), ((short_bin_op op_or_e))))::(((FStar_Syntax_Const.and_lid), ((short_bin_op op_and_t))))::(((FStar_Syntax_Const.or_lid), ((short_bin_op op_or_t))))::(((FStar_Syntax_Const.imp_lid), ((short_bin_op op_imp_t))))::(((FStar_Syntax_Const.ite_lid), (short_op_ite)))::[]
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((FStar_Util.find_map table (fun _56_1539 -> (match (_56_1539) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _150_951 = (mk seen_args)
in Some (_150_951))
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
| _56_1544 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (match ((let _150_954 = (FStar_Syntax_Util.un_uinst l)
in _150_954.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| _56_1549 -> begin
false
end))


let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (

let pos = (fun bs -> (match (bs) with
| ((hd, _56_1558))::_56_1555 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| _56_1562 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| ((_56_1566, Some (FStar_Syntax_Syntax.Implicit (_56_1568))))::_56_1564 -> begin
bs
end
| _56_1574 -> begin
(match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
bs
end
| Some (t) -> begin
(match ((let _150_961 = (FStar_Syntax_Subst.compress t)
in _150_961.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', _56_1580) -> begin
(match ((FStar_Util.prefix_until (fun _56_8 -> (match (_56_8) with
| (_56_1585, Some (FStar_Syntax_Syntax.Implicit (_56_1587))) -> begin
false
end
| _56_1592 -> begin
true
end)) bs')) with
| None -> begin
bs
end
| Some ([], _56_1596, _56_1598) -> begin
bs
end
| Some (imps, _56_1603, _56_1605) -> begin
if (FStar_All.pipe_right imps (FStar_Util.for_all (fun _56_1611 -> (match (_56_1611) with
| (x, _56_1610) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end)))) then begin
(

let r = (pos bs)
in (

let imps = (FStar_All.pipe_right imps (FStar_List.map (fun _56_1615 -> (match (_56_1615) with
| (x, i) -> begin
(let _150_965 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in ((_150_965), (i)))
end))))
in (FStar_List.append imps bs)))
end else begin
bs
end
end)
end
| _56_1618 -> begin
bs
end)
end)
end)))


let maybe_lift : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env e c1 c2 -> (

let m1 = (FStar_TypeChecker_Env.norm_eff_name env c1)
in (

let m2 = (FStar_TypeChecker_Env.norm_eff_name env c2)
in if (((FStar_Ident.lid_equals m1 m2) || ((FStar_Syntax_Util.is_pure_effect c1) && (FStar_Syntax_Util.is_ghost_effect c2))) || ((FStar_Syntax_Util.is_pure_effect c2) && (FStar_Syntax_Util.is_ghost_effect c1))) then begin
e
end else begin
(let _150_974 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m2))))))) _150_974 e.FStar_Syntax_Syntax.pos))
end)))


let maybe_monadic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c t -> (

let m = (FStar_TypeChecker_Env.norm_eff_name env c)
in if (((is_pure_or_ghost_effect env m) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid)) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid)) then begin
e
end else begin
(let _150_983 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))) _150_983 e.FStar_Syntax_Syntax.pos))
end))


let effect_repr_aux = (fun only_reifiable env c u_c -> (match ((let _150_988 = (FStar_TypeChecker_Env.norm_eff_name env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_TypeChecker_Env.effect_decl_opt env _150_988))) with
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
| _56_1639 -> begin
(

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _56_1643 = (let _150_989 = (FStar_List.hd c.FStar_Syntax_Syntax.effect_args)
in ((c.FStar_Syntax_Syntax.result_typ), (_150_989)))
in (match (_56_1643) with
| (res_typ, wp) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_c)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (let _150_995 = (let _150_994 = (let _150_992 = (let _150_991 = (let _150_990 = (FStar_Syntax_Syntax.as_arg res_typ)
in (_150_990)::(wp)::[])
in ((repr), (_150_991)))
in FStar_Syntax_Syntax.Tm_app (_150_992))
in (let _150_993 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _150_994 None _150_993)))
in Some (_150_995)))
end)))
end)
end
end))


let effect_repr : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term Prims.option = (fun env c u_c -> (effect_repr_aux false env c u_c))


let reify_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term = (fun env c u_c -> (

let no_reify = (fun l -> (let _150_1013 = (let _150_1012 = (let _150_1011 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _150_1010 = (FStar_TypeChecker_Env.get_range env)
in ((_150_1011), (_150_1010))))
in FStar_Syntax_Syntax.Error (_150_1012))
in (Prims.raise _150_1013)))
in (match ((let _150_1014 = (c.FStar_Syntax_Syntax.comp ())
in (effect_repr_aux true env _150_1014 u_c))) with
| None -> begin
(no_reify c.FStar_Syntax_Syntax.eff_name)
end
| Some (tm) -> begin
tm
end)))


let d : Prims.string  ->  Prims.unit = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))


let mk_toplevel_definition : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term) = (fun env lident def -> (

let _56_1662 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _56_1660 = (d (FStar_Ident.text_of_lid lident))
in (let _150_1023 = (FStar_Syntax_Print.term_to_string def)
in (FStar_Util.print2 "Registering top-level definition: %s\n%s\n" (FStar_Ident.text_of_lid lident) _150_1023)))
end else begin
()
end
in (

let fv = (let _150_1024 = (FStar_Syntax_Util.incr_delta_qualifier def)
in (FStar_Syntax_Syntax.lid_as_fv lident _150_1024 None))
in (

let lbname = FStar_Util.Inr (fv)
in (

let lb = ((false), (({FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = def})::[]))
in (

let sig_ctx = FStar_Syntax_Syntax.Sig_let (((lb), (FStar_Range.dummyRange), ((lident)::[]), ((FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)::[])))
in (let _150_1025 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) None FStar_Range.dummyRange)
in ((sig_ctx), (_150_1025)))))))))


let check_sigelt_quals : FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun se -> (

let visibility = (fun _56_9 -> (match (_56_9) with
| FStar_Syntax_Syntax.Private -> begin
true
end
| _56_1672 -> begin
false
end))
in (

let reducibility = (fun _56_10 -> (match (_56_10) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) | (FStar_Syntax_Syntax.Visible_default) -> begin
true
end
| _56_1680 -> begin
false
end))
in (

let assumption = (fun _56_11 -> (match (_56_11) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.New) -> begin
true
end
| _56_1686 -> begin
false
end))
in (

let reification = (fun _56_12 -> (match (_56_12) with
| (FStar_Syntax_Syntax.Reifiable) | (FStar_Syntax_Syntax.Reflectable) -> begin
true
end
| _56_1692 -> begin
false
end))
in (

let inferred = (fun _56_13 -> (match (_56_13) with
| (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) | (FStar_Syntax_Syntax.ExceptionConstructor) | (FStar_Syntax_Syntax.HasMaskedEffect) | (FStar_Syntax_Syntax.Effect) -> begin
true
end
| _56_1711 -> begin
false
end))
in (

let has_eq = (fun _56_14 -> (match (_56_14) with
| (FStar_Syntax_Syntax.Noeq) | (FStar_Syntax_Syntax.Unopteq) -> begin
true
end
| _56_1717 -> begin
false
end))
in (

let quals_combo_ok = (fun quals q -> (match (q) with
| FStar_Syntax_Syntax.Assumption -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((x = q) || (x = FStar_Syntax_Syntax.Logic)) || (inferred x)) || (visibility x)) || (assumption x)))))
end
| FStar_Syntax_Syntax.New -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((x = q) || (inferred x)) || (visibility x)) || (assumption x)))))
end
| (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) | (FStar_Syntax_Syntax.Visible_default) | (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Noeq) | (FStar_Syntax_Syntax.Unopteq) -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) || (x = FStar_Syntax_Syntax.Abstract)) || (has_eq x)) || (inferred x)) || (visibility x)))))
end
| FStar_Syntax_Syntax.TotalEffect -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((x = q) || (inferred x)) || (visibility x)) || (reification x)))))
end
| FStar_Syntax_Syntax.Logic -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((x = q) || (x = FStar_Syntax_Syntax.Assumption)) || (inferred x)) || (visibility x)) || (reducibility x)))))
end
| (FStar_Syntax_Syntax.Reifiable) | (FStar_Syntax_Syntax.Reflectable) -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((reification x) || (inferred x)) || (visibility x)) || (x = FStar_Syntax_Syntax.TotalEffect)))))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| _56_1742 -> begin
true
end))
in (

let quals = (FStar_Syntax_Util.quals_of_sigelt se)
in (

let r = (FStar_Syntax_Util.range_of_sigelt se)
in (

let no_dup_quals = (FStar_Util.remove_dups (fun x y -> (x = y)) quals)
in (

let err' = (fun msg -> (let _150_1057 = (let _150_1056 = (let _150_1055 = (let _150_1054 = (FStar_Syntax_Print.quals_to_string quals)
in (FStar_Util.format2 "The qualifier list \"[%s]\" is not permissible for this element%s" _150_1054 msg))
in ((_150_1055), (r)))
in FStar_Syntax_Syntax.Error (_150_1056))
in (Prims.raise _150_1057)))
in (

let err = (fun msg -> (err' (Prims.strcat ": " msg)))
in (

let err' = (fun _56_1753 -> (match (()) with
| () -> begin
(err' "")
end))
in (

let _56_1754 = if ((FStar_List.length quals) <> (FStar_List.length no_dup_quals)) then begin
(err "duplicate qualifiers")
end else begin
()
end
in (

let _56_1756 = if (not ((FStar_All.pipe_right quals (FStar_List.for_all (quals_combo_ok quals))))) then begin
(err "ill-formed combination")
end else begin
()
end
in (match (se) with
| FStar_Syntax_Syntax.Sig_let ((is_rec, _56_1760), _56_1763, _56_1765, _56_1767) -> begin
(

let _56_1770 = if (is_rec && (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))) then begin
(err "recursive definitions cannot be marked inline")
end else begin
()
end
in if (FStar_All.pipe_right quals (FStar_Util.for_some (fun x -> ((assumption x) || (has_eq x))))) then begin
(err "definitions cannot be assumed or marked with equality qualifiers")
end else begin
()
end)
end
| FStar_Syntax_Syntax.Sig_bundle (_56_1774) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.Abstract) || (inferred x)) || (visibility x)) || (has_eq x))))))) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (_56_1778) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some has_eq)) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_assume (_56_1781) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((visibility x) || (x = FStar_Syntax_Syntax.Assumption))))))) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_new_effect (_56_1785) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x))))))) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_56_1789) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x))))))) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_56_1793) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((inferred x) || (visibility x))))))) then begin
(err' ())
end else begin
()
end
end
| _56_1797 -> begin
()
end)))))))))))))))))




