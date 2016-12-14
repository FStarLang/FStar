
open Prims

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv Prims.option * FStar_Syntax_Syntax.lcomp)


let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _154_6 = (FStar_TypeChecker_Env.get_range env)
in (let _154_5 = (FStar_TypeChecker_Errors.failed_to_prove_specification errs)
in (FStar_TypeChecker_Errors.report _154_6 _154_5))))


let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _154_9 = (FStar_Syntax_Subst.compress t)
in _154_9.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_19) -> begin
true
end
| _57_22 -> begin
false
end))


let t_binders : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env -> (let _154_13 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right _154_13 (FStar_List.filter (fun _57_27 -> (match (_57_27) with
| (x, _57_26) -> begin
(is_type x.FStar_Syntax_Syntax.sort)
end))))))


let new_uvar_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun env k -> (

let bs = if ((FStar_Options.full_context_dependency ()) || (let _154_18 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _154_18))) then begin
(FStar_TypeChecker_Env.all_binders env)
end else begin
(t_binders env)
end
in (let _154_19 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Rel.new_uvar _154_19 bs k))))


let new_uvar : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env k -> (let _154_24 = (new_uvar_aux env k)
in (Prims.fst _154_24)))


let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun _57_1 -> (match (_57_1) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, _57_42); FStar_Syntax_Syntax.tk = _57_39; FStar_Syntax_Syntax.pos = _57_37; FStar_Syntax_Syntax.vars = _57_35} -> begin
uv
end
| _57_47 -> begin
(FStar_All.failwith "Impossible")
end))


let new_implicit_var : Prims.string  ->  FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.uvar * FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t) = (fun reason r env k -> (match ((FStar_Syntax_Util.destruct k FStar_Syntax_Const.range_of_lid)) with
| Some ((_57_57)::((tm, _57_54))::[]) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))) None tm.FStar_Syntax_Syntax.pos)
in ((t), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
end
| _57_62 -> begin
(

let _57_65 = (new_uvar_aux env k)
in (match (_57_65) with
| (t, u) -> begin
(

let g = (

let _57_66 = FStar_TypeChecker_Rel.trivial_guard
in (let _154_37 = (let _154_36 = (let _154_35 = (as_uvar u)
in ((reason), (env), (_154_35), (t), (k), (r)))
in (_154_36)::[])
in {FStar_TypeChecker_Env.guard_f = _57_66.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_66.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_66.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _154_37}))
in (let _154_40 = (let _154_39 = (let _154_38 = (as_uvar u)
in ((_154_38), (r)))
in (_154_39)::[])
in ((t), (_154_40), (g))))
end))
end))


let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun r t -> (

let uvs = (FStar_Syntax_Free.uvars t)
in if (not ((FStar_Util.set_is_empty uvs))) then begin
(

let us = (let _154_47 = (let _154_46 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun _57_75 -> (match (_57_75) with
| (x, _57_74) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) _154_46))
in (FStar_All.pipe_right _154_47 (FStar_String.concat ", ")))
in (

let _57_77 = (FStar_Options.push ())
in (

let _57_79 = (FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool (false)))
in (

let _57_81 = (FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)))
in (

let _57_83 = (let _154_49 = (let _154_48 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us _154_48))
in (FStar_TypeChecker_Errors.report r _154_49))
in (FStar_Options.pop ()))))))
end else begin
()
end))


let force_sort' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' = (fun s -> (match ((FStar_ST.read s.FStar_Syntax_Syntax.tk)) with
| None -> begin
(let _154_54 = (let _154_53 = (FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos)
in (let _154_52 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s" _154_53 _154_52)))
in (FStar_All.failwith _154_54))
end
| Some (tk) -> begin
tk
end))


let force_sort = (fun s -> (let _154_56 = (force_sort' s)
in (FStar_Syntax_Syntax.mk _154_56 None s.FStar_Syntax_Syntax.pos)))


let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env _57_98 -> (match (_57_98) with
| {FStar_Syntax_Syntax.lbname = _57_97; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _57_93; FStar_Syntax_Syntax.lbdef = e} -> begin
(

let rng = t.FStar_Syntax_Syntax.pos
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _57_102 = if (univ_vars <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let mk_binder = (fun scope a -> (match ((let _154_65 = (FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort)
in _154_65.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _57_112 = (FStar_Syntax_Util.type_u ())
in (match (_57_112) with
| (k, _57_111) -> begin
(

let t = (let _154_66 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right _154_66 Prims.fst))
in (((

let _57_114 = a
in {FStar_Syntax_Syntax.ppname = _57_114.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_114.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (false)))
end))
end
| _57_117 -> begin
((a), (true))
end))
in (

let rec aux = (fun vars e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, _57_124) -> begin
(aux vars e)
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _57_130) -> begin
((t), (true))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _57_136) -> begin
(

let _57_155 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _57_142 _57_145 -> (match (((_57_142), (_57_145))) with
| ((scope, bs, check), (a, imp)) -> begin
(

let _57_148 = (mk_binder scope a)
in (match (_57_148) with
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
in (match (_57_155) with
| (scope, bs, check) -> begin
(

let _57_158 = (aux scope body)
in (match (_57_158) with
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

let _57_165 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _154_74 = (FStar_Range.string_of_range r)
in (let _154_73 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _154_74 _154_73)))
end else begin
()
end
in ((FStar_Util.Inl (t)), ((check_res || check))))))
end))
end))
end
| _57_168 -> begin
(let _154_77 = (let _154_76 = (let _154_75 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _154_75 Prims.fst))
in FStar_Util.Inl (_154_76))
in ((_154_77), (false)))
end)))
in (

let _57_171 = (let _154_78 = (t_binders env)
in (aux _154_78 e))
in (match (_57_171) with
| (t, b) -> begin
(

let t = (match (t) with
| FStar_Util.Inr (c) -> begin
(let _154_82 = (let _154_81 = (let _154_80 = (let _154_79 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" _154_79))
in ((_154_80), (rng)))
in FStar_Syntax_Syntax.Error (_154_81))
in (Prims.raise _154_82))
end
| FStar_Util.Inl (t) -> begin
t
end)
in (([]), (t), (b)))
end))))))
end
| _57_178 -> begin
(

let _57_181 = (FStar_Syntax_Subst.open_univ_vars univ_vars t)
in (match (_57_181) with
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
| FStar_Syntax_Syntax.Pat_dot_term (x, _57_194) -> begin
(

let _57_200 = (FStar_Syntax_Util.type_u ())
in (match (_57_200) with
| (k, _57_199) -> begin
(

let t = (new_uvar env k)
in (

let x = (

let _57_202 = x
in {FStar_Syntax_Syntax.ppname = _57_202.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_202.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let _57_207 = (let _154_95 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _154_95 t))
in (match (_57_207) with
| (e, u) -> begin
(

let p = (

let _57_208 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (e))); FStar_Syntax_Syntax.ty = _57_208.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _57_208.FStar_Syntax_Syntax.p})
in (([]), ([]), ([]), (env), (e), (p)))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let _57_216 = (FStar_Syntax_Util.type_u ())
in (match (_57_216) with
| (t, _57_215) -> begin
(

let x = (

let _57_217 = x
in (let _154_96 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _57_217.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_217.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _154_96}))
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

let _57_227 = (FStar_Syntax_Util.type_u ())
in (match (_57_227) with
| (t, _57_226) -> begin
(

let x = (

let _57_228 = x
in (let _154_97 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _57_228.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_228.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _154_97}))
in (

let env = (FStar_TypeChecker_Env.push_bv env x)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in (((x)::[]), ((x)::[]), ([]), (env), (e), (p)))))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _57_261 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _57_243 _57_246 -> (match (((_57_243), (_57_246))) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(

let _57_253 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_57_253) with
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
in (match (_57_261) with
| (b, a, w, env, args, pats) -> begin
(

let e = (let _154_104 = (let _154_103 = (let _154_102 = (let _154_101 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (let _154_100 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app _154_101 _154_100 None p.FStar_Syntax_Syntax.p)))
in ((_154_102), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))
in FStar_Syntax_Syntax.Tm_meta (_154_103))
in (FStar_Syntax_Syntax.mk _154_104 None p.FStar_Syntax_Syntax.p))
in (let _154_107 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _154_106 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _154_105 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in ((_154_107), (_154_106), (_154_105), (env), (e), ((

let _57_263 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _57_263.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _57_263.FStar_Syntax_Syntax.p})))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (_57_266) -> begin
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

let pats = (FStar_List.map (fun _57_281 -> (match (_57_281) with
| (p, imp) -> begin
(let _154_119 = (elaborate_pat env p)
in ((_154_119), (imp)))
end)) pats)
in (

let _57_286 = (FStar_TypeChecker_Env.lookup_datacon env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_286) with
| (_57_284, t) -> begin
(

let _57_290 = (FStar_Syntax_Util.arrow_formals t)
in (match (_57_290) with
| (f, _57_289) -> begin
(

let rec aux = (fun formals pats -> (match (((formals), (pats))) with
| ([], []) -> begin
[]
end
| ([], (_57_301)::_57_299) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Too many pattern arguments"), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))))
end
| ((_57_307)::_57_305, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun _57_313 -> (match (_57_313) with
| (t, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(

let a = (let _154_126 = (let _154_125 = (FStar_Syntax_Syntax.range_of_bv t)
in Some (_154_125))
in (FStar_Syntax_Syntax.new_bv _154_126 FStar_Syntax_Syntax.tun))
in (

let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (let _154_127 = (maybe_dot inaccessible a r)
in ((_154_127), (true)))))
end
| _57_320 -> begin
(let _154_131 = (let _154_130 = (let _154_129 = (let _154_128 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _154_128))
in ((_154_129), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))
in FStar_Syntax_Syntax.Error (_154_130))
in (Prims.raise _154_131))
end)
end))))
end
| ((f)::formals', ((p, p_imp))::pats') -> begin
(match (f) with
| (_57_331, Some (FStar_Syntax_Syntax.Implicit (_57_333))) when p_imp -> begin
(let _154_132 = (aux formals' pats')
in (((p), (true)))::_154_132)
end
| (_57_338, Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(

let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let p = (maybe_dot inaccessible a (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
in (let _154_133 = (aux formals' pats)
in (((p), (true)))::_154_133)))
end
| (_57_346, imp) -> begin
(let _154_136 = (let _154_134 = (FStar_Syntax_Syntax.is_implicit imp)
in ((p), (_154_134)))
in (let _154_135 = (aux formals' pats')
in (_154_136)::_154_135))
end)
end))
in (

let _57_349 = p
in (let _154_139 = (let _154_138 = (let _154_137 = (aux f pats)
in ((fv), (_154_137)))
in FStar_Syntax_Syntax.Pat_cons (_154_138))
in {FStar_Syntax_Syntax.v = _154_139; FStar_Syntax_Syntax.ty = _57_349.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _57_349.FStar_Syntax_Syntax.p})))
end))
end)))
end
| _57_352 -> begin
p
end)))
in (

let one_pat = (fun allow_wc_dependence env p -> (

let p = (elaborate_pat env p)
in (

let _57_364 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_57_364) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))) with
| Some (x) -> begin
(let _154_148 = (let _154_147 = (let _154_146 = (FStar_TypeChecker_Errors.nonlinear_pattern_variable x)
in ((_154_146), (p.FStar_Syntax_Syntax.p)))
in FStar_Syntax_Syntax.Error (_154_147))
in (Prims.raise _154_148))
end
| _57_368 -> begin
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

let _57_384 = (one_pat false env q)
in (match (_57_384) with
| (b, a, _57_381, te, q) -> begin
(

let _57_399 = (FStar_List.fold_right (fun p _57_389 -> (match (_57_389) with
| (w, args, pats) -> begin
(

let _57_395 = (one_pat false env p)
in (match (_57_395) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv FStar_Syntax_Syntax.bv_eq a a'))) then begin
(let _154_158 = (let _154_157 = (let _154_156 = (FStar_TypeChecker_Errors.disjunctive_pattern_vars a a')
in (let _154_155 = (FStar_TypeChecker_Env.get_range env)
in ((_154_156), (_154_155))))
in FStar_Syntax_Syntax.Error (_154_157))
in (Prims.raise _154_158))
end else begin
(let _154_160 = (let _154_159 = (FStar_Syntax_Syntax.as_arg arg)
in (_154_159)::args)
in (((FStar_List.append w' w)), (_154_160), ((p)::pats)))
end
end))
end)) pats (([]), ([]), ([])))
in (match (_57_399) with
| (w, args, pats) -> begin
(let _154_162 = (let _154_161 = (FStar_Syntax_Syntax.as_arg te)
in (_154_161)::args)
in (((FStar_List.append b w)), (_154_162), ((

let _57_400 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((q)::pats); FStar_Syntax_Syntax.ty = _57_400.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _57_400.FStar_Syntax_Syntax.p}))))
end))
end))
end
| _57_403 -> begin
(

let _57_411 = (one_pat true env p)
in (match (_57_411) with
| (b, _57_406, _57_408, arg, p) -> begin
(let _154_164 = (let _154_163 = (FStar_Syntax_Syntax.as_arg arg)
in (_154_163)::[])
in ((b), (_154_164), (p)))
end))
end))
in (

let _57_415 = (top_level_pat_as_args env p)
in (match (_57_415) with
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
| (_57_429, FStar_Syntax_Syntax.Tm_uinst (e, _57_432)) -> begin
(aux p e)
end
| (FStar_Syntax_Syntax.Pat_constant (_57_437), FStar_Syntax_Syntax.Tm_constant (_57_440)) -> begin
(let _154_179 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v _154_179))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(

let _57_448 = if (not ((FStar_Syntax_Syntax.bv_eq x y))) then begin
(let _154_182 = (let _154_181 = (FStar_Syntax_Print.bv_to_string x)
in (let _154_180 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _154_181 _154_180)))
in (FStar_All.failwith _154_182))
end else begin
()
end
in (

let _57_450 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _154_184 = (FStar_Syntax_Print.bv_to_string x)
in (let _154_183 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _154_184 _154_183)))
end else begin
()
end
in (

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x = (

let _57_453 = x
in {FStar_Syntax_Syntax.ppname = _57_453.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_453.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x)) s.FStar_Syntax_Syntax.n)))))
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(

let _57_461 = if (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation) then begin
(let _154_187 = (let _154_186 = (FStar_Syntax_Print.bv_to_string x)
in (let _154_185 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _154_186 _154_185)))
in (FStar_All.failwith _154_187))
end else begin
()
end
in (

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x = (

let _57_464 = x
in {FStar_Syntax_Syntax.ppname = _57_464.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_464.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x)) s.FStar_Syntax_Syntax.n))))
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _57_469), _57_473) -> begin
(

let s = (force_sort e)
in (

let x = (

let _57_476 = x
in {FStar_Syntax_Syntax.ppname = _57_476.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_476.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term (((x), (e)))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
(

let _57_486 = if (not ((FStar_Syntax_Syntax.fv_eq fv fv'))) then begin
(let _154_188 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _154_188))
end else begin
()
end
in (let _154_189 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv'), ([])))) _154_189)))
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
(

let _57_529 = if (let _154_190 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right _154_190 Prims.op_Negation)) then begin
(let _154_191 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _154_191))
end else begin
()
end
in (

let fv = fv'
in (

let rec match_args = (fun matched_pats args argpats -> (match (((args), (argpats))) with
| ([], []) -> begin
(let _154_198 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev matched_pats))))) _154_198))
end
| ((arg)::args, ((argpat, _57_545))::argpats) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e, Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (_57_555)) -> begin
(

let x = (let _154_199 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _154_199))
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e)))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args argpats)))
end
| ((e, imp), _57_564) -> begin
(

let pat = (let _154_201 = (aux argpat e)
in (let _154_200 = (FStar_Syntax_Syntax.is_implicit imp)
in ((_154_201), (_154_200))))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _57_568 -> begin
(let _154_204 = (let _154_203 = (FStar_Syntax_Print.pat_to_string p)
in (let _154_202 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _154_203 _154_202)))
in (FStar_All.failwith _154_204))
end))
in (match_args [] args argpats))))
end
| _57_570 -> begin
(let _154_209 = (let _154_208 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (let _154_207 = (FStar_Syntax_Print.pat_to_string qq)
in (let _154_206 = (let _154_205 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right _154_205 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _154_208 _154_207 _154_206))))
in (FStar_All.failwith _154_209))
end))))
in (match (((p.FStar_Syntax_Syntax.v), (exps))) with
| (FStar_Syntax_Syntax.Pat_disj (ps), _57_574) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(

let ps = (FStar_List.map2 aux ps exps)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj (ps)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p))
end
| (_57_578, (e)::[]) -> begin
(aux p e)
end
| _57_583 -> begin
(FStar_All.failwith "Unexpected number of patterns")
end))))


let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (

let topt = Some (pat.FStar_Syntax_Syntax.ty)
in (

let mk = (fun f -> (FStar_Syntax_Syntax.mk f topt pat.FStar_Syntax_Syntax.p))
in (

let pat_as_arg = (fun _57_591 -> (match (_57_591) with
| (p, i) -> begin
(

let _57_594 = (decorated_pattern_as_term p)
in (match (_57_594) with
| (vars, te) -> begin
(let _154_217 = (let _154_216 = (FStar_Syntax_Syntax.as_implicit i)
in ((te), (_154_216)))
in ((vars), (_154_217)))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_57_596) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _154_218 = (mk (FStar_Syntax_Syntax.Tm_constant (c)))
in (([]), (_154_218)))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(let _154_219 = (mk (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (_154_219)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _57_609 = (let _154_220 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _154_220 FStar_List.unzip))
in (match (_57_609) with
| (vars, args) -> begin
(

let vars = (FStar_List.flatten vars)
in (let _154_224 = (let _154_223 = (let _154_222 = (let _154_221 = (FStar_Syntax_Syntax.fv_to_tm fv)
in ((_154_221), (args)))
in FStar_Syntax_Syntax.Tm_app (_154_222))
in (mk _154_223))
in ((vars), (_154_224))))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
(([]), (e))
end)))))


let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun c -> (

let wp = (match (c.FStar_Syntax_Syntax.effect_args) with
| ((wp, _57_618))::[] -> begin
wp
end
| _57_622 -> begin
(let _154_230 = (let _154_229 = (let _154_228 = (FStar_List.map (fun _57_626 -> (match (_57_626) with
| (x, _57_625) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right _154_228 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str _154_229))
in (FStar_All.failwith _154_230))
end)
in (let _154_231 = (FStar_List.hd c.FStar_Syntax_Syntax.comp_univs)
in ((_154_231), (c.FStar_Syntax_Syntax.result_typ), (wp)))))


let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (

let _57_635 = (destruct_comp c)
in (match (_57_635) with
| (u, _57_633, wp) -> begin
(let _154_250 = (let _154_249 = (let _154_248 = (lift c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _154_248))
in (_154_249)::[])
in {FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _154_250; FStar_Syntax_Syntax.flags = []})
end)))


let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let _57_644 = (let _154_258 = (FStar_TypeChecker_Env.norm_eff_name env l1)
in (let _154_257 = (FStar_TypeChecker_Env.norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _154_258 _154_257)))
in (match (_57_644) with
| (m, _57_641, _57_643) -> begin
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

let _57_656 = (FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (_57_656) with
| (m, lift1, lift2) -> begin
(

let m1 = (lift_comp c1 m lift1)
in (

let m2 = (lift_comp c2 m lift2)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (

let _57_662 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (_57_662) with
| (a, kwp) -> begin
(let _154_272 = (destruct_comp m1)
in (let _154_271 = (destruct_comp m2)
in ((((md), (a), (kwp))), (_154_272), (_154_271))))
end)))))
end)))))


let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid))))


let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md u_result result wp flags -> (let _154_293 = (let _154_292 = (let _154_291 = (FStar_Syntax_Syntax.as_arg wp)
in (_154_291)::[])
in {FStar_Syntax_Syntax.comp_univs = (u_result)::[]; FStar_Syntax_Syntax.effect_name = md.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = _154_292; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp _154_293)))


let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (

let _57_676 = lc
in (let _154_300 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _57_676.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _154_300; FStar_Syntax_Syntax.cflags = _57_676.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _57_678 -> (match (()) with
| () -> begin
(let _154_299 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _154_299))
end))})))


let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _154_303 = (FStar_Syntax_Subst.compress t)
in _154_303.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_681) -> begin
true
end
| _57_684 -> begin
false
end))


let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v -> (

let c = if (let _154_310 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation _154_310)) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(

let m = (let _154_311 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must _154_311))
in (

let _57_691 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_57_691) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let u_t = (env.FStar_TypeChecker_Env.universe_of env t)
in (

let wp = (let _154_317 = (let _154_316 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env m m.FStar_Syntax_Syntax.ret_wp)
in (let _154_315 = (let _154_314 = (FStar_Syntax_Syntax.as_arg t)
in (let _154_313 = (let _154_312 = (FStar_Syntax_Syntax.as_arg v)
in (_154_312)::[])
in (_154_314)::_154_313))
in (FStar_Syntax_Syntax.mk_Tm_app _154_316 _154_315 (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _154_317))
in (mk_comp m u_t t wp ((FStar_Syntax_Syntax.RETURN)::[])))))
end)))
end
in (

let _57_696 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return"))) then begin
(let _154_320 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _154_319 = (FStar_Syntax_Print.term_to_string v)
in (let _154_318 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _154_320 _154_319 _154_318))))
end else begin
()
end
in c)))


let bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r1 env e1opt lc1 _57_704 -> (match (_57_704) with
| (b, lc2) -> begin
(

let lc1 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1)
in (

let lc2 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2)
in (

let _57_714 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(

let bstr = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _154_333 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (let _154_332 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _154_331 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" _154_333 _154_332 bstr _154_331)))))
end else begin
()
end
in (

let bind_it = (fun _57_717 -> (match (()) with
| () -> begin
(

let c1 = (lc1.FStar_Syntax_Syntax.comp ())
in (

let c2 = (lc2.FStar_Syntax_Syntax.comp ())
in (

let _57_723 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _154_340 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _154_339 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _154_338 = (FStar_Syntax_Print.comp_to_string c1)
in (let _154_337 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (let _154_336 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" _154_340 _154_339 _154_338 _154_337 _154_336))))))
end else begin
()
end
in (

let try_simplify = (fun _57_726 -> (match (()) with
| () -> begin
(

let aux = (fun _57_728 -> (match (()) with
| () -> begin
if (FStar_Syntax_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some (((c2), ("trivial no binder")))
end
| Some (_57_731) -> begin
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
(let _154_348 = (let _154_347 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in ((_154_347), (reason)))
in Some (_154_348))
end
| _57_741 -> begin
(aux ())
end))
in if ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2)) then begin
(subst_c2 "both total")
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2)) then begin
(let _154_350 = (let _154_349 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((_154_349), ("both gtot")))
in Some (_154_350))
end else begin
(match (((e1opt), (b))) with
| (Some (e), Some (x)) -> begin
if ((FStar_Syntax_Util.is_total_comp c1) && (not ((FStar_Syntax_Syntax.is_null_bv x)))) then begin
(subst_c2 "substituted e")
end else begin
(aux ())
end
end
| _57_748 -> begin
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

let _57_766 = (lift_and_destruct env c1 c2)
in (match (_57_766) with
| ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) -> begin
(

let bs = (match (b) with
| None -> begin
(let _154_351 = (FStar_Syntax_Syntax.null_binder t1)
in (_154_351)::[])
end
| Some (x) -> begin
(let _154_352 = (FStar_Syntax_Syntax.mk_binder x)
in (_154_352)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (

let r1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1))) None r1)
in (

let wp_args = (let _154_364 = (FStar_Syntax_Syntax.as_arg r1)
in (let _154_363 = (let _154_362 = (FStar_Syntax_Syntax.as_arg t1)
in (let _154_361 = (let _154_360 = (FStar_Syntax_Syntax.as_arg t2)
in (let _154_359 = (let _154_358 = (FStar_Syntax_Syntax.as_arg wp1)
in (let _154_357 = (let _154_356 = (let _154_355 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg _154_355))
in (_154_356)::[])
in (_154_358)::_154_357))
in (_154_360)::_154_359))
in (_154_362)::_154_361))
in (_154_364)::_154_363))
in (

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t2))))::[]) kwp)
in (

let wp = (let _154_365 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t1)::(u_t2)::[]) env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _154_365 wp_args None t2.FStar_Syntax_Syntax.pos))
in (

let c = (mk_comp md u_t2 t2 wp [])
in c)))))))
end))
end)))))
end))
in (let _154_366 = (join_lcomp env lc1 lc2)
in {FStar_Syntax_Syntax.eff_name = _154_366; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it})))))
end))


let lift_formula : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t mk_wp f -> (

let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (

let _57_785 = (FStar_TypeChecker_Env.wp_signature env md_pure.FStar_Syntax_Syntax.mname)
in (match (_57_785) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let wp = (let _154_378 = (let _154_377 = (FStar_Syntax_Syntax.as_arg t)
in (let _154_376 = (let _154_375 = (FStar_Syntax_Syntax.as_arg f)
in (_154_375)::[])
in (_154_377)::_154_376))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wp _154_378 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (mk_comp md_pure FStar_Syntax_Syntax.U_zero FStar_TypeChecker_Common.t_unit wp [])))
end))))


let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((f), (FStar_Syntax_Syntax.Meta_labeled (((reason), (r), (false))))))) None f.FStar_Syntax_Syntax.pos))


let label_opt : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _154_402 = (FStar_TypeChecker_Env.should_verify env)
in (FStar_All.pipe_left Prims.op_Negation _154_402)) then begin
f
end else begin
(let _154_403 = (reason ())
in (label _154_403 r f))
end
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let _57_804 = g
in (let _154_411 = (let _154_410 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_154_410))
in {FStar_TypeChecker_Env.guard_f = _154_411; FStar_TypeChecker_Env.deferred = _57_804.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_804.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_804.FStar_TypeChecker_Env.implicits}))
end))


let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| _57_815 -> begin
g2
end))


let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun _57_820 -> (match (()) with
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

let _57_829 = (destruct_comp c)
in (match (_57_829) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let wp = (let _154_430 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assume_p)
in (let _154_429 = (let _154_428 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _154_427 = (let _154_426 = (FStar_Syntax_Syntax.as_arg f)
in (let _154_425 = (let _154_424 = (FStar_Syntax_Syntax.as_arg wp)
in (_154_424)::[])
in (_154_426)::_154_425))
in (_154_428)::_154_427))
in (FStar_Syntax_Syntax.mk_Tm_app _154_430 _154_429 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md u_res_t res_t wp c.FStar_Syntax_Syntax.flags)))
end)))
end
end))
end))
in (

let _57_832 = lc
in {FStar_Syntax_Syntax.eff_name = _57_832.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _57_832.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _57_832.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))


let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> if (FStar_TypeChecker_Rel.is_trivial g0) then begin
((lc), (g0))
end else begin
(

let _57_839 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _154_450 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _154_449 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _154_450 _154_449)))
end else begin
()
end
in (

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _57_2 -> (match (_57_2) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _57_845 -> begin
[]
end))))
in (

let strengthen = (fun _57_848 -> (match (()) with
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

let xret = (let _154_455 = (let _154_454 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _154_454))
in (FStar_Syntax_Util.comp_set_flags _154_455 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (

let lc = (bind e.FStar_Syntax_Syntax.pos env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) ((Some (x)), ((FStar_Syntax_Util.lcomp_of_comp xret))))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (

let _57_858 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _154_457 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _154_456 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _154_457 _154_456)))
end else begin
()
end
in (

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _57_864 = (destruct_comp c)
in (match (_57_864) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let wp = (let _154_466 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assert_p)
in (let _154_465 = (let _154_464 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _154_463 = (let _154_462 = (let _154_459 = (let _154_458 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason _154_458 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _154_459))
in (let _154_461 = (let _154_460 = (FStar_Syntax_Syntax.as_arg wp)
in (_154_460)::[])
in (_154_462)::_154_461))
in (_154_464)::_154_463))
in (FStar_Syntax_Syntax.mk_Tm_app _154_466 _154_465 None wp.FStar_Syntax_Syntax.pos)))
in (

let _57_867 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _154_467 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _154_467))
end else begin
()
end
in (

let c2 = (mk_comp md u_res_t res_t wp flags)
in c2))))
end)))))
end)))
end))
in (let _154_471 = (

let _57_870 = lc
in (let _154_470 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _154_469 = if ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _154_468 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _154_468))) then begin
flags
end else begin
[]
end
in {FStar_Syntax_Syntax.eff_name = _154_470; FStar_Syntax_Syntax.res_typ = _57_870.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _154_469; FStar_Syntax_Syntax.comp = strengthen})))
in ((_154_471), ((

let _57_872 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_872.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_872.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_872.FStar_TypeChecker_Env.implicits})))))))
end)


let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env comp res_t -> (

let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let y = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let _57_882 = (let _154_479 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _154_478 = (FStar_Syntax_Syntax.bv_to_name y)
in ((_154_479), (_154_478))))
in (match (_57_882) with
| (xexp, yexp) -> begin
(

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let yret = (let _154_484 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.ret_wp)
in (let _154_483 = (let _154_482 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _154_481 = (let _154_480 = (FStar_Syntax_Syntax.as_arg yexp)
in (_154_480)::[])
in (_154_482)::_154_481))
in (FStar_Syntax_Syntax.mk_Tm_app _154_484 _154_483 None res_t.FStar_Syntax_Syntax.pos)))
in (

let x_eq_y_yret = (let _154_492 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _154_491 = (let _154_490 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _154_489 = (let _154_488 = (let _154_485 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _154_485))
in (let _154_487 = (let _154_486 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_154_486)::[])
in (_154_488)::_154_487))
in (_154_490)::_154_489))
in (FStar_Syntax_Syntax.mk_Tm_app _154_492 _154_491 None res_t.FStar_Syntax_Syntax.pos)))
in (

let forall_y_x_eq_y_yret = (let _154_502 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::(u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _154_501 = (let _154_500 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _154_499 = (let _154_498 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _154_497 = (let _154_496 = (let _154_495 = (let _154_494 = (let _154_493 = (FStar_Syntax_Syntax.mk_binder y)
in (_154_493)::[])
in (FStar_Syntax_Util.abs _154_494 x_eq_y_yret (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _154_495))
in (_154_496)::[])
in (_154_498)::_154_497))
in (_154_500)::_154_499))
in (FStar_Syntax_Syntax.mk_Tm_app _154_502 _154_501 None res_t.FStar_Syntax_Syntax.pos)))
in (

let lc2 = (mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (

let lc = (let _154_503 = (FStar_TypeChecker_Env.get_range env)
in (bind _154_503 env None (FStar_Syntax_Util.lcomp_of_comp comp) ((Some (x)), ((FStar_Syntax_Util.lcomp_of_comp lc2)))))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))


let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (

let comp = (fun _57_894 -> (match (()) with
| () -> begin
(

let _57_911 = (let _154_515 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _154_514 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _154_515 _154_514)))
in (match (_57_911) with
| ((md, _57_897, _57_899), (u_res_t, res_t, wp_then), (_57_906, _57_908, wp_else)) -> begin
(

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _154_535 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (let _154_534 = (let _154_532 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _154_531 = (let _154_530 = (FStar_Syntax_Syntax.as_arg g)
in (let _154_529 = (let _154_528 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _154_527 = (let _154_526 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_154_526)::[])
in (_154_528)::_154_527))
in (_154_530)::_154_529))
in (_154_532)::_154_531))
in (let _154_533 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _154_535 _154_534 None _154_533)))))
in (

let wp = (ifthenelse md res_t guard wp_then wp_else)
in if ((FStar_Options.split_cases ()) > (Prims.parse_int "0")) then begin
(

let comp = (mk_comp md u_res_t res_t wp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(

let wp = (let _154_540 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (let _154_539 = (let _154_538 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _154_537 = (let _154_536 = (FStar_Syntax_Syntax.as_arg wp)
in (_154_536)::[])
in (_154_538)::_154_537))
in (FStar_Syntax_Syntax.mk_Tm_app _154_540 _154_539 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md u_res_t res_t wp []))
end))
end))
end))
in (let _154_541 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _154_541; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp})))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (let _154_547 = (let _154_546 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid _154_546))
in (FStar_Syntax_Syntax.fvar _154_547 FStar_Syntax_Syntax.Delta_constant None)))


let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (FStar_List.fold_left (fun eff _57_930 -> (match (_57_930) with
| (_57_928, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (

let bind_cases = (fun _57_933 -> (match (()) with
| () -> begin
(

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _154_577 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (let _154_576 = (let _154_574 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _154_573 = (let _154_572 = (FStar_Syntax_Syntax.as_arg g)
in (let _154_571 = (let _154_570 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _154_569 = (let _154_568 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_154_568)::[])
in (_154_570)::_154_569))
in (_154_572)::_154_571))
in (_154_574)::_154_573))
in (let _154_575 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _154_577 _154_576 None _154_575)))))
in (

let default_case = (

let post_k = (let _154_580 = (let _154_578 = (FStar_Syntax_Syntax.null_binder res_t)
in (_154_578)::[])
in (let _154_579 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _154_580 _154_579)))
in (

let kwp = (let _154_583 = (let _154_581 = (FStar_Syntax_Syntax.null_binder post_k)
in (_154_581)::[])
in (let _154_582 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _154_583 _154_582)))
in (

let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (

let wp = (let _154_589 = (let _154_584 = (FStar_Syntax_Syntax.mk_binder post)
in (_154_584)::[])
in (let _154_588 = (let _154_587 = (let _154_585 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Errors.exhaustiveness_check _154_585))
in (let _154_586 = (fvar_const env FStar_Syntax_Const.false_lid)
in (FStar_All.pipe_left _154_587 _154_586)))
in (FStar_Syntax_Util.abs _154_589 _154_588 (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md u_res_t res_t wp []))))))
in (

let comp = (FStar_List.fold_right (fun _57_949 celse -> (match (_57_949) with
| (g, cthen) -> begin
(

let _57_969 = (let _154_592 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _154_592 celse))
in (match (_57_969) with
| ((md, _57_953, _57_955), (_57_958, _57_960, wp_then), (_57_964, _57_966, wp_else)) -> begin
(let _154_593 = (ifthenelse md res_t g wp_then wp_else)
in (mk_comp md u_res_t res_t _154_593 []))
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

let _57_978 = (destruct_comp comp)
in (match (_57_978) with
| (_57_974, _57_976, wp) -> begin
(

let wp = (let _154_598 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (let _154_597 = (let _154_596 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _154_595 = (let _154_594 = (FStar_Syntax_Syntax.as_arg wp)
in (_154_594)::[])
in (_154_596)::_154_595))
in (FStar_Syntax_Syntax.mk_Tm_app _154_598 _154_597 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md u_res_t res_t wp []))
end))))
end))))
end))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))


let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (

let close = (fun _57_984 -> (match (()) with
| () -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in if (FStar_Syntax_Util.is_ml_comp c) then begin
c
end else begin
(

let close_wp = (fun u_res md res_t bvs wp0 -> (FStar_List.fold_right (fun x wp -> (

let bs = (let _154_619 = (FStar_Syntax_Syntax.mk_binder x)
in (_154_619)::[])
in (

let us = (let _154_621 = (let _154_620 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (_154_620)::[])
in (u_res)::_154_621)
in (

let wp = (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))))))
in (let _154_628 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (let _154_627 = (let _154_626 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _154_625 = (let _154_624 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _154_623 = (let _154_622 = (FStar_Syntax_Syntax.as_arg wp)
in (_154_622)::[])
in (_154_624)::_154_623))
in (_154_626)::_154_625))
in (FStar_Syntax_Syntax.mk_Tm_app _154_628 _154_627 None wp0.FStar_Syntax_Syntax.pos))))))) bvs wp0))
in (

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _57_1001 = (destruct_comp c)
in (match (_57_1001) with
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

let _57_1004 = lc
in {FStar_Syntax_Syntax.eff_name = _57_1004.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _57_1004.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _57_1004.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))


let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (

let refine = (fun _57_1010 -> (match (()) with
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
(let _154_639 = (let _154_638 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _154_637 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _154_638 _154_637)))
in (FStar_All.failwith _154_639))
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

let ret = (let _154_641 = (let _154_640 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _154_640 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _154_641))
in (

let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (

let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (

let c = (let _154_643 = (let _154_642 = (bind e.FStar_Syntax_Syntax.pos env None (FStar_Syntax_Util.lcomp_of_comp c) ((Some (x)), (eq_ret)))
in (_154_642.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _154_643 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
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

let _57_1022 = lc
in {FStar_Syntax_Syntax.eff_name = _57_1022.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _57_1022.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))


let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (match ((FStar_TypeChecker_Rel.sub_comp env c c')) with
| None -> begin
(let _154_655 = (let _154_654 = (let _154_653 = (FStar_TypeChecker_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _154_652 = (FStar_TypeChecker_Env.get_range env)
in ((_154_653), (_154_652))))
in FStar_Syntax_Syntax.Error (_154_654))
in (Prims.raise _154_655))
end
| Some (g) -> begin
((e), (c'), (g))
end))


let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match ((let _154_664 = (FStar_Syntax_Subst.compress t)
in _154_664.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_1036) -> begin
(match ((let _154_665 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _154_665.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid) -> begin
(

let _57_1040 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (

let b2t = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (

let lc = (let _154_668 = (let _154_667 = (let _154_666 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _154_666))
in ((None), (_154_667)))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) lc _154_668))
in (

let e = (let _154_670 = (let _154_669 = (FStar_Syntax_Syntax.as_arg e)
in (_154_669)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _154_670 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in ((e), (lc))))))
end
| _57_1046 -> begin
((e), (lc))
end)
end
| _57_1048 -> begin
((e), (lc))
end))


let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (

let gopt = if env.FStar_TypeChecker_Env.use_eq then begin
(let _154_679 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in ((_154_679), (false)))
end else begin
(let _154_680 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in ((_154_680), (true)))
end
in (match (gopt) with
| (None, _57_1056) -> begin
(

let _57_1058 = (FStar_TypeChecker_Rel.subtype_fail env e lc.FStar_Syntax_Syntax.res_typ t)
in ((e), ((

let _57_1060 = lc
in {FStar_Syntax_Syntax.eff_name = _57_1060.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _57_1060.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _57_1060.FStar_Syntax_Syntax.comp})), (FStar_TypeChecker_Rel.trivial_guard)))
end
| (Some (g), apply_guard) -> begin
(match ((FStar_TypeChecker_Rel.guard_form g)) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let lc = (

let _57_1067 = lc
in {FStar_Syntax_Syntax.eff_name = _57_1067.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _57_1067.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _57_1067.FStar_Syntax_Syntax.comp})
in ((e), (lc), (g)))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let g = (

let _57_1072 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_1072.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_1072.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_1072.FStar_TypeChecker_Env.implicits})
in (

let strengthen = (fun _57_1076 -> (match (()) with
| () -> begin
(

let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (match ((let _154_683 = (FStar_Syntax_Subst.compress f)
in _154_683.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_57_1079, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _57_1085; FStar_Syntax_Syntax.pos = _57_1083; FStar_Syntax_Syntax.vars = _57_1081}, _57_1090) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
(

let lc = (

let _57_1093 = lc
in {FStar_Syntax_Syntax.eff_name = _57_1093.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _57_1093.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _57_1093.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| _57_1097 -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let _57_1099 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _154_687 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _154_686 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _154_685 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _154_684 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _154_687 _154_686 _154_685 _154_684)))))
end else begin
()
end
in (

let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _57_1104 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_57_1104) with
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

let _57_1114 = (destruct_comp ct)
in (match (_57_1114) with
| (u_t, _57_1111, _57_1113) -> begin
(

let wp = (let _154_692 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.ret_wp)
in (let _154_691 = (let _154_690 = (FStar_Syntax_Syntax.as_arg t)
in (let _154_689 = (let _154_688 = (FStar_Syntax_Syntax.as_arg xexp)
in (_154_688)::[])
in (_154_690)::_154_689))
in (FStar_Syntax_Syntax.mk_Tm_app _154_692 _154_691 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)))
in (

let cret = (let _154_693 = (mk_comp md u_t t wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _154_693))
in (

let guard = if apply_guard then begin
(let _154_695 = (let _154_694 = (FStar_Syntax_Syntax.as_arg xexp)
in (_154_694)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _154_695 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end else begin
f
end
in (

let _57_1120 = (let _154_703 = (FStar_All.pipe_left (fun _154_700 -> Some (_154_700)) (FStar_TypeChecker_Errors.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _154_702 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _154_701 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _154_703 _154_702 e cret _154_701))))
in (match (_57_1120) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x = (

let _57_1121 = x
in {FStar_Syntax_Syntax.ppname = _57_1121.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1121.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (

let c = (let _154_705 = (let _154_704 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _154_704))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) _154_705 ((Some (x)), (eq_ret))))
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let _57_1126 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _154_706 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _154_706))
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

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _57_3 -> (match (_57_3) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.CPS -> begin
(FStar_Syntax_Syntax.CPS)::[]
end
| _57_1133 -> begin
[]
end))))
in (

let lc = (

let _57_1135 = lc
in (let _154_708 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _154_708; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (

let g = (

let _57_1138 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_1138.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_1138.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_1138.FStar_TypeChecker_Env.implicits})
in ((e), (lc), (g)))))))
end)
end)))


let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _154_720 = (let _154_719 = (let _154_718 = (let _154_717 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _154_717))
in (_154_718)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _154_719 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _154_720))))
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
| ((req, _57_1166))::((ens, _57_1161))::_57_1158 -> begin
(let _154_726 = (let _154_723 = (norm req)
in Some (_154_723))
in (let _154_725 = (let _154_724 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _154_724))
in ((_154_726), (_154_725))))
end
| _57_1170 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Effect constructor is not fully applied"), (comp.FStar_Syntax_Syntax.pos)))))
end)
end else begin
(

let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| ((wp, _57_1176))::_57_1173 -> begin
(

let _57_1182 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (_57_1182) with
| (us_r, _57_1181) -> begin
(

let _57_1186 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (_57_1186) with
| (us_e, _57_1185) -> begin
(

let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (

let as_req = (let _154_727 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.as_requires r) FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.mk_Tm_uinst _154_727 us_r))
in (

let as_ens = (let _154_728 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.as_ensures r) FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.mk_Tm_uinst _154_728 us_e))
in (

let req = (let _154_731 = (let _154_730 = (let _154_729 = (FStar_Syntax_Syntax.as_arg wp)
in (_154_729)::[])
in (((ct.FStar_Syntax_Syntax.result_typ), (Some (FStar_Syntax_Syntax.imp_tag))))::_154_730)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _154_731 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let ens = (let _154_734 = (let _154_733 = (let _154_732 = (FStar_Syntax_Syntax.as_arg wp)
in (_154_732)::[])
in (((ct.FStar_Syntax_Syntax.result_typ), (Some (FStar_Syntax_Syntax.imp_tag))))::_154_733)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _154_734 None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _154_738 = (let _154_735 = (norm req)
in Some (_154_735))
in (let _154_737 = (let _154_736 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm _154_736))
in ((_154_738), (_154_737)))))))))
end))
end))
end
| _57_1193 -> begin
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

let _57_1204 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_1204) with
| (bs, c) -> begin
(

let rec aux = (fun subst _57_4 -> (match (_57_4) with
| ((x, Some (FStar_Syntax_Syntax.Implicit (dot))))::rest -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let _57_1220 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t)
in (match (_57_1220) with
| (v, _57_1218, g) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (v))))::subst
in (

let _57_1226 = (aux subst rest)
in (match (_57_1226) with
| (args, bs, subst, g') -> begin
(let _154_749 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((v), (Some (FStar_Syntax_Syntax.Implicit (dot)))))::args), (bs), (subst), (_154_749)))
end)))
end)))
end
| bs -> begin
(([]), (bs), (subst), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (

let _57_1232 = (aux [] bs)
in (match (_57_1232) with
| (args, bs, subst, guard) -> begin
(match (((args), (bs))) with
| ([], _57_1235) -> begin
((e), (torig), (guard))
end
| (_57_1238, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
((e), (torig), (FStar_TypeChecker_Rel.trivial_guard))
end
| _57_1242 -> begin
(

let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _57_1245 -> begin
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
| _57_1250 -> begin
((e), (t), (FStar_TypeChecker_Rel.trivial_guard))
end)
end))


let string_of_univs = (fun univs -> (let _154_754 = (let _154_753 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _154_753 (FStar_List.map (fun u -> (let _154_752 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _154_752 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _154_754 (FStar_String.concat ", "))))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(

let s = (let _154_760 = (let _154_759 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _154_759))
in (FStar_All.pipe_right _154_760 FStar_Util.set_elements))
in (

let _57_1256 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _154_762 = (let _154_761 = (FStar_TypeChecker_Env.univ_vars env)
in (string_of_univs _154_761))
in (FStar_Util.print1 "univ_vars in env: %s\n" _154_762))
end else begin
()
end
in (

let r = (let _154_763 = (FStar_TypeChecker_Env.get_range env)
in Some (_154_763))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (

let _57_1261 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _154_768 = (let _154_765 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _154_765))
in (let _154_767 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _154_766 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _154_768 _154_767 _154_766))))
end else begin
()
end
in (

let _57_1263 = (FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))))
in u_name))))))
in u_names))))
end)


let gather_free_univnames : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env t -> (

let ctx_univnames = (FStar_TypeChecker_Env.univnames env)
in (

let tm_univnames = (FStar_Syntax_Free.univnames t)
in (

let univnames = (let _154_773 = (FStar_Util.fifo_set_difference tm_univnames ctx_univnames)
in (FStar_All.pipe_right _154_773 FStar_Util.fifo_set_elements))
in univnames))))


let maybe_set_tk = (fun ts _57_5 -> (match (_57_5) with
| None -> begin
ts
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Syntax.mk t None FStar_Range.dummyRange)
in (

let t = (FStar_Syntax_Subst.close_univ_vars (Prims.fst ts) t)
in (

let _57_1278 = (FStar_ST.op_Colon_Equals (Prims.snd ts).FStar_Syntax_Syntax.tk (Some (t.FStar_Syntax_Syntax.n)))
in ts)))
end))


let check_universe_generalization : FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun explicit_univ_names generalized_univ_names t -> (match (((explicit_univ_names), (generalized_univ_names))) with
| ([], _57_1285) -> begin
generalized_univ_names
end
| (_57_1288, []) -> begin
explicit_univ_names
end
| _57_1292 -> begin
(let _154_785 = (let _154_784 = (let _154_783 = (let _154_782 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "Generalized universe in a term containing explicit universe annotation : " _154_782))
in ((_154_783), (t.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_154_784))
in (Prims.raise _154_785))
end))


let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Beta)::[]) env t0)
in (

let univnames = (gather_free_univnames env t)
in (

let univs = (FStar_Syntax_Free.univs t)
in (

let _57_1298 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _154_790 = (string_of_univs univs)
in (FStar_Util.print1 "univs to gen : %s\n" _154_790))
end else begin
()
end
in (

let gen = (gen_univs env univs)
in (

let _57_1301 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _154_791 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _154_791))
end else begin
()
end
in (

let univs = (check_universe_generalization univnames gen t0)
in (

let ts = (FStar_Syntax_Subst.close_univ_vars univs t)
in (let _154_792 = (FStar_ST.read t0.FStar_Syntax_Syntax.tk)
in (maybe_set_tk ((univs), (ts)) _154_792)))))))))))


let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> if (let _154_798 = (FStar_Util.for_all (fun _57_1310 -> (match (_57_1310) with
| (_57_1308, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _154_798)) then begin
None
end else begin
(

let norm = (fun c -> (

let _57_1313 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _154_801 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _154_801))
end else begin
()
end
in (

let c = if (FStar_TypeChecker_Env.should_verify env) then begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
end else begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
end
in (

let _57_1316 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _154_802 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _154_802))
end else begin
()
end
in c))))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (let _154_805 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _154_805 FStar_Util.set_elements)))
in (

let _57_1332 = (let _154_807 = (FStar_All.pipe_right ecs (FStar_List.map (fun _57_1323 -> (match (_57_1323) with
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
in (FStar_All.pipe_right _154_807 FStar_List.unzip))
in (match (_57_1332) with
| (univs, uvars) -> begin
(

let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (

let gen_univs = (gen_univs env univs)
in (

let _57_1336 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end else begin
()
end
in (

let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _57_1341 -> (match (_57_1341) with
| (uvs, e, c) -> begin
(

let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _57_1344 -> (match (_57_1344) with
| (u, k) -> begin
(match ((FStar_Unionfind.find u)) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
((a), (Some (FStar_Syntax_Syntax.imp_tag)))
end
| FStar_Syntax_Syntax.Fixed (_57_1378) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _57_1381 -> begin
(

let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (

let _57_1385 = (FStar_Syntax_Util.arrow_formals k)
in (match (_57_1385) with
| (bs, kres) -> begin
(

let a = (let _154_813 = (let _154_812 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _154_811 -> Some (_154_811)) _154_812))
in (FStar_Syntax_Syntax.new_bv _154_813 kres))
in (

let t = (let _154_818 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _154_817 = (let _154_816 = (let _154_815 = (let _154_814 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _154_814))
in FStar_Util.Inl (_154_815))
in Some (_154_816))
in (FStar_Syntax_Util.abs bs _154_818 _154_817)))
in (

let _57_1388 = (FStar_Syntax_Util.set_uvar u t)
in ((a), (Some (FStar_Syntax_Syntax.imp_tag))))))
end)))
end)
end))))
in (

let _57_1420 = (match (((tvars), (gen_univs))) with
| ([], []) -> begin
((e), (c))
end
| ([], _57_1396) -> begin
(

let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
in (

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env e)
in ((e), (c))))
end
| _57_1401 -> begin
(

let _57_1404 = ((e), (c))
in (match (_57_1404) with
| (e0, c0) -> begin
(

let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
in (

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Iota))::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env e)
in (

let t = (match ((let _154_819 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _154_819.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(

let _57_1413 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (_57_1413) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| _57_1415 -> begin
(FStar_Syntax_Util.arrow tvars c)
end)
in (

let e' = (FStar_Syntax_Util.abs tvars e (Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp c)))))
in (let _154_820 = (FStar_Syntax_Syntax.mk_Total t)
in ((e'), (_154_820)))))))
end))
end)
in (match (_57_1420) with
| (e, c) -> begin
((gen_univs), (e), (c))
end)))
end))))
in Some (ecs)))))
end)))))
end)


let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> (

let _57_1430 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _154_827 = (let _154_826 = (FStar_List.map (fun _57_1429 -> (match (_57_1429) with
| (lb, _57_1426, _57_1428) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _154_826 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _154_827))
end else begin
()
end
in (

let univnames_lecs = (FStar_List.map (fun _57_1435 -> (match (_57_1435) with
| (l, t, c) -> begin
(gather_free_univnames env t)
end)) lecs)
in (

let generalized_lecs = (match ((let _154_830 = (FStar_All.pipe_right lecs (FStar_List.map (fun _57_1441 -> (match (_57_1441) with
| (_57_1438, e, c) -> begin
((e), (c))
end))))
in (gen env _154_830))) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun _57_1446 -> (match (_57_1446) with
| (l, t, c) -> begin
((l), ([]), (t), (c))
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _57_1454 _57_1458 -> (match (((_57_1454), (_57_1458))) with
| ((l, _57_1451, _57_1453), (us, e, c)) -> begin
(

let _57_1459 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _154_837 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _154_836 = (FStar_Syntax_Print.lbname_to_string l)
in (let _154_835 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (let _154_834 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print4 "(%s) Generalized %s at type %s\n%s\n" _154_837 _154_836 _154_835 _154_834)))))
end else begin
()
end
in ((l), (us), (e), (c)))
end)) lecs ecs)
end)
in (FStar_List.map2 (fun univnames _57_1467 -> (match (_57_1467) with
| (l, generalized_univs, t, c) -> begin
(let _154_840 = (check_universe_generalization univnames generalized_univs t)
in ((l), (_154_840), (t), (c)))
end)) univnames_lecs generalized_lecs)))))


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
(let _154_856 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _154_855 -> Some (_154_855)) _154_856))
end)
end)
in (

let is_var = (fun e -> (match ((let _154_859 = (FStar_Syntax_Subst.compress e)
in _154_859.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (_57_1483) -> begin
true
end
| _57_1486 -> begin
false
end))
in (

let decorate = (fun e t -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((

let _57_1493 = x
in {FStar_Syntax_Syntax.ppname = _57_1493.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1493.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| _57_1496 -> begin
(

let _57_1497 = e
in (let _154_864 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _57_1497.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _154_864; FStar_Syntax_Syntax.pos = _57_1497.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_1497.FStar_Syntax_Syntax.vars}))
end)))
in (

let env = (

let _57_1499 = env
in (let _154_865 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _57_1499.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1499.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1499.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1499.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1499.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1499.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1499.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1499.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1499.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1499.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1499.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1499.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1499.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1499.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1499.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _154_865; FStar_TypeChecker_Env.is_iface = _57_1499.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1499.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_1499.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _57_1499.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _57_1499.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1499.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1499.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _57_1499.FStar_TypeChecker_Env.qname_and_index}))
in (match ((check env t1 t2)) with
| None -> begin
(let _154_869 = (let _154_868 = (let _154_867 = (FStar_TypeChecker_Errors.expected_expression_of_type env t2 e t1)
in (let _154_866 = (FStar_TypeChecker_Env.get_range env)
in ((_154_867), (_154_866))))
in FStar_Syntax_Syntax.Error (_154_868))
in (Prims.raise _154_869))
end
| Some (g) -> begin
(

let _57_1505 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_870 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _154_870))
end else begin
()
end
in (let _154_871 = (decorate e t2)
in ((_154_871), (g))))
end)))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (

let discharge = (fun g -> (

let _57_1512 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _154_881 = (discharge g)
in (let _154_880 = (lc.FStar_Syntax_Syntax.comp ())
in ((_154_881), (_154_880))))
end else begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let steps = (FStar_TypeChecker_Normalize.Beta)::[]
in (

let c = (let _154_884 = (let _154_883 = (let _154_882 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (FStar_All.pipe_right _154_882 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right _154_883 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (FStar_All.pipe_right _154_884 (FStar_TypeChecker_Normalize.comp_to_comp_typ env)))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let _57_1522 = (destruct_comp c)
in (match (_57_1522) with
| (u_t, t, wp) -> begin
(

let vc = (let _154_890 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.trivial)
in (let _154_889 = (let _154_887 = (FStar_Syntax_Syntax.as_arg t)
in (let _154_886 = (let _154_885 = (FStar_Syntax_Syntax.as_arg wp)
in (_154_885)::[])
in (_154_887)::_154_886))
in (let _154_888 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk_Tm_app _154_890 _154_889 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _154_888))))
in (

let _57_1524 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _154_891 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _154_891))
end else begin
()
end
in (

let g = (let _154_892 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _154_892))
in (let _154_894 = (discharge g)
in (let _154_893 = (FStar_Syntax_Syntax.mk_Comp c)
in ((_154_894), (_154_893)))))))
end))))))
end)))


let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (

let short_bin_op = (fun f _57_6 -> (match (_57_6) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((fst, _57_1535))::[] -> begin
(f fst)
end
| _57_1539 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (

let op_and_e = (fun e -> (let _154_915 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _154_915 (fun _154_914 -> FStar_TypeChecker_Common.NonTrivial (_154_914)))))
in (

let op_or_e = (fun e -> (let _154_920 = (let _154_918 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _154_918))
in (FStar_All.pipe_right _154_920 (fun _154_919 -> FStar_TypeChecker_Common.NonTrivial (_154_919)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _154_923 -> FStar_TypeChecker_Common.NonTrivial (_154_923))))
in (

let op_or_t = (fun t -> (let _154_927 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _154_927 (fun _154_926 -> FStar_TypeChecker_Common.NonTrivial (_154_926)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _154_930 -> FStar_TypeChecker_Common.NonTrivial (_154_930))))
in (

let short_op_ite = (fun _57_7 -> (match (_57_7) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((guard, _57_1554))::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| (_then)::((guard, _57_1559))::[] -> begin
(let _154_934 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _154_934 (fun _154_933 -> FStar_TypeChecker_Common.NonTrivial (_154_933))))
end
| _57_1564 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (

let table = (((FStar_Syntax_Const.op_And), ((short_bin_op op_and_e))))::(((FStar_Syntax_Const.op_Or), ((short_bin_op op_or_e))))::(((FStar_Syntax_Const.and_lid), ((short_bin_op op_and_t))))::(((FStar_Syntax_Const.or_lid), ((short_bin_op op_or_t))))::(((FStar_Syntax_Const.imp_lid), ((short_bin_op op_imp_t))))::(((FStar_Syntax_Const.ite_lid), (short_op_ite)))::[]
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((FStar_Util.find_map table (fun _57_1572 -> (match (_57_1572) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _154_967 = (mk seen_args)
in Some (_154_967))
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
| _57_1577 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (match ((let _154_970 = (FStar_Syntax_Util.un_uinst l)
in _154_970.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| _57_1582 -> begin
false
end))


let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (

let pos = (fun bs -> (match (bs) with
| ((hd, _57_1591))::_57_1588 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| _57_1595 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| ((_57_1599, Some (FStar_Syntax_Syntax.Implicit (_57_1601))))::_57_1597 -> begin
bs
end
| _57_1607 -> begin
(match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
bs
end
| Some (t) -> begin
(match ((let _154_977 = (FStar_Syntax_Subst.compress t)
in _154_977.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', _57_1613) -> begin
(match ((FStar_Util.prefix_until (fun _57_8 -> (match (_57_8) with
| (_57_1618, Some (FStar_Syntax_Syntax.Implicit (_57_1620))) -> begin
false
end
| _57_1625 -> begin
true
end)) bs')) with
| None -> begin
bs
end
| Some ([], _57_1629, _57_1631) -> begin
bs
end
| Some (imps, _57_1636, _57_1638) -> begin
if (FStar_All.pipe_right imps (FStar_Util.for_all (fun _57_1644 -> (match (_57_1644) with
| (x, _57_1643) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end)))) then begin
(

let r = (pos bs)
in (

let imps = (FStar_All.pipe_right imps (FStar_List.map (fun _57_1648 -> (match (_57_1648) with
| (x, i) -> begin
(let _154_981 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in ((_154_981), (i)))
end))))
in (FStar_List.append imps bs)))
end else begin
bs
end
end)
end
| _57_1651 -> begin
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
(let _154_990 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m2))))))) _154_990 e.FStar_Syntax_Syntax.pos))
end)))


let maybe_monadic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c t -> (

let m = (FStar_TypeChecker_Env.norm_eff_name env c)
in if (((is_pure_or_ghost_effect env m) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid)) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid)) then begin
e
end else begin
(let _154_999 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))) _154_999 e.FStar_Syntax_Syntax.pos))
end))


let effect_repr_aux = (fun only_reifiable env c u_c -> (match ((let _154_1004 = (FStar_TypeChecker_Env.norm_eff_name env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_TypeChecker_Env.effect_decl_opt env _154_1004))) with
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
| _57_1672 -> begin
(

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _57_1676 = (let _154_1005 = (FStar_List.hd c.FStar_Syntax_Syntax.effect_args)
in ((c.FStar_Syntax_Syntax.result_typ), (_154_1005)))
in (match (_57_1676) with
| (res_typ, wp) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_c)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (let _154_1011 = (let _154_1010 = (let _154_1008 = (let _154_1007 = (let _154_1006 = (FStar_Syntax_Syntax.as_arg res_typ)
in (_154_1006)::(wp)::[])
in ((repr), (_154_1007)))
in FStar_Syntax_Syntax.Tm_app (_154_1008))
in (let _154_1009 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _154_1010 None _154_1009)))
in Some (_154_1011)))
end)))
end)
end
end))


let effect_repr : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term Prims.option = (fun env c u_c -> (effect_repr_aux false env c u_c))


let reify_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term = (fun env c u_c -> (

let no_reify = (fun l -> (let _154_1029 = (let _154_1028 = (let _154_1027 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _154_1026 = (FStar_TypeChecker_Env.get_range env)
in ((_154_1027), (_154_1026))))
in FStar_Syntax_Syntax.Error (_154_1028))
in (Prims.raise _154_1029)))
in (match ((let _154_1030 = (c.FStar_Syntax_Syntax.comp ())
in (effect_repr_aux true env _154_1030 u_c))) with
| None -> begin
(no_reify c.FStar_Syntax_Syntax.eff_name)
end
| Some (tm) -> begin
tm
end)))


let d : Prims.string  ->  Prims.unit = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))


let mk_toplevel_definition : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term) = (fun env lident def -> (

let _57_1695 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _57_1693 = (d (FStar_Ident.text_of_lid lident))
in (let _154_1039 = (FStar_Syntax_Print.term_to_string def)
in (FStar_Util.print2 "Registering top-level definition: %s\n%s\n" (FStar_Ident.text_of_lid lident) _154_1039)))
end else begin
()
end
in (

let fv = (let _154_1040 = (FStar_Syntax_Util.incr_delta_qualifier def)
in (FStar_Syntax_Syntax.lid_as_fv lident _154_1040 None))
in (

let lbname = FStar_Util.Inr (fv)
in (

let lb = ((false), (({FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = def})::[]))
in (

let sig_ctx = FStar_Syntax_Syntax.Sig_let (((lb), (FStar_Range.dummyRange), ((lident)::[]), ((FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)::[])))
in (let _154_1041 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) None FStar_Range.dummyRange)
in ((sig_ctx), (_154_1041)))))))))


let check_sigelt_quals : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (

let visibility = (fun _57_9 -> (match (_57_9) with
| FStar_Syntax_Syntax.Private -> begin
true
end
| _57_1706 -> begin
false
end))
in (

let reducibility = (fun _57_10 -> (match (_57_10) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) | (FStar_Syntax_Syntax.Visible_default) | (FStar_Syntax_Syntax.Inline_for_extraction) -> begin
true
end
| _57_1715 -> begin
false
end))
in (

let assumption = (fun _57_11 -> (match (_57_11) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.New) -> begin
true
end
| _57_1721 -> begin
false
end))
in (

let reification = (fun _57_12 -> (match (_57_12) with
| (FStar_Syntax_Syntax.Reifiable) | (FStar_Syntax_Syntax.Reflectable (_)) -> begin
true
end
| _57_1729 -> begin
false
end))
in (

let inferred = (fun _57_13 -> (match (_57_13) with
| (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) | (FStar_Syntax_Syntax.ExceptionConstructor) | (FStar_Syntax_Syntax.HasMaskedEffect) | (FStar_Syntax_Syntax.Effect) -> begin
true
end
| _57_1748 -> begin
false
end))
in (

let has_eq = (fun _57_14 -> (match (_57_14) with
| (FStar_Syntax_Syntax.Noeq) | (FStar_Syntax_Syntax.Unopteq) -> begin
true
end
| _57_1754 -> begin
false
end))
in (

let quals_combo_ok = (fun quals q -> (match (q) with
| FStar_Syntax_Syntax.Assumption -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) || (inferred x)) || (visibility x)) || (assumption x)) || (env.FStar_TypeChecker_Env.is_iface && (x = FStar_Syntax_Syntax.Inline_for_extraction))))))
end
| FStar_Syntax_Syntax.New -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((x = q) || (inferred x)) || (visibility x)) || (assumption x)))))
end
| FStar_Syntax_Syntax.Inline_for_extraction -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) || (visibility x)) || (reducibility x)) || (reification x)) || (inferred x)) || (env.FStar_TypeChecker_Env.is_iface && (x = FStar_Syntax_Syntax.Assumption))))))
end
| (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) | (FStar_Syntax_Syntax.Visible_default) | (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Noeq) | (FStar_Syntax_Syntax.Unopteq) -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) || (x = FStar_Syntax_Syntax.Abstract)) || (x = FStar_Syntax_Syntax.Inline_for_extraction)) || (has_eq x)) || (inferred x)) || (visibility x)))))
end
| FStar_Syntax_Syntax.TotalEffect -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((x = q) || (inferred x)) || (visibility x)) || (reification x)))))
end
| FStar_Syntax_Syntax.Logic -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> (((((x = q) || (x = FStar_Syntax_Syntax.Assumption)) || (inferred x)) || (visibility x)) || (reducibility x)))))
end
| (FStar_Syntax_Syntax.Reifiable) | (FStar_Syntax_Syntax.Reflectable (_)) -> begin
(FStar_All.pipe_right quals (FStar_List.for_all (fun x -> ((((reification x) || (inferred x)) || (visibility x)) || (x = FStar_Syntax_Syntax.TotalEffect)))))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| _57_1783 -> begin
true
end))
in (

let quals = (FStar_Syntax_Util.quals_of_sigelt se)
in (

let r = (FStar_Syntax_Util.range_of_sigelt se)
in (

let no_dup_quals = (FStar_Util.remove_dups (fun x y -> (x = y)) quals)
in (

let err' = (fun msg -> (let _154_1076 = (let _154_1075 = (let _154_1074 = (let _154_1073 = (FStar_Syntax_Print.quals_to_string quals)
in (FStar_Util.format2 "The qualifier list \"[%s]\" is not permissible for this element%s" _154_1073 msg))
in ((_154_1074), (r)))
in FStar_Syntax_Syntax.Error (_154_1075))
in (Prims.raise _154_1076)))
in (

let err = (fun msg -> (err' (Prims.strcat ": " msg)))
in (

let err' = (fun _57_1794 -> (match (()) with
| () -> begin
(err' "")
end))
in (

let _57_1795 = if ((FStar_List.length quals) <> (FStar_List.length no_dup_quals)) then begin
(err "duplicate qualifiers")
end else begin
()
end
in (

let _57_1797 = if (not ((FStar_All.pipe_right quals (FStar_List.for_all (quals_combo_ok quals))))) then begin
(err "ill-formed combination")
end else begin
()
end
in (match (se) with
| FStar_Syntax_Syntax.Sig_let ((is_rec, _57_1801), _57_1804, _57_1806, _57_1808) -> begin
(

let _57_1811 = if (is_rec && (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))) then begin
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
| FStar_Syntax_Syntax.Sig_bundle (_57_1815) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.Abstract) || (inferred x)) || (visibility x)) || (has_eq x))))))) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (_57_1819) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some has_eq)) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_assume (_57_1822) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((visibility x) || (x = FStar_Syntax_Syntax.Assumption))))))) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_new_effect (_57_1826) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x))))))) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_57_1830) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x))))))) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_57_1834) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((inferred x) || (visibility x))))))) then begin
(err' ())
end else begin
()
end
end
| _57_1838 -> begin
()
end)))))))))))))))))




