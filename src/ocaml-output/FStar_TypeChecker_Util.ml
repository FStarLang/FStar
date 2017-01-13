
open Prims

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv Prims.option * FStar_Syntax_Syntax.lcomp)


let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _160_6 = (FStar_TypeChecker_Env.get_range env)
in (let _160_5 = (FStar_TypeChecker_Err.failed_to_prove_specification errs)
in (FStar_Errors.report _160_6 _160_5))))


let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _160_9 = (FStar_Syntax_Subst.compress t)
in _160_9.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_59_25) -> begin
true
end
| _59_28 -> begin
false
end))


let t_binders : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env -> (let _160_13 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right _160_13 (FStar_List.filter (fun _59_33 -> (match (_59_33) with
| (x, _59_32) -> begin
(is_type x.FStar_Syntax_Syntax.sort)
end))))))


let new_uvar_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun env k -> (

let bs = if ((FStar_Options.full_context_dependency ()) || (let _160_18 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _160_18))) then begin
(FStar_TypeChecker_Env.all_binders env)
end else begin
(t_binders env)
end
in (let _160_19 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Rel.new_uvar _160_19 bs k))))


let new_uvar : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env k -> (let _160_24 = (new_uvar_aux env k)
in (Prims.fst _160_24)))


let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun _59_1 -> (match (_59_1) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, _59_48); FStar_Syntax_Syntax.tk = _59_45; FStar_Syntax_Syntax.pos = _59_43; FStar_Syntax_Syntax.vars = _59_41} -> begin
uv
end
| _59_53 -> begin
(failwith "Impossible")
end))


let new_implicit_var : Prims.string  ->  FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.uvar * FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t) = (fun reason r env k -> (match ((FStar_Syntax_Util.destruct k FStar_Syntax_Const.range_of_lid)) with
| Some ((_59_63)::((tm, _59_60))::[]) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))) None tm.FStar_Syntax_Syntax.pos)
in ((t), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
end
| _59_68 -> begin
(

let _59_71 = (new_uvar_aux env k)
in (match (_59_71) with
| (t, u) -> begin
(

let g = (

let _59_72 = FStar_TypeChecker_Rel.trivial_guard
in (let _160_37 = (let _160_36 = (let _160_35 = (as_uvar u)
in ((reason), (env), (_160_35), (t), (k), (r)))
in (_160_36)::[])
in {FStar_TypeChecker_Env.guard_f = _59_72.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _59_72.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _59_72.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _160_37}))
in (let _160_40 = (let _160_39 = (let _160_38 = (as_uvar u)
in ((_160_38), (r)))
in (_160_39)::[])
in ((t), (_160_40), (g))))
end))
end))


let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun r t -> (

let uvs = (FStar_Syntax_Free.uvars t)
in if (not ((FStar_Util.set_is_empty uvs))) then begin
(

let us = (let _160_47 = (let _160_46 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun _59_81 -> (match (_59_81) with
| (x, _59_80) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) _160_46))
in (FStar_All.pipe_right _160_47 (FStar_String.concat ", ")))
in (

let _59_83 = (FStar_Options.push ())
in (

let _59_85 = (FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool (false)))
in (

let _59_87 = (FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)))
in (

let _59_89 = (let _160_49 = (let _160_48 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us _160_48))
in (FStar_Errors.report r _160_49))
in (FStar_Options.pop ()))))))
end else begin
()
end))


let force_sort' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' = (fun s -> (match ((FStar_ST.read s.FStar_Syntax_Syntax.tk)) with
| None -> begin
(let _160_54 = (let _160_53 = (FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos)
in (let _160_52 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s" _160_53 _160_52)))
in (failwith _160_54))
end
| Some (tk) -> begin
tk
end))


let force_sort = (fun s -> (let _160_56 = (force_sort' s)
in (FStar_Syntax_Syntax.mk _160_56 None s.FStar_Syntax_Syntax.pos)))


let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env _59_104 -> (match (_59_104) with
| {FStar_Syntax_Syntax.lbname = _59_103; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _59_99; FStar_Syntax_Syntax.lbdef = e} -> begin
(

let rng = t.FStar_Syntax_Syntax.pos
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _59_108 = if (univ_vars <> []) then begin
(failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let mk_binder = (fun scope a -> (match ((let _160_65 = (FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort)
in _160_65.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _59_118 = (FStar_Syntax_Util.type_u ())
in (match (_59_118) with
| (k, _59_117) -> begin
(

let t = (let _160_66 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right _160_66 Prims.fst))
in (((

let _59_120 = a
in {FStar_Syntax_Syntax.ppname = _59_120.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_120.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (false)))
end))
end
| _59_123 -> begin
((a), (true))
end))
in (

let rec aux = (fun must_check_ty vars e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, _59_131) -> begin
(aux must_check_ty vars e)
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _59_137) -> begin
((t), (true))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _59_143) -> begin
(

let _59_162 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _59_149 _59_152 -> (match (((_59_149), (_59_152))) with
| ((scope, bs, must_check_ty), (a, imp)) -> begin
(

let _59_155 = if must_check_ty then begin
((a), (true))
end else begin
(mk_binder scope a)
end
in (match (_59_155) with
| (tb, must_check_ty) -> begin
(

let b = ((tb), (imp))
in (

let bs = (FStar_List.append bs ((b)::[]))
in (

let scope = (FStar_List.append scope ((b)::[]))
in ((scope), (bs), (must_check_ty)))))
end))
end)) ((vars), ([]), (must_check_ty))))
in (match (_59_162) with
| (scope, bs, must_check_ty) -> begin
(

let _59_165 = (aux must_check_ty scope body)
in (match (_59_165) with
| (res, must_check_ty) -> begin
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

let _59_172 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _160_77 = (FStar_Range.string_of_range r)
in (let _160_76 = (FStar_Syntax_Print.term_to_string t)
in (let _160_75 = (FStar_Util.string_of_bool must_check_ty)
in (FStar_Util.print3 "(%s) Using type %s .... must check = %s\n" _160_77 _160_76 _160_75))))
end else begin
()
end
in ((FStar_Util.Inl (t)), (must_check_ty)))))
end))
end))
end
| _59_175 -> begin
if must_check_ty then begin
((FStar_Util.Inl (FStar_Syntax_Syntax.tun)), (true))
end else begin
(let _160_80 = (let _160_79 = (let _160_78 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _160_78 Prims.fst))
in FStar_Util.Inl (_160_79))
in ((_160_80), (false)))
end
end)))
in (

let _59_178 = (let _160_81 = (t_binders env)
in (aux false _160_81 e))
in (match (_59_178) with
| (t, b) -> begin
(

let t = (match (t) with
| FStar_Util.Inr (c) -> begin
(let _160_85 = (let _160_84 = (let _160_83 = (let _160_82 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" _160_82))
in ((_160_83), (rng)))
in FStar_Errors.Error (_160_84))
in (Prims.raise _160_85))
end
| FStar_Util.Inl (t) -> begin
t
end)
in (([]), (t), (b)))
end))))))
end
| _59_185 -> begin
(

let _59_188 = (FStar_Syntax_Subst.open_univ_vars univ_vars t)
in (match (_59_188) with
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
| FStar_Syntax_Syntax.Pat_dot_term (x, _59_201) -> begin
(

let _59_207 = (FStar_Syntax_Util.type_u ())
in (match (_59_207) with
| (k, _59_206) -> begin
(

let t = (new_uvar env k)
in (

let x = (

let _59_209 = x
in {FStar_Syntax_Syntax.ppname = _59_209.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_209.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let _59_214 = (let _160_98 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _160_98 t))
in (match (_59_214) with
| (e, u) -> begin
(

let p = (

let _59_215 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (e))); FStar_Syntax_Syntax.ty = _59_215.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _59_215.FStar_Syntax_Syntax.p})
in (([]), ([]), ([]), (env), (e), (p)))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let _59_223 = (FStar_Syntax_Util.type_u ())
in (match (_59_223) with
| (t, _59_222) -> begin
(

let x = (

let _59_224 = x
in (let _160_99 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _59_224.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_224.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _160_99}))
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

let _59_234 = (FStar_Syntax_Util.type_u ())
in (match (_59_234) with
| (t, _59_233) -> begin
(

let x = (

let _59_235 = x
in (let _160_100 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _59_235.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_235.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _160_100}))
in (

let env = (FStar_TypeChecker_Env.push_bv env x)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in (((x)::[]), ((x)::[]), ([]), (env), (e), (p)))))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _59_268 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _59_250 _59_253 -> (match (((_59_250), (_59_253))) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(

let _59_260 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_59_260) with
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
in (match (_59_268) with
| (b, a, w, env, args, pats) -> begin
(

let e = (let _160_107 = (let _160_106 = (let _160_105 = (let _160_104 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (let _160_103 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app _160_104 _160_103 None p.FStar_Syntax_Syntax.p)))
in ((_160_105), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))
in FStar_Syntax_Syntax.Tm_meta (_160_106))
in (FStar_Syntax_Syntax.mk _160_107 None p.FStar_Syntax_Syntax.p))
in (let _160_110 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _160_109 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _160_108 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in ((_160_110), (_160_109), (_160_108), (env), (e), ((

let _59_270 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _59_270.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _59_270.FStar_Syntax_Syntax.p})))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (_59_273) -> begin
(failwith "impossible")
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

let pats = (FStar_List.map (fun _59_288 -> (match (_59_288) with
| (p, imp) -> begin
(let _160_122 = (elaborate_pat env p)
in ((_160_122), (imp)))
end)) pats)
in (

let _59_293 = (FStar_TypeChecker_Env.lookup_datacon env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_59_293) with
| (_59_291, t) -> begin
(

let _59_297 = (FStar_Syntax_Util.arrow_formals t)
in (match (_59_297) with
| (f, _59_296) -> begin
(

let rec aux = (fun formals pats -> (match (((formals), (pats))) with
| ([], []) -> begin
[]
end
| ([], (_59_308)::_59_306) -> begin
(Prims.raise (FStar_Errors.Error ((("Too many pattern arguments"), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))))
end
| ((_59_314)::_59_312, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun _59_320 -> (match (_59_320) with
| (t, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(

let a = (let _160_129 = (let _160_128 = (FStar_Syntax_Syntax.range_of_bv t)
in Some (_160_128))
in (FStar_Syntax_Syntax.new_bv _160_129 FStar_Syntax_Syntax.tun))
in (

let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (let _160_130 = (maybe_dot inaccessible a r)
in ((_160_130), (true)))))
end
| _59_327 -> begin
(let _160_134 = (let _160_133 = (let _160_132 = (let _160_131 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _160_131))
in ((_160_132), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))
in FStar_Errors.Error (_160_133))
in (Prims.raise _160_134))
end)
end))))
end
| ((f)::formals', ((p, p_imp))::pats') -> begin
(match (f) with
| (_59_338, Some (FStar_Syntax_Syntax.Implicit (_59_340))) when p_imp -> begin
(let _160_135 = (aux formals' pats')
in (((p), (true)))::_160_135)
end
| (_59_345, Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(

let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let p = (maybe_dot inaccessible a (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
in (let _160_136 = (aux formals' pats)
in (((p), (true)))::_160_136)))
end
| (_59_353, imp) -> begin
(let _160_139 = (let _160_137 = (FStar_Syntax_Syntax.is_implicit imp)
in ((p), (_160_137)))
in (let _160_138 = (aux formals' pats')
in (_160_139)::_160_138))
end)
end))
in (

let _59_356 = p
in (let _160_142 = (let _160_141 = (let _160_140 = (aux f pats)
in ((fv), (_160_140)))
in FStar_Syntax_Syntax.Pat_cons (_160_141))
in {FStar_Syntax_Syntax.v = _160_142; FStar_Syntax_Syntax.ty = _59_356.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _59_356.FStar_Syntax_Syntax.p})))
end))
end)))
end
| _59_359 -> begin
p
end)))
in (

let one_pat = (fun allow_wc_dependence env p -> (

let p = (elaborate_pat env p)
in (

let _59_371 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_59_371) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))) with
| Some (x) -> begin
(let _160_151 = (let _160_150 = (let _160_149 = (FStar_TypeChecker_Err.nonlinear_pattern_variable x)
in ((_160_149), (p.FStar_Syntax_Syntax.p)))
in FStar_Errors.Error (_160_150))
in (Prims.raise _160_151))
end
| _59_375 -> begin
((b), (a), (w), (arg), (p))
end)
end))))
in (

let top_level_pat_as_args = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((q)::pats) -> begin
(

let _59_391 = (one_pat false env q)
in (match (_59_391) with
| (b, a, _59_388, te, q) -> begin
(

let _59_406 = (FStar_List.fold_right (fun p _59_396 -> (match (_59_396) with
| (w, args, pats) -> begin
(

let _59_402 = (one_pat false env p)
in (match (_59_402) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv FStar_Syntax_Syntax.bv_eq a a'))) then begin
(let _160_161 = (let _160_160 = (let _160_159 = (FStar_TypeChecker_Err.disjunctive_pattern_vars a a')
in (let _160_158 = (FStar_TypeChecker_Env.get_range env)
in ((_160_159), (_160_158))))
in FStar_Errors.Error (_160_160))
in (Prims.raise _160_161))
end else begin
(let _160_163 = (let _160_162 = (FStar_Syntax_Syntax.as_arg arg)
in (_160_162)::args)
in (((FStar_List.append w' w)), (_160_163), ((p)::pats)))
end
end))
end)) pats (([]), ([]), ([])))
in (match (_59_406) with
| (w, args, pats) -> begin
(let _160_165 = (let _160_164 = (FStar_Syntax_Syntax.as_arg te)
in (_160_164)::args)
in (((FStar_List.append b w)), (_160_165), ((

let _59_407 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((q)::pats); FStar_Syntax_Syntax.ty = _59_407.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _59_407.FStar_Syntax_Syntax.p}))))
end))
end))
end
| _59_410 -> begin
(

let _59_418 = (one_pat true env p)
in (match (_59_418) with
| (b, _59_413, _59_415, arg, p) -> begin
(let _160_167 = (let _160_166 = (FStar_Syntax_Syntax.as_arg arg)
in (_160_166)::[])
in ((b), (_160_167), (p)))
end))
end))
in (

let _59_422 = (top_level_pat_as_args env p)
in (match (_59_422) with
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
| (_59_436, FStar_Syntax_Syntax.Tm_uinst (e, _59_439)) -> begin
(aux p e)
end
| (FStar_Syntax_Syntax.Pat_constant (_59_444), FStar_Syntax_Syntax.Tm_constant (_59_447)) -> begin
(let _160_182 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v _160_182))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(

let _59_455 = if (not ((FStar_Syntax_Syntax.bv_eq x y))) then begin
(let _160_185 = (let _160_184 = (FStar_Syntax_Print.bv_to_string x)
in (let _160_183 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _160_184 _160_183)))
in (failwith _160_185))
end else begin
()
end
in (

let _59_457 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _160_187 = (FStar_Syntax_Print.bv_to_string x)
in (let _160_186 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _160_187 _160_186)))
end else begin
()
end
in (

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x = (

let _59_460 = x
in {FStar_Syntax_Syntax.ppname = _59_460.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_460.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x)) s.FStar_Syntax_Syntax.n)))))
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(

let _59_468 = if (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation) then begin
(let _160_190 = (let _160_189 = (FStar_Syntax_Print.bv_to_string x)
in (let _160_188 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _160_189 _160_188)))
in (failwith _160_190))
end else begin
()
end
in (

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x = (

let _59_471 = x
in {FStar_Syntax_Syntax.ppname = _59_471.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_471.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x)) s.FStar_Syntax_Syntax.n))))
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _59_476), _59_480) -> begin
(

let s = (force_sort e)
in (

let x = (

let _59_483 = x
in {FStar_Syntax_Syntax.ppname = _59_483.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_483.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term (((x), (e)))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
(

let _59_493 = if (not ((FStar_Syntax_Syntax.fv_eq fv fv'))) then begin
(let _160_191 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith _160_191))
end else begin
()
end
in (let _160_192 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv'), ([])))) _160_192)))
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
(

let _59_536 = if (let _160_193 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right _160_193 Prims.op_Negation)) then begin
(let _160_194 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith _160_194))
end else begin
()
end
in (

let fv = fv'
in (

let rec match_args = (fun matched_pats args argpats -> (match (((args), (argpats))) with
| ([], []) -> begin
(let _160_201 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev matched_pats))))) _160_201))
end
| ((arg)::args, ((argpat, _59_552))::argpats) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e, Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (_59_562)) -> begin
(

let x = (let _160_202 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _160_202))
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e)))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args argpats)))
end
| ((e, imp), _59_571) -> begin
(

let pat = (let _160_204 = (aux argpat e)
in (let _160_203 = (FStar_Syntax_Syntax.is_implicit imp)
in ((_160_204), (_160_203))))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _59_575 -> begin
(let _160_207 = (let _160_206 = (FStar_Syntax_Print.pat_to_string p)
in (let _160_205 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _160_206 _160_205)))
in (failwith _160_207))
end))
in (match_args [] args argpats))))
end
| _59_577 -> begin
(let _160_212 = (let _160_211 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (let _160_210 = (FStar_Syntax_Print.pat_to_string qq)
in (let _160_209 = (let _160_208 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right _160_208 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _160_211 _160_210 _160_209))))
in (failwith _160_212))
end))))
in (match (((p.FStar_Syntax_Syntax.v), (exps))) with
| (FStar_Syntax_Syntax.Pat_disj (ps), _59_581) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(

let ps = (FStar_List.map2 aux ps exps)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj (ps)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p))
end
| (_59_585, (e)::[]) -> begin
(aux p e)
end
| _59_590 -> begin
(failwith "Unexpected number of patterns")
end))))


let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (

let topt = Some (pat.FStar_Syntax_Syntax.ty)
in (

let mk = (fun f -> (FStar_Syntax_Syntax.mk f topt pat.FStar_Syntax_Syntax.p))
in (

let pat_as_arg = (fun _59_598 -> (match (_59_598) with
| (p, i) -> begin
(

let _59_601 = (decorated_pattern_as_term p)
in (match (_59_601) with
| (vars, te) -> begin
(let _160_220 = (let _160_219 = (FStar_Syntax_Syntax.as_implicit i)
in ((te), (_160_219)))
in ((vars), (_160_220)))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_59_603) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _160_221 = (mk (FStar_Syntax_Syntax.Tm_constant (c)))
in (([]), (_160_221)))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(let _160_222 = (mk (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (_160_222)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _59_616 = (let _160_223 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _160_223 FStar_List.unzip))
in (match (_59_616) with
| (vars, args) -> begin
(

let vars = (FStar_List.flatten vars)
in (let _160_227 = (let _160_226 = (let _160_225 = (let _160_224 = (FStar_Syntax_Syntax.fv_to_tm fv)
in ((_160_224), (args)))
in FStar_Syntax_Syntax.Tm_app (_160_225))
in (mk _160_226))
in ((vars), (_160_227))))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
(([]), (e))
end)))))


let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun c -> (

let wp = (match (c.FStar_Syntax_Syntax.effect_args) with
| ((wp, _59_625))::[] -> begin
wp
end
| _59_629 -> begin
(let _160_233 = (let _160_232 = (let _160_231 = (FStar_List.map (fun _59_633 -> (match (_59_633) with
| (x, _59_632) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right _160_231 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str _160_232))
in (failwith _160_233))
end)
in (let _160_234 = (FStar_List.hd c.FStar_Syntax_Syntax.comp_univs)
in ((_160_234), (c.FStar_Syntax_Syntax.result_typ), (wp)))))


let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (

let _59_642 = (destruct_comp c)
in (match (_59_642) with
| (u, _59_640, wp) -> begin
(let _160_253 = (let _160_252 = (let _160_251 = (lift c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _160_251))
in (_160_252)::[])
in {FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _160_253; FStar_Syntax_Syntax.flags = []})
end)))


let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let _59_651 = (let _160_261 = (FStar_TypeChecker_Env.norm_eff_name env l1)
in (let _160_260 = (FStar_TypeChecker_Env.norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _160_261 _160_260)))
in (match (_59_651) with
| (m, _59_648, _59_650) -> begin
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

let _59_663 = (FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (_59_663) with
| (m, lift1, lift2) -> begin
(

let m1 = (lift_comp c1 m lift1)
in (

let m2 = (lift_comp c2 m lift2)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (

let _59_669 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (_59_669) with
| (a, kwp) -> begin
(let _160_275 = (destruct_comp m1)
in (let _160_274 = (destruct_comp m2)
in ((((md), (a), (kwp))), (_160_275), (_160_274))))
end)))))
end)))))


let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid))))


let mk_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result wp flags -> (let _160_296 = (let _160_295 = (let _160_294 = (FStar_Syntax_Syntax.as_arg wp)
in (_160_294)::[])
in {FStar_Syntax_Syntax.comp_univs = (u_result)::[]; FStar_Syntax_Syntax.effect_name = mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = _160_295; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp _160_296)))


let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md -> (mk_comp_l md.FStar_Syntax_Syntax.mname))


let lax_mk_tot_or_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result flags -> if (FStar_Ident.lid_equals mname FStar_Syntax_Const.effect_Tot_lid) then begin
(FStar_Syntax_Syntax.mk_Total' result (Some (u_result)))
end else begin
(mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags)
end)


let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (

let _59_688 = lc
in (let _160_329 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _59_688.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _160_329; FStar_Syntax_Syntax.cflags = _59_688.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _59_690 -> (match (()) with
| () -> begin
(let _160_328 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _160_328))
end))})))


let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _160_332 = (FStar_Syntax_Subst.compress t)
in _160_332.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_59_693) -> begin
true
end
| _59_696 -> begin
false
end))


let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v -> (

let c = if (let _160_339 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation _160_339)) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(

let m = (let _160_340 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must _160_340))
in (

let u_t = (env.FStar_TypeChecker_Env.universe_of env t)
in (

let wp = if (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())) then begin
FStar_Syntax_Syntax.tun
end else begin
(

let _59_704 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_59_704) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (let _160_346 = (let _160_345 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env m m.FStar_Syntax_Syntax.ret_wp)
in (let _160_344 = (let _160_343 = (FStar_Syntax_Syntax.as_arg t)
in (let _160_342 = (let _160_341 = (FStar_Syntax_Syntax.as_arg v)
in (_160_341)::[])
in (_160_343)::_160_342))
in (FStar_Syntax_Syntax.mk_Tm_app _160_345 _160_344 (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _160_346)))
end))
end
in (mk_comp m u_t t wp ((FStar_Syntax_Syntax.RETURN)::[])))))
end
in (

let _59_708 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return"))) then begin
(let _160_349 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _160_348 = (FStar_Syntax_Print.term_to_string v)
in (let _160_347 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _160_349 _160_348 _160_347))))
end else begin
()
end
in c)))


let bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r1 env e1opt lc1 _59_716 -> (match (_59_716) with
| (b, lc2) -> begin
(

let lc1 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1)
in (

let lc2 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2)
in (

let joined_eff = (join_lcomp env lc1 lc2)
in (

let _59_727 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(

let bstr = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _160_362 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (let _160_361 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _160_360 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" _160_362 _160_361 bstr _160_360)))))
end else begin
()
end
in (

let bind_it = (fun _59_730 -> (match (()) with
| () -> begin
if (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())) then begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lc2.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lc2.FStar_Syntax_Syntax.res_typ []))
end else begin
(

let c1 = (lc1.FStar_Syntax_Syntax.comp ())
in (

let c2 = (lc2.FStar_Syntax_Syntax.comp ())
in (

let _59_737 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _160_369 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _160_368 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _160_367 = (FStar_Syntax_Print.comp_to_string c1)
in (let _160_366 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (let _160_365 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" _160_369 _160_368 _160_367 _160_366 _160_365))))))
end else begin
()
end
in (

let try_simplify = (fun _59_740 -> (match (()) with
| () -> begin
(

let aux = (fun _59_742 -> (match (()) with
| () -> begin
if (FStar_Syntax_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some (((c2), ("trivial no binder")))
end
| Some (_59_745) -> begin
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
(let _160_377 = (let _160_376 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in ((_160_376), (reason)))
in Some (_160_377))
end
| _59_755 -> begin
(aux ())
end))
in if ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2)) then begin
(subst_c2 "both total")
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2)) then begin
(let _160_379 = (let _160_378 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((_160_378), ("both gtot")))
in Some (_160_379))
end else begin
(match (((e1opt), (b))) with
| (Some (e), Some (x)) -> begin
if ((FStar_Syntax_Util.is_total_comp c1) && (not ((FStar_Syntax_Syntax.is_null_bv x)))) then begin
(subst_c2 "substituted e")
end else begin
(aux ())
end
end
| _59_762 -> begin
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

let _59_780 = (lift_and_destruct env c1 c2)
in (match (_59_780) with
| ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) -> begin
(

let bs = (match (b) with
| None -> begin
(let _160_380 = (FStar_Syntax_Syntax.null_binder t1)
in (_160_380)::[])
end
| Some (x) -> begin
(let _160_381 = (FStar_Syntax_Syntax.mk_binder x)
in (_160_381)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (

let r1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1))) None r1)
in (

let wp_args = (let _160_393 = (FStar_Syntax_Syntax.as_arg r1)
in (let _160_392 = (let _160_391 = (FStar_Syntax_Syntax.as_arg t1)
in (let _160_390 = (let _160_389 = (FStar_Syntax_Syntax.as_arg t2)
in (let _160_388 = (let _160_387 = (FStar_Syntax_Syntax.as_arg wp1)
in (let _160_386 = (let _160_385 = (let _160_384 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg _160_384))
in (_160_385)::[])
in (_160_387)::_160_386))
in (_160_389)::_160_388))
in (_160_391)::_160_390))
in (_160_393)::_160_392))
in (

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t2))))::[]) kwp)
in (

let wp = (let _160_394 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t1)::(u_t2)::[]) env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _160_394 wp_args None t2.FStar_Syntax_Syntax.pos))
in (

let c = (mk_comp md u_t2 t2 wp [])
in c)))))))
end))
end)))))
end
end))
in {FStar_Syntax_Syntax.eff_name = joined_eff; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it})))))
end))


let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((f), (FStar_Syntax_Syntax.Meta_labeled (((reason), (r), (false))))))) None f.FStar_Syntax_Syntax.pos))


let label_opt : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _160_418 = (FStar_TypeChecker_Env.should_verify env)
in (FStar_All.pipe_left Prims.op_Negation _160_418)) then begin
f
end else begin
(let _160_419 = (reason ())
in (label _160_419 r f))
end
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let _59_808 = g
in (let _160_427 = (let _160_426 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_160_426))
in {FStar_TypeChecker_Env.guard_f = _160_427; FStar_TypeChecker_Env.deferred = _59_808.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _59_808.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _59_808.FStar_TypeChecker_Env.implicits}))
end))


let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| _59_819 -> begin
g2
end))


let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun _59_824 -> (match (()) with
| () -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in if (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())) then begin
c
end else begin
(match (f) with
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

let _59_833 = (destruct_comp c)
in (match (_59_833) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let wp = (let _160_446 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assume_p)
in (let _160_445 = (let _160_444 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _160_443 = (let _160_442 = (FStar_Syntax_Syntax.as_arg f)
in (let _160_441 = (let _160_440 = (FStar_Syntax_Syntax.as_arg wp)
in (_160_440)::[])
in (_160_442)::_160_441))
in (_160_444)::_160_443))
in (FStar_Syntax_Syntax.mk_Tm_app _160_446 _160_445 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md u_res_t res_t wp c.FStar_Syntax_Syntax.flags)))
end)))
end
end)
end)
end))
in (

let _59_836 = lc
in {FStar_Syntax_Syntax.eff_name = _59_836.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _59_836.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _59_836.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))


let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> if (FStar_TypeChecker_Rel.is_trivial g0) then begin
((lc), (g0))
end else begin
(

let _59_843 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _160_466 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _160_465 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _160_466 _160_465)))
end else begin
()
end
in (

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _59_2 -> (match (_59_2) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _59_849 -> begin
[]
end))))
in (

let strengthen = (fun _59_852 -> (match (()) with
| () -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in if (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())) then begin
c
end else begin
(

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

let xret = (let _160_471 = (let _160_470 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _160_470))
in (FStar_Syntax_Util.comp_set_flags _160_471 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (

let lc = (bind e.FStar_Syntax_Syntax.pos env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) ((Some (x)), ((FStar_Syntax_Util.lcomp_of_comp xret))))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (

let _59_862 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _160_473 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _160_472 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _160_473 _160_472)))
end else begin
()
end
in (

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _59_868 = (destruct_comp c)
in (match (_59_868) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let wp = (let _160_482 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assert_p)
in (let _160_481 = (let _160_480 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _160_479 = (let _160_478 = (let _160_475 = (let _160_474 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason _160_474 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _160_475))
in (let _160_477 = (let _160_476 = (FStar_Syntax_Syntax.as_arg wp)
in (_160_476)::[])
in (_160_478)::_160_477))
in (_160_480)::_160_479))
in (FStar_Syntax_Syntax.mk_Tm_app _160_482 _160_481 None wp.FStar_Syntax_Syntax.pos)))
in (

let _59_871 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _160_483 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _160_483))
end else begin
()
end
in (

let c2 = (mk_comp md u_res_t res_t wp flags)
in c2))))
end)))))
end))
end)
end))
in (let _160_487 = (

let _59_874 = lc
in (let _160_486 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _160_485 = if ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _160_484 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _160_484))) then begin
flags
end else begin
[]
end
in {FStar_Syntax_Syntax.eff_name = _160_486; FStar_Syntax_Syntax.res_typ = _59_874.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _160_485; FStar_Syntax_Syntax.comp = strengthen})))
in ((_160_487), ((

let _59_876 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _59_876.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _59_876.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _59_876.FStar_TypeChecker_Env.implicits})))))))
end)


let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env comp res_t -> (

let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let y = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let _59_886 = (let _160_495 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _160_494 = (FStar_Syntax_Syntax.bv_to_name y)
in ((_160_495), (_160_494))))
in (match (_59_886) with
| (xexp, yexp) -> begin
(

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let yret = (let _160_500 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.ret_wp)
in (let _160_499 = (let _160_498 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _160_497 = (let _160_496 = (FStar_Syntax_Syntax.as_arg yexp)
in (_160_496)::[])
in (_160_498)::_160_497))
in (FStar_Syntax_Syntax.mk_Tm_app _160_500 _160_499 None res_t.FStar_Syntax_Syntax.pos)))
in (

let x_eq_y_yret = (let _160_508 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _160_507 = (let _160_506 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _160_505 = (let _160_504 = (let _160_501 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _160_501))
in (let _160_503 = (let _160_502 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_160_502)::[])
in (_160_504)::_160_503))
in (_160_506)::_160_505))
in (FStar_Syntax_Syntax.mk_Tm_app _160_508 _160_507 None res_t.FStar_Syntax_Syntax.pos)))
in (

let forall_y_x_eq_y_yret = (let _160_518 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::(u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _160_517 = (let _160_516 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _160_515 = (let _160_514 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _160_513 = (let _160_512 = (let _160_511 = (let _160_510 = (let _160_509 = (FStar_Syntax_Syntax.mk_binder y)
in (_160_509)::[])
in (FStar_Syntax_Util.abs _160_510 x_eq_y_yret (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _160_511))
in (_160_512)::[])
in (_160_514)::_160_513))
in (_160_516)::_160_515))
in (FStar_Syntax_Syntax.mk_Tm_app _160_518 _160_517 None res_t.FStar_Syntax_Syntax.pos)))
in (

let lc2 = (mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (

let lc = (let _160_519 = (FStar_TypeChecker_Env.get_range env)
in (bind _160_519 env None (FStar_Syntax_Util.lcomp_of_comp comp) ((Some (x)), ((FStar_Syntax_Util.lcomp_of_comp lc2)))))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))


let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (

let joined_eff = (join_lcomp env lcomp_then lcomp_else)
in (

let comp = (fun _59_899 -> (match (()) with
| () -> begin
if (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())) then begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lcomp_then.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lcomp_then.FStar_Syntax_Syntax.res_typ []))
end else begin
(

let _59_917 = (let _160_531 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _160_530 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _160_531 _160_530)))
in (match (_59_917) with
| ((md, _59_903, _59_905), (u_res_t, res_t, wp_then), (_59_912, _59_914, wp_else)) -> begin
(

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _160_551 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (let _160_550 = (let _160_548 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _160_547 = (let _160_546 = (FStar_Syntax_Syntax.as_arg g)
in (let _160_545 = (let _160_544 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _160_543 = (let _160_542 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_160_542)::[])
in (_160_544)::_160_543))
in (_160_546)::_160_545))
in (_160_548)::_160_547))
in (let _160_549 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _160_551 _160_550 None _160_549)))))
in (

let wp = (ifthenelse md res_t guard wp_then wp_else)
in if ((FStar_Options.split_cases ()) > (Prims.parse_int "0")) then begin
(

let comp = (mk_comp md u_res_t res_t wp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(

let wp = (let _160_556 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (let _160_555 = (let _160_554 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _160_553 = (let _160_552 = (FStar_Syntax_Syntax.as_arg wp)
in (_160_552)::[])
in (_160_554)::_160_553))
in (FStar_Syntax_Syntax.mk_Tm_app _160_556 _160_555 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md u_res_t res_t wp []))
end))
end))
end
end))
in (let _160_557 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _160_557; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp}))))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (let _160_563 = (let _160_562 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid _160_562))
in (FStar_Syntax_Syntax.fvar _160_563 FStar_Syntax_Syntax.Delta_constant None)))


let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (FStar_List.fold_left (fun eff _59_936 -> (match (_59_936) with
| (_59_934, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (

let bind_cases = (fun _59_939 -> (match (()) with
| () -> begin
(

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in if (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())) then begin
(lax_mk_tot_or_comp_l eff u_res_t res_t [])
end else begin
(

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _160_593 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (let _160_592 = (let _160_590 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _160_589 = (let _160_588 = (FStar_Syntax_Syntax.as_arg g)
in (let _160_587 = (let _160_586 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _160_585 = (let _160_584 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_160_584)::[])
in (_160_586)::_160_585))
in (_160_588)::_160_587))
in (_160_590)::_160_589))
in (let _160_591 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _160_593 _160_592 None _160_591)))))
in (

let default_case = (

let post_k = (let _160_596 = (let _160_594 = (FStar_Syntax_Syntax.null_binder res_t)
in (_160_594)::[])
in (let _160_595 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _160_596 _160_595)))
in (

let kwp = (let _160_599 = (let _160_597 = (FStar_Syntax_Syntax.null_binder post_k)
in (_160_597)::[])
in (let _160_598 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _160_599 _160_598)))
in (

let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (

let wp = (let _160_605 = (let _160_600 = (FStar_Syntax_Syntax.mk_binder post)
in (_160_600)::[])
in (let _160_604 = (let _160_603 = (let _160_601 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Err.exhaustiveness_check _160_601))
in (let _160_602 = (fvar_const env FStar_Syntax_Const.false_lid)
in (FStar_All.pipe_left _160_603 _160_602)))
in (FStar_Syntax_Util.abs _160_605 _160_604 (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md u_res_t res_t wp []))))))
in (

let comp = (FStar_List.fold_right (fun _59_955 celse -> (match (_59_955) with
| (g, cthen) -> begin
(

let _59_975 = (let _160_608 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _160_608 celse))
in (match (_59_975) with
| ((md, _59_959, _59_961), (_59_964, _59_966, wp_then), (_59_970, _59_972, wp_else)) -> begin
(let _160_609 = (ifthenelse md res_t g wp_then wp_else)
in (mk_comp md u_res_t res_t _160_609 []))
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

let _59_984 = (destruct_comp comp)
in (match (_59_984) with
| (_59_980, _59_982, wp) -> begin
(

let wp = (let _160_614 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (let _160_613 = (let _160_612 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _160_611 = (let _160_610 = (FStar_Syntax_Syntax.as_arg wp)
in (_160_610)::[])
in (_160_612)::_160_611))
in (FStar_Syntax_Syntax.mk_Tm_app _160_614 _160_613 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md u_res_t res_t wp []))
end))))
end)))
end)
end))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))


let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (

let close = (fun _59_990 -> (match (()) with
| () -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in if (FStar_Syntax_Util.is_ml_comp c) then begin
c
end else begin
if (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())) then begin
c
end else begin
(

let close_wp = (fun u_res md res_t bvs wp0 -> (FStar_List.fold_right (fun x wp -> (

let bs = (let _160_635 = (FStar_Syntax_Syntax.mk_binder x)
in (_160_635)::[])
in (

let us = (let _160_637 = (let _160_636 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (_160_636)::[])
in (u_res)::_160_637)
in (

let wp = (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))))))
in (let _160_644 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (let _160_643 = (let _160_642 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _160_641 = (let _160_640 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _160_639 = (let _160_638 = (FStar_Syntax_Syntax.as_arg wp)
in (_160_638)::[])
in (_160_640)::_160_639))
in (_160_642)::_160_641))
in (FStar_Syntax_Syntax.mk_Tm_app _160_644 _160_643 None wp0.FStar_Syntax_Syntax.pos))))))) bvs wp0))
in (

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _59_1007 = (destruct_comp c)
in (match (_59_1007) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let wp = (close_wp u_res_t md res_t bvs wp)
in (mk_comp md u_res_t c.FStar_Syntax_Syntax.result_typ wp c.FStar_Syntax_Syntax.flags)))
end))))
end
end)
end))
in (

let _59_1010 = lc
in {FStar_Syntax_Syntax.eff_name = _59_1010.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _59_1010.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _59_1010.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))


let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (

let refine = (fun _59_1016 -> (match (()) with
| () -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in if ((not ((is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name))) || (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ()))) then begin
c
end else begin
if (FStar_Syntax_Util.is_partial_return c) then begin
c
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c) && (not ((FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)))) then begin
(let _160_655 = (let _160_654 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _160_653 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _160_654 _160_653)))
in (failwith _160_655))
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

let ret = (let _160_657 = (let _160_656 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _160_656 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _160_657))
in (

let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (

let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (

let c = (let _160_659 = (let _160_658 = (bind e.FStar_Syntax_Syntax.pos env None (FStar_Syntax_Util.lcomp_of_comp c) ((Some (x)), (eq_ret)))
in (_160_658.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _160_659 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
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

let _59_1028 = lc
in {FStar_Syntax_Syntax.eff_name = _59_1028.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _59_1028.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))


let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (match ((FStar_TypeChecker_Rel.sub_comp env c c')) with
| None -> begin
(let _160_671 = (let _160_670 = (let _160_669 = (FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation env e c c')
in (let _160_668 = (FStar_TypeChecker_Env.get_range env)
in ((_160_669), (_160_668))))
in FStar_Errors.Error (_160_670))
in (Prims.raise _160_671))
end
| Some (g) -> begin
((e), (c'), (g))
end))


let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match ((let _160_680 = (FStar_Syntax_Subst.compress t)
in _160_680.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_59_1042) -> begin
(match ((let _160_681 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _160_681.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid) -> begin
(

let _59_1046 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (

let b2t = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (

let lc = (let _160_684 = (let _160_683 = (let _160_682 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _160_682))
in ((None), (_160_683)))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) lc _160_684))
in (

let e = (let _160_686 = (let _160_685 = (FStar_Syntax_Syntax.as_arg e)
in (_160_685)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _160_686 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in ((e), (lc))))))
end
| _59_1052 -> begin
((e), (lc))
end)
end
| _59_1054 -> begin
((e), (lc))
end))


let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (

let gopt = if env.FStar_TypeChecker_Env.use_eq then begin
(let _160_695 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in ((_160_695), (false)))
end else begin
(let _160_696 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in ((_160_696), (true)))
end
in (match (gopt) with
| (None, _59_1062) -> begin
(

let _59_1064 = (FStar_TypeChecker_Rel.subtype_fail env e lc.FStar_Syntax_Syntax.res_typ t)
in ((e), ((

let _59_1066 = lc
in {FStar_Syntax_Syntax.eff_name = _59_1066.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _59_1066.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _59_1066.FStar_Syntax_Syntax.comp})), (FStar_TypeChecker_Rel.trivial_guard)))
end
| (Some (g), apply_guard) -> begin
(match ((FStar_TypeChecker_Rel.guard_form g)) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let lc = (

let _59_1073 = lc
in {FStar_Syntax_Syntax.eff_name = _59_1073.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _59_1073.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _59_1073.FStar_Syntax_Syntax.comp})
in ((e), (lc), (g)))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let g = (

let _59_1078 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _59_1078.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _59_1078.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _59_1078.FStar_TypeChecker_Env.implicits})
in (

let strengthen = (fun _59_1082 -> (match (()) with
| () -> begin
if (env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())) then begin
(lc.FStar_Syntax_Syntax.comp ())
end else begin
(

let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (match ((let _160_699 = (FStar_Syntax_Subst.compress f)
in _160_699.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_59_1085, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _59_1091; FStar_Syntax_Syntax.pos = _59_1089; FStar_Syntax_Syntax.vars = _59_1087}, _59_1096) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
(

let lc = (

let _59_1099 = lc
in {FStar_Syntax_Syntax.eff_name = _59_1099.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _59_1099.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _59_1099.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| _59_1103 -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let _59_1105 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _160_703 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _160_702 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _160_701 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _160_700 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _160_703 _160_702 _160_701 _160_700)))))
end else begin
()
end
in (

let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _59_1110 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_59_1110) with
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

let _59_1120 = (destruct_comp ct)
in (match (_59_1120) with
| (u_t, _59_1117, _59_1119) -> begin
(

let wp = (let _160_708 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.ret_wp)
in (let _160_707 = (let _160_706 = (FStar_Syntax_Syntax.as_arg t)
in (let _160_705 = (let _160_704 = (FStar_Syntax_Syntax.as_arg xexp)
in (_160_704)::[])
in (_160_706)::_160_705))
in (FStar_Syntax_Syntax.mk_Tm_app _160_708 _160_707 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)))
in (

let cret = (let _160_709 = (mk_comp md u_t t wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _160_709))
in (

let guard = if apply_guard then begin
(let _160_711 = (let _160_710 = (FStar_Syntax_Syntax.as_arg xexp)
in (_160_710)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _160_711 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end else begin
f
end
in (

let _59_1126 = (let _160_719 = (FStar_All.pipe_left (fun _160_716 -> Some (_160_716)) (FStar_TypeChecker_Err.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _160_718 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _160_717 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _160_719 _160_718 e cret _160_717))))
in (match (_59_1126) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x = (

let _59_1127 = x
in {FStar_Syntax_Syntax.ppname = _59_1127.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_1127.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (

let c = (let _160_721 = (let _160_720 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _160_720))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) _160_721 ((Some (x)), (eq_ret))))
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let _59_1132 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _160_722 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _160_722))
end else begin
()
end
in c))))
end)))))
end))))))
end)))))
end))
end
end))
in (

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _59_3 -> (match (_59_3) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.CPS -> begin
(FStar_Syntax_Syntax.CPS)::[]
end
| _59_1139 -> begin
[]
end))))
in (

let lc = (

let _59_1141 = lc
in (let _160_724 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _160_724; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (

let g = (

let _59_1144 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _59_1144.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _59_1144.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _59_1144.FStar_TypeChecker_Env.implicits})
in ((e), (lc), (g)))))))
end)
end)))


let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _160_736 = (let _160_735 = (let _160_734 = (let _160_733 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _160_733))
in (_160_734)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _160_735 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _160_736))))
in (

let norm = (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env t))
in if (FStar_Syntax_Util.is_tot_or_gtot_comp comp) then begin
((None), ((FStar_Syntax_Util.comp_result comp)))
end else begin
(match (comp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.GTotal (_)) | (FStar_Syntax_Syntax.Total (_)) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
if ((FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Ghost_lid)) then begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| ((req, _59_1172))::((ens, _59_1167))::_59_1164 -> begin
(let _160_742 = (let _160_739 = (norm req)
in Some (_160_739))
in (let _160_741 = (let _160_740 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _160_740))
in ((_160_742), (_160_741))))
end
| _59_1176 -> begin
(let _160_746 = (let _160_745 = (let _160_744 = (let _160_743 = (FStar_Syntax_Print.comp_to_string comp)
in (FStar_Util.format1 "Effect constructor is not fully applied; got %s" _160_743))
in ((_160_744), (comp.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (_160_745))
in (Prims.raise _160_746))
end)
end else begin
(

let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| ((wp, _59_1182))::_59_1179 -> begin
(

let _59_1188 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (_59_1188) with
| (us_r, _59_1187) -> begin
(

let _59_1192 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (_59_1192) with
| (us_e, _59_1191) -> begin
(

let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (

let as_req = (let _160_747 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.as_requires r) FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.mk_Tm_uinst _160_747 us_r))
in (

let as_ens = (let _160_748 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.as_ensures r) FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.mk_Tm_uinst _160_748 us_e))
in (

let req = (let _160_751 = (let _160_750 = (let _160_749 = (FStar_Syntax_Syntax.as_arg wp)
in (_160_749)::[])
in (((ct.FStar_Syntax_Syntax.result_typ), (Some (FStar_Syntax_Syntax.imp_tag))))::_160_750)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _160_751 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let ens = (let _160_754 = (let _160_753 = (let _160_752 = (FStar_Syntax_Syntax.as_arg wp)
in (_160_752)::[])
in (((ct.FStar_Syntax_Syntax.result_typ), (Some (FStar_Syntax_Syntax.imp_tag))))::_160_753)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _160_754 None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _160_758 = (let _160_755 = (norm req)
in Some (_160_755))
in (let _160_757 = (let _160_756 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm _160_756))
in ((_160_758), (_160_757)))))))))
end))
end))
end
| _59_1199 -> begin
(failwith "Impossible")
end))
end
end)
end)))


let maybe_instantiate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let torig = (FStar_Syntax_Subst.compress t)
in if (not (env.FStar_TypeChecker_Env.instantiate_imp)) then begin
((e), (torig), (FStar_TypeChecker_Rel.trivial_guard))
end else begin
(

let number_of_implicits = (fun t -> (

let _59_1209 = (FStar_Syntax_Util.arrow_formals t)
in (match (_59_1209) with
| (formals, _59_1208) -> begin
(

let n_implicits = (match ((FStar_All.pipe_right formals (FStar_Util.prefix_until (fun _59_1213 -> (match (_59_1213) with
| (_59_1211, imp) -> begin
((imp = None) || (imp = Some (FStar_Syntax_Syntax.Equality)))
end))))) with
| None -> begin
(FStar_List.length formals)
end
| Some (implicits, _first_explicit, _rest) -> begin
(FStar_List.length implicits)
end)
in n_implicits)
end)))
in (

let inst_n_binders = (fun t -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
None
end
| Some (expected_t) -> begin
(

let n_expected = (number_of_implicits expected_t)
in (

let n_available = (number_of_implicits t)
in if (n_available < n_expected) then begin
(let _160_776 = (let _160_775 = (let _160_774 = (let _160_772 = (FStar_Util.string_of_int n_expected)
in (let _160_771 = (FStar_Syntax_Print.term_to_string e)
in (let _160_770 = (FStar_Util.string_of_int n_available)
in (FStar_Util.format3 "Expected a term with %s implicit arguments, but %s has only %s" _160_772 _160_771 _160_770))))
in (let _160_773 = (FStar_TypeChecker_Env.get_range env)
in ((_160_774), (_160_773))))
in FStar_Errors.Error (_160_775))
in (Prims.raise _160_776))
end else begin
Some ((n_available - n_expected))
end))
end))
in (

let decr_inst = (fun _59_4 -> (match (_59_4) with
| None -> begin
None
end
| Some (i) -> begin
Some ((i - (Prims.parse_int "1")))
end))
in (match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _59_1239 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_59_1239) with
| (bs, c) -> begin
(

let rec aux = (fun subst inst_n bs -> (match (((inst_n), (bs))) with
| (Some (_160_785), _59_1247) when (_160_785 = (Prims.parse_int "0")) -> begin
(([]), (bs), (subst), (FStar_TypeChecker_Rel.trivial_guard))
end
| (_59_1250, ((x, Some (FStar_Syntax_Syntax.Implicit (dot))))::rest) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let _59_1264 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t)
in (match (_59_1264) with
| (v, _59_1262, g) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (v))))::subst
in (

let _59_1270 = (aux subst (decr_inst inst_n) rest)
in (match (_59_1270) with
| (args, bs, subst, g') -> begin
(let _160_786 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((v), (Some (FStar_Syntax_Syntax.Implicit (dot)))))::args), (bs), (subst), (_160_786)))
end)))
end)))
end
| (_59_1272, bs) -> begin
(([]), (bs), (subst), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (

let _59_1279 = (let _160_787 = (inst_n_binders t)
in (aux [] _160_787 bs))
in (match (_59_1279) with
| (args, bs, subst, guard) -> begin
(match (((args), (bs))) with
| ([], _59_1282) -> begin
((e), (torig), (guard))
end
| (_59_1285, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
((e), (torig), (FStar_TypeChecker_Rel.trivial_guard))
end
| _59_1289 -> begin
(

let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _59_1292 -> begin
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
| _59_1297 -> begin
((e), (t), (FStar_TypeChecker_Rel.trivial_guard))
end))))
end))


let string_of_univs = (fun univs -> (let _160_792 = (let _160_791 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _160_791 (FStar_List.map (fun u -> (let _160_790 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _160_790 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _160_792 (FStar_String.concat ", "))))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(

let s = (let _160_798 = (let _160_797 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _160_797))
in (FStar_All.pipe_right _160_798 FStar_Util.set_elements))
in (

let _59_1303 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _160_800 = (let _160_799 = (FStar_TypeChecker_Env.univ_vars env)
in (string_of_univs _160_799))
in (FStar_Util.print1 "univ_vars in env: %s\n" _160_800))
end else begin
()
end
in (

let r = (let _160_801 = (FStar_TypeChecker_Env.get_range env)
in Some (_160_801))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (

let _59_1308 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _160_806 = (let _160_803 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _160_803))
in (let _160_805 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _160_804 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _160_806 _160_805 _160_804))))
end else begin
()
end
in (

let _59_1310 = (FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))))
in u_name))))))
in u_names))))
end)


let gather_free_univnames : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env t -> (

let ctx_univnames = (FStar_TypeChecker_Env.univnames env)
in (

let tm_univnames = (FStar_Syntax_Free.univnames t)
in (

let univnames = (let _160_811 = (FStar_Util.fifo_set_difference tm_univnames ctx_univnames)
in (FStar_All.pipe_right _160_811 FStar_Util.fifo_set_elements))
in univnames))))


let maybe_set_tk = (fun ts _59_5 -> (match (_59_5) with
| None -> begin
ts
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Syntax.mk t None FStar_Range.dummyRange)
in (

let t = (FStar_Syntax_Subst.close_univ_vars (Prims.fst ts) t)
in (

let _59_1325 = (FStar_ST.op_Colon_Equals (Prims.snd ts).FStar_Syntax_Syntax.tk (Some (t.FStar_Syntax_Syntax.n)))
in ts)))
end))


let check_universe_generalization : FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun explicit_univ_names generalized_univ_names t -> (match (((explicit_univ_names), (generalized_univ_names))) with
| ([], _59_1332) -> begin
generalized_univ_names
end
| (_59_1335, []) -> begin
explicit_univ_names
end
| _59_1339 -> begin
(let _160_823 = (let _160_822 = (let _160_821 = (let _160_820 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "Generalized universe in a term containing explicit universe annotation : " _160_820))
in ((_160_821), (t.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (_160_822))
in (Prims.raise _160_823))
end))


let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Beta)::[]) env t0)
in (

let univnames = (gather_free_univnames env t)
in (

let univs = (FStar_Syntax_Free.univs t)
in (

let _59_1345 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _160_828 = (string_of_univs univs)
in (FStar_Util.print1 "univs to gen : %s\n" _160_828))
end else begin
()
end
in (

let gen = (gen_univs env univs)
in (

let _59_1348 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _160_829 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _160_829))
end else begin
()
end
in (

let univs = (check_universe_generalization univnames gen t0)
in (

let ts = (FStar_Syntax_Subst.close_univ_vars univs t)
in (let _160_830 = (FStar_ST.read t0.FStar_Syntax_Syntax.tk)
in (maybe_set_tk ((univs), (ts)) _160_830)))))))))))


let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> if (let _160_836 = (FStar_Util.for_all (fun _59_1357 -> (match (_59_1357) with
| (_59_1355, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _160_836)) then begin
None
end else begin
(

let norm = (fun c -> (

let _59_1360 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _160_839 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _160_839))
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

let _59_1363 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _160_840 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _160_840))
end else begin
()
end
in c))))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (let _160_843 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _160_843 FStar_Util.set_elements)))
in (

let _59_1379 = (let _160_845 = (FStar_All.pipe_right ecs (FStar_List.map (fun _59_1370 -> (match (_59_1370) with
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
in (FStar_All.pipe_right _160_845 FStar_List.unzip))
in (match (_59_1379) with
| (univs, uvars) -> begin
(

let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (

let gen_univs = (gen_univs env univs)
in (

let _59_1383 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end else begin
()
end
in (

let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _59_1388 -> (match (_59_1388) with
| (uvs, e, c) -> begin
(

let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _59_1391 -> (match (_59_1391) with
| (u, k) -> begin
(match ((FStar_Unionfind.find u)) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
((a), (Some (FStar_Syntax_Syntax.imp_tag)))
end
| FStar_Syntax_Syntax.Fixed (_59_1425) -> begin
(failwith "Unexpected instantiation of mutually recursive uvar")
end
| _59_1428 -> begin
(

let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (

let _59_1432 = (FStar_Syntax_Util.arrow_formals k)
in (match (_59_1432) with
| (bs, kres) -> begin
(

let a = (let _160_851 = (let _160_850 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _160_849 -> Some (_160_849)) _160_850))
in (FStar_Syntax_Syntax.new_bv _160_851 kres))
in (

let t = (let _160_856 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _160_855 = (let _160_854 = (let _160_853 = (let _160_852 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _160_852))
in FStar_Util.Inl (_160_853))
in Some (_160_854))
in (FStar_Syntax_Util.abs bs _160_856 _160_855)))
in (

let _59_1435 = (FStar_Syntax_Util.set_uvar u t)
in ((a), (Some (FStar_Syntax_Syntax.imp_tag))))))
end)))
end)
end))))
in (

let _59_1467 = (match (((tvars), (gen_univs))) with
| ([], []) -> begin
((e), (c))
end
| ([], _59_1443) -> begin
(

let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
in (

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env e)
in ((e), (c))))
end
| _59_1448 -> begin
(

let _59_1451 = ((e), (c))
in (match (_59_1451) with
| (e0, c0) -> begin
(

let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
in (

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Iota))::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env e)
in (

let t = (match ((let _160_857 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _160_857.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(

let _59_1460 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (_59_1460) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| _59_1462 -> begin
(FStar_Syntax_Util.arrow tvars c)
end)
in (

let e' = (FStar_Syntax_Util.abs tvars e (Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp c)))))
in (let _160_858 = (FStar_Syntax_Syntax.mk_Total t)
in ((e'), (_160_858)))))))
end))
end)
in (match (_59_1467) with
| (e, c) -> begin
((gen_univs), (e), (c))
end)))
end))))
in Some (ecs)))))
end)))))
end)


let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> (

let _59_1477 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _160_865 = (let _160_864 = (FStar_List.map (fun _59_1476 -> (match (_59_1476) with
| (lb, _59_1473, _59_1475) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _160_864 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _160_865))
end else begin
()
end
in (

let univnames_lecs = (FStar_List.map (fun _59_1482 -> (match (_59_1482) with
| (l, t, c) -> begin
(gather_free_univnames env t)
end)) lecs)
in (

let generalized_lecs = (match ((let _160_868 = (FStar_All.pipe_right lecs (FStar_List.map (fun _59_1488 -> (match (_59_1488) with
| (_59_1485, e, c) -> begin
((e), (c))
end))))
in (gen env _160_868))) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun _59_1493 -> (match (_59_1493) with
| (l, t, c) -> begin
((l), ([]), (t), (c))
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _59_1501 _59_1505 -> (match (((_59_1501), (_59_1505))) with
| ((l, _59_1498, _59_1500), (us, e, c)) -> begin
(

let _59_1506 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _160_875 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _160_874 = (FStar_Syntax_Print.lbname_to_string l)
in (let _160_873 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (let _160_872 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print4 "(%s) Generalized %s at type %s\n%s\n" _160_875 _160_874 _160_873 _160_872)))))
end else begin
()
end
in ((l), (us), (e), (c)))
end)) lecs ecs)
end)
in (FStar_List.map2 (fun univnames _59_1514 -> (match (_59_1514) with
| (l, generalized_univs, t, c) -> begin
(let _160_878 = (check_universe_generalization univnames generalized_univs t)
in ((l), (_160_878), (t), (c)))
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
(let _160_894 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _160_893 -> Some (_160_893)) _160_894))
end)
end)
in (

let is_var = (fun e -> (match ((let _160_897 = (FStar_Syntax_Subst.compress e)
in _160_897.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (_59_1530) -> begin
true
end
| _59_1533 -> begin
false
end))
in (

let decorate = (fun e t -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((

let _59_1540 = x
in {FStar_Syntax_Syntax.ppname = _59_1540.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_1540.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| _59_1543 -> begin
(

let _59_1544 = e
in (let _160_902 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _59_1544.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _160_902; FStar_Syntax_Syntax.pos = _59_1544.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _59_1544.FStar_Syntax_Syntax.vars}))
end)))
in (

let env = (

let _59_1546 = env
in (let _160_903 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _59_1546.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_1546.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_1546.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_1546.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_1546.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_1546.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_1546.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_1546.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_1546.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_1546.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_1546.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_1546.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_1546.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_1546.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_1546.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _160_903; FStar_TypeChecker_Env.is_iface = _59_1546.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_1546.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_1546.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _59_1546.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_1546.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_1546.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_1546.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_1546.FStar_TypeChecker_Env.qname_and_index}))
in (match ((check env t1 t2)) with
| None -> begin
(let _160_907 = (let _160_906 = (let _160_905 = (FStar_TypeChecker_Err.expected_expression_of_type env t2 e t1)
in (let _160_904 = (FStar_TypeChecker_Env.get_range env)
in ((_160_905), (_160_904))))
in FStar_Errors.Error (_160_906))
in (Prims.raise _160_907))
end
| Some (g) -> begin
(

let _59_1552 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _160_908 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _160_908))
end else begin
()
end
in (let _160_909 = (decorate e t2)
in ((_160_909), (g))))
end)))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (

let discharge = (fun g -> (

let _59_1559 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _160_919 = (discharge g)
in (let _160_918 = (lc.FStar_Syntax_Syntax.comp ())
in ((_160_919), (_160_918))))
end else begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let steps = (FStar_TypeChecker_Normalize.Beta)::[]
in (

let c = (let _160_922 = (let _160_921 = (let _160_920 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (FStar_All.pipe_right _160_920 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right _160_921 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (FStar_All.pipe_right _160_922 (FStar_TypeChecker_Normalize.comp_to_comp_typ env)))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let _59_1569 = (destruct_comp c)
in (match (_59_1569) with
| (u_t, t, wp) -> begin
(

let vc = (let _160_928 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.trivial)
in (let _160_927 = (let _160_925 = (FStar_Syntax_Syntax.as_arg t)
in (let _160_924 = (let _160_923 = (FStar_Syntax_Syntax.as_arg wp)
in (_160_923)::[])
in (_160_925)::_160_924))
in (let _160_926 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk_Tm_app _160_928 _160_927 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _160_926))))
in (

let _59_1571 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _160_929 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _160_929))
end else begin
()
end
in (

let g = (let _160_930 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _160_930))
in (let _160_932 = (discharge g)
in (let _160_931 = (FStar_Syntax_Syntax.mk_Comp c)
in ((_160_932), (_160_931)))))))
end))))))
end)))


let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (

let short_bin_op = (fun f _59_6 -> (match (_59_6) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((fst, _59_1582))::[] -> begin
(f fst)
end
| _59_1586 -> begin
(failwith "Unexpexted args to binary operator")
end))
in (

let op_and_e = (fun e -> (let _160_953 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _160_953 (fun _160_952 -> FStar_TypeChecker_Common.NonTrivial (_160_952)))))
in (

let op_or_e = (fun e -> (let _160_958 = (let _160_956 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _160_956))
in (FStar_All.pipe_right _160_958 (fun _160_957 -> FStar_TypeChecker_Common.NonTrivial (_160_957)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _160_961 -> FStar_TypeChecker_Common.NonTrivial (_160_961))))
in (

let op_or_t = (fun t -> (let _160_965 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _160_965 (fun _160_964 -> FStar_TypeChecker_Common.NonTrivial (_160_964)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _160_968 -> FStar_TypeChecker_Common.NonTrivial (_160_968))))
in (

let short_op_ite = (fun _59_7 -> (match (_59_7) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((guard, _59_1601))::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| (_then)::((guard, _59_1606))::[] -> begin
(let _160_972 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _160_972 (fun _160_971 -> FStar_TypeChecker_Common.NonTrivial (_160_971))))
end
| _59_1611 -> begin
(failwith "Unexpected args to ITE")
end))
in (

let table = (((FStar_Syntax_Const.op_And), ((short_bin_op op_and_e))))::(((FStar_Syntax_Const.op_Or), ((short_bin_op op_or_e))))::(((FStar_Syntax_Const.and_lid), ((short_bin_op op_and_t))))::(((FStar_Syntax_Const.or_lid), ((short_bin_op op_or_t))))::(((FStar_Syntax_Const.imp_lid), ((short_bin_op op_imp_t))))::(((FStar_Syntax_Const.ite_lid), (short_op_ite)))::[]
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((FStar_Util.find_map table (fun _59_1619 -> (match (_59_1619) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _160_1005 = (mk seen_args)
in Some (_160_1005))
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
| _59_1624 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (match ((let _160_1008 = (FStar_Syntax_Util.un_uinst l)
in _160_1008.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| _59_1629 -> begin
false
end))


let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (

let pos = (fun bs -> (match (bs) with
| ((hd, _59_1638))::_59_1635 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| _59_1642 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| ((_59_1646, Some (FStar_Syntax_Syntax.Implicit (_59_1648))))::_59_1644 -> begin
bs
end
| _59_1654 -> begin
(match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
bs
end
| Some (t) -> begin
(match ((let _160_1015 = (FStar_Syntax_Subst.compress t)
in _160_1015.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', _59_1660) -> begin
(match ((FStar_Util.prefix_until (fun _59_8 -> (match (_59_8) with
| (_59_1665, Some (FStar_Syntax_Syntax.Implicit (_59_1667))) -> begin
false
end
| _59_1672 -> begin
true
end)) bs')) with
| None -> begin
bs
end
| Some ([], _59_1676, _59_1678) -> begin
bs
end
| Some (imps, _59_1683, _59_1685) -> begin
if (FStar_All.pipe_right imps (FStar_Util.for_all (fun _59_1691 -> (match (_59_1691) with
| (x, _59_1690) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end)))) then begin
(

let r = (pos bs)
in (

let imps = (FStar_All.pipe_right imps (FStar_List.map (fun _59_1695 -> (match (_59_1695) with
| (x, i) -> begin
(let _160_1019 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in ((_160_1019), (i)))
end))))
in (FStar_List.append imps bs)))
end else begin
bs
end
end)
end
| _59_1698 -> begin
bs
end)
end)
end)))


let maybe_lift : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c1 c2 t -> (

let m1 = (FStar_TypeChecker_Env.norm_eff_name env c1)
in (

let m2 = (FStar_TypeChecker_Env.norm_eff_name env c2)
in if (((FStar_Ident.lid_equals m1 m2) || ((FStar_Syntax_Util.is_pure_effect c1) && (FStar_Syntax_Util.is_ghost_effect c2))) || ((FStar_Syntax_Util.is_pure_effect c2) && (FStar_Syntax_Util.is_ghost_effect c1))) then begin
e
end else begin
(let _160_1030 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m2), (t))))))) _160_1030 e.FStar_Syntax_Syntax.pos))
end)))


let maybe_monadic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c t -> (

let m = (FStar_TypeChecker_Env.norm_eff_name env c)
in if (((is_pure_or_ghost_effect env m) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid)) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid)) then begin
e
end else begin
(let _160_1039 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))) _160_1039 e.FStar_Syntax_Syntax.pos))
end))


let effect_repr_aux = (fun only_reifiable env c u_c -> (match ((let _160_1044 = (FStar_TypeChecker_Env.norm_eff_name env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_TypeChecker_Env.effect_decl_opt env _160_1044))) with
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
| _59_1720 -> begin
(

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _59_1724 = (let _160_1045 = (FStar_List.hd c.FStar_Syntax_Syntax.effect_args)
in ((c.FStar_Syntax_Syntax.result_typ), (_160_1045)))
in (match (_59_1724) with
| (res_typ, wp) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_c)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (let _160_1051 = (let _160_1050 = (let _160_1048 = (let _160_1047 = (let _160_1046 = (FStar_Syntax_Syntax.as_arg res_typ)
in (_160_1046)::(wp)::[])
in ((repr), (_160_1047)))
in FStar_Syntax_Syntax.Tm_app (_160_1048))
in (let _160_1049 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _160_1050 None _160_1049)))
in Some (_160_1051)))
end)))
end)
end
end))


let effect_repr : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term Prims.option = (fun env c u_c -> (effect_repr_aux false env c u_c))


let reify_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term = (fun env c u_c -> (

let no_reify = (fun l -> (let _160_1069 = (let _160_1068 = (let _160_1067 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _160_1066 = (FStar_TypeChecker_Env.get_range env)
in ((_160_1067), (_160_1066))))
in FStar_Errors.Error (_160_1068))
in (Prims.raise _160_1069)))
in (match ((let _160_1070 = (c.FStar_Syntax_Syntax.comp ())
in (effect_repr_aux true env _160_1070 u_c))) with
| None -> begin
(no_reify c.FStar_Syntax_Syntax.eff_name)
end
| Some (tm) -> begin
tm
end)))


let d : Prims.string  ->  Prims.unit = (fun s -> (FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s))


let mk_toplevel_definition : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term) = (fun env lident def -> (

let _59_1743 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _59_1741 = (d (FStar_Ident.text_of_lid lident))
in (let _160_1079 = (FStar_Syntax_Print.term_to_string def)
in (FStar_Util.print2 "Registering top-level definition: %s\n%s\n" (FStar_Ident.text_of_lid lident) _160_1079)))
end else begin
()
end
in (

let fv = (let _160_1080 = (FStar_Syntax_Util.incr_delta_qualifier def)
in (FStar_Syntax_Syntax.lid_as_fv lident _160_1080 None))
in (

let lbname = FStar_Util.Inr (fv)
in (

let lb = ((false), (({FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = def})::[]))
in (

let sig_ctx = FStar_Syntax_Syntax.Sig_let (((lb), (FStar_Range.dummyRange), ((lident)::[]), ((FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)::[]), ([])))
in (let _160_1081 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) None FStar_Range.dummyRange)
in ((sig_ctx), (_160_1081)))))))))


let check_sigelt_quals : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (

let visibility = (fun _59_9 -> (match (_59_9) with
| FStar_Syntax_Syntax.Private -> begin
true
end
| _59_1754 -> begin
false
end))
in (

let reducibility = (fun _59_10 -> (match (_59_10) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) | (FStar_Syntax_Syntax.Visible_default) | (FStar_Syntax_Syntax.Inline_for_extraction) -> begin
true
end
| _59_1763 -> begin
false
end))
in (

let assumption = (fun _59_11 -> (match (_59_11) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.New) -> begin
true
end
| _59_1769 -> begin
false
end))
in (

let reification = (fun _59_12 -> (match (_59_12) with
| (FStar_Syntax_Syntax.Reifiable) | (FStar_Syntax_Syntax.Reflectable (_)) -> begin
true
end
| _59_1777 -> begin
false
end))
in (

let inferred = (fun _59_13 -> (match (_59_13) with
| (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) | (FStar_Syntax_Syntax.ExceptionConstructor) | (FStar_Syntax_Syntax.HasMaskedEffect) | (FStar_Syntax_Syntax.Effect) -> begin
true
end
| _59_1796 -> begin
false
end))
in (

let has_eq = (fun _59_14 -> (match (_59_14) with
| (FStar_Syntax_Syntax.Noeq) | (FStar_Syntax_Syntax.Unopteq) -> begin
true
end
| _59_1802 -> begin
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
| _59_1831 -> begin
true
end))
in (

let quals = (FStar_Syntax_Util.quals_of_sigelt se)
in if (let _160_1110 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _59_15 -> (match (_59_15) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| _59_1836 -> begin
false
end))))
in (FStar_All.pipe_right _160_1110 Prims.op_Negation)) then begin
(

let r = (FStar_Syntax_Util.range_of_sigelt se)
in (

let no_dup_quals = (FStar_Util.remove_dups (fun x y -> (x = y)) quals)
in (

let err' = (fun msg -> (let _160_1118 = (let _160_1117 = (let _160_1116 = (let _160_1115 = (FStar_Syntax_Print.quals_to_string quals)
in (FStar_Util.format2 "The qualifier list \"[%s]\" is not permissible for this element%s" _160_1115 msg))
in ((_160_1116), (r)))
in FStar_Errors.Error (_160_1117))
in (Prims.raise _160_1118)))
in (

let err = (fun msg -> (err' (Prims.strcat ": " msg)))
in (

let err' = (fun _59_1846 -> (match (()) with
| () -> begin
(err' "")
end))
in (

let _59_1847 = if ((FStar_List.length quals) <> (FStar_List.length no_dup_quals)) then begin
(err "duplicate qualifiers")
end else begin
()
end
in (

let _59_1849 = if (not ((FStar_All.pipe_right quals (FStar_List.for_all (quals_combo_ok quals))))) then begin
(err "ill-formed combination")
end else begin
()
end
in (match (se) with
| FStar_Syntax_Syntax.Sig_let ((is_rec, _59_1853), _59_1856, _59_1858, _59_1860, _59_1862) -> begin
(

let _59_1865 = if (is_rec && (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))) then begin
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
| FStar_Syntax_Syntax.Sig_bundle (_59_1869) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.Abstract) || (inferred x)) || (visibility x)) || (has_eq x))))))) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (_59_1873) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some has_eq)) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_assume (_59_1876) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((visibility x) || (x = FStar_Syntax_Syntax.Assumption))))))) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_new_effect (_59_1880) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x))))))) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_59_1884) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x))))))) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_59_1888) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((inferred x) || (visibility x))))))) then begin
(err' ())
end else begin
()
end
end
| _59_1892 -> begin
()
end))))))))
end else begin
()
end)))))))))


let mk_discriminator_and_indexed_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq refine_domain env tc lid uvs inductive_tps indices fields -> (

let p = (FStar_Ident.range_of_lid lid)
in (

let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p))
in (

let projectee = (fun ptyp -> (FStar_Syntax_Syntax.gen_bv "projectee" (Some (p)) ptyp))
in (

let inst_univs = (FStar_List.map (fun u -> FStar_Syntax_Syntax.U_name (u)) uvs)
in (

let tps = inductive_tps
in (

let arg_typ = (

let inst_tc = (let _160_1157 = (let _160_1156 = (let _160_1155 = (let _160_1154 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _160_1154))
in ((_160_1155), (inst_univs)))
in FStar_Syntax_Syntax.Tm_uinst (_160_1156))
in (FStar_Syntax_Syntax.mk _160_1157 None p))
in (

let args = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _59_1914 -> (match (_59_1914) with
| (x, imp) -> begin
(let _160_1159 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_160_1159), (imp)))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app inst_tc args None p)))
in (

let unrefined_arg_binder = (let _160_1160 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder _160_1160))
in (

let arg_binder = if (not (refine_domain)) then begin
unrefined_arg_binder
end else begin
(

let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p)) arg_typ)
in (

let sort = (

let disc_fvar = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range disc_name p) FStar_Syntax_Syntax.Delta_equational None)
in (let _160_1166 = (let _160_1165 = (let _160_1164 = (FStar_Syntax_Syntax.mk_Tm_uinst disc_fvar inst_univs)
in (let _160_1163 = (let _160_1162 = (let _160_1161 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _160_1161))
in (_160_1162)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _160_1164 _160_1163 None p)))
in (FStar_Syntax_Util.b2t _160_1165))
in (FStar_Syntax_Util.refine x _160_1166)))
in (let _160_1167 = (

let _59_1922 = (projectee arg_typ)
in {FStar_Syntax_Syntax.ppname = _59_1922.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_1922.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})
in (FStar_Syntax_Syntax.mk_binder _160_1167)))))
end
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (let _160_1169 = (FStar_List.map (fun _59_1929 -> (match (_59_1929) with
| (x, _59_1928) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end)) tps)
in (FStar_List.append _160_1169 fields))
in (

let imp_binders = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _59_1934 -> (match (_59_1934) with
| (x, _59_1933) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let discriminator_ses = if (fvq <> FStar_Syntax_Syntax.Data_ctor) then begin
[]
end else begin
(

let discriminator_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let no_decl = false
in (

let only_decl = ((let _160_1171 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _160_1171)) || (let _160_1173 = (let _160_1172 = (FStar_TypeChecker_Env.current_module env)
in _160_1172.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _160_1173)))
in (

let quals = (let _160_1177 = (let _160_1176 = if (only_decl && ((FStar_All.pipe_left Prims.op_Negation env.FStar_TypeChecker_Env.is_iface) || env.FStar_TypeChecker_Env.admit)) then begin
(FStar_Syntax_Syntax.Assumption)::[]
end else begin
[]
end
in (let _160_1175 = (FStar_List.filter (fun _59_16 -> (match (_59_16) with
| FStar_Syntax_Syntax.Abstract -> begin
(not (only_decl))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| _59_1943 -> begin
false
end)) iquals)
in (FStar_List.append _160_1176 _160_1175)))
in (FStar_List.append ((FStar_Syntax_Syntax.Discriminator (lid))::if only_decl then begin
(FStar_Syntax_Syntax.Logic)::[]
end else begin
[]
end) _160_1177))
in (

let binders = (FStar_List.append imp_binders ((unrefined_arg_binder)::[]))
in (

let t = (

let bool_typ = (let _160_1179 = (let _160_1178 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _160_1178))
in (FStar_Syntax_Syntax.mk_Total _160_1179))
in (let _160_1180 = (FStar_Syntax_Util.arrow binders bool_typ)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) _160_1180)))
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((discriminator_name), (uvs), (t), (quals), ((FStar_Ident.range_of_lid discriminator_name))))
in (

let _59_1949 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes"))) then begin
(let _160_1181 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a discriminator %s\n" _160_1181))
end else begin
()
end
in if only_decl then begin
(decl)::[]
end else begin
(

let body = if (not (refine_domain)) then begin
FStar_Syntax_Const.exp_true_bool
end else begin
(

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _59_1954 -> (match (_59_1954) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in if (b && (j < ntps)) then begin
(let _160_1187 = (let _160_1186 = (let _160_1185 = (let _160_1184 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in ((_160_1184), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (_160_1185))
in (pos _160_1186))
in ((_160_1187), (b)))
end else begin
(let _160_1190 = (let _160_1189 = (let _160_1188 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_160_1188))
in (pos _160_1189))
in ((_160_1190), (b)))
end)
end))))
in (

let pat_true = (let _160_1194 = (let _160_1193 = (let _160_1192 = (let _160_1191 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in ((_160_1191), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (_160_1192))
in (pos _160_1193))
in ((_160_1194), (None), (FStar_Syntax_Const.exp_true_bool)))
in (

let pat_false = (let _160_1197 = (let _160_1196 = (let _160_1195 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_160_1195))
in (pos _160_1196))
in ((_160_1197), (None), (FStar_Syntax_Const.exp_false_bool)))
in (

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst unrefined_arg_binder))
in (let _160_1203 = (let _160_1202 = (let _160_1201 = (let _160_1200 = (FStar_Syntax_Util.branch pat_true)
in (let _160_1199 = (let _160_1198 = (FStar_Syntax_Util.branch pat_false)
in (_160_1198)::[])
in (_160_1200)::_160_1199))
in ((arg_exp), (_160_1201)))
in FStar_Syntax_Syntax.Tm_match (_160_1202))
in (FStar_Syntax_Syntax.mk _160_1203 None p))))))
end
in (

let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end else begin
FStar_Syntax_Syntax.Delta_equational
end
in (

let imp = (FStar_Syntax_Util.abs binders body None)
in (

let lbtyp = if no_decl then begin
t
end else begin
FStar_Syntax_Syntax.tun
end
in (

let lb = (let _160_1206 = (let _160_1204 = (FStar_Syntax_Syntax.lid_as_fv discriminator_name dd None)
in FStar_Util.Inr (_160_1204))
in (let _160_1205 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = _160_1206; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _160_1205}))
in (

let impl = (let _160_1211 = (let _160_1210 = (let _160_1209 = (let _160_1208 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _160_1208 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_160_1209)::[])
in ((((false), ((lb)::[]))), (p), (_160_1210), (quals), ([])))
in FStar_Syntax_Syntax.Sig_let (_160_1211))
in (

let _59_1967 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes"))) then begin
(let _160_1212 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a discriminator %s\n" _160_1212))
end else begin
()
end
in (decl)::(impl)::[])))))))
end))))))))
end
in (

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst arg_binder))
in (

let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (

let arg = (FStar_Syntax_Util.arg_of_non_null_binder arg_binder)
in (

let subst = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _59_1977 -> (match (_59_1977) with
| (a, _59_1976) -> begin
(

let _59_1981 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (_59_1981) with
| (field_name, _59_1980) -> begin
(

let field_proj_tm = (let _160_1216 = (let _160_1215 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.fv_to_tm _160_1215))
in (FStar_Syntax_Syntax.mk_Tm_uinst _160_1216 inst_univs))
in (

let proj = (FStar_Syntax_Syntax.mk_Tm_app field_proj_tm ((arg)::[]) None p)
in FStar_Syntax_Syntax.NT (((a), (proj)))))
end))
end))))
in (

let projectors_ses = (let _160_1259 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _59_1989 -> (match (_59_1989) with
| (x, _59_1988) -> begin
(

let p = (FStar_Syntax_Syntax.range_of_bv x)
in (

let _59_1994 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (_59_1994) with
| (field_name, _59_1993) -> begin
(

let t = (let _160_1221 = (let _160_1220 = (let _160_1219 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total _160_1219))
in (FStar_Syntax_Util.arrow binders _160_1220))
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) _160_1221))
in (

let only_decl = (((let _160_1222 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _160_1222)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (let _160_1224 = (let _160_1223 = (FStar_TypeChecker_Env.current_module env)
in _160_1223.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _160_1224)))
in (

let no_decl = false
in (

let quals = (fun q -> if only_decl then begin
(let _160_1228 = (FStar_List.filter (fun _59_17 -> (match (_59_17) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| _59_2003 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::_160_1228)
end else begin
q
end)
in (

let quals = (

let iquals = (FStar_All.pipe_right iquals (FStar_List.filter (fun _59_18 -> (match (_59_18) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| _59_2008 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals)))
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), (uvs), (t), (quals), ((FStar_Ident.range_of_lid field_name))))
in (

let _59_2012 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes"))) then begin
(let _160_1230 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a projector %s\n" _160_1230))
end else begin
()
end
in if only_decl then begin
(decl)::[]
end else begin
(

let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _59_2018 -> (match (_59_2018) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in if ((i + ntps) = j) then begin
(let _160_1233 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in ((_160_1233), (b)))
end else begin
if (b && (j < ntps)) then begin
(let _160_1237 = (let _160_1236 = (let _160_1235 = (let _160_1234 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in ((_160_1234), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (_160_1235))
in (pos _160_1236))
in ((_160_1237), (b)))
end else begin
(let _160_1240 = (let _160_1239 = (let _160_1238 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_160_1238))
in (pos _160_1239))
in ((_160_1240), (b)))
end
end)
end))))
in (

let pat = (let _160_1245 = (let _160_1243 = (let _160_1242 = (let _160_1241 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in ((_160_1241), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (_160_1242))
in (pos _160_1243))
in (let _160_1244 = (FStar_Syntax_Syntax.bv_to_name projection)
in ((_160_1245), (None), (_160_1244))))
in (

let body = (let _160_1249 = (let _160_1248 = (let _160_1247 = (let _160_1246 = (FStar_Syntax_Util.branch pat)
in (_160_1246)::[])
in ((arg_exp), (_160_1247)))
in FStar_Syntax_Syntax.Tm_match (_160_1248))
in (FStar_Syntax_Syntax.mk _160_1249 None p))
in (

let imp = (FStar_Syntax_Util.abs binders body None)
in (

let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end else begin
FStar_Syntax_Syntax.Delta_equational
end
in (

let lbtyp = if no_decl then begin
t
end else begin
FStar_Syntax_Syntax.tun
end
in (

let lb = (let _160_1252 = (let _160_1250 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (_160_1250))
in (let _160_1251 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = _160_1252; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _160_1251}))
in (

let impl = (let _160_1257 = (let _160_1256 = (let _160_1255 = (let _160_1254 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _160_1254 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_160_1255)::[])
in ((((false), ((lb)::[]))), (p), (_160_1256), (quals), ([])))
in FStar_Syntax_Syntax.Sig_let (_160_1257))
in (

let _59_2029 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes"))) then begin
(let _160_1258 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a projector %s\n" _160_1258))
end else begin
()
end
in if no_decl then begin
(impl)::[]
end else begin
(decl)::(impl)::[]
end))))))))))
end)))))))
end)))
end))))
in (FStar_All.pipe_right _160_1259 FStar_List.flatten))
in (FStar_List.append discriminator_ses projectors_ses)))))))))))))))))))


let mk_data_operations : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env tcs se -> (match (se) with
| FStar_Syntax_Syntax.Sig_datacon (constr_lid, uvs, t, typ_lid, n_typars, quals, _59_2043, r) when (not ((FStar_Ident.lid_equals constr_lid FStar_Syntax_Const.lexcons_lid))) -> begin
(

let _59_2049 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (_59_2049) with
| (univ_opening, uvs) -> begin
(

let t = (FStar_Syntax_Subst.subst univ_opening t)
in (

let _59_2054 = (FStar_Syntax_Util.arrow_formals t)
in (match (_59_2054) with
| (formals, _59_2053) -> begin
(

let _59_2081 = (

let tps_opt = (FStar_Util.find_map tcs (fun se -> if (let _160_1269 = (FStar_Util.must (FStar_Syntax_Util.lid_of_sigelt se))
in (FStar_Ident.lid_equals typ_lid _160_1269)) then begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_59_2057, uvs', tps, typ0, _59_2062, constrs, _59_2065, _59_2067) -> begin
(

let _59_2070 = ()
in Some (((tps), (typ0), (((FStar_List.length constrs) > (Prims.parse_int "1"))))))
end
| _59_2073 -> begin
(failwith "Impossible")
end)
end else begin
None
end))
in (match (tps_opt) with
| Some (x) -> begin
x
end
| None -> begin
if (FStar_Ident.lid_equals typ_lid FStar_Syntax_Const.exn_lid) then begin
(([]), (FStar_Syntax_Util.ktype0), (true))
end else begin
(Prims.raise (FStar_Errors.Error ((("Unexpected data constructor"), (r)))))
end
end))
in (match (_59_2081) with
| (inductive_tps, typ0, should_refine) -> begin
(

let inductive_tps = (FStar_Syntax_Subst.subst_binders univ_opening inductive_tps)
in (

let typ0 = (FStar_Syntax_Subst.subst univ_opening typ0)
in (

let _59_2087 = (FStar_Syntax_Util.arrow_formals typ0)
in (match (_59_2087) with
| (indices, _59_2086) -> begin
(

let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _59_19 -> (match (_59_19) with
| FStar_Syntax_Syntax.RecordConstructor (_59_2090) -> begin
true
end
| _59_2093 -> begin
false
end)))) then begin
false
end else begin
should_refine
end
in (

let fv_qual = (

let filter_records = (fun _59_20 -> (match (_59_20) with
| FStar_Syntax_Syntax.RecordConstructor (_59_2097, fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((constr_lid), (fns))))
end
| _59_2102 -> begin
None
end))
in (match ((FStar_Util.find_map quals filter_records)) with
| None -> begin
FStar_Syntax_Syntax.Data_ctor
end
| Some (q) -> begin
q
end))
in (

let iquals = if (FStar_List.contains FStar_Syntax_Syntax.Abstract iquals) then begin
(FStar_Syntax_Syntax.Private)::iquals
end else begin
iquals
end
in (

let fields = (

let _59_2111 = (FStar_Util.first_N n_typars formals)
in (match (_59_2111) with
| (imp_tps, fields) -> begin
(

let rename = (FStar_List.map2 (fun _59_2115 _59_2119 -> (match (((_59_2115), (_59_2119))) with
| ((x, _59_2114), (x', _59_2118)) -> begin
(let _160_1276 = (let _160_1275 = (FStar_Syntax_Syntax.bv_to_name x')
in ((x), (_160_1275)))
in FStar_Syntax_Syntax.NT (_160_1276))
end)) imp_tps inductive_tps)
in (FStar_Syntax_Subst.subst_binders rename fields))
end))
in (mk_discriminator_and_indexed_projectors iquals fv_qual refine_domain env typ_lid constr_lid uvs inductive_tps indices fields)))))
end))))
end))
end)))
end))
end
| _59_2123 -> begin
[]
end))




