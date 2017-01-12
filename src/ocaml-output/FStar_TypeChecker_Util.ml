
open Prims

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv Prims.option * FStar_Syntax_Syntax.lcomp)


let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _157_6 = (FStar_TypeChecker_Env.get_range env)
in (let _157_5 = (FStar_TypeChecker_Errors.failed_to_prove_specification errs)
in (FStar_TypeChecker_Errors.report _157_6 _157_5))))


let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _157_9 = (FStar_Syntax_Subst.compress t)
in _157_9.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_58_25) -> begin
true
end
| _58_28 -> begin
false
end))


let t_binders : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env -> (let _157_13 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right _157_13 (FStar_List.filter (fun _58_33 -> (match (_58_33) with
| (x, _58_32) -> begin
(is_type x.FStar_Syntax_Syntax.sort)
end))))))


let new_uvar_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun env k -> (

let bs = if ((FStar_Options.full_context_dependency ()) || (let _157_18 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _157_18))) then begin
(FStar_TypeChecker_Env.all_binders env)
end else begin
(t_binders env)
end
in (let _157_19 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Rel.new_uvar _157_19 bs k))))


let new_uvar : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env k -> (let _157_24 = (new_uvar_aux env k)
in (Prims.fst _157_24)))


let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun _58_1 -> (match (_58_1) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, _58_48); FStar_Syntax_Syntax.tk = _58_45; FStar_Syntax_Syntax.pos = _58_43; FStar_Syntax_Syntax.vars = _58_41} -> begin
uv
end
| _58_53 -> begin
(failwith "Impossible")
end))


let new_implicit_var : Prims.string  ->  FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.uvar * FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t) = (fun reason r env k -> (match ((FStar_Syntax_Util.destruct k FStar_Syntax_Const.range_of_lid)) with
| Some ((_58_63)::((tm, _58_60))::[]) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))) None tm.FStar_Syntax_Syntax.pos)
in ((t), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
end
| _58_68 -> begin
(

let _58_71 = (new_uvar_aux env k)
in (match (_58_71) with
| (t, u) -> begin
(

let g = (

let _58_72 = FStar_TypeChecker_Rel.trivial_guard
in (let _157_37 = (let _157_36 = (let _157_35 = (as_uvar u)
in ((reason), (env), (_157_35), (t), (k), (r)))
in (_157_36)::[])
in {FStar_TypeChecker_Env.guard_f = _58_72.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _58_72.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_72.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _157_37}))
in (let _157_40 = (let _157_39 = (let _157_38 = (as_uvar u)
in ((_157_38), (r)))
in (_157_39)::[])
in ((t), (_157_40), (g))))
end))
end))


let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun r t -> (

let uvs = (FStar_Syntax_Free.uvars t)
in if (not ((FStar_Util.set_is_empty uvs))) then begin
(

let us = (let _157_47 = (let _157_46 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun _58_81 -> (match (_58_81) with
| (x, _58_80) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) _157_46))
in (FStar_All.pipe_right _157_47 (FStar_String.concat ", ")))
in (

let _58_83 = (FStar_Options.push ())
in (

let _58_85 = (FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool (false)))
in (

let _58_87 = (FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)))
in (

let _58_89 = (let _157_49 = (let _157_48 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us _157_48))
in (FStar_TypeChecker_Errors.report r _157_49))
in (FStar_Options.pop ()))))))
end else begin
()
end))


let force_sort' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' = (fun s -> (match ((FStar_ST.read s.FStar_Syntax_Syntax.tk)) with
| None -> begin
(let _157_54 = (let _157_53 = (FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos)
in (let _157_52 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s" _157_53 _157_52)))
in (failwith _157_54))
end
| Some (tk) -> begin
tk
end))


let force_sort = (fun s -> (let _157_56 = (force_sort' s)
in (FStar_Syntax_Syntax.mk _157_56 None s.FStar_Syntax_Syntax.pos)))


let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env _58_104 -> (match (_58_104) with
| {FStar_Syntax_Syntax.lbname = _58_103; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _58_99; FStar_Syntax_Syntax.lbdef = e} -> begin
(

let rng = t.FStar_Syntax_Syntax.pos
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _58_108 = if (univ_vars <> []) then begin
(failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let mk_binder = (fun scope a -> (match ((let _157_65 = (FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort)
in _157_65.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _58_118 = (FStar_Syntax_Util.type_u ())
in (match (_58_118) with
| (k, _58_117) -> begin
(

let t = (let _157_66 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right _157_66 Prims.fst))
in (((

let _58_120 = a
in {FStar_Syntax_Syntax.ppname = _58_120.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_120.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (false)))
end))
end
| _58_123 -> begin
((a), (true))
end))
in (

let rec aux = (fun must_check_ty vars e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, _58_131) -> begin
(aux must_check_ty vars e)
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _58_137) -> begin
((t), (true))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _58_143) -> begin
(

let _58_162 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _58_149 _58_152 -> (match (((_58_149), (_58_152))) with
| ((scope, bs, must_check_ty), (a, imp)) -> begin
(

let _58_155 = if must_check_ty then begin
((a), (true))
end else begin
(mk_binder scope a)
end
in (match (_58_155) with
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
in (match (_58_162) with
| (scope, bs, must_check_ty) -> begin
(

let _58_165 = (aux must_check_ty scope body)
in (match (_58_165) with
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

let _58_172 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_77 = (FStar_Range.string_of_range r)
in (let _157_76 = (FStar_Syntax_Print.term_to_string t)
in (let _157_75 = (FStar_Util.string_of_bool must_check_ty)
in (FStar_Util.print3 "(%s) Using type %s .... must check = %s\n" _157_77 _157_76 _157_75))))
end else begin
()
end
in ((FStar_Util.Inl (t)), (must_check_ty)))))
end))
end))
end
| _58_175 -> begin
if must_check_ty then begin
((FStar_Util.Inl (FStar_Syntax_Syntax.tun)), (true))
end else begin
(let _157_80 = (let _157_79 = (let _157_78 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _157_78 Prims.fst))
in FStar_Util.Inl (_157_79))
in ((_157_80), (false)))
end
end)))
in (

let _58_178 = (let _157_81 = (t_binders env)
in (aux false _157_81 e))
in (match (_58_178) with
| (t, b) -> begin
(

let t = (match (t) with
| FStar_Util.Inr (c) -> begin
(let _157_85 = (let _157_84 = (let _157_83 = (let _157_82 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" _157_82))
in ((_157_83), (rng)))
in FStar_Syntax_Syntax.Error (_157_84))
in (Prims.raise _157_85))
end
| FStar_Util.Inl (t) -> begin
t
end)
in (([]), (t), (b)))
end))))))
end
| _58_185 -> begin
(

let _58_188 = (FStar_Syntax_Subst.open_univ_vars univ_vars t)
in (match (_58_188) with
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
| FStar_Syntax_Syntax.Pat_dot_term (x, _58_201) -> begin
(

let _58_207 = (FStar_Syntax_Util.type_u ())
in (match (_58_207) with
| (k, _58_206) -> begin
(

let t = (new_uvar env k)
in (

let x = (

let _58_209 = x
in {FStar_Syntax_Syntax.ppname = _58_209.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_209.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let _58_214 = (let _157_98 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _157_98 t))
in (match (_58_214) with
| (e, u) -> begin
(

let p = (

let _58_215 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (e))); FStar_Syntax_Syntax.ty = _58_215.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _58_215.FStar_Syntax_Syntax.p})
in (([]), ([]), ([]), (env), (e), (p)))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let _58_223 = (FStar_Syntax_Util.type_u ())
in (match (_58_223) with
| (t, _58_222) -> begin
(

let x = (

let _58_224 = x
in (let _157_99 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _58_224.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_224.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _157_99}))
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

let _58_234 = (FStar_Syntax_Util.type_u ())
in (match (_58_234) with
| (t, _58_233) -> begin
(

let x = (

let _58_235 = x
in (let _157_100 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _58_235.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_235.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _157_100}))
in (

let env = (FStar_TypeChecker_Env.push_bv env x)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in (((x)::[]), ((x)::[]), ([]), (env), (e), (p)))))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _58_268 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _58_250 _58_253 -> (match (((_58_250), (_58_253))) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(

let _58_260 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_58_260) with
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
in (match (_58_268) with
| (b, a, w, env, args, pats) -> begin
(

let e = (let _157_107 = (let _157_106 = (let _157_105 = (let _157_104 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (let _157_103 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app _157_104 _157_103 None p.FStar_Syntax_Syntax.p)))
in ((_157_105), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))
in FStar_Syntax_Syntax.Tm_meta (_157_106))
in (FStar_Syntax_Syntax.mk _157_107 None p.FStar_Syntax_Syntax.p))
in (let _157_110 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _157_109 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _157_108 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in ((_157_110), (_157_109), (_157_108), (env), (e), ((

let _58_270 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _58_270.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _58_270.FStar_Syntax_Syntax.p})))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (_58_273) -> begin
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

let pats = (FStar_List.map (fun _58_288 -> (match (_58_288) with
| (p, imp) -> begin
(let _157_122 = (elaborate_pat env p)
in ((_157_122), (imp)))
end)) pats)
in (

let _58_293 = (FStar_TypeChecker_Env.lookup_datacon env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_58_293) with
| (_58_291, t) -> begin
(

let _58_297 = (FStar_Syntax_Util.arrow_formals t)
in (match (_58_297) with
| (f, _58_296) -> begin
(

let rec aux = (fun formals pats -> (match (((formals), (pats))) with
| ([], []) -> begin
[]
end
| ([], (_58_308)::_58_306) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Too many pattern arguments"), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))))
end
| ((_58_314)::_58_312, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun _58_320 -> (match (_58_320) with
| (t, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(

let a = (let _157_129 = (let _157_128 = (FStar_Syntax_Syntax.range_of_bv t)
in Some (_157_128))
in (FStar_Syntax_Syntax.new_bv _157_129 FStar_Syntax_Syntax.tun))
in (

let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (let _157_130 = (maybe_dot inaccessible a r)
in ((_157_130), (true)))))
end
| _58_327 -> begin
(let _157_134 = (let _157_133 = (let _157_132 = (let _157_131 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _157_131))
in ((_157_132), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))
in FStar_Syntax_Syntax.Error (_157_133))
in (Prims.raise _157_134))
end)
end))))
end
| ((f)::formals', ((p, p_imp))::pats') -> begin
(match (f) with
| (_58_338, Some (FStar_Syntax_Syntax.Implicit (_58_340))) when p_imp -> begin
(let _157_135 = (aux formals' pats')
in (((p), (true)))::_157_135)
end
| (_58_345, Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(

let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let p = (maybe_dot inaccessible a (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
in (let _157_136 = (aux formals' pats)
in (((p), (true)))::_157_136)))
end
| (_58_353, imp) -> begin
(let _157_139 = (let _157_137 = (FStar_Syntax_Syntax.is_implicit imp)
in ((p), (_157_137)))
in (let _157_138 = (aux formals' pats')
in (_157_139)::_157_138))
end)
end))
in (

let _58_356 = p
in (let _157_142 = (let _157_141 = (let _157_140 = (aux f pats)
in ((fv), (_157_140)))
in FStar_Syntax_Syntax.Pat_cons (_157_141))
in {FStar_Syntax_Syntax.v = _157_142; FStar_Syntax_Syntax.ty = _58_356.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _58_356.FStar_Syntax_Syntax.p})))
end))
end)))
end
| _58_359 -> begin
p
end)))
in (

let one_pat = (fun allow_wc_dependence env p -> (

let p = (elaborate_pat env p)
in (

let _58_371 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_58_371) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))) with
| Some (x) -> begin
(let _157_151 = (let _157_150 = (let _157_149 = (FStar_TypeChecker_Errors.nonlinear_pattern_variable x)
in ((_157_149), (p.FStar_Syntax_Syntax.p)))
in FStar_Syntax_Syntax.Error (_157_150))
in (Prims.raise _157_151))
end
| _58_375 -> begin
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

let _58_391 = (one_pat false env q)
in (match (_58_391) with
| (b, a, _58_388, te, q) -> begin
(

let _58_406 = (FStar_List.fold_right (fun p _58_396 -> (match (_58_396) with
| (w, args, pats) -> begin
(

let _58_402 = (one_pat false env p)
in (match (_58_402) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv FStar_Syntax_Syntax.bv_eq a a'))) then begin
(let _157_161 = (let _157_160 = (let _157_159 = (FStar_TypeChecker_Errors.disjunctive_pattern_vars a a')
in (let _157_158 = (FStar_TypeChecker_Env.get_range env)
in ((_157_159), (_157_158))))
in FStar_Syntax_Syntax.Error (_157_160))
in (Prims.raise _157_161))
end else begin
(let _157_163 = (let _157_162 = (FStar_Syntax_Syntax.as_arg arg)
in (_157_162)::args)
in (((FStar_List.append w' w)), (_157_163), ((p)::pats)))
end
end))
end)) pats (([]), ([]), ([])))
in (match (_58_406) with
| (w, args, pats) -> begin
(let _157_165 = (let _157_164 = (FStar_Syntax_Syntax.as_arg te)
in (_157_164)::args)
in (((FStar_List.append b w)), (_157_165), ((

let _58_407 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((q)::pats); FStar_Syntax_Syntax.ty = _58_407.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _58_407.FStar_Syntax_Syntax.p}))))
end))
end))
end
| _58_410 -> begin
(

let _58_418 = (one_pat true env p)
in (match (_58_418) with
| (b, _58_413, _58_415, arg, p) -> begin
(let _157_167 = (let _157_166 = (FStar_Syntax_Syntax.as_arg arg)
in (_157_166)::[])
in ((b), (_157_167), (p)))
end))
end))
in (

let _58_422 = (top_level_pat_as_args env p)
in (match (_58_422) with
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
| (_58_436, FStar_Syntax_Syntax.Tm_uinst (e, _58_439)) -> begin
(aux p e)
end
| (FStar_Syntax_Syntax.Pat_constant (_58_444), FStar_Syntax_Syntax.Tm_constant (_58_447)) -> begin
(let _157_182 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v _157_182))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(

let _58_455 = if (not ((FStar_Syntax_Syntax.bv_eq x y))) then begin
(let _157_185 = (let _157_184 = (FStar_Syntax_Print.bv_to_string x)
in (let _157_183 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _157_184 _157_183)))
in (failwith _157_185))
end else begin
()
end
in (

let _58_457 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _157_187 = (FStar_Syntax_Print.bv_to_string x)
in (let _157_186 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _157_187 _157_186)))
end else begin
()
end
in (

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x = (

let _58_460 = x
in {FStar_Syntax_Syntax.ppname = _58_460.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_460.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x)) s.FStar_Syntax_Syntax.n)))))
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(

let _58_468 = if (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation) then begin
(let _157_190 = (let _157_189 = (FStar_Syntax_Print.bv_to_string x)
in (let _157_188 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _157_189 _157_188)))
in (failwith _157_190))
end else begin
()
end
in (

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x = (

let _58_471 = x
in {FStar_Syntax_Syntax.ppname = _58_471.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_471.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x)) s.FStar_Syntax_Syntax.n))))
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _58_476), _58_480) -> begin
(

let s = (force_sort e)
in (

let x = (

let _58_483 = x
in {FStar_Syntax_Syntax.ppname = _58_483.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_483.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term (((x), (e)))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
(

let _58_493 = if (not ((FStar_Syntax_Syntax.fv_eq fv fv'))) then begin
(let _157_191 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith _157_191))
end else begin
()
end
in (let _157_192 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv'), ([])))) _157_192)))
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
(

let _58_536 = if (let _157_193 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right _157_193 Prims.op_Negation)) then begin
(let _157_194 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith _157_194))
end else begin
()
end
in (

let fv = fv'
in (

let rec match_args = (fun matched_pats args argpats -> (match (((args), (argpats))) with
| ([], []) -> begin
(let _157_201 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev matched_pats))))) _157_201))
end
| ((arg)::args, ((argpat, _58_552))::argpats) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e, Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (_58_562)) -> begin
(

let x = (let _157_202 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _157_202))
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e)))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args argpats)))
end
| ((e, imp), _58_571) -> begin
(

let pat = (let _157_204 = (aux argpat e)
in (let _157_203 = (FStar_Syntax_Syntax.is_implicit imp)
in ((_157_204), (_157_203))))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _58_575 -> begin
(let _157_207 = (let _157_206 = (FStar_Syntax_Print.pat_to_string p)
in (let _157_205 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _157_206 _157_205)))
in (failwith _157_207))
end))
in (match_args [] args argpats))))
end
| _58_577 -> begin
(let _157_212 = (let _157_211 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (let _157_210 = (FStar_Syntax_Print.pat_to_string qq)
in (let _157_209 = (let _157_208 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right _157_208 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _157_211 _157_210 _157_209))))
in (failwith _157_212))
end))))
in (match (((p.FStar_Syntax_Syntax.v), (exps))) with
| (FStar_Syntax_Syntax.Pat_disj (ps), _58_581) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(

let ps = (FStar_List.map2 aux ps exps)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj (ps)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p))
end
| (_58_585, (e)::[]) -> begin
(aux p e)
end
| _58_590 -> begin
(failwith "Unexpected number of patterns")
end))))


let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (

let topt = Some (pat.FStar_Syntax_Syntax.ty)
in (

let mk = (fun f -> (FStar_Syntax_Syntax.mk f topt pat.FStar_Syntax_Syntax.p))
in (

let pat_as_arg = (fun _58_598 -> (match (_58_598) with
| (p, i) -> begin
(

let _58_601 = (decorated_pattern_as_term p)
in (match (_58_601) with
| (vars, te) -> begin
(let _157_220 = (let _157_219 = (FStar_Syntax_Syntax.as_implicit i)
in ((te), (_157_219)))
in ((vars), (_157_220)))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_58_603) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _157_221 = (mk (FStar_Syntax_Syntax.Tm_constant (c)))
in (([]), (_157_221)))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(let _157_222 = (mk (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (_157_222)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _58_616 = (let _157_223 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _157_223 FStar_List.unzip))
in (match (_58_616) with
| (vars, args) -> begin
(

let vars = (FStar_List.flatten vars)
in (let _157_227 = (let _157_226 = (let _157_225 = (let _157_224 = (FStar_Syntax_Syntax.fv_to_tm fv)
in ((_157_224), (args)))
in FStar_Syntax_Syntax.Tm_app (_157_225))
in (mk _157_226))
in ((vars), (_157_227))))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
(([]), (e))
end)))))


let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun c -> (

let wp = (match (c.FStar_Syntax_Syntax.effect_args) with
| ((wp, _58_625))::[] -> begin
wp
end
| _58_629 -> begin
(let _157_233 = (let _157_232 = (let _157_231 = (FStar_List.map (fun _58_633 -> (match (_58_633) with
| (x, _58_632) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right _157_231 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str _157_232))
in (failwith _157_233))
end)
in (let _157_234 = (FStar_List.hd c.FStar_Syntax_Syntax.comp_univs)
in ((_157_234), (c.FStar_Syntax_Syntax.result_typ), (wp)))))


let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (

let _58_642 = (destruct_comp c)
in (match (_58_642) with
| (u, _58_640, wp) -> begin
(let _157_253 = (let _157_252 = (let _157_251 = (lift c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _157_251))
in (_157_252)::[])
in {FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _157_253; FStar_Syntax_Syntax.flags = []})
end)))


let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let _58_651 = (let _157_261 = (FStar_TypeChecker_Env.norm_eff_name env l1)
in (let _157_260 = (FStar_TypeChecker_Env.norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _157_261 _157_260)))
in (match (_58_651) with
| (m, _58_648, _58_650) -> begin
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

let _58_663 = (FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (_58_663) with
| (m, lift1, lift2) -> begin
(

let m1 = (lift_comp c1 m lift1)
in (

let m2 = (lift_comp c2 m lift2)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (

let _58_669 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (_58_669) with
| (a, kwp) -> begin
(let _157_275 = (destruct_comp m1)
in (let _157_274 = (destruct_comp m2)
in ((((md), (a), (kwp))), (_157_275), (_157_274))))
end)))))
end)))))


let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid))))


let mk_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result wp flags -> (let _157_296 = (let _157_295 = (let _157_294 = (FStar_Syntax_Syntax.as_arg wp)
in (_157_294)::[])
in {FStar_Syntax_Syntax.comp_univs = (u_result)::[]; FStar_Syntax_Syntax.effect_name = mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = _157_295; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp _157_296)))


let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md -> (mk_comp_l md.FStar_Syntax_Syntax.mname))


let lax_mk_tot_or_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result flags -> if (FStar_Ident.lid_equals mname FStar_Syntax_Const.effect_Tot_lid) then begin
(FStar_Syntax_Syntax.mk_Total' result (Some (u_result)))
end else begin
(mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags)
end)


let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (

let _58_688 = lc
in (let _157_329 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _58_688.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _157_329; FStar_Syntax_Syntax.cflags = _58_688.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _58_690 -> (match (()) with
| () -> begin
(let _157_328 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _157_328))
end))})))


let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _157_332 = (FStar_Syntax_Subst.compress t)
in _157_332.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_693) -> begin
true
end
| _58_696 -> begin
false
end))


let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v -> (

let c = if (let _157_339 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation _157_339)) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(

let m = (let _157_340 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must _157_340))
in (

let u_t = (env.FStar_TypeChecker_Env.universe_of env t)
in (

let wp = if (env.FStar_TypeChecker_Env.lax && false) then begin
FStar_Syntax_Syntax.tun
end else begin
(

let _58_704 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_58_704) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (let _157_346 = (let _157_345 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env m m.FStar_Syntax_Syntax.ret_wp)
in (let _157_344 = (let _157_343 = (FStar_Syntax_Syntax.as_arg t)
in (let _157_342 = (let _157_341 = (FStar_Syntax_Syntax.as_arg v)
in (_157_341)::[])
in (_157_343)::_157_342))
in (FStar_Syntax_Syntax.mk_Tm_app _157_345 _157_344 (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _157_346)))
end))
end
in (mk_comp m u_t t wp ((FStar_Syntax_Syntax.RETURN)::[])))))
end
in (

let _58_708 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return"))) then begin
(let _157_349 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _157_348 = (FStar_Syntax_Print.term_to_string v)
in (let _157_347 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _157_349 _157_348 _157_347))))
end else begin
()
end
in c)))


let bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r1 env e1opt lc1 _58_716 -> (match (_58_716) with
| (b, lc2) -> begin
(

let lc1 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1)
in (

let lc2 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2)
in (

let joined_eff = (join_lcomp env lc1 lc2)
in (

let _58_727 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(

let bstr = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _157_362 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (let _157_361 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _157_360 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" _157_362 _157_361 bstr _157_360)))))
end else begin
()
end
in (

let bind_it = (fun _58_730 -> (match (()) with
| () -> begin
if (env.FStar_TypeChecker_Env.lax && false) then begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lc2.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lc2.FStar_Syntax_Syntax.res_typ []))
end else begin
(

let c1 = (lc1.FStar_Syntax_Syntax.comp ())
in (

let c2 = (lc2.FStar_Syntax_Syntax.comp ())
in (

let _58_737 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _157_369 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _157_368 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _157_367 = (FStar_Syntax_Print.comp_to_string c1)
in (let _157_366 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (let _157_365 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" _157_369 _157_368 _157_367 _157_366 _157_365))))))
end else begin
()
end
in (

let try_simplify = (fun _58_740 -> (match (()) with
| () -> begin
(

let aux = (fun _58_742 -> (match (()) with
| () -> begin
if (FStar_Syntax_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some (((c2), ("trivial no binder")))
end
| Some (_58_745) -> begin
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
(let _157_377 = (let _157_376 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in ((_157_376), (reason)))
in Some (_157_377))
end
| _58_755 -> begin
(aux ())
end))
in if ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2)) then begin
(subst_c2 "both total")
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2)) then begin
(let _157_379 = (let _157_378 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((_157_378), ("both gtot")))
in Some (_157_379))
end else begin
(match (((e1opt), (b))) with
| (Some (e), Some (x)) -> begin
if ((FStar_Syntax_Util.is_total_comp c1) && (not ((FStar_Syntax_Syntax.is_null_bv x)))) then begin
(subst_c2 "substituted e")
end else begin
(aux ())
end
end
| _58_762 -> begin
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

let _58_780 = (lift_and_destruct env c1 c2)
in (match (_58_780) with
| ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) -> begin
(

let bs = (match (b) with
| None -> begin
(let _157_380 = (FStar_Syntax_Syntax.null_binder t1)
in (_157_380)::[])
end
| Some (x) -> begin
(let _157_381 = (FStar_Syntax_Syntax.mk_binder x)
in (_157_381)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (

let r1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1))) None r1)
in (

let wp_args = (let _157_393 = (FStar_Syntax_Syntax.as_arg r1)
in (let _157_392 = (let _157_391 = (FStar_Syntax_Syntax.as_arg t1)
in (let _157_390 = (let _157_389 = (FStar_Syntax_Syntax.as_arg t2)
in (let _157_388 = (let _157_387 = (FStar_Syntax_Syntax.as_arg wp1)
in (let _157_386 = (let _157_385 = (let _157_384 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg _157_384))
in (_157_385)::[])
in (_157_387)::_157_386))
in (_157_389)::_157_388))
in (_157_391)::_157_390))
in (_157_393)::_157_392))
in (

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t2))))::[]) kwp)
in (

let wp = (let _157_394 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t1)::(u_t2)::[]) env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _157_394 wp_args None t2.FStar_Syntax_Syntax.pos))
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
if (let _157_418 = (FStar_TypeChecker_Env.should_verify env)
in (FStar_All.pipe_left Prims.op_Negation _157_418)) then begin
f
end else begin
(let _157_419 = (reason ())
in (label _157_419 r f))
end
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let _58_808 = g
in (let _157_427 = (let _157_426 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_157_426))
in {FStar_TypeChecker_Env.guard_f = _157_427; FStar_TypeChecker_Env.deferred = _58_808.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_808.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_808.FStar_TypeChecker_Env.implicits}))
end))


let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| _58_819 -> begin
g2
end))


let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun _58_824 -> (match (()) with
| () -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in if (env.FStar_TypeChecker_Env.lax && false) then begin
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

let _58_833 = (destruct_comp c)
in (match (_58_833) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let wp = (let _157_446 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assume_p)
in (let _157_445 = (let _157_444 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _157_443 = (let _157_442 = (FStar_Syntax_Syntax.as_arg f)
in (let _157_441 = (let _157_440 = (FStar_Syntax_Syntax.as_arg wp)
in (_157_440)::[])
in (_157_442)::_157_441))
in (_157_444)::_157_443))
in (FStar_Syntax_Syntax.mk_Tm_app _157_446 _157_445 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md u_res_t res_t wp c.FStar_Syntax_Syntax.flags)))
end)))
end
end)
end)
end))
in (

let _58_836 = lc
in {FStar_Syntax_Syntax.eff_name = _58_836.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _58_836.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _58_836.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))


let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> if (FStar_TypeChecker_Rel.is_trivial g0) then begin
((lc), (g0))
end else begin
(

let _58_843 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _157_466 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _157_465 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _157_466 _157_465)))
end else begin
()
end
in (

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _58_2 -> (match (_58_2) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _58_849 -> begin
[]
end))))
in (

let strengthen = (fun _58_852 -> (match (()) with
| () -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in if (env.FStar_TypeChecker_Env.lax && false) then begin
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

let xret = (let _157_471 = (let _157_470 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _157_470))
in (FStar_Syntax_Util.comp_set_flags _157_471 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (

let lc = (bind e.FStar_Syntax_Syntax.pos env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) ((Some (x)), ((FStar_Syntax_Util.lcomp_of_comp xret))))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (

let _58_862 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _157_473 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _157_472 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _157_473 _157_472)))
end else begin
()
end
in (

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _58_868 = (destruct_comp c)
in (match (_58_868) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let wp = (let _157_482 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assert_p)
in (let _157_481 = (let _157_480 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _157_479 = (let _157_478 = (let _157_475 = (let _157_474 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason _157_474 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _157_475))
in (let _157_477 = (let _157_476 = (FStar_Syntax_Syntax.as_arg wp)
in (_157_476)::[])
in (_157_478)::_157_477))
in (_157_480)::_157_479))
in (FStar_Syntax_Syntax.mk_Tm_app _157_482 _157_481 None wp.FStar_Syntax_Syntax.pos)))
in (

let _58_871 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _157_483 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _157_483))
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
in (let _157_487 = (

let _58_874 = lc
in (let _157_486 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _157_485 = if ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _157_484 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _157_484))) then begin
flags
end else begin
[]
end
in {FStar_Syntax_Syntax.eff_name = _157_486; FStar_Syntax_Syntax.res_typ = _58_874.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _157_485; FStar_Syntax_Syntax.comp = strengthen})))
in ((_157_487), ((

let _58_876 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_876.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_876.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_876.FStar_TypeChecker_Env.implicits})))))))
end)


let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env comp res_t -> (

let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let y = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let _58_886 = (let _157_495 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _157_494 = (FStar_Syntax_Syntax.bv_to_name y)
in ((_157_495), (_157_494))))
in (match (_58_886) with
| (xexp, yexp) -> begin
(

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let yret = (let _157_500 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.ret_wp)
in (let _157_499 = (let _157_498 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _157_497 = (let _157_496 = (FStar_Syntax_Syntax.as_arg yexp)
in (_157_496)::[])
in (_157_498)::_157_497))
in (FStar_Syntax_Syntax.mk_Tm_app _157_500 _157_499 None res_t.FStar_Syntax_Syntax.pos)))
in (

let x_eq_y_yret = (let _157_508 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _157_507 = (let _157_506 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _157_505 = (let _157_504 = (let _157_501 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _157_501))
in (let _157_503 = (let _157_502 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_157_502)::[])
in (_157_504)::_157_503))
in (_157_506)::_157_505))
in (FStar_Syntax_Syntax.mk_Tm_app _157_508 _157_507 None res_t.FStar_Syntax_Syntax.pos)))
in (

let forall_y_x_eq_y_yret = (let _157_518 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::(u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _157_517 = (let _157_516 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _157_515 = (let _157_514 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _157_513 = (let _157_512 = (let _157_511 = (let _157_510 = (let _157_509 = (FStar_Syntax_Syntax.mk_binder y)
in (_157_509)::[])
in (FStar_Syntax_Util.abs _157_510 x_eq_y_yret (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _157_511))
in (_157_512)::[])
in (_157_514)::_157_513))
in (_157_516)::_157_515))
in (FStar_Syntax_Syntax.mk_Tm_app _157_518 _157_517 None res_t.FStar_Syntax_Syntax.pos)))
in (

let lc2 = (mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (

let lc = (let _157_519 = (FStar_TypeChecker_Env.get_range env)
in (bind _157_519 env None (FStar_Syntax_Util.lcomp_of_comp comp) ((Some (x)), ((FStar_Syntax_Util.lcomp_of_comp lc2)))))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))


let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (

let joined_eff = (join_lcomp env lcomp_then lcomp_else)
in (

let comp = (fun _58_899 -> (match (()) with
| () -> begin
if (env.FStar_TypeChecker_Env.lax && false) then begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lcomp_then.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lcomp_then.FStar_Syntax_Syntax.res_typ []))
end else begin
(

let _58_917 = (let _157_531 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _157_530 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _157_531 _157_530)))
in (match (_58_917) with
| ((md, _58_903, _58_905), (u_res_t, res_t, wp_then), (_58_912, _58_914, wp_else)) -> begin
(

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _157_551 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (let _157_550 = (let _157_548 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _157_547 = (let _157_546 = (FStar_Syntax_Syntax.as_arg g)
in (let _157_545 = (let _157_544 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _157_543 = (let _157_542 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_157_542)::[])
in (_157_544)::_157_543))
in (_157_546)::_157_545))
in (_157_548)::_157_547))
in (let _157_549 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _157_551 _157_550 None _157_549)))))
in (

let wp = (ifthenelse md res_t guard wp_then wp_else)
in if ((FStar_Options.split_cases ()) > (Prims.parse_int "0")) then begin
(

let comp = (mk_comp md u_res_t res_t wp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(

let wp = (let _157_556 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (let _157_555 = (let _157_554 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _157_553 = (let _157_552 = (FStar_Syntax_Syntax.as_arg wp)
in (_157_552)::[])
in (_157_554)::_157_553))
in (FStar_Syntax_Syntax.mk_Tm_app _157_556 _157_555 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md u_res_t res_t wp []))
end))
end))
end
end))
in (let _157_557 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _157_557; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp}))))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (let _157_563 = (let _157_562 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid _157_562))
in (FStar_Syntax_Syntax.fvar _157_563 FStar_Syntax_Syntax.Delta_constant None)))


let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (FStar_List.fold_left (fun eff _58_936 -> (match (_58_936) with
| (_58_934, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (

let bind_cases = (fun _58_939 -> (match (()) with
| () -> begin
(

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in if (env.FStar_TypeChecker_Env.lax && false) then begin
(lax_mk_tot_or_comp_l eff u_res_t res_t [])
end else begin
(

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _157_593 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (let _157_592 = (let _157_590 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _157_589 = (let _157_588 = (FStar_Syntax_Syntax.as_arg g)
in (let _157_587 = (let _157_586 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _157_585 = (let _157_584 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_157_584)::[])
in (_157_586)::_157_585))
in (_157_588)::_157_587))
in (_157_590)::_157_589))
in (let _157_591 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _157_593 _157_592 None _157_591)))))
in (

let default_case = (

let post_k = (let _157_596 = (let _157_594 = (FStar_Syntax_Syntax.null_binder res_t)
in (_157_594)::[])
in (let _157_595 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _157_596 _157_595)))
in (

let kwp = (let _157_599 = (let _157_597 = (FStar_Syntax_Syntax.null_binder post_k)
in (_157_597)::[])
in (let _157_598 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _157_599 _157_598)))
in (

let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (

let wp = (let _157_605 = (let _157_600 = (FStar_Syntax_Syntax.mk_binder post)
in (_157_600)::[])
in (let _157_604 = (let _157_603 = (let _157_601 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Errors.exhaustiveness_check _157_601))
in (let _157_602 = (fvar_const env FStar_Syntax_Const.false_lid)
in (FStar_All.pipe_left _157_603 _157_602)))
in (FStar_Syntax_Util.abs _157_605 _157_604 (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md u_res_t res_t wp []))))))
in (

let comp = (FStar_List.fold_right (fun _58_955 celse -> (match (_58_955) with
| (g, cthen) -> begin
(

let _58_975 = (let _157_608 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _157_608 celse))
in (match (_58_975) with
| ((md, _58_959, _58_961), (_58_964, _58_966, wp_then), (_58_970, _58_972, wp_else)) -> begin
(let _157_609 = (ifthenelse md res_t g wp_then wp_else)
in (mk_comp md u_res_t res_t _157_609 []))
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

let _58_984 = (destruct_comp comp)
in (match (_58_984) with
| (_58_980, _58_982, wp) -> begin
(

let wp = (let _157_614 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (let _157_613 = (let _157_612 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _157_611 = (let _157_610 = (FStar_Syntax_Syntax.as_arg wp)
in (_157_610)::[])
in (_157_612)::_157_611))
in (FStar_Syntax_Syntax.mk_Tm_app _157_614 _157_613 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md u_res_t res_t wp []))
end))))
end)))
end)
end))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))


let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (

let close = (fun _58_990 -> (match (()) with
| () -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in if (FStar_Syntax_Util.is_ml_comp c) then begin
c
end else begin
if (env.FStar_TypeChecker_Env.lax && false) then begin
c
end else begin
(

let close_wp = (fun u_res md res_t bvs wp0 -> (FStar_List.fold_right (fun x wp -> (

let bs = (let _157_635 = (FStar_Syntax_Syntax.mk_binder x)
in (_157_635)::[])
in (

let us = (let _157_637 = (let _157_636 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (_157_636)::[])
in (u_res)::_157_637)
in (

let wp = (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))))))
in (let _157_644 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (let _157_643 = (let _157_642 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _157_641 = (let _157_640 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _157_639 = (let _157_638 = (FStar_Syntax_Syntax.as_arg wp)
in (_157_638)::[])
in (_157_640)::_157_639))
in (_157_642)::_157_641))
in (FStar_Syntax_Syntax.mk_Tm_app _157_644 _157_643 None wp0.FStar_Syntax_Syntax.pos))))))) bvs wp0))
in (

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _58_1007 = (destruct_comp c)
in (match (_58_1007) with
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

let _58_1010 = lc
in {FStar_Syntax_Syntax.eff_name = _58_1010.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _58_1010.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _58_1010.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))


let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (

let refine = (fun _58_1016 -> (match (()) with
| () -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in if ((not ((is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name))) || (env.FStar_TypeChecker_Env.lax && false)) then begin
c
end else begin
if (FStar_Syntax_Util.is_partial_return c) then begin
c
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c) && (not ((FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)))) then begin
(let _157_655 = (let _157_654 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _157_653 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _157_654 _157_653)))
in (failwith _157_655))
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

let ret = (let _157_657 = (let _157_656 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _157_656 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _157_657))
in (

let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (

let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (

let c = (let _157_659 = (let _157_658 = (bind e.FStar_Syntax_Syntax.pos env None (FStar_Syntax_Util.lcomp_of_comp c) ((Some (x)), (eq_ret)))
in (_157_658.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _157_659 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
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

let _58_1028 = lc
in {FStar_Syntax_Syntax.eff_name = _58_1028.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _58_1028.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))


let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (match ((FStar_TypeChecker_Rel.sub_comp env c c')) with
| None -> begin
(let _157_671 = (let _157_670 = (let _157_669 = (FStar_TypeChecker_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _157_668 = (FStar_TypeChecker_Env.get_range env)
in ((_157_669), (_157_668))))
in FStar_Syntax_Syntax.Error (_157_670))
in (Prims.raise _157_671))
end
| Some (g) -> begin
((e), (c'), (g))
end))


let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match ((let _157_680 = (FStar_Syntax_Subst.compress t)
in _157_680.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_58_1042) -> begin
(match ((let _157_681 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _157_681.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid) -> begin
(

let _58_1046 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (

let b2t = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (

let lc = (let _157_684 = (let _157_683 = (let _157_682 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _157_682))
in ((None), (_157_683)))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) lc _157_684))
in (

let e = (let _157_686 = (let _157_685 = (FStar_Syntax_Syntax.as_arg e)
in (_157_685)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _157_686 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in ((e), (lc))))))
end
| _58_1052 -> begin
((e), (lc))
end)
end
| _58_1054 -> begin
((e), (lc))
end))


let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (

let gopt = if env.FStar_TypeChecker_Env.use_eq then begin
(let _157_695 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in ((_157_695), (false)))
end else begin
(let _157_696 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in ((_157_696), (true)))
end
in (match (gopt) with
| (None, _58_1062) -> begin
(

let _58_1064 = (FStar_TypeChecker_Rel.subtype_fail env e lc.FStar_Syntax_Syntax.res_typ t)
in ((e), ((

let _58_1066 = lc
in {FStar_Syntax_Syntax.eff_name = _58_1066.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _58_1066.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _58_1066.FStar_Syntax_Syntax.comp})), (FStar_TypeChecker_Rel.trivial_guard)))
end
| (Some (g), apply_guard) -> begin
(match ((FStar_TypeChecker_Rel.guard_form g)) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let lc = (

let _58_1073 = lc
in {FStar_Syntax_Syntax.eff_name = _58_1073.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _58_1073.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _58_1073.FStar_Syntax_Syntax.comp})
in ((e), (lc), (g)))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let g = (

let _58_1078 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_1078.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_1078.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_1078.FStar_TypeChecker_Env.implicits})
in (

let strengthen = (fun _58_1082 -> (match (()) with
| () -> begin
if (env.FStar_TypeChecker_Env.lax && false) then begin
(lc.FStar_Syntax_Syntax.comp ())
end else begin
(

let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (match ((let _157_699 = (FStar_Syntax_Subst.compress f)
in _157_699.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_58_1085, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _58_1091; FStar_Syntax_Syntax.pos = _58_1089; FStar_Syntax_Syntax.vars = _58_1087}, _58_1096) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
(

let lc = (

let _58_1099 = lc
in {FStar_Syntax_Syntax.eff_name = _58_1099.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _58_1099.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _58_1099.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| _58_1103 -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let _58_1105 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _157_703 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _157_702 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _157_701 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _157_700 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _157_703 _157_702 _157_701 _157_700)))))
end else begin
()
end
in (

let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _58_1110 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_58_1110) with
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

let _58_1120 = (destruct_comp ct)
in (match (_58_1120) with
| (u_t, _58_1117, _58_1119) -> begin
(

let wp = (let _157_708 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.ret_wp)
in (let _157_707 = (let _157_706 = (FStar_Syntax_Syntax.as_arg t)
in (let _157_705 = (let _157_704 = (FStar_Syntax_Syntax.as_arg xexp)
in (_157_704)::[])
in (_157_706)::_157_705))
in (FStar_Syntax_Syntax.mk_Tm_app _157_708 _157_707 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)))
in (

let cret = (let _157_709 = (mk_comp md u_t t wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _157_709))
in (

let guard = if apply_guard then begin
(let _157_711 = (let _157_710 = (FStar_Syntax_Syntax.as_arg xexp)
in (_157_710)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _157_711 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end else begin
f
end
in (

let _58_1126 = (let _157_719 = (FStar_All.pipe_left (fun _157_716 -> Some (_157_716)) (FStar_TypeChecker_Errors.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _157_718 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _157_717 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _157_719 _157_718 e cret _157_717))))
in (match (_58_1126) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x = (

let _58_1127 = x
in {FStar_Syntax_Syntax.ppname = _58_1127.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1127.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (

let c = (let _157_721 = (let _157_720 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _157_720))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) _157_721 ((Some (x)), (eq_ret))))
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let _58_1132 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _157_722 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _157_722))
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

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _58_3 -> (match (_58_3) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| FStar_Syntax_Syntax.CPS -> begin
(FStar_Syntax_Syntax.CPS)::[]
end
| _58_1139 -> begin
[]
end))))
in (

let lc = (

let _58_1141 = lc
in (let _157_724 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _157_724; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (

let g = (

let _58_1144 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_1144.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_1144.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_1144.FStar_TypeChecker_Env.implicits})
in ((e), (lc), (g)))))))
end)
end)))


let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _157_736 = (let _157_735 = (let _157_734 = (let _157_733 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _157_733))
in (_157_734)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _157_735 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _157_736))))
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
| ((req, _58_1172))::((ens, _58_1167))::_58_1164 -> begin
(let _157_742 = (let _157_739 = (norm req)
in Some (_157_739))
in (let _157_741 = (let _157_740 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _157_740))
in ((_157_742), (_157_741))))
end
| _58_1176 -> begin
(let _157_746 = (let _157_745 = (let _157_744 = (let _157_743 = (FStar_Syntax_Print.comp_to_string comp)
in (FStar_Util.format1 "Effect constructor is not fully applied; got %s" _157_743))
in ((_157_744), (comp.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_157_745))
in (Prims.raise _157_746))
end)
end else begin
(

let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| ((wp, _58_1182))::_58_1179 -> begin
(

let _58_1188 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (_58_1188) with
| (us_r, _58_1187) -> begin
(

let _58_1192 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (_58_1192) with
| (us_e, _58_1191) -> begin
(

let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (

let as_req = (let _157_747 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.as_requires r) FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.mk_Tm_uinst _157_747 us_r))
in (

let as_ens = (let _157_748 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.as_ensures r) FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.mk_Tm_uinst _157_748 us_e))
in (

let req = (let _157_751 = (let _157_750 = (let _157_749 = (FStar_Syntax_Syntax.as_arg wp)
in (_157_749)::[])
in (((ct.FStar_Syntax_Syntax.result_typ), (Some (FStar_Syntax_Syntax.imp_tag))))::_157_750)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _157_751 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let ens = (let _157_754 = (let _157_753 = (let _157_752 = (FStar_Syntax_Syntax.as_arg wp)
in (_157_752)::[])
in (((ct.FStar_Syntax_Syntax.result_typ), (Some (FStar_Syntax_Syntax.imp_tag))))::_157_753)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _157_754 None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _157_758 = (let _157_755 = (norm req)
in Some (_157_755))
in (let _157_757 = (let _157_756 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm _157_756))
in ((_157_758), (_157_757)))))))))
end))
end))
end
| _58_1199 -> begin
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

let _58_1209 = (FStar_Syntax_Util.arrow_formals t)
in (match (_58_1209) with
| (formals, _58_1208) -> begin
(

let n_implicits = (match ((FStar_All.pipe_right formals (FStar_Util.prefix_until (fun _58_1213 -> (match (_58_1213) with
| (_58_1211, imp) -> begin
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
(let _157_776 = (let _157_775 = (let _157_774 = (let _157_772 = (FStar_Util.string_of_int n_expected)
in (let _157_771 = (FStar_Syntax_Print.term_to_string e)
in (let _157_770 = (FStar_Util.string_of_int n_available)
in (FStar_Util.format3 "Expected a term with %s implicit arguments, but %s has only %s" _157_772 _157_771 _157_770))))
in (let _157_773 = (FStar_TypeChecker_Env.get_range env)
in ((_157_774), (_157_773))))
in FStar_Syntax_Syntax.Error (_157_775))
in (Prims.raise _157_776))
end else begin
Some ((n_available - n_expected))
end))
end))
in (

let decr_inst = (fun _58_4 -> (match (_58_4) with
| None -> begin
None
end
| Some (i) -> begin
Some ((i - (Prims.parse_int "1")))
end))
in (match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _58_1239 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_1239) with
| (bs, c) -> begin
(

let rec aux = (fun subst inst_n bs -> (match (((inst_n), (bs))) with
| (Some (_157_785), _58_1247) when (_157_785 = (Prims.parse_int "0")) -> begin
(([]), (bs), (subst), (FStar_TypeChecker_Rel.trivial_guard))
end
| (_58_1250, ((x, Some (FStar_Syntax_Syntax.Implicit (dot))))::rest) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let _58_1264 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t)
in (match (_58_1264) with
| (v, _58_1262, g) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (v))))::subst
in (

let _58_1270 = (aux subst (decr_inst inst_n) rest)
in (match (_58_1270) with
| (args, bs, subst, g') -> begin
(let _157_786 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((v), (Some (FStar_Syntax_Syntax.Implicit (dot)))))::args), (bs), (subst), (_157_786)))
end)))
end)))
end
| (_58_1272, bs) -> begin
(([]), (bs), (subst), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (

let _58_1279 = (let _157_787 = (inst_n_binders t)
in (aux [] _157_787 bs))
in (match (_58_1279) with
| (args, bs, subst, guard) -> begin
(match (((args), (bs))) with
| ([], _58_1282) -> begin
((e), (torig), (guard))
end
| (_58_1285, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
((e), (torig), (FStar_TypeChecker_Rel.trivial_guard))
end
| _58_1289 -> begin
(

let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _58_1292 -> begin
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
| _58_1297 -> begin
((e), (t), (FStar_TypeChecker_Rel.trivial_guard))
end))))
end))


let string_of_univs = (fun univs -> (let _157_792 = (let _157_791 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _157_791 (FStar_List.map (fun u -> (let _157_790 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _157_790 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _157_792 (FStar_String.concat ", "))))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(

let s = (let _157_798 = (let _157_797 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _157_797))
in (FStar_All.pipe_right _157_798 FStar_Util.set_elements))
in (

let _58_1303 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _157_800 = (let _157_799 = (FStar_TypeChecker_Env.univ_vars env)
in (string_of_univs _157_799))
in (FStar_Util.print1 "univ_vars in env: %s\n" _157_800))
end else begin
()
end
in (

let r = (let _157_801 = (FStar_TypeChecker_Env.get_range env)
in Some (_157_801))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (

let _58_1308 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _157_806 = (let _157_803 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _157_803))
in (let _157_805 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _157_804 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _157_806 _157_805 _157_804))))
end else begin
()
end
in (

let _58_1310 = (FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))))
in u_name))))))
in u_names))))
end)


let gather_free_univnames : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env t -> (

let ctx_univnames = (FStar_TypeChecker_Env.univnames env)
in (

let tm_univnames = (FStar_Syntax_Free.univnames t)
in (

let univnames = (let _157_811 = (FStar_Util.fifo_set_difference tm_univnames ctx_univnames)
in (FStar_All.pipe_right _157_811 FStar_Util.fifo_set_elements))
in univnames))))


let maybe_set_tk = (fun ts _58_5 -> (match (_58_5) with
| None -> begin
ts
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Syntax.mk t None FStar_Range.dummyRange)
in (

let t = (FStar_Syntax_Subst.close_univ_vars (Prims.fst ts) t)
in (

let _58_1325 = (FStar_ST.op_Colon_Equals (Prims.snd ts).FStar_Syntax_Syntax.tk (Some (t.FStar_Syntax_Syntax.n)))
in ts)))
end))


let check_universe_generalization : FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun explicit_univ_names generalized_univ_names t -> (match (((explicit_univ_names), (generalized_univ_names))) with
| ([], _58_1332) -> begin
generalized_univ_names
end
| (_58_1335, []) -> begin
explicit_univ_names
end
| _58_1339 -> begin
(let _157_823 = (let _157_822 = (let _157_821 = (let _157_820 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "Generalized universe in a term containing explicit universe annotation : " _157_820))
in ((_157_821), (t.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_157_822))
in (Prims.raise _157_823))
end))


let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Beta)::[]) env t0)
in (

let univnames = (gather_free_univnames env t)
in (

let univs = (FStar_Syntax_Free.univs t)
in (

let _58_1345 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _157_828 = (string_of_univs univs)
in (FStar_Util.print1 "univs to gen : %s\n" _157_828))
end else begin
()
end
in (

let gen = (gen_univs env univs)
in (

let _58_1348 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _157_829 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _157_829))
end else begin
()
end
in (

let univs = (check_universe_generalization univnames gen t0)
in (

let ts = (FStar_Syntax_Subst.close_univ_vars univs t)
in (let _157_830 = (FStar_ST.read t0.FStar_Syntax_Syntax.tk)
in (maybe_set_tk ((univs), (ts)) _157_830)))))))))))


let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> if (let _157_836 = (FStar_Util.for_all (fun _58_1357 -> (match (_58_1357) with
| (_58_1355, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _157_836)) then begin
None
end else begin
(

let norm = (fun c -> (

let _58_1360 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _157_839 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _157_839))
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

let _58_1363 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _157_840 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _157_840))
end else begin
()
end
in c))))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (let _157_843 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _157_843 FStar_Util.set_elements)))
in (

let _58_1379 = (let _157_845 = (FStar_All.pipe_right ecs (FStar_List.map (fun _58_1370 -> (match (_58_1370) with
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
in (FStar_All.pipe_right _157_845 FStar_List.unzip))
in (match (_58_1379) with
| (univs, uvars) -> begin
(

let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (

let gen_univs = (gen_univs env univs)
in (

let _58_1383 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end else begin
()
end
in (

let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _58_1388 -> (match (_58_1388) with
| (uvs, e, c) -> begin
(

let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _58_1391 -> (match (_58_1391) with
| (u, k) -> begin
(match ((FStar_Unionfind.find u)) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
((a), (Some (FStar_Syntax_Syntax.imp_tag)))
end
| FStar_Syntax_Syntax.Fixed (_58_1425) -> begin
(failwith "Unexpected instantiation of mutually recursive uvar")
end
| _58_1428 -> begin
(

let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (

let _58_1432 = (FStar_Syntax_Util.arrow_formals k)
in (match (_58_1432) with
| (bs, kres) -> begin
(

let a = (let _157_851 = (let _157_850 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _157_849 -> Some (_157_849)) _157_850))
in (FStar_Syntax_Syntax.new_bv _157_851 kres))
in (

let t = (let _157_856 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _157_855 = (let _157_854 = (let _157_853 = (let _157_852 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _157_852))
in FStar_Util.Inl (_157_853))
in Some (_157_854))
in (FStar_Syntax_Util.abs bs _157_856 _157_855)))
in (

let _58_1435 = (FStar_Syntax_Util.set_uvar u t)
in ((a), (Some (FStar_Syntax_Syntax.imp_tag))))))
end)))
end)
end))))
in (

let _58_1467 = (match (((tvars), (gen_univs))) with
| ([], []) -> begin
((e), (c))
end
| ([], _58_1443) -> begin
(

let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
in (

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env e)
in ((e), (c))))
end
| _58_1448 -> begin
(

let _58_1451 = ((e), (c))
in (match (_58_1451) with
| (e0, c0) -> begin
(

let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
in (

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Iota))::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env e)
in (

let t = (match ((let _157_857 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _157_857.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(

let _58_1460 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (_58_1460) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| _58_1462 -> begin
(FStar_Syntax_Util.arrow tvars c)
end)
in (

let e' = (FStar_Syntax_Util.abs tvars e (Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp c)))))
in (let _157_858 = (FStar_Syntax_Syntax.mk_Total t)
in ((e'), (_157_858)))))))
end))
end)
in (match (_58_1467) with
| (e, c) -> begin
((gen_univs), (e), (c))
end)))
end))))
in Some (ecs)))))
end)))))
end)


let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> (

let _58_1477 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_865 = (let _157_864 = (FStar_List.map (fun _58_1476 -> (match (_58_1476) with
| (lb, _58_1473, _58_1475) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _157_864 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _157_865))
end else begin
()
end
in (

let univnames_lecs = (FStar_List.map (fun _58_1482 -> (match (_58_1482) with
| (l, t, c) -> begin
(gather_free_univnames env t)
end)) lecs)
in (

let generalized_lecs = (match ((let _157_868 = (FStar_All.pipe_right lecs (FStar_List.map (fun _58_1488 -> (match (_58_1488) with
| (_58_1485, e, c) -> begin
((e), (c))
end))))
in (gen env _157_868))) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun _58_1493 -> (match (_58_1493) with
| (l, t, c) -> begin
((l), ([]), (t), (c))
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _58_1501 _58_1505 -> (match (((_58_1501), (_58_1505))) with
| ((l, _58_1498, _58_1500), (us, e, c)) -> begin
(

let _58_1506 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _157_875 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _157_874 = (FStar_Syntax_Print.lbname_to_string l)
in (let _157_873 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (let _157_872 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print4 "(%s) Generalized %s at type %s\n%s\n" _157_875 _157_874 _157_873 _157_872)))))
end else begin
()
end
in ((l), (us), (e), (c)))
end)) lecs ecs)
end)
in (FStar_List.map2 (fun univnames _58_1514 -> (match (_58_1514) with
| (l, generalized_univs, t, c) -> begin
(let _157_878 = (check_universe_generalization univnames generalized_univs t)
in ((l), (_157_878), (t), (c)))
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
(let _157_894 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _157_893 -> Some (_157_893)) _157_894))
end)
end)
in (

let is_var = (fun e -> (match ((let _157_897 = (FStar_Syntax_Subst.compress e)
in _157_897.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (_58_1530) -> begin
true
end
| _58_1533 -> begin
false
end))
in (

let decorate = (fun e t -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((

let _58_1540 = x
in {FStar_Syntax_Syntax.ppname = _58_1540.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1540.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| _58_1543 -> begin
(

let _58_1544 = e
in (let _157_902 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _58_1544.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _157_902; FStar_Syntax_Syntax.pos = _58_1544.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_1544.FStar_Syntax_Syntax.vars}))
end)))
in (

let env = (

let _58_1546 = env
in (let _157_903 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _58_1546.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1546.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1546.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1546.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1546.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1546.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1546.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1546.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1546.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1546.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1546.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1546.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1546.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1546.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1546.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _157_903; FStar_TypeChecker_Env.is_iface = _58_1546.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1546.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1546.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_1546.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_1546.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1546.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1546.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1546.FStar_TypeChecker_Env.qname_and_index}))
in (match ((check env t1 t2)) with
| None -> begin
(let _157_907 = (let _157_906 = (let _157_905 = (FStar_TypeChecker_Errors.expected_expression_of_type env t2 e t1)
in (let _157_904 = (FStar_TypeChecker_Env.get_range env)
in ((_157_905), (_157_904))))
in FStar_Syntax_Syntax.Error (_157_906))
in (Prims.raise _157_907))
end
| Some (g) -> begin
(

let _58_1552 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _157_908 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _157_908))
end else begin
()
end
in (let _157_909 = (decorate e t2)
in ((_157_909), (g))))
end)))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (

let discharge = (fun g -> (

let _58_1559 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _157_919 = (discharge g)
in (let _157_918 = (lc.FStar_Syntax_Syntax.comp ())
in ((_157_919), (_157_918))))
end else begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let steps = (FStar_TypeChecker_Normalize.Beta)::[]
in (

let c = (let _157_922 = (let _157_921 = (let _157_920 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (FStar_All.pipe_right _157_920 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right _157_921 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (FStar_All.pipe_right _157_922 (FStar_TypeChecker_Normalize.comp_to_comp_typ env)))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let _58_1569 = (destruct_comp c)
in (match (_58_1569) with
| (u_t, t, wp) -> begin
(

let vc = (let _157_928 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.trivial)
in (let _157_927 = (let _157_925 = (FStar_Syntax_Syntax.as_arg t)
in (let _157_924 = (let _157_923 = (FStar_Syntax_Syntax.as_arg wp)
in (_157_923)::[])
in (_157_925)::_157_924))
in (let _157_926 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk_Tm_app _157_928 _157_927 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _157_926))))
in (

let _58_1571 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _157_929 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _157_929))
end else begin
()
end
in (

let g = (let _157_930 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _157_930))
in (let _157_932 = (discharge g)
in (let _157_931 = (FStar_Syntax_Syntax.mk_Comp c)
in ((_157_932), (_157_931)))))))
end))))))
end)))


let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (

let short_bin_op = (fun f _58_6 -> (match (_58_6) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((fst, _58_1582))::[] -> begin
(f fst)
end
| _58_1586 -> begin
(failwith "Unexpexted args to binary operator")
end))
in (

let op_and_e = (fun e -> (let _157_953 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _157_953 (fun _157_952 -> FStar_TypeChecker_Common.NonTrivial (_157_952)))))
in (

let op_or_e = (fun e -> (let _157_958 = (let _157_956 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _157_956))
in (FStar_All.pipe_right _157_958 (fun _157_957 -> FStar_TypeChecker_Common.NonTrivial (_157_957)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _157_961 -> FStar_TypeChecker_Common.NonTrivial (_157_961))))
in (

let op_or_t = (fun t -> (let _157_965 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _157_965 (fun _157_964 -> FStar_TypeChecker_Common.NonTrivial (_157_964)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _157_968 -> FStar_TypeChecker_Common.NonTrivial (_157_968))))
in (

let short_op_ite = (fun _58_7 -> (match (_58_7) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((guard, _58_1601))::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| (_then)::((guard, _58_1606))::[] -> begin
(let _157_972 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _157_972 (fun _157_971 -> FStar_TypeChecker_Common.NonTrivial (_157_971))))
end
| _58_1611 -> begin
(failwith "Unexpected args to ITE")
end))
in (

let table = (((FStar_Syntax_Const.op_And), ((short_bin_op op_and_e))))::(((FStar_Syntax_Const.op_Or), ((short_bin_op op_or_e))))::(((FStar_Syntax_Const.and_lid), ((short_bin_op op_and_t))))::(((FStar_Syntax_Const.or_lid), ((short_bin_op op_or_t))))::(((FStar_Syntax_Const.imp_lid), ((short_bin_op op_imp_t))))::(((FStar_Syntax_Const.ite_lid), (short_op_ite)))::[]
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((FStar_Util.find_map table (fun _58_1619 -> (match (_58_1619) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _157_1005 = (mk seen_args)
in Some (_157_1005))
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
| _58_1624 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (match ((let _157_1008 = (FStar_Syntax_Util.un_uinst l)
in _157_1008.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| _58_1629 -> begin
false
end))


let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (

let pos = (fun bs -> (match (bs) with
| ((hd, _58_1638))::_58_1635 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| _58_1642 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| ((_58_1646, Some (FStar_Syntax_Syntax.Implicit (_58_1648))))::_58_1644 -> begin
bs
end
| _58_1654 -> begin
(match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
bs
end
| Some (t) -> begin
(match ((let _157_1015 = (FStar_Syntax_Subst.compress t)
in _157_1015.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', _58_1660) -> begin
(match ((FStar_Util.prefix_until (fun _58_8 -> (match (_58_8) with
| (_58_1665, Some (FStar_Syntax_Syntax.Implicit (_58_1667))) -> begin
false
end
| _58_1672 -> begin
true
end)) bs')) with
| None -> begin
bs
end
| Some ([], _58_1676, _58_1678) -> begin
bs
end
| Some (imps, _58_1683, _58_1685) -> begin
if (FStar_All.pipe_right imps (FStar_Util.for_all (fun _58_1691 -> (match (_58_1691) with
| (x, _58_1690) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end)))) then begin
(

let r = (pos bs)
in (

let imps = (FStar_All.pipe_right imps (FStar_List.map (fun _58_1695 -> (match (_58_1695) with
| (x, i) -> begin
(let _157_1019 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in ((_157_1019), (i)))
end))))
in (FStar_List.append imps bs)))
end else begin
bs
end
end)
end
| _58_1698 -> begin
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
(let _157_1030 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m2), (t))))))) _157_1030 e.FStar_Syntax_Syntax.pos))
end)))


let maybe_monadic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c t -> (

let m = (FStar_TypeChecker_Env.norm_eff_name env c)
in if (((is_pure_or_ghost_effect env m) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid)) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid)) then begin
e
end else begin
(let _157_1039 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))) _157_1039 e.FStar_Syntax_Syntax.pos))
end))


let effect_repr_aux = (fun only_reifiable env c u_c -> (match ((let _157_1044 = (FStar_TypeChecker_Env.norm_eff_name env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_TypeChecker_Env.effect_decl_opt env _157_1044))) with
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
| _58_1720 -> begin
(

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _58_1724 = (let _157_1045 = (FStar_List.hd c.FStar_Syntax_Syntax.effect_args)
in ((c.FStar_Syntax_Syntax.result_typ), (_157_1045)))
in (match (_58_1724) with
| (res_typ, wp) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_c)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (let _157_1051 = (let _157_1050 = (let _157_1048 = (let _157_1047 = (let _157_1046 = (FStar_Syntax_Syntax.as_arg res_typ)
in (_157_1046)::(wp)::[])
in ((repr), (_157_1047)))
in FStar_Syntax_Syntax.Tm_app (_157_1048))
in (let _157_1049 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _157_1050 None _157_1049)))
in Some (_157_1051)))
end)))
end)
end
end))


let effect_repr : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term Prims.option = (fun env c u_c -> (effect_repr_aux false env c u_c))


let reify_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term = (fun env c u_c -> (

let no_reify = (fun l -> (let _157_1069 = (let _157_1068 = (let _157_1067 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _157_1066 = (FStar_TypeChecker_Env.get_range env)
in ((_157_1067), (_157_1066))))
in FStar_Syntax_Syntax.Error (_157_1068))
in (Prims.raise _157_1069)))
in (match ((let _157_1070 = (c.FStar_Syntax_Syntax.comp ())
in (effect_repr_aux true env _157_1070 u_c))) with
| None -> begin
(no_reify c.FStar_Syntax_Syntax.eff_name)
end
| Some (tm) -> begin
tm
end)))


let d : Prims.string  ->  Prims.unit = (fun s -> (FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s))


let mk_toplevel_definition : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term) = (fun env lident def -> (

let _58_1743 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _58_1741 = (d (FStar_Ident.text_of_lid lident))
in (let _157_1079 = (FStar_Syntax_Print.term_to_string def)
in (FStar_Util.print2 "Registering top-level definition: %s\n%s\n" (FStar_Ident.text_of_lid lident) _157_1079)))
end else begin
()
end
in (

let fv = (let _157_1080 = (FStar_Syntax_Util.incr_delta_qualifier def)
in (FStar_Syntax_Syntax.lid_as_fv lident _157_1080 None))
in (

let lbname = FStar_Util.Inr (fv)
in (

let lb = ((false), (({FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = def})::[]))
in (

let sig_ctx = FStar_Syntax_Syntax.Sig_let (((lb), (FStar_Range.dummyRange), ((lident)::[]), ((FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)::[]), ([])))
in (let _157_1081 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) None FStar_Range.dummyRange)
in ((sig_ctx), (_157_1081)))))))))


let check_sigelt_quals : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (

let visibility = (fun _58_9 -> (match (_58_9) with
| FStar_Syntax_Syntax.Private -> begin
true
end
| _58_1754 -> begin
false
end))
in (

let reducibility = (fun _58_10 -> (match (_58_10) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) | (FStar_Syntax_Syntax.Visible_default) | (FStar_Syntax_Syntax.Inline_for_extraction) -> begin
true
end
| _58_1763 -> begin
false
end))
in (

let assumption = (fun _58_11 -> (match (_58_11) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.New) -> begin
true
end
| _58_1769 -> begin
false
end))
in (

let reification = (fun _58_12 -> (match (_58_12) with
| (FStar_Syntax_Syntax.Reifiable) | (FStar_Syntax_Syntax.Reflectable (_)) -> begin
true
end
| _58_1777 -> begin
false
end))
in (

let inferred = (fun _58_13 -> (match (_58_13) with
| (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) | (FStar_Syntax_Syntax.ExceptionConstructor) | (FStar_Syntax_Syntax.HasMaskedEffect) | (FStar_Syntax_Syntax.Effect) -> begin
true
end
| _58_1796 -> begin
false
end))
in (

let has_eq = (fun _58_14 -> (match (_58_14) with
| (FStar_Syntax_Syntax.Noeq) | (FStar_Syntax_Syntax.Unopteq) -> begin
true
end
| _58_1802 -> begin
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
| _58_1831 -> begin
true
end))
in (

let quals = (FStar_Syntax_Util.quals_of_sigelt se)
in if (let _157_1110 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _58_15 -> (match (_58_15) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| _58_1836 -> begin
false
end))))
in (FStar_All.pipe_right _157_1110 Prims.op_Negation)) then begin
(

let r = (FStar_Syntax_Util.range_of_sigelt se)
in (

let no_dup_quals = (FStar_Util.remove_dups (fun x y -> (x = y)) quals)
in (

let err' = (fun msg -> (let _157_1118 = (let _157_1117 = (let _157_1116 = (let _157_1115 = (FStar_Syntax_Print.quals_to_string quals)
in (FStar_Util.format2 "The qualifier list \"[%s]\" is not permissible for this element%s" _157_1115 msg))
in ((_157_1116), (r)))
in FStar_Syntax_Syntax.Error (_157_1117))
in (Prims.raise _157_1118)))
in (

let err = (fun msg -> (err' (Prims.strcat ": " msg)))
in (

let err' = (fun _58_1846 -> (match (()) with
| () -> begin
(err' "")
end))
in (

let _58_1847 = if ((FStar_List.length quals) <> (FStar_List.length no_dup_quals)) then begin
(err "duplicate qualifiers")
end else begin
()
end
in (

let _58_1849 = if (not ((FStar_All.pipe_right quals (FStar_List.for_all (quals_combo_ok quals))))) then begin
(err "ill-formed combination")
end else begin
()
end
in (match (se) with
| FStar_Syntax_Syntax.Sig_let ((is_rec, _58_1853), _58_1856, _58_1858, _58_1860, _58_1862) -> begin
(

let _58_1865 = if (is_rec && (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))) then begin
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
| FStar_Syntax_Syntax.Sig_bundle (_58_1869) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.Abstract) || (inferred x)) || (visibility x)) || (has_eq x))))))) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (_58_1873) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some has_eq)) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_assume (_58_1876) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((visibility x) || (x = FStar_Syntax_Syntax.Assumption))))))) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_new_effect (_58_1880) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x))))))) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_58_1884) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x))))))) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_58_1888) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((inferred x) || (visibility x))))))) then begin
(err' ())
end else begin
()
end
end
| _58_1892 -> begin
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

let inst_tc = (let _157_1157 = (let _157_1156 = (let _157_1155 = (let _157_1154 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _157_1154))
in ((_157_1155), (inst_univs)))
in FStar_Syntax_Syntax.Tm_uinst (_157_1156))
in (FStar_Syntax_Syntax.mk _157_1157 None p))
in (

let args = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _58_1914 -> (match (_58_1914) with
| (x, imp) -> begin
(let _157_1159 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_157_1159), (imp)))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app inst_tc args None p)))
in (

let unrefined_arg_binder = (let _157_1160 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder _157_1160))
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
in (let _157_1166 = (let _157_1165 = (let _157_1164 = (FStar_Syntax_Syntax.mk_Tm_uinst disc_fvar inst_univs)
in (let _157_1163 = (let _157_1162 = (let _157_1161 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _157_1161))
in (_157_1162)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _157_1164 _157_1163 None p)))
in (FStar_Syntax_Util.b2t _157_1165))
in (FStar_Syntax_Util.refine x _157_1166)))
in (let _157_1167 = (

let _58_1922 = (projectee arg_typ)
in {FStar_Syntax_Syntax.ppname = _58_1922.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1922.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})
in (FStar_Syntax_Syntax.mk_binder _157_1167)))))
end
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (let _157_1169 = (FStar_List.map (fun _58_1929 -> (match (_58_1929) with
| (x, _58_1928) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end)) tps)
in (FStar_List.append _157_1169 fields))
in (

let imp_binders = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _58_1934 -> (match (_58_1934) with
| (x, _58_1933) -> begin
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

let only_decl = ((let _157_1171 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _157_1171)) || (let _157_1173 = (let _157_1172 = (FStar_TypeChecker_Env.current_module env)
in _157_1172.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _157_1173)))
in (

let quals = (let _157_1177 = (let _157_1176 = if (only_decl && ((FStar_All.pipe_left Prims.op_Negation env.FStar_TypeChecker_Env.is_iface) || env.FStar_TypeChecker_Env.admit)) then begin
(FStar_Syntax_Syntax.Assumption)::[]
end else begin
[]
end
in (let _157_1175 = (FStar_List.filter (fun _58_16 -> (match (_58_16) with
| FStar_Syntax_Syntax.Abstract -> begin
(not (only_decl))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| _58_1943 -> begin
false
end)) iquals)
in (FStar_List.append _157_1176 _157_1175)))
in (FStar_List.append ((FStar_Syntax_Syntax.Discriminator (lid))::if only_decl then begin
(FStar_Syntax_Syntax.Logic)::[]
end else begin
[]
end) _157_1177))
in (

let binders = (FStar_List.append imp_binders ((unrefined_arg_binder)::[]))
in (

let t = (

let bool_typ = (let _157_1179 = (let _157_1178 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _157_1178))
in (FStar_Syntax_Syntax.mk_Total _157_1179))
in (let _157_1180 = (FStar_Syntax_Util.arrow binders bool_typ)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) _157_1180)))
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((discriminator_name), (uvs), (t), (quals), ((FStar_Ident.range_of_lid discriminator_name))))
in (

let _58_1949 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes"))) then begin
(let _157_1181 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a discriminator %s\n" _157_1181))
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

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _58_1954 -> (match (_58_1954) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in if (b && (j < ntps)) then begin
(let _157_1187 = (let _157_1186 = (let _157_1185 = (let _157_1184 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in ((_157_1184), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (_157_1185))
in (pos _157_1186))
in ((_157_1187), (b)))
end else begin
(let _157_1190 = (let _157_1189 = (let _157_1188 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_157_1188))
in (pos _157_1189))
in ((_157_1190), (b)))
end)
end))))
in (

let pat_true = (let _157_1194 = (let _157_1193 = (let _157_1192 = (let _157_1191 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in ((_157_1191), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (_157_1192))
in (pos _157_1193))
in ((_157_1194), (None), (FStar_Syntax_Const.exp_true_bool)))
in (

let pat_false = (let _157_1197 = (let _157_1196 = (let _157_1195 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_157_1195))
in (pos _157_1196))
in ((_157_1197), (None), (FStar_Syntax_Const.exp_false_bool)))
in (

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst unrefined_arg_binder))
in (let _157_1203 = (let _157_1202 = (let _157_1201 = (let _157_1200 = (FStar_Syntax_Util.branch pat_true)
in (let _157_1199 = (let _157_1198 = (FStar_Syntax_Util.branch pat_false)
in (_157_1198)::[])
in (_157_1200)::_157_1199))
in ((arg_exp), (_157_1201)))
in FStar_Syntax_Syntax.Tm_match (_157_1202))
in (FStar_Syntax_Syntax.mk _157_1203 None p))))))
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

let lb = (let _157_1206 = (let _157_1204 = (FStar_Syntax_Syntax.lid_as_fv discriminator_name dd None)
in FStar_Util.Inr (_157_1204))
in (let _157_1205 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = _157_1206; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _157_1205}))
in (

let impl = (let _157_1211 = (let _157_1210 = (let _157_1209 = (let _157_1208 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _157_1208 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_157_1209)::[])
in ((((false), ((lb)::[]))), (p), (_157_1210), (quals), ([])))
in FStar_Syntax_Syntax.Sig_let (_157_1211))
in (

let _58_1967 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes"))) then begin
(let _157_1212 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a discriminator %s\n" _157_1212))
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

let subst = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _58_1977 -> (match (_58_1977) with
| (a, _58_1976) -> begin
(

let _58_1981 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (_58_1981) with
| (field_name, _58_1980) -> begin
(

let field_proj_tm = (let _157_1216 = (let _157_1215 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.fv_to_tm _157_1215))
in (FStar_Syntax_Syntax.mk_Tm_uinst _157_1216 inst_univs))
in (

let proj = (FStar_Syntax_Syntax.mk_Tm_app field_proj_tm ((arg)::[]) None p)
in FStar_Syntax_Syntax.NT (((a), (proj)))))
end))
end))))
in (

let projectors_ses = (let _157_1259 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _58_1989 -> (match (_58_1989) with
| (x, _58_1988) -> begin
(

let p = (FStar_Syntax_Syntax.range_of_bv x)
in (

let _58_1994 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (_58_1994) with
| (field_name, _58_1993) -> begin
(

let t = (let _157_1221 = (let _157_1220 = (let _157_1219 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total _157_1219))
in (FStar_Syntax_Util.arrow binders _157_1220))
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) _157_1221))
in (

let only_decl = (((let _157_1222 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _157_1222)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (let _157_1224 = (let _157_1223 = (FStar_TypeChecker_Env.current_module env)
in _157_1223.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _157_1224)))
in (

let no_decl = false
in (

let quals = (fun q -> if only_decl then begin
(let _157_1228 = (FStar_List.filter (fun _58_17 -> (match (_58_17) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| _58_2003 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::_157_1228)
end else begin
q
end)
in (

let quals = (

let iquals = (FStar_All.pipe_right iquals (FStar_List.filter (fun _58_18 -> (match (_58_18) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| _58_2008 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals)))
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), (uvs), (t), (quals), ((FStar_Ident.range_of_lid field_name))))
in (

let _58_2012 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes"))) then begin
(let _157_1230 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a projector %s\n" _157_1230))
end else begin
()
end
in if only_decl then begin
(decl)::[]
end else begin
(

let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _58_2018 -> (match (_58_2018) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in if ((i + ntps) = j) then begin
(let _157_1233 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in ((_157_1233), (b)))
end else begin
if (b && (j < ntps)) then begin
(let _157_1237 = (let _157_1236 = (let _157_1235 = (let _157_1234 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in ((_157_1234), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (_157_1235))
in (pos _157_1236))
in ((_157_1237), (b)))
end else begin
(let _157_1240 = (let _157_1239 = (let _157_1238 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_157_1238))
in (pos _157_1239))
in ((_157_1240), (b)))
end
end)
end))))
in (

let pat = (let _157_1245 = (let _157_1243 = (let _157_1242 = (let _157_1241 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in ((_157_1241), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (_157_1242))
in (pos _157_1243))
in (let _157_1244 = (FStar_Syntax_Syntax.bv_to_name projection)
in ((_157_1245), (None), (_157_1244))))
in (

let body = (let _157_1249 = (let _157_1248 = (let _157_1247 = (let _157_1246 = (FStar_Syntax_Util.branch pat)
in (_157_1246)::[])
in ((arg_exp), (_157_1247)))
in FStar_Syntax_Syntax.Tm_match (_157_1248))
in (FStar_Syntax_Syntax.mk _157_1249 None p))
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

let lb = (let _157_1252 = (let _157_1250 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (_157_1250))
in (let _157_1251 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = _157_1252; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _157_1251}))
in (

let impl = (let _157_1257 = (let _157_1256 = (let _157_1255 = (let _157_1254 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _157_1254 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_157_1255)::[])
in ((((false), ((lb)::[]))), (p), (_157_1256), (quals), ([])))
in FStar_Syntax_Syntax.Sig_let (_157_1257))
in (

let _58_2029 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes"))) then begin
(let _157_1258 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a projector %s\n" _157_1258))
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
in (FStar_All.pipe_right _157_1259 FStar_List.flatten))
in (FStar_List.append discriminator_ses projectors_ses)))))))))))))))))))


let mk_data_operations : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env tcs se -> (match (se) with
| FStar_Syntax_Syntax.Sig_datacon (constr_lid, uvs, t, typ_lid, n_typars, quals, _58_2043, r) when (not ((FStar_Ident.lid_equals constr_lid FStar_Syntax_Const.lexcons_lid))) -> begin
(

let _58_2049 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (_58_2049) with
| (univ_opening, uvs) -> begin
(

let t = (FStar_Syntax_Subst.subst univ_opening t)
in (

let _58_2054 = (FStar_Syntax_Util.arrow_formals t)
in (match (_58_2054) with
| (formals, _58_2053) -> begin
(

let _58_2081 = (

let tps_opt = (FStar_Util.find_map tcs (fun se -> if (let _157_1269 = (FStar_Util.must (FStar_Syntax_Util.lid_of_sigelt se))
in (FStar_Ident.lid_equals typ_lid _157_1269)) then begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_2057, uvs', tps, typ0, _58_2062, constrs, _58_2065, _58_2067) -> begin
(

let _58_2070 = ()
in Some (((tps), (typ0), (((FStar_List.length constrs) > (Prims.parse_int "1"))))))
end
| _58_2073 -> begin
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
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected data constructor"), (r)))))
end
end))
in (match (_58_2081) with
| (inductive_tps, typ0, should_refine) -> begin
(

let inductive_tps = (FStar_Syntax_Subst.subst_binders univ_opening inductive_tps)
in (

let typ0 = (FStar_Syntax_Subst.subst univ_opening typ0)
in (

let _58_2087 = (FStar_Syntax_Util.arrow_formals typ0)
in (match (_58_2087) with
| (indices, _58_2086) -> begin
(

let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _58_19 -> (match (_58_19) with
| FStar_Syntax_Syntax.RecordConstructor (_58_2090) -> begin
true
end
| _58_2093 -> begin
false
end)))) then begin
false
end else begin
should_refine
end
in (

let fv_qual = (

let filter_records = (fun _58_20 -> (match (_58_20) with
| FStar_Syntax_Syntax.RecordConstructor (_58_2097, fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((constr_lid), (fns))))
end
| _58_2102 -> begin
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

let _58_2111 = (FStar_Util.first_N n_typars formals)
in (match (_58_2111) with
| (imp_tps, fields) -> begin
(

let rename = (FStar_List.map2 (fun _58_2115 _58_2119 -> (match (((_58_2115), (_58_2119))) with
| ((x, _58_2114), (x', _58_2118)) -> begin
(let _157_1276 = (let _157_1275 = (FStar_Syntax_Syntax.bv_to_name x')
in ((x), (_157_1275)))
in FStar_Syntax_Syntax.NT (_157_1276))
end)) imp_tps inductive_tps)
in (FStar_Syntax_Subst.subst_binders rename fields))
end))
in (mk_discriminator_and_indexed_projectors iquals fv_qual refine_domain env typ_lid constr_lid uvs inductive_tps indices fields)))))
end))))
end))
end)))
end))
end
| _58_2123 -> begin
[]
end))




