
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

let rec aux = (fun vars e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, _58_130) -> begin
(aux vars e)
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _58_136) -> begin
((t), (true))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _58_142) -> begin
(

let _58_161 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _58_148 _58_151 -> (match (((_58_148), (_58_151))) with
| ((scope, bs, check), (a, imp)) -> begin
(

let _58_154 = (mk_binder scope a)
in (match (_58_154) with
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
in (match (_58_161) with
| (scope, bs, check) -> begin
(

let _58_164 = (aux scope body)
in (match (_58_164) with
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

let _58_171 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _157_74 = (FStar_Range.string_of_range r)
in (let _157_73 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _157_74 _157_73)))
end else begin
()
end
in ((FStar_Util.Inl (t)), ((check_res || check))))))
end))
end))
end
| _58_174 -> begin
(let _157_77 = (let _157_76 = (let _157_75 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _157_75 Prims.fst))
in FStar_Util.Inl (_157_76))
in ((_157_77), (false)))
end)))
in (

let _58_177 = (let _157_78 = (t_binders env)
in (aux _157_78 e))
in (match (_58_177) with
| (t, b) -> begin
(

let t = (match (t) with
| FStar_Util.Inr (c) -> begin
(let _157_82 = (let _157_81 = (let _157_80 = (let _157_79 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" _157_79))
in ((_157_80), (rng)))
in FStar_Syntax_Syntax.Error (_157_81))
in (Prims.raise _157_82))
end
| FStar_Util.Inl (t) -> begin
t
end)
in (([]), (t), (b)))
end))))))
end
| _58_184 -> begin
(

let _58_187 = (FStar_Syntax_Subst.open_univ_vars univ_vars t)
in (match (_58_187) with
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
| FStar_Syntax_Syntax.Pat_dot_term (x, _58_200) -> begin
(

let _58_206 = (FStar_Syntax_Util.type_u ())
in (match (_58_206) with
| (k, _58_205) -> begin
(

let t = (new_uvar env k)
in (

let x = (

let _58_208 = x
in {FStar_Syntax_Syntax.ppname = _58_208.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_208.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let _58_213 = (let _157_95 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _157_95 t))
in (match (_58_213) with
| (e, u) -> begin
(

let p = (

let _58_214 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (e))); FStar_Syntax_Syntax.ty = _58_214.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _58_214.FStar_Syntax_Syntax.p})
in (([]), ([]), ([]), (env), (e), (p)))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let _58_222 = (FStar_Syntax_Util.type_u ())
in (match (_58_222) with
| (t, _58_221) -> begin
(

let x = (

let _58_223 = x
in (let _157_96 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _58_223.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_223.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _157_96}))
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

let _58_233 = (FStar_Syntax_Util.type_u ())
in (match (_58_233) with
| (t, _58_232) -> begin
(

let x = (

let _58_234 = x
in (let _157_97 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _58_234.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_234.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _157_97}))
in (

let env = (FStar_TypeChecker_Env.push_bv env x)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in (((x)::[]), ((x)::[]), ([]), (env), (e), (p)))))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _58_267 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _58_249 _58_252 -> (match (((_58_249), (_58_252))) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(

let _58_259 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_58_259) with
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
in (match (_58_267) with
| (b, a, w, env, args, pats) -> begin
(

let e = (let _157_104 = (let _157_103 = (let _157_102 = (let _157_101 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (let _157_100 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app _157_101 _157_100 None p.FStar_Syntax_Syntax.p)))
in ((_157_102), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))
in FStar_Syntax_Syntax.Tm_meta (_157_103))
in (FStar_Syntax_Syntax.mk _157_104 None p.FStar_Syntax_Syntax.p))
in (let _157_107 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _157_106 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _157_105 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in ((_157_107), (_157_106), (_157_105), (env), (e), ((

let _58_269 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _58_269.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _58_269.FStar_Syntax_Syntax.p})))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (_58_272) -> begin
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

let pats = (FStar_List.map (fun _58_287 -> (match (_58_287) with
| (p, imp) -> begin
(let _157_119 = (elaborate_pat env p)
in ((_157_119), (imp)))
end)) pats)
in (

let _58_292 = (FStar_TypeChecker_Env.lookup_datacon env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_58_292) with
| (_58_290, t) -> begin
(

let _58_296 = (FStar_Syntax_Util.arrow_formals t)
in (match (_58_296) with
| (f, _58_295) -> begin
(

let rec aux = (fun formals pats -> (match (((formals), (pats))) with
| ([], []) -> begin
[]
end
| ([], (_58_307)::_58_305) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Too many pattern arguments"), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))))
end
| ((_58_313)::_58_311, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun _58_319 -> (match (_58_319) with
| (t, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(

let a = (let _157_126 = (let _157_125 = (FStar_Syntax_Syntax.range_of_bv t)
in Some (_157_125))
in (FStar_Syntax_Syntax.new_bv _157_126 FStar_Syntax_Syntax.tun))
in (

let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (let _157_127 = (maybe_dot inaccessible a r)
in ((_157_127), (true)))))
end
| _58_326 -> begin
(let _157_131 = (let _157_130 = (let _157_129 = (let _157_128 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _157_128))
in ((_157_129), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))
in FStar_Syntax_Syntax.Error (_157_130))
in (Prims.raise _157_131))
end)
end))))
end
| ((f)::formals', ((p, p_imp))::pats') -> begin
(match (f) with
| (_58_337, Some (FStar_Syntax_Syntax.Implicit (_58_339))) when p_imp -> begin
(let _157_132 = (aux formals' pats')
in (((p), (true)))::_157_132)
end
| (_58_344, Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(

let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let p = (maybe_dot inaccessible a (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
in (let _157_133 = (aux formals' pats)
in (((p), (true)))::_157_133)))
end
| (_58_352, imp) -> begin
(let _157_136 = (let _157_134 = (FStar_Syntax_Syntax.is_implicit imp)
in ((p), (_157_134)))
in (let _157_135 = (aux formals' pats')
in (_157_136)::_157_135))
end)
end))
in (

let _58_355 = p
in (let _157_139 = (let _157_138 = (let _157_137 = (aux f pats)
in ((fv), (_157_137)))
in FStar_Syntax_Syntax.Pat_cons (_157_138))
in {FStar_Syntax_Syntax.v = _157_139; FStar_Syntax_Syntax.ty = _58_355.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _58_355.FStar_Syntax_Syntax.p})))
end))
end)))
end
| _58_358 -> begin
p
end)))
in (

let one_pat = (fun allow_wc_dependence env p -> (

let p = (elaborate_pat env p)
in (

let _58_370 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_58_370) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))) with
| Some (x) -> begin
(let _157_148 = (let _157_147 = (let _157_146 = (FStar_TypeChecker_Errors.nonlinear_pattern_variable x)
in ((_157_146), (p.FStar_Syntax_Syntax.p)))
in FStar_Syntax_Syntax.Error (_157_147))
in (Prims.raise _157_148))
end
| _58_374 -> begin
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

let _58_390 = (one_pat false env q)
in (match (_58_390) with
| (b, a, _58_387, te, q) -> begin
(

let _58_405 = (FStar_List.fold_right (fun p _58_395 -> (match (_58_395) with
| (w, args, pats) -> begin
(

let _58_401 = (one_pat false env p)
in (match (_58_401) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv FStar_Syntax_Syntax.bv_eq a a'))) then begin
(let _157_158 = (let _157_157 = (let _157_156 = (FStar_TypeChecker_Errors.disjunctive_pattern_vars a a')
in (let _157_155 = (FStar_TypeChecker_Env.get_range env)
in ((_157_156), (_157_155))))
in FStar_Syntax_Syntax.Error (_157_157))
in (Prims.raise _157_158))
end else begin
(let _157_160 = (let _157_159 = (FStar_Syntax_Syntax.as_arg arg)
in (_157_159)::args)
in (((FStar_List.append w' w)), (_157_160), ((p)::pats)))
end
end))
end)) pats (([]), ([]), ([])))
in (match (_58_405) with
| (w, args, pats) -> begin
(let _157_162 = (let _157_161 = (FStar_Syntax_Syntax.as_arg te)
in (_157_161)::args)
in (((FStar_List.append b w)), (_157_162), ((

let _58_406 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((q)::pats); FStar_Syntax_Syntax.ty = _58_406.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _58_406.FStar_Syntax_Syntax.p}))))
end))
end))
end
| _58_409 -> begin
(

let _58_417 = (one_pat true env p)
in (match (_58_417) with
| (b, _58_412, _58_414, arg, p) -> begin
(let _157_164 = (let _157_163 = (FStar_Syntax_Syntax.as_arg arg)
in (_157_163)::[])
in ((b), (_157_164), (p)))
end))
end))
in (

let _58_421 = (top_level_pat_as_args env p)
in (match (_58_421) with
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
| (_58_435, FStar_Syntax_Syntax.Tm_uinst (e, _58_438)) -> begin
(aux p e)
end
| (FStar_Syntax_Syntax.Pat_constant (_58_443), FStar_Syntax_Syntax.Tm_constant (_58_446)) -> begin
(let _157_179 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v _157_179))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(

let _58_454 = if (not ((FStar_Syntax_Syntax.bv_eq x y))) then begin
(let _157_182 = (let _157_181 = (FStar_Syntax_Print.bv_to_string x)
in (let _157_180 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _157_181 _157_180)))
in (failwith _157_182))
end else begin
()
end
in (

let _58_456 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _157_184 = (FStar_Syntax_Print.bv_to_string x)
in (let _157_183 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _157_184 _157_183)))
end else begin
()
end
in (

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x = (

let _58_459 = x
in {FStar_Syntax_Syntax.ppname = _58_459.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_459.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x)) s.FStar_Syntax_Syntax.n)))))
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(

let _58_467 = if (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation) then begin
(let _157_187 = (let _157_186 = (FStar_Syntax_Print.bv_to_string x)
in (let _157_185 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _157_186 _157_185)))
in (failwith _157_187))
end else begin
()
end
in (

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x = (

let _58_470 = x
in {FStar_Syntax_Syntax.ppname = _58_470.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_470.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x)) s.FStar_Syntax_Syntax.n))))
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _58_475), _58_479) -> begin
(

let s = (force_sort e)
in (

let x = (

let _58_482 = x
in {FStar_Syntax_Syntax.ppname = _58_482.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_482.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term (((x), (e)))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
(

let _58_492 = if (not ((FStar_Syntax_Syntax.fv_eq fv fv'))) then begin
(let _157_188 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith _157_188))
end else begin
()
end
in (let _157_189 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv'), ([])))) _157_189)))
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
(

let _58_535 = if (let _157_190 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right _157_190 Prims.op_Negation)) then begin
(let _157_191 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (failwith _157_191))
end else begin
()
end
in (

let fv = fv'
in (

let rec match_args = (fun matched_pats args argpats -> (match (((args), (argpats))) with
| ([], []) -> begin
(let _157_198 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev matched_pats))))) _157_198))
end
| ((arg)::args, ((argpat, _58_551))::argpats) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e, Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (_58_561)) -> begin
(

let x = (let _157_199 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _157_199))
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e)))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args argpats)))
end
| ((e, imp), _58_570) -> begin
(

let pat = (let _157_201 = (aux argpat e)
in (let _157_200 = (FStar_Syntax_Syntax.is_implicit imp)
in ((_157_201), (_157_200))))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _58_574 -> begin
(let _157_204 = (let _157_203 = (FStar_Syntax_Print.pat_to_string p)
in (let _157_202 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _157_203 _157_202)))
in (failwith _157_204))
end))
in (match_args [] args argpats))))
end
| _58_576 -> begin
(let _157_209 = (let _157_208 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (let _157_207 = (FStar_Syntax_Print.pat_to_string qq)
in (let _157_206 = (let _157_205 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right _157_205 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _157_208 _157_207 _157_206))))
in (failwith _157_209))
end))))
in (match (((p.FStar_Syntax_Syntax.v), (exps))) with
| (FStar_Syntax_Syntax.Pat_disj (ps), _58_580) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(

let ps = (FStar_List.map2 aux ps exps)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj (ps)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p))
end
| (_58_584, (e)::[]) -> begin
(aux p e)
end
| _58_589 -> begin
(failwith "Unexpected number of patterns")
end))))


let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (

let topt = Some (pat.FStar_Syntax_Syntax.ty)
in (

let mk = (fun f -> (FStar_Syntax_Syntax.mk f topt pat.FStar_Syntax_Syntax.p))
in (

let pat_as_arg = (fun _58_597 -> (match (_58_597) with
| (p, i) -> begin
(

let _58_600 = (decorated_pattern_as_term p)
in (match (_58_600) with
| (vars, te) -> begin
(let _157_217 = (let _157_216 = (FStar_Syntax_Syntax.as_implicit i)
in ((te), (_157_216)))
in ((vars), (_157_217)))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_58_602) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _157_218 = (mk (FStar_Syntax_Syntax.Tm_constant (c)))
in (([]), (_157_218)))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(let _157_219 = (mk (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (_157_219)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _58_615 = (let _157_220 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _157_220 FStar_List.unzip))
in (match (_58_615) with
| (vars, args) -> begin
(

let vars = (FStar_List.flatten vars)
in (let _157_224 = (let _157_223 = (let _157_222 = (let _157_221 = (FStar_Syntax_Syntax.fv_to_tm fv)
in ((_157_221), (args)))
in FStar_Syntax_Syntax.Tm_app (_157_222))
in (mk _157_223))
in ((vars), (_157_224))))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
(([]), (e))
end)))))


let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun c -> (

let wp = (match (c.FStar_Syntax_Syntax.effect_args) with
| ((wp, _58_624))::[] -> begin
wp
end
| _58_628 -> begin
(let _157_230 = (let _157_229 = (let _157_228 = (FStar_List.map (fun _58_632 -> (match (_58_632) with
| (x, _58_631) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right _157_228 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str _157_229))
in (failwith _157_230))
end)
in (let _157_231 = (FStar_List.hd c.FStar_Syntax_Syntax.comp_univs)
in ((_157_231), (c.FStar_Syntax_Syntax.result_typ), (wp)))))


let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (

let _58_641 = (destruct_comp c)
in (match (_58_641) with
| (u, _58_639, wp) -> begin
(let _157_250 = (let _157_249 = (let _157_248 = (lift c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _157_248))
in (_157_249)::[])
in {FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _157_250; FStar_Syntax_Syntax.flags = []})
end)))


let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let _58_650 = (let _157_258 = (FStar_TypeChecker_Env.norm_eff_name env l1)
in (let _157_257 = (FStar_TypeChecker_Env.norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _157_258 _157_257)))
in (match (_58_650) with
| (m, _58_647, _58_649) -> begin
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

let _58_662 = (FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (_58_662) with
| (m, lift1, lift2) -> begin
(

let m1 = (lift_comp c1 m lift1)
in (

let m2 = (lift_comp c2 m lift2)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (

let _58_668 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (_58_668) with
| (a, kwp) -> begin
(let _157_272 = (destruct_comp m1)
in (let _157_271 = (destruct_comp m2)
in ((((md), (a), (kwp))), (_157_272), (_157_271))))
end)))))
end)))))


let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid))))


let mk_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result wp flags -> (let _157_293 = (let _157_292 = (let _157_291 = (FStar_Syntax_Syntax.as_arg wp)
in (_157_291)::[])
in {FStar_Syntax_Syntax.comp_univs = (u_result)::[]; FStar_Syntax_Syntax.effect_name = mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = _157_292; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp _157_293)))


let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md -> (mk_comp_l md.FStar_Syntax_Syntax.mname))


let lax_mk_tot_or_comp_l : FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun mname u_result result flags -> if (FStar_Ident.lid_equals mname FStar_Syntax_Const.effect_Tot_lid) then begin
(FStar_Syntax_Syntax.mk_Total' result (Some (u_result)))
end else begin
(mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags)
end)


let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (

let _58_687 = lc
in (let _157_326 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _58_687.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _157_326; FStar_Syntax_Syntax.cflags = _58_687.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _58_689 -> (match (()) with
| () -> begin
(let _157_325 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _157_325))
end))})))


let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _157_329 = (FStar_Syntax_Subst.compress t)
in _157_329.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_692) -> begin
true
end
| _58_695 -> begin
false
end))


let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v -> (

let c = if (let _157_336 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation _157_336)) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(

let m = (let _157_337 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must _157_337))
in (

let u_t = (env.FStar_TypeChecker_Env.universe_of env t)
in (

let wp = if (env.FStar_TypeChecker_Env.lax && false) then begin
FStar_Syntax_Syntax.tun
end else begin
(

let _58_703 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_58_703) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (let _157_343 = (let _157_342 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env m m.FStar_Syntax_Syntax.ret_wp)
in (let _157_341 = (let _157_340 = (FStar_Syntax_Syntax.as_arg t)
in (let _157_339 = (let _157_338 = (FStar_Syntax_Syntax.as_arg v)
in (_157_338)::[])
in (_157_340)::_157_339))
in (FStar_Syntax_Syntax.mk_Tm_app _157_342 _157_341 (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _157_343)))
end))
end
in (mk_comp m u_t t wp ((FStar_Syntax_Syntax.RETURN)::[])))))
end
in (

let _58_707 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return"))) then begin
(let _157_346 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _157_345 = (FStar_Syntax_Print.term_to_string v)
in (let _157_344 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _157_346 _157_345 _157_344))))
end else begin
()
end
in c)))


let bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r1 env e1opt lc1 _58_715 -> (match (_58_715) with
| (b, lc2) -> begin
(

let lc1 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1)
in (

let lc2 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2)
in (

let joined_eff = (join_lcomp env lc1 lc2)
in (

let _58_726 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(

let bstr = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _157_359 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (let _157_358 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _157_357 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" _157_359 _157_358 bstr _157_357)))))
end else begin
()
end
in (

let bind_it = (fun _58_729 -> (match (()) with
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

let _58_736 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _157_366 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _157_365 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _157_364 = (FStar_Syntax_Print.comp_to_string c1)
in (let _157_363 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (let _157_362 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" _157_366 _157_365 _157_364 _157_363 _157_362))))))
end else begin
()
end
in (

let try_simplify = (fun _58_739 -> (match (()) with
| () -> begin
(

let aux = (fun _58_741 -> (match (()) with
| () -> begin
if (FStar_Syntax_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some (((c2), ("trivial no binder")))
end
| Some (_58_744) -> begin
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
(let _157_374 = (let _157_373 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in ((_157_373), (reason)))
in Some (_157_374))
end
| _58_754 -> begin
(aux ())
end))
in if ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2)) then begin
(subst_c2 "both total")
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2)) then begin
(let _157_376 = (let _157_375 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((_157_375), ("both gtot")))
in Some (_157_376))
end else begin
(match (((e1opt), (b))) with
| (Some (e), Some (x)) -> begin
if ((FStar_Syntax_Util.is_total_comp c1) && (not ((FStar_Syntax_Syntax.is_null_bv x)))) then begin
(subst_c2 "substituted e")
end else begin
(aux ())
end
end
| _58_761 -> begin
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

let _58_779 = (lift_and_destruct env c1 c2)
in (match (_58_779) with
| ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) -> begin
(

let bs = (match (b) with
| None -> begin
(let _157_377 = (FStar_Syntax_Syntax.null_binder t1)
in (_157_377)::[])
end
| Some (x) -> begin
(let _157_378 = (FStar_Syntax_Syntax.mk_binder x)
in (_157_378)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (

let r1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1))) None r1)
in (

let wp_args = (let _157_390 = (FStar_Syntax_Syntax.as_arg r1)
in (let _157_389 = (let _157_388 = (FStar_Syntax_Syntax.as_arg t1)
in (let _157_387 = (let _157_386 = (FStar_Syntax_Syntax.as_arg t2)
in (let _157_385 = (let _157_384 = (FStar_Syntax_Syntax.as_arg wp1)
in (let _157_383 = (let _157_382 = (let _157_381 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg _157_381))
in (_157_382)::[])
in (_157_384)::_157_383))
in (_157_386)::_157_385))
in (_157_388)::_157_387))
in (_157_390)::_157_389))
in (

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t2))))::[]) kwp)
in (

let wp = (let _157_391 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t1)::(u_t2)::[]) env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _157_391 wp_args None t2.FStar_Syntax_Syntax.pos))
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
if (let _157_415 = (FStar_TypeChecker_Env.should_verify env)
in (FStar_All.pipe_left Prims.op_Negation _157_415)) then begin
f
end else begin
(let _157_416 = (reason ())
in (label _157_416 r f))
end
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let _58_807 = g
in (let _157_424 = (let _157_423 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_157_423))
in {FStar_TypeChecker_Env.guard_f = _157_424; FStar_TypeChecker_Env.deferred = _58_807.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_807.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_807.FStar_TypeChecker_Env.implicits}))
end))


let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| _58_818 -> begin
g2
end))


let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun _58_823 -> (match (()) with
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

let _58_832 = (destruct_comp c)
in (match (_58_832) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let wp = (let _157_443 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assume_p)
in (let _157_442 = (let _157_441 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _157_440 = (let _157_439 = (FStar_Syntax_Syntax.as_arg f)
in (let _157_438 = (let _157_437 = (FStar_Syntax_Syntax.as_arg wp)
in (_157_437)::[])
in (_157_439)::_157_438))
in (_157_441)::_157_440))
in (FStar_Syntax_Syntax.mk_Tm_app _157_443 _157_442 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md u_res_t res_t wp c.FStar_Syntax_Syntax.flags)))
end)))
end
end)
end)
end))
in (

let _58_835 = lc
in {FStar_Syntax_Syntax.eff_name = _58_835.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _58_835.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _58_835.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))


let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> if (FStar_TypeChecker_Rel.is_trivial g0) then begin
((lc), (g0))
end else begin
(

let _58_842 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _157_463 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _157_462 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _157_463 _157_462)))
end else begin
()
end
in (

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _58_2 -> (match (_58_2) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _58_848 -> begin
[]
end))))
in (

let strengthen = (fun _58_851 -> (match (()) with
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

let xret = (let _157_468 = (let _157_467 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _157_467))
in (FStar_Syntax_Util.comp_set_flags _157_468 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (

let lc = (bind e.FStar_Syntax_Syntax.pos env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) ((Some (x)), ((FStar_Syntax_Util.lcomp_of_comp xret))))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (

let _58_861 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _157_470 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _157_469 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _157_470 _157_469)))
end else begin
()
end
in (

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _58_867 = (destruct_comp c)
in (match (_58_867) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let wp = (let _157_479 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assert_p)
in (let _157_478 = (let _157_477 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _157_476 = (let _157_475 = (let _157_472 = (let _157_471 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason _157_471 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _157_472))
in (let _157_474 = (let _157_473 = (FStar_Syntax_Syntax.as_arg wp)
in (_157_473)::[])
in (_157_475)::_157_474))
in (_157_477)::_157_476))
in (FStar_Syntax_Syntax.mk_Tm_app _157_479 _157_478 None wp.FStar_Syntax_Syntax.pos)))
in (

let _58_870 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _157_480 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _157_480))
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
in (let _157_484 = (

let _58_873 = lc
in (let _157_483 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _157_482 = if ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _157_481 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _157_481))) then begin
flags
end else begin
[]
end
in {FStar_Syntax_Syntax.eff_name = _157_483; FStar_Syntax_Syntax.res_typ = _58_873.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _157_482; FStar_Syntax_Syntax.comp = strengthen})))
in ((_157_484), ((

let _58_875 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_875.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_875.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_875.FStar_TypeChecker_Env.implicits})))))))
end)


let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env comp res_t -> (

let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let y = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let _58_885 = (let _157_492 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _157_491 = (FStar_Syntax_Syntax.bv_to_name y)
in ((_157_492), (_157_491))))
in (match (_58_885) with
| (xexp, yexp) -> begin
(

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let yret = (let _157_497 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.ret_wp)
in (let _157_496 = (let _157_495 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _157_494 = (let _157_493 = (FStar_Syntax_Syntax.as_arg yexp)
in (_157_493)::[])
in (_157_495)::_157_494))
in (FStar_Syntax_Syntax.mk_Tm_app _157_497 _157_496 None res_t.FStar_Syntax_Syntax.pos)))
in (

let x_eq_y_yret = (let _157_505 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _157_504 = (let _157_503 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _157_502 = (let _157_501 = (let _157_498 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _157_498))
in (let _157_500 = (let _157_499 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_157_499)::[])
in (_157_501)::_157_500))
in (_157_503)::_157_502))
in (FStar_Syntax_Syntax.mk_Tm_app _157_505 _157_504 None res_t.FStar_Syntax_Syntax.pos)))
in (

let forall_y_x_eq_y_yret = (let _157_515 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::(u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _157_514 = (let _157_513 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _157_512 = (let _157_511 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _157_510 = (let _157_509 = (let _157_508 = (let _157_507 = (let _157_506 = (FStar_Syntax_Syntax.mk_binder y)
in (_157_506)::[])
in (FStar_Syntax_Util.abs _157_507 x_eq_y_yret (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _157_508))
in (_157_509)::[])
in (_157_511)::_157_510))
in (_157_513)::_157_512))
in (FStar_Syntax_Syntax.mk_Tm_app _157_515 _157_514 None res_t.FStar_Syntax_Syntax.pos)))
in (

let lc2 = (mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (

let lc = (let _157_516 = (FStar_TypeChecker_Env.get_range env)
in (bind _157_516 env None (FStar_Syntax_Util.lcomp_of_comp comp) ((Some (x)), ((FStar_Syntax_Util.lcomp_of_comp lc2)))))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))


let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (

let joined_eff = (join_lcomp env lcomp_then lcomp_else)
in (

let comp = (fun _58_898 -> (match (()) with
| () -> begin
if (env.FStar_TypeChecker_Env.lax && false) then begin
(

let u_t = (env.FStar_TypeChecker_Env.universe_of env lcomp_then.FStar_Syntax_Syntax.res_typ)
in (lax_mk_tot_or_comp_l joined_eff u_t lcomp_then.FStar_Syntax_Syntax.res_typ []))
end else begin
(

let _58_916 = (let _157_528 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _157_527 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _157_528 _157_527)))
in (match (_58_916) with
| ((md, _58_902, _58_904), (u_res_t, res_t, wp_then), (_58_911, _58_913, wp_else)) -> begin
(

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _157_548 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (let _157_547 = (let _157_545 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _157_544 = (let _157_543 = (FStar_Syntax_Syntax.as_arg g)
in (let _157_542 = (let _157_541 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _157_540 = (let _157_539 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_157_539)::[])
in (_157_541)::_157_540))
in (_157_543)::_157_542))
in (_157_545)::_157_544))
in (let _157_546 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _157_548 _157_547 None _157_546)))))
in (

let wp = (ifthenelse md res_t guard wp_then wp_else)
in if ((FStar_Options.split_cases ()) > (Prims.parse_int "0")) then begin
(

let comp = (mk_comp md u_res_t res_t wp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(

let wp = (let _157_553 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (let _157_552 = (let _157_551 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _157_550 = (let _157_549 = (FStar_Syntax_Syntax.as_arg wp)
in (_157_549)::[])
in (_157_551)::_157_550))
in (FStar_Syntax_Syntax.mk_Tm_app _157_553 _157_552 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md u_res_t res_t wp []))
end))
end))
end
end))
in (let _157_554 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _157_554; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp}))))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (let _157_560 = (let _157_559 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid _157_559))
in (FStar_Syntax_Syntax.fvar _157_560 FStar_Syntax_Syntax.Delta_constant None)))


let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (FStar_List.fold_left (fun eff _58_935 -> (match (_58_935) with
| (_58_933, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (

let bind_cases = (fun _58_938 -> (match (()) with
| () -> begin
(

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in if (env.FStar_TypeChecker_Env.lax && false) then begin
(lax_mk_tot_or_comp_l eff u_res_t res_t [])
end else begin
(

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _157_590 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (let _157_589 = (let _157_587 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _157_586 = (let _157_585 = (FStar_Syntax_Syntax.as_arg g)
in (let _157_584 = (let _157_583 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _157_582 = (let _157_581 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_157_581)::[])
in (_157_583)::_157_582))
in (_157_585)::_157_584))
in (_157_587)::_157_586))
in (let _157_588 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _157_590 _157_589 None _157_588)))))
in (

let default_case = (

let post_k = (let _157_593 = (let _157_591 = (FStar_Syntax_Syntax.null_binder res_t)
in (_157_591)::[])
in (let _157_592 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _157_593 _157_592)))
in (

let kwp = (let _157_596 = (let _157_594 = (FStar_Syntax_Syntax.null_binder post_k)
in (_157_594)::[])
in (let _157_595 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _157_596 _157_595)))
in (

let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (

let wp = (let _157_602 = (let _157_597 = (FStar_Syntax_Syntax.mk_binder post)
in (_157_597)::[])
in (let _157_601 = (let _157_600 = (let _157_598 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Errors.exhaustiveness_check _157_598))
in (let _157_599 = (fvar_const env FStar_Syntax_Const.false_lid)
in (FStar_All.pipe_left _157_600 _157_599)))
in (FStar_Syntax_Util.abs _157_602 _157_601 (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md u_res_t res_t wp []))))))
in (

let comp = (FStar_List.fold_right (fun _58_954 celse -> (match (_58_954) with
| (g, cthen) -> begin
(

let _58_974 = (let _157_605 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _157_605 celse))
in (match (_58_974) with
| ((md, _58_958, _58_960), (_58_963, _58_965, wp_then), (_58_969, _58_971, wp_else)) -> begin
(let _157_606 = (ifthenelse md res_t g wp_then wp_else)
in (mk_comp md u_res_t res_t _157_606 []))
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

let _58_983 = (destruct_comp comp)
in (match (_58_983) with
| (_58_979, _58_981, wp) -> begin
(

let wp = (let _157_611 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (let _157_610 = (let _157_609 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _157_608 = (let _157_607 = (FStar_Syntax_Syntax.as_arg wp)
in (_157_607)::[])
in (_157_609)::_157_608))
in (FStar_Syntax_Syntax.mk_Tm_app _157_611 _157_610 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md u_res_t res_t wp []))
end))))
end)))
end)
end))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))


let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (

let close = (fun _58_989 -> (match (()) with
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

let bs = (let _157_632 = (FStar_Syntax_Syntax.mk_binder x)
in (_157_632)::[])
in (

let us = (let _157_634 = (let _157_633 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (_157_633)::[])
in (u_res)::_157_634)
in (

let wp = (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))))))
in (let _157_641 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (let _157_640 = (let _157_639 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _157_638 = (let _157_637 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _157_636 = (let _157_635 = (FStar_Syntax_Syntax.as_arg wp)
in (_157_635)::[])
in (_157_637)::_157_636))
in (_157_639)::_157_638))
in (FStar_Syntax_Syntax.mk_Tm_app _157_641 _157_640 None wp0.FStar_Syntax_Syntax.pos))))))) bvs wp0))
in (

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _58_1006 = (destruct_comp c)
in (match (_58_1006) with
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

let _58_1009 = lc
in {FStar_Syntax_Syntax.eff_name = _58_1009.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _58_1009.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _58_1009.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))


let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (

let refine = (fun _58_1015 -> (match (()) with
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
(let _157_652 = (let _157_651 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _157_650 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _157_651 _157_650)))
in (failwith _157_652))
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

let ret = (let _157_654 = (let _157_653 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _157_653 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _157_654))
in (

let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (

let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (

let c = (let _157_656 = (let _157_655 = (bind e.FStar_Syntax_Syntax.pos env None (FStar_Syntax_Util.lcomp_of_comp c) ((Some (x)), (eq_ret)))
in (_157_655.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _157_656 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
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

let _58_1027 = lc
in {FStar_Syntax_Syntax.eff_name = _58_1027.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _58_1027.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))


let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (match ((FStar_TypeChecker_Rel.sub_comp env c c')) with
| None -> begin
(let _157_668 = (let _157_667 = (let _157_666 = (FStar_TypeChecker_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _157_665 = (FStar_TypeChecker_Env.get_range env)
in ((_157_666), (_157_665))))
in FStar_Syntax_Syntax.Error (_157_667))
in (Prims.raise _157_668))
end
| Some (g) -> begin
((e), (c'), (g))
end))


let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match ((let _157_677 = (FStar_Syntax_Subst.compress t)
in _157_677.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_58_1041) -> begin
(match ((let _157_678 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _157_678.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid) -> begin
(

let _58_1045 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (

let b2t = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (

let lc = (let _157_681 = (let _157_680 = (let _157_679 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _157_679))
in ((None), (_157_680)))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) lc _157_681))
in (

let e = (let _157_683 = (let _157_682 = (FStar_Syntax_Syntax.as_arg e)
in (_157_682)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _157_683 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in ((e), (lc))))))
end
| _58_1051 -> begin
((e), (lc))
end)
end
| _58_1053 -> begin
((e), (lc))
end))


let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (

let gopt = if env.FStar_TypeChecker_Env.use_eq then begin
(let _157_692 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in ((_157_692), (false)))
end else begin
(let _157_693 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in ((_157_693), (true)))
end
in (match (gopt) with
| (None, _58_1061) -> begin
(

let _58_1063 = (FStar_TypeChecker_Rel.subtype_fail env e lc.FStar_Syntax_Syntax.res_typ t)
in ((e), ((

let _58_1065 = lc
in {FStar_Syntax_Syntax.eff_name = _58_1065.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _58_1065.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _58_1065.FStar_Syntax_Syntax.comp})), (FStar_TypeChecker_Rel.trivial_guard)))
end
| (Some (g), apply_guard) -> begin
(match ((FStar_TypeChecker_Rel.guard_form g)) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let lc = (

let _58_1072 = lc
in {FStar_Syntax_Syntax.eff_name = _58_1072.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _58_1072.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _58_1072.FStar_Syntax_Syntax.comp})
in ((e), (lc), (g)))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let g = (

let _58_1077 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_1077.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_1077.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_1077.FStar_TypeChecker_Env.implicits})
in (

let strengthen = (fun _58_1081 -> (match (()) with
| () -> begin
if (env.FStar_TypeChecker_Env.lax && false) then begin
(lc.FStar_Syntax_Syntax.comp ())
end else begin
(

let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (match ((let _157_696 = (FStar_Syntax_Subst.compress f)
in _157_696.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_58_1084, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _58_1090; FStar_Syntax_Syntax.pos = _58_1088; FStar_Syntax_Syntax.vars = _58_1086}, _58_1095) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
(

let lc = (

let _58_1098 = lc
in {FStar_Syntax_Syntax.eff_name = _58_1098.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _58_1098.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _58_1098.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| _58_1102 -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let _58_1104 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _157_700 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _157_699 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _157_698 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _157_697 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _157_700 _157_699 _157_698 _157_697)))))
end else begin
()
end
in (

let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _58_1109 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_58_1109) with
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

let _58_1119 = (destruct_comp ct)
in (match (_58_1119) with
| (u_t, _58_1116, _58_1118) -> begin
(

let wp = (let _157_705 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.ret_wp)
in (let _157_704 = (let _157_703 = (FStar_Syntax_Syntax.as_arg t)
in (let _157_702 = (let _157_701 = (FStar_Syntax_Syntax.as_arg xexp)
in (_157_701)::[])
in (_157_703)::_157_702))
in (FStar_Syntax_Syntax.mk_Tm_app _157_705 _157_704 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)))
in (

let cret = (let _157_706 = (mk_comp md u_t t wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _157_706))
in (

let guard = if apply_guard then begin
(let _157_708 = (let _157_707 = (FStar_Syntax_Syntax.as_arg xexp)
in (_157_707)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _157_708 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end else begin
f
end
in (

let _58_1125 = (let _157_716 = (FStar_All.pipe_left (fun _157_713 -> Some (_157_713)) (FStar_TypeChecker_Errors.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _157_715 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _157_714 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _157_716 _157_715 e cret _157_714))))
in (match (_58_1125) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x = (

let _58_1126 = x
in {FStar_Syntax_Syntax.ppname = _58_1126.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1126.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (

let c = (let _157_718 = (let _157_717 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _157_717))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) _157_718 ((Some (x)), (eq_ret))))
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let _58_1131 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _157_719 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _157_719))
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
| _58_1138 -> begin
[]
end))))
in (

let lc = (

let _58_1140 = lc
in (let _157_721 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _157_721; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (

let g = (

let _58_1143 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_1143.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_1143.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_1143.FStar_TypeChecker_Env.implicits})
in ((e), (lc), (g)))))))
end)
end)))


let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _157_733 = (let _157_732 = (let _157_731 = (let _157_730 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _157_730))
in (_157_731)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _157_732 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _157_733))))
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
| ((req, _58_1171))::((ens, _58_1166))::_58_1163 -> begin
(let _157_739 = (let _157_736 = (norm req)
in Some (_157_736))
in (let _157_738 = (let _157_737 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _157_737))
in ((_157_739), (_157_738))))
end
| _58_1175 -> begin
(let _157_743 = (let _157_742 = (let _157_741 = (let _157_740 = (FStar_Syntax_Print.comp_to_string comp)
in (FStar_Util.format1 "Effect constructor is not fully applied; got %s" _157_740))
in ((_157_741), (comp.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_157_742))
in (Prims.raise _157_743))
end)
end else begin
(

let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| ((wp, _58_1181))::_58_1178 -> begin
(

let _58_1187 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (_58_1187) with
| (us_r, _58_1186) -> begin
(

let _58_1191 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (_58_1191) with
| (us_e, _58_1190) -> begin
(

let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (

let as_req = (let _157_744 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.as_requires r) FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.mk_Tm_uinst _157_744 us_r))
in (

let as_ens = (let _157_745 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.as_ensures r) FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.mk_Tm_uinst _157_745 us_e))
in (

let req = (let _157_748 = (let _157_747 = (let _157_746 = (FStar_Syntax_Syntax.as_arg wp)
in (_157_746)::[])
in (((ct.FStar_Syntax_Syntax.result_typ), (Some (FStar_Syntax_Syntax.imp_tag))))::_157_747)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _157_748 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let ens = (let _157_751 = (let _157_750 = (let _157_749 = (FStar_Syntax_Syntax.as_arg wp)
in (_157_749)::[])
in (((ct.FStar_Syntax_Syntax.result_typ), (Some (FStar_Syntax_Syntax.imp_tag))))::_157_750)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _157_751 None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _157_755 = (let _157_752 = (norm req)
in Some (_157_752))
in (let _157_754 = (let _157_753 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm _157_753))
in ((_157_755), (_157_754)))))))))
end))
end))
end
| _58_1198 -> begin
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
(match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _58_1209 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_1209) with
| (bs, c) -> begin
(

let rec aux = (fun subst _58_4 -> (match (_58_4) with
| ((x, Some (FStar_Syntax_Syntax.Implicit (dot))))::rest -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let _58_1225 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t)
in (match (_58_1225) with
| (v, _58_1223, g) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (v))))::subst
in (

let _58_1231 = (aux subst rest)
in (match (_58_1231) with
| (args, bs, subst, g') -> begin
(let _157_766 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((v), (Some (FStar_Syntax_Syntax.Implicit (dot)))))::args), (bs), (subst), (_157_766)))
end)))
end)))
end
| bs -> begin
(([]), (bs), (subst), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (

let _58_1237 = (aux [] bs)
in (match (_58_1237) with
| (args, bs, subst, guard) -> begin
(match (((args), (bs))) with
| ([], _58_1240) -> begin
((e), (torig), (guard))
end
| (_58_1243, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
((e), (torig), (FStar_TypeChecker_Rel.trivial_guard))
end
| _58_1247 -> begin
(

let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _58_1250 -> begin
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
| _58_1255 -> begin
((e), (t), (FStar_TypeChecker_Rel.trivial_guard))
end)
end))


let string_of_univs = (fun univs -> (let _157_771 = (let _157_770 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _157_770 (FStar_List.map (fun u -> (let _157_769 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _157_769 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _157_771 (FStar_String.concat ", "))))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(

let s = (let _157_777 = (let _157_776 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _157_776))
in (FStar_All.pipe_right _157_777 FStar_Util.set_elements))
in (

let _58_1261 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _157_779 = (let _157_778 = (FStar_TypeChecker_Env.univ_vars env)
in (string_of_univs _157_778))
in (FStar_Util.print1 "univ_vars in env: %s\n" _157_779))
end else begin
()
end
in (

let r = (let _157_780 = (FStar_TypeChecker_Env.get_range env)
in Some (_157_780))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (

let _58_1266 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _157_785 = (let _157_782 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _157_782))
in (let _157_784 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _157_783 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _157_785 _157_784 _157_783))))
end else begin
()
end
in (

let _58_1268 = (FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))))
in u_name))))))
in u_names))))
end)


let gather_free_univnames : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env t -> (

let ctx_univnames = (FStar_TypeChecker_Env.univnames env)
in (

let tm_univnames = (FStar_Syntax_Free.univnames t)
in (

let univnames = (let _157_790 = (FStar_Util.fifo_set_difference tm_univnames ctx_univnames)
in (FStar_All.pipe_right _157_790 FStar_Util.fifo_set_elements))
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

let _58_1283 = (FStar_ST.op_Colon_Equals (Prims.snd ts).FStar_Syntax_Syntax.tk (Some (t.FStar_Syntax_Syntax.n)))
in ts)))
end))


let check_universe_generalization : FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun explicit_univ_names generalized_univ_names t -> (match (((explicit_univ_names), (generalized_univ_names))) with
| ([], _58_1290) -> begin
generalized_univ_names
end
| (_58_1293, []) -> begin
explicit_univ_names
end
| _58_1297 -> begin
(let _157_802 = (let _157_801 = (let _157_800 = (let _157_799 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "Generalized universe in a term containing explicit universe annotation : " _157_799))
in ((_157_800), (t.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_157_801))
in (Prims.raise _157_802))
end))


let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Beta)::[]) env t0)
in (

let univnames = (gather_free_univnames env t)
in (

let univs = (FStar_Syntax_Free.univs t)
in (

let _58_1303 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _157_807 = (string_of_univs univs)
in (FStar_Util.print1 "univs to gen : %s\n" _157_807))
end else begin
()
end
in (

let gen = (gen_univs env univs)
in (

let _58_1306 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _157_808 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _157_808))
end else begin
()
end
in (

let univs = (check_universe_generalization univnames gen t0)
in (

let ts = (FStar_Syntax_Subst.close_univ_vars univs t)
in (let _157_809 = (FStar_ST.read t0.FStar_Syntax_Syntax.tk)
in (maybe_set_tk ((univs), (ts)) _157_809)))))))))))


let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> if (let _157_815 = (FStar_Util.for_all (fun _58_1315 -> (match (_58_1315) with
| (_58_1313, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _157_815)) then begin
None
end else begin
(

let norm = (fun c -> (

let _58_1318 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _157_818 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _157_818))
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

let _58_1321 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _157_819 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _157_819))
end else begin
()
end
in c))))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (let _157_822 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _157_822 FStar_Util.set_elements)))
in (

let _58_1337 = (let _157_824 = (FStar_All.pipe_right ecs (FStar_List.map (fun _58_1328 -> (match (_58_1328) with
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
in (FStar_All.pipe_right _157_824 FStar_List.unzip))
in (match (_58_1337) with
| (univs, uvars) -> begin
(

let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (

let gen_univs = (gen_univs env univs)
in (

let _58_1341 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end else begin
()
end
in (

let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _58_1346 -> (match (_58_1346) with
| (uvs, e, c) -> begin
(

let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _58_1349 -> (match (_58_1349) with
| (u, k) -> begin
(match ((FStar_Unionfind.find u)) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
((a), (Some (FStar_Syntax_Syntax.imp_tag)))
end
| FStar_Syntax_Syntax.Fixed (_58_1383) -> begin
(failwith "Unexpected instantiation of mutually recursive uvar")
end
| _58_1386 -> begin
(

let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (

let _58_1390 = (FStar_Syntax_Util.arrow_formals k)
in (match (_58_1390) with
| (bs, kres) -> begin
(

let a = (let _157_830 = (let _157_829 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _157_828 -> Some (_157_828)) _157_829))
in (FStar_Syntax_Syntax.new_bv _157_830 kres))
in (

let t = (let _157_835 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _157_834 = (let _157_833 = (let _157_832 = (let _157_831 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _157_831))
in FStar_Util.Inl (_157_832))
in Some (_157_833))
in (FStar_Syntax_Util.abs bs _157_835 _157_834)))
in (

let _58_1393 = (FStar_Syntax_Util.set_uvar u t)
in ((a), (Some (FStar_Syntax_Syntax.imp_tag))))))
end)))
end)
end))))
in (

let _58_1425 = (match (((tvars), (gen_univs))) with
| ([], []) -> begin
((e), (c))
end
| ([], _58_1401) -> begin
(

let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
in (

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env e)
in ((e), (c))))
end
| _58_1406 -> begin
(

let _58_1409 = ((e), (c))
in (match (_58_1409) with
| (e0, c0) -> begin
(

let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
in (

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Iota))::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env e)
in (

let t = (match ((let _157_836 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _157_836.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(

let _58_1418 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (_58_1418) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| _58_1420 -> begin
(FStar_Syntax_Util.arrow tvars c)
end)
in (

let e' = (FStar_Syntax_Util.abs tvars e (Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp c)))))
in (let _157_837 = (FStar_Syntax_Syntax.mk_Total t)
in ((e'), (_157_837)))))))
end))
end)
in (match (_58_1425) with
| (e, c) -> begin
((gen_univs), (e), (c))
end)))
end))))
in Some (ecs)))))
end)))))
end)


let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> (

let _58_1435 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _157_844 = (let _157_843 = (FStar_List.map (fun _58_1434 -> (match (_58_1434) with
| (lb, _58_1431, _58_1433) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _157_843 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _157_844))
end else begin
()
end
in (

let univnames_lecs = (FStar_List.map (fun _58_1440 -> (match (_58_1440) with
| (l, t, c) -> begin
(gather_free_univnames env t)
end)) lecs)
in (

let generalized_lecs = (match ((let _157_847 = (FStar_All.pipe_right lecs (FStar_List.map (fun _58_1446 -> (match (_58_1446) with
| (_58_1443, e, c) -> begin
((e), (c))
end))))
in (gen env _157_847))) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun _58_1451 -> (match (_58_1451) with
| (l, t, c) -> begin
((l), ([]), (t), (c))
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _58_1459 _58_1463 -> (match (((_58_1459), (_58_1463))) with
| ((l, _58_1456, _58_1458), (us, e, c)) -> begin
(

let _58_1464 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _157_854 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _157_853 = (FStar_Syntax_Print.lbname_to_string l)
in (let _157_852 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (let _157_851 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print4 "(%s) Generalized %s at type %s\n%s\n" _157_854 _157_853 _157_852 _157_851)))))
end else begin
()
end
in ((l), (us), (e), (c)))
end)) lecs ecs)
end)
in (FStar_List.map2 (fun univnames _58_1472 -> (match (_58_1472) with
| (l, generalized_univs, t, c) -> begin
(let _157_857 = (check_universe_generalization univnames generalized_univs t)
in ((l), (_157_857), (t), (c)))
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
(let _157_873 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _157_872 -> Some (_157_872)) _157_873))
end)
end)
in (

let is_var = (fun e -> (match ((let _157_876 = (FStar_Syntax_Subst.compress e)
in _157_876.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (_58_1488) -> begin
true
end
| _58_1491 -> begin
false
end))
in (

let decorate = (fun e t -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((

let _58_1498 = x
in {FStar_Syntax_Syntax.ppname = _58_1498.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1498.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| _58_1501 -> begin
(

let _58_1502 = e
in (let _157_881 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _58_1502.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _157_881; FStar_Syntax_Syntax.pos = _58_1502.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_1502.FStar_Syntax_Syntax.vars}))
end)))
in (

let env = (

let _58_1504 = env
in (let _157_882 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _58_1504.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1504.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1504.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1504.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1504.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1504.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1504.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1504.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1504.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1504.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1504.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1504.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1504.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1504.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1504.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _157_882; FStar_TypeChecker_Env.is_iface = _58_1504.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1504.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1504.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_1504.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_1504.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1504.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1504.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1504.FStar_TypeChecker_Env.qname_and_index}))
in (match ((check env t1 t2)) with
| None -> begin
(let _157_886 = (let _157_885 = (let _157_884 = (FStar_TypeChecker_Errors.expected_expression_of_type env t2 e t1)
in (let _157_883 = (FStar_TypeChecker_Env.get_range env)
in ((_157_884), (_157_883))))
in FStar_Syntax_Syntax.Error (_157_885))
in (Prims.raise _157_886))
end
| Some (g) -> begin
(

let _58_1510 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _157_887 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _157_887))
end else begin
()
end
in (let _157_888 = (decorate e t2)
in ((_157_888), (g))))
end)))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (

let discharge = (fun g -> (

let _58_1517 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _157_898 = (discharge g)
in (let _157_897 = (lc.FStar_Syntax_Syntax.comp ())
in ((_157_898), (_157_897))))
end else begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let steps = (FStar_TypeChecker_Normalize.Beta)::[]
in (

let c = (let _157_901 = (let _157_900 = (let _157_899 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (FStar_All.pipe_right _157_899 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right _157_900 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (FStar_All.pipe_right _157_901 (FStar_TypeChecker_Normalize.comp_to_comp_typ env)))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let _58_1527 = (destruct_comp c)
in (match (_58_1527) with
| (u_t, t, wp) -> begin
(

let vc = (let _157_907 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.trivial)
in (let _157_906 = (let _157_904 = (FStar_Syntax_Syntax.as_arg t)
in (let _157_903 = (let _157_902 = (FStar_Syntax_Syntax.as_arg wp)
in (_157_902)::[])
in (_157_904)::_157_903))
in (let _157_905 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk_Tm_app _157_907 _157_906 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _157_905))))
in (

let _58_1529 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _157_908 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _157_908))
end else begin
()
end
in (

let g = (let _157_909 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _157_909))
in (let _157_911 = (discharge g)
in (let _157_910 = (FStar_Syntax_Syntax.mk_Comp c)
in ((_157_911), (_157_910)))))))
end))))))
end)))


let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (

let short_bin_op = (fun f _58_6 -> (match (_58_6) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((fst, _58_1540))::[] -> begin
(f fst)
end
| _58_1544 -> begin
(failwith "Unexpexted args to binary operator")
end))
in (

let op_and_e = (fun e -> (let _157_932 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _157_932 (fun _157_931 -> FStar_TypeChecker_Common.NonTrivial (_157_931)))))
in (

let op_or_e = (fun e -> (let _157_937 = (let _157_935 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _157_935))
in (FStar_All.pipe_right _157_937 (fun _157_936 -> FStar_TypeChecker_Common.NonTrivial (_157_936)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _157_940 -> FStar_TypeChecker_Common.NonTrivial (_157_940))))
in (

let op_or_t = (fun t -> (let _157_944 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _157_944 (fun _157_943 -> FStar_TypeChecker_Common.NonTrivial (_157_943)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _157_947 -> FStar_TypeChecker_Common.NonTrivial (_157_947))))
in (

let short_op_ite = (fun _58_7 -> (match (_58_7) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((guard, _58_1559))::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| (_then)::((guard, _58_1564))::[] -> begin
(let _157_951 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _157_951 (fun _157_950 -> FStar_TypeChecker_Common.NonTrivial (_157_950))))
end
| _58_1569 -> begin
(failwith "Unexpected args to ITE")
end))
in (

let table = (((FStar_Syntax_Const.op_And), ((short_bin_op op_and_e))))::(((FStar_Syntax_Const.op_Or), ((short_bin_op op_or_e))))::(((FStar_Syntax_Const.and_lid), ((short_bin_op op_and_t))))::(((FStar_Syntax_Const.or_lid), ((short_bin_op op_or_t))))::(((FStar_Syntax_Const.imp_lid), ((short_bin_op op_imp_t))))::(((FStar_Syntax_Const.ite_lid), (short_op_ite)))::[]
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((FStar_Util.find_map table (fun _58_1577 -> (match (_58_1577) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _157_984 = (mk seen_args)
in Some (_157_984))
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
| _58_1582 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (match ((let _157_987 = (FStar_Syntax_Util.un_uinst l)
in _157_987.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| _58_1587 -> begin
false
end))


let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (

let pos = (fun bs -> (match (bs) with
| ((hd, _58_1596))::_58_1593 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| _58_1600 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| ((_58_1604, Some (FStar_Syntax_Syntax.Implicit (_58_1606))))::_58_1602 -> begin
bs
end
| _58_1612 -> begin
(match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
bs
end
| Some (t) -> begin
(match ((let _157_994 = (FStar_Syntax_Subst.compress t)
in _157_994.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', _58_1618) -> begin
(match ((FStar_Util.prefix_until (fun _58_8 -> (match (_58_8) with
| (_58_1623, Some (FStar_Syntax_Syntax.Implicit (_58_1625))) -> begin
false
end
| _58_1630 -> begin
true
end)) bs')) with
| None -> begin
bs
end
| Some ([], _58_1634, _58_1636) -> begin
bs
end
| Some (imps, _58_1641, _58_1643) -> begin
if (FStar_All.pipe_right imps (FStar_Util.for_all (fun _58_1649 -> (match (_58_1649) with
| (x, _58_1648) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end)))) then begin
(

let r = (pos bs)
in (

let imps = (FStar_All.pipe_right imps (FStar_List.map (fun _58_1653 -> (match (_58_1653) with
| (x, i) -> begin
(let _157_998 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in ((_157_998), (i)))
end))))
in (FStar_List.append imps bs)))
end else begin
bs
end
end)
end
| _58_1656 -> begin
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
(let _157_1009 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m2), (t))))))) _157_1009 e.FStar_Syntax_Syntax.pos))
end)))


let maybe_monadic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c t -> (

let m = (FStar_TypeChecker_Env.norm_eff_name env c)
in if (((is_pure_or_ghost_effect env m) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid)) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid)) then begin
e
end else begin
(let _157_1018 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))) _157_1018 e.FStar_Syntax_Syntax.pos))
end))


let effect_repr_aux = (fun only_reifiable env c u_c -> (match ((let _157_1023 = (FStar_TypeChecker_Env.norm_eff_name env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_TypeChecker_Env.effect_decl_opt env _157_1023))) with
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
| _58_1678 -> begin
(

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _58_1682 = (let _157_1024 = (FStar_List.hd c.FStar_Syntax_Syntax.effect_args)
in ((c.FStar_Syntax_Syntax.result_typ), (_157_1024)))
in (match (_58_1682) with
| (res_typ, wp) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_c)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (let _157_1030 = (let _157_1029 = (let _157_1027 = (let _157_1026 = (let _157_1025 = (FStar_Syntax_Syntax.as_arg res_typ)
in (_157_1025)::(wp)::[])
in ((repr), (_157_1026)))
in FStar_Syntax_Syntax.Tm_app (_157_1027))
in (let _157_1028 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _157_1029 None _157_1028)))
in Some (_157_1030)))
end)))
end)
end
end))


let effect_repr : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term Prims.option = (fun env c u_c -> (effect_repr_aux false env c u_c))


let reify_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term = (fun env c u_c -> (

let no_reify = (fun l -> (let _157_1048 = (let _157_1047 = (let _157_1046 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _157_1045 = (FStar_TypeChecker_Env.get_range env)
in ((_157_1046), (_157_1045))))
in FStar_Syntax_Syntax.Error (_157_1047))
in (Prims.raise _157_1048)))
in (match ((let _157_1049 = (c.FStar_Syntax_Syntax.comp ())
in (effect_repr_aux true env _157_1049 u_c))) with
| None -> begin
(no_reify c.FStar_Syntax_Syntax.eff_name)
end
| Some (tm) -> begin
tm
end)))


let d : Prims.string  ->  Prims.unit = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))


let mk_toplevel_definition : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term) = (fun env lident def -> (

let _58_1701 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _58_1699 = (d (FStar_Ident.text_of_lid lident))
in (let _157_1058 = (FStar_Syntax_Print.term_to_string def)
in (FStar_Util.print2 "Registering top-level definition: %s\n%s\n" (FStar_Ident.text_of_lid lident) _157_1058)))
end else begin
()
end
in (

let fv = (let _157_1059 = (FStar_Syntax_Util.incr_delta_qualifier def)
in (FStar_Syntax_Syntax.lid_as_fv lident _157_1059 None))
in (

let lbname = FStar_Util.Inr (fv)
in (

let lb = ((false), (({FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = def})::[]))
in (

let sig_ctx = FStar_Syntax_Syntax.Sig_let (((lb), (FStar_Range.dummyRange), ((lident)::[]), ((FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)::[]), ([])))
in (let _157_1060 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) None FStar_Range.dummyRange)
in ((sig_ctx), (_157_1060)))))))))


let check_sigelt_quals : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (

let visibility = (fun _58_9 -> (match (_58_9) with
| FStar_Syntax_Syntax.Private -> begin
true
end
| _58_1712 -> begin
false
end))
in (

let reducibility = (fun _58_10 -> (match (_58_10) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) | (FStar_Syntax_Syntax.Visible_default) | (FStar_Syntax_Syntax.Inline_for_extraction) -> begin
true
end
| _58_1721 -> begin
false
end))
in (

let assumption = (fun _58_11 -> (match (_58_11) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.New) -> begin
true
end
| _58_1727 -> begin
false
end))
in (

let reification = (fun _58_12 -> (match (_58_12) with
| (FStar_Syntax_Syntax.Reifiable) | (FStar_Syntax_Syntax.Reflectable (_)) -> begin
true
end
| _58_1735 -> begin
false
end))
in (

let inferred = (fun _58_13 -> (match (_58_13) with
| (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) | (FStar_Syntax_Syntax.ExceptionConstructor) | (FStar_Syntax_Syntax.HasMaskedEffect) | (FStar_Syntax_Syntax.Effect) -> begin
true
end
| _58_1754 -> begin
false
end))
in (

let has_eq = (fun _58_14 -> (match (_58_14) with
| (FStar_Syntax_Syntax.Noeq) | (FStar_Syntax_Syntax.Unopteq) -> begin
true
end
| _58_1760 -> begin
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
| _58_1789 -> begin
true
end))
in (

let quals = (FStar_Syntax_Util.quals_of_sigelt se)
in if (let _157_1089 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _58_15 -> (match (_58_15) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| _58_1794 -> begin
false
end))))
in (FStar_All.pipe_right _157_1089 Prims.op_Negation)) then begin
(

let r = (FStar_Syntax_Util.range_of_sigelt se)
in (

let no_dup_quals = (FStar_Util.remove_dups (fun x y -> (x = y)) quals)
in (

let err' = (fun msg -> (let _157_1097 = (let _157_1096 = (let _157_1095 = (let _157_1094 = (FStar_Syntax_Print.quals_to_string quals)
in (FStar_Util.format2 "The qualifier list \"[%s]\" is not permissible for this element%s" _157_1094 msg))
in ((_157_1095), (r)))
in FStar_Syntax_Syntax.Error (_157_1096))
in (Prims.raise _157_1097)))
in (

let err = (fun msg -> (err' (Prims.strcat ": " msg)))
in (

let err' = (fun _58_1804 -> (match (()) with
| () -> begin
(err' "")
end))
in (

let _58_1805 = if ((FStar_List.length quals) <> (FStar_List.length no_dup_quals)) then begin
(err "duplicate qualifiers")
end else begin
()
end
in (

let _58_1807 = if (not ((FStar_All.pipe_right quals (FStar_List.for_all (quals_combo_ok quals))))) then begin
(err "ill-formed combination")
end else begin
()
end
in (match (se) with
| FStar_Syntax_Syntax.Sig_let ((is_rec, _58_1811), _58_1814, _58_1816, _58_1818, _58_1820) -> begin
(

let _58_1823 = if (is_rec && (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))) then begin
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
| FStar_Syntax_Syntax.Sig_bundle (_58_1827) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.Abstract) || (inferred x)) || (visibility x)) || (has_eq x))))))) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (_58_1831) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some has_eq)) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_assume (_58_1834) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((visibility x) || (x = FStar_Syntax_Syntax.Assumption))))))) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_new_effect (_58_1838) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x))))))) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_58_1842) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x))))))) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_58_1846) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((inferred x) || (visibility x))))))) then begin
(err' ())
end else begin
()
end
end
| _58_1850 -> begin
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

let inst_tc = (let _157_1136 = (let _157_1135 = (let _157_1134 = (let _157_1133 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _157_1133))
in ((_157_1134), (inst_univs)))
in FStar_Syntax_Syntax.Tm_uinst (_157_1135))
in (FStar_Syntax_Syntax.mk _157_1136 None p))
in (

let args = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _58_1872 -> (match (_58_1872) with
| (x, imp) -> begin
(let _157_1138 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_157_1138), (imp)))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app inst_tc args None p)))
in (

let unrefined_arg_binder = (let _157_1139 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder _157_1139))
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
in (let _157_1145 = (let _157_1144 = (let _157_1143 = (FStar_Syntax_Syntax.mk_Tm_uinst disc_fvar inst_univs)
in (let _157_1142 = (let _157_1141 = (let _157_1140 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _157_1140))
in (_157_1141)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _157_1143 _157_1142 None p)))
in (FStar_Syntax_Util.b2t _157_1144))
in (FStar_Syntax_Util.refine x _157_1145)))
in (let _157_1146 = (

let _58_1880 = (projectee arg_typ)
in {FStar_Syntax_Syntax.ppname = _58_1880.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1880.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})
in (FStar_Syntax_Syntax.mk_binder _157_1146)))))
end
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (let _157_1148 = (FStar_List.map (fun _58_1887 -> (match (_58_1887) with
| (x, _58_1886) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end)) tps)
in (FStar_List.append _157_1148 fields))
in (

let imp_binders = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _58_1892 -> (match (_58_1892) with
| (x, _58_1891) -> begin
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

let only_decl = ((let _157_1150 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _157_1150)) || (let _157_1152 = (let _157_1151 = (FStar_TypeChecker_Env.current_module env)
in _157_1151.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _157_1152)))
in (

let quals = (let _157_1156 = (let _157_1155 = if (only_decl && ((FStar_All.pipe_left Prims.op_Negation env.FStar_TypeChecker_Env.is_iface) || env.FStar_TypeChecker_Env.admit)) then begin
(FStar_Syntax_Syntax.Assumption)::[]
end else begin
[]
end
in (let _157_1154 = (FStar_List.filter (fun _58_16 -> (match (_58_16) with
| FStar_Syntax_Syntax.Abstract -> begin
(not (only_decl))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| _58_1901 -> begin
false
end)) iquals)
in (FStar_List.append _157_1155 _157_1154)))
in (FStar_List.append ((FStar_Syntax_Syntax.Discriminator (lid))::if only_decl then begin
(FStar_Syntax_Syntax.Logic)::[]
end else begin
[]
end) _157_1156))
in (

let binders = (FStar_List.append imp_binders ((unrefined_arg_binder)::[]))
in (

let t = (

let bool_typ = (let _157_1158 = (let _157_1157 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _157_1157))
in (FStar_Syntax_Syntax.mk_Total _157_1158))
in (let _157_1159 = (FStar_Syntax_Util.arrow binders bool_typ)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) _157_1159)))
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((discriminator_name), (uvs), (t), (quals), ((FStar_Ident.range_of_lid discriminator_name))))
in (

let _58_1907 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes"))) then begin
(let _157_1160 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a discriminator %s\n" _157_1160))
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

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _58_1912 -> (match (_58_1912) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in if (b && (j < ntps)) then begin
(let _157_1166 = (let _157_1165 = (let _157_1164 = (let _157_1163 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in ((_157_1163), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (_157_1164))
in (pos _157_1165))
in ((_157_1166), (b)))
end else begin
(let _157_1169 = (let _157_1168 = (let _157_1167 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_157_1167))
in (pos _157_1168))
in ((_157_1169), (b)))
end)
end))))
in (

let pat_true = (let _157_1173 = (let _157_1172 = (let _157_1171 = (let _157_1170 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in ((_157_1170), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (_157_1171))
in (pos _157_1172))
in ((_157_1173), (None), (FStar_Syntax_Const.exp_true_bool)))
in (

let pat_false = (let _157_1176 = (let _157_1175 = (let _157_1174 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_157_1174))
in (pos _157_1175))
in ((_157_1176), (None), (FStar_Syntax_Const.exp_false_bool)))
in (

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst unrefined_arg_binder))
in (let _157_1182 = (let _157_1181 = (let _157_1180 = (let _157_1179 = (FStar_Syntax_Util.branch pat_true)
in (let _157_1178 = (let _157_1177 = (FStar_Syntax_Util.branch pat_false)
in (_157_1177)::[])
in (_157_1179)::_157_1178))
in ((arg_exp), (_157_1180)))
in FStar_Syntax_Syntax.Tm_match (_157_1181))
in (FStar_Syntax_Syntax.mk _157_1182 None p))))))
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

let lb = (let _157_1185 = (let _157_1183 = (FStar_Syntax_Syntax.lid_as_fv discriminator_name dd None)
in FStar_Util.Inr (_157_1183))
in (let _157_1184 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = _157_1185; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _157_1184}))
in (

let impl = (let _157_1190 = (let _157_1189 = (let _157_1188 = (let _157_1187 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _157_1187 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_157_1188)::[])
in ((((false), ((lb)::[]))), (p), (_157_1189), (quals), ([])))
in FStar_Syntax_Syntax.Sig_let (_157_1190))
in (

let _58_1925 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes"))) then begin
(let _157_1191 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a discriminator %s\n" _157_1191))
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

let subst = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _58_1935 -> (match (_58_1935) with
| (a, _58_1934) -> begin
(

let _58_1939 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (_58_1939) with
| (field_name, _58_1938) -> begin
(

let field_proj_tm = (let _157_1195 = (let _157_1194 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.fv_to_tm _157_1194))
in (FStar_Syntax_Syntax.mk_Tm_uinst _157_1195 inst_univs))
in (

let proj = (FStar_Syntax_Syntax.mk_Tm_app field_proj_tm ((arg)::[]) None p)
in FStar_Syntax_Syntax.NT (((a), (proj)))))
end))
end))))
in (

let projectors_ses = (let _157_1238 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _58_1947 -> (match (_58_1947) with
| (x, _58_1946) -> begin
(

let p = (FStar_Syntax_Syntax.range_of_bv x)
in (

let _58_1952 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (_58_1952) with
| (field_name, _58_1951) -> begin
(

let t = (let _157_1200 = (let _157_1199 = (let _157_1198 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total _157_1198))
in (FStar_Syntax_Util.arrow binders _157_1199))
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) _157_1200))
in (

let only_decl = (((let _157_1201 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _157_1201)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (let _157_1203 = (let _157_1202 = (FStar_TypeChecker_Env.current_module env)
in _157_1202.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _157_1203)))
in (

let no_decl = false
in (

let quals = (fun q -> if only_decl then begin
(let _157_1207 = (FStar_List.filter (fun _58_17 -> (match (_58_17) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| _58_1961 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::_157_1207)
end else begin
q
end)
in (

let quals = (

let iquals = (FStar_All.pipe_right iquals (FStar_List.filter (fun _58_18 -> (match (_58_18) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| _58_1966 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals)))
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), (uvs), (t), (quals), ((FStar_Ident.range_of_lid field_name))))
in (

let _58_1970 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes"))) then begin
(let _157_1209 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a projector %s\n" _157_1209))
end else begin
()
end
in if only_decl then begin
(decl)::[]
end else begin
(

let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _58_1976 -> (match (_58_1976) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in if ((i + ntps) = j) then begin
(let _157_1212 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in ((_157_1212), (b)))
end else begin
if (b && (j < ntps)) then begin
(let _157_1216 = (let _157_1215 = (let _157_1214 = (let _157_1213 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in ((_157_1213), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (_157_1214))
in (pos _157_1215))
in ((_157_1216), (b)))
end else begin
(let _157_1219 = (let _157_1218 = (let _157_1217 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_157_1217))
in (pos _157_1218))
in ((_157_1219), (b)))
end
end)
end))))
in (

let pat = (let _157_1224 = (let _157_1222 = (let _157_1221 = (let _157_1220 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in ((_157_1220), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (_157_1221))
in (pos _157_1222))
in (let _157_1223 = (FStar_Syntax_Syntax.bv_to_name projection)
in ((_157_1224), (None), (_157_1223))))
in (

let body = (let _157_1228 = (let _157_1227 = (let _157_1226 = (let _157_1225 = (FStar_Syntax_Util.branch pat)
in (_157_1225)::[])
in ((arg_exp), (_157_1226)))
in FStar_Syntax_Syntax.Tm_match (_157_1227))
in (FStar_Syntax_Syntax.mk _157_1228 None p))
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

let lb = (let _157_1231 = (let _157_1229 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (_157_1229))
in (let _157_1230 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = _157_1231; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _157_1230}))
in (

let impl = (let _157_1236 = (let _157_1235 = (let _157_1234 = (let _157_1233 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _157_1233 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_157_1234)::[])
in ((((false), ((lb)::[]))), (p), (_157_1235), (quals), ([])))
in FStar_Syntax_Syntax.Sig_let (_157_1236))
in (

let _58_1987 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes"))) then begin
(let _157_1237 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a projector %s\n" _157_1237))
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
in (FStar_All.pipe_right _157_1238 FStar_List.flatten))
in (FStar_List.append discriminator_ses projectors_ses)))))))))))))))))))


let mk_data_operations : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env tcs se -> (match (se) with
| FStar_Syntax_Syntax.Sig_datacon (constr_lid, uvs, t, typ_lid, n_typars, quals, _58_2001, r) when (not ((FStar_Ident.lid_equals constr_lid FStar_Syntax_Const.lexcons_lid))) -> begin
(

let _58_2007 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (_58_2007) with
| (univ_opening, uvs) -> begin
(

let t = (FStar_Syntax_Subst.subst univ_opening t)
in (

let _58_2012 = (FStar_Syntax_Util.arrow_formals t)
in (match (_58_2012) with
| (formals, _58_2011) -> begin
(

let _58_2039 = (

let tps_opt = (FStar_Util.find_map tcs (fun se -> if (let _157_1248 = (FStar_Util.must (FStar_Syntax_Util.lid_of_sigelt se))
in (FStar_Ident.lid_equals typ_lid _157_1248)) then begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_2015, uvs', tps, typ0, _58_2020, constrs, _58_2023, _58_2025) -> begin
(

let _58_2028 = ()
in Some (((tps), (typ0), (((FStar_List.length constrs) > (Prims.parse_int "1"))))))
end
| _58_2031 -> begin
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
in (match (_58_2039) with
| (inductive_tps, typ0, should_refine) -> begin
(

let inductive_tps = (FStar_Syntax_Subst.subst_binders univ_opening inductive_tps)
in (

let typ0 = (FStar_Syntax_Subst.subst univ_opening typ0)
in (

let _58_2045 = (FStar_Syntax_Util.arrow_formals typ0)
in (match (_58_2045) with
| (indices, _58_2044) -> begin
(

let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _58_19 -> (match (_58_19) with
| FStar_Syntax_Syntax.RecordConstructor (_58_2048) -> begin
true
end
| _58_2051 -> begin
false
end)))) then begin
false
end else begin
should_refine
end
in (

let fv_qual = (

let filter_records = (fun _58_20 -> (match (_58_20) with
| FStar_Syntax_Syntax.RecordConstructor (_58_2055, fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((constr_lid), (fns))))
end
| _58_2060 -> begin
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

let _58_2069 = (FStar_Util.first_N n_typars formals)
in (match (_58_2069) with
| (imp_tps, fields) -> begin
(

let rename = (FStar_List.map2 (fun _58_2073 _58_2077 -> (match (((_58_2073), (_58_2077))) with
| ((x, _58_2072), (x', _58_2076)) -> begin
(let _157_1255 = (let _157_1254 = (FStar_Syntax_Syntax.bv_to_name x')
in ((x), (_157_1254)))
in FStar_Syntax_Syntax.NT (_157_1255))
end)) imp_tps inductive_tps)
in (FStar_Syntax_Subst.subst_binders rename fields))
end))
in (mk_discriminator_and_indexed_projectors iquals fv_qual refine_domain env typ_lid constr_lid uvs inductive_tps indices fields)))))
end))))
end))
end)))
end))
end
| _58_2081 -> begin
[]
end))




