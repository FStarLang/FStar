
open Prims

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv Prims.option * FStar_Syntax_Syntax.lcomp)


let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _156_6 = (FStar_TypeChecker_Env.get_range env)
in (let _156_5 = (FStar_TypeChecker_Errors.failed_to_prove_specification errs)
in (FStar_TypeChecker_Errors.report _156_6 _156_5))))


let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _156_9 = (FStar_Syntax_Subst.compress t)
in _156_9.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_58_25) -> begin
true
end
| _58_28 -> begin
false
end))


let t_binders : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env -> (let _156_13 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right _156_13 (FStar_List.filter (fun _58_33 -> (match (_58_33) with
| (x, _58_32) -> begin
(is_type x.FStar_Syntax_Syntax.sort)
end))))))


let new_uvar_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun env k -> (

let bs = if ((FStar_Options.full_context_dependency ()) || (let _156_18 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _156_18))) then begin
(FStar_TypeChecker_Env.all_binders env)
end else begin
(t_binders env)
end
in (let _156_19 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Rel.new_uvar _156_19 bs k))))


let new_uvar : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env k -> (let _156_24 = (new_uvar_aux env k)
in (Prims.fst _156_24)))


let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun _58_1 -> (match (_58_1) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, _58_48); FStar_Syntax_Syntax.tk = _58_45; FStar_Syntax_Syntax.pos = _58_43; FStar_Syntax_Syntax.vars = _58_41} -> begin
uv
end
| _58_53 -> begin
(FStar_All.failwith "Impossible")
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
in (let _156_37 = (let _156_36 = (let _156_35 = (as_uvar u)
in ((reason), (env), (_156_35), (t), (k), (r)))
in (_156_36)::[])
in {FStar_TypeChecker_Env.guard_f = _58_72.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _58_72.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_72.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _156_37}))
in (let _156_40 = (let _156_39 = (let _156_38 = (as_uvar u)
in ((_156_38), (r)))
in (_156_39)::[])
in ((t), (_156_40), (g))))
end))
end))


let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun r t -> (

let uvs = (FStar_Syntax_Free.uvars t)
in if (not ((FStar_Util.set_is_empty uvs))) then begin
(

let us = (let _156_47 = (let _156_46 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun _58_81 -> (match (_58_81) with
| (x, _58_80) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) _156_46))
in (FStar_All.pipe_right _156_47 (FStar_String.concat ", ")))
in (

let _58_83 = (FStar_Options.push ())
in (

let _58_85 = (FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool (false)))
in (

let _58_87 = (FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)))
in (

let _58_89 = (let _156_49 = (let _156_48 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us _156_48))
in (FStar_TypeChecker_Errors.report r _156_49))
in (FStar_Options.pop ()))))))
end else begin
()
end))


let force_sort' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' = (fun s -> (match ((FStar_ST.read s.FStar_Syntax_Syntax.tk)) with
| None -> begin
(let _156_54 = (let _156_53 = (FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos)
in (let _156_52 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s" _156_53 _156_52)))
in (FStar_All.failwith _156_54))
end
| Some (tk) -> begin
tk
end))


let force_sort = (fun s -> (let _156_56 = (force_sort' s)
in (FStar_Syntax_Syntax.mk _156_56 None s.FStar_Syntax_Syntax.pos)))


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
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let mk_binder = (fun scope a -> (match ((let _156_65 = (FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort)
in _156_65.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _58_118 = (FStar_Syntax_Util.type_u ())
in (match (_58_118) with
| (k, _58_117) -> begin
(

let t = (let _156_66 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right _156_66 Prims.fst))
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
(let _156_74 = (FStar_Range.string_of_range r)
in (let _156_73 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _156_74 _156_73)))
end else begin
()
end
in ((FStar_Util.Inl (t)), ((check_res || check))))))
end))
end))
end
| _58_174 -> begin
(let _156_77 = (let _156_76 = (let _156_75 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _156_75 Prims.fst))
in FStar_Util.Inl (_156_76))
in ((_156_77), (false)))
end)))
in (

let _58_177 = (let _156_78 = (t_binders env)
in (aux _156_78 e))
in (match (_58_177) with
| (t, b) -> begin
(

let t = (match (t) with
| FStar_Util.Inr (c) -> begin
(let _156_82 = (let _156_81 = (let _156_80 = (let _156_79 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" _156_79))
in ((_156_80), (rng)))
in FStar_Syntax_Syntax.Error (_156_81))
in (Prims.raise _156_82))
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

let _58_213 = (let _156_95 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _156_95 t))
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
in (let _156_96 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _58_223.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_223.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _156_96}))
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
in (let _156_97 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _58_234.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_234.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _156_97}))
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

let e = (let _156_104 = (let _156_103 = (let _156_102 = (let _156_101 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (let _156_100 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app _156_101 _156_100 None p.FStar_Syntax_Syntax.p)))
in ((_156_102), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))
in FStar_Syntax_Syntax.Tm_meta (_156_103))
in (FStar_Syntax_Syntax.mk _156_104 None p.FStar_Syntax_Syntax.p))
in (let _156_107 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _156_106 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _156_105 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in ((_156_107), (_156_106), (_156_105), (env), (e), ((

let _58_269 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _58_269.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _58_269.FStar_Syntax_Syntax.p})))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (_58_272) -> begin
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

let pats = (FStar_List.map (fun _58_287 -> (match (_58_287) with
| (p, imp) -> begin
(let _156_119 = (elaborate_pat env p)
in ((_156_119), (imp)))
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

let a = (let _156_126 = (let _156_125 = (FStar_Syntax_Syntax.range_of_bv t)
in Some (_156_125))
in (FStar_Syntax_Syntax.new_bv _156_126 FStar_Syntax_Syntax.tun))
in (

let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (let _156_127 = (maybe_dot inaccessible a r)
in ((_156_127), (true)))))
end
| _58_326 -> begin
(let _156_131 = (let _156_130 = (let _156_129 = (let _156_128 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _156_128))
in ((_156_129), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))
in FStar_Syntax_Syntax.Error (_156_130))
in (Prims.raise _156_131))
end)
end))))
end
| ((f)::formals', ((p, p_imp))::pats') -> begin
(match (f) with
| (_58_337, Some (FStar_Syntax_Syntax.Implicit (_58_339))) when p_imp -> begin
(let _156_132 = (aux formals' pats')
in (((p), (true)))::_156_132)
end
| (_58_344, Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(

let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let p = (maybe_dot inaccessible a (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
in (let _156_133 = (aux formals' pats)
in (((p), (true)))::_156_133)))
end
| (_58_352, imp) -> begin
(let _156_136 = (let _156_134 = (FStar_Syntax_Syntax.is_implicit imp)
in ((p), (_156_134)))
in (let _156_135 = (aux formals' pats')
in (_156_136)::_156_135))
end)
end))
in (

let _58_355 = p
in (let _156_139 = (let _156_138 = (let _156_137 = (aux f pats)
in ((fv), (_156_137)))
in FStar_Syntax_Syntax.Pat_cons (_156_138))
in {FStar_Syntax_Syntax.v = _156_139; FStar_Syntax_Syntax.ty = _58_355.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _58_355.FStar_Syntax_Syntax.p})))
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
(let _156_148 = (let _156_147 = (let _156_146 = (FStar_TypeChecker_Errors.nonlinear_pattern_variable x)
in ((_156_146), (p.FStar_Syntax_Syntax.p)))
in FStar_Syntax_Syntax.Error (_156_147))
in (Prims.raise _156_148))
end
| _58_374 -> begin
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
(let _156_158 = (let _156_157 = (let _156_156 = (FStar_TypeChecker_Errors.disjunctive_pattern_vars a a')
in (let _156_155 = (FStar_TypeChecker_Env.get_range env)
in ((_156_156), (_156_155))))
in FStar_Syntax_Syntax.Error (_156_157))
in (Prims.raise _156_158))
end else begin
(let _156_160 = (let _156_159 = (FStar_Syntax_Syntax.as_arg arg)
in (_156_159)::args)
in (((FStar_List.append w' w)), (_156_160), ((p)::pats)))
end
end))
end)) pats (([]), ([]), ([])))
in (match (_58_405) with
| (w, args, pats) -> begin
(let _156_162 = (let _156_161 = (FStar_Syntax_Syntax.as_arg te)
in (_156_161)::args)
in (((FStar_List.append b w)), (_156_162), ((

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
(let _156_164 = (let _156_163 = (FStar_Syntax_Syntax.as_arg arg)
in (_156_163)::[])
in ((b), (_156_164), (p)))
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
(let _156_179 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v _156_179))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(

let _58_454 = if (not ((FStar_Syntax_Syntax.bv_eq x y))) then begin
(let _156_182 = (let _156_181 = (FStar_Syntax_Print.bv_to_string x)
in (let _156_180 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _156_181 _156_180)))
in (FStar_All.failwith _156_182))
end else begin
()
end
in (

let _58_456 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _156_184 = (FStar_Syntax_Print.bv_to_string x)
in (let _156_183 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _156_184 _156_183)))
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
(let _156_187 = (let _156_186 = (FStar_Syntax_Print.bv_to_string x)
in (let _156_185 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _156_186 _156_185)))
in (FStar_All.failwith _156_187))
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
(let _156_188 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _156_188))
end else begin
()
end
in (let _156_189 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv'), ([])))) _156_189)))
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
(

let _58_535 = if (let _156_190 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right _156_190 Prims.op_Negation)) then begin
(let _156_191 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _156_191))
end else begin
()
end
in (

let fv = fv'
in (

let rec match_args = (fun matched_pats args argpats -> (match (((args), (argpats))) with
| ([], []) -> begin
(let _156_198 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev matched_pats))))) _156_198))
end
| ((arg)::args, ((argpat, _58_551))::argpats) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e, Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (_58_561)) -> begin
(

let x = (let _156_199 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _156_199))
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e)))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args argpats)))
end
| ((e, imp), _58_570) -> begin
(

let pat = (let _156_201 = (aux argpat e)
in (let _156_200 = (FStar_Syntax_Syntax.is_implicit imp)
in ((_156_201), (_156_200))))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _58_574 -> begin
(let _156_204 = (let _156_203 = (FStar_Syntax_Print.pat_to_string p)
in (let _156_202 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _156_203 _156_202)))
in (FStar_All.failwith _156_204))
end))
in (match_args [] args argpats))))
end
| _58_576 -> begin
(let _156_209 = (let _156_208 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (let _156_207 = (FStar_Syntax_Print.pat_to_string qq)
in (let _156_206 = (let _156_205 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right _156_205 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _156_208 _156_207 _156_206))))
in (FStar_All.failwith _156_209))
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
(FStar_All.failwith "Unexpected number of patterns")
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
(let _156_217 = (let _156_216 = (FStar_Syntax_Syntax.as_implicit i)
in ((te), (_156_216)))
in ((vars), (_156_217)))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_58_602) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _156_218 = (mk (FStar_Syntax_Syntax.Tm_constant (c)))
in (([]), (_156_218)))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(let _156_219 = (mk (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (_156_219)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _58_615 = (let _156_220 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _156_220 FStar_List.unzip))
in (match (_58_615) with
| (vars, args) -> begin
(

let vars = (FStar_List.flatten vars)
in (let _156_224 = (let _156_223 = (let _156_222 = (let _156_221 = (FStar_Syntax_Syntax.fv_to_tm fv)
in ((_156_221), (args)))
in FStar_Syntax_Syntax.Tm_app (_156_222))
in (mk _156_223))
in ((vars), (_156_224))))
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
(let _156_230 = (let _156_229 = (let _156_228 = (FStar_List.map (fun _58_632 -> (match (_58_632) with
| (x, _58_631) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right _156_228 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str _156_229))
in (FStar_All.failwith _156_230))
end)
in (let _156_231 = (FStar_List.hd c.FStar_Syntax_Syntax.comp_univs)
in ((_156_231), (c.FStar_Syntax_Syntax.result_typ), (wp)))))


let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (

let _58_641 = (destruct_comp c)
in (match (_58_641) with
| (u, _58_639, wp) -> begin
(let _156_250 = (let _156_249 = (let _156_248 = (lift c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _156_248))
in (_156_249)::[])
in {FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _156_250; FStar_Syntax_Syntax.flags = []})
end)))


let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let _58_650 = (let _156_258 = (FStar_TypeChecker_Env.norm_eff_name env l1)
in (let _156_257 = (FStar_TypeChecker_Env.norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _156_258 _156_257)))
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
(let _156_272 = (destruct_comp m1)
in (let _156_271 = (destruct_comp m2)
in ((((md), (a), (kwp))), (_156_272), (_156_271))))
end)))))
end)))))


let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid))))


let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md u_result result wp flags -> (let _156_293 = (let _156_292 = (let _156_291 = (FStar_Syntax_Syntax.as_arg wp)
in (_156_291)::[])
in {FStar_Syntax_Syntax.comp_univs = (u_result)::[]; FStar_Syntax_Syntax.effect_name = md.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = _156_292; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp _156_293)))


let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (

let _58_682 = lc
in (let _156_300 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _58_682.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _156_300; FStar_Syntax_Syntax.cflags = _58_682.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _58_684 -> (match (()) with
| () -> begin
(let _156_299 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _156_299))
end))})))


let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _156_303 = (FStar_Syntax_Subst.compress t)
in _156_303.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_58_687) -> begin
true
end
| _58_690 -> begin
false
end))


let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v -> (

let c = if (let _156_310 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation _156_310)) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(

let m = (let _156_311 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must _156_311))
in (

let _58_697 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_58_697) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let u_t = (env.FStar_TypeChecker_Env.universe_of env t)
in (

let wp = (let _156_317 = (let _156_316 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env m m.FStar_Syntax_Syntax.ret_wp)
in (let _156_315 = (let _156_314 = (FStar_Syntax_Syntax.as_arg t)
in (let _156_313 = (let _156_312 = (FStar_Syntax_Syntax.as_arg v)
in (_156_312)::[])
in (_156_314)::_156_313))
in (FStar_Syntax_Syntax.mk_Tm_app _156_316 _156_315 (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _156_317))
in (mk_comp m u_t t wp ((FStar_Syntax_Syntax.RETURN)::[])))))
end)))
end
in (

let _58_702 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return"))) then begin
(let _156_320 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _156_319 = (FStar_Syntax_Print.term_to_string v)
in (let _156_318 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _156_320 _156_319 _156_318))))
end else begin
()
end
in c)))


let bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r1 env e1opt lc1 _58_710 -> (match (_58_710) with
| (b, lc2) -> begin
(

let lc1 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1)
in (

let lc2 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2)
in (

let _58_720 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(

let bstr = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _156_333 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (let _156_332 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _156_331 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" _156_333 _156_332 bstr _156_331)))))
end else begin
()
end
in (

let bind_it = (fun _58_723 -> (match (()) with
| () -> begin
(

let c1 = (lc1.FStar_Syntax_Syntax.comp ())
in (

let c2 = (lc2.FStar_Syntax_Syntax.comp ())
in (

let _58_729 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _156_340 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _156_339 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _156_338 = (FStar_Syntax_Print.comp_to_string c1)
in (let _156_337 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (let _156_336 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" _156_340 _156_339 _156_338 _156_337 _156_336))))))
end else begin
()
end
in (

let try_simplify = (fun _58_732 -> (match (()) with
| () -> begin
(

let aux = (fun _58_734 -> (match (()) with
| () -> begin
if (FStar_Syntax_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some (((c2), ("trivial no binder")))
end
| Some (_58_737) -> begin
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
(let _156_348 = (let _156_347 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in ((_156_347), (reason)))
in Some (_156_348))
end
| _58_747 -> begin
(aux ())
end))
in if ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2)) then begin
(subst_c2 "both total")
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2)) then begin
(let _156_350 = (let _156_349 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((_156_349), ("both gtot")))
in Some (_156_350))
end else begin
(match (((e1opt), (b))) with
| (Some (e), Some (x)) -> begin
if ((FStar_Syntax_Util.is_total_comp c1) && (not ((FStar_Syntax_Syntax.is_null_bv x)))) then begin
(subst_c2 "substituted e")
end else begin
(aux ())
end
end
| _58_754 -> begin
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

let _58_772 = (lift_and_destruct env c1 c2)
in (match (_58_772) with
| ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) -> begin
(

let bs = (match (b) with
| None -> begin
(let _156_351 = (FStar_Syntax_Syntax.null_binder t1)
in (_156_351)::[])
end
| Some (x) -> begin
(let _156_352 = (FStar_Syntax_Syntax.mk_binder x)
in (_156_352)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (

let r1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1))) None r1)
in (

let wp_args = (let _156_364 = (FStar_Syntax_Syntax.as_arg r1)
in (let _156_363 = (let _156_362 = (FStar_Syntax_Syntax.as_arg t1)
in (let _156_361 = (let _156_360 = (FStar_Syntax_Syntax.as_arg t2)
in (let _156_359 = (let _156_358 = (FStar_Syntax_Syntax.as_arg wp1)
in (let _156_357 = (let _156_356 = (let _156_355 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg _156_355))
in (_156_356)::[])
in (_156_358)::_156_357))
in (_156_360)::_156_359))
in (_156_362)::_156_361))
in (_156_364)::_156_363))
in (

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t2))))::[]) kwp)
in (

let wp = (let _156_365 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t1)::(u_t2)::[]) env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _156_365 wp_args None t2.FStar_Syntax_Syntax.pos))
in (

let c = (mk_comp md u_t2 t2 wp [])
in c)))))))
end))
end)))))
end))
in (let _156_366 = (join_lcomp env lc1 lc2)
in {FStar_Syntax_Syntax.eff_name = _156_366; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it})))))
end))


let lift_formula : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t mk_wp f -> (

let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (

let _58_791 = (FStar_TypeChecker_Env.wp_signature env md_pure.FStar_Syntax_Syntax.mname)
in (match (_58_791) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let wp = (let _156_378 = (let _156_377 = (FStar_Syntax_Syntax.as_arg t)
in (let _156_376 = (let _156_375 = (FStar_Syntax_Syntax.as_arg f)
in (_156_375)::[])
in (_156_377)::_156_376))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wp _156_378 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (mk_comp md_pure FStar_Syntax_Syntax.U_zero FStar_TypeChecker_Common.t_unit wp [])))
end))))


let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((f), (FStar_Syntax_Syntax.Meta_labeled (((reason), (r), (false))))))) None f.FStar_Syntax_Syntax.pos))


let label_opt : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _156_402 = (FStar_TypeChecker_Env.should_verify env)
in (FStar_All.pipe_left Prims.op_Negation _156_402)) then begin
f
end else begin
(let _156_403 = (reason ())
in (label _156_403 r f))
end
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let _58_810 = g
in (let _156_411 = (let _156_410 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_156_410))
in {FStar_TypeChecker_Env.guard_f = _156_411; FStar_TypeChecker_Env.deferred = _58_810.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_810.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_810.FStar_TypeChecker_Env.implicits}))
end))


let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| _58_821 -> begin
g2
end))


let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun _58_826 -> (match (()) with
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

let _58_835 = (destruct_comp c)
in (match (_58_835) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let wp = (let _156_430 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assume_p)
in (let _156_429 = (let _156_428 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _156_427 = (let _156_426 = (FStar_Syntax_Syntax.as_arg f)
in (let _156_425 = (let _156_424 = (FStar_Syntax_Syntax.as_arg wp)
in (_156_424)::[])
in (_156_426)::_156_425))
in (_156_428)::_156_427))
in (FStar_Syntax_Syntax.mk_Tm_app _156_430 _156_429 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md u_res_t res_t wp c.FStar_Syntax_Syntax.flags)))
end)))
end
end))
end))
in (

let _58_838 = lc
in {FStar_Syntax_Syntax.eff_name = _58_838.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _58_838.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _58_838.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))


let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> if (FStar_TypeChecker_Rel.is_trivial g0) then begin
((lc), (g0))
end else begin
(

let _58_845 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _156_450 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _156_449 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _156_450 _156_449)))
end else begin
()
end
in (

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _58_2 -> (match (_58_2) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _58_851 -> begin
[]
end))))
in (

let strengthen = (fun _58_854 -> (match (()) with
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

let xret = (let _156_455 = (let _156_454 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _156_454))
in (FStar_Syntax_Util.comp_set_flags _156_455 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (

let lc = (bind e.FStar_Syntax_Syntax.pos env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) ((Some (x)), ((FStar_Syntax_Util.lcomp_of_comp xret))))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (

let _58_864 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _156_457 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _156_456 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _156_457 _156_456)))
end else begin
()
end
in (

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _58_870 = (destruct_comp c)
in (match (_58_870) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let wp = (let _156_466 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assert_p)
in (let _156_465 = (let _156_464 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _156_463 = (let _156_462 = (let _156_459 = (let _156_458 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason _156_458 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _156_459))
in (let _156_461 = (let _156_460 = (FStar_Syntax_Syntax.as_arg wp)
in (_156_460)::[])
in (_156_462)::_156_461))
in (_156_464)::_156_463))
in (FStar_Syntax_Syntax.mk_Tm_app _156_466 _156_465 None wp.FStar_Syntax_Syntax.pos)))
in (

let _58_873 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _156_467 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _156_467))
end else begin
()
end
in (

let c2 = (mk_comp md u_res_t res_t wp flags)
in c2))))
end)))))
end)))
end))
in (let _156_471 = (

let _58_876 = lc
in (let _156_470 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _156_469 = if ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _156_468 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _156_468))) then begin
flags
end else begin
[]
end
in {FStar_Syntax_Syntax.eff_name = _156_470; FStar_Syntax_Syntax.res_typ = _58_876.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _156_469; FStar_Syntax_Syntax.comp = strengthen})))
in ((_156_471), ((

let _58_878 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _58_878.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _58_878.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _58_878.FStar_TypeChecker_Env.implicits})))))))
end)


let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env comp res_t -> (

let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let y = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let _58_888 = (let _156_479 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _156_478 = (FStar_Syntax_Syntax.bv_to_name y)
in ((_156_479), (_156_478))))
in (match (_58_888) with
| (xexp, yexp) -> begin
(

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let yret = (let _156_484 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.ret_wp)
in (let _156_483 = (let _156_482 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _156_481 = (let _156_480 = (FStar_Syntax_Syntax.as_arg yexp)
in (_156_480)::[])
in (_156_482)::_156_481))
in (FStar_Syntax_Syntax.mk_Tm_app _156_484 _156_483 None res_t.FStar_Syntax_Syntax.pos)))
in (

let x_eq_y_yret = (let _156_492 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _156_491 = (let _156_490 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _156_489 = (let _156_488 = (let _156_485 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _156_485))
in (let _156_487 = (let _156_486 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_156_486)::[])
in (_156_488)::_156_487))
in (_156_490)::_156_489))
in (FStar_Syntax_Syntax.mk_Tm_app _156_492 _156_491 None res_t.FStar_Syntax_Syntax.pos)))
in (

let forall_y_x_eq_y_yret = (let _156_502 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::(u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _156_501 = (let _156_500 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _156_499 = (let _156_498 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _156_497 = (let _156_496 = (let _156_495 = (let _156_494 = (let _156_493 = (FStar_Syntax_Syntax.mk_binder y)
in (_156_493)::[])
in (FStar_Syntax_Util.abs _156_494 x_eq_y_yret (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _156_495))
in (_156_496)::[])
in (_156_498)::_156_497))
in (_156_500)::_156_499))
in (FStar_Syntax_Syntax.mk_Tm_app _156_502 _156_501 None res_t.FStar_Syntax_Syntax.pos)))
in (

let lc2 = (mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (

let lc = (let _156_503 = (FStar_TypeChecker_Env.get_range env)
in (bind _156_503 env None (FStar_Syntax_Util.lcomp_of_comp comp) ((Some (x)), ((FStar_Syntax_Util.lcomp_of_comp lc2)))))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))


let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (

let comp = (fun _58_900 -> (match (()) with
| () -> begin
(

let _58_917 = (let _156_515 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _156_514 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _156_515 _156_514)))
in (match (_58_917) with
| ((md, _58_903, _58_905), (u_res_t, res_t, wp_then), (_58_912, _58_914, wp_else)) -> begin
(

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _156_535 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (let _156_534 = (let _156_532 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _156_531 = (let _156_530 = (FStar_Syntax_Syntax.as_arg g)
in (let _156_529 = (let _156_528 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _156_527 = (let _156_526 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_156_526)::[])
in (_156_528)::_156_527))
in (_156_530)::_156_529))
in (_156_532)::_156_531))
in (let _156_533 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _156_535 _156_534 None _156_533)))))
in (

let wp = (ifthenelse md res_t guard wp_then wp_else)
in if ((FStar_Options.split_cases ()) > (Prims.parse_int "0")) then begin
(

let comp = (mk_comp md u_res_t res_t wp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(

let wp = (let _156_540 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (let _156_539 = (let _156_538 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _156_537 = (let _156_536 = (FStar_Syntax_Syntax.as_arg wp)
in (_156_536)::[])
in (_156_538)::_156_537))
in (FStar_Syntax_Syntax.mk_Tm_app _156_540 _156_539 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md u_res_t res_t wp []))
end))
end))
end))
in (let _156_541 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _156_541; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp})))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (let _156_547 = (let _156_546 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid _156_546))
in (FStar_Syntax_Syntax.fvar _156_547 FStar_Syntax_Syntax.Delta_constant None)))


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
in (

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _156_577 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (let _156_576 = (let _156_574 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _156_573 = (let _156_572 = (FStar_Syntax_Syntax.as_arg g)
in (let _156_571 = (let _156_570 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _156_569 = (let _156_568 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_156_568)::[])
in (_156_570)::_156_569))
in (_156_572)::_156_571))
in (_156_574)::_156_573))
in (let _156_575 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _156_577 _156_576 None _156_575)))))
in (

let default_case = (

let post_k = (let _156_580 = (let _156_578 = (FStar_Syntax_Syntax.null_binder res_t)
in (_156_578)::[])
in (let _156_579 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _156_580 _156_579)))
in (

let kwp = (let _156_583 = (let _156_581 = (FStar_Syntax_Syntax.null_binder post_k)
in (_156_581)::[])
in (let _156_582 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _156_583 _156_582)))
in (

let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (

let wp = (let _156_589 = (let _156_584 = (FStar_Syntax_Syntax.mk_binder post)
in (_156_584)::[])
in (let _156_588 = (let _156_587 = (let _156_585 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Errors.exhaustiveness_check _156_585))
in (let _156_586 = (fvar_const env FStar_Syntax_Const.false_lid)
in (FStar_All.pipe_left _156_587 _156_586)))
in (FStar_Syntax_Util.abs _156_589 _156_588 (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md u_res_t res_t wp []))))))
in (

let comp = (FStar_List.fold_right (fun _58_955 celse -> (match (_58_955) with
| (g, cthen) -> begin
(

let _58_975 = (let _156_592 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _156_592 celse))
in (match (_58_975) with
| ((md, _58_959, _58_961), (_58_964, _58_966, wp_then), (_58_970, _58_972, wp_else)) -> begin
(let _156_593 = (ifthenelse md res_t g wp_then wp_else)
in (mk_comp md u_res_t res_t _156_593 []))
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

let wp = (let _156_598 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (let _156_597 = (let _156_596 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _156_595 = (let _156_594 = (FStar_Syntax_Syntax.as_arg wp)
in (_156_594)::[])
in (_156_596)::_156_595))
in (FStar_Syntax_Syntax.mk_Tm_app _156_598 _156_597 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md u_res_t res_t wp []))
end))))
end))))
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
(

let close_wp = (fun u_res md res_t bvs wp0 -> (FStar_List.fold_right (fun x wp -> (

let bs = (let _156_619 = (FStar_Syntax_Syntax.mk_binder x)
in (_156_619)::[])
in (

let us = (let _156_621 = (let _156_620 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (_156_620)::[])
in (u_res)::_156_621)
in (

let wp = (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))))))
in (let _156_628 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (let _156_627 = (let _156_626 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _156_625 = (let _156_624 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _156_623 = (let _156_622 = (FStar_Syntax_Syntax.as_arg wp)
in (_156_622)::[])
in (_156_624)::_156_623))
in (_156_626)::_156_625))
in (FStar_Syntax_Syntax.mk_Tm_app _156_628 _156_627 None wp0.FStar_Syntax_Syntax.pos))))))) bvs wp0))
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
in if (not ((is_pure_or_ghost_effect env lc.FStar_Syntax_Syntax.eff_name))) then begin
c
end else begin
if (FStar_Syntax_Util.is_partial_return c) then begin
c
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c) && (not ((FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)))) then begin
(let _156_639 = (let _156_638 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _156_637 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _156_638 _156_637)))
in (FStar_All.failwith _156_639))
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

let ret = (let _156_641 = (let _156_640 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _156_640 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _156_641))
in (

let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (

let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (

let c = (let _156_643 = (let _156_642 = (bind e.FStar_Syntax_Syntax.pos env None (FStar_Syntax_Util.lcomp_of_comp c) ((Some (x)), (eq_ret)))
in (_156_642.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _156_643 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
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
(let _156_655 = (let _156_654 = (let _156_653 = (FStar_TypeChecker_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _156_652 = (FStar_TypeChecker_Env.get_range env)
in ((_156_653), (_156_652))))
in FStar_Syntax_Syntax.Error (_156_654))
in (Prims.raise _156_655))
end
| Some (g) -> begin
((e), (c'), (g))
end))


let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match ((let _156_664 = (FStar_Syntax_Subst.compress t)
in _156_664.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_58_1042) -> begin
(match ((let _156_665 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _156_665.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid) -> begin
(

let _58_1046 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (

let b2t = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (

let lc = (let _156_668 = (let _156_667 = (let _156_666 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _156_666))
in ((None), (_156_667)))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) lc _156_668))
in (

let e = (let _156_670 = (let _156_669 = (FStar_Syntax_Syntax.as_arg e)
in (_156_669)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _156_670 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
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
(let _156_679 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in ((_156_679), (false)))
end else begin
(let _156_680 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in ((_156_680), (true)))
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
(

let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (match ((let _156_683 = (FStar_Syntax_Subst.compress f)
in _156_683.FStar_Syntax_Syntax.n)) with
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
(let _156_687 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _156_686 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _156_685 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _156_684 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _156_687 _156_686 _156_685 _156_684)))))
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

let wp = (let _156_692 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.ret_wp)
in (let _156_691 = (let _156_690 = (FStar_Syntax_Syntax.as_arg t)
in (let _156_689 = (let _156_688 = (FStar_Syntax_Syntax.as_arg xexp)
in (_156_688)::[])
in (_156_690)::_156_689))
in (FStar_Syntax_Syntax.mk_Tm_app _156_692 _156_691 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)))
in (

let cret = (let _156_693 = (mk_comp md u_t t wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _156_693))
in (

let guard = if apply_guard then begin
(let _156_695 = (let _156_694 = (FStar_Syntax_Syntax.as_arg xexp)
in (_156_694)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _156_695 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end else begin
f
end
in (

let _58_1126 = (let _156_703 = (FStar_All.pipe_left (fun _156_700 -> Some (_156_700)) (FStar_TypeChecker_Errors.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _156_702 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _156_701 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _156_703 _156_702 e cret _156_701))))
in (match (_58_1126) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x = (

let _58_1127 = x
in {FStar_Syntax_Syntax.ppname = _58_1127.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1127.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (

let c = (let _156_705 = (let _156_704 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _156_704))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) _156_705 ((Some (x)), (eq_ret))))
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let _58_1132 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _156_706 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _156_706))
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
in (let _156_708 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _156_708; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
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
in (let _156_720 = (let _156_719 = (let _156_718 = (let _156_717 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _156_717))
in (_156_718)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _156_719 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _156_720))))
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
| ((req, _58_1172))::((ens, _58_1167))::_58_1164 -> begin
(let _156_726 = (let _156_723 = (norm req)
in Some (_156_723))
in (let _156_725 = (let _156_724 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _156_724))
in ((_156_726), (_156_725))))
end
| _58_1176 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Effect constructor is not fully applied"), (comp.FStar_Syntax_Syntax.pos)))))
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

let as_req = (let _156_727 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.as_requires r) FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.mk_Tm_uinst _156_727 us_r))
in (

let as_ens = (let _156_728 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.as_ensures r) FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.mk_Tm_uinst _156_728 us_e))
in (

let req = (let _156_731 = (let _156_730 = (let _156_729 = (FStar_Syntax_Syntax.as_arg wp)
in (_156_729)::[])
in (((ct.FStar_Syntax_Syntax.result_typ), (Some (FStar_Syntax_Syntax.imp_tag))))::_156_730)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _156_731 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let ens = (let _156_734 = (let _156_733 = (let _156_732 = (FStar_Syntax_Syntax.as_arg wp)
in (_156_732)::[])
in (((ct.FStar_Syntax_Syntax.result_typ), (Some (FStar_Syntax_Syntax.imp_tag))))::_156_733)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _156_734 None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _156_738 = (let _156_735 = (norm req)
in Some (_156_735))
in (let _156_737 = (let _156_736 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm _156_736))
in ((_156_738), (_156_737)))))))))
end))
end))
end
| _58_1199 -> begin
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

let _58_1210 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_58_1210) with
| (bs, c) -> begin
(

let rec aux = (fun subst _58_4 -> (match (_58_4) with
| ((x, Some (FStar_Syntax_Syntax.Implicit (dot))))::rest -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let _58_1226 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t)
in (match (_58_1226) with
| (v, _58_1224, g) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (v))))::subst
in (

let _58_1232 = (aux subst rest)
in (match (_58_1232) with
| (args, bs, subst, g') -> begin
(let _156_749 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((v), (Some (FStar_Syntax_Syntax.Implicit (dot)))))::args), (bs), (subst), (_156_749)))
end)))
end)))
end
| bs -> begin
(([]), (bs), (subst), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (

let _58_1238 = (aux [] bs)
in (match (_58_1238) with
| (args, bs, subst, guard) -> begin
(match (((args), (bs))) with
| ([], _58_1241) -> begin
((e), (torig), (guard))
end
| (_58_1244, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
((e), (torig), (FStar_TypeChecker_Rel.trivial_guard))
end
| _58_1248 -> begin
(

let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _58_1251 -> begin
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
| _58_1256 -> begin
((e), (t), (FStar_TypeChecker_Rel.trivial_guard))
end)
end))


let string_of_univs = (fun univs -> (let _156_754 = (let _156_753 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _156_753 (FStar_List.map (fun u -> (let _156_752 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _156_752 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _156_754 (FStar_String.concat ", "))))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(

let s = (let _156_760 = (let _156_759 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _156_759))
in (FStar_All.pipe_right _156_760 FStar_Util.set_elements))
in (

let _58_1262 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _156_762 = (let _156_761 = (FStar_TypeChecker_Env.univ_vars env)
in (string_of_univs _156_761))
in (FStar_Util.print1 "univ_vars in env: %s\n" _156_762))
end else begin
()
end
in (

let r = (let _156_763 = (FStar_TypeChecker_Env.get_range env)
in Some (_156_763))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (

let _58_1267 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _156_768 = (let _156_765 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _156_765))
in (let _156_767 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _156_766 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _156_768 _156_767 _156_766))))
end else begin
()
end
in (

let _58_1269 = (FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))))
in u_name))))))
in u_names))))
end)


let gather_free_univnames : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env t -> (

let ctx_univnames = (FStar_TypeChecker_Env.univnames env)
in (

let tm_univnames = (FStar_Syntax_Free.univnames t)
in (

let univnames = (let _156_773 = (FStar_Util.fifo_set_difference tm_univnames ctx_univnames)
in (FStar_All.pipe_right _156_773 FStar_Util.fifo_set_elements))
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

let _58_1284 = (FStar_ST.op_Colon_Equals (Prims.snd ts).FStar_Syntax_Syntax.tk (Some (t.FStar_Syntax_Syntax.n)))
in ts)))
end))


let check_universe_generalization : FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun explicit_univ_names generalized_univ_names t -> (match (((explicit_univ_names), (generalized_univ_names))) with
| ([], _58_1291) -> begin
generalized_univ_names
end
| (_58_1294, []) -> begin
explicit_univ_names
end
| _58_1298 -> begin
(let _156_785 = (let _156_784 = (let _156_783 = (let _156_782 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "Generalized universe in a term containing explicit universe annotation : " _156_782))
in ((_156_783), (t.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_156_784))
in (Prims.raise _156_785))
end))


let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Beta)::[]) env t0)
in (

let univnames = (gather_free_univnames env t)
in (

let univs = (FStar_Syntax_Free.univs t)
in (

let _58_1304 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _156_790 = (string_of_univs univs)
in (FStar_Util.print1 "univs to gen : %s\n" _156_790))
end else begin
()
end
in (

let gen = (gen_univs env univs)
in (

let _58_1307 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _156_791 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _156_791))
end else begin
()
end
in (

let univs = (check_universe_generalization univnames gen t0)
in (

let ts = (FStar_Syntax_Subst.close_univ_vars univs t)
in (let _156_792 = (FStar_ST.read t0.FStar_Syntax_Syntax.tk)
in (maybe_set_tk ((univs), (ts)) _156_792)))))))))))


let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> if (let _156_798 = (FStar_Util.for_all (fun _58_1316 -> (match (_58_1316) with
| (_58_1314, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _156_798)) then begin
None
end else begin
(

let norm = (fun c -> (

let _58_1319 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _156_801 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _156_801))
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

let _58_1322 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _156_802 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _156_802))
end else begin
()
end
in c))))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (let _156_805 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _156_805 FStar_Util.set_elements)))
in (

let _58_1338 = (let _156_807 = (FStar_All.pipe_right ecs (FStar_List.map (fun _58_1329 -> (match (_58_1329) with
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
in (FStar_All.pipe_right _156_807 FStar_List.unzip))
in (match (_58_1338) with
| (univs, uvars) -> begin
(

let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (

let gen_univs = (gen_univs env univs)
in (

let _58_1342 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end else begin
()
end
in (

let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _58_1347 -> (match (_58_1347) with
| (uvs, e, c) -> begin
(

let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _58_1350 -> (match (_58_1350) with
| (u, k) -> begin
(match ((FStar_Unionfind.find u)) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
((a), (Some (FStar_Syntax_Syntax.imp_tag)))
end
| FStar_Syntax_Syntax.Fixed (_58_1384) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _58_1387 -> begin
(

let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (

let _58_1391 = (FStar_Syntax_Util.arrow_formals k)
in (match (_58_1391) with
| (bs, kres) -> begin
(

let a = (let _156_813 = (let _156_812 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _156_811 -> Some (_156_811)) _156_812))
in (FStar_Syntax_Syntax.new_bv _156_813 kres))
in (

let t = (let _156_818 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _156_817 = (let _156_816 = (let _156_815 = (let _156_814 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _156_814))
in FStar_Util.Inl (_156_815))
in Some (_156_816))
in (FStar_Syntax_Util.abs bs _156_818 _156_817)))
in (

let _58_1394 = (FStar_Syntax_Util.set_uvar u t)
in ((a), (Some (FStar_Syntax_Syntax.imp_tag))))))
end)))
end)
end))))
in (

let _58_1426 = (match (((tvars), (gen_univs))) with
| ([], []) -> begin
((e), (c))
end
| ([], _58_1402) -> begin
(

let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
in (

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env e)
in ((e), (c))))
end
| _58_1407 -> begin
(

let _58_1410 = ((e), (c))
in (match (_58_1410) with
| (e0, c0) -> begin
(

let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
in (

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Iota))::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env e)
in (

let t = (match ((let _156_819 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _156_819.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(

let _58_1419 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (_58_1419) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| _58_1421 -> begin
(FStar_Syntax_Util.arrow tvars c)
end)
in (

let e' = (FStar_Syntax_Util.abs tvars e (Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp c)))))
in (let _156_820 = (FStar_Syntax_Syntax.mk_Total t)
in ((e'), (_156_820)))))))
end))
end)
in (match (_58_1426) with
| (e, c) -> begin
((gen_univs), (e), (c))
end)))
end))))
in Some (ecs)))))
end)))))
end)


let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> (

let _58_1436 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _156_827 = (let _156_826 = (FStar_List.map (fun _58_1435 -> (match (_58_1435) with
| (lb, _58_1432, _58_1434) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _156_826 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _156_827))
end else begin
()
end
in (

let univnames_lecs = (FStar_List.map (fun _58_1441 -> (match (_58_1441) with
| (l, t, c) -> begin
(gather_free_univnames env t)
end)) lecs)
in (

let generalized_lecs = (match ((let _156_830 = (FStar_All.pipe_right lecs (FStar_List.map (fun _58_1447 -> (match (_58_1447) with
| (_58_1444, e, c) -> begin
((e), (c))
end))))
in (gen env _156_830))) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun _58_1452 -> (match (_58_1452) with
| (l, t, c) -> begin
((l), ([]), (t), (c))
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _58_1460 _58_1464 -> (match (((_58_1460), (_58_1464))) with
| ((l, _58_1457, _58_1459), (us, e, c)) -> begin
(

let _58_1465 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _156_837 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _156_836 = (FStar_Syntax_Print.lbname_to_string l)
in (let _156_835 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (let _156_834 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print4 "(%s) Generalized %s at type %s\n%s\n" _156_837 _156_836 _156_835 _156_834)))))
end else begin
()
end
in ((l), (us), (e), (c)))
end)) lecs ecs)
end)
in (FStar_List.map2 (fun univnames _58_1473 -> (match (_58_1473) with
| (l, generalized_univs, t, c) -> begin
(let _156_840 = (check_universe_generalization univnames generalized_univs t)
in ((l), (_156_840), (t), (c)))
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
(let _156_856 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _156_855 -> Some (_156_855)) _156_856))
end)
end)
in (

let is_var = (fun e -> (match ((let _156_859 = (FStar_Syntax_Subst.compress e)
in _156_859.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (_58_1489) -> begin
true
end
| _58_1492 -> begin
false
end))
in (

let decorate = (fun e t -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((

let _58_1499 = x
in {FStar_Syntax_Syntax.ppname = _58_1499.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1499.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| _58_1502 -> begin
(

let _58_1503 = e
in (let _156_864 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _58_1503.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _156_864; FStar_Syntax_Syntax.pos = _58_1503.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _58_1503.FStar_Syntax_Syntax.vars}))
end)))
in (

let env = (

let _58_1505 = env
in (let _156_865 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _58_1505.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _58_1505.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _58_1505.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _58_1505.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _58_1505.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _58_1505.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _58_1505.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _58_1505.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _58_1505.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _58_1505.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _58_1505.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _58_1505.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _58_1505.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _58_1505.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _58_1505.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _156_865; FStar_TypeChecker_Env.is_iface = _58_1505.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _58_1505.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _58_1505.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _58_1505.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _58_1505.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _58_1505.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _58_1505.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _58_1505.FStar_TypeChecker_Env.qname_and_index}))
in (match ((check env t1 t2)) with
| None -> begin
(let _156_869 = (let _156_868 = (let _156_867 = (FStar_TypeChecker_Errors.expected_expression_of_type env t2 e t1)
in (let _156_866 = (FStar_TypeChecker_Env.get_range env)
in ((_156_867), (_156_866))))
in FStar_Syntax_Syntax.Error (_156_868))
in (Prims.raise _156_869))
end
| Some (g) -> begin
(

let _58_1511 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _156_870 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _156_870))
end else begin
()
end
in (let _156_871 = (decorate e t2)
in ((_156_871), (g))))
end)))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (

let discharge = (fun g -> (

let _58_1518 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _156_881 = (discharge g)
in (let _156_880 = (lc.FStar_Syntax_Syntax.comp ())
in ((_156_881), (_156_880))))
end else begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let steps = (FStar_TypeChecker_Normalize.Beta)::[]
in (

let c = (let _156_884 = (let _156_883 = (let _156_882 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (FStar_All.pipe_right _156_882 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right _156_883 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (FStar_All.pipe_right _156_884 (FStar_TypeChecker_Normalize.comp_to_comp_typ env)))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let _58_1528 = (destruct_comp c)
in (match (_58_1528) with
| (u_t, t, wp) -> begin
(

let vc = (let _156_890 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.trivial)
in (let _156_889 = (let _156_887 = (FStar_Syntax_Syntax.as_arg t)
in (let _156_886 = (let _156_885 = (FStar_Syntax_Syntax.as_arg wp)
in (_156_885)::[])
in (_156_887)::_156_886))
in (let _156_888 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk_Tm_app _156_890 _156_889 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _156_888))))
in (

let _58_1530 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _156_891 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _156_891))
end else begin
()
end
in (

let g = (let _156_892 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _156_892))
in (let _156_894 = (discharge g)
in (let _156_893 = (FStar_Syntax_Syntax.mk_Comp c)
in ((_156_894), (_156_893)))))))
end))))))
end)))


let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (

let short_bin_op = (fun f _58_6 -> (match (_58_6) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((fst, _58_1541))::[] -> begin
(f fst)
end
| _58_1545 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (

let op_and_e = (fun e -> (let _156_915 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _156_915 (fun _156_914 -> FStar_TypeChecker_Common.NonTrivial (_156_914)))))
in (

let op_or_e = (fun e -> (let _156_920 = (let _156_918 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _156_918))
in (FStar_All.pipe_right _156_920 (fun _156_919 -> FStar_TypeChecker_Common.NonTrivial (_156_919)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _156_923 -> FStar_TypeChecker_Common.NonTrivial (_156_923))))
in (

let op_or_t = (fun t -> (let _156_927 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _156_927 (fun _156_926 -> FStar_TypeChecker_Common.NonTrivial (_156_926)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _156_930 -> FStar_TypeChecker_Common.NonTrivial (_156_930))))
in (

let short_op_ite = (fun _58_7 -> (match (_58_7) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((guard, _58_1560))::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| (_then)::((guard, _58_1565))::[] -> begin
(let _156_934 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _156_934 (fun _156_933 -> FStar_TypeChecker_Common.NonTrivial (_156_933))))
end
| _58_1570 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (

let table = (((FStar_Syntax_Const.op_And), ((short_bin_op op_and_e))))::(((FStar_Syntax_Const.op_Or), ((short_bin_op op_or_e))))::(((FStar_Syntax_Const.and_lid), ((short_bin_op op_and_t))))::(((FStar_Syntax_Const.or_lid), ((short_bin_op op_or_t))))::(((FStar_Syntax_Const.imp_lid), ((short_bin_op op_imp_t))))::(((FStar_Syntax_Const.ite_lid), (short_op_ite)))::[]
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((FStar_Util.find_map table (fun _58_1578 -> (match (_58_1578) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _156_967 = (mk seen_args)
in Some (_156_967))
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
| _58_1583 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (match ((let _156_970 = (FStar_Syntax_Util.un_uinst l)
in _156_970.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| _58_1588 -> begin
false
end))


let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (

let pos = (fun bs -> (match (bs) with
| ((hd, _58_1597))::_58_1594 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| _58_1601 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| ((_58_1605, Some (FStar_Syntax_Syntax.Implicit (_58_1607))))::_58_1603 -> begin
bs
end
| _58_1613 -> begin
(match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
bs
end
| Some (t) -> begin
(match ((let _156_977 = (FStar_Syntax_Subst.compress t)
in _156_977.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', _58_1619) -> begin
(match ((FStar_Util.prefix_until (fun _58_8 -> (match (_58_8) with
| (_58_1624, Some (FStar_Syntax_Syntax.Implicit (_58_1626))) -> begin
false
end
| _58_1631 -> begin
true
end)) bs')) with
| None -> begin
bs
end
| Some ([], _58_1635, _58_1637) -> begin
bs
end
| Some (imps, _58_1642, _58_1644) -> begin
if (FStar_All.pipe_right imps (FStar_Util.for_all (fun _58_1650 -> (match (_58_1650) with
| (x, _58_1649) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end)))) then begin
(

let r = (pos bs)
in (

let imps = (FStar_All.pipe_right imps (FStar_List.map (fun _58_1654 -> (match (_58_1654) with
| (x, i) -> begin
(let _156_981 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in ((_156_981), (i)))
end))))
in (FStar_List.append imps bs)))
end else begin
bs
end
end)
end
| _58_1657 -> begin
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
(let _156_992 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m2), (t))))))) _156_992 e.FStar_Syntax_Syntax.pos))
end)))


let maybe_monadic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c t -> (

let m = (FStar_TypeChecker_Env.norm_eff_name env c)
in if (((is_pure_or_ghost_effect env m) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid)) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid)) then begin
e
end else begin
(let _156_1001 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))) _156_1001 e.FStar_Syntax_Syntax.pos))
end))


let effect_repr_aux = (fun only_reifiable env c u_c -> (match ((let _156_1006 = (FStar_TypeChecker_Env.norm_eff_name env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_TypeChecker_Env.effect_decl_opt env _156_1006))) with
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
| _58_1679 -> begin
(

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _58_1683 = (let _156_1007 = (FStar_List.hd c.FStar_Syntax_Syntax.effect_args)
in ((c.FStar_Syntax_Syntax.result_typ), (_156_1007)))
in (match (_58_1683) with
| (res_typ, wp) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_c)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (let _156_1013 = (let _156_1012 = (let _156_1010 = (let _156_1009 = (let _156_1008 = (FStar_Syntax_Syntax.as_arg res_typ)
in (_156_1008)::(wp)::[])
in ((repr), (_156_1009)))
in FStar_Syntax_Syntax.Tm_app (_156_1010))
in (let _156_1011 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _156_1012 None _156_1011)))
in Some (_156_1013)))
end)))
end)
end
end))


let effect_repr : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term Prims.option = (fun env c u_c -> (effect_repr_aux false env c u_c))


let reify_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term = (fun env c u_c -> (

let no_reify = (fun l -> (let _156_1031 = (let _156_1030 = (let _156_1029 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _156_1028 = (FStar_TypeChecker_Env.get_range env)
in ((_156_1029), (_156_1028))))
in FStar_Syntax_Syntax.Error (_156_1030))
in (Prims.raise _156_1031)))
in (match ((let _156_1032 = (c.FStar_Syntax_Syntax.comp ())
in (effect_repr_aux true env _156_1032 u_c))) with
| None -> begin
(no_reify c.FStar_Syntax_Syntax.eff_name)
end
| Some (tm) -> begin
tm
end)))


let d : Prims.string  ->  Prims.unit = (fun s -> (FStar_Util.print1 "[01;36m%s[00m\n" s))


let mk_toplevel_definition : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term) = (fun env lident def -> (

let _58_1702 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _58_1700 = (d (FStar_Ident.text_of_lid lident))
in (let _156_1041 = (FStar_Syntax_Print.term_to_string def)
in (FStar_Util.print2 "Registering top-level definition: %s\n%s\n" (FStar_Ident.text_of_lid lident) _156_1041)))
end else begin
()
end
in (

let fv = (let _156_1042 = (FStar_Syntax_Util.incr_delta_qualifier def)
in (FStar_Syntax_Syntax.lid_as_fv lident _156_1042 None))
in (

let lbname = FStar_Util.Inr (fv)
in (

let lb = ((false), (({FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = def})::[]))
in (

let sig_ctx = FStar_Syntax_Syntax.Sig_let (((lb), (FStar_Range.dummyRange), ((lident)::[]), ((FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)::[]), ([])))
in (let _156_1043 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) None FStar_Range.dummyRange)
in ((sig_ctx), (_156_1043)))))))))


let check_sigelt_quals : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (

let visibility = (fun _58_9 -> (match (_58_9) with
| FStar_Syntax_Syntax.Private -> begin
true
end
| _58_1713 -> begin
false
end))
in (

let reducibility = (fun _58_10 -> (match (_58_10) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) | (FStar_Syntax_Syntax.Visible_default) | (FStar_Syntax_Syntax.Inline_for_extraction) -> begin
true
end
| _58_1722 -> begin
false
end))
in (

let assumption = (fun _58_11 -> (match (_58_11) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.New) -> begin
true
end
| _58_1728 -> begin
false
end))
in (

let reification = (fun _58_12 -> (match (_58_12) with
| (FStar_Syntax_Syntax.Reifiable) | (FStar_Syntax_Syntax.Reflectable (_)) -> begin
true
end
| _58_1736 -> begin
false
end))
in (

let inferred = (fun _58_13 -> (match (_58_13) with
| (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) | (FStar_Syntax_Syntax.ExceptionConstructor) | (FStar_Syntax_Syntax.HasMaskedEffect) | (FStar_Syntax_Syntax.Effect) -> begin
true
end
| _58_1755 -> begin
false
end))
in (

let has_eq = (fun _58_14 -> (match (_58_14) with
| (FStar_Syntax_Syntax.Noeq) | (FStar_Syntax_Syntax.Unopteq) -> begin
true
end
| _58_1761 -> begin
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
| _58_1790 -> begin
true
end))
in (

let quals = (FStar_Syntax_Util.quals_of_sigelt se)
in if (let _156_1072 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _58_15 -> (match (_58_15) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| _58_1795 -> begin
false
end))))
in (FStar_All.pipe_right _156_1072 Prims.op_Negation)) then begin
(

let r = (FStar_Syntax_Util.range_of_sigelt se)
in (

let no_dup_quals = (FStar_Util.remove_dups (fun x y -> (x = y)) quals)
in (

let err' = (fun msg -> (let _156_1080 = (let _156_1079 = (let _156_1078 = (let _156_1077 = (FStar_Syntax_Print.quals_to_string quals)
in (FStar_Util.format2 "The qualifier list \"[%s]\" is not permissible for this element%s" _156_1077 msg))
in ((_156_1078), (r)))
in FStar_Syntax_Syntax.Error (_156_1079))
in (Prims.raise _156_1080)))
in (

let err = (fun msg -> (err' (Prims.strcat ": " msg)))
in (

let err' = (fun _58_1805 -> (match (()) with
| () -> begin
(err' "")
end))
in (

let _58_1806 = if ((FStar_List.length quals) <> (FStar_List.length no_dup_quals)) then begin
(err "duplicate qualifiers")
end else begin
()
end
in (

let _58_1808 = if (not ((FStar_All.pipe_right quals (FStar_List.for_all (quals_combo_ok quals))))) then begin
(err "ill-formed combination")
end else begin
()
end
in (match (se) with
| FStar_Syntax_Syntax.Sig_let ((is_rec, _58_1812), _58_1815, _58_1817, _58_1819, _58_1821) -> begin
(

let _58_1824 = if (is_rec && (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))) then begin
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
| FStar_Syntax_Syntax.Sig_bundle (_58_1828) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.Abstract) || (inferred x)) || (visibility x)) || (has_eq x))))))) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (_58_1832) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some has_eq)) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_assume (_58_1835) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((visibility x) || (x = FStar_Syntax_Syntax.Assumption))))))) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_new_effect (_58_1839) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x))))))) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_58_1843) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x))))))) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_58_1847) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((inferred x) || (visibility x))))))) then begin
(err' ())
end else begin
()
end
end
| _58_1851 -> begin
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

let inst_tc = (let _156_1119 = (let _156_1118 = (let _156_1117 = (let _156_1116 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _156_1116))
in ((_156_1117), (inst_univs)))
in FStar_Syntax_Syntax.Tm_uinst (_156_1118))
in (FStar_Syntax_Syntax.mk _156_1119 None p))
in (

let args = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _58_1873 -> (match (_58_1873) with
| (x, imp) -> begin
(let _156_1121 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_156_1121), (imp)))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app inst_tc args None p)))
in (

let unrefined_arg_binder = (let _156_1122 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder _156_1122))
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
in (let _156_1128 = (let _156_1127 = (let _156_1126 = (FStar_Syntax_Syntax.mk_Tm_uinst disc_fvar inst_univs)
in (let _156_1125 = (let _156_1124 = (let _156_1123 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _156_1123))
in (_156_1124)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _156_1126 _156_1125 None p)))
in (FStar_Syntax_Util.b2t _156_1127))
in (FStar_Syntax_Util.refine x _156_1128)))
in (let _156_1129 = (

let _58_1881 = (projectee arg_typ)
in {FStar_Syntax_Syntax.ppname = _58_1881.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _58_1881.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})
in (FStar_Syntax_Syntax.mk_binder _156_1129)))))
end
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (let _156_1131 = (FStar_List.map (fun _58_1888 -> (match (_58_1888) with
| (x, _58_1887) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end)) tps)
in (FStar_List.append _156_1131 fields))
in (

let imp_binders = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _58_1893 -> (match (_58_1893) with
| (x, _58_1892) -> begin
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

let only_decl = ((let _156_1133 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _156_1133)) || (let _156_1135 = (let _156_1134 = (FStar_TypeChecker_Env.current_module env)
in _156_1134.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _156_1135)))
in (

let quals = (let _156_1139 = (let _156_1138 = if (only_decl && ((FStar_All.pipe_left Prims.op_Negation env.FStar_TypeChecker_Env.is_iface) || env.FStar_TypeChecker_Env.admit)) then begin
(FStar_Syntax_Syntax.Assumption)::[]
end else begin
[]
end
in (let _156_1137 = (FStar_List.filter (fun _58_16 -> (match (_58_16) with
| FStar_Syntax_Syntax.Abstract -> begin
(not (only_decl))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| _58_1902 -> begin
false
end)) iquals)
in (FStar_List.append _156_1138 _156_1137)))
in (FStar_List.append ((FStar_Syntax_Syntax.Discriminator (lid))::if only_decl then begin
(FStar_Syntax_Syntax.Logic)::[]
end else begin
[]
end) _156_1139))
in (

let binders = (FStar_List.append imp_binders ((unrefined_arg_binder)::[]))
in (

let t = (

let bool_typ = (let _156_1141 = (let _156_1140 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _156_1140))
in (FStar_Syntax_Syntax.mk_Total _156_1141))
in (let _156_1142 = (FStar_Syntax_Util.arrow binders bool_typ)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) _156_1142)))
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((discriminator_name), (uvs), (t), (quals), ((FStar_Ident.range_of_lid discriminator_name))))
in (

let _58_1908 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes"))) then begin
(let _156_1143 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a discriminator %s\n" _156_1143))
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

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _58_1913 -> (match (_58_1913) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in if (b && (j < ntps)) then begin
(let _156_1149 = (let _156_1148 = (let _156_1147 = (let _156_1146 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in ((_156_1146), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (_156_1147))
in (pos _156_1148))
in ((_156_1149), (b)))
end else begin
(let _156_1152 = (let _156_1151 = (let _156_1150 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_156_1150))
in (pos _156_1151))
in ((_156_1152), (b)))
end)
end))))
in (

let pat_true = (let _156_1156 = (let _156_1155 = (let _156_1154 = (let _156_1153 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in ((_156_1153), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (_156_1154))
in (pos _156_1155))
in ((_156_1156), (None), (FStar_Syntax_Const.exp_true_bool)))
in (

let pat_false = (let _156_1159 = (let _156_1158 = (let _156_1157 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_156_1157))
in (pos _156_1158))
in ((_156_1159), (None), (FStar_Syntax_Const.exp_false_bool)))
in (

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst unrefined_arg_binder))
in (let _156_1165 = (let _156_1164 = (let _156_1163 = (let _156_1162 = (FStar_Syntax_Util.branch pat_true)
in (let _156_1161 = (let _156_1160 = (FStar_Syntax_Util.branch pat_false)
in (_156_1160)::[])
in (_156_1162)::_156_1161))
in ((arg_exp), (_156_1163)))
in FStar_Syntax_Syntax.Tm_match (_156_1164))
in (FStar_Syntax_Syntax.mk _156_1165 None p))))))
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

let lb = (let _156_1168 = (let _156_1166 = (FStar_Syntax_Syntax.lid_as_fv discriminator_name dd None)
in FStar_Util.Inr (_156_1166))
in (let _156_1167 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = _156_1168; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _156_1167}))
in (

let impl = (let _156_1173 = (let _156_1172 = (let _156_1171 = (let _156_1170 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _156_1170 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_156_1171)::[])
in ((((false), ((lb)::[]))), (p), (_156_1172), (quals), ([])))
in FStar_Syntax_Syntax.Sig_let (_156_1173))
in (

let _58_1926 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes"))) then begin
(let _156_1174 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a discriminator %s\n" _156_1174))
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

let subst = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _58_1936 -> (match (_58_1936) with
| (a, _58_1935) -> begin
(

let _58_1940 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (_58_1940) with
| (field_name, _58_1939) -> begin
(

let field_proj_tm = (let _156_1178 = (let _156_1177 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.fv_to_tm _156_1177))
in (FStar_Syntax_Syntax.mk_Tm_uinst _156_1178 inst_univs))
in (

let proj = (FStar_Syntax_Syntax.mk_Tm_app field_proj_tm ((arg)::[]) None p)
in FStar_Syntax_Syntax.NT (((a), (proj)))))
end))
end))))
in (

let projectors_ses = (let _156_1221 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _58_1948 -> (match (_58_1948) with
| (x, _58_1947) -> begin
(

let p = (FStar_Syntax_Syntax.range_of_bv x)
in (

let _58_1953 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (_58_1953) with
| (field_name, _58_1952) -> begin
(

let t = (let _156_1183 = (let _156_1182 = (let _156_1181 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total _156_1181))
in (FStar_Syntax_Util.arrow binders _156_1182))
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) _156_1183))
in (

let only_decl = (((let _156_1184 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _156_1184)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (let _156_1186 = (let _156_1185 = (FStar_TypeChecker_Env.current_module env)
in _156_1185.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _156_1186)))
in (

let no_decl = false
in (

let quals = (fun q -> if only_decl then begin
(let _156_1190 = (FStar_List.filter (fun _58_17 -> (match (_58_17) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| _58_1962 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::_156_1190)
end else begin
q
end)
in (

let quals = (

let iquals = (FStar_All.pipe_right iquals (FStar_List.filter (fun _58_18 -> (match (_58_18) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| _58_1967 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals)))
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), (uvs), (t), (quals), ((FStar_Ident.range_of_lid field_name))))
in (

let _58_1971 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes"))) then begin
(let _156_1192 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a projector %s\n" _156_1192))
end else begin
()
end
in if only_decl then begin
(decl)::[]
end else begin
(

let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _58_1977 -> (match (_58_1977) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in if ((i + ntps) = j) then begin
(let _156_1195 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in ((_156_1195), (b)))
end else begin
if (b && (j < ntps)) then begin
(let _156_1199 = (let _156_1198 = (let _156_1197 = (let _156_1196 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in ((_156_1196), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (_156_1197))
in (pos _156_1198))
in ((_156_1199), (b)))
end else begin
(let _156_1202 = (let _156_1201 = (let _156_1200 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_156_1200))
in (pos _156_1201))
in ((_156_1202), (b)))
end
end)
end))))
in (

let pat = (let _156_1207 = (let _156_1205 = (let _156_1204 = (let _156_1203 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in ((_156_1203), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (_156_1204))
in (pos _156_1205))
in (let _156_1206 = (FStar_Syntax_Syntax.bv_to_name projection)
in ((_156_1207), (None), (_156_1206))))
in (

let body = (let _156_1211 = (let _156_1210 = (let _156_1209 = (let _156_1208 = (FStar_Syntax_Util.branch pat)
in (_156_1208)::[])
in ((arg_exp), (_156_1209)))
in FStar_Syntax_Syntax.Tm_match (_156_1210))
in (FStar_Syntax_Syntax.mk _156_1211 None p))
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

let lb = (let _156_1214 = (let _156_1212 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (_156_1212))
in (let _156_1213 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = _156_1214; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _156_1213}))
in (

let impl = (let _156_1219 = (let _156_1218 = (let _156_1217 = (let _156_1216 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _156_1216 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_156_1217)::[])
in ((((false), ((lb)::[]))), (p), (_156_1218), (quals), ([])))
in FStar_Syntax_Syntax.Sig_let (_156_1219))
in (

let _58_1988 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes"))) then begin
(let _156_1220 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a projector %s\n" _156_1220))
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
in (FStar_All.pipe_right _156_1221 FStar_List.flatten))
in (FStar_List.append discriminator_ses projectors_ses)))))))))))))))))))


let mk_data_operations : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env tcs se -> (match (se) with
| FStar_Syntax_Syntax.Sig_datacon (constr_lid, uvs, t, typ_lid, n_typars, quals, _58_2002, r) when (not ((FStar_Ident.lid_equals constr_lid FStar_Syntax_Const.lexcons_lid))) -> begin
(

let _58_2008 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (_58_2008) with
| (univ_opening, uvs) -> begin
(

let t = (FStar_Syntax_Subst.subst univ_opening t)
in (

let _58_2013 = (FStar_Syntax_Util.arrow_formals t)
in (match (_58_2013) with
| (formals, _58_2012) -> begin
(

let _58_2040 = (

let tps_opt = (FStar_Util.find_map tcs (fun se -> if (let _156_1231 = (FStar_Util.must (FStar_Syntax_Util.lid_of_sigelt se))
in (FStar_Ident.lid_equals typ_lid _156_1231)) then begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_58_2016, uvs', tps, typ0, _58_2021, constrs, _58_2024, _58_2026) -> begin
(

let _58_2029 = ()
in Some (((tps), (typ0), (((FStar_List.length constrs) > (Prims.parse_int "1"))))))
end
| _58_2032 -> begin
(FStar_All.failwith "Impossible")
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
in (match (_58_2040) with
| (inductive_tps, typ0, should_refine) -> begin
(

let inductive_tps = (FStar_Syntax_Subst.subst_binders univ_opening inductive_tps)
in (

let typ0 = (FStar_Syntax_Subst.subst univ_opening typ0)
in (

let _58_2046 = (FStar_Syntax_Util.arrow_formals typ0)
in (match (_58_2046) with
| (indices, _58_2045) -> begin
(

let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _58_19 -> (match (_58_19) with
| FStar_Syntax_Syntax.RecordConstructor (_58_2049) -> begin
true
end
| _58_2052 -> begin
false
end)))) then begin
false
end else begin
should_refine
end
in (

let fv_qual = (

let filter_records = (fun _58_20 -> (match (_58_20) with
| FStar_Syntax_Syntax.RecordConstructor (_58_2056, fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((constr_lid), (fns))))
end
| _58_2061 -> begin
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

let _58_2070 = (FStar_Util.first_N n_typars formals)
in (match (_58_2070) with
| (imp_tps, fields) -> begin
(

let rename = (FStar_List.map2 (fun _58_2074 _58_2078 -> (match (((_58_2074), (_58_2078))) with
| ((x, _58_2073), (x', _58_2077)) -> begin
(let _156_1238 = (let _156_1237 = (FStar_Syntax_Syntax.bv_to_name x')
in ((x), (_156_1237)))
in FStar_Syntax_Syntax.NT (_156_1238))
end)) imp_tps inductive_tps)
in (FStar_Syntax_Subst.subst_binders rename fields))
end))
in (mk_discriminator_and_indexed_projectors iquals fv_qual refine_domain env typ_lid constr_lid uvs inductive_tps indices fields)))))
end))))
end))
end)))
end))
end
| _58_2082 -> begin
[]
end))




