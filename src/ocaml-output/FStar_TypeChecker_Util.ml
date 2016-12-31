
open Prims

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv Prims.option * FStar_Syntax_Syntax.lcomp)


let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _155_6 = (FStar_TypeChecker_Env.get_range env)
in (let _155_5 = (FStar_TypeChecker_Errors.failed_to_prove_specification errs)
in (FStar_TypeChecker_Errors.report _155_6 _155_5))))


let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _155_9 = (FStar_Syntax_Subst.compress t)
in _155_9.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_25) -> begin
true
end
| _57_28 -> begin
false
end))


let t_binders : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env -> (let _155_13 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right _155_13 (FStar_List.filter (fun _57_33 -> (match (_57_33) with
| (x, _57_32) -> begin
(is_type x.FStar_Syntax_Syntax.sort)
end))))))


let new_uvar_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun env k -> (

let bs = if ((FStar_Options.full_context_dependency ()) || (let _155_18 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _155_18))) then begin
(FStar_TypeChecker_Env.all_binders env)
end else begin
(t_binders env)
end
in (let _155_19 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Rel.new_uvar _155_19 bs k))))


let new_uvar : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env k -> (let _155_24 = (new_uvar_aux env k)
in (Prims.fst _155_24)))


let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun _57_1 -> (match (_57_1) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, _57_48); FStar_Syntax_Syntax.tk = _57_45; FStar_Syntax_Syntax.pos = _57_43; FStar_Syntax_Syntax.vars = _57_41} -> begin
uv
end
| _57_53 -> begin
(FStar_All.failwith "Impossible")
end))


let new_implicit_var : Prims.string  ->  FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.uvar * FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t) = (fun reason r env k -> (match ((FStar_Syntax_Util.destruct k FStar_Syntax_Const.range_of_lid)) with
| Some ((_57_63)::((tm, _57_60))::[]) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))) None tm.FStar_Syntax_Syntax.pos)
in ((t), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
end
| _57_68 -> begin
(

let _57_71 = (new_uvar_aux env k)
in (match (_57_71) with
| (t, u) -> begin
(

let g = (

let _57_72 = FStar_TypeChecker_Rel.trivial_guard
in (let _155_37 = (let _155_36 = (let _155_35 = (as_uvar u)
in ((reason), (env), (_155_35), (t), (k), (r)))
in (_155_36)::[])
in {FStar_TypeChecker_Env.guard_f = _57_72.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_72.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_72.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _155_37}))
in (let _155_40 = (let _155_39 = (let _155_38 = (as_uvar u)
in ((_155_38), (r)))
in (_155_39)::[])
in ((t), (_155_40), (g))))
end))
end))


let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun r t -> (

let uvs = (FStar_Syntax_Free.uvars t)
in if (not ((FStar_Util.set_is_empty uvs))) then begin
(

let us = (let _155_47 = (let _155_46 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun _57_81 -> (match (_57_81) with
| (x, _57_80) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) _155_46))
in (FStar_All.pipe_right _155_47 (FStar_String.concat ", ")))
in (

let _57_83 = (FStar_Options.push ())
in (

let _57_85 = (FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool (false)))
in (

let _57_87 = (FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)))
in (

let _57_89 = (let _155_49 = (let _155_48 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us _155_48))
in (FStar_TypeChecker_Errors.report r _155_49))
in (FStar_Options.pop ()))))))
end else begin
()
end))


let force_sort' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' = (fun s -> (match ((FStar_ST.read s.FStar_Syntax_Syntax.tk)) with
| None -> begin
(let _155_54 = (let _155_53 = (FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos)
in (let _155_52 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s" _155_53 _155_52)))
in (FStar_All.failwith _155_54))
end
| Some (tk) -> begin
tk
end))


let force_sort = (fun s -> (let _155_56 = (force_sort' s)
in (FStar_Syntax_Syntax.mk _155_56 None s.FStar_Syntax_Syntax.pos)))


let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env _57_104 -> (match (_57_104) with
| {FStar_Syntax_Syntax.lbname = _57_103; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _57_99; FStar_Syntax_Syntax.lbdef = e} -> begin
(

let rng = t.FStar_Syntax_Syntax.pos
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _57_108 = if (univ_vars <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let mk_binder = (fun scope a -> (match ((let _155_65 = (FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort)
in _155_65.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _57_118 = (FStar_Syntax_Util.type_u ())
in (match (_57_118) with
| (k, _57_117) -> begin
(

let t = (let _155_66 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right _155_66 Prims.fst))
in (((

let _57_120 = a
in {FStar_Syntax_Syntax.ppname = _57_120.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_120.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (false)))
end))
end
| _57_123 -> begin
((a), (true))
end))
in (

let rec aux = (fun vars e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, _57_130) -> begin
(aux vars e)
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _57_136) -> begin
((t), (true))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _57_142) -> begin
(

let _57_161 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _57_148 _57_151 -> (match (((_57_148), (_57_151))) with
| ((scope, bs, check), (a, imp)) -> begin
(

let _57_154 = (mk_binder scope a)
in (match (_57_154) with
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
in (match (_57_161) with
| (scope, bs, check) -> begin
(

let _57_164 = (aux scope body)
in (match (_57_164) with
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

let _57_171 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _155_74 = (FStar_Range.string_of_range r)
in (let _155_73 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _155_74 _155_73)))
end else begin
()
end
in ((FStar_Util.Inl (t)), ((check_res || check))))))
end))
end))
end
| _57_174 -> begin
(let _155_77 = (let _155_76 = (let _155_75 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _155_75 Prims.fst))
in FStar_Util.Inl (_155_76))
in ((_155_77), (false)))
end)))
in (

let _57_177 = (let _155_78 = (t_binders env)
in (aux _155_78 e))
in (match (_57_177) with
| (t, b) -> begin
(

let t = (match (t) with
| FStar_Util.Inr (c) -> begin
(let _155_82 = (let _155_81 = (let _155_80 = (let _155_79 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" _155_79))
in ((_155_80), (rng)))
in FStar_Syntax_Syntax.Error (_155_81))
in (Prims.raise _155_82))
end
| FStar_Util.Inl (t) -> begin
t
end)
in (([]), (t), (b)))
end))))))
end
| _57_184 -> begin
(

let _57_187 = (FStar_Syntax_Subst.open_univ_vars univ_vars t)
in (match (_57_187) with
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
| FStar_Syntax_Syntax.Pat_dot_term (x, _57_200) -> begin
(

let _57_206 = (FStar_Syntax_Util.type_u ())
in (match (_57_206) with
| (k, _57_205) -> begin
(

let t = (new_uvar env k)
in (

let x = (

let _57_208 = x
in {FStar_Syntax_Syntax.ppname = _57_208.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_208.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let _57_213 = (let _155_95 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _155_95 t))
in (match (_57_213) with
| (e, u) -> begin
(

let p = (

let _57_214 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (e))); FStar_Syntax_Syntax.ty = _57_214.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _57_214.FStar_Syntax_Syntax.p})
in (([]), ([]), ([]), (env), (e), (p)))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let _57_222 = (FStar_Syntax_Util.type_u ())
in (match (_57_222) with
| (t, _57_221) -> begin
(

let x = (

let _57_223 = x
in (let _155_96 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _57_223.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_223.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _155_96}))
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

let _57_233 = (FStar_Syntax_Util.type_u ())
in (match (_57_233) with
| (t, _57_232) -> begin
(

let x = (

let _57_234 = x
in (let _155_97 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _57_234.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_234.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _155_97}))
in (

let env = (FStar_TypeChecker_Env.push_bv env x)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in (((x)::[]), ((x)::[]), ([]), (env), (e), (p)))))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _57_267 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _57_249 _57_252 -> (match (((_57_249), (_57_252))) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(

let _57_259 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_57_259) with
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
in (match (_57_267) with
| (b, a, w, env, args, pats) -> begin
(

let e = (let _155_104 = (let _155_103 = (let _155_102 = (let _155_101 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (let _155_100 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app _155_101 _155_100 None p.FStar_Syntax_Syntax.p)))
in ((_155_102), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))
in FStar_Syntax_Syntax.Tm_meta (_155_103))
in (FStar_Syntax_Syntax.mk _155_104 None p.FStar_Syntax_Syntax.p))
in (let _155_107 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _155_106 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _155_105 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in ((_155_107), (_155_106), (_155_105), (env), (e), ((

let _57_269 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _57_269.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _57_269.FStar_Syntax_Syntax.p})))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (_57_272) -> begin
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

let pats = (FStar_List.map (fun _57_287 -> (match (_57_287) with
| (p, imp) -> begin
(let _155_119 = (elaborate_pat env p)
in ((_155_119), (imp)))
end)) pats)
in (

let _57_292 = (FStar_TypeChecker_Env.lookup_datacon env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_57_292) with
| (_57_290, t) -> begin
(

let _57_296 = (FStar_Syntax_Util.arrow_formals t)
in (match (_57_296) with
| (f, _57_295) -> begin
(

let rec aux = (fun formals pats -> (match (((formals), (pats))) with
| ([], []) -> begin
[]
end
| ([], (_57_307)::_57_305) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Too many pattern arguments"), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))))
end
| ((_57_313)::_57_311, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun _57_319 -> (match (_57_319) with
| (t, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(

let a = (let _155_126 = (let _155_125 = (FStar_Syntax_Syntax.range_of_bv t)
in Some (_155_125))
in (FStar_Syntax_Syntax.new_bv _155_126 FStar_Syntax_Syntax.tun))
in (

let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (let _155_127 = (maybe_dot inaccessible a r)
in ((_155_127), (true)))))
end
| _57_326 -> begin
(let _155_131 = (let _155_130 = (let _155_129 = (let _155_128 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _155_128))
in ((_155_129), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))
in FStar_Syntax_Syntax.Error (_155_130))
in (Prims.raise _155_131))
end)
end))))
end
| ((f)::formals', ((p, p_imp))::pats') -> begin
(match (f) with
| (_57_337, Some (FStar_Syntax_Syntax.Implicit (_57_339))) when p_imp -> begin
(let _155_132 = (aux formals' pats')
in (((p), (true)))::_155_132)
end
| (_57_344, Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(

let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let p = (maybe_dot inaccessible a (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
in (let _155_133 = (aux formals' pats)
in (((p), (true)))::_155_133)))
end
| (_57_352, imp) -> begin
(let _155_136 = (let _155_134 = (FStar_Syntax_Syntax.is_implicit imp)
in ((p), (_155_134)))
in (let _155_135 = (aux formals' pats')
in (_155_136)::_155_135))
end)
end))
in (

let _57_355 = p
in (let _155_139 = (let _155_138 = (let _155_137 = (aux f pats)
in ((fv), (_155_137)))
in FStar_Syntax_Syntax.Pat_cons (_155_138))
in {FStar_Syntax_Syntax.v = _155_139; FStar_Syntax_Syntax.ty = _57_355.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _57_355.FStar_Syntax_Syntax.p})))
end))
end)))
end
| _57_358 -> begin
p
end)))
in (

let one_pat = (fun allow_wc_dependence env p -> (

let p = (elaborate_pat env p)
in (

let _57_370 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_57_370) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))) with
| Some (x) -> begin
(let _155_148 = (let _155_147 = (let _155_146 = (FStar_TypeChecker_Errors.nonlinear_pattern_variable x)
in ((_155_146), (p.FStar_Syntax_Syntax.p)))
in FStar_Syntax_Syntax.Error (_155_147))
in (Prims.raise _155_148))
end
| _57_374 -> begin
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

let _57_390 = (one_pat false env q)
in (match (_57_390) with
| (b, a, _57_387, te, q) -> begin
(

let _57_405 = (FStar_List.fold_right (fun p _57_395 -> (match (_57_395) with
| (w, args, pats) -> begin
(

let _57_401 = (one_pat false env p)
in (match (_57_401) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv FStar_Syntax_Syntax.bv_eq a a'))) then begin
(let _155_158 = (let _155_157 = (let _155_156 = (FStar_TypeChecker_Errors.disjunctive_pattern_vars a a')
in (let _155_155 = (FStar_TypeChecker_Env.get_range env)
in ((_155_156), (_155_155))))
in FStar_Syntax_Syntax.Error (_155_157))
in (Prims.raise _155_158))
end else begin
(let _155_160 = (let _155_159 = (FStar_Syntax_Syntax.as_arg arg)
in (_155_159)::args)
in (((FStar_List.append w' w)), (_155_160), ((p)::pats)))
end
end))
end)) pats (([]), ([]), ([])))
in (match (_57_405) with
| (w, args, pats) -> begin
(let _155_162 = (let _155_161 = (FStar_Syntax_Syntax.as_arg te)
in (_155_161)::args)
in (((FStar_List.append b w)), (_155_162), ((

let _57_406 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((q)::pats); FStar_Syntax_Syntax.ty = _57_406.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _57_406.FStar_Syntax_Syntax.p}))))
end))
end))
end
| _57_409 -> begin
(

let _57_417 = (one_pat true env p)
in (match (_57_417) with
| (b, _57_412, _57_414, arg, p) -> begin
(let _155_164 = (let _155_163 = (FStar_Syntax_Syntax.as_arg arg)
in (_155_163)::[])
in ((b), (_155_164), (p)))
end))
end))
in (

let _57_421 = (top_level_pat_as_args env p)
in (match (_57_421) with
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
| (_57_435, FStar_Syntax_Syntax.Tm_uinst (e, _57_438)) -> begin
(aux p e)
end
| (FStar_Syntax_Syntax.Pat_constant (_57_443), FStar_Syntax_Syntax.Tm_constant (_57_446)) -> begin
(let _155_179 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v _155_179))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(

let _57_454 = if (not ((FStar_Syntax_Syntax.bv_eq x y))) then begin
(let _155_182 = (let _155_181 = (FStar_Syntax_Print.bv_to_string x)
in (let _155_180 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _155_181 _155_180)))
in (FStar_All.failwith _155_182))
end else begin
()
end
in (

let _57_456 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _155_184 = (FStar_Syntax_Print.bv_to_string x)
in (let _155_183 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _155_184 _155_183)))
end else begin
()
end
in (

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x = (

let _57_459 = x
in {FStar_Syntax_Syntax.ppname = _57_459.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_459.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x)) s.FStar_Syntax_Syntax.n)))))
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(

let _57_467 = if (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation) then begin
(let _155_187 = (let _155_186 = (FStar_Syntax_Print.bv_to_string x)
in (let _155_185 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _155_186 _155_185)))
in (FStar_All.failwith _155_187))
end else begin
()
end
in (

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x = (

let _57_470 = x
in {FStar_Syntax_Syntax.ppname = _57_470.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_470.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x)) s.FStar_Syntax_Syntax.n))))
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _57_475), _57_479) -> begin
(

let s = (force_sort e)
in (

let x = (

let _57_482 = x
in {FStar_Syntax_Syntax.ppname = _57_482.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_482.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term (((x), (e)))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
(

let _57_492 = if (not ((FStar_Syntax_Syntax.fv_eq fv fv'))) then begin
(let _155_188 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _155_188))
end else begin
()
end
in (let _155_189 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv'), ([])))) _155_189)))
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
(

let _57_535 = if (let _155_190 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right _155_190 Prims.op_Negation)) then begin
(let _155_191 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _155_191))
end else begin
()
end
in (

let fv = fv'
in (

let rec match_args = (fun matched_pats args argpats -> (match (((args), (argpats))) with
| ([], []) -> begin
(let _155_198 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev matched_pats))))) _155_198))
end
| ((arg)::args, ((argpat, _57_551))::argpats) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e, Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (_57_561)) -> begin
(

let x = (let _155_199 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _155_199))
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e)))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args argpats)))
end
| ((e, imp), _57_570) -> begin
(

let pat = (let _155_201 = (aux argpat e)
in (let _155_200 = (FStar_Syntax_Syntax.is_implicit imp)
in ((_155_201), (_155_200))))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _57_574 -> begin
(let _155_204 = (let _155_203 = (FStar_Syntax_Print.pat_to_string p)
in (let _155_202 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _155_203 _155_202)))
in (FStar_All.failwith _155_204))
end))
in (match_args [] args argpats))))
end
| _57_576 -> begin
(let _155_209 = (let _155_208 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (let _155_207 = (FStar_Syntax_Print.pat_to_string qq)
in (let _155_206 = (let _155_205 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right _155_205 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _155_208 _155_207 _155_206))))
in (FStar_All.failwith _155_209))
end))))
in (match (((p.FStar_Syntax_Syntax.v), (exps))) with
| (FStar_Syntax_Syntax.Pat_disj (ps), _57_580) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(

let ps = (FStar_List.map2 aux ps exps)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj (ps)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p))
end
| (_57_584, (e)::[]) -> begin
(aux p e)
end
| _57_589 -> begin
(FStar_All.failwith "Unexpected number of patterns")
end))))


let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (

let topt = Some (pat.FStar_Syntax_Syntax.ty)
in (

let mk = (fun f -> (FStar_Syntax_Syntax.mk f topt pat.FStar_Syntax_Syntax.p))
in (

let pat_as_arg = (fun _57_597 -> (match (_57_597) with
| (p, i) -> begin
(

let _57_600 = (decorated_pattern_as_term p)
in (match (_57_600) with
| (vars, te) -> begin
(let _155_217 = (let _155_216 = (FStar_Syntax_Syntax.as_implicit i)
in ((te), (_155_216)))
in ((vars), (_155_217)))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_57_602) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _155_218 = (mk (FStar_Syntax_Syntax.Tm_constant (c)))
in (([]), (_155_218)))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(let _155_219 = (mk (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (_155_219)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _57_615 = (let _155_220 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _155_220 FStar_List.unzip))
in (match (_57_615) with
| (vars, args) -> begin
(

let vars = (FStar_List.flatten vars)
in (let _155_224 = (let _155_223 = (let _155_222 = (let _155_221 = (FStar_Syntax_Syntax.fv_to_tm fv)
in ((_155_221), (args)))
in FStar_Syntax_Syntax.Tm_app (_155_222))
in (mk _155_223))
in ((vars), (_155_224))))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
(([]), (e))
end)))))


let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun c -> (

let wp = (match (c.FStar_Syntax_Syntax.effect_args) with
| ((wp, _57_624))::[] -> begin
wp
end
| _57_628 -> begin
(let _155_230 = (let _155_229 = (let _155_228 = (FStar_List.map (fun _57_632 -> (match (_57_632) with
| (x, _57_631) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right _155_228 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str _155_229))
in (FStar_All.failwith _155_230))
end)
in (let _155_231 = (FStar_List.hd c.FStar_Syntax_Syntax.comp_univs)
in ((_155_231), (c.FStar_Syntax_Syntax.result_typ), (wp)))))


let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (

let _57_641 = (destruct_comp c)
in (match (_57_641) with
| (u, _57_639, wp) -> begin
(let _155_250 = (let _155_249 = (let _155_248 = (lift c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _155_248))
in (_155_249)::[])
in {FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _155_250; FStar_Syntax_Syntax.flags = []})
end)))


let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let _57_650 = (let _155_258 = (FStar_TypeChecker_Env.norm_eff_name env l1)
in (let _155_257 = (FStar_TypeChecker_Env.norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _155_258 _155_257)))
in (match (_57_650) with
| (m, _57_647, _57_649) -> begin
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

let _57_662 = (FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (_57_662) with
| (m, lift1, lift2) -> begin
(

let m1 = (lift_comp c1 m lift1)
in (

let m2 = (lift_comp c2 m lift2)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (

let _57_668 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (_57_668) with
| (a, kwp) -> begin
(let _155_272 = (destruct_comp m1)
in (let _155_271 = (destruct_comp m2)
in ((((md), (a), (kwp))), (_155_272), (_155_271))))
end)))))
end)))))


let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid))))


let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md u_result result wp flags -> (let _155_293 = (let _155_292 = (let _155_291 = (FStar_Syntax_Syntax.as_arg wp)
in (_155_291)::[])
in {FStar_Syntax_Syntax.comp_univs = (u_result)::[]; FStar_Syntax_Syntax.effect_name = md.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = _155_292; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp _155_293)))


let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (

let _57_682 = lc
in (let _155_300 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _57_682.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _155_300; FStar_Syntax_Syntax.cflags = _57_682.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _57_684 -> (match (()) with
| () -> begin
(let _155_299 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _155_299))
end))})))


let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _155_303 = (FStar_Syntax_Subst.compress t)
in _155_303.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_57_687) -> begin
true
end
| _57_690 -> begin
false
end))


let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v -> (

let c = if (let _155_310 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation _155_310)) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(

let m = (let _155_311 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must _155_311))
in (

let _57_697 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_57_697) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let u_t = (env.FStar_TypeChecker_Env.universe_of env t)
in (

let wp = (let _155_317 = (let _155_316 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env m m.FStar_Syntax_Syntax.ret_wp)
in (let _155_315 = (let _155_314 = (FStar_Syntax_Syntax.as_arg t)
in (let _155_313 = (let _155_312 = (FStar_Syntax_Syntax.as_arg v)
in (_155_312)::[])
in (_155_314)::_155_313))
in (FStar_Syntax_Syntax.mk_Tm_app _155_316 _155_315 (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _155_317))
in (mk_comp m u_t t wp ((FStar_Syntax_Syntax.RETURN)::[])))))
end)))
end
in (

let _57_702 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return"))) then begin
(let _155_320 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _155_319 = (FStar_Syntax_Print.term_to_string v)
in (let _155_318 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _155_320 _155_319 _155_318))))
end else begin
()
end
in c)))


let bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r1 env e1opt lc1 _57_710 -> (match (_57_710) with
| (b, lc2) -> begin
(

let lc1 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1)
in (

let lc2 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2)
in (

let _57_720 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(

let bstr = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _155_333 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (let _155_332 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _155_331 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" _155_333 _155_332 bstr _155_331)))))
end else begin
()
end
in (

let bind_it = (fun _57_723 -> (match (()) with
| () -> begin
(

let c1 = (lc1.FStar_Syntax_Syntax.comp ())
in (

let c2 = (lc2.FStar_Syntax_Syntax.comp ())
in (

let _57_729 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _155_340 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _155_339 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _155_338 = (FStar_Syntax_Print.comp_to_string c1)
in (let _155_337 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (let _155_336 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" _155_340 _155_339 _155_338 _155_337 _155_336))))))
end else begin
()
end
in (

let try_simplify = (fun _57_732 -> (match (()) with
| () -> begin
(

let aux = (fun _57_734 -> (match (()) with
| () -> begin
if (FStar_Syntax_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some (((c2), ("trivial no binder")))
end
| Some (_57_737) -> begin
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
(let _155_348 = (let _155_347 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in ((_155_347), (reason)))
in Some (_155_348))
end
| _57_747 -> begin
(aux ())
end))
in if ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2)) then begin
(subst_c2 "both total")
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2)) then begin
(let _155_350 = (let _155_349 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((_155_349), ("both gtot")))
in Some (_155_350))
end else begin
(match (((e1opt), (b))) with
| (Some (e), Some (x)) -> begin
if ((FStar_Syntax_Util.is_total_comp c1) && (not ((FStar_Syntax_Syntax.is_null_bv x)))) then begin
(subst_c2 "substituted e")
end else begin
(aux ())
end
end
| _57_754 -> begin
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

let _57_772 = (lift_and_destruct env c1 c2)
in (match (_57_772) with
| ((md, a, kwp), (u_t1, t1, wp1), (u_t2, t2, wp2)) -> begin
(

let bs = (match (b) with
| None -> begin
(let _155_351 = (FStar_Syntax_Syntax.null_binder t1)
in (_155_351)::[])
end
| Some (x) -> begin
(let _155_352 = (FStar_Syntax_Syntax.mk_binder x)
in (_155_352)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (

let r1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1))) None r1)
in (

let wp_args = (let _155_364 = (FStar_Syntax_Syntax.as_arg r1)
in (let _155_363 = (let _155_362 = (FStar_Syntax_Syntax.as_arg t1)
in (let _155_361 = (let _155_360 = (FStar_Syntax_Syntax.as_arg t2)
in (let _155_359 = (let _155_358 = (FStar_Syntax_Syntax.as_arg wp1)
in (let _155_357 = (let _155_356 = (let _155_355 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg _155_355))
in (_155_356)::[])
in (_155_358)::_155_357))
in (_155_360)::_155_359))
in (_155_362)::_155_361))
in (_155_364)::_155_363))
in (

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t2))))::[]) kwp)
in (

let wp = (let _155_365 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t1)::(u_t2)::[]) env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _155_365 wp_args None t2.FStar_Syntax_Syntax.pos))
in (

let c = (mk_comp md u_t2 t2 wp [])
in c)))))))
end))
end)))))
end))
in (let _155_366 = (join_lcomp env lc1 lc2)
in {FStar_Syntax_Syntax.eff_name = _155_366; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it})))))
end))


let lift_formula : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t mk_wp f -> (

let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (

let _57_791 = (FStar_TypeChecker_Env.wp_signature env md_pure.FStar_Syntax_Syntax.mname)
in (match (_57_791) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let wp = (let _155_378 = (let _155_377 = (FStar_Syntax_Syntax.as_arg t)
in (let _155_376 = (let _155_375 = (FStar_Syntax_Syntax.as_arg f)
in (_155_375)::[])
in (_155_377)::_155_376))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wp _155_378 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (mk_comp md_pure FStar_Syntax_Syntax.U_zero FStar_TypeChecker_Common.t_unit wp [])))
end))))


let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((f), (FStar_Syntax_Syntax.Meta_labeled (((reason), (r), (false))))))) None f.FStar_Syntax_Syntax.pos))


let label_opt : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _155_402 = (FStar_TypeChecker_Env.should_verify env)
in (FStar_All.pipe_left Prims.op_Negation _155_402)) then begin
f
end else begin
(let _155_403 = (reason ())
in (label _155_403 r f))
end
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let _57_810 = g
in (let _155_411 = (let _155_410 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_155_410))
in {FStar_TypeChecker_Env.guard_f = _155_411; FStar_TypeChecker_Env.deferred = _57_810.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_810.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_810.FStar_TypeChecker_Env.implicits}))
end))


let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| _57_821 -> begin
g2
end))


let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun _57_826 -> (match (()) with
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

let _57_835 = (destruct_comp c)
in (match (_57_835) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let wp = (let _155_430 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assume_p)
in (let _155_429 = (let _155_428 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _155_427 = (let _155_426 = (FStar_Syntax_Syntax.as_arg f)
in (let _155_425 = (let _155_424 = (FStar_Syntax_Syntax.as_arg wp)
in (_155_424)::[])
in (_155_426)::_155_425))
in (_155_428)::_155_427))
in (FStar_Syntax_Syntax.mk_Tm_app _155_430 _155_429 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md u_res_t res_t wp c.FStar_Syntax_Syntax.flags)))
end)))
end
end))
end))
in (

let _57_838 = lc
in {FStar_Syntax_Syntax.eff_name = _57_838.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _57_838.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _57_838.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))


let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> if (FStar_TypeChecker_Rel.is_trivial g0) then begin
((lc), (g0))
end else begin
(

let _57_845 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _155_450 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _155_449 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _155_450 _155_449)))
end else begin
()
end
in (

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _57_2 -> (match (_57_2) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _57_851 -> begin
[]
end))))
in (

let strengthen = (fun _57_854 -> (match (()) with
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

let xret = (let _155_455 = (let _155_454 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _155_454))
in (FStar_Syntax_Util.comp_set_flags _155_455 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (

let lc = (bind e.FStar_Syntax_Syntax.pos env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) ((Some (x)), ((FStar_Syntax_Util.lcomp_of_comp xret))))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (

let _57_864 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _155_457 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _155_456 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _155_457 _155_456)))
end else begin
()
end
in (

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _57_870 = (destruct_comp c)
in (match (_57_870) with
| (u_res_t, res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let wp = (let _155_466 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.assert_p)
in (let _155_465 = (let _155_464 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _155_463 = (let _155_462 = (let _155_459 = (let _155_458 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason _155_458 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _155_459))
in (let _155_461 = (let _155_460 = (FStar_Syntax_Syntax.as_arg wp)
in (_155_460)::[])
in (_155_462)::_155_461))
in (_155_464)::_155_463))
in (FStar_Syntax_Syntax.mk_Tm_app _155_466 _155_465 None wp.FStar_Syntax_Syntax.pos)))
in (

let _57_873 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _155_467 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _155_467))
end else begin
()
end
in (

let c2 = (mk_comp md u_res_t res_t wp flags)
in c2))))
end)))))
end)))
end))
in (let _155_471 = (

let _57_876 = lc
in (let _155_470 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _155_469 = if ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _155_468 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _155_468))) then begin
flags
end else begin
[]
end
in {FStar_Syntax_Syntax.eff_name = _155_470; FStar_Syntax_Syntax.res_typ = _57_876.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _155_469; FStar_Syntax_Syntax.comp = strengthen})))
in ((_155_471), ((

let _57_878 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_878.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_878.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_878.FStar_TypeChecker_Env.implicits})))))))
end)


let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env comp res_t -> (

let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let y = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let _57_888 = (let _155_479 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _155_478 = (FStar_Syntax_Syntax.bv_to_name y)
in ((_155_479), (_155_478))))
in (match (_57_888) with
| (xexp, yexp) -> begin
(

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let yret = (let _155_484 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.ret_wp)
in (let _155_483 = (let _155_482 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _155_481 = (let _155_480 = (FStar_Syntax_Syntax.as_arg yexp)
in (_155_480)::[])
in (_155_482)::_155_481))
in (FStar_Syntax_Syntax.mk_Tm_app _155_484 _155_483 None res_t.FStar_Syntax_Syntax.pos)))
in (

let x_eq_y_yret = (let _155_492 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _155_491 = (let _155_490 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _155_489 = (let _155_488 = (let _155_485 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _155_485))
in (let _155_487 = (let _155_486 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_155_486)::[])
in (_155_488)::_155_487))
in (_155_490)::_155_489))
in (FStar_Syntax_Syntax.mk_Tm_app _155_492 _155_491 None res_t.FStar_Syntax_Syntax.pos)))
in (

let forall_y_x_eq_y_yret = (let _155_502 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::(u_res_t)::[]) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _155_501 = (let _155_500 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _155_499 = (let _155_498 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _155_497 = (let _155_496 = (let _155_495 = (let _155_494 = (let _155_493 = (FStar_Syntax_Syntax.mk_binder y)
in (_155_493)::[])
in (FStar_Syntax_Util.abs _155_494 x_eq_y_yret (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _155_495))
in (_155_496)::[])
in (_155_498)::_155_497))
in (_155_500)::_155_499))
in (FStar_Syntax_Syntax.mk_Tm_app _155_502 _155_501 None res_t.FStar_Syntax_Syntax.pos)))
in (

let lc2 = (mk_comp md_pure u_res_t res_t forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (

let lc = (let _155_503 = (FStar_TypeChecker_Env.get_range env)
in (bind _155_503 env None (FStar_Syntax_Util.lcomp_of_comp comp) ((Some (x)), ((FStar_Syntax_Util.lcomp_of_comp lc2)))))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))


let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (

let comp = (fun _57_900 -> (match (()) with
| () -> begin
(

let _57_917 = (let _155_515 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _155_514 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _155_515 _155_514)))
in (match (_57_917) with
| ((md, _57_903, _57_905), (u_res_t, res_t, wp_then), (_57_912, _57_914, wp_else)) -> begin
(

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _155_535 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (let _155_534 = (let _155_532 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _155_531 = (let _155_530 = (FStar_Syntax_Syntax.as_arg g)
in (let _155_529 = (let _155_528 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _155_527 = (let _155_526 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_155_526)::[])
in (_155_528)::_155_527))
in (_155_530)::_155_529))
in (_155_532)::_155_531))
in (let _155_533 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _155_535 _155_534 None _155_533)))))
in (

let wp = (ifthenelse md res_t guard wp_then wp_else)
in if ((FStar_Options.split_cases ()) > (Prims.parse_int "0")) then begin
(

let comp = (mk_comp md u_res_t res_t wp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(

let wp = (let _155_540 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (let _155_539 = (let _155_538 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _155_537 = (let _155_536 = (FStar_Syntax_Syntax.as_arg wp)
in (_155_536)::[])
in (_155_538)::_155_537))
in (FStar_Syntax_Syntax.mk_Tm_app _155_540 _155_539 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md u_res_t res_t wp []))
end))
end))
end))
in (let _155_541 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _155_541; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp})))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (let _155_547 = (let _155_546 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid _155_546))
in (FStar_Syntax_Syntax.fvar _155_547 FStar_Syntax_Syntax.Delta_constant None)))


let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (FStar_List.fold_left (fun eff _57_936 -> (match (_57_936) with
| (_57_934, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (

let bind_cases = (fun _57_939 -> (match (()) with
| () -> begin
(

let u_res_t = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _155_577 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.if_then_else)
in (let _155_576 = (let _155_574 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _155_573 = (let _155_572 = (FStar_Syntax_Syntax.as_arg g)
in (let _155_571 = (let _155_570 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _155_569 = (let _155_568 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_155_568)::[])
in (_155_570)::_155_569))
in (_155_572)::_155_571))
in (_155_574)::_155_573))
in (let _155_575 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _155_577 _155_576 None _155_575)))))
in (

let default_case = (

let post_k = (let _155_580 = (let _155_578 = (FStar_Syntax_Syntax.null_binder res_t)
in (_155_578)::[])
in (let _155_579 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _155_580 _155_579)))
in (

let kwp = (let _155_583 = (let _155_581 = (FStar_Syntax_Syntax.null_binder post_k)
in (_155_581)::[])
in (let _155_582 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _155_583 _155_582)))
in (

let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (

let wp = (let _155_589 = (let _155_584 = (FStar_Syntax_Syntax.mk_binder post)
in (_155_584)::[])
in (let _155_588 = (let _155_587 = (let _155_585 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Errors.exhaustiveness_check _155_585))
in (let _155_586 = (fvar_const env FStar_Syntax_Const.false_lid)
in (FStar_All.pipe_left _155_587 _155_586)))
in (FStar_Syntax_Util.abs _155_589 _155_588 (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md u_res_t res_t wp []))))))
in (

let comp = (FStar_List.fold_right (fun _57_955 celse -> (match (_57_955) with
| (g, cthen) -> begin
(

let _57_975 = (let _155_592 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _155_592 celse))
in (match (_57_975) with
| ((md, _57_959, _57_961), (_57_964, _57_966, wp_then), (_57_970, _57_972, wp_else)) -> begin
(let _155_593 = (ifthenelse md res_t g wp_then wp_else)
in (mk_comp md u_res_t res_t _155_593 []))
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

let _57_984 = (destruct_comp comp)
in (match (_57_984) with
| (_57_980, _57_982, wp) -> begin
(

let wp = (let _155_598 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_res_t)::[]) env md md.FStar_Syntax_Syntax.ite_wp)
in (let _155_597 = (let _155_596 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _155_595 = (let _155_594 = (FStar_Syntax_Syntax.as_arg wp)
in (_155_594)::[])
in (_155_596)::_155_595))
in (FStar_Syntax_Syntax.mk_Tm_app _155_598 _155_597 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md u_res_t res_t wp []))
end))))
end))))
end))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))


let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (

let close = (fun _57_990 -> (match (()) with
| () -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in if (FStar_Syntax_Util.is_ml_comp c) then begin
c
end else begin
(

let close_wp = (fun u_res md res_t bvs wp0 -> (FStar_List.fold_right (fun x wp -> (

let bs = (let _155_619 = (FStar_Syntax_Syntax.mk_binder x)
in (_155_619)::[])
in (

let us = (let _155_621 = (let _155_620 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (_155_620)::[])
in (u_res)::_155_621)
in (

let wp = (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))))))
in (let _155_628 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (let _155_627 = (let _155_626 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _155_625 = (let _155_624 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _155_623 = (let _155_622 = (FStar_Syntax_Syntax.as_arg wp)
in (_155_622)::[])
in (_155_624)::_155_623))
in (_155_626)::_155_625))
in (FStar_Syntax_Syntax.mk_Tm_app _155_628 _155_627 None wp0.FStar_Syntax_Syntax.pos))))))) bvs wp0))
in (

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _57_1007 = (destruct_comp c)
in (match (_57_1007) with
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

let _57_1010 = lc
in {FStar_Syntax_Syntax.eff_name = _57_1010.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _57_1010.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _57_1010.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))


let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (

let refine = (fun _57_1016 -> (match (()) with
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
(let _155_639 = (let _155_638 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _155_637 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _155_638 _155_637)))
in (FStar_All.failwith _155_639))
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

let ret = (let _155_641 = (let _155_640 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _155_640 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _155_641))
in (

let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (

let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (

let c = (let _155_643 = (let _155_642 = (bind e.FStar_Syntax_Syntax.pos env None (FStar_Syntax_Util.lcomp_of_comp c) ((Some (x)), (eq_ret)))
in (_155_642.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _155_643 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
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

let _57_1028 = lc
in {FStar_Syntax_Syntax.eff_name = _57_1028.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _57_1028.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))


let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (match ((FStar_TypeChecker_Rel.sub_comp env c c')) with
| None -> begin
(let _155_655 = (let _155_654 = (let _155_653 = (FStar_TypeChecker_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _155_652 = (FStar_TypeChecker_Env.get_range env)
in ((_155_653), (_155_652))))
in FStar_Syntax_Syntax.Error (_155_654))
in (Prims.raise _155_655))
end
| Some (g) -> begin
((e), (c'), (g))
end))


let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match ((let _155_664 = (FStar_Syntax_Subst.compress t)
in _155_664.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_57_1042) -> begin
(match ((let _155_665 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _155_665.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid) -> begin
(

let _57_1046 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (

let b2t = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (

let lc = (let _155_668 = (let _155_667 = (let _155_666 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _155_666))
in ((None), (_155_667)))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) lc _155_668))
in (

let e = (let _155_670 = (let _155_669 = (FStar_Syntax_Syntax.as_arg e)
in (_155_669)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _155_670 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in ((e), (lc))))))
end
| _57_1052 -> begin
((e), (lc))
end)
end
| _57_1054 -> begin
((e), (lc))
end))


let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (

let gopt = if env.FStar_TypeChecker_Env.use_eq then begin
(let _155_679 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in ((_155_679), (false)))
end else begin
(let _155_680 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in ((_155_680), (true)))
end
in (match (gopt) with
| (None, _57_1062) -> begin
(

let _57_1064 = (FStar_TypeChecker_Rel.subtype_fail env e lc.FStar_Syntax_Syntax.res_typ t)
in ((e), ((

let _57_1066 = lc
in {FStar_Syntax_Syntax.eff_name = _57_1066.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _57_1066.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _57_1066.FStar_Syntax_Syntax.comp})), (FStar_TypeChecker_Rel.trivial_guard)))
end
| (Some (g), apply_guard) -> begin
(match ((FStar_TypeChecker_Rel.guard_form g)) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let lc = (

let _57_1073 = lc
in {FStar_Syntax_Syntax.eff_name = _57_1073.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _57_1073.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _57_1073.FStar_Syntax_Syntax.comp})
in ((e), (lc), (g)))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let g = (

let _57_1078 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_1078.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_1078.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_1078.FStar_TypeChecker_Env.implicits})
in (

let strengthen = (fun _57_1082 -> (match (()) with
| () -> begin
(

let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (match ((let _155_683 = (FStar_Syntax_Subst.compress f)
in _155_683.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_57_1085, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _57_1091; FStar_Syntax_Syntax.pos = _57_1089; FStar_Syntax_Syntax.vars = _57_1087}, _57_1096) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
(

let lc = (

let _57_1099 = lc
in {FStar_Syntax_Syntax.eff_name = _57_1099.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _57_1099.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _57_1099.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| _57_1103 -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let _57_1105 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _155_687 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _155_686 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _155_685 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _155_684 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _155_687 _155_686 _155_685 _155_684)))))
end else begin
()
end
in (

let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _57_1110 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_57_1110) with
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

let _57_1120 = (destruct_comp ct)
in (match (_57_1120) with
| (u_t, _57_1117, _57_1119) -> begin
(

let wp = (let _155_692 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.ret_wp)
in (let _155_691 = (let _155_690 = (FStar_Syntax_Syntax.as_arg t)
in (let _155_689 = (let _155_688 = (FStar_Syntax_Syntax.as_arg xexp)
in (_155_688)::[])
in (_155_690)::_155_689))
in (FStar_Syntax_Syntax.mk_Tm_app _155_692 _155_691 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)))
in (

let cret = (let _155_693 = (mk_comp md u_t t wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _155_693))
in (

let guard = if apply_guard then begin
(let _155_695 = (let _155_694 = (FStar_Syntax_Syntax.as_arg xexp)
in (_155_694)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _155_695 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end else begin
f
end
in (

let _57_1126 = (let _155_703 = (FStar_All.pipe_left (fun _155_700 -> Some (_155_700)) (FStar_TypeChecker_Errors.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _155_702 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _155_701 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _155_703 _155_702 e cret _155_701))))
in (match (_57_1126) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x = (

let _57_1127 = x
in {FStar_Syntax_Syntax.ppname = _57_1127.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1127.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (

let c = (let _155_705 = (let _155_704 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _155_704))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) _155_705 ((Some (x)), (eq_ret))))
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let _57_1132 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _155_706 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _155_706))
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
| _57_1139 -> begin
[]
end))))
in (

let lc = (

let _57_1141 = lc
in (let _155_708 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _155_708; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (

let g = (

let _57_1144 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_1144.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_1144.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_1144.FStar_TypeChecker_Env.implicits})
in ((e), (lc), (g)))))))
end)
end)))


let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _155_720 = (let _155_719 = (let _155_718 = (let _155_717 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _155_717))
in (_155_718)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _155_719 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _155_720))))
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
| ((req, _57_1172))::((ens, _57_1167))::_57_1164 -> begin
(let _155_726 = (let _155_723 = (norm req)
in Some (_155_723))
in (let _155_725 = (let _155_724 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _155_724))
in ((_155_726), (_155_725))))
end
| _57_1176 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Effect constructor is not fully applied"), (comp.FStar_Syntax_Syntax.pos)))))
end)
end else begin
(

let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| ((wp, _57_1182))::_57_1179 -> begin
(

let _57_1188 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (_57_1188) with
| (us_r, _57_1187) -> begin
(

let _57_1192 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (_57_1192) with
| (us_e, _57_1191) -> begin
(

let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (

let as_req = (let _155_727 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.as_requires r) FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.mk_Tm_uinst _155_727 us_r))
in (

let as_ens = (let _155_728 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.as_ensures r) FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.mk_Tm_uinst _155_728 us_e))
in (

let req = (let _155_731 = (let _155_730 = (let _155_729 = (FStar_Syntax_Syntax.as_arg wp)
in (_155_729)::[])
in (((ct.FStar_Syntax_Syntax.result_typ), (Some (FStar_Syntax_Syntax.imp_tag))))::_155_730)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _155_731 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let ens = (let _155_734 = (let _155_733 = (let _155_732 = (FStar_Syntax_Syntax.as_arg wp)
in (_155_732)::[])
in (((ct.FStar_Syntax_Syntax.result_typ), (Some (FStar_Syntax_Syntax.imp_tag))))::_155_733)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _155_734 None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _155_738 = (let _155_735 = (norm req)
in Some (_155_735))
in (let _155_737 = (let _155_736 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm _155_736))
in ((_155_738), (_155_737)))))))))
end))
end))
end
| _57_1199 -> begin
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

let _57_1210 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_1210) with
| (bs, c) -> begin
(

let rec aux = (fun subst _57_4 -> (match (_57_4) with
| ((x, Some (FStar_Syntax_Syntax.Implicit (dot))))::rest -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let _57_1226 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t)
in (match (_57_1226) with
| (v, _57_1224, g) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (v))))::subst
in (

let _57_1232 = (aux subst rest)
in (match (_57_1232) with
| (args, bs, subst, g') -> begin
(let _155_749 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((v), (Some (FStar_Syntax_Syntax.Implicit (dot)))))::args), (bs), (subst), (_155_749)))
end)))
end)))
end
| bs -> begin
(([]), (bs), (subst), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (

let _57_1238 = (aux [] bs)
in (match (_57_1238) with
| (args, bs, subst, guard) -> begin
(match (((args), (bs))) with
| ([], _57_1241) -> begin
((e), (torig), (guard))
end
| (_57_1244, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
((e), (torig), (FStar_TypeChecker_Rel.trivial_guard))
end
| _57_1248 -> begin
(

let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _57_1251 -> begin
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
| _57_1256 -> begin
((e), (t), (FStar_TypeChecker_Rel.trivial_guard))
end)
end))


let string_of_univs = (fun univs -> (let _155_754 = (let _155_753 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _155_753 (FStar_List.map (fun u -> (let _155_752 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _155_752 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _155_754 (FStar_String.concat ", "))))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(

let s = (let _155_760 = (let _155_759 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _155_759))
in (FStar_All.pipe_right _155_760 FStar_Util.set_elements))
in (

let _57_1262 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _155_762 = (let _155_761 = (FStar_TypeChecker_Env.univ_vars env)
in (string_of_univs _155_761))
in (FStar_Util.print1 "univ_vars in env: %s\n" _155_762))
end else begin
()
end
in (

let r = (let _155_763 = (FStar_TypeChecker_Env.get_range env)
in Some (_155_763))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (

let _57_1267 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _155_768 = (let _155_765 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _155_765))
in (let _155_767 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _155_766 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _155_768 _155_767 _155_766))))
end else begin
()
end
in (

let _57_1269 = (FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))))
in u_name))))))
in u_names))))
end)


let gather_free_univnames : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env t -> (

let ctx_univnames = (FStar_TypeChecker_Env.univnames env)
in (

let tm_univnames = (FStar_Syntax_Free.univnames t)
in (

let univnames = (let _155_773 = (FStar_Util.fifo_set_difference tm_univnames ctx_univnames)
in (FStar_All.pipe_right _155_773 FStar_Util.fifo_set_elements))
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

let _57_1284 = (FStar_ST.op_Colon_Equals (Prims.snd ts).FStar_Syntax_Syntax.tk (Some (t.FStar_Syntax_Syntax.n)))
in ts)))
end))


let check_universe_generalization : FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun explicit_univ_names generalized_univ_names t -> (match (((explicit_univ_names), (generalized_univ_names))) with
| ([], _57_1291) -> begin
generalized_univ_names
end
| (_57_1294, []) -> begin
explicit_univ_names
end
| _57_1298 -> begin
(let _155_785 = (let _155_784 = (let _155_783 = (let _155_782 = (FStar_Syntax_Print.term_to_string t)
in (Prims.strcat "Generalized universe in a term containing explicit universe annotation : " _155_782))
in ((_155_783), (t.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_155_784))
in (Prims.raise _155_785))
end))


let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.NoFullNorm)::(FStar_TypeChecker_Normalize.Beta)::[]) env t0)
in (

let univnames = (gather_free_univnames env t)
in (

let univs = (FStar_Syntax_Free.univs t)
in (

let _57_1304 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _155_790 = (string_of_univs univs)
in (FStar_Util.print1 "univs to gen : %s\n" _155_790))
end else begin
()
end
in (

let gen = (gen_univs env univs)
in (

let _57_1307 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _155_791 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _155_791))
end else begin
()
end
in (

let univs = (check_universe_generalization univnames gen t0)
in (

let ts = (FStar_Syntax_Subst.close_univ_vars univs t)
in (let _155_792 = (FStar_ST.read t0.FStar_Syntax_Syntax.tk)
in (maybe_set_tk ((univs), (ts)) _155_792)))))))))))


let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> if (let _155_798 = (FStar_Util.for_all (fun _57_1316 -> (match (_57_1316) with
| (_57_1314, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _155_798)) then begin
None
end else begin
(

let norm = (fun c -> (

let _57_1319 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _155_801 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _155_801))
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

let _57_1322 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _155_802 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _155_802))
end else begin
()
end
in c))))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (let _155_805 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _155_805 FStar_Util.set_elements)))
in (

let _57_1338 = (let _155_807 = (FStar_All.pipe_right ecs (FStar_List.map (fun _57_1329 -> (match (_57_1329) with
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
in (FStar_All.pipe_right _155_807 FStar_List.unzip))
in (match (_57_1338) with
| (univs, uvars) -> begin
(

let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (

let gen_univs = (gen_univs env univs)
in (

let _57_1342 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end else begin
()
end
in (

let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _57_1347 -> (match (_57_1347) with
| (uvs, e, c) -> begin
(

let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _57_1350 -> (match (_57_1350) with
| (u, k) -> begin
(match ((FStar_Unionfind.find u)) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
((a), (Some (FStar_Syntax_Syntax.imp_tag)))
end
| FStar_Syntax_Syntax.Fixed (_57_1384) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _57_1387 -> begin
(

let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (

let _57_1391 = (FStar_Syntax_Util.arrow_formals k)
in (match (_57_1391) with
| (bs, kres) -> begin
(

let a = (let _155_813 = (let _155_812 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _155_811 -> Some (_155_811)) _155_812))
in (FStar_Syntax_Syntax.new_bv _155_813 kres))
in (

let t = (let _155_818 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _155_817 = (let _155_816 = (let _155_815 = (let _155_814 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _155_814))
in FStar_Util.Inl (_155_815))
in Some (_155_816))
in (FStar_Syntax_Util.abs bs _155_818 _155_817)))
in (

let _57_1394 = (FStar_Syntax_Util.set_uvar u t)
in ((a), (Some (FStar_Syntax_Syntax.imp_tag))))))
end)))
end)
end))))
in (

let _57_1426 = (match (((tvars), (gen_univs))) with
| ([], []) -> begin
((e), (c))
end
| ([], _57_1402) -> begin
(

let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
in (

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env e)
in ((e), (c))))
end
| _57_1407 -> begin
(

let _57_1410 = ((e), (c))
in (match (_57_1410) with
| (e0, c0) -> begin
(

let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env c)
in (

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Iota))::(FStar_TypeChecker_Normalize.NoFullNorm)::[]) env e)
in (

let t = (match ((let _155_819 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _155_819.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(

let _57_1419 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (_57_1419) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| _57_1421 -> begin
(FStar_Syntax_Util.arrow tvars c)
end)
in (

let e' = (FStar_Syntax_Util.abs tvars e (Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp c)))))
in (let _155_820 = (FStar_Syntax_Syntax.mk_Total t)
in ((e'), (_155_820)))))))
end))
end)
in (match (_57_1426) with
| (e, c) -> begin
((gen_univs), (e), (c))
end)))
end))))
in Some (ecs)))))
end)))))
end)


let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> (

let _57_1436 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _155_827 = (let _155_826 = (FStar_List.map (fun _57_1435 -> (match (_57_1435) with
| (lb, _57_1432, _57_1434) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _155_826 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _155_827))
end else begin
()
end
in (

let univnames_lecs = (FStar_List.map (fun _57_1441 -> (match (_57_1441) with
| (l, t, c) -> begin
(gather_free_univnames env t)
end)) lecs)
in (

let generalized_lecs = (match ((let _155_830 = (FStar_All.pipe_right lecs (FStar_List.map (fun _57_1447 -> (match (_57_1447) with
| (_57_1444, e, c) -> begin
((e), (c))
end))))
in (gen env _155_830))) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun _57_1452 -> (match (_57_1452) with
| (l, t, c) -> begin
((l), ([]), (t), (c))
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _57_1460 _57_1464 -> (match (((_57_1460), (_57_1464))) with
| ((l, _57_1457, _57_1459), (us, e, c)) -> begin
(

let _57_1465 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _155_837 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _155_836 = (FStar_Syntax_Print.lbname_to_string l)
in (let _155_835 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (let _155_834 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print4 "(%s) Generalized %s at type %s\n%s\n" _155_837 _155_836 _155_835 _155_834)))))
end else begin
()
end
in ((l), (us), (e), (c)))
end)) lecs ecs)
end)
in (FStar_List.map2 (fun univnames _57_1473 -> (match (_57_1473) with
| (l, generalized_univs, t, c) -> begin
(let _155_840 = (check_universe_generalization univnames generalized_univs t)
in ((l), (_155_840), (t), (c)))
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
(let _155_856 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _155_855 -> Some (_155_855)) _155_856))
end)
end)
in (

let is_var = (fun e -> (match ((let _155_859 = (FStar_Syntax_Subst.compress e)
in _155_859.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (_57_1489) -> begin
true
end
| _57_1492 -> begin
false
end))
in (

let decorate = (fun e t -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((

let _57_1499 = x
in {FStar_Syntax_Syntax.ppname = _57_1499.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1499.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| _57_1502 -> begin
(

let _57_1503 = e
in (let _155_864 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _57_1503.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _155_864; FStar_Syntax_Syntax.pos = _57_1503.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _57_1503.FStar_Syntax_Syntax.vars}))
end)))
in (

let env = (

let _57_1505 = env
in (let _155_865 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _57_1505.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_1505.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_1505.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_1505.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_1505.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_1505.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_1505.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_1505.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_1505.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_1505.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_1505.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_1505.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_1505.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_1505.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_1505.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _155_865; FStar_TypeChecker_Env.is_iface = _57_1505.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_1505.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_1505.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _57_1505.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _57_1505.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_1505.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _57_1505.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _57_1505.FStar_TypeChecker_Env.qname_and_index}))
in (match ((check env t1 t2)) with
| None -> begin
(let _155_869 = (let _155_868 = (let _155_867 = (FStar_TypeChecker_Errors.expected_expression_of_type env t2 e t1)
in (let _155_866 = (FStar_TypeChecker_Env.get_range env)
in ((_155_867), (_155_866))))
in FStar_Syntax_Syntax.Error (_155_868))
in (Prims.raise _155_869))
end
| Some (g) -> begin
(

let _57_1511 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _155_870 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _155_870))
end else begin
()
end
in (let _155_871 = (decorate e t2)
in ((_155_871), (g))))
end)))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (

let discharge = (fun g -> (

let _57_1518 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _155_881 = (discharge g)
in (let _155_880 = (lc.FStar_Syntax_Syntax.comp ())
in ((_155_881), (_155_880))))
end else begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let steps = (FStar_TypeChecker_Normalize.Beta)::[]
in (

let c = (let _155_884 = (let _155_883 = (let _155_882 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (FStar_All.pipe_right _155_882 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right _155_883 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (FStar_All.pipe_right _155_884 (FStar_TypeChecker_Normalize.comp_to_comp_typ env)))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let _57_1528 = (destruct_comp c)
in (match (_57_1528) with
| (u_t, t, wp) -> begin
(

let vc = (let _155_890 = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_t)::[]) env md md.FStar_Syntax_Syntax.trivial)
in (let _155_889 = (let _155_887 = (FStar_Syntax_Syntax.as_arg t)
in (let _155_886 = (let _155_885 = (FStar_Syntax_Syntax.as_arg wp)
in (_155_885)::[])
in (_155_887)::_155_886))
in (let _155_888 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk_Tm_app _155_890 _155_889 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _155_888))))
in (

let _57_1530 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _155_891 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _155_891))
end else begin
()
end
in (

let g = (let _155_892 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _155_892))
in (let _155_894 = (discharge g)
in (let _155_893 = (FStar_Syntax_Syntax.mk_Comp c)
in ((_155_894), (_155_893)))))))
end))))))
end)))


let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (

let short_bin_op = (fun f _57_6 -> (match (_57_6) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((fst, _57_1541))::[] -> begin
(f fst)
end
| _57_1545 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (

let op_and_e = (fun e -> (let _155_915 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _155_915 (fun _155_914 -> FStar_TypeChecker_Common.NonTrivial (_155_914)))))
in (

let op_or_e = (fun e -> (let _155_920 = (let _155_918 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _155_918))
in (FStar_All.pipe_right _155_920 (fun _155_919 -> FStar_TypeChecker_Common.NonTrivial (_155_919)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _155_923 -> FStar_TypeChecker_Common.NonTrivial (_155_923))))
in (

let op_or_t = (fun t -> (let _155_927 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _155_927 (fun _155_926 -> FStar_TypeChecker_Common.NonTrivial (_155_926)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _155_930 -> FStar_TypeChecker_Common.NonTrivial (_155_930))))
in (

let short_op_ite = (fun _57_7 -> (match (_57_7) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((guard, _57_1560))::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| (_then)::((guard, _57_1565))::[] -> begin
(let _155_934 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _155_934 (fun _155_933 -> FStar_TypeChecker_Common.NonTrivial (_155_933))))
end
| _57_1570 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (

let table = (((FStar_Syntax_Const.op_And), ((short_bin_op op_and_e))))::(((FStar_Syntax_Const.op_Or), ((short_bin_op op_or_e))))::(((FStar_Syntax_Const.and_lid), ((short_bin_op op_and_t))))::(((FStar_Syntax_Const.or_lid), ((short_bin_op op_or_t))))::(((FStar_Syntax_Const.imp_lid), ((short_bin_op op_imp_t))))::(((FStar_Syntax_Const.ite_lid), (short_op_ite)))::[]
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((FStar_Util.find_map table (fun _57_1578 -> (match (_57_1578) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _155_967 = (mk seen_args)
in Some (_155_967))
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
| _57_1583 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (match ((let _155_970 = (FStar_Syntax_Util.un_uinst l)
in _155_970.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| _57_1588 -> begin
false
end))


let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (

let pos = (fun bs -> (match (bs) with
| ((hd, _57_1597))::_57_1594 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| _57_1601 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| ((_57_1605, Some (FStar_Syntax_Syntax.Implicit (_57_1607))))::_57_1603 -> begin
bs
end
| _57_1613 -> begin
(match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
bs
end
| Some (t) -> begin
(match ((let _155_977 = (FStar_Syntax_Subst.compress t)
in _155_977.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', _57_1619) -> begin
(match ((FStar_Util.prefix_until (fun _57_8 -> (match (_57_8) with
| (_57_1624, Some (FStar_Syntax_Syntax.Implicit (_57_1626))) -> begin
false
end
| _57_1631 -> begin
true
end)) bs')) with
| None -> begin
bs
end
| Some ([], _57_1635, _57_1637) -> begin
bs
end
| Some (imps, _57_1642, _57_1644) -> begin
if (FStar_All.pipe_right imps (FStar_Util.for_all (fun _57_1650 -> (match (_57_1650) with
| (x, _57_1649) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end)))) then begin
(

let r = (pos bs)
in (

let imps = (FStar_All.pipe_right imps (FStar_List.map (fun _57_1654 -> (match (_57_1654) with
| (x, i) -> begin
(let _155_981 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in ((_155_981), (i)))
end))))
in (FStar_List.append imps bs)))
end else begin
bs
end
end)
end
| _57_1657 -> begin
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
(let _155_992 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m2), (t))))))) _155_992 e.FStar_Syntax_Syntax.pos))
end)))


let maybe_monadic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c t -> (

let m = (FStar_TypeChecker_Env.norm_eff_name env c)
in if (((is_pure_or_ghost_effect env m) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid)) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid)) then begin
e
end else begin
(let _155_1001 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))) _155_1001 e.FStar_Syntax_Syntax.pos))
end))


let effect_repr_aux = (fun only_reifiable env c u_c -> (match ((let _155_1006 = (FStar_TypeChecker_Env.norm_eff_name env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_TypeChecker_Env.effect_decl_opt env _155_1006))) with
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
| _57_1679 -> begin
(

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _57_1683 = (let _155_1007 = (FStar_List.hd c.FStar_Syntax_Syntax.effect_args)
in ((c.FStar_Syntax_Syntax.result_typ), (_155_1007)))
in (match (_57_1683) with
| (res_typ, wp) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_c)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (let _155_1013 = (let _155_1012 = (let _155_1010 = (let _155_1009 = (let _155_1008 = (FStar_Syntax_Syntax.as_arg res_typ)
in (_155_1008)::(wp)::[])
in ((repr), (_155_1009)))
in FStar_Syntax_Syntax.Tm_app (_155_1010))
in (let _155_1011 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _155_1012 None _155_1011)))
in Some (_155_1013)))
end)))
end)
end
end))


let effect_repr : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term Prims.option = (fun env c u_c -> (effect_repr_aux false env c u_c))


let reify_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term = (fun env c u_c -> (

let no_reify = (fun l -> (let _155_1031 = (let _155_1030 = (let _155_1029 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _155_1028 = (FStar_TypeChecker_Env.get_range env)
in ((_155_1029), (_155_1028))))
in FStar_Syntax_Syntax.Error (_155_1030))
in (Prims.raise _155_1031)))
in (match ((let _155_1032 = (c.FStar_Syntax_Syntax.comp ())
in (effect_repr_aux true env _155_1032 u_c))) with
| None -> begin
(no_reify c.FStar_Syntax_Syntax.eff_name)
end
| Some (tm) -> begin
tm
end)))


let d : Prims.string  ->  Prims.unit = (fun s -> (FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s))


let mk_toplevel_definition : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term) = (fun env lident def -> (

let _57_1702 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _57_1700 = (d (FStar_Ident.text_of_lid lident))
in (let _155_1041 = (FStar_Syntax_Print.term_to_string def)
in (FStar_Util.print2 "Registering top-level definition: %s\n%s\n" (FStar_Ident.text_of_lid lident) _155_1041)))
end else begin
()
end
in (

let fv = (let _155_1042 = (FStar_Syntax_Util.incr_delta_qualifier def)
in (FStar_Syntax_Syntax.lid_as_fv lident _155_1042 None))
in (

let lbname = FStar_Util.Inr (fv)
in (

let lb = ((false), (({FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = def})::[]))
in (

let sig_ctx = FStar_Syntax_Syntax.Sig_let (((lb), (FStar_Range.dummyRange), ((lident)::[]), ((FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen)::[]), ([])))
in (let _155_1043 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) None FStar_Range.dummyRange)
in ((sig_ctx), (_155_1043)))))))))


let check_sigelt_quals : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (

let visibility = (fun _57_9 -> (match (_57_9) with
| FStar_Syntax_Syntax.Private -> begin
true
end
| _57_1713 -> begin
false
end))
in (

let reducibility = (fun _57_10 -> (match (_57_10) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Irreducible) | (FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) | (FStar_Syntax_Syntax.Visible_default) | (FStar_Syntax_Syntax.Inline_for_extraction) -> begin
true
end
| _57_1722 -> begin
false
end))
in (

let assumption = (fun _57_11 -> (match (_57_11) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.New) -> begin
true
end
| _57_1728 -> begin
false
end))
in (

let reification = (fun _57_12 -> (match (_57_12) with
| (FStar_Syntax_Syntax.Reifiable) | (FStar_Syntax_Syntax.Reflectable (_)) -> begin
true
end
| _57_1736 -> begin
false
end))
in (

let inferred = (fun _57_13 -> (match (_57_13) with
| (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.RecordType (_)) | (FStar_Syntax_Syntax.RecordConstructor (_)) | (FStar_Syntax_Syntax.ExceptionConstructor) | (FStar_Syntax_Syntax.HasMaskedEffect) | (FStar_Syntax_Syntax.Effect) -> begin
true
end
| _57_1755 -> begin
false
end))
in (

let has_eq = (fun _57_14 -> (match (_57_14) with
| (FStar_Syntax_Syntax.Noeq) | (FStar_Syntax_Syntax.Unopteq) -> begin
true
end
| _57_1761 -> begin
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
| _57_1790 -> begin
true
end))
in (

let quals = (FStar_Syntax_Util.quals_of_sigelt se)
in if (let _155_1072 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _57_15 -> (match (_57_15) with
| FStar_Syntax_Syntax.OnlyName -> begin
true
end
| _57_1795 -> begin
false
end))))
in (FStar_All.pipe_right _155_1072 Prims.op_Negation)) then begin
(

let r = (FStar_Syntax_Util.range_of_sigelt se)
in (

let no_dup_quals = (FStar_Util.remove_dups (fun x y -> (x = y)) quals)
in (

let err' = (fun msg -> (let _155_1080 = (let _155_1079 = (let _155_1078 = (let _155_1077 = (FStar_Syntax_Print.quals_to_string quals)
in (FStar_Util.format2 "The qualifier list \"[%s]\" is not permissible for this element%s" _155_1077 msg))
in ((_155_1078), (r)))
in FStar_Syntax_Syntax.Error (_155_1079))
in (Prims.raise _155_1080)))
in (

let err = (fun msg -> (err' (Prims.strcat ": " msg)))
in (

let err' = (fun _57_1805 -> (match (()) with
| () -> begin
(err' "")
end))
in (

let _57_1806 = if ((FStar_List.length quals) <> (FStar_List.length no_dup_quals)) then begin
(err "duplicate qualifiers")
end else begin
()
end
in (

let _57_1808 = if (not ((FStar_All.pipe_right quals (FStar_List.for_all (quals_combo_ok quals))))) then begin
(err "ill-formed combination")
end else begin
()
end
in (match (se) with
| FStar_Syntax_Syntax.Sig_let ((is_rec, _57_1812), _57_1815, _57_1817, _57_1819, _57_1821) -> begin
(

let _57_1824 = if (is_rec && (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))) then begin
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
| FStar_Syntax_Syntax.Sig_bundle (_57_1828) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.Abstract) || (inferred x)) || (visibility x)) || (has_eq x))))))) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (_57_1832) -> begin
if (FStar_All.pipe_right quals (FStar_Util.for_some has_eq)) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_assume (_57_1835) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((visibility x) || (x = FStar_Syntax_Syntax.Assumption))))))) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_new_effect (_57_1839) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x))))))) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_57_1843) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((((x = FStar_Syntax_Syntax.TotalEffect) || (inferred x)) || (visibility x)) || (reification x))))))) then begin
(err' ())
end else begin
()
end
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (_57_1847) -> begin
if (not ((FStar_All.pipe_right quals (FStar_Util.for_all (fun x -> ((inferred x) || (visibility x))))))) then begin
(err' ())
end else begin
()
end
end
| _57_1851 -> begin
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

let inst_tc = (let _155_1119 = (let _155_1118 = (let _155_1117 = (let _155_1116 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _155_1116))
in ((_155_1117), (inst_univs)))
in FStar_Syntax_Syntax.Tm_uinst (_155_1118))
in (FStar_Syntax_Syntax.mk _155_1119 None p))
in (

let args = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _57_1873 -> (match (_57_1873) with
| (x, imp) -> begin
(let _155_1121 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_155_1121), (imp)))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app inst_tc args None p)))
in (

let unrefined_arg_binder = (let _155_1122 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder _155_1122))
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
in (let _155_1128 = (let _155_1127 = (let _155_1126 = (FStar_Syntax_Syntax.mk_Tm_uinst disc_fvar inst_univs)
in (let _155_1125 = (let _155_1124 = (let _155_1123 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _155_1123))
in (_155_1124)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _155_1126 _155_1125 None p)))
in (FStar_Syntax_Util.b2t _155_1127))
in (FStar_Syntax_Util.refine x _155_1128)))
in (let _155_1129 = (

let _57_1881 = (projectee arg_typ)
in {FStar_Syntax_Syntax.ppname = _57_1881.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1881.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = sort})
in (FStar_Syntax_Syntax.mk_binder _155_1129)))))
end
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (let _155_1131 = (FStar_List.map (fun _57_1888 -> (match (_57_1888) with
| (x, _57_1887) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end)) tps)
in (FStar_List.append _155_1131 fields))
in (

let imp_binders = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _57_1893 -> (match (_57_1893) with
| (x, _57_1892) -> begin
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

let only_decl = ((let _155_1133 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _155_1133)) || (let _155_1135 = (let _155_1134 = (FStar_TypeChecker_Env.current_module env)
in _155_1134.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _155_1135)))
in (

let quals = (let _155_1139 = (let _155_1138 = if (only_decl && ((FStar_All.pipe_left Prims.op_Negation env.FStar_TypeChecker_Env.is_iface) || env.FStar_TypeChecker_Env.admit)) then begin
(FStar_Syntax_Syntax.Assumption)::[]
end else begin
[]
end
in (let _155_1137 = (FStar_List.filter (fun _57_16 -> (match (_57_16) with
| FStar_Syntax_Syntax.Abstract -> begin
(not (only_decl))
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| _57_1902 -> begin
false
end)) iquals)
in (FStar_List.append _155_1138 _155_1137)))
in (FStar_List.append ((FStar_Syntax_Syntax.Discriminator (lid))::if only_decl then begin
(FStar_Syntax_Syntax.Logic)::[]
end else begin
[]
end) _155_1139))
in (

let binders = (FStar_List.append imp_binders ((unrefined_arg_binder)::[]))
in (

let t = (

let bool_typ = (let _155_1141 = (let _155_1140 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _155_1140))
in (FStar_Syntax_Syntax.mk_Total _155_1141))
in (let _155_1142 = (FStar_Syntax_Util.arrow binders bool_typ)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) _155_1142)))
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((discriminator_name), (uvs), (t), (quals), ((FStar_Ident.range_of_lid discriminator_name))))
in (

let _57_1908 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes"))) then begin
(let _155_1143 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a discriminator %s\n" _155_1143))
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

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _57_1913 -> (match (_57_1913) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in if (b && (j < ntps)) then begin
(let _155_1149 = (let _155_1148 = (let _155_1147 = (let _155_1146 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in ((_155_1146), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (_155_1147))
in (pos _155_1148))
in ((_155_1149), (b)))
end else begin
(let _155_1152 = (let _155_1151 = (let _155_1150 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_155_1150))
in (pos _155_1151))
in ((_155_1152), (b)))
end)
end))))
in (

let pat_true = (let _155_1156 = (let _155_1155 = (let _155_1154 = (let _155_1153 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in ((_155_1153), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (_155_1154))
in (pos _155_1155))
in ((_155_1156), (None), (FStar_Syntax_Const.exp_true_bool)))
in (

let pat_false = (let _155_1159 = (let _155_1158 = (let _155_1157 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_155_1157))
in (pos _155_1158))
in ((_155_1159), (None), (FStar_Syntax_Const.exp_false_bool)))
in (

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst unrefined_arg_binder))
in (let _155_1165 = (let _155_1164 = (let _155_1163 = (let _155_1162 = (FStar_Syntax_Util.branch pat_true)
in (let _155_1161 = (let _155_1160 = (FStar_Syntax_Util.branch pat_false)
in (_155_1160)::[])
in (_155_1162)::_155_1161))
in ((arg_exp), (_155_1163)))
in FStar_Syntax_Syntax.Tm_match (_155_1164))
in (FStar_Syntax_Syntax.mk _155_1165 None p))))))
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

let lb = (let _155_1168 = (let _155_1166 = (FStar_Syntax_Syntax.lid_as_fv discriminator_name dd None)
in FStar_Util.Inr (_155_1166))
in (let _155_1167 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = _155_1168; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _155_1167}))
in (

let impl = (let _155_1173 = (let _155_1172 = (let _155_1171 = (let _155_1170 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _155_1170 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_155_1171)::[])
in ((((false), ((lb)::[]))), (p), (_155_1172), (quals), ([])))
in FStar_Syntax_Syntax.Sig_let (_155_1173))
in (

let _57_1926 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes"))) then begin
(let _155_1174 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a discriminator %s\n" _155_1174))
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

let subst = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _57_1936 -> (match (_57_1936) with
| (a, _57_1935) -> begin
(

let _57_1940 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (_57_1940) with
| (field_name, _57_1939) -> begin
(

let field_proj_tm = (let _155_1178 = (let _155_1177 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.fv_to_tm _155_1177))
in (FStar_Syntax_Syntax.mk_Tm_uinst _155_1178 inst_univs))
in (

let proj = (FStar_Syntax_Syntax.mk_Tm_app field_proj_tm ((arg)::[]) None p)
in FStar_Syntax_Syntax.NT (((a), (proj)))))
end))
end))))
in (

let projectors_ses = (let _155_1221 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _57_1948 -> (match (_57_1948) with
| (x, _57_1947) -> begin
(

let p = (FStar_Syntax_Syntax.range_of_bv x)
in (

let _57_1953 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (_57_1953) with
| (field_name, _57_1952) -> begin
(

let t = (let _155_1183 = (let _155_1182 = (let _155_1181 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total _155_1181))
in (FStar_Syntax_Util.arrow binders _155_1182))
in (FStar_All.pipe_left (FStar_Syntax_Subst.close_univ_vars uvs) _155_1183))
in (

let only_decl = (((let _155_1184 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _155_1184)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (let _155_1186 = (let _155_1185 = (FStar_TypeChecker_Env.current_module env)
in _155_1185.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _155_1186)))
in (

let no_decl = false
in (

let quals = (fun q -> if only_decl then begin
(let _155_1190 = (FStar_List.filter (fun _57_17 -> (match (_57_17) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| _57_1962 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::_155_1190)
end else begin
q
end)
in (

let quals = (

let iquals = (FStar_All.pipe_right iquals (FStar_List.filter (fun _57_18 -> (match (_57_18) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| _57_1967 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals)))
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), (uvs), (t), (quals), ((FStar_Ident.range_of_lid field_name))))
in (

let _57_1971 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes"))) then begin
(let _155_1192 = (FStar_Syntax_Print.sigelt_to_string decl)
in (FStar_Util.print1 "Declaration of a projector %s\n" _155_1192))
end else begin
()
end
in if only_decl then begin
(decl)::[]
end else begin
(

let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _57_1977 -> (match (_57_1977) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in if ((i + ntps) = j) then begin
(let _155_1195 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in ((_155_1195), (b)))
end else begin
if (b && (j < ntps)) then begin
(let _155_1199 = (let _155_1198 = (let _155_1197 = (let _155_1196 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in ((_155_1196), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (_155_1197))
in (pos _155_1198))
in ((_155_1199), (b)))
end else begin
(let _155_1202 = (let _155_1201 = (let _155_1200 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_155_1200))
in (pos _155_1201))
in ((_155_1202), (b)))
end
end)
end))))
in (

let pat = (let _155_1207 = (let _155_1205 = (let _155_1204 = (let _155_1203 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in ((_155_1203), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (_155_1204))
in (pos _155_1205))
in (let _155_1206 = (FStar_Syntax_Syntax.bv_to_name projection)
in ((_155_1207), (None), (_155_1206))))
in (

let body = (let _155_1211 = (let _155_1210 = (let _155_1209 = (let _155_1208 = (FStar_Syntax_Util.branch pat)
in (_155_1208)::[])
in ((arg_exp), (_155_1209)))
in FStar_Syntax_Syntax.Tm_match (_155_1210))
in (FStar_Syntax_Syntax.mk _155_1211 None p))
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

let lb = (let _155_1214 = (let _155_1212 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (_155_1212))
in (let _155_1213 = (FStar_Syntax_Subst.close_univ_vars uvs imp)
in {FStar_Syntax_Syntax.lbname = _155_1214; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = lbtyp; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _155_1213}))
in (

let impl = (let _155_1219 = (let _155_1218 = (let _155_1217 = (let _155_1216 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _155_1216 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_155_1217)::[])
in ((((false), ((lb)::[]))), (p), (_155_1218), (quals), ([])))
in FStar_Syntax_Syntax.Sig_let (_155_1219))
in (

let _57_1988 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("LogTypes"))) then begin
(let _155_1220 = (FStar_Syntax_Print.sigelt_to_string impl)
in (FStar_Util.print1 "Implementation of a projector %s\n" _155_1220))
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
in (FStar_All.pipe_right _155_1221 FStar_List.flatten))
in (FStar_List.append discriminator_ses projectors_ses)))))))))))))))))))


let mk_data_operations : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env tcs se -> (match (se) with
| FStar_Syntax_Syntax.Sig_datacon (constr_lid, uvs, t, typ_lid, n_typars, quals, _57_2002, r) when (not ((FStar_Ident.lid_equals constr_lid FStar_Syntax_Const.lexcons_lid))) -> begin
(

let _57_2008 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (_57_2008) with
| (univ_opening, uvs) -> begin
(

let t = (FStar_Syntax_Subst.subst univ_opening t)
in (

let _57_2013 = (FStar_Syntax_Util.arrow_formals t)
in (match (_57_2013) with
| (formals, _57_2012) -> begin
(

let _57_2040 = (

let tps_opt = (FStar_Util.find_map tcs (fun se -> if (let _155_1231 = (FStar_Util.must (FStar_Syntax_Util.lid_of_sigelt se))
in (FStar_Ident.lid_equals typ_lid _155_1231)) then begin
(match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (_57_2016, uvs', tps, typ0, _57_2021, constrs, _57_2024, _57_2026) -> begin
(

let _57_2029 = ()
in Some (((tps), (typ0), (((FStar_List.length constrs) > (Prims.parse_int "1"))))))
end
| _57_2032 -> begin
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
in (match (_57_2040) with
| (inductive_tps, typ0, should_refine) -> begin
(

let inductive_tps = (FStar_Syntax_Subst.subst_binders univ_opening inductive_tps)
in (

let typ0 = (FStar_Syntax_Subst.subst univ_opening typ0)
in (

let _57_2046 = (FStar_Syntax_Util.arrow_formals typ0)
in (match (_57_2046) with
| (indices, _57_2045) -> begin
(

let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _57_19 -> (match (_57_19) with
| FStar_Syntax_Syntax.RecordConstructor (_57_2049) -> begin
true
end
| _57_2052 -> begin
false
end)))) then begin
false
end else begin
should_refine
end
in (

let fv_qual = (

let filter_records = (fun _57_20 -> (match (_57_20) with
| FStar_Syntax_Syntax.RecordConstructor (_57_2056, fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((constr_lid), (fns))))
end
| _57_2061 -> begin
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

let _57_2070 = (FStar_Util.first_N n_typars formals)
in (match (_57_2070) with
| (imp_tps, fields) -> begin
(

let rename = (FStar_List.map2 (fun _57_2074 _57_2078 -> (match (((_57_2074), (_57_2078))) with
| ((x, _57_2073), (x', _57_2077)) -> begin
(let _155_1238 = (let _155_1237 = (FStar_Syntax_Syntax.bv_to_name x')
in ((x), (_155_1237)))
in FStar_Syntax_Syntax.NT (_155_1238))
end)) imp_tps inductive_tps)
in (FStar_Syntax_Subst.subst_binders rename fields))
end))
in (mk_discriminator_and_indexed_projectors iquals fv_qual refine_domain env typ_lid constr_lid uvs inductive_tps indices fields)))))
end))))
end))
end)))
end))
end
| _57_2082 -> begin
[]
end))




