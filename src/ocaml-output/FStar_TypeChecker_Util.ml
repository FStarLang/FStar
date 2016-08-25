
open Prims

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv Prims.option * FStar_Syntax_Syntax.lcomp)


let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _149_6 = (FStar_TypeChecker_Env.get_range env)
in (let _149_5 = (FStar_TypeChecker_Errors.failed_to_prove_specification errs)
in (FStar_TypeChecker_Errors.report _149_6 _149_5))))


let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _149_9 = (FStar_Syntax_Subst.compress t)
in _149_9.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_56_12) -> begin
true
end
| _56_15 -> begin
false
end))


let t_binders : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env -> (let _149_13 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right _149_13 (FStar_List.filter (fun _56_20 -> (match (_56_20) with
| (x, _56_19) -> begin
(is_type x.FStar_Syntax_Syntax.sort)
end))))))


let new_uvar_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun env k -> (

let bs = if ((FStar_Options.full_context_dependency ()) || (let _149_18 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _149_18))) then begin
(FStar_TypeChecker_Env.all_binders env)
end else begin
(t_binders env)
end
in (let _149_19 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Rel.new_uvar _149_19 bs k))))


let new_uvar : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env k -> (let _149_24 = (new_uvar_aux env k)
in (Prims.fst _149_24)))


let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun _56_1 -> (match (_56_1) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, _56_35); FStar_Syntax_Syntax.tk = _56_32; FStar_Syntax_Syntax.pos = _56_30; FStar_Syntax_Syntax.vars = _56_28} -> begin
uv
end
| _56_40 -> begin
(FStar_All.failwith "Impossible")
end))


let new_implicit_var : Prims.string  ->  FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.uvar * FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t) = (fun reason r env k -> (match ((FStar_Syntax_Util.destruct k FStar_Syntax_Const.range_of_lid)) with
| Some ((_56_50)::((tm, _56_47))::[]) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos))) None tm.FStar_Syntax_Syntax.pos)
in ((t), ([]), (FStar_TypeChecker_Rel.trivial_guard)))
end
| _56_55 -> begin
(

let _56_58 = (new_uvar_aux env k)
in (match (_56_58) with
| (t, u) -> begin
(

let g = (

let _56_59 = FStar_TypeChecker_Rel.trivial_guard
in (let _149_37 = (let _149_36 = (let _149_35 = (as_uvar u)
in ((reason), (env), (_149_35), (t), (k), (r)))
in (_149_36)::[])
in {FStar_TypeChecker_Env.guard_f = _56_59.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _56_59.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_59.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _149_37}))
in (let _149_40 = (let _149_39 = (let _149_38 = (as_uvar u)
in ((_149_38), (r)))
in (_149_39)::[])
in ((t), (_149_40), (g))))
end))
end))


let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun r t -> (

let uvs = (FStar_Syntax_Free.uvars t)
in if (not ((FStar_Util.set_is_empty uvs))) then begin
(

let us = (let _149_47 = (let _149_46 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun _56_68 -> (match (_56_68) with
| (x, _56_67) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) _149_46))
in (FStar_All.pipe_right _149_47 (FStar_String.concat ", ")))
in (

let _56_70 = (FStar_Options.push ())
in (

let _56_72 = (FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool (false)))
in (

let _56_74 = (FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)))
in (

let _56_76 = (let _149_49 = (let _149_48 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us _149_48))
in (FStar_TypeChecker_Errors.report r _149_49))
in (FStar_Options.pop ()))))))
end else begin
()
end))


let force_sort' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' = (fun s -> (match ((FStar_ST.read s.FStar_Syntax_Syntax.tk)) with
| None -> begin
(let _149_54 = (let _149_53 = (FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos)
in (let _149_52 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s" _149_53 _149_52)))
in (FStar_All.failwith _149_54))
end
| Some (tk) -> begin
tk
end))


let force_sort = (fun s -> (let _149_56 = (force_sort' s)
in (FStar_Syntax_Syntax.mk _149_56 None s.FStar_Syntax_Syntax.pos)))


let extract_let_rec_annotation : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.typ * Prims.bool) = (fun env _56_91 -> (match (_56_91) with
| {FStar_Syntax_Syntax.lbname = _56_90; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _56_86; FStar_Syntax_Syntax.lbdef = e} -> begin
(

let rng = t.FStar_Syntax_Syntax.pos
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _56_95 = if (univ_vars <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let mk_binder = (fun scope a -> (match ((let _149_65 = (FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort)
in _149_65.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _56_105 = (FStar_Syntax_Util.type_u ())
in (match (_56_105) with
| (k, _56_104) -> begin
(

let t = (let _149_66 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right _149_66 Prims.fst))
in (((

let _56_107 = a
in {FStar_Syntax_Syntax.ppname = _56_107.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_107.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (false)))
end))
end
| _56_110 -> begin
((a), (true))
end))
in (

let rec aux = (fun vars e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, _56_117) -> begin
(aux vars e)
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _56_123) -> begin
((t), (true))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _56_129) -> begin
(

let _56_148 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _56_135 _56_138 -> (match (((_56_135), (_56_138))) with
| ((scope, bs, check), (a, imp)) -> begin
(

let _56_141 = (mk_binder scope a)
in (match (_56_141) with
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
in (match (_56_148) with
| (scope, bs, check) -> begin
(

let _56_151 = (aux scope body)
in (match (_56_151) with
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

let _56_158 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _149_74 = (FStar_Range.string_of_range r)
in (let _149_73 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _149_74 _149_73)))
end else begin
()
end
in ((FStar_Util.Inl (t)), ((check_res || check))))))
end))
end))
end
| _56_161 -> begin
(let _149_77 = (let _149_76 = (let _149_75 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _149_75 Prims.fst))
in FStar_Util.Inl (_149_76))
in ((_149_77), (false)))
end)))
in (

let _56_164 = (let _149_78 = (t_binders env)
in (aux _149_78 e))
in (match (_56_164) with
| (t, b) -> begin
(

let t = (match (t) with
| FStar_Util.Inr (c) -> begin
(let _149_82 = (let _149_81 = (let _149_80 = (let _149_79 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" _149_79))
in ((_149_80), (rng)))
in FStar_Syntax_Syntax.Error (_149_81))
in (Prims.raise _149_82))
end
| FStar_Util.Inl (t) -> begin
t
end)
in (([]), (t), (b)))
end))))))
end
| _56_171 -> begin
(

let _56_174 = (FStar_Syntax_Subst.open_univ_vars univ_vars t)
in (match (_56_174) with
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
| FStar_Syntax_Syntax.Pat_dot_term (x, _56_187) -> begin
(

let _56_193 = (FStar_Syntax_Util.type_u ())
in (match (_56_193) with
| (k, _56_192) -> begin
(

let t = (new_uvar env k)
in (

let x = (

let _56_195 = x
in {FStar_Syntax_Syntax.ppname = _56_195.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_195.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let _56_200 = (let _149_95 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _149_95 t))
in (match (_56_200) with
| (e, u) -> begin
(

let p = (

let _56_201 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (e))); FStar_Syntax_Syntax.ty = _56_201.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_201.FStar_Syntax_Syntax.p})
in (([]), ([]), ([]), (env), (e), (p)))
end))))
end))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let _56_209 = (FStar_Syntax_Util.type_u ())
in (match (_56_209) with
| (t, _56_208) -> begin
(

let x = (

let _56_210 = x
in (let _149_96 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _56_210.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_210.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_96}))
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

let _56_220 = (FStar_Syntax_Util.type_u ())
in (match (_56_220) with
| (t, _56_219) -> begin
(

let x = (

let _56_221 = x
in (let _149_97 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _56_221.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_221.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_97}))
in (

let env = (FStar_TypeChecker_Env.push_bv env x)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in (((x)::[]), ((x)::[]), ([]), (env), (e), (p)))))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _56_254 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _56_236 _56_239 -> (match (((_56_236), (_56_239))) with
| ((b, a, w, env, args, pats), (p, imp)) -> begin
(

let _56_246 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_56_246) with
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
in (match (_56_254) with
| (b, a, w, env, args, pats) -> begin
(

let e = (let _149_104 = (let _149_103 = (let _149_102 = (let _149_101 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (let _149_100 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app _149_101 _149_100 None p.FStar_Syntax_Syntax.p)))
in ((_149_102), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))
in FStar_Syntax_Syntax.Tm_meta (_149_103))
in (FStar_Syntax_Syntax.mk _149_104 None p.FStar_Syntax_Syntax.p))
in (let _149_107 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _149_106 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _149_105 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in ((_149_107), (_149_106), (_149_105), (env), (e), ((

let _56_256 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _56_256.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_256.FStar_Syntax_Syntax.p})))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (_56_259) -> begin
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

let pats = (FStar_List.map (fun _56_274 -> (match (_56_274) with
| (p, imp) -> begin
(let _149_119 = (elaborate_pat env p)
in ((_149_119), (imp)))
end)) pats)
in (

let _56_279 = (FStar_TypeChecker_Env.lookup_datacon env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_56_279) with
| (_56_277, t) -> begin
(

let _56_283 = (FStar_Syntax_Util.arrow_formals t)
in (match (_56_283) with
| (f, _56_282) -> begin
(

let rec aux = (fun formals pats -> (match (((formals), (pats))) with
| ([], []) -> begin
[]
end
| ([], (_56_294)::_56_292) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Too many pattern arguments"), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))))
end
| ((_56_300)::_56_298, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun _56_306 -> (match (_56_306) with
| (t, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(

let a = (let _149_126 = (let _149_125 = (FStar_Syntax_Syntax.range_of_bv t)
in Some (_149_125))
in (FStar_Syntax_Syntax.new_bv _149_126 FStar_Syntax_Syntax.tun))
in (

let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (let _149_127 = (maybe_dot inaccessible a r)
in ((_149_127), (true)))))
end
| _56_313 -> begin
(let _149_131 = (let _149_130 = (let _149_129 = (let _149_128 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _149_128))
in ((_149_129), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))
in FStar_Syntax_Syntax.Error (_149_130))
in (Prims.raise _149_131))
end)
end))))
end
| ((f)::formals', ((p, p_imp))::pats') -> begin
(match (f) with
| (_56_324, Some (FStar_Syntax_Syntax.Implicit (_56_326))) when p_imp -> begin
(let _149_132 = (aux formals' pats')
in (((p), (true)))::_149_132)
end
| (_56_331, Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(

let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let p = (maybe_dot inaccessible a (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
in (let _149_133 = (aux formals' pats)
in (((p), (true)))::_149_133)))
end
| (_56_339, imp) -> begin
(let _149_136 = (let _149_134 = (FStar_Syntax_Syntax.is_implicit imp)
in ((p), (_149_134)))
in (let _149_135 = (aux formals' pats')
in (_149_136)::_149_135))
end)
end))
in (

let _56_342 = p
in (let _149_139 = (let _149_138 = (let _149_137 = (aux f pats)
in ((fv), (_149_137)))
in FStar_Syntax_Syntax.Pat_cons (_149_138))
in {FStar_Syntax_Syntax.v = _149_139; FStar_Syntax_Syntax.ty = _56_342.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_342.FStar_Syntax_Syntax.p})))
end))
end)))
end
| _56_345 -> begin
p
end)))
in (

let one_pat = (fun allow_wc_dependence env p -> (

let p = (elaborate_pat env p)
in (

let _56_357 = (pat_as_arg_with_env allow_wc_dependence env p)
in (match (_56_357) with
| (b, a, w, env, arg, p) -> begin
(match ((FStar_All.pipe_right b (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq))) with
| Some (x) -> begin
(let _149_148 = (let _149_147 = (let _149_146 = (FStar_TypeChecker_Errors.nonlinear_pattern_variable x)
in ((_149_146), (p.FStar_Syntax_Syntax.p)))
in FStar_Syntax_Syntax.Error (_149_147))
in (Prims.raise _149_148))
end
| _56_361 -> begin
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

let _56_377 = (one_pat false env q)
in (match (_56_377) with
| (b, a, _56_374, te, q) -> begin
(

let _56_392 = (FStar_List.fold_right (fun p _56_382 -> (match (_56_382) with
| (w, args, pats) -> begin
(

let _56_388 = (one_pat false env p)
in (match (_56_388) with
| (b', a', w', arg, p) -> begin
if (not ((FStar_Util.multiset_equiv FStar_Syntax_Syntax.bv_eq a a'))) then begin
(let _149_158 = (let _149_157 = (let _149_156 = (FStar_TypeChecker_Errors.disjunctive_pattern_vars a a')
in (let _149_155 = (FStar_TypeChecker_Env.get_range env)
in ((_149_156), (_149_155))))
in FStar_Syntax_Syntax.Error (_149_157))
in (Prims.raise _149_158))
end else begin
(let _149_160 = (let _149_159 = (FStar_Syntax_Syntax.as_arg arg)
in (_149_159)::args)
in (((FStar_List.append w' w)), (_149_160), ((p)::pats)))
end
end))
end)) pats (([]), ([]), ([])))
in (match (_56_392) with
| (w, args, pats) -> begin
(let _149_162 = (let _149_161 = (FStar_Syntax_Syntax.as_arg te)
in (_149_161)::args)
in (((FStar_List.append b w)), (_149_162), ((

let _56_393 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((q)::pats); FStar_Syntax_Syntax.ty = _56_393.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_393.FStar_Syntax_Syntax.p}))))
end))
end))
end
| _56_396 -> begin
(

let _56_404 = (one_pat true env p)
in (match (_56_404) with
| (b, _56_399, _56_401, arg, p) -> begin
(let _149_164 = (let _149_163 = (FStar_Syntax_Syntax.as_arg arg)
in (_149_163)::[])
in ((b), (_149_164), (p)))
end))
end))
in (

let _56_408 = (top_level_pat_as_args env p)
in (match (_56_408) with
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
| (_56_422, FStar_Syntax_Syntax.Tm_uinst (e, _56_425)) -> begin
(aux p e)
end
| (FStar_Syntax_Syntax.Pat_constant (_56_430), FStar_Syntax_Syntax.Tm_constant (_56_433)) -> begin
(let _149_179 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v _149_179))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(

let _56_441 = if (not ((FStar_Syntax_Syntax.bv_eq x y))) then begin
(let _149_182 = (let _149_181 = (FStar_Syntax_Print.bv_to_string x)
in (let _149_180 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _149_181 _149_180)))
in (FStar_All.failwith _149_182))
end else begin
()
end
in (

let _56_443 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _149_184 = (FStar_Syntax_Print.bv_to_string x)
in (let _149_183 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _149_184 _149_183)))
end else begin
()
end
in (

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x = (

let _56_446 = x
in {FStar_Syntax_Syntax.ppname = _56_446.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_446.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_var (x)) s.FStar_Syntax_Syntax.n)))))
end
| (FStar_Syntax_Syntax.Pat_wild (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(

let _56_454 = if (FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y) Prims.op_Negation) then begin
(let _149_187 = (let _149_186 = (FStar_Syntax_Print.bv_to_string x)
in (let _149_185 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _149_186 _149_185)))
in (FStar_All.failwith _149_187))
end else begin
()
end
in (

let s = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env y.FStar_Syntax_Syntax.sort)
in (

let x = (

let _56_457 = x
in {FStar_Syntax_Syntax.ppname = _56_457.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_457.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_wild (x)) s.FStar_Syntax_Syntax.n))))
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _56_462), _56_466) -> begin
(

let s = (force_sort e)
in (

let x = (

let _56_469 = x
in {FStar_Syntax_Syntax.ppname = _56_469.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_469.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = s})
in (pkg (FStar_Syntax_Syntax.Pat_dot_term (((x), (e)))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
(

let _56_479 = if (not ((FStar_Syntax_Syntax.fv_eq fv fv'))) then begin
(let _149_188 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _149_188))
end else begin
()
end
in (let _149_189 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv'), ([])))) _149_189)))
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
(

let _56_522 = if (let _149_190 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right _149_190 Prims.op_Negation)) then begin
(let _149_191 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _149_191))
end else begin
()
end
in (

let fv = fv'
in (

let rec match_args = (fun matched_pats args argpats -> (match (((args), (argpats))) with
| ([], []) -> begin
(let _149_198 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev matched_pats))))) _149_198))
end
| ((arg)::args, ((argpat, _56_538))::argpats) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e, Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (_56_548)) -> begin
(

let x = (let _149_199 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _149_199))
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e)))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args argpats)))
end
| ((e, imp), _56_557) -> begin
(

let pat = (let _149_201 = (aux argpat e)
in (let _149_200 = (FStar_Syntax_Syntax.is_implicit imp)
in ((_149_201), (_149_200))))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _56_561 -> begin
(let _149_204 = (let _149_203 = (FStar_Syntax_Print.pat_to_string p)
in (let _149_202 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _149_203 _149_202)))
in (FStar_All.failwith _149_204))
end))
in (match_args [] args argpats))))
end
| _56_563 -> begin
(let _149_209 = (let _149_208 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (let _149_207 = (FStar_Syntax_Print.pat_to_string qq)
in (let _149_206 = (let _149_205 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right _149_205 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _149_208 _149_207 _149_206))))
in (FStar_All.failwith _149_209))
end))))
in (match (((p.FStar_Syntax_Syntax.v), (exps))) with
| (FStar_Syntax_Syntax.Pat_disj (ps), _56_567) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(

let ps = (FStar_List.map2 aux ps exps)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj (ps)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p))
end
| (_56_571, (e)::[]) -> begin
(aux p e)
end
| _56_576 -> begin
(FStar_All.failwith "Unexpected number of patterns")
end))))


let rec decorated_pattern_as_term : FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term) = (fun pat -> (

let topt = Some (pat.FStar_Syntax_Syntax.ty)
in (

let mk = (fun f -> (FStar_Syntax_Syntax.mk f topt pat.FStar_Syntax_Syntax.p))
in (

let pat_as_arg = (fun _56_584 -> (match (_56_584) with
| (p, i) -> begin
(

let _56_587 = (decorated_pattern_as_term p)
in (match (_56_587) with
| (vars, te) -> begin
(let _149_217 = (let _149_216 = (FStar_Syntax_Syntax.as_implicit i)
in ((te), (_149_216)))
in ((vars), (_149_217)))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_56_589) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _149_218 = (mk (FStar_Syntax_Syntax.Tm_constant (c)))
in (([]), (_149_218)))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(let _149_219 = (mk (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (_149_219)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _56_602 = (let _149_220 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _149_220 FStar_List.unzip))
in (match (_56_602) with
| (vars, args) -> begin
(

let vars = (FStar_List.flatten vars)
in (let _149_224 = (let _149_223 = (let _149_222 = (let _149_221 = (FStar_Syntax_Syntax.fv_to_tm fv)
in ((_149_221), (args)))
in FStar_Syntax_Syntax.Tm_app (_149_222))
in (mk _149_223))
in ((vars), (_149_224))))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
(([]), (e))
end)))))


let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.typ * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun c -> (

let wp = (match (c.FStar_Syntax_Syntax.effect_args) with
| ((wp, _56_611))::[] -> begin
wp
end
| _56_615 -> begin
(let _149_230 = (let _149_229 = (let _149_228 = (FStar_List.map (fun _56_619 -> (match (_56_619) with
| (x, _56_618) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right _149_228 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str _149_229))
in (FStar_All.failwith _149_230))
end)
in ((c.FStar_Syntax_Syntax.result_typ), (wp))))


let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (

let _56_627 = (destruct_comp c)
in (match (_56_627) with
| (_56_625, wp) -> begin
(let _149_249 = (let _149_248 = (let _149_247 = (lift c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _149_247))
in (_149_248)::[])
in {FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _149_249; FStar_Syntax_Syntax.flags = []})
end)))


let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let _56_636 = (let _149_257 = (FStar_TypeChecker_Env.norm_eff_name env l1)
in (let _149_256 = (FStar_TypeChecker_Env.norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _149_257 _149_256)))
in (match (_56_636) with
| (m, _56_633, _56_635) -> begin
m
end)))


let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> if ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2)) then begin
FStar_Syntax_Const.effect_Tot_lid
end else begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)


let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.typ * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) * (FStar_Syntax_Syntax.typ * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)) = (fun env c1 c2 -> (

let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (

let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (

let _56_648 = (FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (_56_648) with
| (m, lift1, lift2) -> begin
(

let m1 = (lift_comp c1 m lift1)
in (

let m2 = (lift_comp c2 m lift2)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (

let _56_654 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (_56_654) with
| (a, kwp) -> begin
(let _149_271 = (destruct_comp m1)
in (let _149_270 = (destruct_comp m2)
in ((((md), (a), (kwp))), (_149_271), (_149_270))))
end)))))
end)))))


let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid))))


let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md result wp flags -> (let _149_290 = (let _149_289 = (let _149_288 = (FStar_Syntax_Syntax.as_arg wp)
in (_149_288)::[])
in {FStar_Syntax_Syntax.effect_name = md.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = _149_289; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp _149_290)))


let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (

let _56_667 = lc
in (let _149_297 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _56_667.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _149_297; FStar_Syntax_Syntax.cflags = _56_667.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _56_669 -> (match (()) with
| () -> begin
(let _149_296 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _149_296))
end))})))


let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _149_300 = (FStar_Syntax_Subst.compress t)
in _149_300.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_56_672) -> begin
true
end
| _56_675 -> begin
false
end))


let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v -> (

let c = if (let _149_307 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation _149_307)) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(

let m = (let _149_308 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must _149_308))
in (

let _56_682 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_56_682) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let wp = (let _149_316 = (let _149_315 = (let _149_310 = (let _149_309 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_149_309)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _149_310 env m m.FStar_Syntax_Syntax.ret_wp))
in (let _149_314 = (let _149_313 = (FStar_Syntax_Syntax.as_arg t)
in (let _149_312 = (let _149_311 = (FStar_Syntax_Syntax.as_arg v)
in (_149_311)::[])
in (_149_313)::_149_312))
in (FStar_Syntax_Syntax.mk_Tm_app _149_315 _149_314 (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _149_316))
in (mk_comp m t wp ((FStar_Syntax_Syntax.RETURN)::[]))))
end)))
end
in (

let _56_686 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return"))) then begin
(let _149_319 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _149_318 = (FStar_Syntax_Print.term_to_string v)
in (let _149_317 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _149_319 _149_318 _149_317))))
end else begin
()
end
in c)))


let bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r1 env e1opt lc1 _56_694 -> (match (_56_694) with
| (b, lc2) -> begin
(

let lc1 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1)
in (

let lc2 = (FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2)
in (

let _56_704 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(

let bstr = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _149_332 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (let _149_331 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _149_330 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" _149_332 _149_331 bstr _149_330)))))
end else begin
()
end
in (

let bind_it = (fun _56_707 -> (match (()) with
| () -> begin
(

let c1 = (lc1.FStar_Syntax_Syntax.comp ())
in (

let c2 = (lc2.FStar_Syntax_Syntax.comp ())
in (

let _56_713 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _149_339 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _149_338 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _149_337 = (FStar_Syntax_Print.comp_to_string c1)
in (let _149_336 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (let _149_335 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" _149_339 _149_338 _149_337 _149_336 _149_335))))))
end else begin
()
end
in (

let try_simplify = (fun _56_716 -> (match (()) with
| () -> begin
(

let aux = (fun _56_718 -> (match (()) with
| () -> begin
if (FStar_Syntax_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some (((c2), ("trivial no binder")))
end
| Some (_56_721) -> begin
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
(let _149_347 = (let _149_346 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in ((_149_346), (reason)))
in Some (_149_347))
end
| _56_731 -> begin
(aux ())
end))
in if ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2)) then begin
(subst_c2 "both total")
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2)) then begin
(let _149_349 = (let _149_348 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((_149_348), ("both gtot")))
in Some (_149_349))
end else begin
(match (((e1opt), (b))) with
| (Some (e), Some (x)) -> begin
if ((FStar_Syntax_Util.is_total_comp c1) && (not ((FStar_Syntax_Syntax.is_null_bv x)))) then begin
(subst_c2 "substituted e")
end else begin
(aux ())
end
end
| _56_738 -> begin
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

let _56_754 = (lift_and_destruct env c1 c2)
in (match (_56_754) with
| ((md, a, kwp), (t1, wp1), (t2, wp2)) -> begin
(

let bs = (match (b) with
| None -> begin
(let _149_350 = (FStar_Syntax_Syntax.null_binder t1)
in (_149_350)::[])
end
| Some (x) -> begin
(let _149_351 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_351)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid)))))
in (

let r1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1))) None r1)
in (

let wp_args = (let _149_363 = (FStar_Syntax_Syntax.as_arg r1)
in (let _149_362 = (let _149_361 = (FStar_Syntax_Syntax.as_arg t1)
in (let _149_360 = (let _149_359 = (FStar_Syntax_Syntax.as_arg t2)
in (let _149_358 = (let _149_357 = (FStar_Syntax_Syntax.as_arg wp1)
in (let _149_356 = (let _149_355 = (let _149_354 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg _149_354))
in (_149_355)::[])
in (_149_357)::_149_356))
in (_149_359)::_149_358))
in (_149_361)::_149_360))
in (_149_363)::_149_362))
in (

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t2))))::[]) kwp)
in (

let us = (let _149_366 = (env.FStar_TypeChecker_Env.universe_of env t1)
in (let _149_365 = (let _149_364 = (env.FStar_TypeChecker_Env.universe_of env t2)
in (_149_364)::[])
in (_149_366)::_149_365))
in (

let wp = (let _149_367 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _149_367 wp_args None t2.FStar_Syntax_Syntax.pos))
in (

let c = (mk_comp md t2 wp [])
in c))))))))
end))
end)))))
end))
in (let _149_368 = (join_lcomp env lc1 lc2)
in {FStar_Syntax_Syntax.eff_name = _149_368; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it})))))
end))


let lift_formula : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t mk_wp f -> (

let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (

let _56_774 = (FStar_TypeChecker_Env.wp_signature env md_pure.FStar_Syntax_Syntax.mname)
in (match (_56_774) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let wp = (let _149_380 = (let _149_379 = (FStar_Syntax_Syntax.as_arg t)
in (let _149_378 = (let _149_377 = (FStar_Syntax_Syntax.as_arg f)
in (_149_377)::[])
in (_149_379)::_149_378))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wp _149_380 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (mk_comp md_pure FStar_TypeChecker_Common.t_unit wp [])))
end))))


let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((f), (FStar_Syntax_Syntax.Meta_labeled (((reason), (r), (false))))))) None f.FStar_Syntax_Syntax.pos))


let label_opt : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _149_404 = (FStar_TypeChecker_Env.should_verify env)
in (FStar_All.pipe_left Prims.op_Negation _149_404)) then begin
f
end else begin
(let _149_405 = (reason ())
in (label _149_405 r f))
end
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let _56_793 = g
in (let _149_413 = (let _149_412 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_149_412))
in {FStar_TypeChecker_Env.guard_f = _149_413; FStar_TypeChecker_Env.deferred = _56_793.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_793.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_793.FStar_TypeChecker_Env.implicits}))
end))


let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| _56_804 -> begin
g2
end))


let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun _56_809 -> (match (()) with
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

let _56_817 = (destruct_comp c)
in (match (_56_817) with
| (res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let us = (let _149_426 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_149_426)::[])
in (

let wp = (let _149_433 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _149_432 = (let _149_431 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _149_430 = (let _149_429 = (FStar_Syntax_Syntax.as_arg f)
in (let _149_428 = (let _149_427 = (FStar_Syntax_Syntax.as_arg wp)
in (_149_427)::[])
in (_149_429)::_149_428))
in (_149_431)::_149_430))
in (FStar_Syntax_Syntax.mk_Tm_app _149_433 _149_432 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp c.FStar_Syntax_Syntax.flags))))
end)))
end
end))
end))
in (

let _56_821 = lc
in {FStar_Syntax_Syntax.eff_name = _56_821.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _56_821.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _56_821.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))


let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> if (FStar_TypeChecker_Rel.is_trivial g0) then begin
((lc), (g0))
end else begin
(

let _56_828 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _149_453 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _149_452 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _149_453 _149_452)))
end else begin
()
end
in (

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _56_2 -> (match (_56_2) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _56_834 -> begin
[]
end))))
in (

let strengthen = (fun _56_837 -> (match (()) with
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

let xret = (let _149_458 = (let _149_457 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _149_457))
in (FStar_Syntax_Util.comp_set_flags _149_458 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (

let lc = (bind e.FStar_Syntax_Syntax.pos env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) ((Some (x)), ((FStar_Syntax_Util.lcomp_of_comp xret))))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (

let _56_847 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _149_460 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _149_459 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _149_460 _149_459)))
end else begin
()
end
in (

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _56_852 = (destruct_comp c)
in (match (_56_852) with
| (res_t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let us = (let _149_461 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_149_461)::[])
in (

let wp = (let _149_470 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assert_p)
in (let _149_469 = (let _149_468 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _149_467 = (let _149_466 = (let _149_463 = (let _149_462 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason _149_462 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _149_463))
in (let _149_465 = (let _149_464 = (FStar_Syntax_Syntax.as_arg wp)
in (_149_464)::[])
in (_149_466)::_149_465))
in (_149_468)::_149_467))
in (FStar_Syntax_Syntax.mk_Tm_app _149_470 _149_469 None wp.FStar_Syntax_Syntax.pos)))
in (

let _56_856 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _149_471 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _149_471))
end else begin
()
end
in (

let c2 = (mk_comp md res_t wp flags)
in c2)))))
end)))))
end)))
end))
in (let _149_475 = (

let _56_859 = lc
in (let _149_474 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _149_473 = if ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _149_472 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _149_472))) then begin
flags
end else begin
[]
end
in {FStar_Syntax_Syntax.eff_name = _149_474; FStar_Syntax_Syntax.res_typ = _56_859.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _149_473; FStar_Syntax_Syntax.comp = strengthen})))
in ((_149_475), ((

let _56_861 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _56_861.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_861.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_861.FStar_TypeChecker_Env.implicits})))))))
end)


let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env comp res_t -> (

let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let y = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let _56_871 = (let _149_483 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _149_482 = (FStar_Syntax_Syntax.bv_to_name y)
in ((_149_483), (_149_482))))
in (match (_56_871) with
| (xexp, yexp) -> begin
(

let us = (let _149_484 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_149_484)::[])
in (

let yret = (let _149_489 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret_wp)
in (let _149_488 = (let _149_487 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _149_486 = (let _149_485 = (FStar_Syntax_Syntax.as_arg yexp)
in (_149_485)::[])
in (_149_487)::_149_486))
in (FStar_Syntax_Syntax.mk_Tm_app _149_489 _149_488 None res_t.FStar_Syntax_Syntax.pos)))
in (

let x_eq_y_yret = (let _149_497 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _149_496 = (let _149_495 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _149_494 = (let _149_493 = (let _149_490 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _149_490))
in (let _149_492 = (let _149_491 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_149_491)::[])
in (_149_493)::_149_492))
in (_149_495)::_149_494))
in (FStar_Syntax_Syntax.mk_Tm_app _149_497 _149_496 None res_t.FStar_Syntax_Syntax.pos)))
in (

let forall_y_x_eq_y_yret = (let _149_507 = (FStar_TypeChecker_Env.inst_effect_fun_with (FStar_List.append us us) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _149_506 = (let _149_505 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _149_504 = (let _149_503 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _149_502 = (let _149_501 = (let _149_500 = (let _149_499 = (let _149_498 = (FStar_Syntax_Syntax.mk_binder y)
in (_149_498)::[])
in (FStar_Syntax_Util.abs _149_499 x_eq_y_yret (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid)))))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _149_500))
in (_149_501)::[])
in (_149_503)::_149_502))
in (_149_505)::_149_504))
in (FStar_Syntax_Syntax.mk_Tm_app _149_507 _149_506 None res_t.FStar_Syntax_Syntax.pos)))
in (

let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (

let lc = (let _149_508 = (FStar_TypeChecker_Env.get_range env)
in (bind _149_508 env None (FStar_Syntax_Util.lcomp_of_comp comp) ((Some (x)), ((FStar_Syntax_Util.lcomp_of_comp lc2)))))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))


let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (

let comp = (fun _56_883 -> (match (()) with
| () -> begin
(

let _56_897 = (let _149_520 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _149_519 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _149_520 _149_519)))
in (match (_56_897) with
| ((md, _56_886, _56_888), (res_t, wp_then), (_56_894, wp_else)) -> begin
(

let us = (let _149_521 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_149_521)::[])
in (

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _149_541 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _149_540 = (let _149_538 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _149_537 = (let _149_536 = (FStar_Syntax_Syntax.as_arg g)
in (let _149_535 = (let _149_534 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _149_533 = (let _149_532 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_149_532)::[])
in (_149_534)::_149_533))
in (_149_536)::_149_535))
in (_149_538)::_149_537))
in (let _149_539 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _149_541 _149_540 None _149_539)))))
in (

let wp = (ifthenelse md res_t guard wp_then wp_else)
in if ((FStar_Options.split_cases ()) > (Prims.parse_int "0")) then begin
(

let comp = (mk_comp md res_t wp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(

let wp = (let _149_546 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _149_545 = (let _149_544 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _149_543 = (let _149_542 = (FStar_Syntax_Syntax.as_arg wp)
in (_149_542)::[])
in (_149_544)::_149_543))
in (FStar_Syntax_Syntax.mk_Tm_app _149_546 _149_545 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp []))
end)))
end))
end))
in (let _149_547 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _149_547; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp})))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (let _149_553 = (let _149_552 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid _149_552))
in (FStar_Syntax_Syntax.fvar _149_553 FStar_Syntax_Syntax.Delta_constant None)))


let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (FStar_List.fold_left (fun eff _56_917 -> (match (_56_917) with
| (_56_915, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (

let bind_cases = (fun _56_920 -> (match (()) with
| () -> begin
(

let us = (let _149_564 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_149_564)::[])
in (

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _149_584 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _149_583 = (let _149_581 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _149_580 = (let _149_579 = (FStar_Syntax_Syntax.as_arg g)
in (let _149_578 = (let _149_577 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _149_576 = (let _149_575 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_149_575)::[])
in (_149_577)::_149_576))
in (_149_579)::_149_578))
in (_149_581)::_149_580))
in (let _149_582 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _149_584 _149_583 None _149_582)))))
in (

let default_case = (

let post_k = (let _149_587 = (let _149_585 = (FStar_Syntax_Syntax.null_binder res_t)
in (_149_585)::[])
in (let _149_586 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _149_587 _149_586)))
in (

let kwp = (let _149_590 = (let _149_588 = (FStar_Syntax_Syntax.null_binder post_k)
in (_149_588)::[])
in (let _149_589 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _149_590 _149_589)))
in (

let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (

let wp = (let _149_596 = (let _149_591 = (FStar_Syntax_Syntax.mk_binder post)
in (_149_591)::[])
in (let _149_595 = (let _149_594 = (let _149_592 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Errors.exhaustiveness_check _149_592))
in (let _149_593 = (fvar_const env FStar_Syntax_Const.false_lid)
in (FStar_All.pipe_left _149_594 _149_593)))
in (FStar_Syntax_Util.abs _149_596 _149_595 (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md res_t wp []))))))
in (

let comp = (FStar_List.fold_right (fun _56_936 celse -> (match (_56_936) with
| (g, cthen) -> begin
(

let _56_952 = (let _149_599 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _149_599 celse))
in (match (_56_952) with
| ((md, _56_940, _56_942), (_56_945, wp_then), (_56_949, wp_else)) -> begin
(let _149_600 = (ifthenelse md res_t g wp_then wp_else)
in (mk_comp md res_t _149_600 []))
end))
end)) lcases default_case)
in if ((FStar_Options.split_cases ()) > (Prims.parse_int "0")) then begin
(add_equality_to_post_condition env comp res_t)
end else begin
(

let comp = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env comp.FStar_Syntax_Syntax.effect_name)
in (

let _56_959 = (destruct_comp comp)
in (match (_56_959) with
| (_56_957, wp) -> begin
(

let wp = (let _149_605 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _149_604 = (let _149_603 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _149_602 = (let _149_601 = (FStar_Syntax_Syntax.as_arg wp)
in (_149_601)::[])
in (_149_603)::_149_602))
in (FStar_Syntax_Syntax.mk_Tm_app _149_605 _149_604 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp []))
end))))
end))))
end))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))


let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (

let close = (fun _56_965 -> (match (()) with
| () -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in if (FStar_Syntax_Util.is_ml_comp c) then begin
c
end else begin
(

let close_wp = (fun u_res md res_t bvs wp0 -> (FStar_List.fold_right (fun x wp -> (

let bs = (let _149_626 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_626)::[])
in (

let us = (let _149_628 = (let _149_627 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (_149_627)::[])
in (u_res)::_149_628)
in (

let wp = (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid))))
in (let _149_635 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (let _149_634 = (let _149_633 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _149_632 = (let _149_631 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _149_630 = (let _149_629 = (FStar_Syntax_Syntax.as_arg wp)
in (_149_629)::[])
in (_149_631)::_149_630))
in (_149_633)::_149_632))
in (FStar_Syntax_Syntax.mk_Tm_app _149_635 _149_634 None wp0.FStar_Syntax_Syntax.pos))))))) bvs wp0))
in (

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _56_981 = (destruct_comp c)
in (match (_56_981) with
| (t, wp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let u_res = (env.FStar_TypeChecker_Env.universe_of env c.FStar_Syntax_Syntax.result_typ)
in (

let wp = (close_wp u_res md c.FStar_Syntax_Syntax.result_typ bvs wp)
in (mk_comp md c.FStar_Syntax_Syntax.result_typ wp c.FStar_Syntax_Syntax.flags))))
end))))
end)
end))
in (

let _56_985 = lc
in {FStar_Syntax_Syntax.eff_name = _56_985.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _56_985.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _56_985.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))


let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (

let refine = (fun _56_991 -> (match (()) with
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
(let _149_646 = (let _149_645 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _149_644 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _149_645 _149_644)))
in (FStar_All.failwith _149_646))
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

let ret = (let _149_648 = (let _149_647 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _149_647 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _149_648))
in (

let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (

let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (

let c = (let _149_650 = (let _149_649 = (bind e.FStar_Syntax_Syntax.pos env None (FStar_Syntax_Util.lcomp_of_comp c) ((Some (x)), (eq_ret)))
in (_149_649.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _149_650 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
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

let _56_1003 = lc
in {FStar_Syntax_Syntax.eff_name = _56_1003.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _56_1003.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))


let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (match ((FStar_TypeChecker_Rel.sub_comp env c c')) with
| None -> begin
(let _149_662 = (let _149_661 = (let _149_660 = (FStar_TypeChecker_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _149_659 = (FStar_TypeChecker_Env.get_range env)
in ((_149_660), (_149_659))))
in FStar_Syntax_Syntax.Error (_149_661))
in (Prims.raise _149_662))
end
| Some (g) -> begin
((e), (c'), (g))
end))


let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match ((let _149_671 = (FStar_Syntax_Subst.compress t)
in _149_671.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_56_1017) -> begin
(match ((let _149_672 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _149_672.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid) -> begin
(

let _56_1021 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (

let b2t = (let _149_673 = (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar _149_673 (FStar_Syntax_Syntax.Delta_unfoldable ((Prims.parse_int "1"))) None))
in (

let lc = (let _149_676 = (let _149_675 = (let _149_674 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _149_674))
in ((None), (_149_675)))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) lc _149_676))
in (

let e = (let _149_678 = (let _149_677 = (FStar_Syntax_Syntax.as_arg e)
in (_149_677)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _149_678 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in ((e), (lc))))))
end
| _56_1027 -> begin
((e), (lc))
end)
end
| _56_1029 -> begin
((e), (lc))
end))


let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (

let gopt = if env.FStar_TypeChecker_Env.use_eq then begin
(let _149_687 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in ((_149_687), (false)))
end else begin
(let _149_688 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in ((_149_688), (true)))
end
in (match (gopt) with
| (None, _56_1037) -> begin
(

let _56_1039 = (FStar_TypeChecker_Rel.subtype_fail env lc.FStar_Syntax_Syntax.res_typ t)
in ((e), ((

let _56_1041 = lc
in {FStar_Syntax_Syntax.eff_name = _56_1041.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _56_1041.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _56_1041.FStar_Syntax_Syntax.comp})), (FStar_TypeChecker_Rel.trivial_guard)))
end
| (Some (g), apply_guard) -> begin
(match ((FStar_TypeChecker_Rel.guard_form g)) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let lc = (

let _56_1048 = lc
in {FStar_Syntax_Syntax.eff_name = _56_1048.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _56_1048.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _56_1048.FStar_Syntax_Syntax.comp})
in ((e), (lc), (g)))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let g = (

let _56_1053 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _56_1053.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_1053.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_1053.FStar_TypeChecker_Env.implicits})
in (

let strengthen = (fun _56_1057 -> (match (()) with
| () -> begin
(

let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (match ((let _149_691 = (FStar_Syntax_Subst.compress f)
in _149_691.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_56_1060, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _56_1066; FStar_Syntax_Syntax.pos = _56_1064; FStar_Syntax_Syntax.vars = _56_1062}, _56_1071) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
(

let lc = (

let _56_1074 = lc
in {FStar_Syntax_Syntax.eff_name = _56_1074.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _56_1074.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _56_1074.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| _56_1078 -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let _56_1080 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _149_695 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _149_694 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _149_693 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _149_692 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _149_695 _149_694 _149_693 _149_692)))))
end else begin
()
end
in (

let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _56_1085 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_56_1085) with
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

let us = (let _149_696 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_149_696)::[])
in (

let wp = (let _149_701 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ret_wp)
in (let _149_700 = (let _149_699 = (FStar_Syntax_Syntax.as_arg t)
in (let _149_698 = (let _149_697 = (FStar_Syntax_Syntax.as_arg xexp)
in (_149_697)::[])
in (_149_699)::_149_698))
in (FStar_Syntax_Syntax.mk_Tm_app _149_701 _149_700 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)))
in (

let cret = (let _149_702 = (mk_comp md t wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _149_702))
in (

let guard = if apply_guard then begin
(let _149_704 = (let _149_703 = (FStar_Syntax_Syntax.as_arg xexp)
in (_149_703)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _149_704 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end else begin
f
end
in (

let _56_1096 = (let _149_712 = (FStar_All.pipe_left (fun _149_709 -> Some (_149_709)) (FStar_TypeChecker_Errors.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _149_711 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _149_710 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _149_712 _149_711 e cret _149_710))))
in (match (_56_1096) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x = (

let _56_1097 = x
in {FStar_Syntax_Syntax.ppname = _56_1097.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_1097.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (

let c = (let _149_714 = (let _149_713 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _149_713))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) _149_714 ((Some (x)), (eq_ret))))
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let _56_1102 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _149_715 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _149_715))
end else begin
()
end
in c))))
end))))))))))
end)))))
end))
end))
in (

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _56_3 -> (match (_56_3) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _56_1108 -> begin
[]
end))))
in (

let lc = (

let _56_1110 = lc
in (let _149_717 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _149_717; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (

let g = (

let _56_1113 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _56_1113.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_1113.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_1113.FStar_TypeChecker_Env.implicits})
in ((e), (lc), (g)))))))
end)
end)))


let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _149_729 = (let _149_728 = (let _149_727 = (let _149_726 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _149_726))
in (_149_727)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _149_728 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _149_729))))
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
| ((req, _56_1141))::((ens, _56_1136))::_56_1133 -> begin
(let _149_735 = (let _149_732 = (norm req)
in Some (_149_732))
in (let _149_734 = (let _149_733 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _149_733))
in ((_149_735), (_149_734))))
end
| _56_1145 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(

let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| ((wp, _56_1151))::_56_1148 -> begin
(

let _56_1157 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (_56_1157) with
| (us_r, _56_1156) -> begin
(

let _56_1161 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (_56_1161) with
| (us_e, _56_1160) -> begin
(

let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (

let as_req = (let _149_737 = (let _149_736 = (FStar_Ident.set_lid_range FStar_Syntax_Const.as_requires r)
in (FStar_Syntax_Syntax.fvar _149_736 FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _149_737 us_r))
in (

let as_ens = (let _149_739 = (let _149_738 = (FStar_Ident.set_lid_range FStar_Syntax_Const.as_ensures r)
in (FStar_Syntax_Syntax.fvar _149_738 FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _149_739 us_e))
in (

let req = (let _149_742 = (let _149_741 = (let _149_740 = (FStar_Syntax_Syntax.as_arg wp)
in (_149_740)::[])
in (((ct.FStar_Syntax_Syntax.result_typ), (Some (FStar_Syntax_Syntax.imp_tag))))::_149_741)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _149_742 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let ens = (let _149_745 = (let _149_744 = (let _149_743 = (FStar_Syntax_Syntax.as_arg wp)
in (_149_743)::[])
in (((ct.FStar_Syntax_Syntax.result_typ), (Some (FStar_Syntax_Syntax.imp_tag))))::_149_744)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _149_745 None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _149_749 = (let _149_746 = (norm req)
in Some (_149_746))
in (let _149_748 = (let _149_747 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm _149_747))
in ((_149_749), (_149_748)))))))))
end))
end))
end
| _56_1168 -> begin
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

let _56_1179 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_56_1179) with
| (bs, c) -> begin
(

let rec aux = (fun subst _56_4 -> (match (_56_4) with
| ((x, Some (FStar_Syntax_Syntax.Implicit (dot))))::rest -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let _56_1195 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t)
in (match (_56_1195) with
| (v, _56_1193, g) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (v))))::subst
in (

let _56_1201 = (aux subst rest)
in (match (_56_1201) with
| (args, bs, subst, g') -> begin
(let _149_760 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((v), (Some (FStar_Syntax_Syntax.Implicit (dot)))))::args), (bs), (subst), (_149_760)))
end)))
end)))
end
| bs -> begin
(([]), (bs), (subst), (FStar_TypeChecker_Rel.trivial_guard))
end))
in (

let _56_1207 = (aux [] bs)
in (match (_56_1207) with
| (args, bs, subst, guard) -> begin
(match (((args), (bs))) with
| ([], _56_1210) -> begin
((e), (torig), (guard))
end
| (_56_1213, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
((e), (torig), (FStar_TypeChecker_Rel.trivial_guard))
end
| _56_1217 -> begin
(

let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _56_1220 -> begin
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
| _56_1225 -> begin
((e), (t), (FStar_TypeChecker_Rel.trivial_guard))
end)
end))


let string_of_univs = (fun univs -> (let _149_765 = (let _149_764 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _149_764 (FStar_List.map (fun u -> (let _149_763 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _149_763 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _149_765 (FStar_String.concat ", "))))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(

let s = (let _149_771 = (let _149_770 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _149_770))
in (FStar_All.pipe_right _149_771 FStar_Util.set_elements))
in (

let _56_1231 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _149_773 = (let _149_772 = (FStar_TypeChecker_Env.univ_vars env)
in (string_of_univs _149_772))
in (FStar_Util.print1 "univ_vars in env: %s\n" _149_773))
end else begin
()
end
in (

let r = (let _149_774 = (FStar_TypeChecker_Env.get_range env)
in Some (_149_774))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (

let _56_1236 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _149_779 = (let _149_776 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _149_776))
in (let _149_778 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _149_777 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _149_779 _149_778 _149_777))))
end else begin
()
end
in (

let _56_1238 = (FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))))
in u_name))))))
in u_names))))
end)


let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (

let univs = (FStar_Syntax_Free.univs t)
in (

let _56_1245 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _149_784 = (string_of_univs univs)
in (FStar_Util.print1 "univs to gen : %s\n" _149_784))
end else begin
()
end
in (

let gen = (gen_univs env univs)
in (

let _56_1248 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _149_785 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _149_785))
end else begin
()
end
in (

let ts = (FStar_Syntax_Subst.close_univ_vars gen t)
in ((gen), (ts)))))))))


let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> if (let _149_791 = (FStar_Util.for_all (fun _56_1256 -> (match (_56_1256) with
| (_56_1254, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _149_791)) then begin
None
end else begin
(

let norm = (fun c -> (

let _56_1259 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _149_794 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _149_794))
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

let _56_1262 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _149_795 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _149_795))
end else begin
()
end
in c))))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (let _149_798 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _149_798 FStar_Util.set_elements)))
in (

let _56_1279 = (let _149_800 = (FStar_All.pipe_right ecs (FStar_List.map (fun _56_1269 -> (match (_56_1269) with
| (e, c) -> begin
(

let t = (FStar_All.pipe_right (FStar_Syntax_Util.comp_result c) FStar_Syntax_Subst.compress)
in (

let c = (norm c)
in (

let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (

let t = ct.FStar_Syntax_Syntax.result_typ
in (

let univs = (FStar_Syntax_Free.univs t)
in (

let uvt = (FStar_Syntax_Free.uvars t)
in (

let uvs = (gen_uvars uvt)
in ((univs), (((uvs), (e), (c)))))))))))
end))))
in (FStar_All.pipe_right _149_800 FStar_List.unzip))
in (match (_56_1279) with
| (univs, uvars) -> begin
(

let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (

let gen_univs = (gen_univs env univs)
in (

let _56_1283 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end else begin
()
end
in (

let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _56_1288 -> (match (_56_1288) with
| (uvs, e, c) -> begin
(

let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _56_1291 -> (match (_56_1291) with
| (u, k) -> begin
(match ((FStar_Unionfind.find u)) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
((a), (Some (FStar_Syntax_Syntax.imp_tag)))
end
| FStar_Syntax_Syntax.Fixed (_56_1325) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _56_1328 -> begin
(

let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (

let _56_1332 = (FStar_Syntax_Util.arrow_formals k)
in (match (_56_1332) with
| (bs, kres) -> begin
(

let a = (let _149_806 = (let _149_805 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _149_804 -> Some (_149_804)) _149_805))
in (FStar_Syntax_Syntax.new_bv _149_806 kres))
in (

let t = (let _149_811 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _149_810 = (let _149_809 = (let _149_808 = (let _149_807 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _149_807))
in FStar_Util.Inl (_149_808))
in Some (_149_809))
in (FStar_Syntax_Util.abs bs _149_811 _149_810)))
in (

let _56_1335 = (FStar_Syntax_Util.set_uvar u t)
in ((a), (Some (FStar_Syntax_Syntax.imp_tag))))))
end)))
end)
end))))
in (

let _56_1367 = (match (((tvars), (gen_univs))) with
| ([], []) -> begin
((e), (c))
end
| ([], _56_1343) -> begin
(

let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoInline)::[]) env c)
in (

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoInline)::[]) env e)
in ((e), (c))))
end
| _56_1348 -> begin
(

let _56_1351 = ((e), (c))
in (match (_56_1351) with
| (e0, c0) -> begin
(

let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoInline)::(FStar_TypeChecker_Normalize.CompressUvars)::[]) env c)
in (

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoInline)::(FStar_TypeChecker_Normalize.CompressUvars)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Iota))::[]) env e)
in (

let t = (match ((let _149_812 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _149_812.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(

let _56_1360 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (_56_1360) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| _56_1362 -> begin
(FStar_Syntax_Util.arrow tvars c)
end)
in (

let e' = (FStar_Syntax_Util.abs tvars e (Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp c)))))
in (let _149_813 = (FStar_Syntax_Syntax.mk_Total t)
in ((e'), (_149_813)))))))
end))
end)
in (match (_56_1367) with
| (e, c) -> begin
((gen_univs), (e), (c))
end)))
end))))
in Some (ecs)))))
end)))))
end)


let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> (

let _56_1377 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _149_820 = (let _149_819 = (FStar_List.map (fun _56_1376 -> (match (_56_1376) with
| (lb, _56_1373, _56_1375) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _149_819 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _149_820))
end else begin
()
end
in (match ((let _149_822 = (FStar_All.pipe_right lecs (FStar_List.map (fun _56_1383 -> (match (_56_1383) with
| (_56_1380, e, c) -> begin
((e), (c))
end))))
in (gen env _149_822))) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun _56_1388 -> (match (_56_1388) with
| (l, t, c) -> begin
((l), ([]), (t), (c))
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _56_1396 _56_1400 -> (match (((_56_1396), (_56_1400))) with
| ((l, _56_1393, _56_1395), (us, e, c)) -> begin
(

let _56_1401 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _149_829 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _149_828 = (FStar_Syntax_Print.lbname_to_string l)
in (let _149_827 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (let _149_826 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print4 "(%s) Generalized %s at type %s\n%s\n" _149_829 _149_828 _149_827 _149_826)))))
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
(let _149_845 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _149_844 -> Some (_149_844)) _149_845))
end)
end)
in (

let is_var = (fun e -> (match ((let _149_848 = (FStar_Syntax_Subst.compress e)
in _149_848.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (_56_1418) -> begin
true
end
| _56_1421 -> begin
false
end))
in (

let decorate = (fun e t -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((

let _56_1428 = x
in {FStar_Syntax_Syntax.ppname = _56_1428.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_1428.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| _56_1431 -> begin
(

let _56_1432 = e
in (let _149_853 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _56_1432.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _149_853; FStar_Syntax_Syntax.pos = _56_1432.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _56_1432.FStar_Syntax_Syntax.vars}))
end)))
in (

let env = (

let _56_1434 = env
in (let _149_854 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _56_1434.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _56_1434.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _56_1434.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _56_1434.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _56_1434.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _56_1434.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _56_1434.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _56_1434.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _56_1434.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _56_1434.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _56_1434.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _56_1434.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _56_1434.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _56_1434.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _56_1434.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _149_854; FStar_TypeChecker_Env.is_iface = _56_1434.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _56_1434.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _56_1434.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.type_of = _56_1434.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _56_1434.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _56_1434.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _56_1434.FStar_TypeChecker_Env.qname_and_index}))
in (match ((check env t1 t2)) with
| None -> begin
(let _149_858 = (let _149_857 = (let _149_856 = (FStar_TypeChecker_Errors.expected_expression_of_type env t2 e t1)
in (let _149_855 = (FStar_TypeChecker_Env.get_range env)
in ((_149_856), (_149_855))))
in FStar_Syntax_Syntax.Error (_149_857))
in (Prims.raise _149_858))
end
| Some (g) -> begin
(

let _56_1440 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_859 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _149_859))
end else begin
()
end
in (let _149_860 = (decorate e t2)
in ((_149_860), (g))))
end)))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (

let discharge = (fun g -> (

let _56_1447 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _149_870 = (discharge g)
in (let _149_869 = (lc.FStar_Syntax_Syntax.comp ())
in ((_149_870), (_149_869))))
end else begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let steps = (FStar_TypeChecker_Normalize.Beta)::[]
in (

let c = (let _149_873 = (let _149_872 = (let _149_871 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (FStar_All.pipe_right _149_871 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right _149_872 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (FStar_All.pipe_right _149_873 FStar_Syntax_Util.comp_to_comp_typ))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let _56_1456 = (destruct_comp c)
in (match (_56_1456) with
| (t, wp) -> begin
(

let vc = (let _149_881 = (let _149_875 = (let _149_874 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_149_874)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _149_875 env md md.FStar_Syntax_Syntax.trivial))
in (let _149_880 = (let _149_878 = (FStar_Syntax_Syntax.as_arg t)
in (let _149_877 = (let _149_876 = (FStar_Syntax_Syntax.as_arg wp)
in (_149_876)::[])
in (_149_878)::_149_877))
in (let _149_879 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk_Tm_app _149_881 _149_880 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _149_879))))
in (

let _56_1458 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _149_882 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _149_882))
end else begin
()
end
in (

let g = (let _149_883 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _149_883))
in (let _149_885 = (discharge g)
in (let _149_884 = (FStar_Syntax_Syntax.mk_Comp c)
in ((_149_885), (_149_884)))))))
end))))))
end)))


let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (

let short_bin_op = (fun f _56_5 -> (match (_56_5) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((fst, _56_1469))::[] -> begin
(f fst)
end
| _56_1473 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (

let op_and_e = (fun e -> (let _149_906 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _149_906 (fun _149_905 -> FStar_TypeChecker_Common.NonTrivial (_149_905)))))
in (

let op_or_e = (fun e -> (let _149_911 = (let _149_909 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _149_909))
in (FStar_All.pipe_right _149_911 (fun _149_910 -> FStar_TypeChecker_Common.NonTrivial (_149_910)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _149_914 -> FStar_TypeChecker_Common.NonTrivial (_149_914))))
in (

let op_or_t = (fun t -> (let _149_918 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _149_918 (fun _149_917 -> FStar_TypeChecker_Common.NonTrivial (_149_917)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _149_921 -> FStar_TypeChecker_Common.NonTrivial (_149_921))))
in (

let short_op_ite = (fun _56_6 -> (match (_56_6) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((guard, _56_1488))::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| (_then)::((guard, _56_1493))::[] -> begin
(let _149_925 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _149_925 (fun _149_924 -> FStar_TypeChecker_Common.NonTrivial (_149_924))))
end
| _56_1498 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (

let table = (((FStar_Syntax_Const.op_And), ((short_bin_op op_and_e))))::(((FStar_Syntax_Const.op_Or), ((short_bin_op op_or_e))))::(((FStar_Syntax_Const.and_lid), ((short_bin_op op_and_t))))::(((FStar_Syntax_Const.or_lid), ((short_bin_op op_or_t))))::(((FStar_Syntax_Const.imp_lid), ((short_bin_op op_imp_t))))::(((FStar_Syntax_Const.ite_lid), (short_op_ite)))::[]
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((FStar_Util.find_map table (fun _56_1506 -> (match (_56_1506) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _149_958 = (mk seen_args)
in Some (_149_958))
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
| _56_1511 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (match ((let _149_961 = (FStar_Syntax_Util.un_uinst l)
in _149_961.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| _56_1516 -> begin
false
end))


let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (

let pos = (fun bs -> (match (bs) with
| ((hd, _56_1525))::_56_1522 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| _56_1529 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| ((_56_1533, Some (FStar_Syntax_Syntax.Implicit (_56_1535))))::_56_1531 -> begin
bs
end
| _56_1541 -> begin
(match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
bs
end
| Some (t) -> begin
(match ((let _149_968 = (FStar_Syntax_Subst.compress t)
in _149_968.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', _56_1547) -> begin
(match ((FStar_Util.prefix_until (fun _56_7 -> (match (_56_7) with
| (_56_1552, Some (FStar_Syntax_Syntax.Implicit (_56_1554))) -> begin
false
end
| _56_1559 -> begin
true
end)) bs')) with
| None -> begin
bs
end
| Some ([], _56_1563, _56_1565) -> begin
bs
end
| Some (imps, _56_1570, _56_1572) -> begin
if (FStar_All.pipe_right imps (FStar_Util.for_all (fun _56_1578 -> (match (_56_1578) with
| (x, _56_1577) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end)))) then begin
(

let r = (pos bs)
in (

let imps = (FStar_All.pipe_right imps (FStar_List.map (fun _56_1582 -> (match (_56_1582) with
| (x, i) -> begin
(let _149_972 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in ((_149_972), (i)))
end))))
in (FStar_List.append imps bs)))
end else begin
bs
end
end)
end
| _56_1585 -> begin
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
(let _149_981 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m2))))))) _149_981 e.FStar_Syntax_Syntax.pos))
end)))


let maybe_monadic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e c t -> (

let m = (FStar_TypeChecker_Env.norm_eff_name env c)
in if (((is_pure_or_ghost_effect env m) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid)) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid)) then begin
e
end else begin
(let _149_990 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))) _149_990 e.FStar_Syntax_Syntax.pos))
end))


let reify_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term = (fun env c u_c -> (

let no_reify = (fun l -> (let _149_1002 = (let _149_1001 = (let _149_1000 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _149_999 = (FStar_TypeChecker_Env.get_range env)
in ((_149_1000), (_149_999))))
in FStar_Syntax_Syntax.Error (_149_1001))
in (Prims.raise _149_1002)))
in (match ((let _149_1003 = (FStar_TypeChecker_Env.norm_eff_name env c.FStar_Syntax_Syntax.eff_name)
in (FStar_TypeChecker_Env.effect_decl_opt env _149_1003))) with
| None -> begin
(no_reify c.FStar_Syntax_Syntax.eff_name)
end
| Some (ed) -> begin
if (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)))) then begin
(no_reify c.FStar_Syntax_Syntax.eff_name)
end else begin
(

let c = (let _149_1004 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_TypeChecker_Normalize.unfold_effect_abbrev env _149_1004))
in (

let _56_1608 = (let _149_1005 = (FStar_List.hd c.FStar_Syntax_Syntax.effect_args)
in ((c.FStar_Syntax_Syntax.result_typ), (_149_1005)))
in (match (_56_1608) with
| (res_typ, wp) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_c)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (let _149_1010 = (let _149_1008 = (let _149_1007 = (let _149_1006 = (FStar_Syntax_Syntax.as_arg res_typ)
in (_149_1006)::(wp)::[])
in ((repr), (_149_1007)))
in FStar_Syntax_Syntax.Tm_app (_149_1008))
in (let _149_1009 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _149_1010 None _149_1009))))
end)))
end
end)))


let d : Prims.string  ->  Prims.unit = (fun s -> (FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s))


let mk_toplevel_definition : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.term) = (fun env lident def -> (

let _56_1616 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("ED"))) then begin
(

let _56_1614 = (d (FStar_Ident.text_of_lid lident))
in (let _149_1019 = (FStar_Syntax_Print.term_to_string def)
in (FStar_Util.print2 "Registering top-level definition: %s\n%s\n" (FStar_Ident.text_of_lid lident) _149_1019)))
end else begin
()
end
in (

let fv = (let _149_1020 = (FStar_Syntax_Util.incr_delta_qualifier def)
in (FStar_Syntax_Syntax.lid_as_fv lident _149_1020 None))
in (

let lbname = FStar_Util.Inr (fv)
in (

let lb = ((false), (({FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = def})::[]))
in (

let sig_ctx = FStar_Syntax_Syntax.Sig_let (((lb), (FStar_Range.dummyRange), ((lident)::[]), ((FStar_Syntax_Syntax.Inline)::[])))
in (let _149_1021 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) None FStar_Range.dummyRange)
in ((sig_ctx), (_149_1021)))))))))




