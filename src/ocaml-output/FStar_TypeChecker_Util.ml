
open Prims

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv Prims.option * FStar_Syntax_Syntax.lcomp)


let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _148_6 = (FStar_TypeChecker_Env.get_range env)
in (let _148_5 = (FStar_TypeChecker_Errors.failed_to_prove_specification errs)
in (FStar_TypeChecker_Errors.report _148_6 _148_5))))


let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _148_9 = (FStar_Syntax_Subst.compress t)
in _148_9.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_56_12) -> begin
true
end
| _56_15 -> begin
false
end))


let t_binders : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env -> (let _148_13 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right _148_13 (FStar_List.filter (fun _56_20 -> (match (_56_20) with
| (x, _56_19) -> begin
(is_type x.FStar_Syntax_Syntax.sort)
end))))))


let new_uvar_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun env k -> (

let bs = if ((FStar_Options.full_context_dependency ()) || (let _148_18 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _148_18))) then begin
(FStar_TypeChecker_Env.all_binders env)
end else begin
(t_binders env)
end
in (let _148_19 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Rel.new_uvar _148_19 bs k))))


let new_uvar : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env k -> (let _148_24 = (new_uvar_aux env k)
in (Prims.fst _148_24)))


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
in (let _148_37 = (let _148_36 = (let _148_35 = (as_uvar u)
in ((reason), (env), (_148_35), (t), (k), (r)))
in (_148_36)::[])
in {FStar_TypeChecker_Env.guard_f = _56_59.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _56_59.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_59.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _148_37}))
in (let _148_40 = (let _148_39 = (let _148_38 = (as_uvar u)
in ((_148_38), (r)))
in (_148_39)::[])
in ((t), (_148_40), (g))))
end))
end))


let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun r t -> (

let uvs = (FStar_Syntax_Free.uvars t)
in if (not ((FStar_Util.set_is_empty uvs))) then begin
(

let us = (let _148_47 = (let _148_46 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun _56_68 -> (match (_56_68) with
| (x, _56_67) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) _148_46))
in (FStar_All.pipe_right _148_47 (FStar_String.concat ", ")))
in (

let _56_70 = (FStar_Options.push ())
in (

let _56_72 = (FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool (false)))
in (

let _56_74 = (FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)))
in (

let _56_76 = (let _148_49 = (let _148_48 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us _148_48))
in (FStar_TypeChecker_Errors.report r _148_49))
in (FStar_Options.pop ()))))))
end else begin
()
end))


let force_sort' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' = (fun s -> (match ((FStar_ST.read s.FStar_Syntax_Syntax.tk)) with
| None -> begin
(let _148_54 = (let _148_53 = (FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos)
in (let _148_52 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s" _148_53 _148_52)))
in (FStar_All.failwith _148_54))
end
| Some (tk) -> begin
tk
end))


let force_sort = (fun s -> (let _148_56 = (force_sort' s)
in (FStar_Syntax_Syntax.mk _148_56 None s.FStar_Syntax_Syntax.pos)))


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

let mk_binder = (fun scope a -> (match ((let _148_65 = (FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort)
in _148_65.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _56_105 = (FStar_Syntax_Util.type_u ())
in (match (_56_105) with
| (k, _56_104) -> begin
(

let t = (let _148_66 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right _148_66 Prims.fst))
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
(let _148_74 = (FStar_Range.string_of_range r)
in (let _148_73 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _148_74 _148_73)))
end else begin
()
end
in ((FStar_Util.Inl (t)), ((check_res || check))))))
end))
end))
end
| _56_161 -> begin
(let _148_77 = (let _148_76 = (let _148_75 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _148_75 Prims.fst))
in FStar_Util.Inl (_148_76))
in ((_148_77), (false)))
end)))
in (

let _56_164 = (let _148_78 = (t_binders env)
in (aux _148_78 e))
in (match (_56_164) with
| (t, b) -> begin
(

let t = (match (t) with
| FStar_Util.Inr (c) -> begin
(let _148_82 = (let _148_81 = (let _148_80 = (let _148_79 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" _148_79))
in ((_148_80), (rng)))
in FStar_Syntax_Syntax.Error (_148_81))
in (Prims.raise _148_82))
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

let _56_200 = (let _148_95 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _148_95 t))
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
in (let _148_96 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _56_210.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_210.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_96}))
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
in (let _148_97 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _56_221.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_221.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_97}))
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

let e = (let _148_104 = (let _148_103 = (let _148_102 = (let _148_101 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (let _148_100 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app _148_101 _148_100 None p.FStar_Syntax_Syntax.p)))
in ((_148_102), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))
in FStar_Syntax_Syntax.Tm_meta (_148_103))
in (FStar_Syntax_Syntax.mk _148_104 None p.FStar_Syntax_Syntax.p))
in (let _148_107 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _148_106 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _148_105 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in ((_148_107), (_148_106), (_148_105), (env), (e), ((

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
(let _148_119 = (elaborate_pat env p)
in ((_148_119), (imp)))
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

let a = (let _148_126 = (let _148_125 = (FStar_Syntax_Syntax.range_of_bv t)
in Some (_148_125))
in (FStar_Syntax_Syntax.new_bv _148_126 FStar_Syntax_Syntax.tun))
in (

let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (let _148_127 = (maybe_dot inaccessible a r)
in ((_148_127), (true)))))
end
| _56_313 -> begin
(let _148_131 = (let _148_130 = (let _148_129 = (let _148_128 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _148_128))
in ((_148_129), ((FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))))
in FStar_Syntax_Syntax.Error (_148_130))
in (Prims.raise _148_131))
end)
end))))
end
| ((f)::formals', ((p, p_imp))::pats') -> begin
(match (f) with
| (_56_324, Some (FStar_Syntax_Syntax.Implicit (_56_326))) when p_imp -> begin
(let _148_132 = (aux formals' pats')
in (((p), (true)))::_148_132)
end
| (_56_331, Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(

let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let p = (maybe_dot inaccessible a (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
in (let _148_133 = (aux formals' pats)
in (((p), (true)))::_148_133)))
end
| (_56_339, imp) -> begin
(let _148_136 = (let _148_134 = (FStar_Syntax_Syntax.is_implicit imp)
in ((p), (_148_134)))
in (let _148_135 = (aux formals' pats')
in (_148_136)::_148_135))
end)
end))
in (

let _56_342 = p
in (let _148_139 = (let _148_138 = (let _148_137 = (aux f pats)
in ((fv), (_148_137)))
in FStar_Syntax_Syntax.Pat_cons (_148_138))
in {FStar_Syntax_Syntax.v = _148_139; FStar_Syntax_Syntax.ty = _56_342.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_342.FStar_Syntax_Syntax.p})))
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
(let _148_148 = (let _148_147 = (let _148_146 = (FStar_TypeChecker_Errors.nonlinear_pattern_variable x)
in ((_148_146), (p.FStar_Syntax_Syntax.p)))
in FStar_Syntax_Syntax.Error (_148_147))
in (Prims.raise _148_148))
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
(let _148_158 = (let _148_157 = (let _148_156 = (FStar_TypeChecker_Errors.disjunctive_pattern_vars a a')
in (let _148_155 = (FStar_TypeChecker_Env.get_range env)
in ((_148_156), (_148_155))))
in FStar_Syntax_Syntax.Error (_148_157))
in (Prims.raise _148_158))
end else begin
(let _148_160 = (let _148_159 = (FStar_Syntax_Syntax.as_arg arg)
in (_148_159)::args)
in (((FStar_List.append w' w)), (_148_160), ((p)::pats)))
end
end))
end)) pats (([]), ([]), ([])))
in (match (_56_392) with
| (w, args, pats) -> begin
(let _148_162 = (let _148_161 = (FStar_Syntax_Syntax.as_arg te)
in (_148_161)::args)
in (((FStar_List.append b w)), (_148_162), ((

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
(let _148_164 = (let _148_163 = (FStar_Syntax_Syntax.as_arg arg)
in (_148_163)::[])
in ((b), (_148_164), (p)))
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
(let _148_179 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v _148_179))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(

let _56_441 = if (not ((FStar_Syntax_Syntax.bv_eq x y))) then begin
(let _148_182 = (let _148_181 = (FStar_Syntax_Print.bv_to_string x)
in (let _148_180 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _148_181 _148_180)))
in (FStar_All.failwith _148_182))
end else begin
()
end
in (

let _56_443 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _148_184 = (FStar_Syntax_Print.bv_to_string x)
in (let _148_183 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _148_184 _148_183)))
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
(let _148_187 = (let _148_186 = (FStar_Syntax_Print.bv_to_string x)
in (let _148_185 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _148_186 _148_185)))
in (FStar_All.failwith _148_187))
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
(let _148_188 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _148_188))
end else begin
()
end
in (let _148_189 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv'), ([])))) _148_189)))
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
(

let _56_522 = if (let _148_190 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right _148_190 Prims.op_Negation)) then begin
(let _148_191 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _148_191))
end else begin
()
end
in (

let fv = fv'
in (

let rec match_args = (fun matched_pats args argpats -> (match (((args), (argpats))) with
| ([], []) -> begin
(let _148_198 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev matched_pats))))) _148_198))
end
| ((arg)::args, ((argpat, _56_538))::argpats) -> begin
(match (((arg), (argpat.FStar_Syntax_Syntax.v))) with
| ((e, Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (_56_548)) -> begin
(

let x = (let _148_199 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _148_199))
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term (((x), (e)))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args ((((q), (true)))::matched_pats) args argpats)))
end
| ((e, imp), _56_557) -> begin
(

let pat = (let _148_201 = (aux argpat e)
in (let _148_200 = (FStar_Syntax_Syntax.is_implicit imp)
in ((_148_201), (_148_200))))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _56_561 -> begin
(let _148_204 = (let _148_203 = (FStar_Syntax_Print.pat_to_string p)
in (let _148_202 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _148_203 _148_202)))
in (FStar_All.failwith _148_204))
end))
in (match_args [] args argpats))))
end
| _56_563 -> begin
(let _148_209 = (let _148_208 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (let _148_207 = (FStar_Syntax_Print.pat_to_string qq)
in (let _148_206 = (let _148_205 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right _148_205 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _148_208 _148_207 _148_206))))
in (FStar_All.failwith _148_209))
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
(let _148_217 = (let _148_216 = (FStar_Syntax_Syntax.as_implicit i)
in ((te), (_148_216)))
in ((vars), (_148_217)))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_56_589) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _148_218 = (mk (FStar_Syntax_Syntax.Tm_constant (c)))
in (([]), (_148_218)))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(let _148_219 = (mk (FStar_Syntax_Syntax.Tm_name (x)))
in (((x)::[]), (_148_219)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _56_602 = (let _148_220 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _148_220 FStar_List.unzip))
in (match (_56_602) with
| (vars, args) -> begin
(

let vars = (FStar_List.flatten vars)
in (let _148_224 = (let _148_223 = (let _148_222 = (let _148_221 = (FStar_Syntax_Syntax.fv_to_tm fv)
in ((_148_221), (args)))
in FStar_Syntax_Syntax.Tm_app (_148_222))
in (mk _148_223))
in ((vars), (_148_224))))
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
(let _148_230 = (let _148_229 = (let _148_228 = (FStar_List.map (fun _56_619 -> (match (_56_619) with
| (x, _56_618) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right _148_228 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str _148_229))
in (FStar_All.failwith _148_230))
end)
in ((c.FStar_Syntax_Syntax.result_typ), (wp))))


let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (

let _56_627 = (destruct_comp c)
in (match (_56_627) with
| (_56_625, wp) -> begin
(let _148_249 = (let _148_248 = (let _148_247 = (lift c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _148_247))
in (_148_248)::[])
in {FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _148_249; FStar_Syntax_Syntax.flags = []})
end)))


let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let _56_636 = (let _148_257 = (FStar_TypeChecker_Env.norm_eff_name env l1)
in (let _148_256 = (FStar_TypeChecker_Env.norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _148_257 _148_256)))
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
(let _148_271 = (destruct_comp m1)
in (let _148_270 = (destruct_comp m2)
in ((((md), (a), (kwp))), (_148_271), (_148_270))))
end)))))
end)))))


let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid))))


let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md result wp flags -> (let _148_290 = (let _148_289 = (let _148_288 = (FStar_Syntax_Syntax.as_arg wp)
in (_148_288)::[])
in {FStar_Syntax_Syntax.effect_name = md.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = _148_289; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp _148_290)))


let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (

let _56_667 = lc
in (let _148_297 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _56_667.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _148_297; FStar_Syntax_Syntax.cflags = _56_667.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _56_669 -> (match (()) with
| () -> begin
(let _148_296 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _148_296))
end))})))


let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _148_300 = (FStar_Syntax_Subst.compress t)
in _148_300.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_56_672) -> begin
true
end
| _56_675 -> begin
false
end))


let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v -> (

let c = if (let _148_307 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation _148_307)) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(

let m = (let _148_308 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must _148_308))
in (

let _56_682 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_56_682) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t))))::[]) kwp)
in (

let wp = (let _148_316 = (let _148_315 = (let _148_310 = (let _148_309 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_148_309)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _148_310 env m m.FStar_Syntax_Syntax.ret_wp))
in (let _148_314 = (let _148_313 = (FStar_Syntax_Syntax.as_arg t)
in (let _148_312 = (let _148_311 = (FStar_Syntax_Syntax.as_arg v)
in (_148_311)::[])
in (_148_313)::_148_312))
in (FStar_Syntax_Syntax.mk_Tm_app _148_315 _148_314 (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _148_316))
in (mk_comp m t wp ((FStar_Syntax_Syntax.RETURN)::[]))))
end)))
end
in (

let _56_686 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return"))) then begin
(let _148_319 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _148_318 = (FStar_Syntax_Print.term_to_string v)
in (let _148_317 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _148_319 _148_318 _148_317))))
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
in (let _148_332 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (let _148_331 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _148_330 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" _148_332 _148_331 bstr _148_330)))))
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
(let _148_339 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _148_338 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _148_337 = (FStar_Syntax_Print.comp_to_string c1)
in (let _148_336 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (let _148_335 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" _148_339 _148_338 _148_337 _148_336 _148_335))))))
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
(let _148_347 = (let _148_346 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) c2)
in ((_148_346), (reason)))
in Some (_148_347))
end
| _56_731 -> begin
(aux ())
end))
in if ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2)) then begin
(subst_c2 "both total")
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2)) then begin
(let _148_349 = (let _148_348 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in ((_148_348), ("both gtot")))
in Some (_148_349))
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
(let _148_350 = (FStar_Syntax_Syntax.null_binder t1)
in (_148_350)::[])
end
| Some (x) -> begin
(let _148_351 = (FStar_Syntax_Syntax.mk_binder x)
in (_148_351)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid)))))
in (

let r1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1))) None r1)
in (

let wp_args = (let _148_363 = (FStar_Syntax_Syntax.as_arg r1)
in (let _148_362 = (let _148_361 = (FStar_Syntax_Syntax.as_arg t1)
in (let _148_360 = (let _148_359 = (FStar_Syntax_Syntax.as_arg t2)
in (let _148_358 = (let _148_357 = (FStar_Syntax_Syntax.as_arg wp1)
in (let _148_356 = (let _148_355 = (let _148_354 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg _148_354))
in (_148_355)::[])
in (_148_357)::_148_356))
in (_148_359)::_148_358))
in (_148_361)::_148_360))
in (_148_363)::_148_362))
in (

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((a), (t2))))::[]) kwp)
in (

let us = (let _148_366 = (env.FStar_TypeChecker_Env.universe_of env t1)
in (let _148_365 = (let _148_364 = (env.FStar_TypeChecker_Env.universe_of env t2)
in (_148_364)::[])
in (_148_366)::_148_365))
in (

let wp = (let _148_367 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _148_367 wp_args None t2.FStar_Syntax_Syntax.pos))
in (

let c = (mk_comp md t2 wp [])
in c))))))))
end))
end)))))
end))
in (let _148_368 = (join_lcomp env lc1 lc2)
in {FStar_Syntax_Syntax.eff_name = _148_368; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it})))))
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

let wp = (let _148_380 = (let _148_379 = (FStar_Syntax_Syntax.as_arg t)
in (let _148_378 = (let _148_377 = (FStar_Syntax_Syntax.as_arg f)
in (_148_377)::[])
in (_148_379)::_148_378))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wp _148_380 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (mk_comp md_pure FStar_TypeChecker_Common.t_unit wp [])))
end))))


let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((f), (FStar_Syntax_Syntax.Meta_labeled (((reason), (r), (false))))))) None f.FStar_Syntax_Syntax.pos))


let label_opt : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _148_404 = (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)
in (FStar_All.pipe_left Prims.op_Negation _148_404)) then begin
f
end else begin
(let _148_405 = (reason ())
in (label _148_405 r f))
end
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let _56_793 = g
in (let _148_413 = (let _148_412 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_148_412))
in {FStar_TypeChecker_Env.guard_f = _148_413; FStar_TypeChecker_Env.deferred = _56_793.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_793.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_793.FStar_TypeChecker_Env.implicits}))
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

let us = (let _148_426 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_148_426)::[])
in (

let wp = (let _148_433 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _148_432 = (let _148_431 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_430 = (let _148_429 = (FStar_Syntax_Syntax.as_arg f)
in (let _148_428 = (let _148_427 = (FStar_Syntax_Syntax.as_arg wp)
in (_148_427)::[])
in (_148_429)::_148_428))
in (_148_431)::_148_430))
in (FStar_Syntax_Syntax.mk_Tm_app _148_433 _148_432 None wp.FStar_Syntax_Syntax.pos)))
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
(let _148_453 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _148_452 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _148_453 _148_452)))
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

let xret = (let _148_458 = (let _148_457 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _148_457))
in (FStar_Syntax_Util.comp_set_flags _148_458 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (

let lc = (bind e.FStar_Syntax_Syntax.pos env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) ((Some (x)), ((FStar_Syntax_Util.lcomp_of_comp xret))))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (

let _56_847 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _148_460 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _148_459 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _148_460 _148_459)))
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

let us = (let _148_461 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_148_461)::[])
in (

let wp = (let _148_470 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assert_p)
in (let _148_469 = (let _148_468 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_467 = (let _148_466 = (let _148_463 = (let _148_462 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason _148_462 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _148_463))
in (let _148_465 = (let _148_464 = (FStar_Syntax_Syntax.as_arg wp)
in (_148_464)::[])
in (_148_466)::_148_465))
in (_148_468)::_148_467))
in (FStar_Syntax_Syntax.mk_Tm_app _148_470 _148_469 None wp.FStar_Syntax_Syntax.pos)))
in (

let _56_856 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _148_471 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _148_471))
end else begin
()
end
in (

let c2 = (mk_comp md res_t wp flags)
in c2)))))
end)))))
end)))
end))
in (let _148_475 = (

let _56_859 = lc
in (let _148_474 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _148_473 = if ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _148_472 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _148_472))) then begin
flags
end else begin
[]
end
in {FStar_Syntax_Syntax.eff_name = _148_474; FStar_Syntax_Syntax.res_typ = _56_859.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _148_473; FStar_Syntax_Syntax.comp = strengthen})))
in ((_148_475), ((

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

let _56_871 = (let _148_483 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _148_482 = (FStar_Syntax_Syntax.bv_to_name y)
in ((_148_483), (_148_482))))
in (match (_56_871) with
| (xexp, yexp) -> begin
(

let us = (let _148_484 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_148_484)::[])
in (

let yret = (let _148_489 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret_wp)
in (let _148_488 = (let _148_487 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_486 = (let _148_485 = (FStar_Syntax_Syntax.as_arg yexp)
in (_148_485)::[])
in (_148_487)::_148_486))
in (FStar_Syntax_Syntax.mk_Tm_app _148_489 _148_488 None res_t.FStar_Syntax_Syntax.pos)))
in (

let x_eq_y_yret = (let _148_497 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _148_496 = (let _148_495 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_494 = (let _148_493 = (let _148_490 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _148_490))
in (let _148_492 = (let _148_491 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_148_491)::[])
in (_148_493)::_148_492))
in (_148_495)::_148_494))
in (FStar_Syntax_Syntax.mk_Tm_app _148_497 _148_496 None res_t.FStar_Syntax_Syntax.pos)))
in (

let forall_y_x_eq_y_yret = (let _148_507 = (FStar_TypeChecker_Env.inst_effect_fun_with (FStar_List.append us us) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _148_506 = (let _148_505 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_504 = (let _148_503 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_502 = (let _148_501 = (let _148_500 = (let _148_499 = (let _148_498 = (FStar_Syntax_Syntax.mk_binder y)
in (_148_498)::[])
in (FStar_Syntax_Util.abs _148_499 x_eq_y_yret (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid)))))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _148_500))
in (_148_501)::[])
in (_148_503)::_148_502))
in (_148_505)::_148_504))
in (FStar_Syntax_Syntax.mk_Tm_app _148_507 _148_506 None res_t.FStar_Syntax_Syntax.pos)))
in (

let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (

let lc = (let _148_508 = (FStar_TypeChecker_Env.get_range env)
in (bind _148_508 env None (FStar_Syntax_Util.lcomp_of_comp comp) ((Some (x)), ((FStar_Syntax_Util.lcomp_of_comp lc2)))))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))


let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (

let comp = (fun _56_883 -> (match (()) with
| () -> begin
(

let _56_897 = (let _148_520 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _148_519 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _148_520 _148_519)))
in (match (_56_897) with
| ((md, _56_886, _56_888), (res_t, wp_then), (_56_894, wp_else)) -> begin
(

let us = (let _148_521 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_148_521)::[])
in (

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _148_541 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _148_540 = (let _148_538 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_537 = (let _148_536 = (FStar_Syntax_Syntax.as_arg g)
in (let _148_535 = (let _148_534 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _148_533 = (let _148_532 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_148_532)::[])
in (_148_534)::_148_533))
in (_148_536)::_148_535))
in (_148_538)::_148_537))
in (let _148_539 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _148_541 _148_540 None _148_539)))))
in (

let wp = (ifthenelse md res_t guard wp_then wp_else)
in if ((FStar_Options.split_cases ()) > 0) then begin
(

let comp = (mk_comp md res_t wp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(

let wp = (let _148_546 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _148_545 = (let _148_544 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_543 = (let _148_542 = (FStar_Syntax_Syntax.as_arg wp)
in (_148_542)::[])
in (_148_544)::_148_543))
in (FStar_Syntax_Syntax.mk_Tm_app _148_546 _148_545 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp []))
end)))
end))
end))
in (let _148_547 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _148_547; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp})))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (let _148_553 = (let _148_552 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid _148_552))
in (FStar_Syntax_Syntax.fvar _148_553 FStar_Syntax_Syntax.Delta_constant None)))


let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (FStar_List.fold_left (fun eff _56_917 -> (match (_56_917) with
| (_56_915, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (

let bind_cases = (fun _56_920 -> (match (()) with
| () -> begin
(

let us = (let _148_564 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_148_564)::[])
in (

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _148_584 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _148_583 = (let _148_581 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_580 = (let _148_579 = (FStar_Syntax_Syntax.as_arg g)
in (let _148_578 = (let _148_577 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _148_576 = (let _148_575 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_148_575)::[])
in (_148_577)::_148_576))
in (_148_579)::_148_578))
in (_148_581)::_148_580))
in (let _148_582 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _148_584 _148_583 None _148_582)))))
in (

let default_case = (

let post_k = (let _148_587 = (let _148_585 = (FStar_Syntax_Syntax.null_binder res_t)
in (_148_585)::[])
in (let _148_586 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _148_587 _148_586)))
in (

let kwp = (let _148_590 = (let _148_588 = (FStar_Syntax_Syntax.null_binder post_k)
in (_148_588)::[])
in (let _148_589 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _148_590 _148_589)))
in (

let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (

let wp = (let _148_596 = (let _148_591 = (FStar_Syntax_Syntax.mk_binder post)
in (_148_591)::[])
in (let _148_595 = (let _148_594 = (let _148_592 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Errors.exhaustiveness_check _148_592))
in (let _148_593 = (fvar_const env FStar_Syntax_Const.false_lid)
in (FStar_All.pipe_left _148_594 _148_593)))
in (FStar_Syntax_Util.abs _148_596 _148_595 (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md res_t wp []))))))
in (

let comp = (FStar_List.fold_right (fun _56_936 celse -> (match (_56_936) with
| (g, cthen) -> begin
(

let _56_952 = (let _148_599 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _148_599 celse))
in (match (_56_952) with
| ((md, _56_940, _56_942), (_56_945, wp_then), (_56_949, wp_else)) -> begin
(let _148_600 = (ifthenelse md res_t g wp_then wp_else)
in (mk_comp md res_t _148_600 []))
end))
end)) lcases default_case)
in if ((FStar_Options.split_cases ()) > 0) then begin
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

let wp = (let _148_605 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _148_604 = (let _148_603 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_602 = (let _148_601 = (FStar_Syntax_Syntax.as_arg wp)
in (_148_601)::[])
in (_148_603)::_148_602))
in (FStar_Syntax_Syntax.mk_Tm_app _148_605 _148_604 None wp.FStar_Syntax_Syntax.pos)))
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

let bs = (let _148_626 = (FStar_Syntax_Syntax.mk_binder x)
in (_148_626)::[])
in (

let us = (let _148_628 = (let _148_627 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (_148_627)::[])
in (u_res)::_148_628)
in (

let wp = (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid))))
in (let _148_635 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (let _148_634 = (let _148_633 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _148_632 = (let _148_631 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _148_630 = (let _148_629 = (FStar_Syntax_Syntax.as_arg wp)
in (_148_629)::[])
in (_148_631)::_148_630))
in (_148_633)::_148_632))
in (FStar_Syntax_Syntax.mk_Tm_app _148_635 _148_634 None wp0.FStar_Syntax_Syntax.pos))))))) bvs wp0))
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
(let _148_646 = (let _148_645 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _148_644 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _148_645 _148_644)))
in (FStar_All.failwith _148_646))
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

let ret = (let _148_648 = (let _148_647 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _148_647 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_648))
in (

let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (

let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (

let c = (let _148_650 = (let _148_649 = (bind e.FStar_Syntax_Syntax.pos env None (FStar_Syntax_Util.lcomp_of_comp c) ((Some (x)), (eq_ret)))
in (_148_649.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _148_650 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
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
(let _148_662 = (let _148_661 = (let _148_660 = (FStar_TypeChecker_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _148_659 = (FStar_TypeChecker_Env.get_range env)
in ((_148_660), (_148_659))))
in FStar_Syntax_Syntax.Error (_148_661))
in (Prims.raise _148_662))
end
| Some (g) -> begin
((e), (c'), (g))
end))


let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match ((let _148_671 = (FStar_Syntax_Subst.compress t)
in _148_671.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_56_1017) -> begin
(match ((let _148_672 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _148_672.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid) -> begin
(

let _56_1021 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (

let b2t = (let _148_673 = (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar _148_673 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (

let lc = (let _148_676 = (let _148_675 = (let _148_674 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_674))
in ((None), (_148_675)))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) lc _148_676))
in (

let e = (let _148_678 = (let _148_677 = (FStar_Syntax_Syntax.as_arg e)
in (_148_677)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _148_678 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
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
(let _148_687 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in ((_148_687), (false)))
end else begin
(let _148_688 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in ((_148_688), (true)))
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
in (match ((let _148_691 = (FStar_Syntax_Subst.compress f)
in _148_691.FStar_Syntax_Syntax.n)) with
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
(let _148_695 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _148_694 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _148_693 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _148_692 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _148_695 _148_694 _148_693 _148_692)))))
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

let us = (let _148_696 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_148_696)::[])
in (

let wp = (let _148_701 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ret_wp)
in (let _148_700 = (let _148_699 = (FStar_Syntax_Syntax.as_arg t)
in (let _148_698 = (let _148_697 = (FStar_Syntax_Syntax.as_arg xexp)
in (_148_697)::[])
in (_148_699)::_148_698))
in (FStar_Syntax_Syntax.mk_Tm_app _148_701 _148_700 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)))
in (

let cret = (let _148_702 = (mk_comp md t wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_702))
in (

let guard = if apply_guard then begin
(let _148_704 = (let _148_703 = (FStar_Syntax_Syntax.as_arg xexp)
in (_148_703)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _148_704 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end else begin
f
end
in (

let _56_1096 = (let _148_712 = (FStar_All.pipe_left (fun _148_709 -> Some (_148_709)) (FStar_TypeChecker_Errors.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _148_711 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _148_710 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _148_712 _148_711 e cret _148_710))))
in (match (_56_1096) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x = (

let _56_1097 = x
in {FStar_Syntax_Syntax.ppname = _56_1097.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_1097.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (

let c = (let _148_714 = (let _148_713 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _148_713))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) _148_714 ((Some (x)), (eq_ret))))
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let _56_1102 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _148_715 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _148_715))
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
in (let _148_717 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _148_717; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
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
in (let _148_729 = (let _148_728 = (let _148_727 = (let _148_726 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _148_726))
in (_148_727)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _148_728 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _148_729))))
in (

let norm = (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Unlabel)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env t))
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
(let _148_735 = (let _148_732 = (norm req)
in Some (_148_732))
in (let _148_734 = (let _148_733 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _148_733))
in ((_148_735), (_148_734))))
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

let as_req = (let _148_737 = (let _148_736 = (FStar_Ident.set_lid_range FStar_Syntax_Const.as_requires r)
in (FStar_Syntax_Syntax.fvar _148_736 FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _148_737 us_r))
in (

let as_ens = (let _148_739 = (let _148_738 = (FStar_Ident.set_lid_range FStar_Syntax_Const.as_ensures r)
in (FStar_Syntax_Syntax.fvar _148_738 FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _148_739 us_e))
in (

let req = (let _148_742 = (let _148_741 = (let _148_740 = (FStar_Syntax_Syntax.as_arg wp)
in (_148_740)::[])
in (((ct.FStar_Syntax_Syntax.result_typ), (Some (FStar_Syntax_Syntax.imp_tag))))::_148_741)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _148_742 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let ens = (let _148_745 = (let _148_744 = (let _148_743 = (FStar_Syntax_Syntax.as_arg wp)
in (_148_743)::[])
in (((ct.FStar_Syntax_Syntax.result_typ), (Some (FStar_Syntax_Syntax.imp_tag))))::_148_744)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _148_745 None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _148_749 = (let _148_746 = (norm req)
in Some (_148_746))
in (let _148_748 = (let _148_747 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm _148_747))
in ((_148_749), (_148_748)))))))))
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
(let _148_760 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((v), (Some (FStar_Syntax_Syntax.Implicit (dot)))))::args), (bs), (subst), (_148_760)))
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


let string_of_univs = (fun univs -> (let _148_765 = (let _148_764 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _148_764 (FStar_List.map (fun u -> (let _148_763 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _148_763 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _148_765 (FStar_String.concat ", "))))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(

let s = (let _148_771 = (let _148_770 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _148_770))
in (FStar_All.pipe_right _148_771 FStar_Util.set_elements))
in (

let _56_1231 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _148_773 = (let _148_772 = (FStar_TypeChecker_Env.univ_vars env)
in (string_of_univs _148_772))
in (FStar_Util.print1 "univ_vars in env: %s\n" _148_773))
end else begin
()
end
in (

let r = (let _148_774 = (FStar_TypeChecker_Env.get_range env)
in Some (_148_774))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (

let _56_1236 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _148_779 = (let _148_776 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _148_776))
in (let _148_778 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _148_777 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _148_779 _148_778 _148_777))))
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
(let _148_784 = (string_of_univs univs)
in (FStar_Util.print1 "univs to gen : %s\n" _148_784))
end else begin
()
end
in (

let gen = (gen_univs env univs)
in (

let _56_1248 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _148_785 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _148_785))
end else begin
()
end
in (

let ts = (FStar_Syntax_Subst.close_univ_vars gen t)
in ((gen), (ts)))))))))


let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> if (let _148_791 = (FStar_Util.for_all (fun _56_1256 -> (match (_56_1256) with
| (_56_1254, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _148_791)) then begin
None
end else begin
(

let norm = (fun c -> (

let _56_1259 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _148_794 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _148_794))
end else begin
()
end
in (

let c = if (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str) then begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.Eta)::[]) env c)
end else begin
(FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env c)
end
in (

let _56_1262 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _148_795 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _148_795))
end else begin
()
end
in c))))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (let _148_798 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _148_798 FStar_Util.set_elements)))
in (

let _56_1279 = (let _148_800 = (FStar_All.pipe_right ecs (FStar_List.map (fun _56_1269 -> (match (_56_1269) with
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
in (FStar_All.pipe_right _148_800 FStar_List.unzip))
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

let a = (let _148_806 = (let _148_805 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _148_804 -> Some (_148_804)) _148_805))
in (FStar_Syntax_Syntax.new_bv _148_806 kres))
in (

let t = (let _148_811 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _148_810 = (let _148_809 = (let _148_808 = (let _148_807 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _148_807))
in FStar_Util.Inl (_148_808))
in Some (_148_809))
in (FStar_Syntax_Util.abs bs _148_811 _148_810)))
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

let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoInline)::[]) env c)
in (

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoInline)::[]) env e)
in (

let t = (match ((let _148_812 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _148_812.FStar_Syntax_Syntax.n)) with
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
in (let _148_813 = (FStar_Syntax_Syntax.mk_Total t)
in ((e'), (_148_813)))))))
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
(let _148_820 = (let _148_819 = (FStar_List.map (fun _56_1376 -> (match (_56_1376) with
| (lb, _56_1373, _56_1375) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _148_819 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _148_820))
end else begin
()
end
in (match ((let _148_822 = (FStar_All.pipe_right lecs (FStar_List.map (fun _56_1383 -> (match (_56_1383) with
| (_56_1380, e, c) -> begin
((e), (c))
end))))
in (gen env _148_822))) with
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
(let _148_828 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _148_827 = (FStar_Syntax_Print.lbname_to_string l)
in (let _148_826 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.print3 "(%s) Generalized %s to %s\n" _148_828 _148_827 _148_826))))
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
(let _148_844 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _148_843 -> Some (_148_843)) _148_844))
end)
end)
in (

let is_var = (fun e -> (match ((let _148_847 = (FStar_Syntax_Subst.compress e)
in _148_847.FStar_Syntax_Syntax.n)) with
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
in (let _148_852 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _56_1432.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _148_852; FStar_Syntax_Syntax.pos = _56_1432.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _56_1432.FStar_Syntax_Syntax.vars}))
end)))
in (

let env = (

let _56_1434 = env
in (let _148_853 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _56_1434.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _56_1434.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _56_1434.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _56_1434.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _56_1434.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _56_1434.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _56_1434.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _56_1434.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _56_1434.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _56_1434.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _56_1434.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _56_1434.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _56_1434.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _56_1434.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _56_1434.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _148_853; FStar_TypeChecker_Env.is_iface = _56_1434.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _56_1434.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _56_1434.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _56_1434.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _56_1434.FStar_TypeChecker_Env.use_bv_sorts}))
in (match ((check env t1 t2)) with
| None -> begin
(let _148_857 = (let _148_856 = (let _148_855 = (FStar_TypeChecker_Errors.expected_expression_of_type env t2 e t1)
in (let _148_854 = (FStar_TypeChecker_Env.get_range env)
in ((_148_855), (_148_854))))
in FStar_Syntax_Syntax.Error (_148_856))
in (Prims.raise _148_857))
end
| Some (g) -> begin
(

let _56_1440 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _148_858 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _148_858))
end else begin
()
end
in (let _148_859 = (decorate e t2)
in ((_148_859), (g))))
end)))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (

let discharge = (fun g -> (

let _56_1447 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _148_869 = (discharge g)
in (let _148_868 = (lc.FStar_Syntax_Syntax.comp ())
in ((_148_869), (_148_868))))
end else begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let steps = (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.DeltaComp)::[]
in (

let c = (let _148_872 = (let _148_871 = (let _148_870 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (FStar_All.pipe_right _148_870 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right _148_871 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (FStar_All.pipe_right _148_872 FStar_Syntax_Util.comp_to_comp_typ))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let _56_1456 = (destruct_comp c)
in (match (_56_1456) with
| (t, wp) -> begin
(

let vc = (let _148_880 = (let _148_874 = (let _148_873 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_148_873)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _148_874 env md md.FStar_Syntax_Syntax.trivial))
in (let _148_879 = (let _148_877 = (FStar_Syntax_Syntax.as_arg t)
in (let _148_876 = (let _148_875 = (FStar_Syntax_Syntax.as_arg wp)
in (_148_875)::[])
in (_148_877)::_148_876))
in (let _148_878 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk_Tm_app _148_880 _148_879 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _148_878))))
in (

let _56_1458 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _148_881 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _148_881))
end else begin
()
end
in (

let g = (let _148_882 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _148_882))
in (let _148_884 = (discharge g)
in (let _148_883 = (FStar_Syntax_Syntax.mk_Comp c)
in ((_148_884), (_148_883)))))))
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

let op_and_e = (fun e -> (let _148_905 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _148_905 (fun _148_904 -> FStar_TypeChecker_Common.NonTrivial (_148_904)))))
in (

let op_or_e = (fun e -> (let _148_910 = (let _148_908 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _148_908))
in (FStar_All.pipe_right _148_910 (fun _148_909 -> FStar_TypeChecker_Common.NonTrivial (_148_909)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _148_913 -> FStar_TypeChecker_Common.NonTrivial (_148_913))))
in (

let op_or_t = (fun t -> (let _148_917 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _148_917 (fun _148_916 -> FStar_TypeChecker_Common.NonTrivial (_148_916)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _148_920 -> FStar_TypeChecker_Common.NonTrivial (_148_920))))
in (

let short_op_ite = (fun _56_6 -> (match (_56_6) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((guard, _56_1488))::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| (_then)::((guard, _56_1493))::[] -> begin
(let _148_924 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _148_924 (fun _148_923 -> FStar_TypeChecker_Common.NonTrivial (_148_923))))
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
(let _148_957 = (mk seen_args)
in Some (_148_957))
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


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (match ((let _148_960 = (FStar_Syntax_Util.un_uinst l)
in _148_960.FStar_Syntax_Syntax.n)) with
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
(match ((let _148_967 = (FStar_Syntax_Subst.compress t)
in _148_967.FStar_Syntax_Syntax.n)) with
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
(let _148_971 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in ((_148_971), (i)))
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
(let _148_980 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic_lift (((m1), (m2))))))) _148_980 e.FStar_Syntax_Syntax.pos))
end)))


let maybe_monadic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env e c -> (

let m = (FStar_TypeChecker_Env.norm_eff_name env c)
in if (((is_pure_or_ghost_effect env m) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid)) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid)) then begin
e
end else begin
(let _148_987 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_monadic (m))))) _148_987 e.FStar_Syntax_Syntax.pos))
end))


let reify_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term = (fun env c u_c -> (

let no_reify = (fun l -> (let _148_999 = (let _148_998 = (let _148_997 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in (let _148_996 = (FStar_TypeChecker_Env.get_range env)
in ((_148_997), (_148_996))))
in FStar_Syntax_Syntax.Error (_148_998))
in (Prims.raise _148_999)))
in (match ((let _148_1000 = (FStar_TypeChecker_Env.norm_eff_name env c.FStar_Syntax_Syntax.eff_name)
in (FStar_TypeChecker_Env.effect_decl_opt env _148_1000))) with
| None -> begin
(no_reify c.FStar_Syntax_Syntax.eff_name)
end
| Some (ed) -> begin
if (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)))) then begin
(no_reify c.FStar_Syntax_Syntax.eff_name)
end else begin
(

let c = (let _148_1001 = (c.FStar_Syntax_Syntax.comp ())
in (FStar_TypeChecker_Normalize.unfold_effect_abbrev env _148_1001))
in (

let _56_1607 = (let _148_1002 = (FStar_List.hd c.FStar_Syntax_Syntax.effect_args)
in ((c.FStar_Syntax_Syntax.result_typ), (_148_1002)))
in (match (_56_1607) with
| (res_typ, wp) -> begin
(

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u_c)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (let _148_1007 = (let _148_1005 = (let _148_1004 = (let _148_1003 = (FStar_Syntax_Syntax.as_arg res_typ)
in (_148_1003)::(wp)::[])
in ((repr), (_148_1004)))
in FStar_Syntax_Syntax.Tm_app (_148_1005))
in (let _148_1006 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk _148_1007 None _148_1006))))
end)))
end
end)))


let d : Prims.string  ->  Prims.unit = (fun s -> (FStar_Util.print1 "\\x1b[01;36m%s\\x1b[00m\n" s))


let register_toplevel_definition : FStar_TypeChecker_Env.env  ->  (FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelts * FStar_TypeChecker_Env.env))  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.typ) = (fun env tc_decl lident def -> (

let _56_1614 = (d (FStar_Ident.text_of_lid lident))
in (

let _56_1616 = (let _148_1028 = (FStar_Syntax_Print.term_to_string def)
in (FStar_Util.print2 "Registering top-level definition: %s\n%s\n" (FStar_Ident.text_of_lid lident) _148_1028))
in (

let fv = (let _148_1029 = (FStar_Syntax_Util.incr_delta_qualifier def)
in (FStar_Syntax_Syntax.lid_as_fv lident _148_1029 None))
in (

let lbname = FStar_Util.Inr (fv)
in (

let lb = ((false), (({FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = def})::[]))
in (

let sig_ctx = FStar_Syntax_Syntax.Sig_let (((lb), (FStar_Range.dummyRange), ((lident)::[]), ([])))
in (

let _56_1624 = (tc_decl env sig_ctx)
in (match (_56_1624) with
| (se, env) -> begin
(

let _56_1650 = (match (se) with
| (FStar_Syntax_Syntax.Sig_let ((_56_1626, ({FStar_Syntax_Syntax.lbname = _56_1635; FStar_Syntax_Syntax.lbunivs = _56_1633; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _56_1630; FStar_Syntax_Syntax.lbdef = _56_1628})::[]), _56_1640, _56_1642, _56_1644))::[] -> begin
(let _148_1030 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Inferred type: %s\n" _148_1030))
end
| _56_1649 -> begin
(FStar_All.failwith "nope")
end)
in (let _148_1031 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) None FStar_Range.dummyRange)
in ((env), (_148_1031))))
end)))))))))




