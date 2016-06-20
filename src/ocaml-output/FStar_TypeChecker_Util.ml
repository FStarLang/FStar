
open Prims

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv Prims.option * FStar_Syntax_Syntax.lcomp)


let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _146_6 = (FStar_TypeChecker_Env.get_range env)
in (let _146_5 = (FStar_TypeChecker_Errors.failed_to_prove_specification errs)
in (FStar_TypeChecker_Errors.report _146_6 _146_5))))


let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _146_9 = (FStar_Syntax_Subst.compress t)
in _146_9.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_56_12) -> begin
true
end
| _56_15 -> begin
false
end))


let t_binders : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env -> (let _146_13 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right _146_13 (FStar_List.filter (fun _56_20 -> (match (_56_20) with
| (x, _56_19) -> begin
(is_type x.FStar_Syntax_Syntax.sort)
end))))))


let new_uvar_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun env k -> (

let bs = if ((FStar_Options.full_context_dependency ()) || (let _146_18 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _146_18))) then begin
(FStar_TypeChecker_Env.all_binders env)
end else begin
(t_binders env)
end
in (let _146_19 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Rel.new_uvar _146_19 bs k))))


let new_uvar : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env k -> (let _146_24 = (new_uvar_aux env k)
in (Prims.fst _146_24)))


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
in (t, [], FStar_TypeChecker_Rel.trivial_guard))
end
| _56_55 -> begin
(

let _56_58 = (new_uvar_aux env k)
in (match (_56_58) with
| (t, u) -> begin
(

let g = (

let _56_59 = FStar_TypeChecker_Rel.trivial_guard
in (let _146_37 = (let _146_36 = (let _146_35 = (as_uvar u)
in (reason, env, _146_35, t, k, r))
in (_146_36)::[])
in {FStar_TypeChecker_Env.guard_f = _56_59.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _56_59.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_59.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _146_37}))
in (let _146_40 = (let _146_39 = (let _146_38 = (as_uvar u)
in (_146_38, r))
in (_146_39)::[])
in (t, _146_40, g)))
end))
end))


let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun r t -> (

let uvs = (FStar_Syntax_Free.uvars t)
in if (not ((FStar_Util.set_is_empty uvs))) then begin
(

let us = (let _146_47 = (let _146_46 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun _56_68 -> (match (_56_68) with
| (x, _56_67) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) _146_46))
in (FStar_All.pipe_right _146_47 (FStar_String.concat ", ")))
in (

let _56_70 = (FStar_Options.push ())
in (

let _56_72 = (FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool (false)))
in (

let _56_74 = (FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)))
in (

let _56_76 = (let _146_49 = (let _146_48 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us _146_48))
in (FStar_TypeChecker_Errors.report r _146_49))
in (FStar_Options.pop ()))))))
end else begin
()
end))


let force_sort' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' = (fun s -> (match ((FStar_ST.read s.FStar_Syntax_Syntax.tk)) with
| None -> begin
(let _146_54 = (let _146_53 = (FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos)
in (let _146_52 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s" _146_53 _146_52)))
in (FStar_All.failwith _146_54))
end
| Some (tk) -> begin
tk
end))


let force_sort = (fun s -> (let _146_56 = (force_sort' s)
in (FStar_Syntax_Syntax.mk _146_56 None s.FStar_Syntax_Syntax.pos)))


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

let mk_binder = (fun scope a -> (match ((let _146_65 = (FStar_Syntax_Subst.compress a.FStar_Syntax_Syntax.sort)
in _146_65.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _56_105 = (FStar_Syntax_Util.type_u ())
in (match (_56_105) with
| (k, _56_104) -> begin
(

let t = (let _146_66 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right _146_66 Prims.fst))
in ((

let _56_107 = a
in {FStar_Syntax_Syntax.ppname = _56_107.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_107.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), false))
end))
end
| _56_110 -> begin
(a, true)
end))
in (

let rec aux = (fun vars e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, _56_117) -> begin
(aux vars e)
end
| FStar_Syntax_Syntax.Tm_ascribed (e, t, _56_123) -> begin
(t, true)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _56_129) -> begin
(

let _56_148 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _56_135 _56_138 -> (match ((_56_135, _56_138)) with
| ((scope, bs, check), (a, imp)) -> begin
(

let _56_141 = (mk_binder scope a)
in (match (_56_141) with
| (tb, c) -> begin
(

let b = (tb, imp)
in (

let bs = (FStar_List.append bs ((b)::[]))
in (

let scope = (FStar_List.append scope ((b)::[]))
in (scope, bs, (c || check)))))
end))
end)) (vars, [], false)))
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
(let _146_74 = (FStar_Range.string_of_range r)
in (let _146_73 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _146_74 _146_73)))
end else begin
()
end
in (FStar_Util.Inl (t), (check_res || check)))))
end))
end))
end
| _56_161 -> begin
(let _146_77 = (let _146_76 = (let _146_75 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _146_75 Prims.fst))
in FStar_Util.Inl (_146_76))
in (_146_77, false))
end)))
in (

let _56_164 = (let _146_78 = (t_binders env)
in (aux _146_78 e))
in (match (_56_164) with
| (t, b) -> begin
(

let t = (match (t) with
| FStar_Util.Inr (c) -> begin
(let _146_82 = (let _146_81 = (let _146_80 = (let _146_79 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" _146_79))
in (_146_80, rng))
in FStar_Syntax_Syntax.Error (_146_81))
in (Prims.raise _146_82))
end
| FStar_Util.Inl (t) -> begin
t
end)
in ([], t, b))
end))))))
end
| _56_171 -> begin
(

let _56_174 = (FStar_Syntax_Subst.open_univ_vars univ_vars t)
in (match (_56_174) with
| (univ_vars, t) -> begin
(univ_vars, t, false)
end))
end)))
end))


let pat_as_exps : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term Prims.list * FStar_Syntax_Syntax.pat) = (fun allow_implicits env p -> (

let rec pat_as_arg_with_env = (fun allow_wc_dependence env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) None p.FStar_Syntax_Syntax.p)
in ([], [], [], env, e, p))
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

let _56_200 = (let _146_95 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _146_95 t))
in (match (_56_200) with
| (e, u) -> begin
(

let p = (

let _56_201 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, e)); FStar_Syntax_Syntax.ty = _56_201.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_201.FStar_Syntax_Syntax.p})
in ([], [], [], env, e, p))
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
in (let _146_96 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _56_210.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_210.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_96}))
in (

let env = if allow_wc_dependence then begin
(FStar_TypeChecker_Env.push_bv env x)
end else begin
env
end
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in ((x)::[], [], (x)::[], env, e, p))))
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
in (let _146_97 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _56_221.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_221.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_97}))
in (

let env = (FStar_TypeChecker_Env.push_bv env x)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name (x)) None p.FStar_Syntax_Syntax.p)
in ((x)::[], (x)::[], [], env, e, p))))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _56_254 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _56_236 _56_239 -> (match ((_56_236, _56_239)) with
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
in ((b')::b, (a')::a, (w')::w, env, (arg)::args, ((pat, imp))::pats))
end))
end)) ([], [], [], env, [], [])))
in (match (_56_254) with
| (b, a, w, env, args, pats) -> begin
(

let e = (let _146_104 = (let _146_103 = (let _146_102 = (let _146_101 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (let _146_100 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app _146_101 _146_100 None p.FStar_Syntax_Syntax.p)))
in (_146_102, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))
in FStar_Syntax_Syntax.Tm_meta (_146_103))
in (FStar_Syntax_Syntax.mk _146_104 None p.FStar_Syntax_Syntax.p))
in (let _146_107 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _146_106 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _146_105 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in (_146_107, _146_106, _146_105, env, e, (

let _56_256 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _56_256.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_256.FStar_Syntax_Syntax.p}))))))
end))
end
| FStar_Syntax_Syntax.Pat_disj (_56_259) -> begin
(FStar_All.failwith "impossible")
end))
in (

let rec elaborate_pat = (fun env p -> (

let maybe_dot = (fun inaccessible a r -> if (allow_implicits && inaccessible) then begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term ((a, FStar_Syntax_Syntax.tun))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end else begin
(FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var (a)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r)
end)
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let pats = (FStar_List.map (fun _56_274 -> (match (_56_274) with
| (p, imp) -> begin
(let _146_119 = (elaborate_pat env p)
in (_146_119, imp))
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

let rec aux = (fun formals pats -> (match ((formals, pats)) with
| ([], []) -> begin
[]
end
| ([], (_56_294)::_56_292) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))))
end
| ((_56_300)::_56_298, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun _56_306 -> (match (_56_306) with
| (t, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(

let a = (let _146_126 = (let _146_125 = (FStar_Syntax_Syntax.range_of_bv t)
in Some (_146_125))
in (FStar_Syntax_Syntax.new_bv _146_126 FStar_Syntax_Syntax.tun))
in (

let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (let _146_127 = (maybe_dot inaccessible a r)
in (_146_127, true))))
end
| _56_313 -> begin
(let _146_131 = (let _146_130 = (let _146_129 = (let _146_128 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _146_128))
in (_146_129, (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in FStar_Syntax_Syntax.Error (_146_130))
in (Prims.raise _146_131))
end)
end))))
end
| ((f)::formals', ((p, p_imp))::pats') -> begin
(match (f) with
| (_56_324, Some (FStar_Syntax_Syntax.Implicit (_56_326))) when p_imp -> begin
(let _146_132 = (aux formals' pats')
in ((p, true))::_146_132)
end
| (_56_331, Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(

let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let p = (maybe_dot inaccessible a (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
in (let _146_133 = (aux formals' pats)
in ((p, true))::_146_133)))
end
| (_56_339, imp) -> begin
(let _146_136 = (let _146_134 = (FStar_Syntax_Syntax.is_implicit imp)
in (p, _146_134))
in (let _146_135 = (aux formals' pats')
in (_146_136)::_146_135))
end)
end))
in (

let _56_342 = p
in (let _146_139 = (let _146_138 = (let _146_137 = (aux f pats)
in (fv, _146_137))
in FStar_Syntax_Syntax.Pat_cons (_146_138))
in {FStar_Syntax_Syntax.v = _146_139; FStar_Syntax_Syntax.ty = _56_342.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_342.FStar_Syntax_Syntax.p})))
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
(let _146_148 = (let _146_147 = (let _146_146 = (FStar_TypeChecker_Errors.nonlinear_pattern_variable x)
in (_146_146, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_146_147))
in (Prims.raise _146_148))
end
| _56_361 -> begin
(b, a, w, arg, p)
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
(let _146_158 = (let _146_157 = (let _146_156 = (FStar_TypeChecker_Errors.disjunctive_pattern_vars a a')
in (let _146_155 = (FStar_TypeChecker_Env.get_range env)
in (_146_156, _146_155)))
in FStar_Syntax_Syntax.Error (_146_157))
in (Prims.raise _146_158))
end else begin
(let _146_160 = (let _146_159 = (FStar_Syntax_Syntax.as_arg arg)
in (_146_159)::args)
in ((FStar_List.append w' w), _146_160, (p)::pats))
end
end))
end)) pats ([], [], []))
in (match (_56_392) with
| (w, args, pats) -> begin
(let _146_162 = (let _146_161 = (FStar_Syntax_Syntax.as_arg te)
in (_146_161)::args)
in ((FStar_List.append b w), _146_162, (

let _56_393 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((q)::pats); FStar_Syntax_Syntax.ty = _56_393.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_393.FStar_Syntax_Syntax.p})))
end))
end))
end
| _56_396 -> begin
(

let _56_404 = (one_pat true env p)
in (match (_56_404) with
| (b, _56_399, _56_401, arg, p) -> begin
(let _146_164 = (let _146_163 = (FStar_Syntax_Syntax.as_arg arg)
in (_146_163)::[])
in (b, _146_164, p))
end))
end))
in (

let _56_408 = (top_level_pat_as_args env p)
in (match (_56_408) with
| (b, args, p) -> begin
(

let exps = (FStar_All.pipe_right args (FStar_List.map Prims.fst))
in (b, exps, p))
end)))))))


let decorate_pattern : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.pat = (fun env p exps -> (

let qq = p
in (

let rec aux = (fun p e -> (

let pkg = (fun q t -> (FStar_Syntax_Syntax.withinfo q t p.FStar_Syntax_Syntax.p))
in (

let e = (FStar_Syntax_Util.unmeta e)
in (match ((p.FStar_Syntax_Syntax.v, e.FStar_Syntax_Syntax.n)) with
| (_56_422, FStar_Syntax_Syntax.Tm_uinst (e, _56_425)) -> begin
(aux p e)
end
| (FStar_Syntax_Syntax.Pat_constant (_56_430), FStar_Syntax_Syntax.Tm_constant (_56_433)) -> begin
(let _146_179 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v _146_179))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(

let _56_441 = if (not ((FStar_Syntax_Syntax.bv_eq x y))) then begin
(let _146_182 = (let _146_181 = (FStar_Syntax_Print.bv_to_string x)
in (let _146_180 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _146_181 _146_180)))
in (FStar_All.failwith _146_182))
end else begin
()
end
in (

let _56_443 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _146_184 = (FStar_Syntax_Print.bv_to_string x)
in (let _146_183 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _146_184 _146_183)))
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
(let _146_187 = (let _146_186 = (FStar_Syntax_Print.bv_to_string x)
in (let _146_185 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _146_186 _146_185)))
in (FStar_All.failwith _146_187))
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
in (pkg (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) s.FStar_Syntax_Syntax.n)))
end
| (FStar_Syntax_Syntax.Pat_cons (fv, []), FStar_Syntax_Syntax.Tm_fvar (fv')) -> begin
(

let _56_479 = if (not ((FStar_Syntax_Syntax.fv_eq fv fv'))) then begin
(let _146_188 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _146_188))
end else begin
()
end
in (let _146_189 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv', []))) _146_189)))
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
(

let _56_522 = if (let _146_190 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right _146_190 Prims.op_Negation)) then begin
(let _146_191 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _146_191))
end else begin
()
end
in (

let fv = fv'
in (

let rec match_args = (fun matched_pats args argpats -> (match ((args, argpats)) with
| ([], []) -> begin
(let _146_198 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev matched_pats)))) _146_198))
end
| ((arg)::args, ((argpat, _56_538))::argpats) -> begin
(match ((arg, argpat.FStar_Syntax_Syntax.v)) with
| ((e, Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (_56_548)) -> begin
(

let x = (let _146_199 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _146_199))
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((e, imp), _56_557) -> begin
(

let pat = (let _146_201 = (aux argpat e)
in (let _146_200 = (FStar_Syntax_Syntax.is_implicit imp)
in (_146_201, _146_200)))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _56_561 -> begin
(let _146_204 = (let _146_203 = (FStar_Syntax_Print.pat_to_string p)
in (let _146_202 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _146_203 _146_202)))
in (FStar_All.failwith _146_204))
end))
in (match_args [] args argpats))))
end
| _56_563 -> begin
(let _146_209 = (let _146_208 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (let _146_207 = (FStar_Syntax_Print.pat_to_string qq)
in (let _146_206 = (let _146_205 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right _146_205 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _146_208 _146_207 _146_206))))
in (FStar_All.failwith _146_209))
end))))
in (match ((p.FStar_Syntax_Syntax.v, exps)) with
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
(let _146_217 = (let _146_216 = (FStar_Syntax_Syntax.as_implicit i)
in (te, _146_216))
in (vars, _146_217))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_56_589) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _146_218 = (mk (FStar_Syntax_Syntax.Tm_constant (c)))
in ([], _146_218))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(let _146_219 = (mk (FStar_Syntax_Syntax.Tm_name (x)))
in ((x)::[], _146_219))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _56_602 = (let _146_220 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _146_220 FStar_List.unzip))
in (match (_56_602) with
| (vars, args) -> begin
(

let vars = (FStar_List.flatten vars)
in (let _146_224 = (let _146_223 = (let _146_222 = (let _146_221 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (_146_221, args))
in FStar_Syntax_Syntax.Tm_app (_146_222))
in (mk _146_223))
in (vars, _146_224)))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
([], e)
end)))))


let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.typ * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun c -> (

let wp = (match (c.FStar_Syntax_Syntax.effect_args) with
| ((wp, _56_611))::[] -> begin
wp
end
| _56_615 -> begin
(let _146_230 = (let _146_229 = (let _146_228 = (FStar_List.map (fun _56_619 -> (match (_56_619) with
| (x, _56_618) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right _146_228 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str _146_229))
in (FStar_All.failwith _146_230))
end)
in (c.FStar_Syntax_Syntax.result_typ, wp)))


let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (

let _56_627 = (destruct_comp c)
in (match (_56_627) with
| (_56_625, wp) -> begin
(let _146_249 = (let _146_248 = (let _146_247 = (lift c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _146_247))
in (_146_248)::[])
in {FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _146_249; FStar_Syntax_Syntax.flags = []})
end)))


let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let _56_636 = (let _146_257 = (FStar_TypeChecker_Env.norm_eff_name env l1)
in (let _146_256 = (FStar_TypeChecker_Env.norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _146_257 _146_256)))
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
(let _146_271 = (destruct_comp m1)
in (let _146_270 = (destruct_comp m2)
in ((md, a, kwp), _146_271, _146_270)))
end)))))
end)))))


let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid))))


let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md result wp flags -> (let _146_290 = (let _146_289 = (let _146_288 = (FStar_Syntax_Syntax.as_arg wp)
in (_146_288)::[])
in {FStar_Syntax_Syntax.effect_name = md.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = _146_289; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp _146_290)))


let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (

let _56_667 = lc
in (let _146_297 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _56_667.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _146_297; FStar_Syntax_Syntax.cflags = _56_667.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _56_669 -> (match (()) with
| () -> begin
(let _146_296 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _146_296))
end))})))


let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _146_300 = (FStar_Syntax_Subst.compress t)
in _146_300.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_56_672) -> begin
true
end
| _56_675 -> begin
false
end))


let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v -> (

let c = if (let _146_307 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation _146_307)) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(

let m = (let _146_308 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must _146_308))
in (

let _56_682 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_56_682) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (

let wp = (let _146_316 = (let _146_315 = (let _146_310 = (let _146_309 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_146_309)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _146_310 env m m.FStar_Syntax_Syntax.ret))
in (let _146_314 = (let _146_313 = (FStar_Syntax_Syntax.as_arg t)
in (let _146_312 = (let _146_311 = (FStar_Syntax_Syntax.as_arg v)
in (_146_311)::[])
in (_146_313)::_146_312))
in (FStar_Syntax_Syntax.mk_Tm_app _146_315 _146_314 (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _146_316))
in (mk_comp m t wp ((FStar_Syntax_Syntax.RETURN)::[]))))
end)))
end
in (

let _56_686 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return"))) then begin
(let _146_319 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _146_318 = (FStar_Syntax_Print.term_to_string v)
in (let _146_317 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _146_319 _146_318 _146_317))))
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
in (let _146_332 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (let _146_331 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _146_330 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" _146_332 _146_331 bstr _146_330)))))
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
(let _146_339 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _146_338 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _146_337 = (FStar_Syntax_Print.comp_to_string c1)
in (let _146_336 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (let _146_335 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" _146_339 _146_338 _146_337 _146_336 _146_335))))))
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
Some ((c2, "trivial no binder"))
end
| Some (_56_721) -> begin
if (FStar_Syntax_Util.is_ml_comp c2) then begin
Some ((c2, "trivial ml"))
end else begin
None
end
end)
end else begin
if ((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) then begin
Some ((c2, "both ml"))
end else begin
None
end
end
end))
in (

let subst_c2 = (fun reason -> (match ((e1opt, b)) with
| (Some (e), Some (x)) -> begin
(let _146_347 = (let _146_346 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT ((x, e)))::[]) c2)
in (_146_346, reason))
in Some (_146_347))
end
| _56_731 -> begin
(aux ())
end))
in if ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2)) then begin
(subst_c2 "both total")
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2)) then begin
(let _146_349 = (let _146_348 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in (_146_348, "both gtot"))
in Some (_146_349))
end else begin
(match ((e1opt, b)) with
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
(let _146_350 = (FStar_Syntax_Syntax.null_binder t1)
in (_146_350)::[])
end
| Some (x) -> begin
(let _146_351 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_351)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid)))))
in (

let r1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1))) None r1)
in (

let wp_args = (let _146_363 = (FStar_Syntax_Syntax.as_arg r1)
in (let _146_362 = (let _146_361 = (FStar_Syntax_Syntax.as_arg t1)
in (let _146_360 = (let _146_359 = (FStar_Syntax_Syntax.as_arg t2)
in (let _146_358 = (let _146_357 = (FStar_Syntax_Syntax.as_arg wp1)
in (let _146_356 = (let _146_355 = (let _146_354 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg _146_354))
in (_146_355)::[])
in (_146_357)::_146_356))
in (_146_359)::_146_358))
in (_146_361)::_146_360))
in (_146_363)::_146_362))
in (

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t2)))::[]) kwp)
in (

let us = (let _146_366 = (env.FStar_TypeChecker_Env.universe_of env t1)
in (let _146_365 = (let _146_364 = (env.FStar_TypeChecker_Env.universe_of env t2)
in (_146_364)::[])
in (_146_366)::_146_365))
in (

let wp = (let _146_367 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _146_367 wp_args None t2.FStar_Syntax_Syntax.pos))
in (

let c = (mk_comp md t2 wp [])
in c))))))))
end))
end)))))
end))
in (let _146_368 = (join_lcomp env lc1 lc2)
in {FStar_Syntax_Syntax.eff_name = _146_368; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it})))))
end))


let lift_formula : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t mk_wp f -> (

let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (

let _56_774 = (FStar_TypeChecker_Env.wp_signature env md_pure.FStar_Syntax_Syntax.mname)
in (match (_56_774) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (

let wp = (let _146_380 = (let _146_379 = (FStar_Syntax_Syntax.as_arg t)
in (let _146_378 = (let _146_377 = (FStar_Syntax_Syntax.as_arg f)
in (_146_377)::[])
in (_146_379)::_146_378))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wp _146_380 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (mk_comp md_pure FStar_TypeChecker_Common.t_unit wp [])))
end))))


let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((f, FStar_Syntax_Syntax.Meta_labeled ((reason, r, false))))) None f.FStar_Syntax_Syntax.pos))


let label_opt : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _146_404 = (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)
in (FStar_All.pipe_left Prims.op_Negation _146_404)) then begin
f
end else begin
(let _146_405 = (reason ())
in (label _146_405 r f))
end
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let _56_793 = g
in (let _146_413 = (let _146_412 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_146_412))
in {FStar_TypeChecker_Env.guard_f = _146_413; FStar_TypeChecker_Env.deferred = _56_793.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_793.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_793.FStar_TypeChecker_Env.implicits}))
end))


let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
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

let us = (let _146_426 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_146_426)::[])
in (

let wp = (let _146_433 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _146_432 = (let _146_431 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_430 = (let _146_429 = (FStar_Syntax_Syntax.as_arg f)
in (let _146_428 = (let _146_427 = (FStar_Syntax_Syntax.as_arg wp)
in (_146_427)::[])
in (_146_429)::_146_428))
in (_146_431)::_146_430))
in (FStar_Syntax_Syntax.mk_Tm_app _146_433 _146_432 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp c.FStar_Syntax_Syntax.flags))))
end)))
end
end))
end))
in (

let _56_821 = lc
in {FStar_Syntax_Syntax.eff_name = _56_821.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _56_821.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _56_821.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))


let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> if (FStar_TypeChecker_Rel.is_trivial g0) then begin
(lc, g0)
end else begin
(

let _56_828 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _146_453 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _146_452 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _146_453 _146_452)))
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

let xret = (let _146_458 = (let _146_457 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _146_457))
in (FStar_Syntax_Util.comp_set_flags _146_458 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (

let lc = (bind e.FStar_Syntax_Syntax.pos env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), (FStar_Syntax_Util.lcomp_of_comp xret)))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (

let _56_847 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _146_460 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _146_459 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _146_460 _146_459)))
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

let us = (let _146_461 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_146_461)::[])
in (

let wp = (let _146_470 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assert_p)
in (let _146_469 = (let _146_468 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_467 = (let _146_466 = (let _146_463 = (let _146_462 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason _146_462 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _146_463))
in (let _146_465 = (let _146_464 = (FStar_Syntax_Syntax.as_arg wp)
in (_146_464)::[])
in (_146_466)::_146_465))
in (_146_468)::_146_467))
in (FStar_Syntax_Syntax.mk_Tm_app _146_470 _146_469 None wp.FStar_Syntax_Syntax.pos)))
in (

let _56_856 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _146_471 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _146_471))
end else begin
()
end
in (

let c2 = (mk_comp md res_t wp flags)
in c2)))))
end)))))
end)))
end))
in (let _146_475 = (

let _56_859 = lc
in (let _146_474 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _146_473 = if ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _146_472 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _146_472))) then begin
flags
end else begin
[]
end
in {FStar_Syntax_Syntax.eff_name = _146_474; FStar_Syntax_Syntax.res_typ = _56_859.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _146_473; FStar_Syntax_Syntax.comp = strengthen})))
in (_146_475, (

let _56_861 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _56_861.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_861.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_861.FStar_TypeChecker_Env.implicits}))))))
end)


let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env comp res_t -> (

let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let y = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let _56_871 = (let _146_483 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _146_482 = (FStar_Syntax_Syntax.bv_to_name y)
in (_146_483, _146_482)))
in (match (_56_871) with
| (xexp, yexp) -> begin
(

let us = (let _146_484 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_146_484)::[])
in (

let yret = (let _146_489 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _146_488 = (let _146_487 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_486 = (let _146_485 = (FStar_Syntax_Syntax.as_arg yexp)
in (_146_485)::[])
in (_146_487)::_146_486))
in (FStar_Syntax_Syntax.mk_Tm_app _146_489 _146_488 None res_t.FStar_Syntax_Syntax.pos)))
in (

let x_eq_y_yret = (let _146_497 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _146_496 = (let _146_495 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_494 = (let _146_493 = (let _146_490 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _146_490))
in (let _146_492 = (let _146_491 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_146_491)::[])
in (_146_493)::_146_492))
in (_146_495)::_146_494))
in (FStar_Syntax_Syntax.mk_Tm_app _146_497 _146_496 None res_t.FStar_Syntax_Syntax.pos)))
in (

let forall_y_x_eq_y_yret = (let _146_507 = (FStar_TypeChecker_Env.inst_effect_fun_with (FStar_List.append us us) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _146_506 = (let _146_505 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_504 = (let _146_503 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_502 = (let _146_501 = (let _146_500 = (let _146_499 = (let _146_498 = (FStar_Syntax_Syntax.mk_binder y)
in (_146_498)::[])
in (FStar_Syntax_Util.abs _146_499 x_eq_y_yret (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid)))))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _146_500))
in (_146_501)::[])
in (_146_503)::_146_502))
in (_146_505)::_146_504))
in (FStar_Syntax_Syntax.mk_Tm_app _146_507 _146_506 None res_t.FStar_Syntax_Syntax.pos)))
in (

let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (

let lc = (let _146_508 = (FStar_TypeChecker_Env.get_range env)
in (bind _146_508 env None (FStar_Syntax_Util.lcomp_of_comp comp) (Some (x), (FStar_Syntax_Util.lcomp_of_comp lc2))))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))


let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (

let comp = (fun _56_883 -> (match (()) with
| () -> begin
(

let _56_897 = (let _146_520 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _146_519 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _146_520 _146_519)))
in (match (_56_897) with
| ((md, _56_886, _56_888), (res_t, wp_then), (_56_894, wp_else)) -> begin
(

let us = (let _146_521 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_146_521)::[])
in (

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _146_541 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _146_540 = (let _146_538 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_537 = (let _146_536 = (FStar_Syntax_Syntax.as_arg g)
in (let _146_535 = (let _146_534 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _146_533 = (let _146_532 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_146_532)::[])
in (_146_534)::_146_533))
in (_146_536)::_146_535))
in (_146_538)::_146_537))
in (let _146_539 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _146_541 _146_540 None _146_539)))))
in (

let wp = (ifthenelse md res_t guard wp_then wp_else)
in if ((FStar_Options.split_cases ()) > 0) then begin
(

let comp = (mk_comp md res_t wp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(

let wp = (let _146_546 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _146_545 = (let _146_544 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_543 = (let _146_542 = (FStar_Syntax_Syntax.as_arg wp)
in (_146_542)::[])
in (_146_544)::_146_543))
in (FStar_Syntax_Syntax.mk_Tm_app _146_546 _146_545 None wp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp []))
end)))
end))
end))
in (let _146_547 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _146_547; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp})))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (let _146_553 = (let _146_552 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid _146_552))
in (FStar_Syntax_Syntax.fvar _146_553 FStar_Syntax_Syntax.Delta_constant None)))


let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (FStar_List.fold_left (fun eff _56_917 -> (match (_56_917) with
| (_56_915, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (

let bind_cases = (fun _56_920 -> (match (()) with
| () -> begin
(

let us = (let _146_564 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_146_564)::[])
in (

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _146_584 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _146_583 = (let _146_581 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_580 = (let _146_579 = (FStar_Syntax_Syntax.as_arg g)
in (let _146_578 = (let _146_577 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _146_576 = (let _146_575 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_146_575)::[])
in (_146_577)::_146_576))
in (_146_579)::_146_578))
in (_146_581)::_146_580))
in (let _146_582 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _146_584 _146_583 None _146_582)))))
in (

let default_case = (

let post_k = (let _146_587 = (let _146_585 = (FStar_Syntax_Syntax.null_binder res_t)
in (_146_585)::[])
in (let _146_586 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _146_587 _146_586)))
in (

let kwp = (let _146_590 = (let _146_588 = (FStar_Syntax_Syntax.null_binder post_k)
in (_146_588)::[])
in (let _146_589 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _146_590 _146_589)))
in (

let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (

let wp = (let _146_596 = (let _146_591 = (FStar_Syntax_Syntax.mk_binder post)
in (_146_591)::[])
in (let _146_595 = (let _146_594 = (let _146_592 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Errors.exhaustiveness_check _146_592))
in (let _146_593 = (fvar_const env FStar_Syntax_Const.false_lid)
in (FStar_All.pipe_left _146_594 _146_593)))
in (FStar_Syntax_Util.abs _146_596 _146_595 (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md res_t wp []))))))
in (

let comp = (FStar_List.fold_right (fun _56_936 celse -> (match (_56_936) with
| (g, cthen) -> begin
(

let _56_952 = (let _146_599 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _146_599 celse))
in (match (_56_952) with
| ((md, _56_940, _56_942), (_56_945, wp_then), (_56_949, wp_else)) -> begin
(let _146_600 = (ifthenelse md res_t g wp_then wp_else)
in (mk_comp md res_t _146_600 []))
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

let wp = (let _146_605 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _146_604 = (let _146_603 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_602 = (let _146_601 = (FStar_Syntax_Syntax.as_arg wp)
in (_146_601)::[])
in (_146_603)::_146_602))
in (FStar_Syntax_Syntax.mk_Tm_app _146_605 _146_604 None wp.FStar_Syntax_Syntax.pos)))
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

let bs = (let _146_626 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_626)::[])
in (

let us = (let _146_628 = (let _146_627 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (_146_627)::[])
in (u_res)::_146_628)
in (

let wp = (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid))))
in (let _146_635 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (let _146_634 = (let _146_633 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _146_632 = (let _146_631 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _146_630 = (let _146_629 = (FStar_Syntax_Syntax.as_arg wp)
in (_146_629)::[])
in (_146_631)::_146_630))
in (_146_633)::_146_632))
in (FStar_Syntax_Syntax.mk_Tm_app _146_635 _146_634 None wp0.FStar_Syntax_Syntax.pos))))))) bvs wp0))
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
(let _146_646 = (let _146_645 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _146_644 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _146_645 _146_644)))
in (FStar_All.failwith _146_646))
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

let ret = (let _146_648 = (let _146_647 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _146_647 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_648))
in (

let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (

let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (

let c = (let _146_650 = (let _146_649 = (bind e.FStar_Syntax_Syntax.pos env None (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), eq_ret))
in (_146_649.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _146_650 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
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
(let _146_662 = (let _146_661 = (let _146_660 = (FStar_TypeChecker_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _146_659 = (FStar_TypeChecker_Env.get_range env)
in (_146_660, _146_659)))
in FStar_Syntax_Syntax.Error (_146_661))
in (Prims.raise _146_662))
end
| Some (g) -> begin
(e, c', g)
end))


let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match ((let _146_671 = (FStar_Syntax_Subst.compress t)
in _146_671.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_56_1017) -> begin
(match ((let _146_672 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _146_672.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid) -> begin
(

let _56_1021 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (

let b2t = (let _146_673 = (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar _146_673 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (

let lc = (let _146_676 = (let _146_675 = (let _146_674 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_674))
in (None, _146_675))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) lc _146_676))
in (

let e = (let _146_678 = (let _146_677 = (FStar_Syntax_Syntax.as_arg e)
in (_146_677)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _146_678 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (e, lc)))))
end
| _56_1027 -> begin
(e, lc)
end)
end
| _56_1029 -> begin
(e, lc)
end))


let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (

let gopt = if env.FStar_TypeChecker_Env.use_eq then begin
(let _146_687 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in (_146_687, false))
end else begin
(let _146_688 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in (_146_688, true))
end
in (match (gopt) with
| (None, _56_1037) -> begin
(FStar_TypeChecker_Rel.subtype_fail env lc.FStar_Syntax_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(match ((FStar_TypeChecker_Rel.guard_form g)) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let lc = (

let _56_1044 = lc
in {FStar_Syntax_Syntax.eff_name = _56_1044.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _56_1044.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _56_1044.FStar_Syntax_Syntax.comp})
in (e, lc, g))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let g = (

let _56_1049 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _56_1049.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_1049.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_1049.FStar_TypeChecker_Env.implicits})
in (

let strengthen = (fun _56_1053 -> (match (()) with
| () -> begin
(

let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (match ((let _146_691 = (FStar_Syntax_Subst.compress f)
in _146_691.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_56_1056, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _56_1062; FStar_Syntax_Syntax.pos = _56_1060; FStar_Syntax_Syntax.vars = _56_1058}, _56_1067) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
(

let lc = (

let _56_1070 = lc
in {FStar_Syntax_Syntax.eff_name = _56_1070.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _56_1070.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _56_1070.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| _56_1074 -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let _56_1076 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _146_695 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _146_694 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _146_693 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _146_692 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _146_695 _146_694 _146_693 _146_692)))))
end else begin
()
end
in (

let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _56_1081 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_56_1081) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env ct.FStar_Syntax_Syntax.effect_name)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in (

let xexp = (FStar_Syntax_Syntax.bv_to_name x)
in (

let us = (let _146_696 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_146_696)::[])
in (

let wp = (let _146_701 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ret)
in (let _146_700 = (let _146_699 = (FStar_Syntax_Syntax.as_arg t)
in (let _146_698 = (let _146_697 = (FStar_Syntax_Syntax.as_arg xexp)
in (_146_697)::[])
in (_146_699)::_146_698))
in (FStar_Syntax_Syntax.mk_Tm_app _146_701 _146_700 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)))
in (

let cret = (let _146_702 = (mk_comp md t wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_702))
in (

let guard = if apply_guard then begin
(let _146_704 = (let _146_703 = (FStar_Syntax_Syntax.as_arg xexp)
in (_146_703)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _146_704 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end else begin
f
end
in (

let _56_1092 = (let _146_712 = (FStar_All.pipe_left (fun _146_709 -> Some (_146_709)) (FStar_TypeChecker_Errors.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _146_711 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _146_710 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _146_712 _146_711 e cret _146_710))))
in (match (_56_1092) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x = (

let _56_1093 = x
in {FStar_Syntax_Syntax.ppname = _56_1093.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_1093.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (

let c = (let _146_714 = (let _146_713 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_713))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) _146_714 (Some (x), eq_ret)))
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let _56_1098 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _146_715 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _146_715))
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
| _56_1104 -> begin
[]
end))))
in (

let lc = (

let _56_1106 = lc
in (let _146_717 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _146_717; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (

let g = (

let _56_1109 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _56_1109.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_1109.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_1109.FStar_TypeChecker_Env.implicits})
in (e, lc, g))))))
end)
end)))


let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _146_729 = (let _146_728 = (let _146_727 = (let _146_726 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _146_726))
in (_146_727)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _146_728 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _146_729))))
in (

let norm = (fun t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Unlabel)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env t))
in if (FStar_Syntax_Util.is_tot_or_gtot_comp comp) then begin
(None, (FStar_Syntax_Util.comp_result comp))
end else begin
(match (comp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.GTotal (_)) | (FStar_Syntax_Syntax.Total (_)) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
if ((FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Pure_lid) || (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Ghost_lid)) then begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| ((req, _56_1137))::((ens, _56_1132))::_56_1129 -> begin
(let _146_735 = (let _146_732 = (norm req)
in Some (_146_732))
in (let _146_734 = (let _146_733 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _146_733))
in (_146_735, _146_734)))
end
| _56_1141 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(

let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| ((wp, _56_1147))::_56_1144 -> begin
(

let _56_1153 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (_56_1153) with
| (us_r, _56_1152) -> begin
(

let _56_1157 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (_56_1157) with
| (us_e, _56_1156) -> begin
(

let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (

let as_req = (let _146_737 = (let _146_736 = (FStar_Ident.set_lid_range FStar_Syntax_Const.as_requires r)
in (FStar_Syntax_Syntax.fvar _146_736 FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _146_737 us_r))
in (

let as_ens = (let _146_739 = (let _146_738 = (FStar_Ident.set_lid_range FStar_Syntax_Const.as_ensures r)
in (FStar_Syntax_Syntax.fvar _146_738 FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _146_739 us_e))
in (

let req = (let _146_742 = (let _146_741 = (let _146_740 = (FStar_Syntax_Syntax.as_arg wp)
in (_146_740)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.imp_tag)))::_146_741)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _146_742 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let ens = (let _146_745 = (let _146_744 = (let _146_743 = (FStar_Syntax_Syntax.as_arg wp)
in (_146_743)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.imp_tag)))::_146_744)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _146_745 None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _146_749 = (let _146_746 = (norm req)
in Some (_146_746))
in (let _146_748 = (let _146_747 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm _146_747))
in (_146_749, _146_748))))))))
end))
end))
end
| _56_1164 -> begin
(FStar_All.failwith "Impossible")
end))
end
end)
end)))


let maybe_instantiate : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let torig = (FStar_Syntax_Subst.compress t)
in if (not (env.FStar_TypeChecker_Env.instantiate_imp)) then begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end else begin
(match (torig.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _56_1175 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_56_1175) with
| (bs, c) -> begin
(

let rec aux = (fun subst _56_4 -> (match (_56_4) with
| ((x, Some (FStar_Syntax_Syntax.Implicit (dot))))::rest -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let _56_1191 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t)
in (match (_56_1191) with
| (v, _56_1189, g) -> begin
(

let subst = (FStar_Syntax_Syntax.NT ((x, v)))::subst
in (

let _56_1197 = (aux subst rest)
in (match (_56_1197) with
| (args, bs, subst, g') -> begin
(let _146_760 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((v, Some (FStar_Syntax_Syntax.Implicit (dot))))::args, bs, subst, _146_760))
end)))
end)))
end
| bs -> begin
([], bs, subst, FStar_TypeChecker_Rel.trivial_guard)
end))
in (

let _56_1203 = (aux [] bs)
in (match (_56_1203) with
| (args, bs, subst, guard) -> begin
(match ((args, bs)) with
| ([], _56_1206) -> begin
(e, torig, guard)
end
| (_56_1209, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end
| _56_1213 -> begin
(

let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _56_1216 -> begin
(FStar_Syntax_Util.arrow bs c)
end)
in (

let t = (FStar_Syntax_Subst.subst subst t)
in (

let e = (FStar_Syntax_Syntax.mk_Tm_app e args (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (e, t, guard))))
end)
end)))
end))
end
| _56_1221 -> begin
(e, t, FStar_TypeChecker_Rel.trivial_guard)
end)
end))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(

let s = (let _146_766 = (let _146_765 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _146_765))
in (FStar_All.pipe_right _146_766 FStar_Util.set_elements))
in (

let r = (let _146_767 = (FStar_TypeChecker_Env.get_range env)
in Some (_146_767))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (

let _56_1228 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _146_772 = (let _146_769 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _146_769))
in (let _146_771 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _146_770 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _146_772 _146_771 _146_770))))
end else begin
()
end
in (

let _56_1230 = (FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))))
in u_name))))))
in u_names)))
end)


let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (

let univs = (FStar_Syntax_Free.univs t)
in (

let _56_1238 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _146_781 = (let _146_780 = (let _146_779 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _146_779 (FStar_List.map (fun u -> (let _146_778 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _146_778 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _146_780 (FStar_String.concat ", ")))
in (FStar_Util.print1 "univs to gen : %s\n" _146_781))
end else begin
()
end
in (

let gen = (gen_univs env univs)
in (

let _56_1241 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _146_782 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _146_782))
end else begin
()
end
in (

let ts = (FStar_Syntax_Subst.close_univ_vars gen t)
in (gen, ts))))))))


let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> if (let _146_788 = (FStar_Util.for_all (fun _56_1249 -> (match (_56_1249) with
| (_56_1247, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _146_788)) then begin
None
end else begin
(

let norm = (fun c -> (

let _56_1252 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _146_791 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _146_791))
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

let _56_1255 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _146_792 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _146_792))
end else begin
()
end
in c))))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (let _146_795 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _146_795 FStar_Util.set_elements)))
in (

let _56_1272 = (let _146_797 = (FStar_All.pipe_right ecs (FStar_List.map (fun _56_1262 -> (match (_56_1262) with
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
in (univs, (uvs, e, c)))))))))
end))))
in (FStar_All.pipe_right _146_797 FStar_List.unzip))
in (match (_56_1272) with
| (univs, uvars) -> begin
(

let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (

let gen_univs = (gen_univs env univs)
in (

let _56_1276 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end else begin
()
end
in (

let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _56_1281 -> (match (_56_1281) with
| (uvs, e, c) -> begin
(

let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _56_1284 -> (match (_56_1284) with
| (u, k) -> begin
(match ((FStar_Unionfind.find u)) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(a, Some (FStar_Syntax_Syntax.imp_tag))
end
| FStar_Syntax_Syntax.Fixed (_56_1318) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _56_1321 -> begin
(

let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (

let _56_1325 = (FStar_Syntax_Util.arrow_formals k)
in (match (_56_1325) with
| (bs, kres) -> begin
(

let a = (let _146_803 = (let _146_802 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _146_801 -> Some (_146_801)) _146_802))
in (FStar_Syntax_Syntax.new_bv _146_803 kres))
in (

let t = (let _146_808 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _146_807 = (let _146_806 = (let _146_805 = (let _146_804 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _146_804))
in FStar_Util.Inl (_146_805))
in Some (_146_806))
in (FStar_Syntax_Util.abs bs _146_808 _146_807)))
in (

let _56_1328 = (FStar_Syntax_Util.set_uvar u t)
in (a, Some (FStar_Syntax_Syntax.imp_tag)))))
end)))
end)
end))))
in (

let _56_1352 = (match (tvars) with
| [] -> begin
(e, c)
end
| _56_1333 -> begin
(

let _56_1336 = (e, c)
in (match (_56_1336) with
| (e0, c0) -> begin
(

let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.BetaUVars)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::[]) env c)
in (

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.BetaUVars)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::[]) env e)
in (

let t = (match ((let _146_809 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _146_809.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(

let _56_1345 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (_56_1345) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| _56_1347 -> begin
(FStar_Syntax_Util.arrow tvars c)
end)
in (

let e' = (FStar_Syntax_Util.abs tvars e (Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp c)))))
in (let _146_810 = (FStar_Syntax_Syntax.mk_Total t)
in (e', _146_810))))))
end))
end)
in (match (_56_1352) with
| (e, c) -> begin
(gen_univs, e, c)
end)))
end))))
in Some (ecs)))))
end)))))
end)


let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> (

let _56_1362 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _146_817 = (let _146_816 = (FStar_List.map (fun _56_1361 -> (match (_56_1361) with
| (lb, _56_1358, _56_1360) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _146_816 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _146_817))
end else begin
()
end
in (match ((let _146_819 = (FStar_All.pipe_right lecs (FStar_List.map (fun _56_1368 -> (match (_56_1368) with
| (_56_1365, e, c) -> begin
(e, c)
end))))
in (gen env _146_819))) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun _56_1373 -> (match (_56_1373) with
| (l, t, c) -> begin
(l, [], t, c)
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _56_1381 _56_1385 -> (match ((_56_1381, _56_1385)) with
| ((l, _56_1378, _56_1380), (us, e, c)) -> begin
(

let _56_1386 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _146_825 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _146_824 = (FStar_Syntax_Print.lbname_to_string l)
in (let _146_823 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.print3 "(%s) Generalized %s to %s\n" _146_825 _146_824 _146_823))))
end else begin
()
end
in (l, us, e, c))
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
(let _146_841 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _146_840 -> Some (_146_840)) _146_841))
end)
end)
in (

let is_var = (fun e -> (match ((let _146_844 = (FStar_Syntax_Subst.compress e)
in _146_844.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (_56_1403) -> begin
true
end
| _56_1406 -> begin
false
end))
in (

let decorate = (fun e t -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((

let _56_1413 = x
in {FStar_Syntax_Syntax.ppname = _56_1413.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_1413.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| _56_1416 -> begin
(

let _56_1417 = e
in (let _146_849 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _56_1417.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _146_849; FStar_Syntax_Syntax.pos = _56_1417.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _56_1417.FStar_Syntax_Syntax.vars}))
end)))
in (

let env = (

let _56_1419 = env
in (let _146_850 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _56_1419.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _56_1419.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _56_1419.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _56_1419.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _56_1419.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _56_1419.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _56_1419.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _56_1419.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _56_1419.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _56_1419.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _56_1419.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _56_1419.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _56_1419.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _56_1419.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _56_1419.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _146_850; FStar_TypeChecker_Env.is_iface = _56_1419.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _56_1419.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _56_1419.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _56_1419.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _56_1419.FStar_TypeChecker_Env.use_bv_sorts}))
in (match ((check env t1 t2)) with
| None -> begin
(let _146_854 = (let _146_853 = (let _146_852 = (FStar_TypeChecker_Errors.expected_expression_of_type env t2 e t1)
in (let _146_851 = (FStar_TypeChecker_Env.get_range env)
in (_146_852, _146_851)))
in FStar_Syntax_Syntax.Error (_146_853))
in (Prims.raise _146_854))
end
| Some (g) -> begin
(

let _56_1425 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _146_855 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _146_855))
end else begin
()
end
in (let _146_856 = (decorate e t2)
in (_146_856, g)))
end)))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (

let discharge = (fun g -> (

let _56_1432 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _146_866 = (discharge g)
in (let _146_865 = (lc.FStar_Syntax_Syntax.comp ())
in (_146_866, _146_865)))
end else begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let steps = (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.DeltaComp)::[]
in (

let c = (let _146_869 = (let _146_868 = (let _146_867 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (FStar_All.pipe_right _146_867 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right _146_868 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (FStar_All.pipe_right _146_869 FStar_Syntax_Util.comp_to_comp_typ))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let _56_1441 = (destruct_comp c)
in (match (_56_1441) with
| (t, wp) -> begin
(

let vc = (let _146_877 = (let _146_871 = (let _146_870 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_146_870)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _146_871 env md md.FStar_Syntax_Syntax.trivial))
in (let _146_876 = (let _146_874 = (FStar_Syntax_Syntax.as_arg t)
in (let _146_873 = (let _146_872 = (FStar_Syntax_Syntax.as_arg wp)
in (_146_872)::[])
in (_146_874)::_146_873))
in (let _146_875 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk_Tm_app _146_877 _146_876 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _146_875))))
in (

let _56_1443 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _146_878 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _146_878))
end else begin
()
end
in (

let g = (let _146_879 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _146_879))
in (let _146_881 = (discharge g)
in (let _146_880 = (FStar_Syntax_Syntax.mk_Comp c)
in (_146_881, _146_880))))))
end))))))
end)))


let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (

let short_bin_op = (fun f _56_5 -> (match (_56_5) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((fst, _56_1454))::[] -> begin
(f fst)
end
| _56_1458 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (

let op_and_e = (fun e -> (let _146_902 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _146_902 (fun _146_901 -> FStar_TypeChecker_Common.NonTrivial (_146_901)))))
in (

let op_or_e = (fun e -> (let _146_907 = (let _146_905 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _146_905))
in (FStar_All.pipe_right _146_907 (fun _146_906 -> FStar_TypeChecker_Common.NonTrivial (_146_906)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _146_910 -> FStar_TypeChecker_Common.NonTrivial (_146_910))))
in (

let op_or_t = (fun t -> (let _146_914 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _146_914 (fun _146_913 -> FStar_TypeChecker_Common.NonTrivial (_146_913)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _146_917 -> FStar_TypeChecker_Common.NonTrivial (_146_917))))
in (

let short_op_ite = (fun _56_6 -> (match (_56_6) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| ((guard, _56_1473))::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| (_then)::((guard, _56_1478))::[] -> begin
(let _146_921 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _146_921 (fun _146_920 -> FStar_TypeChecker_Common.NonTrivial (_146_920))))
end
| _56_1483 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (

let table = ((FStar_Syntax_Const.op_And, (short_bin_op op_and_e)))::((FStar_Syntax_Const.op_Or, (short_bin_op op_or_e)))::((FStar_Syntax_Const.and_lid, (short_bin_op op_and_t)))::((FStar_Syntax_Const.or_lid, (short_bin_op op_or_t)))::((FStar_Syntax_Const.imp_lid, (short_bin_op op_imp_t)))::((FStar_Syntax_Const.ite_lid, short_op_ite))::[]
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((FStar_Util.find_map table (fun _56_1491 -> (match (_56_1491) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _146_954 = (mk seen_args)
in Some (_146_954))
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
| _56_1496 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (match ((let _146_957 = (FStar_Syntax_Util.un_uinst l)
in _146_957.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| _56_1501 -> begin
false
end))


let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (

let pos = (fun bs -> (match (bs) with
| ((hd, _56_1510))::_56_1507 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| _56_1514 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| ((_56_1518, Some (FStar_Syntax_Syntax.Implicit (_56_1520))))::_56_1516 -> begin
bs
end
| _56_1526 -> begin
(match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
bs
end
| Some (t) -> begin
(match ((let _146_964 = (FStar_Syntax_Subst.compress t)
in _146_964.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', _56_1532) -> begin
(match ((FStar_Util.prefix_until (fun _56_7 -> (match (_56_7) with
| (_56_1537, Some (FStar_Syntax_Syntax.Implicit (_56_1539))) -> begin
false
end
| _56_1544 -> begin
true
end)) bs')) with
| None -> begin
bs
end
| Some ([], _56_1548, _56_1550) -> begin
bs
end
| Some (imps, _56_1555, _56_1557) -> begin
if (FStar_All.pipe_right imps (FStar_Util.for_all (fun _56_1563 -> (match (_56_1563) with
| (x, _56_1562) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end)))) then begin
(

let r = (pos bs)
in (

let imps = (FStar_All.pipe_right imps (FStar_List.map (fun _56_1567 -> (match (_56_1567) with
| (x, i) -> begin
(let _146_968 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in (_146_968, i))
end))))
in (FStar_List.append imps bs)))
end else begin
bs
end
end)
end
| _56_1570 -> begin
bs
end)
end)
end)))


let maybe_lift : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env e c1 c2 -> (

let m1 = (FStar_TypeChecker_Env.norm_eff_name env c1)
in (

let m2 = (FStar_TypeChecker_Env.norm_eff_name env c2)
in if (FStar_Ident.lid_equals m1 m2) then begin
e
end else begin
(let _146_977 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_monadic_lift ((m1, m2))))) _146_977 e.FStar_Syntax_Syntax.pos))
end)))


let maybe_monadic : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env e c -> (

let m = (FStar_TypeChecker_Env.norm_eff_name env c)
in if (((is_pure_or_ghost_effect env m) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_Tot_lid)) || (FStar_Ident.lid_equals m FStar_Syntax_Const.effect_GTot_lid)) then begin
e
end else begin
(let _146_984 = (FStar_ST.read e.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_monadic (m)))) _146_984 e.FStar_Syntax_Syntax.pos))
end))




