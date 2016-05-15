
open Prims

type lcomp_with_binder =
(FStar_Syntax_Syntax.bv Prims.option * FStar_Syntax_Syntax.lcomp)


let report : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  Prims.unit = (fun env errs -> (let _145_6 = (FStar_TypeChecker_Env.get_range env)
in (let _145_5 = (FStar_TypeChecker_Errors.failed_to_prove_specification errs)
in (FStar_TypeChecker_Errors.report _145_6 _145_5))))


let is_type : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _145_9 = (FStar_Syntax_Subst.compress t)
in _145_9.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_56_12) -> begin
true
end
| _56_15 -> begin
false
end))


let t_binders : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env -> (let _145_13 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_All.pipe_right _145_13 (FStar_List.filter (fun _56_20 -> (match (_56_20) with
| (x, _56_19) -> begin
(is_type x.FStar_Syntax_Syntax.sort)
end))))))


let new_uvar_aux : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun env k -> (

let bs = if ((FStar_Options.full_context_dependency ()) || (let _145_18 = (FStar_TypeChecker_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _145_18))) then begin
(FStar_TypeChecker_Env.all_binders env)
end else begin
(t_binders env)
end
in (let _145_19 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Rel.new_uvar _145_19 bs k))))


let new_uvar : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env k -> (let _145_24 = (new_uvar_aux env k)
in (Prims.fst _145_24)))


let as_uvar : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.uvar = (fun _56_1 -> (match (_56_1) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, _56_35); FStar_Syntax_Syntax.tk = _56_32; FStar_Syntax_Syntax.pos = _56_30; FStar_Syntax_Syntax.vars = _56_28} -> begin
uv
end
| _56_40 -> begin
(FStar_All.failwith "Impossible")
end))


let new_implicit_var : Prims.string  ->  FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.uvar * FStar_Range.range) Prims.list * FStar_TypeChecker_Env.guard_t) = (fun reason r env k -> (match ((FStar_Syntax_Util.destruct k FStar_Syntax_Const.range_of_lid)) with
| Some (_56_50::(tm, _56_47)::[]) -> begin
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
in (let _145_37 = (let _145_36 = (let _145_35 = (as_uvar u)
in (reason, env, _145_35, t, k, r))
in (_145_36)::[])
in {FStar_TypeChecker_Env.guard_f = _56_59.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _56_59.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_59.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _145_37}))
in (let _145_40 = (let _145_39 = (let _145_38 = (as_uvar u)
in (_145_38, r))
in (_145_39)::[])
in (t, _145_40, g)))
end))
end))


let check_uvars : FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun r t -> (

let uvs = (FStar_Syntax_Free.uvars t)
in if (not ((FStar_Util.set_is_empty uvs))) then begin
(

let us = (let _145_47 = (let _145_46 = (FStar_Util.set_elements uvs)
in (FStar_List.map (fun _56_68 -> (match (_56_68) with
| (x, _56_67) -> begin
(FStar_Syntax_Print.uvar_to_string x)
end)) _145_46))
in (FStar_All.pipe_right _145_47 (FStar_String.concat ", ")))
in (

let _56_70 = (FStar_Options.push ())
in (

let _56_72 = (FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool (false)))
in (

let _56_74 = (FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)))
in (

let _56_76 = (let _145_49 = (let _145_48 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Unconstrained unification variables %s in type signature %s; please add an annotation" us _145_48))
in (FStar_TypeChecker_Errors.report r _145_49))
in (FStar_Options.pop ()))))))
end else begin
()
end))


let force_sort' : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' = (fun s -> (match ((FStar_ST.read s.FStar_Syntax_Syntax.tk)) with
| None -> begin
(let _145_54 = (let _145_53 = (FStar_Range.string_of_range s.FStar_Syntax_Syntax.pos)
in (let _145_52 = (FStar_Syntax_Print.term_to_string s)
in (FStar_Util.format2 "(%s) Impossible: Forced tk not present on %s" _145_53 _145_52)))
in (FStar_All.failwith _145_54))
end
| Some (tk) -> begin
tk
end))


let force_sort = (fun s -> (let _145_56 = (force_sort' s)
in (FStar_Syntax_Syntax.mk _145_56 None s.FStar_Syntax_Syntax.pos)))


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

let mk_binder = (fun scope a -> (match (a.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _56_105 = (FStar_Syntax_Util.type_u ())
in (match (_56_105) with
| (k, _56_104) -> begin
(

let t = (let _145_65 = (FStar_TypeChecker_Rel.new_uvar e.FStar_Syntax_Syntax.pos scope k)
in (FStar_All.pipe_right _145_65 Prims.fst))
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
(let _145_73 = (FStar_Range.string_of_range r)
in (let _145_72 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Using type %s\n" _145_73 _145_72)))
end else begin
()
end
in (FStar_Util.Inl (t), (check_res || check)))))
end))
end))
end
| _56_161 -> begin
(let _145_76 = (let _145_75 = (let _145_74 = (FStar_TypeChecker_Rel.new_uvar r vars FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _145_74 Prims.fst))
in FStar_Util.Inl (_145_75))
in (_145_76, false))
end)))
in (

let _56_164 = (let _145_77 = (t_binders env)
in (aux _145_77 e))
in (match (_56_164) with
| (t, b) -> begin
(

let t = (match (t) with
| FStar_Util.Inr (c) -> begin
(let _145_81 = (let _145_80 = (let _145_79 = (let _145_78 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.format1 "Expected a \'let rec\' to be annotated with a value type; got a computation type %s" _145_78))
in (_145_79, rng))
in FStar_Syntax_Syntax.Error (_145_80))
in (Prims.raise _145_81))
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

let _56_200 = (let _145_94 = (FStar_TypeChecker_Env.all_binders env)
in (FStar_TypeChecker_Rel.new_uvar p.FStar_Syntax_Syntax.p _145_94 t))
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
in (let _145_95 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _56_210.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_210.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_95}))
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
in (let _145_96 = (new_uvar env t)
in {FStar_Syntax_Syntax.ppname = _56_221.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_221.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_96}))
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

let e = (let _145_103 = (let _145_102 = (let _145_101 = (let _145_100 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (let _145_99 = (FStar_All.pipe_right args FStar_List.rev)
in (FStar_Syntax_Syntax.mk_Tm_app _145_100 _145_99 None p.FStar_Syntax_Syntax.p)))
in (_145_101, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))
in FStar_Syntax_Syntax.Tm_meta (_145_102))
in (FStar_Syntax_Syntax.mk _145_103 None p.FStar_Syntax_Syntax.p))
in (let _145_106 = (FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten)
in (let _145_105 = (FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten)
in (let _145_104 = (FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten)
in (_145_106, _145_105, _145_104, env, e, (

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
(let _145_118 = (elaborate_pat env p)
in (_145_118, imp))
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
| ([], _56_294::_56_292) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Too many pattern arguments", (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))))
end
| (_56_300::_56_298, []) -> begin
(FStar_All.pipe_right formals (FStar_List.map (fun _56_306 -> (match (_56_306) with
| (t, imp) -> begin
(match (imp) with
| Some (FStar_Syntax_Syntax.Implicit (inaccessible)) -> begin
(

let a = (let _145_125 = (let _145_124 = (FStar_Syntax_Syntax.range_of_bv t)
in Some (_145_124))
in (FStar_Syntax_Syntax.new_bv _145_125 FStar_Syntax_Syntax.tun))
in (

let r = (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (let _145_126 = (maybe_dot inaccessible a r)
in (_145_126, true))))
end
| _56_313 -> begin
(let _145_130 = (let _145_129 = (let _145_128 = (let _145_127 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.format1 "Insufficient pattern arguments (%s)" _145_127))
in (_145_128, (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in FStar_Syntax_Syntax.Error (_145_129))
in (Prims.raise _145_130))
end)
end))))
end
| (f::formals', (p, p_imp)::pats') -> begin
(match (f) with
| (_56_324, Some (FStar_Syntax_Syntax.Implicit (_56_326))) when p_imp -> begin
(let _145_131 = (aux formals' pats')
in ((p, true))::_145_131)
end
| (_56_331, Some (FStar_Syntax_Syntax.Implicit (inaccessible))) -> begin
(

let a = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) FStar_Syntax_Syntax.tun)
in (

let p = (maybe_dot inaccessible a (FStar_Ident.range_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))
in (let _145_132 = (aux formals' pats)
in ((p, true))::_145_132)))
end
| (_56_339, imp) -> begin
(let _145_135 = (let _145_133 = (FStar_Syntax_Syntax.is_implicit imp)
in (p, _145_133))
in (let _145_134 = (aux formals' pats')
in (_145_135)::_145_134))
end)
end))
in (

let _56_342 = p
in (let _145_138 = (let _145_137 = (let _145_136 = (aux f pats)
in (fv, _145_136))
in FStar_Syntax_Syntax.Pat_cons (_145_137))
in {FStar_Syntax_Syntax.v = _145_138; FStar_Syntax_Syntax.ty = _56_342.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_342.FStar_Syntax_Syntax.p})))
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
(let _145_147 = (let _145_146 = (let _145_145 = (FStar_TypeChecker_Errors.nonlinear_pattern_variable x)
in (_145_145, p.FStar_Syntax_Syntax.p))
in FStar_Syntax_Syntax.Error (_145_146))
in (Prims.raise _145_147))
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
| FStar_Syntax_Syntax.Pat_disj (q::pats) -> begin
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
(let _145_157 = (let _145_156 = (let _145_155 = (FStar_TypeChecker_Errors.disjunctive_pattern_vars a a')
in (let _145_154 = (FStar_TypeChecker_Env.get_range env)
in (_145_155, _145_154)))
in FStar_Syntax_Syntax.Error (_145_156))
in (Prims.raise _145_157))
end else begin
(let _145_159 = (let _145_158 = (FStar_Syntax_Syntax.as_arg arg)
in (_145_158)::args)
in ((FStar_List.append w' w), _145_159, (p)::pats))
end
end))
end)) pats ([], [], []))
in (match (_56_392) with
| (w, args, pats) -> begin
(let _145_161 = (let _145_160 = (FStar_Syntax_Syntax.as_arg te)
in (_145_160)::args)
in ((FStar_List.append b w), _145_161, (

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
(let _145_163 = (let _145_162 = (FStar_Syntax_Syntax.as_arg arg)
in (_145_162)::[])
in (b, _145_163, p))
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
(let _145_178 = (force_sort' e)
in (pkg p.FStar_Syntax_Syntax.v _145_178))
end
| (FStar_Syntax_Syntax.Pat_var (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
(

let _56_441 = if (not ((FStar_Syntax_Syntax.bv_eq x y))) then begin
(let _145_181 = (let _145_180 = (FStar_Syntax_Print.bv_to_string x)
in (let _145_179 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _145_180 _145_179)))
in (FStar_All.failwith _145_181))
end else begin
()
end
in (

let _56_443 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Pat"))) then begin
(let _145_183 = (FStar_Syntax_Print.bv_to_string x)
in (let _145_182 = (FStar_TypeChecker_Normalize.term_to_string env y.FStar_Syntax_Syntax.sort)
in (FStar_Util.print2 "Pattern variable %s introduced at type %s\n" _145_183 _145_182)))
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
(let _145_186 = (let _145_185 = (FStar_Syntax_Print.bv_to_string x)
in (let _145_184 = (FStar_Syntax_Print.bv_to_string y)
in (FStar_Util.format2 "Expected pattern variable %s; got %s" _145_185 _145_184)))
in (FStar_All.failwith _145_186))
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
(let _145_187 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _145_187))
end else begin
()
end
in (let _145_188 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv', []))) _145_188)))
end
| ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) | ((FStar_Syntax_Syntax.Pat_cons (fv, argpats), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv'); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args))) -> begin
(

let _56_522 = if (let _145_189 = (FStar_Syntax_Syntax.fv_eq fv fv')
in (FStar_All.pipe_right _145_189 Prims.op_Negation)) then begin
(let _145_190 = (FStar_Util.format2 "Expected pattern constructor %s; got %s" fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str fv'.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (FStar_All.failwith _145_190))
end else begin
()
end
in (

let fv = fv'
in (

let rec match_args = (fun matched_pats args argpats -> (match ((args, argpats)) with
| ([], []) -> begin
(let _145_197 = (force_sort' e)
in (pkg (FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev matched_pats)))) _145_197))
end
| (arg::args, (argpat, _56_538)::argpats) -> begin
(match ((arg, argpat.FStar_Syntax_Syntax.v)) with
| ((e, Some (FStar_Syntax_Syntax.Implicit (true))), FStar_Syntax_Syntax.Pat_dot_term (_56_548)) -> begin
(

let x = (let _145_198 = (force_sort e)
in (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Syntax_Syntax.p)) _145_198))
in (

let q = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_dot_term ((x, e))) x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p)
in (match_args (((q, true))::matched_pats) args argpats)))
end
| ((e, imp), _56_557) -> begin
(

let pat = (let _145_200 = (aux argpat e)
in (let _145_199 = (FStar_Syntax_Syntax.is_implicit imp)
in (_145_200, _145_199)))
in (match_args ((pat)::matched_pats) args argpats))
end)
end
| _56_561 -> begin
(let _145_203 = (let _145_202 = (FStar_Syntax_Print.pat_to_string p)
in (let _145_201 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected number of pattern arguments: \n\t%s\n\t%s\n" _145_202 _145_201)))
in (FStar_All.failwith _145_203))
end))
in (match_args [] args argpats))))
end
| _56_563 -> begin
(let _145_208 = (let _145_207 = (FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p)
in (let _145_206 = (FStar_Syntax_Print.pat_to_string qq)
in (let _145_205 = (let _145_204 = (FStar_All.pipe_right exps (FStar_List.map FStar_Syntax_Print.term_to_string))
in (FStar_All.pipe_right _145_204 (FStar_String.concat "\n\t")))
in (FStar_Util.format3 "(%s) Impossible: pattern to decorate is %s; expression is %s\n" _145_207 _145_206 _145_205))))
in (FStar_All.failwith _145_208))
end))))
in (match ((p.FStar_Syntax_Syntax.v, exps)) with
| (FStar_Syntax_Syntax.Pat_disj (ps), _56_567) when ((FStar_List.length ps) = (FStar_List.length exps)) -> begin
(

let ps = (FStar_List.map2 aux ps exps)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_disj (ps)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Syntax_Syntax.p))
end
| (_56_571, e::[]) -> begin
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
(let _145_216 = (let _145_215 = (FStar_Syntax_Syntax.as_implicit i)
in (te, _145_215))
in (vars, _145_216))
end))
end))
in (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_56_589) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _145_217 = (mk (FStar_Syntax_Syntax.Tm_constant (c)))
in ([], _145_217))
end
| (FStar_Syntax_Syntax.Pat_wild (x)) | (FStar_Syntax_Syntax.Pat_var (x)) -> begin
(let _145_218 = (mk (FStar_Syntax_Syntax.Tm_name (x)))
in ((x)::[], _145_218))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _56_602 = (let _145_219 = (FStar_All.pipe_right pats (FStar_List.map pat_as_arg))
in (FStar_All.pipe_right _145_219 FStar_List.unzip))
in (match (_56_602) with
| (vars, args) -> begin
(

let vars = (FStar_List.flatten vars)
in (let _145_223 = (let _145_222 = (let _145_221 = (let _145_220 = (FStar_Syntax_Syntax.fv_to_tm fv)
in (_145_220, args))
in FStar_Syntax_Syntax.Tm_app (_145_221))
in (mk _145_222))
in (vars, _145_223)))
end))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, e) -> begin
([], e)
end)))))


let destruct_comp : FStar_Syntax_Syntax.comp_typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun c -> (

let _56_626 = (match (c.FStar_Syntax_Syntax.effect_args) with
| (wp, _56_615)::(wlp, _56_611)::[] -> begin
(wp, wlp)
end
| _56_619 -> begin
(let _145_229 = (let _145_228 = (let _145_227 = (FStar_List.map (fun _56_623 -> (match (_56_623) with
| (x, _56_622) -> begin
(FStar_Syntax_Print.term_to_string x)
end)) c.FStar_Syntax_Syntax.effect_args)
in (FStar_All.pipe_right _145_227 (FStar_String.concat ", ")))
in (FStar_Util.format2 "Impossible: Got a computation %s with effect args [%s]" c.FStar_Syntax_Syntax.effect_name.FStar_Ident.str _145_228))
in (FStar_All.failwith _145_229))
end)
in (match (_56_626) with
| (wp, wlp) -> begin
(c.FStar_Syntax_Syntax.result_typ, wp, wlp)
end)))


let lift_comp : FStar_Syntax_Syntax.comp_typ  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.comp_typ = (fun c m lift -> (

let _56_634 = (destruct_comp c)
in (match (_56_634) with
| (_56_631, wp, wlp) -> begin
(let _145_251 = (let _145_250 = (let _145_246 = (lift c.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _145_246))
in (let _145_249 = (let _145_248 = (let _145_247 = (lift c.FStar_Syntax_Syntax.result_typ wlp)
in (FStar_Syntax_Syntax.as_arg _145_247))
in (_145_248)::[])
in (_145_250)::_145_249))
in {FStar_Syntax_Syntax.effect_name = m; FStar_Syntax_Syntax.result_typ = c.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _145_251; FStar_Syntax_Syntax.flags = []})
end)))


let join_effects : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env l1 l2 -> (

let _56_643 = (let _145_259 = (FStar_TypeChecker_Env.norm_eff_name env l1)
in (let _145_258 = (FStar_TypeChecker_Env.norm_eff_name env l2)
in (FStar_TypeChecker_Env.join env _145_259 _145_258)))
in (match (_56_643) with
| (m, _56_640, _56_642) -> begin
m
end)))


let join_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Ident.lident = (fun env c1 c2 -> if ((FStar_Syntax_Util.is_total_lcomp c1) && (FStar_Syntax_Util.is_total_lcomp c2)) then begin
FStar_Syntax_Const.effect_Tot_lid
end else begin
(join_effects env c1.FStar_Syntax_Syntax.eff_name c2.FStar_Syntax_Syntax.eff_name)
end)


let lift_and_destruct : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  ((FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)) = (fun env c1 c2 -> (

let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (

let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (

let _56_655 = (FStar_TypeChecker_Env.join env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)
in (match (_56_655) with
| (m, lift1, lift2) -> begin
(

let m1 = (lift_comp c1 m lift1)
in (

let m2 = (lift_comp c2 m lift2)
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env m)
in (

let _56_661 = (FStar_TypeChecker_Env.wp_signature env md.FStar_Syntax_Syntax.mname)
in (match (_56_661) with
| (a, kwp) -> begin
(let _145_273 = (destruct_comp m1)
in (let _145_272 = (destruct_comp m2)
in ((md, a, kwp), _145_273, _145_272)))
end)))))
end)))))


let is_pure_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)))


let is_pure_or_ghost_effect : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let l = (FStar_TypeChecker_Env.norm_eff_name env l)
in ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid))))


let mk_comp : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun md result wp wlp flags -> (let _145_296 = (let _145_295 = (let _145_294 = (FStar_Syntax_Syntax.as_arg wp)
in (let _145_293 = (let _145_292 = (FStar_Syntax_Syntax.as_arg wlp)
in (_145_292)::[])
in (_145_294)::_145_293))
in {FStar_Syntax_Syntax.effect_name = md.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = result; FStar_Syntax_Syntax.effect_args = _145_295; FStar_Syntax_Syntax.flags = flags})
in (FStar_Syntax_Syntax.mk_Comp _145_296)))


let subst_lcomp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun subst lc -> (

let _56_675 = lc
in (let _145_303 = (FStar_Syntax_Subst.subst subst lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _56_675.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _145_303; FStar_Syntax_Syntax.cflags = _56_675.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _56_677 -> (match (()) with
| () -> begin
(let _145_302 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp subst _145_302))
end))})))


let is_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _145_306 = (FStar_Syntax_Subst.compress t)
in _145_306.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_56_680) -> begin
true
end
| _56_683 -> begin
false
end))


let return_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t v -> (

let c = if (let _145_313 = (FStar_TypeChecker_Env.lid_exists env FStar_Syntax_Const.effect_GTot_lid)
in (FStar_All.pipe_left Prims.op_Negation _145_313)) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(

let m = (let _145_314 = (FStar_TypeChecker_Env.effect_decl_opt env FStar_Syntax_Const.effect_PURE_lid)
in (FStar_Util.must _145_314))
in (

let _56_690 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_56_690) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (

let wp = (let _145_322 = (let _145_321 = (let _145_316 = (let _145_315 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_145_315)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _145_316 env m m.FStar_Syntax_Syntax.ret))
in (let _145_320 = (let _145_319 = (FStar_Syntax_Syntax.as_arg t)
in (let _145_318 = (let _145_317 = (FStar_Syntax_Syntax.as_arg v)
in (_145_317)::[])
in (_145_319)::_145_318))
in (FStar_Syntax_Syntax.mk_Tm_app _145_321 _145_320 (Some (k.FStar_Syntax_Syntax.n)) v.FStar_Syntax_Syntax.pos)))
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env _145_322))
in (

let wlp = wp
in (mk_comp m t wp wlp ((FStar_Syntax_Syntax.RETURN)::[])))))
end)))
end
in (

let _56_695 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Return"))) then begin
(let _145_325 = (FStar_Range.string_of_range v.FStar_Syntax_Syntax.pos)
in (let _145_324 = (FStar_Syntax_Print.term_to_string v)
in (let _145_323 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print3 "(%s) returning %s at comp type %s\n" _145_325 _145_324 _145_323))))
end else begin
()
end
in c)))


let bind : FStar_Range.range  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.lcomp  ->  lcomp_with_binder  ->  FStar_Syntax_Syntax.lcomp = (fun r1 env e1opt lc1 _56_703 -> (match (_56_703) with
| (b, lc2) -> begin
(

let _56_711 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(

let bstr = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _145_338 = (match (e1opt) with
| None -> begin
"None"
end
| Some (e) -> begin
(FStar_Syntax_Print.term_to_string e)
end)
in (let _145_337 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _145_336 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (FStar_Util.print4 "Before lift: Making bind (e1=%s)@c1=%s\nb=%s\t\tc2=%s\n" _145_338 _145_337 bstr _145_336)))))
end else begin
()
end
in (

let bind_it = (fun _56_714 -> (match (()) with
| () -> begin
(

let c1 = (lc1.FStar_Syntax_Syntax.comp ())
in (

let c2 = (lc2.FStar_Syntax_Syntax.comp ())
in (

let _56_720 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _145_345 = (match (b) with
| None -> begin
"none"
end
| Some (x) -> begin
(FStar_Syntax_Print.bv_to_string x)
end)
in (let _145_344 = (FStar_Syntax_Print.lcomp_to_string lc1)
in (let _145_343 = (FStar_Syntax_Print.comp_to_string c1)
in (let _145_342 = (FStar_Syntax_Print.lcomp_to_string lc2)
in (let _145_341 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print5 "b=%s,Evaluated %s to %s\n And %s to %s\n" _145_345 _145_344 _145_343 _145_342 _145_341))))))
end else begin
()
end
in (

let try_simplify = (fun _56_723 -> (match (()) with
| () -> begin
(

let aux = (fun _56_725 -> (match (()) with
| () -> begin
if (FStar_Syntax_Util.is_trivial_wp c1) then begin
(match (b) with
| None -> begin
Some ((c2, "trivial no binder"))
end
| Some (_56_728) -> begin
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
(let _145_353 = (let _145_352 = (FStar_Syntax_Subst.subst_comp ((FStar_Syntax_Syntax.NT ((x, e)))::[]) c2)
in (_145_352, reason))
in Some (_145_353))
end
| _56_738 -> begin
(aux ())
end))
in if ((FStar_Syntax_Util.is_total_comp c1) && (FStar_Syntax_Util.is_total_comp c2)) then begin
(subst_c2 "both total")
end else begin
if ((FStar_Syntax_Util.is_tot_or_gtot_comp c1) && (FStar_Syntax_Util.is_tot_or_gtot_comp c2)) then begin
(let _145_355 = (let _145_354 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c2))
in (_145_354, "both gtot"))
in Some (_145_355))
end else begin
(match ((e1opt, b)) with
| (Some (e), Some (x)) -> begin
if ((FStar_Syntax_Util.is_total_comp c1) && (not ((FStar_Syntax_Syntax.is_null_bv x)))) then begin
(subst_c2 "substituted e")
end else begin
(aux ())
end
end
| _56_745 -> begin
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

let _56_763 = (lift_and_destruct env c1 c2)
in (match (_56_763) with
| ((md, a, kwp), (t1, wp1, wlp1), (t2, wp2, wlp2)) -> begin
(

let bs = (match (b) with
| None -> begin
(let _145_356 = (FStar_Syntax_Syntax.null_binder t1)
in (_145_356)::[])
end
| Some (x) -> begin
(let _145_357 = (FStar_Syntax_Syntax.mk_binder x)
in (_145_357)::[])
end)
in (

let mk_lam = (fun wp -> (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid)))))
in (

let r1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1))) None r1)
in (

let wp_args = (let _145_374 = (FStar_Syntax_Syntax.as_arg r1)
in (let _145_373 = (let _145_372 = (FStar_Syntax_Syntax.as_arg t1)
in (let _145_371 = (let _145_370 = (FStar_Syntax_Syntax.as_arg t2)
in (let _145_369 = (let _145_368 = (FStar_Syntax_Syntax.as_arg wp1)
in (let _145_367 = (let _145_366 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _145_365 = (let _145_364 = (let _145_360 = (mk_lam wp2)
in (FStar_Syntax_Syntax.as_arg _145_360))
in (let _145_363 = (let _145_362 = (let _145_361 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _145_361))
in (_145_362)::[])
in (_145_364)::_145_363))
in (_145_366)::_145_365))
in (_145_368)::_145_367))
in (_145_370)::_145_369))
in (_145_372)::_145_371))
in (_145_374)::_145_373))
in (

let wlp_args = (let _145_384 = (FStar_Syntax_Syntax.as_arg r1)
in (let _145_383 = (let _145_382 = (FStar_Syntax_Syntax.as_arg t1)
in (let _145_381 = (let _145_380 = (FStar_Syntax_Syntax.as_arg t2)
in (let _145_379 = (let _145_378 = (FStar_Syntax_Syntax.as_arg wlp1)
in (let _145_377 = (let _145_376 = (let _145_375 = (mk_lam wlp2)
in (FStar_Syntax_Syntax.as_arg _145_375))
in (_145_376)::[])
in (_145_378)::_145_377))
in (_145_380)::_145_379))
in (_145_382)::_145_381))
in (_145_384)::_145_383))
in (

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t2)))::[]) kwp)
in (

let us = (let _145_387 = (env.FStar_TypeChecker_Env.universe_of env t1)
in (let _145_386 = (let _145_385 = (env.FStar_TypeChecker_Env.universe_of env t2)
in (_145_385)::[])
in (_145_387)::_145_386))
in (

let wp = (let _145_388 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wp)
in (FStar_Syntax_Syntax.mk_Tm_app _145_388 wp_args None t2.FStar_Syntax_Syntax.pos))
in (

let wlp = (let _145_389 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.bind_wlp)
in (FStar_Syntax_Syntax.mk_Tm_app _145_389 wlp_args None t2.FStar_Syntax_Syntax.pos))
in (

let c = (mk_comp md t2 wp wlp [])
in c))))))))))
end))
end)))))
end))
in (let _145_390 = (join_lcomp env lc1 lc2)
in {FStar_Syntax_Syntax.eff_name = _145_390; FStar_Syntax_Syntax.res_typ = lc2.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_it})))
end))


let lift_formula : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env t mk_wp mk_wlp f -> (

let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (

let _56_786 = (FStar_TypeChecker_Env.wp_signature env md_pure.FStar_Syntax_Syntax.mname)
in (match (_56_786) with
| (a, kwp) -> begin
(

let k = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((a, t)))::[]) kwp)
in (

let wp = (let _145_404 = (let _145_403 = (FStar_Syntax_Syntax.as_arg t)
in (let _145_402 = (let _145_401 = (FStar_Syntax_Syntax.as_arg f)
in (_145_401)::[])
in (_145_403)::_145_402))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wp _145_404 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (

let wlp = (let _145_408 = (let _145_407 = (FStar_Syntax_Syntax.as_arg t)
in (let _145_406 = (let _145_405 = (FStar_Syntax_Syntax.as_arg f)
in (_145_405)::[])
in (_145_407)::_145_406))
in (FStar_Syntax_Syntax.mk_Tm_app mk_wlp _145_408 (Some (k.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (mk_comp md_pure FStar_TypeChecker_Common.t_unit wp wlp []))))
end))))


let label : Prims.string  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun reason r f -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((f, FStar_Syntax_Syntax.Meta_labeled ((reason, r, false))))) None f.FStar_Syntax_Syntax.pos))


let label_opt : FStar_TypeChecker_Env.env  ->  (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env reason r f -> (match (reason) with
| None -> begin
f
end
| Some (reason) -> begin
if (let _145_432 = (FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str)
in (FStar_All.pipe_left Prims.op_Negation _145_432)) then begin
f
end else begin
(let _145_433 = (reason ())
in (label _145_433 r f))
end
end))


let label_guard : FStar_Range.range  ->  Prims.string  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun r reason g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let _56_806 = g
in (let _145_441 = (let _145_440 = (label reason r f)
in FStar_TypeChecker_Common.NonTrivial (_145_440))
in {FStar_TypeChecker_Env.guard_f = _145_441; FStar_TypeChecker_Env.deferred = _56_806.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_806.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_806.FStar_TypeChecker_Env.implicits}))
end))


let weaken_guard : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(

let g = (FStar_Syntax_Util.mk_imp f1 f2)
in FStar_TypeChecker_Common.NonTrivial (g))
end
| _56_817 -> begin
g2
end))


let weaken_precondition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_Syntax_Syntax.lcomp = (fun env lc f -> (

let weaken = (fun _56_822 -> (match (()) with
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

let _56_831 = (destruct_comp c)
in (match (_56_831) with
| (res_t, wp, wlp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let us = (let _145_454 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_145_454)::[])
in (

let wp = (let _145_461 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _145_460 = (let _145_459 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_458 = (let _145_457 = (FStar_Syntax_Syntax.as_arg f)
in (let _145_456 = (let _145_455 = (FStar_Syntax_Syntax.as_arg wp)
in (_145_455)::[])
in (_145_457)::_145_456))
in (_145_459)::_145_458))
in (FStar_Syntax_Syntax.mk_Tm_app _145_461 _145_460 None wp.FStar_Syntax_Syntax.pos)))
in (

let wlp = (let _145_468 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _145_467 = (let _145_466 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_465 = (let _145_464 = (FStar_Syntax_Syntax.as_arg f)
in (let _145_463 = (let _145_462 = (FStar_Syntax_Syntax.as_arg wlp)
in (_145_462)::[])
in (_145_464)::_145_463))
in (_145_466)::_145_465))
in (FStar_Syntax_Syntax.mk_Tm_app _145_468 _145_467 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp c.FStar_Syntax_Syntax.flags)))))
end)))
end
end))
end))
in (

let _56_836 = lc
in {FStar_Syntax_Syntax.eff_name = _56_836.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _56_836.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _56_836.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = weaken})))


let strengthen_precondition : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun reason env e lc g0 -> if (FStar_TypeChecker_Rel.is_trivial g0) then begin
(lc, g0)
end else begin
(

let _56_843 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _145_488 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _145_487 = (FStar_TypeChecker_Rel.guard_to_string env g0)
in (FStar_Util.print2 "+++++++++++++Strengthening pre-condition of term %s with guard %s\n" _145_488 _145_487)))
end else begin
()
end
in (

let flags = (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.collect (fun _56_2 -> (match (_56_2) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
(FStar_Syntax_Syntax.PARTIAL_RETURN)::[]
end
| _56_849 -> begin
[]
end))))
in (

let strengthen = (fun _56_852 -> (match (()) with
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

let xret = (let _145_493 = (let _145_492 = (FStar_Syntax_Syntax.bv_to_name x)
in (return_value env x.FStar_Syntax_Syntax.sort _145_492))
in (FStar_Syntax_Util.comp_set_flags _145_493 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (

let lc = (bind e.FStar_Syntax_Syntax.pos env (Some (e)) (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), (FStar_Syntax_Util.lcomp_of_comp xret)))
in (lc.FStar_Syntax_Syntax.comp ()))))
end else begin
c
end
in (

let _56_862 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _145_495 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _145_494 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print2 "-------------Strengthening pre-condition of term %s with guard %s\n" _145_495 _145_494)))
end else begin
()
end
in (

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _56_868 = (destruct_comp c)
in (match (_56_868) with
| (res_t, wp, wlp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let us = (let _145_496 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_145_496)::[])
in (

let wp = (let _145_505 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assert_p)
in (let _145_504 = (let _145_503 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_502 = (let _145_501 = (let _145_498 = (let _145_497 = (FStar_TypeChecker_Env.get_range env)
in (label_opt env reason _145_497 f))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _145_498))
in (let _145_500 = (let _145_499 = (FStar_Syntax_Syntax.as_arg wp)
in (_145_499)::[])
in (_145_501)::_145_500))
in (_145_503)::_145_502))
in (FStar_Syntax_Syntax.mk_Tm_app _145_505 _145_504 None wp.FStar_Syntax_Syntax.pos)))
in (

let wlp = (let _145_512 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.assume_p)
in (let _145_511 = (let _145_510 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_509 = (let _145_508 = (FStar_Syntax_Syntax.as_arg f)
in (let _145_507 = (let _145_506 = (FStar_Syntax_Syntax.as_arg wlp)
in (_145_506)::[])
in (_145_508)::_145_507))
in (_145_510)::_145_509))
in (FStar_Syntax_Syntax.mk_Tm_app _145_512 _145_511 None wlp.FStar_Syntax_Syntax.pos)))
in (

let _56_873 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _145_513 = (FStar_Syntax_Print.term_to_string wp)
in (FStar_Util.print1 "-------------Strengthened pre-condition is %s\n" _145_513))
end else begin
()
end
in (

let c2 = (mk_comp md res_t wp wlp flags)
in c2))))))
end)))))
end)))
end))
in (let _145_517 = (

let _56_876 = lc
in (let _145_516 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in (let _145_515 = if ((FStar_Syntax_Util.is_pure_lcomp lc) && (let _145_514 = (FStar_Syntax_Util.is_function_typ lc.FStar_Syntax_Syntax.res_typ)
in (FStar_All.pipe_left Prims.op_Negation _145_514))) then begin
flags
end else begin
[]
end
in {FStar_Syntax_Syntax.eff_name = _145_516; FStar_Syntax_Syntax.res_typ = _56_876.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _145_515; FStar_Syntax_Syntax.comp = strengthen})))
in (_145_517, (

let _56_878 = g0
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _56_878.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_878.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_878.FStar_TypeChecker_Env.implicits}))))))
end)


let add_equality_to_post_condition : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.comp = (fun env comp res_t -> (

let md_pure = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let y = (FStar_Syntax_Syntax.new_bv None res_t)
in (

let _56_888 = (let _145_525 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _145_524 = (FStar_Syntax_Syntax.bv_to_name y)
in (_145_525, _145_524)))
in (match (_56_888) with
| (xexp, yexp) -> begin
(

let us = (let _145_526 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_145_526)::[])
in (

let yret = (let _145_531 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.ret)
in (let _145_530 = (let _145_529 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_528 = (let _145_527 = (FStar_Syntax_Syntax.as_arg yexp)
in (_145_527)::[])
in (_145_529)::_145_528))
in (FStar_Syntax_Syntax.mk_Tm_app _145_531 _145_530 None res_t.FStar_Syntax_Syntax.pos)))
in (

let x_eq_y_yret = (let _145_539 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md_pure md_pure.FStar_Syntax_Syntax.assume_p)
in (let _145_538 = (let _145_537 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_536 = (let _145_535 = (let _145_532 = (FStar_Syntax_Util.mk_eq res_t res_t xexp yexp)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _145_532))
in (let _145_534 = (let _145_533 = (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg yret)
in (_145_533)::[])
in (_145_535)::_145_534))
in (_145_537)::_145_536))
in (FStar_Syntax_Syntax.mk_Tm_app _145_539 _145_538 None res_t.FStar_Syntax_Syntax.pos)))
in (

let forall_y_x_eq_y_yret = (let _145_549 = (FStar_TypeChecker_Env.inst_effect_fun_with (FStar_List.append us us) env md_pure md_pure.FStar_Syntax_Syntax.close_wp)
in (let _145_548 = (let _145_547 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_546 = (let _145_545 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_544 = (let _145_543 = (let _145_542 = (let _145_541 = (let _145_540 = (FStar_Syntax_Syntax.mk_binder y)
in (_145_540)::[])
in (FStar_Syntax_Util.abs _145_541 x_eq_y_yret (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid)))))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _145_542))
in (_145_543)::[])
in (_145_545)::_145_544))
in (_145_547)::_145_546))
in (FStar_Syntax_Syntax.mk_Tm_app _145_549 _145_548 None res_t.FStar_Syntax_Syntax.pos)))
in (

let lc2 = (mk_comp md_pure res_t forall_y_x_eq_y_yret forall_y_x_eq_y_yret ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[]))
in (

let lc = (let _145_550 = (FStar_TypeChecker_Env.get_range env)
in (bind _145_550 env None (FStar_Syntax_Util.lcomp_of_comp comp) (Some (x), (FStar_Syntax_Util.lcomp_of_comp lc2))))
in (lc.FStar_Syntax_Syntax.comp ())))))))
end))))))


let ite : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.formula  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env guard lcomp_then lcomp_else -> (

let comp = (fun _56_900 -> (match (()) with
| () -> begin
(

let _56_916 = (let _145_562 = (lcomp_then.FStar_Syntax_Syntax.comp ())
in (let _145_561 = (lcomp_else.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _145_562 _145_561)))
in (match (_56_916) with
| ((md, _56_903, _56_905), (res_t, wp_then, wlp_then), (_56_912, wp_else, wlp_else)) -> begin
(

let us = (let _145_563 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_145_563)::[])
in (

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _145_583 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _145_582 = (let _145_580 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_579 = (let _145_578 = (FStar_Syntax_Syntax.as_arg g)
in (let _145_577 = (let _145_576 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _145_575 = (let _145_574 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_145_574)::[])
in (_145_576)::_145_575))
in (_145_578)::_145_577))
in (_145_580)::_145_579))
in (let _145_581 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _145_583 _145_582 None _145_581)))))
in (

let wp = (ifthenelse md res_t guard wp_then wp_else)
in (

let wlp = (ifthenelse md res_t guard wlp_then wlp_else)
in if ((FStar_Options.split_cases ()) > 0) then begin
(

let comp = (mk_comp md res_t wp wlp [])
in (add_equality_to_post_condition env comp res_t))
end else begin
(

let wp = (let _145_590 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _145_589 = (let _145_588 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_587 = (let _145_586 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _145_585 = (let _145_584 = (FStar_Syntax_Syntax.as_arg wp)
in (_145_584)::[])
in (_145_586)::_145_585))
in (_145_588)::_145_587))
in (FStar_Syntax_Syntax.mk_Tm_app _145_590 _145_589 None wp.FStar_Syntax_Syntax.pos)))
in (

let wlp = (let _145_595 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _145_594 = (let _145_593 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_592 = (let _145_591 = (FStar_Syntax_Syntax.as_arg wlp)
in (_145_591)::[])
in (_145_593)::_145_592))
in (FStar_Syntax_Syntax.mk_Tm_app _145_595 _145_594 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end))))
end))
end))
in (let _145_596 = (join_effects env lcomp_then.FStar_Syntax_Syntax.eff_name lcomp_else.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _145_596; FStar_Syntax_Syntax.res_typ = lcomp_then.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = comp})))


let fvar_const : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env lid -> (let _145_602 = (let _145_601 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Ident.set_lid_range lid _145_601))
in (FStar_Syntax_Syntax.fvar _145_602 FStar_Syntax_Syntax.Delta_constant None)))


let bind_cases : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.lcomp) Prims.list  ->  FStar_Syntax_Syntax.lcomp = (fun env res_t lcases -> (

let eff = (FStar_List.fold_left (fun eff _56_938 -> (match (_56_938) with
| (_56_936, lc) -> begin
(join_effects env eff lc.FStar_Syntax_Syntax.eff_name)
end)) FStar_Syntax_Const.effect_PURE_lid lcases)
in (

let bind_cases = (fun _56_941 -> (match (()) with
| () -> begin
(

let us = (let _145_613 = (env.FStar_TypeChecker_Env.universe_of env res_t)
in (_145_613)::[])
in (

let ifthenelse = (fun md res_t g wp_t wp_e -> (let _145_633 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.if_then_else)
in (let _145_632 = (let _145_630 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_629 = (let _145_628 = (FStar_Syntax_Syntax.as_arg g)
in (let _145_627 = (let _145_626 = (FStar_Syntax_Syntax.as_arg wp_t)
in (let _145_625 = (let _145_624 = (FStar_Syntax_Syntax.as_arg wp_e)
in (_145_624)::[])
in (_145_626)::_145_625))
in (_145_628)::_145_627))
in (_145_630)::_145_629))
in (let _145_631 = (FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos wp_e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_app _145_633 _145_632 None _145_631)))))
in (

let default_case = (

let post_k = (let _145_636 = (let _145_634 = (FStar_Syntax_Syntax.null_binder res_t)
in (_145_634)::[])
in (let _145_635 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _145_636 _145_635)))
in (

let kwp = (let _145_639 = (let _145_637 = (FStar_Syntax_Syntax.null_binder post_k)
in (_145_637)::[])
in (let _145_638 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_Syntax_Util.arrow _145_639 _145_638)))
in (

let post = (FStar_Syntax_Syntax.new_bv None post_k)
in (

let wp = (let _145_645 = (let _145_640 = (FStar_Syntax_Syntax.mk_binder post)
in (_145_640)::[])
in (let _145_644 = (let _145_643 = (let _145_641 = (FStar_TypeChecker_Env.get_range env)
in (label FStar_TypeChecker_Errors.exhaustiveness_check _145_641))
in (let _145_642 = (fvar_const env FStar_Syntax_Const.false_lid)
in (FStar_All.pipe_left _145_643 _145_642)))
in (FStar_Syntax_Util.abs _145_645 _145_644 (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid))))))
in (

let wlp = (let _145_648 = (let _145_646 = (FStar_Syntax_Syntax.mk_binder post)
in (_145_646)::[])
in (let _145_647 = (fvar_const env FStar_Syntax_Const.true_lid)
in (FStar_Syntax_Util.abs _145_648 _145_647 (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid))))))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env FStar_Syntax_Const.effect_PURE_lid)
in (mk_comp md res_t wp wlp [])))))))
in (

let comp = (FStar_List.fold_right (fun _56_958 celse -> (match (_56_958) with
| (g, cthen) -> begin
(

let _56_976 = (let _145_651 = (cthen.FStar_Syntax_Syntax.comp ())
in (lift_and_destruct env _145_651 celse))
in (match (_56_976) with
| ((md, _56_962, _56_964), (_56_967, wp_then, wlp_then), (_56_972, wp_else, wlp_else)) -> begin
(let _145_653 = (ifthenelse md res_t g wp_then wp_else)
in (let _145_652 = (ifthenelse md res_t g wlp_then wlp_else)
in (mk_comp md res_t _145_653 _145_652 [])))
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

let _56_984 = (destruct_comp comp)
in (match (_56_984) with
| (_56_981, wp, wlp) -> begin
(

let wp = (let _145_660 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wp)
in (let _145_659 = (let _145_658 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_657 = (let _145_656 = (FStar_Syntax_Syntax.as_arg wlp)
in (let _145_655 = (let _145_654 = (FStar_Syntax_Syntax.as_arg wp)
in (_145_654)::[])
in (_145_656)::_145_655))
in (_145_658)::_145_657))
in (FStar_Syntax_Syntax.mk_Tm_app _145_660 _145_659 None wp.FStar_Syntax_Syntax.pos)))
in (

let wlp = (let _145_665 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ite_wlp)
in (let _145_664 = (let _145_663 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_662 = (let _145_661 = (FStar_Syntax_Syntax.as_arg wlp)
in (_145_661)::[])
in (_145_663)::_145_662))
in (FStar_Syntax_Syntax.mk_Tm_app _145_665 _145_664 None wlp.FStar_Syntax_Syntax.pos)))
in (mk_comp md res_t wp wlp [])))
end))))
end))))
end))
in {FStar_Syntax_Syntax.eff_name = eff; FStar_Syntax_Syntax.res_typ = res_t; FStar_Syntax_Syntax.cflags = []; FStar_Syntax_Syntax.comp = bind_cases})))


let close_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env bvs lc -> (

let close = (fun _56_991 -> (match (()) with
| () -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in if (FStar_Syntax_Util.is_ml_comp c) then begin
c
end else begin
(

let close_wp = (fun u_res md res_t bvs wp0 -> (FStar_List.fold_right (fun x wp -> (

let bs = (let _145_686 = (FStar_Syntax_Syntax.mk_binder x)
in (_145_686)::[])
in (

let us = (let _145_688 = (let _145_687 = (env.FStar_TypeChecker_Env.universe_of env x.FStar_Syntax_Syntax.sort)
in (_145_687)::[])
in (u_res)::_145_688)
in (

let wp = (FStar_Syntax_Util.abs bs wp (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid))))
in (let _145_695 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.close_wp)
in (let _145_694 = (let _145_693 = (FStar_Syntax_Syntax.as_arg res_t)
in (let _145_692 = (let _145_691 = (FStar_Syntax_Syntax.as_arg x.FStar_Syntax_Syntax.sort)
in (let _145_690 = (let _145_689 = (FStar_Syntax_Syntax.as_arg wp)
in (_145_689)::[])
in (_145_691)::_145_690))
in (_145_693)::_145_692))
in (FStar_Syntax_Syntax.mk_Tm_app _145_695 _145_694 None wp0.FStar_Syntax_Syntax.pos))))))) bvs wp0))
in (

let c = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _56_1008 = (destruct_comp c)
in (match (_56_1008) with
| (t, wp, wlp) -> begin
(

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let u_res = (env.FStar_TypeChecker_Env.universe_of env c.FStar_Syntax_Syntax.result_typ)
in (

let wp = (close_wp u_res md c.FStar_Syntax_Syntax.result_typ bvs wp)
in (

let wlp = (close_wp u_res md c.FStar_Syntax_Syntax.result_typ bvs wlp)
in (mk_comp md c.FStar_Syntax_Syntax.result_typ wp wlp c.FStar_Syntax_Syntax.flags)))))
end))))
end)
end))
in (

let _56_1013 = lc
in {FStar_Syntax_Syntax.eff_name = _56_1013.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _56_1013.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _56_1013.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = close})))


let maybe_assume_result_eq_pure_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env e lc -> (

let refine = (fun _56_1019 -> (match (()) with
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
(let _145_706 = (let _145_705 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _145_704 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "%s: %s\n" _145_705 _145_704)))
in (FStar_All.failwith _145_706))
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

let ret = (let _145_708 = (let _145_707 = (return_value env t xexp)
in (FStar_Syntax_Util.comp_set_flags _145_707 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::[])))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _145_708))
in (

let eq = (FStar_Syntax_Util.mk_eq t t xexp e)
in (

let eq_ret = (weaken_precondition env ret (FStar_TypeChecker_Common.NonTrivial (eq)))
in (

let c = (let _145_710 = (let _145_709 = (bind e.FStar_Syntax_Syntax.pos env None (FStar_Syntax_Util.lcomp_of_comp c) (Some (x), eq_ret))
in (_145_709.FStar_Syntax_Syntax.comp ()))
in (FStar_Syntax_Util.comp_set_flags _145_710 ((FStar_Syntax_Syntax.PARTIAL_RETURN)::(FStar_Syntax_Util.comp_flags c))))
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

let _56_1031 = lc
in {FStar_Syntax_Syntax.eff_name = _56_1031.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _56_1031.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = refine}))))


let check_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env e c c' -> (match ((FStar_TypeChecker_Rel.sub_comp env c c')) with
| None -> begin
(let _145_722 = (let _145_721 = (let _145_720 = (FStar_TypeChecker_Errors.computed_computation_type_does_not_match_annotation env e c c')
in (let _145_719 = (FStar_TypeChecker_Env.get_range env)
in (_145_720, _145_719)))
in FStar_Syntax_Syntax.Error (_145_721))
in (Prims.raise _145_722))
end
| Some (g) -> begin
(e, c', g)
end))


let maybe_coerce_bool_to_type : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env e lc t -> (match ((let _145_731 = (FStar_Syntax_Subst.compress t)
in _145_731.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_56_1045) -> begin
(match ((let _145_732 = (FStar_Syntax_Subst.compress lc.FStar_Syntax_Syntax.res_typ)
in _145_732.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.bool_lid) -> begin
(

let _56_1049 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.b2t_lid)
in (

let b2t = (let _145_733 = (FStar_Ident.set_lid_range FStar_Syntax_Const.b2t_lid e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar _145_733 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (

let lc = (let _145_736 = (let _145_735 = (let _145_734 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _145_734))
in (None, _145_735))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) lc _145_736))
in (

let e = (let _145_738 = (let _145_737 = (FStar_Syntax_Syntax.as_arg e)
in (_145_737)::[])
in (FStar_Syntax_Syntax.mk_Tm_app b2t _145_738 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (e, lc)))))
end
| _56_1055 -> begin
(e, lc)
end)
end
| _56_1057 -> begin
(e, lc)
end))


let weaken_result_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc t -> (

let gopt = if env.FStar_TypeChecker_Env.use_eq then begin
(let _145_747 = (FStar_TypeChecker_Rel.try_teq env lc.FStar_Syntax_Syntax.res_typ t)
in (_145_747, false))
end else begin
(let _145_748 = (FStar_TypeChecker_Rel.try_subtype env lc.FStar_Syntax_Syntax.res_typ t)
in (_145_748, true))
end
in (match (gopt) with
| (None, _56_1065) -> begin
(FStar_TypeChecker_Rel.subtype_fail env lc.FStar_Syntax_Syntax.res_typ t)
end
| (Some (g), apply_guard) -> begin
(match ((FStar_TypeChecker_Rel.guard_form g)) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let lc = (

let _56_1072 = lc
in {FStar_Syntax_Syntax.eff_name = _56_1072.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _56_1072.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _56_1072.FStar_Syntax_Syntax.comp})
in (e, lc, g))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let g = (

let _56_1077 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _56_1077.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_1077.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_1077.FStar_TypeChecker_Env.implicits})
in (

let strengthen = (fun _56_1081 -> (match (()) with
| () -> begin
(

let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (match ((let _145_751 = (FStar_Syntax_Subst.compress f)
in _145_751.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_56_1084, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _56_1090; FStar_Syntax_Syntax.pos = _56_1088; FStar_Syntax_Syntax.vars = _56_1086}, _56_1095) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
(

let lc = (

let _56_1098 = lc
in {FStar_Syntax_Syntax.eff_name = _56_1098.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _56_1098.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _56_1098.FStar_Syntax_Syntax.comp})
in (lc.FStar_Syntax_Syntax.comp ()))
end
| _56_1102 -> begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let _56_1104 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _145_755 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (let _145_754 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (let _145_753 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (let _145_752 = (FStar_TypeChecker_Normalize.term_to_string env f)
in (FStar_Util.print4 "Weakened from %s to %s\nStrengthening %s with guard %s\n" _145_755 _145_754 _145_753 _145_752)))))
end else begin
()
end
in (

let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (

let _56_1109 = (FStar_TypeChecker_Env.wp_signature env FStar_Syntax_Const.effect_PURE_lid)
in (match (_56_1109) with
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

let us = (let _145_756 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_145_756)::[])
in (

let wp = (let _145_761 = (FStar_TypeChecker_Env.inst_effect_fun_with us env md md.FStar_Syntax_Syntax.ret)
in (let _145_760 = (let _145_759 = (FStar_Syntax_Syntax.as_arg t)
in (let _145_758 = (let _145_757 = (FStar_Syntax_Syntax.as_arg xexp)
in (_145_757)::[])
in (_145_759)::_145_758))
in (FStar_Syntax_Syntax.mk_Tm_app _145_761 _145_760 (Some (k.FStar_Syntax_Syntax.n)) xexp.FStar_Syntax_Syntax.pos)))
in (

let cret = (let _145_762 = (mk_comp md t wp wp ((FStar_Syntax_Syntax.RETURN)::[]))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _145_762))
in (

let guard = if apply_guard then begin
(let _145_764 = (let _145_763 = (FStar_Syntax_Syntax.as_arg xexp)
in (_145_763)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f _145_764 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
end else begin
f
end
in (

let _56_1120 = (let _145_772 = (FStar_All.pipe_left (fun _145_769 -> Some (_145_769)) (FStar_TypeChecker_Errors.subtyping_failed env lc.FStar_Syntax_Syntax.res_typ t))
in (let _145_771 = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (let _145_770 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (guard)))
in (strengthen_precondition _145_772 _145_771 e cret _145_770))))
in (match (_56_1120) with
| (eq_ret, _trivial_so_ok_to_discard) -> begin
(

let x = (

let _56_1121 = x
in {FStar_Syntax_Syntax.ppname = _56_1121.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_1121.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lc.FStar_Syntax_Syntax.res_typ})
in (

let c = (let _145_774 = (let _145_773 = (FStar_Syntax_Syntax.mk_Comp ct)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _145_773))
in (bind e.FStar_Syntax_Syntax.pos env (Some (e)) _145_774 (Some (x), eq_ret)))
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let _56_1126 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _145_775 = (FStar_TypeChecker_Normalize.comp_to_string env c)
in (FStar_Util.print1 "Strengthened to %s\n" _145_775))
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
| _56_1132 -> begin
[]
end))))
in (

let lc = (

let _56_1134 = lc
in (let _145_777 = (FStar_TypeChecker_Env.norm_eff_name env lc.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.eff_name = _145_777; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = strengthen}))
in (

let g = (

let _56_1137 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _56_1137.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_1137.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_1137.FStar_TypeChecker_Env.implicits})
in (e, lc, g))))))
end)
end)))


let pure_or_ghost_pre_and_post : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_Syntax_Syntax.typ) = (fun env comp -> (

let mk_post_type = (fun res_t ens -> (

let x = (FStar_Syntax_Syntax.new_bv None res_t)
in (let _145_789 = (let _145_788 = (let _145_787 = (let _145_786 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _145_786))
in (_145_787)::[])
in (FStar_Syntax_Syntax.mk_Tm_app ens _145_788 None res_t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Util.refine x _145_789))))
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
| (req, _56_1165)::(ens, _56_1160)::_56_1157 -> begin
(let _145_795 = (let _145_792 = (norm req)
in Some (_145_792))
in (let _145_794 = (let _145_793 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (FStar_All.pipe_left norm _145_793))
in (_145_795, _145_794)))
end
| _56_1169 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(

let ct = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env comp)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (wp, _56_1180)::(wlp, _56_1175)::_56_1172 -> begin
(

let _56_1186 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_requires)
in (match (_56_1186) with
| (us_r, _56_1185) -> begin
(

let _56_1190 = (FStar_TypeChecker_Env.lookup_lid env FStar_Syntax_Const.as_ensures)
in (match (_56_1190) with
| (us_e, _56_1189) -> begin
(

let r = ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos
in (

let as_req = (let _145_797 = (let _145_796 = (FStar_Ident.set_lid_range FStar_Syntax_Const.as_requires r)
in (FStar_Syntax_Syntax.fvar _145_796 FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _145_797 us_r))
in (

let as_ens = (let _145_799 = (let _145_798 = (FStar_Ident.set_lid_range FStar_Syntax_Const.as_ensures r)
in (FStar_Syntax_Syntax.fvar _145_798 FStar_Syntax_Syntax.Delta_equational None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _145_799 us_e))
in (

let req = (let _145_802 = (let _145_801 = (let _145_800 = (FStar_Syntax_Syntax.as_arg wp)
in (_145_800)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.imp_tag)))::_145_801)
in (FStar_Syntax_Syntax.mk_Tm_app as_req _145_802 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let ens = (let _145_805 = (let _145_804 = (let _145_803 = (FStar_Syntax_Syntax.as_arg wlp)
in (_145_803)::[])
in ((ct.FStar_Syntax_Syntax.result_typ, Some (FStar_Syntax_Syntax.imp_tag)))::_145_804)
in (FStar_Syntax_Syntax.mk_Tm_app as_ens _145_805 None ct.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (let _145_809 = (let _145_806 = (norm req)
in Some (_145_806))
in (let _145_808 = (let _145_807 = (mk_post_type ct.FStar_Syntax_Syntax.result_typ ens)
in (norm _145_807))
in (_145_809, _145_808))))))))
end))
end))
end
| _56_1197 -> begin
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

let _56_1208 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_56_1208) with
| (bs, c) -> begin
(

let rec aux = (fun subst _56_4 -> (match (_56_4) with
| (x, Some (FStar_Syntax_Syntax.Implicit (dot)))::rest -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let _56_1224 = (new_implicit_var "Instantiation of implicit argument" e.FStar_Syntax_Syntax.pos env t)
in (match (_56_1224) with
| (v, _56_1222, g) -> begin
(

let subst = (FStar_Syntax_Syntax.NT ((x, v)))::subst
in (

let _56_1230 = (aux subst rest)
in (match (_56_1230) with
| (args, bs, subst, g') -> begin
(let _145_820 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((v, Some (FStar_Syntax_Syntax.Implicit (dot))))::args, bs, subst, _145_820))
end)))
end)))
end
| bs -> begin
([], bs, subst, FStar_TypeChecker_Rel.trivial_guard)
end))
in (

let _56_1236 = (aux [] bs)
in (match (_56_1236) with
| (args, bs, subst, guard) -> begin
(match ((args, bs)) with
| ([], _56_1239) -> begin
(e, torig, guard)
end
| (_56_1242, []) when (not ((FStar_Syntax_Util.is_total_comp c))) -> begin
(e, torig, FStar_TypeChecker_Rel.trivial_guard)
end
| _56_1246 -> begin
(

let t = (match (bs) with
| [] -> begin
(FStar_Syntax_Util.comp_result c)
end
| _56_1249 -> begin
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
| _56_1254 -> begin
(e, t, FStar_TypeChecker_Rel.trivial_guard)
end)
end))


let gen_univs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set  ->  FStar_Syntax_Syntax.univ_name Prims.list = (fun env x -> if (FStar_Util.set_is_empty x) then begin
[]
end else begin
(

let s = (let _145_826 = (let _145_825 = (FStar_TypeChecker_Env.univ_vars env)
in (FStar_Util.set_difference x _145_825))
in (FStar_All.pipe_right _145_826 FStar_Util.set_elements))
in (

let r = (let _145_827 = (FStar_TypeChecker_Env.get_range env)
in Some (_145_827))
in (

let u_names = (FStar_All.pipe_right s (FStar_List.map (fun u -> (

let u_name = (FStar_Syntax_Syntax.new_univ_name r)
in (

let _56_1261 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _145_832 = (let _145_829 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_left FStar_Util.string_of_int _145_829))
in (let _145_831 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (u)))
in (let _145_830 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_name (u_name)))
in (FStar_Util.print3 "Setting ?%s (%s) to %s\n" _145_832 _145_831 _145_830))))
end else begin
()
end
in (

let _56_1263 = (FStar_Unionfind.change u (Some (FStar_Syntax_Syntax.U_name (u_name))))
in u_name))))))
in u_names)))
end)


let generalize_universes : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.tscheme = (fun env t -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (

let univs = (FStar_Syntax_Free.univs t)
in (

let _56_1271 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _145_841 = (let _145_840 = (let _145_839 = (FStar_Util.set_elements univs)
in (FStar_All.pipe_right _145_839 (FStar_List.map (fun u -> (let _145_838 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _145_838 FStar_Util.string_of_int))))))
in (FStar_All.pipe_right _145_840 (FStar_String.concat ", ")))
in (FStar_Util.print1 "univs to gen : %s\n" _145_841))
end else begin
()
end
in (

let gen = (gen_univs env univs)
in (

let _56_1274 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Gen"))) then begin
(let _145_842 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "After generalization: %s\n" _145_842))
end else begin
()
end
in (

let ts = (FStar_Syntax_Subst.close_univ_vars gen t)
in (gen, ts))))))))


let gen : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list Prims.option = (fun env ecs -> if (let _145_848 = (FStar_Util.for_all (fun _56_1282 -> (match (_56_1282) with
| (_56_1280, c) -> begin
(FStar_Syntax_Util.is_pure_or_ghost_comp c)
end)) ecs)
in (FStar_All.pipe_left Prims.op_Negation _145_848)) then begin
None
end else begin
(

let norm = (fun c -> (

let _56_1285 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _145_851 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n" _145_851))
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

let _56_1288 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _145_852 = (FStar_Syntax_Print.comp_to_string c)
in (FStar_Util.print1 "Normalized to:\n\t %s\n" _145_852))
end else begin
()
end
in c))))
in (

let env_uvars = (FStar_TypeChecker_Env.uvars_in_env env)
in (

let gen_uvars = (fun uvs -> (let _145_855 = (FStar_Util.set_difference uvs env_uvars)
in (FStar_All.pipe_right _145_855 FStar_Util.set_elements)))
in (

let _56_1305 = (let _145_857 = (FStar_All.pipe_right ecs (FStar_List.map (fun _56_1295 -> (match (_56_1295) with
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
in (FStar_All.pipe_right _145_857 FStar_List.unzip))
in (match (_56_1305) with
| (univs, uvars) -> begin
(

let univs = (FStar_List.fold_left FStar_Util.set_union FStar_Syntax_Syntax.no_universe_uvars univs)
in (

let gen_univs = (gen_univs env univs)
in (

let _56_1309 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(FStar_All.pipe_right gen_univs (FStar_List.iter (fun x -> (FStar_Util.print1 "Generalizing uvar %s\n" x.FStar_Ident.idText))))
end else begin
()
end
in (

let ecs = (FStar_All.pipe_right uvars (FStar_List.map (fun _56_1314 -> (match (_56_1314) with
| (uvs, e, c) -> begin
(

let tvars = (FStar_All.pipe_right uvs (FStar_List.map (fun _56_1317 -> (match (_56_1317) with
| (u, k) -> begin
(match ((FStar_Unionfind.find u)) with
| (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) | (FStar_Syntax_Syntax.Fixed ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (_, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (a); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _})) -> begin
(a, Some (FStar_Syntax_Syntax.imp_tag))
end
| FStar_Syntax_Syntax.Fixed (_56_1351) -> begin
(FStar_All.failwith "Unexpected instantiation of mutually recursive uvar")
end
| _56_1354 -> begin
(

let k = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k)
in (

let _56_1358 = (FStar_Syntax_Util.arrow_formals k)
in (match (_56_1358) with
| (bs, kres) -> begin
(

let a = (let _145_863 = (let _145_862 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _145_861 -> Some (_145_861)) _145_862))
in (FStar_Syntax_Syntax.new_bv _145_863 kres))
in (

let t = (let _145_868 = (FStar_Syntax_Syntax.bv_to_name a)
in (let _145_867 = (let _145_866 = (let _145_865 = (let _145_864 = (FStar_Syntax_Syntax.mk_Total kres)
in (FStar_Syntax_Util.lcomp_of_comp _145_864))
in FStar_Util.Inl (_145_865))
in Some (_145_866))
in (FStar_Syntax_Util.abs bs _145_868 _145_867)))
in (

let _56_1361 = (FStar_Syntax_Util.set_uvar u t)
in (a, Some (FStar_Syntax_Syntax.imp_tag)))))
end)))
end)
end))))
in (

let _56_1385 = (match (tvars) with
| [] -> begin
(e, c)
end
| _56_1366 -> begin
(

let _56_1369 = (e, c)
in (match (_56_1369) with
| (e0, c0) -> begin
(

let c = (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.BetaUVars)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::[]) env c)
in (

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.BetaUVars)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::[]) env e)
in (

let t = (match ((let _145_869 = (FStar_Syntax_Subst.compress (FStar_Syntax_Util.comp_result c))
in _145_869.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cod) -> begin
(

let _56_1378 = (FStar_Syntax_Subst.open_comp bs cod)
in (match (_56_1378) with
| (bs, cod) -> begin
(FStar_Syntax_Util.arrow (FStar_List.append tvars bs) cod)
end))
end
| _56_1380 -> begin
(FStar_Syntax_Util.arrow tvars c)
end)
in (

let e' = (FStar_Syntax_Util.abs tvars e (Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp c)))))
in (let _145_870 = (FStar_Syntax_Syntax.mk_Total t)
in (e', _145_870))))))
end))
end)
in (match (_56_1385) with
| (e, c) -> begin
(gen_univs, e, c)
end)))
end))))
in Some (ecs)))))
end)))))
end)


let generalize : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) Prims.list = (fun env lecs -> (

let _56_1395 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _145_877 = (let _145_876 = (FStar_List.map (fun _56_1394 -> (match (_56_1394) with
| (lb, _56_1391, _56_1393) -> begin
(FStar_Syntax_Print.lbname_to_string lb)
end)) lecs)
in (FStar_All.pipe_right _145_876 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Generalizing: %s\n" _145_877))
end else begin
()
end
in (match ((let _145_879 = (FStar_All.pipe_right lecs (FStar_List.map (fun _56_1401 -> (match (_56_1401) with
| (_56_1398, e, c) -> begin
(e, c)
end))))
in (gen env _145_879))) with
| None -> begin
(FStar_All.pipe_right lecs (FStar_List.map (fun _56_1406 -> (match (_56_1406) with
| (l, t, c) -> begin
(l, [], t, c)
end))))
end
| Some (ecs) -> begin
(FStar_List.map2 (fun _56_1414 _56_1418 -> (match ((_56_1414, _56_1418)) with
| ((l, _56_1411, _56_1413), (us, e, c)) -> begin
(

let _56_1419 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _145_885 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _145_884 = (FStar_Syntax_Print.lbname_to_string l)
in (let _145_883 = (FStar_Syntax_Print.term_to_string (FStar_Syntax_Util.comp_result c))
in (FStar_Util.print3 "(%s) Generalized %s to %s\n" _145_885 _145_884 _145_883))))
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
(let _145_901 = (FStar_TypeChecker_Rel.apply_guard f e)
in (FStar_All.pipe_left (fun _145_900 -> Some (_145_900)) _145_901))
end)
end)
in (

let is_var = (fun e -> (match ((let _145_904 = (FStar_Syntax_Subst.compress e)
in _145_904.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (_56_1436) -> begin
true
end
| _56_1439 -> begin
false
end))
in (

let decorate = (fun e t -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name ((

let _56_1446 = x
in {FStar_Syntax_Syntax.ppname = _56_1446.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_1446.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t2}))) (Some (t2.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
end
| _56_1449 -> begin
(

let _56_1450 = e
in (let _145_909 = (FStar_Util.mk_ref (Some (t2.FStar_Syntax_Syntax.n)))
in {FStar_Syntax_Syntax.n = _56_1450.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _145_909; FStar_Syntax_Syntax.pos = _56_1450.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _56_1450.FStar_Syntax_Syntax.vars}))
end)))
in (

let env = (

let _56_1452 = env
in (let _145_910 = (env.FStar_TypeChecker_Env.use_eq || (env.FStar_TypeChecker_Env.is_pattern && (is_var e)))
in {FStar_TypeChecker_Env.solver = _56_1452.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _56_1452.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _56_1452.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _56_1452.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _56_1452.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _56_1452.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _56_1452.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _56_1452.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _56_1452.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _56_1452.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _56_1452.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _56_1452.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _56_1452.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _56_1452.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _56_1452.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _145_910; FStar_TypeChecker_Env.is_iface = _56_1452.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _56_1452.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _56_1452.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _56_1452.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _56_1452.FStar_TypeChecker_Env.use_bv_sorts}))
in (match ((check env t1 t2)) with
| None -> begin
(let _145_914 = (let _145_913 = (let _145_912 = (FStar_TypeChecker_Errors.expected_expression_of_type env t2 e t1)
in (let _145_911 = (FStar_TypeChecker_Env.get_range env)
in (_145_912, _145_911)))
in FStar_Syntax_Syntax.Error (_145_913))
in (Prims.raise _145_914))
end
| Some (g) -> begin
(

let _56_1458 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_915 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_All.pipe_left (FStar_Util.print1 "Applied guard is %s\n") _145_915))
end else begin
()
end
in (let _145_916 = (decorate e t2)
in (_145_916, g)))
end)))))))


let check_top_level : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.lcomp  ->  (Prims.bool * FStar_Syntax_Syntax.comp) = (fun env g lc -> (

let discharge = (fun g -> (

let _56_1465 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in (FStar_Syntax_Util.is_pure_lcomp lc)))
in (

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _145_926 = (discharge g)
in (let _145_925 = (lc.FStar_Syntax_Syntax.comp ())
in (_145_926, _145_925)))
end else begin
(

let c = (lc.FStar_Syntax_Syntax.comp ())
in (

let steps = (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.SNComp)::(FStar_TypeChecker_Normalize.DeltaComp)::[]
in (

let c = (let _145_929 = (let _145_928 = (let _145_927 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c)
in (FStar_All.pipe_right _145_927 FStar_Syntax_Syntax.mk_Comp))
in (FStar_All.pipe_right _145_928 (FStar_TypeChecker_Normalize.normalize_comp steps env)))
in (FStar_All.pipe_right _145_929 FStar_Syntax_Util.comp_to_comp_typ))
in (

let md = (FStar_TypeChecker_Env.get_effect_decl env c.FStar_Syntax_Syntax.effect_name)
in (

let _56_1476 = (destruct_comp c)
in (match (_56_1476) with
| (t, wp, _56_1475) -> begin
(

let vc = (let _145_937 = (let _145_931 = (let _145_930 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_145_930)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _145_931 env md md.FStar_Syntax_Syntax.trivial))
in (let _145_936 = (let _145_934 = (FStar_Syntax_Syntax.as_arg t)
in (let _145_933 = (let _145_932 = (FStar_Syntax_Syntax.as_arg wp)
in (_145_932)::[])
in (_145_934)::_145_933))
in (let _145_935 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Syntax_Syntax.mk_Tm_app _145_937 _145_936 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) _145_935))))
in (

let _56_1478 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _145_938 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.print1 "top-level VC: %s\n" _145_938))
end else begin
()
end
in (

let g = (let _145_939 = (FStar_All.pipe_left FStar_TypeChecker_Rel.guard_of_guard_formula (FStar_TypeChecker_Common.NonTrivial (vc)))
in (FStar_TypeChecker_Rel.conj_guard g _145_939))
in (let _145_941 = (discharge g)
in (let _145_940 = (FStar_Syntax_Syntax.mk_Comp c)
in (_145_941, _145_940))))))
end))))))
end)))


let short_circuit : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.args  ->  FStar_TypeChecker_Common.guard_formula = (fun head seen_args -> (

let short_bin_op = (fun f _56_5 -> (match (_56_5) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (fst, _56_1489)::[] -> begin
(f fst)
end
| _56_1493 -> begin
(FStar_All.failwith "Unexpexted args to binary operator")
end))
in (

let op_and_e = (fun e -> (let _145_962 = (FStar_Syntax_Util.b2t e)
in (FStar_All.pipe_right _145_962 (fun _145_961 -> FStar_TypeChecker_Common.NonTrivial (_145_961)))))
in (

let op_or_e = (fun e -> (let _145_967 = (let _145_965 = (FStar_Syntax_Util.b2t e)
in (FStar_Syntax_Util.mk_neg _145_965))
in (FStar_All.pipe_right _145_967 (fun _145_966 -> FStar_TypeChecker_Common.NonTrivial (_145_966)))))
in (

let op_and_t = (fun t -> (FStar_All.pipe_right t (fun _145_970 -> FStar_TypeChecker_Common.NonTrivial (_145_970))))
in (

let op_or_t = (fun t -> (let _145_974 = (FStar_All.pipe_right t FStar_Syntax_Util.mk_neg)
in (FStar_All.pipe_right _145_974 (fun _145_973 -> FStar_TypeChecker_Common.NonTrivial (_145_973)))))
in (

let op_imp_t = (fun t -> (FStar_All.pipe_right t (fun _145_977 -> FStar_TypeChecker_Common.NonTrivial (_145_977))))
in (

let short_op_ite = (fun _56_6 -> (match (_56_6) with
| [] -> begin
FStar_TypeChecker_Common.Trivial
end
| (guard, _56_1508)::[] -> begin
FStar_TypeChecker_Common.NonTrivial (guard)
end
| _then::(guard, _56_1513)::[] -> begin
(let _145_981 = (FStar_Syntax_Util.mk_neg guard)
in (FStar_All.pipe_right _145_981 (fun _145_980 -> FStar_TypeChecker_Common.NonTrivial (_145_980))))
end
| _56_1518 -> begin
(FStar_All.failwith "Unexpected args to ITE")
end))
in (

let table = ((FStar_Syntax_Const.op_And, (short_bin_op op_and_e)))::((FStar_Syntax_Const.op_Or, (short_bin_op op_or_e)))::((FStar_Syntax_Const.and_lid, (short_bin_op op_and_t)))::((FStar_Syntax_Const.or_lid, (short_bin_op op_or_t)))::((FStar_Syntax_Const.imp_lid, (short_bin_op op_imp_t)))::((FStar_Syntax_Const.ite_lid, short_op_ite))::[]
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((FStar_Util.find_map table (fun _56_1526 -> (match (_56_1526) with
| (x, mk) -> begin
if (FStar_Ident.lid_equals x lid) then begin
(let _145_1014 = (mk seen_args)
in Some (_145_1014))
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
| _56_1531 -> begin
FStar_TypeChecker_Common.Trivial
end))))))))))


let short_circuit_head : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun l -> (match ((let _145_1017 = (FStar_Syntax_Util.un_uinst l)
in _145_1017.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv) ((FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.imp_lid)::(FStar_Syntax_Const.ite_lid)::[]))
end
| _56_1536 -> begin
false
end))


let maybe_add_implicit_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun env bs -> (

let pos = (fun bs -> (match (bs) with
| (hd, _56_1545)::_56_1542 -> begin
(FStar_Syntax_Syntax.range_of_bv hd)
end
| _56_1549 -> begin
(FStar_TypeChecker_Env.get_range env)
end))
in (match (bs) with
| (_56_1553, Some (FStar_Syntax_Syntax.Implicit (_56_1555)))::_56_1551 -> begin
bs
end
| _56_1561 -> begin
(match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
bs
end
| Some (t) -> begin
(match ((let _145_1024 = (FStar_Syntax_Subst.compress t)
in _145_1024.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', _56_1567) -> begin
(match ((FStar_Util.prefix_until (fun _56_7 -> (match (_56_7) with
| (_56_1572, Some (FStar_Syntax_Syntax.Implicit (_56_1574))) -> begin
false
end
| _56_1579 -> begin
true
end)) bs')) with
| None -> begin
bs
end
| Some ([], _56_1583, _56_1585) -> begin
bs
end
| Some (imps, _56_1590, _56_1592) -> begin
if (FStar_All.pipe_right imps (FStar_Util.for_all (fun _56_1598 -> (match (_56_1598) with
| (x, _56_1597) -> begin
(FStar_Util.starts_with x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText "\'")
end)))) then begin
(

let r = (pos bs)
in (

let imps = (FStar_All.pipe_right imps (FStar_List.map (fun _56_1602 -> (match (_56_1602) with
| (x, i) -> begin
(let _145_1028 = (FStar_Syntax_Syntax.set_range_of_bv x r)
in (_145_1028, i))
end))))
in (FStar_List.append imps bs)))
end else begin
bs
end
end)
end
| _56_1605 -> begin
bs
end)
end)
end)))




