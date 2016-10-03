
open Prims

exception Un_extractable


let is_Un_extractable = (fun _discr_ -> (match (_discr_) with
| Un_extractable (_) -> begin
true
end
| _ -> begin
false
end))


let type_leq : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))


let type_leq_c : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr Prims.option) = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq_c (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))


let erasableType : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t -> (FStar_Extraction_ML_Util.erasableType (FStar_Extraction_ML_Util.udelta_unfold g) t))


let eraseTypeDeep : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold g) t))


let fail = (fun r msg -> (

let _79_17 = (let _176_29 = (let _176_28 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _176_28 msg))
in (FStar_All.pipe_left FStar_Util.print_string _176_29))
in (FStar_All.failwith msg)))


let err_uninst = (fun env t _79_23 -> (match (_79_23) with
| (vars, ty) -> begin
(let _176_37 = (let _176_36 = (FStar_Syntax_Print.term_to_string t)
in (let _176_35 = (let _176_33 = (FStar_All.pipe_right vars (FStar_List.map Prims.fst))
in (FStar_All.pipe_right _176_33 (FStar_String.concat ", ")))
in (let _176_34 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated" _176_36 _176_35 _176_34))))
in (fail t.FStar_Syntax_Syntax.pos _176_37))
end))


let err_ill_typed_application = (fun env t args ty -> (let _176_47 = (let _176_46 = (FStar_Syntax_Print.term_to_string t)
in (let _176_45 = (let _176_43 = (FStar_All.pipe_right args (FStar_List.map (fun _79_31 -> (match (_79_31) with
| (x, _79_30) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _176_43 (FStar_String.concat " ")))
in (let _176_44 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n" _176_46 _176_45 _176_44))))
in (fail t.FStar_Syntax_Syntax.pos _176_47)))


let err_value_restriction = (fun t -> (let _176_51 = (let _176_50 = (FStar_Syntax_Print.tag_of_term t)
in (let _176_49 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Refusing to generalize because of the value restriction: (%s) %s" _176_50 _176_49)))
in (fail t.FStar_Syntax_Syntax.pos _176_51)))


let err_unexpected_eff = (fun t f0 f1 -> (let _176_56 = (let _176_55 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" _176_55 (FStar_Extraction_ML_Util.eff_to_string f0) (FStar_Extraction_ML_Util.eff_to_string f1)))
in (fail t.FStar_Syntax_Syntax.pos _176_56)))


let effect_as_etag : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.e_tag = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (

let rec delta_norm_eff = (fun g l -> (match ((FStar_Util.smap_try_find cache l.FStar_Ident.str)) with
| Some (l) -> begin
l
end
| None -> begin
(

let res = (match ((FStar_TypeChecker_Env.lookup_effect_abbrev g.FStar_Extraction_ML_UEnv.tcenv ((FStar_Syntax_Syntax.U_zero)::[]) l)) with
| None -> begin
l
end
| Some (_79_45, c) -> begin
(delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c))
end)
in (

let _79_50 = (FStar_Util.smap_add cache l.FStar_Ident.str res)
in res))
end))
in (fun g l -> (

let l = (delta_norm_eff g l)
in if (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) then begin
FStar_Extraction_ML_Syntax.E_PURE
end else begin
if (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid) then begin
FStar_Extraction_ML_Syntax.E_GHOST
end else begin
FStar_Extraction_ML_Syntax.E_IMPURE
end
end))))


type level_t =
| Term_level
| Type_level
| Kind_level


let is_Term_level = (fun _discr_ -> (match (_discr_) with
| Term_level (_) -> begin
true
end
| _ -> begin
false
end))


let is_Type_level = (fun _discr_ -> (match (_discr_) with
| Type_level (_) -> begin
true
end
| _ -> begin
false
end))


let is_Kind_level = (fun _discr_ -> (match (_discr_) with
| Kind_level (_) -> begin
true
end
| _ -> begin
false
end))


let predecessor = (fun t _79_1 -> (match (_79_1) with
| Term_level -> begin
Term_level
end
| Type_level -> begin
Term_level
end
| Kind_level -> begin
Type_level
end))


let rec level : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  level_t = (fun env t -> (

let predecessor = (fun l -> (predecessor t l))
in (

let t = (FStar_Syntax_Subst.compress t)
in (

let _79_67 = (FStar_Extraction_ML_UEnv.debug env (fun _79_65 -> (let _176_78 = (FStar_Syntax_Print.term_to_string t)
in (let _176_77 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "level %s (%s)\n" _176_78 _176_77)))))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_79_70) -> begin
(let _176_83 = (let _176_82 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: %s" _176_82))
in (FStar_All.failwith _176_83))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
Kind_level
end
| FStar_Syntax_Syntax.Tm_constant (_79_74) -> begin
Term_level
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _79_82; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_unfoldable (_79_79); FStar_Syntax_Syntax.fv_qual = _79_77}) -> begin
(

let t' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Iota))::[]) env.FStar_Extraction_ML_UEnv.tcenv t)
in (

let _79_87 = (FStar_Extraction_ML_UEnv.debug env (fun _79_86 -> (match (()) with
| () -> begin
(let _176_86 = (FStar_Syntax_Print.term_to_string t)
in (let _176_85 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Normalized %s to %s\n" _176_86 _176_85)))
end)))
in (level env t')))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
if (FStar_TypeChecker_Env.is_type_constructor env.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) then begin
Type_level
end else begin
(let _176_87 = (level env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (FStar_All.pipe_left predecessor _176_87))
end
end
| (FStar_Syntax_Syntax.Tm_uvar (_, t)) | (FStar_Syntax_Syntax.Tm_bvar ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})) | (FStar_Syntax_Syntax.Tm_name ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})) -> begin
(let _176_88 = (level env t)
in (FStar_All.pipe_left predecessor _176_88))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _79_110, _79_112) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_type (_79_116) -> begin
Kind_level
end
| FStar_Syntax_Syntax.Tm_uinst (t, _79_120) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_refine (x, _79_125) -> begin
(match ((level env x.FStar_Syntax_Syntax.sort)) with
| Term_level -> begin
Type_level
end
| l -> begin
l
end)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match ((level env (FStar_Syntax_Util.comp_result c))) with
| Term_level -> begin
Type_level
end
| l -> begin
l
end)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _79_139) -> begin
(level env body)
end
| FStar_Syntax_Syntax.Tm_let (_79_143, body) -> begin
(level env body)
end
| FStar_Syntax_Syntax.Tm_match (_79_148, branches) -> begin
(match (branches) with
| ((_79_155, _79_157, e))::_79_153 -> begin
(level env e)
end
| _79_162 -> begin
(FStar_All.failwith "Empty branches")
end)
end
| FStar_Syntax_Syntax.Tm_meta (t, _79_165) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_app (head, _79_170) -> begin
(level env head)
end)))))


let is_type : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((level env t)) with
| Term_level -> begin
false
end
| _79_177 -> begin
true
end))


let is_type_binder = (fun env x -> (match ((level env (Prims.fst x).FStar_Syntax_Syntax.sort)) with
| Term_level -> begin
(FStar_All.failwith "Impossible: Binder is a term")
end
| Type_level -> begin
false
end
| Kind_level -> begin
true
end))


let is_constructor : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _176_97 = (FStar_Syntax_Subst.compress t)
in _176_97.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _79_203 -> begin
false
end))


let rec is_fstar_value : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _176_100 = (FStar_Syntax_Subst.compress t)
in _176_100.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
if (is_constructor head) then begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _79_224 -> (match (_79_224) with
| (te, _79_223) -> begin
(is_fstar_value te)
end))))
end else begin
false
end
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t, _, _)) -> begin
(is_fstar_value t)
end
| _79_237 -> begin
false
end))


let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Fun (_)) -> begin
true
end
| (FStar_Extraction_ML_Syntax.MLE_CTor (_, exps)) | (FStar_Extraction_ML_Syntax.MLE_Tuple (exps)) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (_79_258, fields) -> begin
(FStar_Util.for_all (fun _79_265 -> (match (_79_265) with
| (_79_263, e) -> begin
(is_ml_value e)
end)) fields)
end
| _79_267 -> begin
false
end))


let normalize_abs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t0 -> (

let rec aux = (fun bs t copt -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs', body, copt) -> begin
(aux (FStar_List.append bs bs') body copt)
end
| _79_280 -> begin
(

let e' = (FStar_Syntax_Util.unascribe t)
in if (FStar_Syntax_Util.is_fun e') then begin
(aux bs e' copt)
end else begin
(FStar_Syntax_Util.abs bs e' copt)
end)
end)))
in (aux [] t0 None)))


let unit_binder : FStar_Syntax_Syntax.binder = (let _176_113 = (FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _176_113))


let check_pats_for_ite : (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term Prims.option) = (fun l -> (

let def = ((false), (None), (None))
in if ((FStar_List.length l) <> (Prims.parse_int "2")) then begin
def
end else begin
(

let _79_287 = (FStar_List.hd l)
in (match (_79_287) with
| (p1, w1, e1) -> begin
(

let _79_291 = (let _176_116 = (FStar_List.tl l)
in (FStar_List.hd _176_116))
in (match (_79_291) with
| (p2, w2, e2) -> begin
(match (((w1), (w2), (p1.FStar_Syntax_Syntax.v), (p2.FStar_Syntax_Syntax.v))) with
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
((true), (Some (e1)), (Some (e2)))
end
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
((true), (Some (e2)), (Some (e1)))
end
| _79_311 -> begin
def
end)
end))
end))
end))


let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))


let erasable : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g f t -> ((f = FStar_Extraction_ML_Syntax.E_GHOST) || ((f = FStar_Extraction_ML_Syntax.E_PURE) && (erasableType g t))))


let erase : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e ty f -> (

let e = if (erasable g f ty) then begin
if (type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
FStar_Extraction_ML_Syntax.ml_unit
end else begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) (FStar_Extraction_ML_Syntax.MLE_Coerce (((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.ml_unit_ty), (ty)))))
end
end else begin
e
end
in ((e), (f), (ty))))


let maybe_coerce : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e ty expect -> (

let ty = (eraseTypeDeep g ty)
in (match ((type_leq_c g (Some (e)) ty expect)) with
| (true, Some (e')) -> begin
e'
end
| _79_332 -> begin
(

let _79_334 = (FStar_Extraction_ML_UEnv.debug g (fun _79_333 -> (match (()) with
| () -> begin
(let _176_146 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (let _176_145 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (let _176_144 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule expect)
in (FStar_Util.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n" _176_146 _176_145 _176_144))))
end)))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (ty), (expect))))))
end)))


let bv_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bv -> (match ((FStar_Extraction_ML_UEnv.lookup_bv g bv)) with
| FStar_Util.Inl (_79_339, t) -> begin
t
end
| _79_344 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end))


let rec term_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlty' g t)))
and term_as_mlty' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun env t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _176_167 = (let _176_166 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Impossible: Unexpected term %s" _176_166))
in (FStar_All.failwith _176_167))
end
| FStar_Syntax_Syntax.Tm_uvar (_79_362) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}, _)) | (FStar_Syntax_Syntax.Tm_uinst (t, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t, _, _)) -> begin
(term_as_mlty' env t)
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv [])
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _79_398 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_79_398) with
| (bs, c) -> begin
(

let _79_401 = (binders_as_ml_binders env bs)
in (match (_79_401) with
| (mlbs, env) -> begin
(

let t_ret = (

let eff = (FStar_TypeChecker_Env.norm_eff_name env.FStar_Extraction_ML_UEnv.tcenv (FStar_Syntax_Util.comp_effect_name c))
in (

let ed = (FStar_TypeChecker_Env.get_effect_decl env.FStar_Extraction_ML_UEnv.tcenv eff)
in if (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) then begin
(

let t = (FStar_TypeChecker_Util.reify_comp env.FStar_Extraction_ML_UEnv.tcenv (FStar_Syntax_Util.lcomp_of_comp c) FStar_Syntax_Syntax.U_unknown)
in (

let res = (term_as_mlty' env t)
in res))
end else begin
(term_as_mlty' env (FStar_Syntax_Util.comp_result c))
end))
in (

let erase = (effect_as_etag env (FStar_Syntax_Util.comp_effect_name c))
in (

let _79_418 = (FStar_List.fold_right (fun _79_411 _79_414 -> (match (((_79_411), (_79_414))) with
| ((_79_409, t), (tag, t')) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((t), (tag), (t')))))
end)) mlbs ((erase), (t_ret)))
in (match (_79_418) with
| (_79_416, t) -> begin
t
end))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let res = (match ((let _176_170 = (FStar_Syntax_Util.un_uinst head)
in _176_170.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv args)
end
| FStar_Syntax_Syntax.Tm_app (head, args') -> begin
(let _176_171 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head), ((FStar_List.append args' args))))) None t.FStar_Syntax_Syntax.pos)
in (term_as_mlty' env _176_171))
end
| _79_432 -> begin
FStar_Extraction_ML_UEnv.unknownType
end)
in res)
end
| FStar_Syntax_Syntax.Tm_abs (bs, ty, _79_437) -> begin
(

let _79_442 = (FStar_Syntax_Subst.open_term bs ty)
in (match (_79_442) with
| (bs, ty) -> begin
(

let _79_445 = (binders_as_ml_binders env bs)
in (match (_79_445) with
| (bts, env) -> begin
(term_as_mlty' env ty)
end))
end))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
FStar_Extraction_ML_UEnv.unknownType
end)))
and arg_as_mlty : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  FStar_Extraction_ML_Syntax.mlty = (fun g _79_459 -> (match (_79_459) with
| (a, _79_458) -> begin
if (is_type g a) then begin
(term_as_mlty' g a)
end else begin
FStar_Extraction_ML_UEnv.erasedContent
end
end))
and fv_app_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.args  ->  FStar_Extraction_ML_Syntax.mlty = (fun g fv args -> (

let _79_465 = (FStar_Syntax_Util.arrow_formals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (match (_79_465) with
| (formals, t) -> begin
(

let mlargs = (FStar_List.map (arg_as_mlty g) args)
in (

let mlargs = (

let n_args = (FStar_List.length args)
in if ((FStar_List.length formals) > n_args) then begin
(

let _79_471 = (FStar_Util.first_N n_args formals)
in (match (_79_471) with
| (_79_469, rest) -> begin
(let _176_178 = (FStar_List.map (fun _79_472 -> FStar_Extraction_ML_UEnv.erasedContent) rest)
in (FStar_List.append mlargs _176_178))
end))
end else begin
mlargs
end)
in (let _176_180 = (let _176_179 = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in ((mlargs), (_176_179)))
in FStar_Extraction_ML_Syntax.MLTY_Named (_176_180))))
end)))
and binders_as_ml_binders : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list * FStar_Extraction_ML_UEnv.env) = (fun g bs -> (

let _79_490 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _79_479 b -> (match (_79_479) with
| (ml_bs, env) -> begin
if (is_type_binder g b) then begin
(

let b = (Prims.fst b)
in (

let env = (FStar_Extraction_ML_UEnv.extend_ty env b (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (

let ml_b = (let _176_185 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b)
in ((_176_185), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
in (((ml_b)::ml_bs), (env)))))
end else begin
(

let b = (Prims.fst b)
in (

let t = (term_as_mlty env b.FStar_Syntax_Syntax.sort)
in (

let env = (FStar_Extraction_ML_UEnv.extend_bv env b (([]), (t)) false false false)
in (

let ml_b = (let _176_186 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b)
in ((_176_186), (t)))
in (((ml_b)::ml_bs), (env))))))
end
end)) (([]), (g))))
in (match (_79_490) with
| (ml_bs, env) -> begin
(((FStar_List.rev ml_bs)), (env))
end)))


let mk_MLE_Seq : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun e1 e2 -> (match (((e1.FStar_Extraction_ML_Syntax.expr), (e2.FStar_Extraction_ML_Syntax.expr))) with
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 es2))
end
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), _79_501) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 ((e2)::[])))
end
| (_79_504, FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::es2)
end
| _79_509 -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::(e2)::[])
end))


let mk_MLE_Let : Prims.bool  ->  FStar_Extraction_ML_Syntax.mlletbinding  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun top_level lbs body -> (match (lbs) with
| (FStar_Extraction_ML_Syntax.NoLetQualifier, (lb)::[]) when (not (top_level)) -> begin
(match (lb.FStar_Extraction_ML_Syntax.mllb_tysc) with
| Some ([], t) when (t = FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
if (body.FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr) then begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end else begin
(match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Var (x) when (x = lb.FStar_Extraction_ML_Syntax.mllb_name) -> begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end
| _79_524 when (lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr) -> begin
body.FStar_Extraction_ML_Syntax.expr
end
| _79_526 -> begin
(mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def body)
end)
end
end
| _79_528 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end)
end
| _79_530 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end))


let resugar_pat : FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_ML_Syntax.mlpattern = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(match ((FStar_Extraction_ML_Util.is_xtuple d)) with
| Some (n) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| _79_540 -> begin
(match (q) with
| Some (FStar_Syntax_Syntax.Record_ctor (_79_542, fns)) -> begin
(

let p = (FStar_Extraction_ML_Util.record_field_path fns)
in (

let fs = (FStar_Extraction_ML_Util.record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record (((p), (fs)))))
end
| _79_550 -> begin
p
end)
end)
end
| _79_552 -> begin
p
end))


let extract_pat : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option) Prims.list * Prims.bool) = (fun g p expected_t -> (

let rec extract_one_pat = (fun disjunctive_pat imp g p expected_topt -> (

let ok = (fun t -> (match (expected_topt) with
| None -> begin
true
end
| Some (t') -> begin
(type_leq g t t')
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_79_568) -> begin
(FStar_All.failwith "Impossible: Nested disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int (c, None)) -> begin
(

let i = FStar_Const.Const_int (((c), (None)))
in (

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let when_clause = (let _176_227 = (let _176_226 = (let _176_225 = (let _176_224 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (let _176_223 = (let _176_222 = (let _176_221 = (let _176_220 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p i)
in (FStar_All.pipe_left (fun _176_219 -> FStar_Extraction_ML_Syntax.MLE_Const (_176_219)) _176_220))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) _176_221))
in (_176_222)::[])
in (_176_224)::_176_223))
in ((FStar_Extraction_ML_Util.prims_op_equality), (_176_225)))
in FStar_Extraction_ML_Syntax.MLE_App (_176_226))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _176_227))
in (let _176_228 = (ok FStar_Extraction_ML_Syntax.ml_int_ty)
in ((g), (Some (((FStar_Extraction_ML_Syntax.MLP_Var (x)), ((when_clause)::[])))), (_176_228))))))
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(

let t = (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange s)
in (

let mlty = (term_as_mlty g t)
in (let _176_233 = (let _176_231 = (let _176_230 = (let _176_229 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (_176_229))
in ((_176_230), ([])))
in Some (_176_231))
in (let _176_232 = (ok mlty)
in ((g), (_176_233), (_176_232))))))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let g = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (let _176_238 = if imp then begin
None
end else begin
(let _176_236 = (let _176_235 = (let _176_234 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in FStar_Extraction_ML_Syntax.MLP_Var (_176_234))
in ((_176_235), ([])))
in Some (_176_236))
end
in (let _176_237 = (ok mlty)
in ((g), (_176_238), (_176_237))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) when disjunctive_pat -> begin
((g), (Some (((FStar_Extraction_ML_Syntax.MLP_Wild), ([])))), (true))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let g = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (let _176_243 = if imp then begin
None
end else begin
(let _176_241 = (let _176_240 = (let _176_239 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in FStar_Extraction_ML_Syntax.MLP_Var (_176_239))
in ((_176_240), ([])))
in Some (_176_241))
end
in (let _176_242 = (ok mlty)
in ((g), (_176_243), (_176_242))))))
end
| FStar_Syntax_Syntax.Pat_dot_term (_79_593) -> begin
((g), (None), (true))
end
| FStar_Syntax_Syntax.Pat_cons (f, pats) -> begin
(

let _79_615 = (match ((FStar_Extraction_ML_UEnv.lookup_fv g f)) with
| FStar_Util.Inr ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n); FStar_Extraction_ML_Syntax.mlty = _79_602; FStar_Extraction_ML_Syntax.loc = _79_600}, ttys, _79_608) -> begin
((n), (ttys))
end
| _79_612 -> begin
(FStar_All.failwith "Expected a constructor")
end)
in (match (_79_615) with
| (d, tys) -> begin
(

let nTyVars = (FStar_List.length (Prims.fst tys))
in (

let _79_619 = (FStar_Util.first_N nTyVars pats)
in (match (_79_619) with
| (tysVarPats, restPats) -> begin
(

let pat_ty_compat = (match (expected_topt) with
| None -> begin
true
end
| Some (expected_t) -> begin
try
(match (()) with
| () -> begin
(

let mlty_args = (FStar_All.pipe_right tysVarPats (FStar_List.map (fun _79_632 -> (match (_79_632) with
| (p, _79_631) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (_79_634, t) -> begin
(term_as_mlty g t)
end
| _79_639 -> begin
(Prims.raise Un_extractable)
end)
end))))
in (

let pat_ty = (FStar_Extraction_ML_Util.subst tys mlty_args)
in (type_leq g pat_ty expected_t)))
end)
with
| Un_extractable -> begin
false
end
end)
in (

let _79_654 = (FStar_Util.fold_map (fun g _79_646 -> (match (_79_646) with
| (p, imp) -> begin
(

let _79_651 = (extract_one_pat disjunctive_pat true g p None)
in (match (_79_651) with
| (g, p, _79_650) -> begin
((g), (p))
end))
end)) g tysVarPats)
in (match (_79_654) with
| (g, tyMLPats) -> begin
(

let _79_666 = (FStar_Util.fold_map (fun g _79_658 -> (match (_79_658) with
| (p, imp) -> begin
(

let _79_663 = (extract_one_pat disjunctive_pat false g p None)
in (match (_79_663) with
| (g, p, _79_662) -> begin
((g), (p))
end))
end)) g restPats)
in (match (_79_666) with
| (g, restMLPats) -> begin
(

let _79_674 = (let _176_252 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun _79_2 -> (match (_79_2) with
| Some (x) -> begin
(x)::[]
end
| _79_671 -> begin
[]
end))))
in (FStar_All.pipe_right _176_252 FStar_List.split))
in (match (_79_674) with
| (mlPats, when_clauses) -> begin
(let _176_256 = (let _176_255 = (let _176_254 = (resugar_pat f.FStar_Syntax_Syntax.fv_qual (FStar_Extraction_ML_Syntax.MLP_CTor (((d), (mlPats)))))
in (let _176_253 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in ((_176_254), (_176_253))))
in Some (_176_255))
in ((g), (_176_256), (pat_ty_compat)))
end))
end))
end)))
end)))
end))
end)))
in (

let extract_one_pat = (fun disj g p expected_t -> (match ((extract_one_pat disj false g p expected_t)) with
| (g, Some (x, v), b) -> begin
((g), (((x), (v))), (b))
end
| _79_688 -> begin
(FStar_All.failwith "Impossible: Unable to translate pattern")
end))
in (

let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| (hd)::tl -> begin
(let _176_267 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl)
in Some (_176_267))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: Empty disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_disj ((p)::pats) -> begin
(

let _79_704 = (extract_one_pat true g p (Some (expected_t)))
in (match (_79_704) with
| (g, p, b) -> begin
(

let _79_714 = (FStar_Util.fold_map (fun b p -> (

let _79_711 = (extract_one_pat true g p (Some (expected_t)))
in (match (_79_711) with
| (_79_708, p, b') -> begin
(((b && b')), (p))
end))) b pats)
in (match (_79_714) with
| (b, ps) -> begin
(

let ps = (p)::ps
in (

let _79_729 = (FStar_All.pipe_right ps (FStar_List.partition (fun _79_3 -> (match (_79_3) with
| (_79_718, (_79_722)::_79_720) -> begin
true
end
| _79_726 -> begin
false
end))))
in (match (_79_729) with
| (ps_when, rest) -> begin
(

let ps = (FStar_All.pipe_right ps_when (FStar_List.map (fun _79_732 -> (match (_79_732) with
| (x, whens) -> begin
(let _176_272 = (mk_when_clause whens)
in ((x), (_176_272)))
end))))
in (

let res = (match (rest) with
| [] -> begin
((g), (ps), (b))
end
| rest -> begin
(let _176_276 = (let _176_275 = (let _176_274 = (let _176_273 = (FStar_List.map Prims.fst rest)
in FStar_Extraction_ML_Syntax.MLP_Branch (_176_273))
in ((_176_274), (None)))
in (_176_275)::ps)
in ((g), (_176_276), (b)))
end)
in res))
end)))
end))
end))
end
| _79_738 -> begin
(

let _79_744 = (extract_one_pat false g p (Some (expected_t)))
in (match (_79_744) with
| (g, (p, whens), b) -> begin
(

let when_clause = (mk_when_clause whens)
in ((g), ((((p), (when_clause)))::[]), (b)))
end))
end)))))


let maybe_eta_data_and_project_record : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (

let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, _79_755, t1) -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _176_291 = (let _176_290 = (let _176_289 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((((x), (t0))), (_176_289)))
in (_176_290)::more_args)
in (eta_args _176_291 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_79_761, _79_763) -> begin
(((FStar_List.rev more_args)), (t))
end
| _79_767 -> begin
(FStar_All.failwith "Impossible: Head type is not an arrow")
end))
in (

let as_record = (fun qual e -> (match (((e.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (_79_772, args), Some (FStar_Syntax_Syntax.Record_ctor (_79_777, fields))) -> begin
(

let path = (FStar_Extraction_ML_Util.record_field_path fields)
in (

let fields = (FStar_Extraction_ML_Util.record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record (((path), (fields)))))))
end
| _79_786 -> begin
e
end))
in (

let resugar_and_maybe_eta = (fun qual e -> (

let _79_792 = (eta_args [] residualType)
in (match (_79_792) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(let _176_300 = (as_record qual e)
in (FStar_Extraction_ML_Util.resugar_exp _176_300))
end
| _79_795 -> begin
(

let _79_798 = (FStar_List.unzip eargs)
in (match (_79_798) with
| (binders, eargs) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head, args) -> begin
(

let body = (let _176_302 = (let _176_301 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor (((head), ((FStar_List.append args eargs))))))
in (FStar_All.pipe_left (as_record qual) _176_301))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp _176_302))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun (((binders), (body))))))
end
| _79_805 -> begin
(FStar_All.failwith "Impossible: Not a constructor")
end)
end))
end)
end)))
in (match (((mlAppExpr.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (_79_807, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _79_813; FStar_Extraction_ML_Syntax.loc = _79_811}, (mle)::args), Some (FStar_Syntax_Syntax.Record_projector (f))) -> begin
(

let fn = (FStar_Extraction_ML_Util.mlpath_of_lid f)
in (

let proj = FStar_Extraction_ML_Syntax.MLE_Proj (((mle), (fn)))
in (

let e = (match (args) with
| [] -> begin
proj
end
| _79_830 -> begin
(let _176_304 = (let _176_303 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in ((_176_303), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (_176_304))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e))))
end
| ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _176_305 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _176_305))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _176_306 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _176_306))
end
| _79_870 -> begin
mlAppExpr
end)))))


let maybe_downgrade_eff : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag = (fun g f t -> if ((f = FStar_Extraction_ML_Syntax.E_GHOST) && (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty)) then begin
FStar_Extraction_ML_Syntax.E_PURE
end else begin
f
end)


let rec term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g t -> (

let _79_879 = (term_as_mlexpr' g t)
in (match (_79_879) with
| (e, tag, ty) -> begin
(

let tag = (maybe_downgrade_eff g tag ty)
in (

let _79_882 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (let _176_331 = (let _176_330 = (FStar_Syntax_Print.tag_of_term t)
in (let _176_329 = (FStar_Syntax_Print.term_to_string t)
in (let _176_328 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format4 "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n" _176_330 _176_329 _176_328 (FStar_Extraction_ML_Util.eff_to_string tag)))))
in (FStar_Util.print_string _176_331))))
in (erase g e ty tag)))
end)))
and check_term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g t f ty -> (

let _79_890 = (check_term_as_mlexpr' g t f ty)
in (match (_79_890) with
| (e, t) -> begin
(

let _79_895 = (erase g e t f)
in (match (_79_895) with
| (r, _79_893, t) -> begin
((r), (t))
end))
end)))
and check_term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g e0 f ty -> (

let _79_903 = (term_as_mlexpr g e0)
in (match (_79_903) with
| (e, tag, t) -> begin
(

let tag = (maybe_downgrade_eff g tag t)
in if (FStar_Extraction_ML_Util.eff_leq tag f) then begin
(let _176_340 = (maybe_coerce g e t ty)
in ((_176_340), (ty)))
end else begin
(err_unexpected_eff e0 f tag)
end)
end)))
and term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g top -> (

let _79_908 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (let _176_347 = (let _176_346 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _176_345 = (FStar_Syntax_Print.tag_of_term top)
in (let _176_344 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format3 "%s: term_as_mlexpr\' (%s) :  %s \n" _176_346 _176_345 _176_344))))
in (FStar_Util.print_string _176_347))))
in (

let t = (FStar_Syntax_Subst.compress top)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) -> begin
(let _176_349 = (let _176_348 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" _176_348))
in (FStar_All.failwith _176_349))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc)) -> begin
(match ((term_as_mlexpr' g t)) with
| ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let ((FStar_Extraction_ML_Syntax.NoLetQualifier, bodies), continuation); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}, tag, typ) -> begin
(({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let (((((FStar_Extraction_ML_Syntax.Mutable), (bodies))), (continuation))); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}), (tag), (typ))
end
| _79_948 -> begin
(FStar_All.failwith "impossible")
end)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, _79_952)) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) when (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl g.FStar_Extraction_ML_UEnv.tcenv m)
in if (let _176_350 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right _176_350 Prims.op_Negation)) then begin
(term_as_mlexpr' g t)
end else begin
(

let ml_result_ty_1 = (term_as_mlty g lb.FStar_Syntax_Syntax.lbtyp)
in (

let _79_972 = (term_as_mlexpr g lb.FStar_Syntax_Syntax.lbdef)
in (match (_79_972) with
| (comp_1, _79_969, _79_971) -> begin
(

let _79_991 = (

let k = (let _176_353 = (let _176_352 = (let _176_351 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_All.pipe_right _176_351 FStar_Syntax_Syntax.mk_binder))
in (_176_352)::[])
in (FStar_Syntax_Util.abs _176_353 body None))
in (

let _79_978 = (term_as_mlexpr g k)
in (match (_79_978) with
| (ml_k, _79_976, t_k) -> begin
(

let m_2 = (match (t_k) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_79_980, _79_982, m_2) -> begin
m_2
end
| _79_987 -> begin
(FStar_All.failwith "Impossible")
end)
in ((ml_k), (m_2)))
end)))
in (match (_79_991) with
| (ml_k, ty) -> begin
(

let bind = (let _176_356 = (let _176_355 = (let _176_354 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (FStar_All.pipe_right _176_354 Prims.fst))
in FStar_Extraction_ML_Syntax.MLE_Name (_176_355))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _176_356))
in (let _176_357 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) (FStar_Extraction_ML_Syntax.MLE_App (((bind), ((comp_1)::(ml_k)::[])))))
in ((_176_357), (FStar_Extraction_ML_Syntax.E_IMPURE), (ty))))
end))
end)))
end)
end
| _79_994 -> begin
(term_as_mlexpr' g t)
end))
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_uinst (t, _)) -> begin
(term_as_mlexpr' g t)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let _79_1011 = (FStar_TypeChecker_TcTerm.type_of_tot_term g.FStar_Extraction_ML_UEnv.tcenv t)
in (match (_79_1011) with
| (_79_1007, ty, _79_1010) -> begin
(

let ml_ty = (term_as_mlty g ty)
in (let _176_361 = (let _176_360 = (let _176_359 = (FStar_Extraction_ML_Util.mlconst_of_const' t.FStar_Syntax_Syntax.pos c)
in (FStar_All.pipe_left (fun _176_358 -> FStar_Extraction_ML_Syntax.MLE_Const (_176_358)) _176_359))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty _176_360))
in ((_176_361), (FStar_Extraction_ML_Syntax.E_PURE), (ml_ty))))
end))
end
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
if (is_type g t) then begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end else begin
(match ((FStar_Extraction_ML_UEnv.lookup_term g t)) with
| (FStar_Util.Inl (_79_1020), _79_1023) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| (FStar_Util.Inr (x, mltys, _79_1028), qual) -> begin
(match (mltys) with
| ([], t) when (t = FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t))
end
| ([], t) -> begin
(let _176_362 = (maybe_eta_data_and_project_record g qual t x)
in ((_176_362), (FStar_Extraction_ML_Syntax.E_PURE), (t)))
end
| _79_1040 -> begin
(err_uninst g t mltys)
end)
end)
end
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, copt) -> begin
(

let _79_1048 = (FStar_Syntax_Subst.open_term bs body)
in (match (_79_1048) with
| (bs, body) -> begin
(

let _79_1051 = (binders_as_ml_binders g bs)
in (match (_79_1051) with
| (ml_bs, env) -> begin
(

let _79_1055 = (term_as_mlexpr env body)
in (match (_79_1055) with
| (ml_body, f, t) -> begin
(

let _79_1065 = (FStar_List.fold_right (fun _79_1059 _79_1062 -> (match (((_79_1059), (_79_1062))) with
| ((_79_1057, targ), (f, t)) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((targ), (f), (t)))))
end)) ml_bs ((f), (t)))
in (match (_79_1065) with
| (f, tfun) -> begin
(let _176_365 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun (((ml_bs), (ml_body)))))
in ((_176_365), (f), (tfun)))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _79_1071; FStar_Syntax_Syntax.pos = _79_1069; FStar_Syntax_Syntax.vars = _79_1067}, (t)::[]) -> begin
(

let _79_1082 = (term_as_mlexpr' g (Prims.fst t))
in (match (_79_1082) with
| (ml, e_tag, mlty) -> begin
((ml), (FStar_Extraction_ML_Syntax.E_PURE), (mlty))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_79_1090)); FStar_Syntax_Syntax.tk = _79_1088; FStar_Syntax_Syntax.pos = _79_1086; FStar_Syntax_Syntax.vars = _79_1084}, (t)::[]) -> begin
(

let _79_1101 = (term_as_mlexpr' g (Prims.fst t))
in (match (_79_1101) with
| (ml, e_tag, mlty) -> begin
((ml), (FStar_Extraction_ML_Syntax.E_IMPURE), (mlty))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (_79_1107) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t))
end
| _79_1111 -> begin
(

let rec extract_app = (fun is_data _79_1116 _79_1119 restArgs -> (match (((_79_1116), (_79_1119))) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match (((restArgs), (t))) with
| ([], _79_1123) -> begin
(

let evaluation_order_guaranteed = ((((FStar_List.length mlargs_f) = (Prims.parse_int "1")) || (FStar_Extraction_ML_Util.codegen_fsharp ())) || (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = {FStar_Syntax_Syntax.v = v; FStar_Syntax_Syntax.ty = _79_1132; FStar_Syntax_Syntax.p = _79_1130}; FStar_Syntax_Syntax.fv_delta = _79_1128; FStar_Syntax_Syntax.fv_qual = _79_1126}) -> begin
((v = FStar_Syntax_Const.op_And) || (v = FStar_Syntax_Const.op_Or))
end
| _79_1138 -> begin
false
end))
in (

let _79_1149 = if evaluation_order_guaranteed then begin
(let _176_374 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in (([]), (_176_374)))
end else begin
(FStar_List.fold_left (fun _79_1142 _79_1145 -> (match (((_79_1142), (_79_1145))) with
| ((lbs, out_args), (arg, f)) -> begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) || (f = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
((lbs), ((arg)::out_args))
end else begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _176_378 = (let _176_377 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (_176_377)::out_args)
in (((((x), (arg)))::lbs), (_176_378))))
end
end)) (([]), ([])) mlargs_f)
end
in (match (_79_1149) with
| (lbs, mlargs) -> begin
(

let app = (let _176_379 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_App (((mlhead), (mlargs)))))
in (FStar_All.pipe_left (maybe_eta_data_and_project_record g is_data t) _176_379))
in (

let l_app = (FStar_List.fold_right (fun _79_1153 out -> (match (_79_1153) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.mlty) (mk_MLE_Let false ((FStar_Extraction_ML_Syntax.NoLetQualifier), (({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = Some ((([]), (arg.FStar_Extraction_ML_Syntax.mlty))); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg; FStar_Extraction_ML_Syntax.print_typ = true})::[])) out))
end)) lbs app)
in ((l_app), (f), (t))))
end)))
end
| (((arg, _79_1159))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (formal_t, f', t)) when (is_type g arg) -> begin
if (type_leq g formal_t FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
(let _176_383 = (let _176_382 = (FStar_Extraction_ML_Util.join arg.FStar_Syntax_Syntax.pos f f')
in ((_176_382), (t)))
in (extract_app is_data ((mlhead), ((((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE)))::mlargs_f)) _176_383 rest))
end else begin
(let _176_388 = (let _176_387 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule mlhead)
in (let _176_386 = (FStar_Syntax_Print.term_to_string arg)
in (let _176_385 = (FStar_Syntax_Print.tag_of_term arg)
in (let _176_384 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule formal_t)
in (FStar_Util.format4 "Impossible: ill-typed application:\n\thead=%s, arg=%s, tag=%s\n\texpected type unit, got %s" _176_387 _176_386 _176_385 _176_384)))))
in (FStar_All.failwith _176_388))
end
end
| (((e0, _79_1171))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t)) -> begin
(

let r = e0.FStar_Syntax_Syntax.pos
in (

let _79_1184 = (term_as_mlexpr g e0)
in (match (_79_1184) with
| (e0, f0, tInferred) -> begin
(

let e0 = (maybe_coerce g e0 tInferred tExpected)
in (let _176_390 = (let _176_389 = (FStar_Extraction_ML_Util.join_l r ((f)::(f')::(f0)::[]))
in ((_176_389), (t)))
in (extract_app is_data ((mlhead), ((((e0), (f0)))::mlargs_f)) _176_390 rest)))
end)))
end
| _79_1187 -> begin
(match ((FStar_Extraction_ML_Util.udelta_unfold g t)) with
| Some (t) -> begin
(extract_app is_data ((mlhead), (mlargs_f)) ((f), (t)) restArgs)
end
| None -> begin
(err_ill_typed_application g top restArgs t)
end)
end)
end))
in (

let extract_app_maybe_projector = (fun is_data mlhead _79_1196 args -> (match (_79_1196) with
| (f, t) -> begin
(match (is_data) with
| Some (FStar_Syntax_Syntax.Record_projector (_79_1199)) -> begin
(

let rec remove_implicits = (fun args f t -> (match (((args), (t))) with
| (((a0, Some (FStar_Syntax_Syntax.Implicit (_79_1209))))::args, FStar_Extraction_ML_Syntax.MLTY_Fun (_79_1215, f', t)) -> begin
(let _176_405 = (FStar_Extraction_ML_Util.join a0.FStar_Syntax_Syntax.pos f f')
in (remove_implicits args _176_405 t))
end
| _79_1222 -> begin
((args), (f), (t))
end))
in (

let _79_1226 = (remove_implicits args f t)
in (match (_79_1226) with
| (args, f, t) -> begin
(extract_app is_data ((mlhead), ([])) ((f), (t)) args)
end)))
end
| _79_1228 -> begin
(extract_app is_data ((mlhead), ([])) ((f), (t)) args)
end)
end))
in if (is_type g t) then begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end else begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let _79_1249 = (match ((FStar_Extraction_ML_UEnv.lookup_term g head)) with
| (FStar_Util.Inr (u), q) -> begin
((u), (q))
end
| _79_1241 -> begin
(FStar_All.failwith "FIXME Ty")
end)
in (match (_79_1249) with
| ((head_ml, (vars, t), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, _79_1254))::_79_1251 -> begin
(is_type g a)
end
| _79_1258 -> begin
false
end)
in (

let _79_1304 = (match (vars) with
| (_79_1263)::_79_1261 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t), (args))
end
| _79_1266 -> begin
(

let n = (FStar_List.length vars)
in if (n <= (FStar_List.length args)) then begin
(

let _79_1270 = (FStar_Util.first_N n args)
in (match (_79_1270) with
| (prefix, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun _79_1274 -> (match (_79_1274) with
| (x, _79_1273) -> begin
(term_as_mlty g x)
end)) prefix)
in (

let t = (instantiate ((vars), (t)) prefixAsMLTypes)
in (

let head = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) -> begin
(

let _79_1283 = head_ml
in {FStar_Extraction_ML_Syntax.expr = _79_1283.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t; FStar_Extraction_ML_Syntax.loc = _79_1283.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = _79_1289; FStar_Extraction_ML_Syntax.loc = _79_1287})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let _79_1296 = head
in {FStar_Extraction_ML_Syntax.expr = _79_1296.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t))); FStar_Extraction_ML_Syntax.loc = _79_1296.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t))
end
| _79_1299 -> begin
(FStar_All.failwith "Impossible: Unexpected head term")
end)
in ((head), (t), (rest)))))
end))
end else begin
(err_uninst g head ((vars), (t)))
end)
end)
in (match (_79_1304) with
| (head_ml, head_t, args) -> begin
(match (args) with
| [] -> begin
(let _176_407 = (maybe_eta_data_and_project_record g qual head_t head_ml)
in ((_176_407), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| _79_1307 -> begin
(extract_app_maybe_projector qual head_ml ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args)
end)
end)))
end))
end
| _79_1309 -> begin
(

let _79_1313 = (term_as_mlexpr g head)
in (match (_79_1313) with
| (head, f, t) -> begin
(extract_app_maybe_projector None head ((f), (t)) args)
end))
end))
end))
end)
end
| FStar_Syntax_Syntax.Tm_ascribed (e0, tc, f) -> begin
(

let t = (match (tc) with
| FStar_Util.Inl (t) -> begin
(term_as_mlty g t)
end
| FStar_Util.Inr (c) -> begin
(term_as_mlty g (FStar_Syntax_Util.comp_result c))
end)
in (

let f = (match (f) with
| None -> begin
(FStar_All.failwith "Ascription node with an empty effect label")
end
| Some (l) -> begin
(effect_as_etag g l)
end)
in (

let _79_1330 = (check_term_as_mlexpr g e0 f t)
in (match (_79_1330) with
| (e, t) -> begin
((e), (f), (t))
end))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') -> begin
(

let top_level = (FStar_Syntax_Syntax.is_top_level lbs)
in (

let _79_1346 = if is_rec then begin
(FStar_Syntax_Subst.open_let_rec lbs e')
end else begin
if (FStar_Syntax_Syntax.is_top_level lbs) then begin
((lbs), (e'))
end else begin
(

let lb = (FStar_List.hd lbs)
in (

let x = (let _176_408 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv _176_408))
in (

let lb = (

let _79_1340 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _79_1340.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _79_1340.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _79_1340.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _79_1340.FStar_Syntax_Syntax.lbdef})
in (

let e' = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x))))::[]) e')
in (((lb)::[]), (e'))))))
end
end
in (match (_79_1346) with
| (lbs, e') -> begin
(

let maybe_generalize = (fun _79_1354 -> (match (_79_1354) with
| {FStar_Syntax_Syntax.lbname = lbname_; FStar_Syntax_Syntax.lbunivs = _79_1352; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = lbeff; FStar_Syntax_Syntax.lbdef = e} -> begin
(

let f_e = (effect_as_etag g lbeff)
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when (let _176_411 = (FStar_List.hd bs)
in (FStar_All.pipe_right _176_411 (is_type_binder g))) -> begin
(

let _79_1363 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_79_1363) with
| (bs, c) -> begin
(

let _79_1373 = (match ((FStar_Util.prefix_until (fun x -> (not ((is_type_binder g x)))) bs)) with
| None -> begin
((bs), ((FStar_Syntax_Util.comp_result c)))
end
| Some (bs, b, rest) -> begin
(let _176_413 = (FStar_Syntax_Util.arrow ((b)::rest) c)
in ((bs), (_176_413)))
end)
in (match (_79_1373) with
| (tbinders, tbody) -> begin
(

let n_tbinders = (FStar_List.length tbinders)
in (

let e = (normalize_abs e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _79_1379) -> begin
(

let _79_1384 = (FStar_Syntax_Subst.open_term bs body)
in (match (_79_1384) with
| (bs, body) -> begin
if (n_tbinders <= (FStar_List.length bs)) then begin
(

let _79_1387 = (FStar_Util.first_N n_tbinders bs)
in (match (_79_1387) with
| (targs, rest_args) -> begin
(

let expected_source_ty = (

let s = (FStar_List.map2 (fun _79_1391 _79_1395 -> (match (((_79_1391), (_79_1395))) with
| ((x, _79_1390), (y, _79_1394)) -> begin
(let _176_417 = (let _176_416 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (_176_416)))
in FStar_Syntax_Syntax.NT (_176_417))
end)) tbinders targs)
in (FStar_Syntax_Subst.subst s tbody))
in (

let env = (FStar_List.fold_left (fun env _79_1402 -> (match (_79_1402) with
| (a, _79_1401) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) g targs)
in (

let expected_t = (term_as_mlty env expected_source_ty)
in (

let polytype = (let _176_421 = (FStar_All.pipe_right targs (FStar_List.map (fun _79_1408 -> (match (_79_1408) with
| (x, _79_1407) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((_176_421), (expected_t)))
in (

let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_fstar_value body)))
end
| _79_1412 -> begin
false
end)
in (

let rest_args = if add_unit then begin
(unit_binder)::rest_args
end else begin
rest_args
end
in (

let body = (match (rest_args) with
| [] -> begin
body
end
| _79_1417 -> begin
(FStar_Syntax_Util.abs rest_args body None)
end)
in ((lbname_), (f_e), (((t), (((targs), (polytype))))), (add_unit), (body)))))))))
end))
end else begin
(FStar_All.failwith "Not enough type binders")
end
end))
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) -> begin
(

let env = (FStar_List.fold_left (fun env _79_1432 -> (match (_79_1432) with
| (a, _79_1431) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (let _176_425 = (FStar_All.pipe_right tbinders (FStar_List.map (fun _79_1438 -> (match (_79_1438) with
| (x, _79_1437) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((_176_425), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun _79_1443 -> (match (_79_1443) with
| (bv, _79_1442) -> begin
(let _176_427 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right _176_427 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e), (args)))) None e.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t), (((tbinders), (polytype))))), (false), (e)))))))
end
| _79_1447 -> begin
(err_value_restriction e)
end)))
end))
end))
end
| _79_1449 -> begin
(

let expected_t = (term_as_mlty g t)
in ((lbname_), (f_e), (((t), ((([]), ((([]), (expected_t))))))), (false), (e)))
end)))
end))
in (

let check_lb = (fun env _79_1464 -> (match (_79_1464) with
| (nm, (lbname, f, (t, (targs, polytype)), add_unit, e)) -> begin
(

let env = (FStar_List.fold_left (fun env _79_1469 -> (match (_79_1469) with
| (a, _79_1468) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) env targs)
in (

let expected_t = if add_unit then begin
FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), ((Prims.snd polytype))))
end else begin
(Prims.snd polytype)
end
in (

let _79_1475 = (check_term_as_mlexpr env e f expected_t)
in (match (_79_1475) with
| (e, _79_1474) -> begin
(

let f = (maybe_downgrade_eff env f expected_t)
in ((f), ({FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = true})))
end))))
end))
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map maybe_generalize))
in (

let _79_1500 = (FStar_List.fold_right (fun lb _79_1481 -> (match (_79_1481) with
| (env, lbs) -> begin
(

let _79_1494 = lb
in (match (_79_1494) with
| (lbname, _79_1484, (t, (_79_1487, polytype)), add_unit, _79_1493) -> begin
(

let _79_1497 = (FStar_Extraction_ML_UEnv.extend_lb env lbname t polytype add_unit true)
in (match (_79_1497) with
| (env, nm) -> begin
((env), ((((nm), (lb)))::lbs))
end))
end))
end)) lbs ((g), ([])))
in (match (_79_1500) with
| (env_body, lbs) -> begin
(

let env_def = if is_rec then begin
env_body
end else begin
g
end
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (check_lb env_def)))
in (

let e'_rng = e'.FStar_Syntax_Syntax.pos
in (

let _79_1507 = (term_as_mlexpr env_body e')
in (match (_79_1507) with
| (e', f', t') -> begin
(

let f = (let _176_437 = (let _176_436 = (FStar_List.map Prims.fst lbs)
in (f')::_176_436)
in (FStar_Extraction_ML_Util.join_l e'_rng _176_437))
in (

let is_rec = if (is_rec = true) then begin
FStar_Extraction_ML_Syntax.Rec
end else begin
FStar_Extraction_ML_Syntax.NoLetQualifier
end
in (let _176_442 = (let _176_441 = (let _176_439 = (let _176_438 = (FStar_List.map Prims.snd lbs)
in ((is_rec), (_176_438)))
in (mk_MLE_Let top_level _176_439 e'))
in (let _176_440 = (FStar_Extraction_ML_Util.mlloc_of_range t.FStar_Syntax_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' _176_441 _176_440)))
in ((_176_442), (f), (t')))))
end)))))
end)))))
end)))
end
| FStar_Syntax_Syntax.Tm_match (scrutinee, pats) -> begin
(

let _79_1517 = (term_as_mlexpr g scrutinee)
in (match (_79_1517) with
| (e, f_e, t_e) -> begin
(

let _79_1521 = (check_pats_for_ite pats)
in (match (_79_1521) with
| (b, then_e, else_e) -> begin
(

let no_lift = (fun x t -> x)
in if b then begin
(match (((then_e), (else_e))) with
| (Some (then_e), Some (else_e)) -> begin
(

let _79_1533 = (term_as_mlexpr g then_e)
in (match (_79_1533) with
| (then_mle, f_then, t_then) -> begin
(

let _79_1537 = (term_as_mlexpr g else_e)
in (match (_79_1537) with
| (else_mle, f_else, t_else) -> begin
(

let _79_1540 = if (type_leq g t_then t_else) then begin
((t_else), (no_lift))
end else begin
if (type_leq g t_else t_then) then begin
((t_then), (no_lift))
end else begin
((FStar_Extraction_ML_Syntax.MLTY_Top), (FStar_Extraction_ML_Syntax.apply_obj_repr))
end
end
in (match (_79_1540) with
| (t_branch, maybe_lift) -> begin
(let _176_473 = (let _176_471 = (let _176_470 = (let _176_469 = (maybe_lift then_mle t_then)
in (let _176_468 = (let _176_467 = (maybe_lift else_mle t_else)
in Some (_176_467))
in ((e), (_176_469), (_176_468))))
in FStar_Extraction_ML_Syntax.MLE_If (_176_470))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) _176_471))
in (let _176_472 = (FStar_Extraction_ML_Util.join then_e.FStar_Syntax_Syntax.pos f_then f_else)
in ((_176_473), (_176_472), (t_branch))))
end))
end))
end))
end
| _79_1542 -> begin
(FStar_All.failwith "ITE pats matched but then and else expressions not found?")
end)
end else begin
(

let _79_1574 = (FStar_All.pipe_right pats (FStar_Util.fold_map (fun compat br -> (

let _79_1548 = (FStar_Syntax_Subst.open_branch br)
in (match (_79_1548) with
| (pat, when_opt, branch) -> begin
(

let _79_1552 = (extract_pat g pat t_e)
in (match (_79_1552) with
| (env, p, pat_t_compat) -> begin
(

let _79_1563 = (match (when_opt) with
| None -> begin
((None), (FStar_Extraction_ML_Syntax.E_PURE))
end
| Some (w) -> begin
(

let _79_1559 = (term_as_mlexpr env w)
in (match (_79_1559) with
| (w, f_w, t_w) -> begin
(

let w = (maybe_coerce env w t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in ((Some (w)), (f_w)))
end))
end)
in (match (_79_1563) with
| (when_opt, f_when) -> begin
(

let _79_1567 = (term_as_mlexpr env branch)
in (match (_79_1567) with
| (mlbranch, f_branch, t_branch) -> begin
(let _176_477 = (FStar_All.pipe_right p (FStar_List.map (fun _79_1570 -> (match (_79_1570) with
| (p, wopt) -> begin
(

let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt)
in ((p), (((when_clause), (f_when))), (((mlbranch), (f_branch), (t_branch)))))
end))))
in (((compat && pat_t_compat)), (_176_477)))
end))
end))
end))
end))) true))
in (match (_79_1574) with
| (pat_t_compat, mlbranches) -> begin
(

let mlbranches = (FStar_List.flatten mlbranches)
in (

let e = if pat_t_compat then begin
e
end else begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_e) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (t_e), (FStar_Extraction_ML_Syntax.MLTY_Top)))))
end
in (match (mlbranches) with
| [] -> begin
(

let _79_1583 = (let _176_479 = (let _176_478 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Extraction_ML_UEnv.lookup_fv g _176_478))
in (FStar_All.pipe_left FStar_Util.right _176_479))
in (match (_79_1583) with
| (fw, _79_1580, _79_1582) -> begin
(let _176_484 = (let _176_483 = (let _176_482 = (let _176_481 = (let _176_480 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (_176_480)::[])
in ((fw), (_176_481)))
in FStar_Extraction_ML_Syntax.MLE_App (_176_482))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) _176_483))
in ((_176_484), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
end))
end
| ((_79_1586, _79_1588, (_79_1590, f_first, t_first)))::rest -> begin
(

let _79_1616 = (FStar_List.fold_left (fun _79_1598 _79_1608 -> (match (((_79_1598), (_79_1608))) with
| ((topt, f), (_79_1600, _79_1602, (_79_1604, f_branch, t_branch))) -> begin
(

let f = (FStar_Extraction_ML_Util.join top.FStar_Syntax_Syntax.pos f f_branch)
in (

let topt = (match (topt) with
| None -> begin
None
end
| Some (t) -> begin
if (type_leq g t t_branch) then begin
Some (t_branch)
end else begin
if (type_leq g t_branch t) then begin
Some (t)
end else begin
None
end
end
end)
in ((topt), (f))))
end)) ((Some (t_first)), (f_first)) rest)
in (match (_79_1616) with
| (topt, f_match) -> begin
(

let mlbranches = (FStar_All.pipe_right mlbranches (FStar_List.map (fun _79_1627 -> (match (_79_1627) with
| (p, (wopt, _79_1620), (b, _79_1624, t)) -> begin
(

let b = (match (topt) with
| None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b t)
end
| Some (_79_1630) -> begin
b
end)
in ((p), (wopt), (b)))
end))))
in (

let t_match = (match (topt) with
| None -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end
| Some (t) -> begin
t
end)
in (let _176_488 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match (((e), (mlbranches)))))
in ((_176_488), (f_match), (t_match)))))
end))
end)))
end))
end)
end))
end))
end))))


let fresh : Prims.string  ->  (Prims.string * Prims.int) = (

let c = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun x -> (

let _79_1640 = (FStar_Util.incr c)
in (let _176_491 = (FStar_ST.read c)
in ((x), (_176_491))))))


let ind_discriminator_body : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (

let _79_1648 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv discName)
in (match (_79_1648) with
| (_79_1646, fstar_disc_type) -> begin
(

let wildcards = (match ((let _176_498 = (FStar_Syntax_Subst.compress fstar_disc_type)
in _176_498.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _79_1651) -> begin
(let _176_502 = (FStar_All.pipe_right binders (FStar_List.filter (fun _79_4 -> (match (_79_4) with
| (_79_1656, Some (FStar_Syntax_Syntax.Implicit (_79_1658))) -> begin
true
end
| _79_1663 -> begin
false
end))))
in (FStar_All.pipe_right _176_502 (FStar_List.map (fun _79_1664 -> (let _176_501 = (fresh "_")
in ((_176_501), (FStar_Extraction_ML_Syntax.MLTY_Top)))))))
end
| _79_1667 -> begin
(FStar_All.failwith "Discriminator must be a function")
end)
in (

let mlid = (fresh "_discr_")
in (

let targ = FStar_Extraction_ML_Syntax.MLTY_Top
in (

let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top
in (

let discrBody = (let _176_517 = (let _176_516 = (let _176_515 = (let _176_514 = (let _176_513 = (let _176_512 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name ((([]), ((FStar_Extraction_ML_Syntax.idsym mlid))))))
in (let _176_511 = (let _176_510 = (let _176_506 = (let _176_504 = (let _176_503 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in ((_176_503), ((FStar_Extraction_ML_Syntax.MLP_Wild)::[])))
in FStar_Extraction_ML_Syntax.MLP_CTor (_176_504))
in (let _176_505 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in ((_176_506), (None), (_176_505))))
in (let _176_509 = (let _176_508 = (let _176_507 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in ((FStar_Extraction_ML_Syntax.MLP_Wild), (None), (_176_507)))
in (_176_508)::[])
in (_176_510)::_176_509))
in ((_176_512), (_176_511))))
in FStar_Extraction_ML_Syntax.MLE_Match (_176_513))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _176_514))
in (((FStar_List.append wildcards ((((mlid), (targ)))::[]))), (_176_515)))
in FStar_Extraction_ML_Syntax.MLE_Fun (_176_516))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) _176_517))
in FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NoLetQualifier), (({FStar_Extraction_ML_Syntax.mllb_name = (FStar_Extraction_ML_UEnv.convIdent discName.FStar_Ident.ident); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.print_typ = false})::[]))))))))
end)))




