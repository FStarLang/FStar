
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

let _78_17 = (let _170_29 = (let _170_28 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _170_28 msg))
in (FStar_All.pipe_left FStar_Util.print_string _170_29))
in (FStar_All.failwith msg)))


let err_uninst = (fun env t _78_23 -> (match (_78_23) with
| (vars, ty) -> begin
(let _170_37 = (let _170_36 = (FStar_Syntax_Print.term_to_string t)
in (let _170_35 = (let _170_33 = (FStar_All.pipe_right vars (FStar_List.map Prims.fst))
in (FStar_All.pipe_right _170_33 (FStar_String.concat ", ")))
in (let _170_34 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated" _170_36 _170_35 _170_34))))
in (fail t.FStar_Syntax_Syntax.pos _170_37))
end))


let err_ill_typed_application = (fun env t args ty -> (let _170_47 = (let _170_46 = (FStar_Syntax_Print.term_to_string t)
in (let _170_45 = (let _170_43 = (FStar_All.pipe_right args (FStar_List.map (fun _78_31 -> (match (_78_31) with
| (x, _78_30) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _170_43 (FStar_String.concat " ")))
in (let _170_44 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n" _170_46 _170_45 _170_44))))
in (fail t.FStar_Syntax_Syntax.pos _170_47)))


let err_value_restriction = (fun t -> (let _170_51 = (let _170_50 = (FStar_Syntax_Print.tag_of_term t)
in (let _170_49 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Refusing to generalize because of the value restriction: (%s) %s" _170_50 _170_49)))
in (fail t.FStar_Syntax_Syntax.pos _170_51)))


let err_unexpected_eff = (fun t f0 f1 -> (let _170_56 = (let _170_55 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" _170_55 (FStar_Extraction_ML_Util.eff_to_string f0) (FStar_Extraction_ML_Util.eff_to_string f1)))
in (fail t.FStar_Syntax_Syntax.pos _170_56)))


let effect_as_etag : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.e_tag = (

let cache = (FStar_Util.smap_create 20)
in (

let rec delta_norm_eff = (fun g l -> (match ((FStar_Util.smap_try_find cache l.FStar_Ident.str)) with
| Some (l) -> begin
l
end
| None -> begin
(

let res = (match ((FStar_TypeChecker_Env.lookup_effect_abbrev g.FStar_Extraction_ML_UEnv.tcenv FStar_Syntax_Syntax.U_zero l)) with
| None -> begin
l
end
| Some (_78_45, c) -> begin
(delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c))
end)
in (

let _78_50 = (FStar_Util.smap_add cache l.FStar_Ident.str res)
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


let predecessor = (fun t _78_1 -> (match (_78_1) with
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

let _78_67 = (FStar_Extraction_ML_UEnv.debug env (fun _78_65 -> (let _170_78 = (FStar_Syntax_Print.term_to_string t)
in (let _170_77 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "level %s (%s)\n" _170_78 _170_77)))))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_78_70) -> begin
(let _170_83 = (let _170_82 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: %s" _170_82))
in (FStar_All.failwith _170_83))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
Kind_level
end
| FStar_Syntax_Syntax.Tm_constant (_78_74) -> begin
Term_level
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _78_82; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_unfoldable (_78_79); FStar_Syntax_Syntax.fv_qual = _78_77}) -> begin
(

let t' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Iota))::[]) env.FStar_Extraction_ML_UEnv.tcenv t)
in (

let _78_87 = (FStar_Extraction_ML_UEnv.debug env (fun _78_86 -> (match (()) with
| () -> begin
(let _170_86 = (FStar_Syntax_Print.term_to_string t)
in (let _170_85 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Normalized %s to %s\n" _170_86 _170_85)))
end)))
in (level env t')))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
if (FStar_TypeChecker_Env.is_type_constructor env.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) then begin
Type_level
end else begin
(let _170_87 = (level env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (FStar_All.pipe_left predecessor _170_87))
end
end
| (FStar_Syntax_Syntax.Tm_uvar (_, t)) | (FStar_Syntax_Syntax.Tm_bvar ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})) | (FStar_Syntax_Syntax.Tm_name ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})) -> begin
(let _170_88 = (level env t)
in (FStar_All.pipe_left predecessor _170_88))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _78_110, _78_112) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_type (_78_116) -> begin
Kind_level
end
| FStar_Syntax_Syntax.Tm_uinst (t, _78_120) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_refine (x, _78_125) -> begin
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
| FStar_Syntax_Syntax.Tm_abs (bs, body, _78_139) -> begin
(level env body)
end
| FStar_Syntax_Syntax.Tm_let (_78_143, body) -> begin
(level env body)
end
| FStar_Syntax_Syntax.Tm_match (_78_148, branches) -> begin
(match (branches) with
| ((_78_155, _78_157, e))::_78_153 -> begin
(level env e)
end
| _78_162 -> begin
(FStar_All.failwith "Empty branches")
end)
end
| FStar_Syntax_Syntax.Tm_meta (t, _78_165) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_app (head, _78_170) -> begin
(level env head)
end)))))


let is_type : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((level env t)) with
| Term_level -> begin
false
end
| _78_177 -> begin
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


let is_constructor : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _170_97 = (FStar_Syntax_Subst.compress t)
in _170_97.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _78_203 -> begin
false
end))


let rec is_fstar_value : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _170_100 = (FStar_Syntax_Subst.compress t)
in _170_100.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
if (is_constructor head) then begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _78_224 -> (match (_78_224) with
| (te, _78_223) -> begin
(is_fstar_value te)
end))))
end else begin
false
end
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t, _, _)) -> begin
(is_fstar_value t)
end
| _78_237 -> begin
false
end))


let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Fun (_)) -> begin
true
end
| (FStar_Extraction_ML_Syntax.MLE_CTor (_, exps)) | (FStar_Extraction_ML_Syntax.MLE_Tuple (exps)) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (_78_258, fields) -> begin
(FStar_Util.for_all (fun _78_265 -> (match (_78_265) with
| (_78_263, e) -> begin
(is_ml_value e)
end)) fields)
end
| _78_267 -> begin
false
end))


let normalize_abs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t0 -> (

let rec aux = (fun bs t copt -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs', body, copt) -> begin
(aux (FStar_List.append bs bs') body copt)
end
| _78_280 -> begin
(

let e' = (FStar_Syntax_Util.unascribe t)
in if (FStar_Syntax_Util.is_fun e') then begin
(aux bs e' copt)
end else begin
(FStar_Syntax_Util.abs bs e' copt)
end)
end)))
in (aux [] t0 None)))


let unit_binder : FStar_Syntax_Syntax.binder = (let _170_113 = (FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _170_113))


let check_pats_for_ite : (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term Prims.option) = (fun l -> (

let def = ((false), (None), (None))
in if ((FStar_List.length l) <> 2) then begin
def
end else begin
(

let _78_287 = (FStar_List.hd l)
in (match (_78_287) with
| (p1, w1, e1) -> begin
(

let _78_291 = (let _170_116 = (FStar_List.tl l)
in (FStar_List.hd _170_116))
in (match (_78_291) with
| (p2, w2, e2) -> begin
(match (((w1), (w2), (p1.FStar_Syntax_Syntax.v), (p2.FStar_Syntax_Syntax.v))) with
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
((true), (Some (e1)), (Some (e2)))
end
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
((true), (Some (e2)), (Some (e1)))
end
| _78_311 -> begin
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
| _78_332 -> begin
(

let _78_334 = (FStar_Extraction_ML_UEnv.debug g (fun _78_333 -> (match (()) with
| () -> begin
(let _170_146 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (let _170_145 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (let _170_144 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule expect)
in (FStar_Util.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n" _170_146 _170_145 _170_144))))
end)))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (ty), (expect))))))
end)))


let bv_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bv -> (match ((FStar_Extraction_ML_UEnv.lookup_bv g bv)) with
| FStar_Util.Inl (_78_339, t) -> begin
t
end
| _78_344 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end))


let rec term_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlty' g t)))
and term_as_mlty' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun env t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _170_167 = (let _170_166 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Impossible: Unexpected term %s" _170_166))
in (FStar_All.failwith _170_167))
end
| FStar_Syntax_Syntax.Tm_uvar (_78_362) -> begin
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

let _78_398 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_78_398) with
| (bs, c) -> begin
(

let _78_401 = (binders_as_ml_binders env bs)
in (match (_78_401) with
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

let _78_418 = (FStar_List.fold_right (fun _78_411 _78_414 -> (match (((_78_411), (_78_414))) with
| ((_78_409, t), (tag, t')) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((t), (tag), (t')))))
end)) mlbs ((erase), (t_ret)))
in (match (_78_418) with
| (_78_416, t) -> begin
t
end))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let res = (match ((let _170_170 = (FStar_Syntax_Util.un_uinst head)
in _170_170.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv args)
end
| FStar_Syntax_Syntax.Tm_app (head, args') -> begin
(let _170_171 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head), ((FStar_List.append args' args))))) None t.FStar_Syntax_Syntax.pos)
in (term_as_mlty' env _170_171))
end
| _78_432 -> begin
FStar_Extraction_ML_UEnv.unknownType
end)
in res)
end
| FStar_Syntax_Syntax.Tm_abs (bs, ty, _78_437) -> begin
(

let _78_442 = (FStar_Syntax_Subst.open_term bs ty)
in (match (_78_442) with
| (bs, ty) -> begin
(

let _78_445 = (binders_as_ml_binders env bs)
in (match (_78_445) with
| (bts, env) -> begin
(term_as_mlty' env ty)
end))
end))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
FStar_Extraction_ML_UEnv.unknownType
end)))
and arg_as_mlty : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  FStar_Extraction_ML_Syntax.mlty = (fun g _78_459 -> (match (_78_459) with
| (a, _78_458) -> begin
if (is_type g a) then begin
(term_as_mlty' g a)
end else begin
FStar_Extraction_ML_UEnv.erasedContent
end
end))
and fv_app_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.args  ->  FStar_Extraction_ML_Syntax.mlty = (fun g fv args -> (

let _78_465 = (FStar_Syntax_Util.arrow_formals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (match (_78_465) with
| (formals, t) -> begin
(

let mlargs = (FStar_List.map (arg_as_mlty g) args)
in (

let mlargs = (

let n_args = (FStar_List.length args)
in if ((FStar_List.length formals) > n_args) then begin
(

let _78_471 = (FStar_Util.first_N n_args formals)
in (match (_78_471) with
| (_78_469, rest) -> begin
(let _170_178 = (FStar_List.map (fun _78_472 -> FStar_Extraction_ML_UEnv.erasedContent) rest)
in (FStar_List.append mlargs _170_178))
end))
end else begin
mlargs
end)
in (let _170_180 = (let _170_179 = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in ((mlargs), (_170_179)))
in FStar_Extraction_ML_Syntax.MLTY_Named (_170_180))))
end)))
and binders_as_ml_binders : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list * FStar_Extraction_ML_UEnv.env) = (fun g bs -> (

let _78_490 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _78_479 b -> (match (_78_479) with
| (ml_bs, env) -> begin
if (is_type_binder g b) then begin
(

let b = (Prims.fst b)
in (

let env = (FStar_Extraction_ML_UEnv.extend_ty env b (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (

let ml_b = (let _170_185 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b)
in ((_170_185), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
in (((ml_b)::ml_bs), (env)))))
end else begin
(

let b = (Prims.fst b)
in (

let t = (term_as_mlty env b.FStar_Syntax_Syntax.sort)
in (

let env = (FStar_Extraction_ML_UEnv.extend_bv env b (([]), (t)) false false false)
in (

let ml_b = (let _170_186 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b)
in ((_170_186), (t)))
in (((ml_b)::ml_bs), (env))))))
end
end)) (([]), (g))))
in (match (_78_490) with
| (ml_bs, env) -> begin
(((FStar_List.rev ml_bs)), (env))
end)))


let mk_MLE_Seq : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun e1 e2 -> (match (((e1.FStar_Extraction_ML_Syntax.expr), (e2.FStar_Extraction_ML_Syntax.expr))) with
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 es2))
end
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), _78_501) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 ((e2)::[])))
end
| (_78_504, FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::es2)
end
| _78_509 -> begin
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
| _78_524 when (lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr) -> begin
body.FStar_Extraction_ML_Syntax.expr
end
| _78_526 -> begin
(mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def body)
end)
end
end
| _78_528 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end)
end
| _78_530 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end))


let resugar_pat : FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_ML_Syntax.mlpattern = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(match ((FStar_Extraction_ML_Util.is_xtuple d)) with
| Some (n) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| _78_540 -> begin
(match (q) with
| Some (FStar_Syntax_Syntax.Record_ctor (_78_542, fns)) -> begin
(

let p = (FStar_Extraction_ML_Util.record_field_path fns)
in (

let fs = (FStar_Extraction_ML_Util.record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record (((p), (fs)))))
end
| _78_550 -> begin
p
end)
end)
end
| _78_552 -> begin
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
| FStar_Syntax_Syntax.Pat_disj (_78_568) -> begin
(FStar_All.failwith "Impossible: Nested disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int (c, None)) when (not ((FStar_Options.use_native_int ()))) -> begin
(

let i = FStar_Const.Const_int (((c), (None)))
in (

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let when_clause = (let _170_227 = (let _170_226 = (let _170_225 = (let _170_224 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (let _170_223 = (let _170_222 = (let _170_221 = (let _170_220 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p i)
in (FStar_All.pipe_left (fun _170_219 -> FStar_Extraction_ML_Syntax.MLE_Const (_170_219)) _170_220))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) _170_221))
in (_170_222)::[])
in (_170_224)::_170_223))
in ((FStar_Extraction_ML_Util.prims_op_equality), (_170_225)))
in FStar_Extraction_ML_Syntax.MLE_App (_170_226))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _170_227))
in (let _170_228 = (ok FStar_Extraction_ML_Syntax.ml_int_ty)
in ((g), (Some (((FStar_Extraction_ML_Syntax.MLP_Var (x)), ((when_clause)::[])))), (_170_228))))))
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(

let t = (FStar_TypeChecker_Tc.tc_constant FStar_Range.dummyRange s)
in (

let mlty = (term_as_mlty g t)
in (let _170_233 = (let _170_231 = (let _170_230 = (let _170_229 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (_170_229))
in ((_170_230), ([])))
in Some (_170_231))
in (let _170_232 = (ok mlty)
in ((g), (_170_233), (_170_232))))))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let g = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (let _170_238 = if imp then begin
None
end else begin
(let _170_236 = (let _170_235 = (let _170_234 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in FStar_Extraction_ML_Syntax.MLP_Var (_170_234))
in ((_170_235), ([])))
in Some (_170_236))
end
in (let _170_237 = (ok mlty)
in ((g), (_170_238), (_170_237))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) when disjunctive_pat -> begin
((g), (Some (((FStar_Extraction_ML_Syntax.MLP_Wild), ([])))), (true))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let g = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (let _170_243 = if imp then begin
None
end else begin
(let _170_241 = (let _170_240 = (let _170_239 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in FStar_Extraction_ML_Syntax.MLP_Var (_170_239))
in ((_170_240), ([])))
in Some (_170_241))
end
in (let _170_242 = (ok mlty)
in ((g), (_170_243), (_170_242))))))
end
| FStar_Syntax_Syntax.Pat_dot_term (_78_593) -> begin
((g), (None), (true))
end
| FStar_Syntax_Syntax.Pat_cons (f, pats) -> begin
(

let _78_615 = (match ((FStar_Extraction_ML_UEnv.lookup_fv g f)) with
| FStar_Util.Inr ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n); FStar_Extraction_ML_Syntax.mlty = _78_602; FStar_Extraction_ML_Syntax.loc = _78_600}, ttys, _78_608) -> begin
((n), (ttys))
end
| _78_612 -> begin
(FStar_All.failwith "Expected a constructor")
end)
in (match (_78_615) with
| (d, tys) -> begin
(

let nTyVars = (FStar_List.length (Prims.fst tys))
in (

let _78_619 = (FStar_Util.first_N nTyVars pats)
in (match (_78_619) with
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

let mlty_args = (FStar_All.pipe_right tysVarPats (FStar_List.map (fun _78_632 -> (match (_78_632) with
| (p, _78_631) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (_78_634, t) -> begin
(term_as_mlty g t)
end
| _78_639 -> begin
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

let _78_654 = (FStar_Util.fold_map (fun g _78_646 -> (match (_78_646) with
| (p, imp) -> begin
(

let _78_651 = (extract_one_pat disjunctive_pat true g p None)
in (match (_78_651) with
| (g, p, _78_650) -> begin
((g), (p))
end))
end)) g tysVarPats)
in (match (_78_654) with
| (g, tyMLPats) -> begin
(

let _78_666 = (FStar_Util.fold_map (fun g _78_658 -> (match (_78_658) with
| (p, imp) -> begin
(

let _78_663 = (extract_one_pat disjunctive_pat false g p None)
in (match (_78_663) with
| (g, p, _78_662) -> begin
((g), (p))
end))
end)) g restPats)
in (match (_78_666) with
| (g, restMLPats) -> begin
(

let _78_674 = (let _170_252 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun _78_2 -> (match (_78_2) with
| Some (x) -> begin
(x)::[]
end
| _78_671 -> begin
[]
end))))
in (FStar_All.pipe_right _170_252 FStar_List.split))
in (match (_78_674) with
| (mlPats, when_clauses) -> begin
(let _170_256 = (let _170_255 = (let _170_254 = (resugar_pat f.FStar_Syntax_Syntax.fv_qual (FStar_Extraction_ML_Syntax.MLP_CTor (((d), (mlPats)))))
in (let _170_253 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in ((_170_254), (_170_253))))
in Some (_170_255))
in ((g), (_170_256), (pat_ty_compat)))
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
| _78_688 -> begin
(FStar_All.failwith "Impossible: Unable to translate pattern")
end))
in (

let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| (hd)::tl -> begin
(let _170_267 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl)
in Some (_170_267))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: Empty disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_disj ((p)::pats) -> begin
(

let _78_704 = (extract_one_pat true g p (Some (expected_t)))
in (match (_78_704) with
| (g, p, b) -> begin
(

let _78_714 = (FStar_Util.fold_map (fun b p -> (

let _78_711 = (extract_one_pat true g p (Some (expected_t)))
in (match (_78_711) with
| (_78_708, p, b') -> begin
(((b && b')), (p))
end))) b pats)
in (match (_78_714) with
| (b, ps) -> begin
(

let ps = (p)::ps
in (

let _78_729 = (FStar_All.pipe_right ps (FStar_List.partition (fun _78_3 -> (match (_78_3) with
| (_78_718, (_78_722)::_78_720) -> begin
true
end
| _78_726 -> begin
false
end))))
in (match (_78_729) with
| (ps_when, rest) -> begin
(

let ps = (FStar_All.pipe_right ps_when (FStar_List.map (fun _78_732 -> (match (_78_732) with
| (x, whens) -> begin
(let _170_272 = (mk_when_clause whens)
in ((x), (_170_272)))
end))))
in (

let res = (match (rest) with
| [] -> begin
((g), (ps), (b))
end
| rest -> begin
(let _170_276 = (let _170_275 = (let _170_274 = (let _170_273 = (FStar_List.map Prims.fst rest)
in FStar_Extraction_ML_Syntax.MLP_Branch (_170_273))
in ((_170_274), (None)))
in (_170_275)::ps)
in ((g), (_170_276), (b)))
end)
in res))
end)))
end))
end))
end
| _78_738 -> begin
(

let _78_744 = (extract_one_pat false g p (Some (expected_t)))
in (match (_78_744) with
| (g, (p, whens), b) -> begin
(

let when_clause = (mk_when_clause whens)
in ((g), ((((p), (when_clause)))::[]), (b)))
end))
end)))))


let maybe_eta_data_and_project_record : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (

let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, _78_755, t1) -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _170_291 = (let _170_290 = (let _170_289 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((((x), (t0))), (_170_289)))
in (_170_290)::more_args)
in (eta_args _170_291 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_78_761, _78_763) -> begin
(((FStar_List.rev more_args)), (t))
end
| _78_767 -> begin
(FStar_All.failwith "Impossible: Head type is not an arrow")
end))
in (

let as_record = (fun qual e -> (match (((e.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (_78_772, args), Some (FStar_Syntax_Syntax.Record_ctor (_78_777, fields))) -> begin
(

let path = (FStar_Extraction_ML_Util.record_field_path fields)
in (

let fields = (FStar_Extraction_ML_Util.record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record (((path), (fields)))))))
end
| _78_786 -> begin
e
end))
in (

let resugar_and_maybe_eta = (fun qual e -> (

let _78_792 = (eta_args [] residualType)
in (match (_78_792) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(let _170_300 = (as_record qual e)
in (FStar_Extraction_ML_Util.resugar_exp _170_300))
end
| _78_795 -> begin
(

let _78_798 = (FStar_List.unzip eargs)
in (match (_78_798) with
| (binders, eargs) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head, args) -> begin
(

let body = (let _170_302 = (let _170_301 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor (((head), ((FStar_List.append args eargs))))))
in (FStar_All.pipe_left (as_record qual) _170_301))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp _170_302))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun (((binders), (body))))))
end
| _78_805 -> begin
(FStar_All.failwith "Impossible: Not a constructor")
end)
end))
end)
end)))
in (match (((mlAppExpr.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (_78_807, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _78_813; FStar_Extraction_ML_Syntax.loc = _78_811}, (mle)::args), Some (FStar_Syntax_Syntax.Record_projector (f))) -> begin
(

let fn = (FStar_Extraction_ML_Util.mlpath_of_lid f)
in (

let proj = FStar_Extraction_ML_Syntax.MLE_Proj (((mle), (fn)))
in (

let e = (match (args) with
| [] -> begin
proj
end
| _78_830 -> begin
(let _170_304 = (let _170_303 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in ((_170_303), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (_170_304))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e))))
end
| ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _170_305 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _170_305))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _170_306 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _170_306))
end
| _78_870 -> begin
mlAppExpr
end)))))


let maybe_downgrade_eff : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag = (fun g f t -> if ((f = FStar_Extraction_ML_Syntax.E_GHOST) && (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty)) then begin
FStar_Extraction_ML_Syntax.E_PURE
end else begin
f
end)


let rec term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g t -> (

let _78_879 = (term_as_mlexpr' g t)
in (match (_78_879) with
| (e, tag, ty) -> begin
(

let _78_881 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (let _170_331 = (let _170_330 = (FStar_Syntax_Print.tag_of_term t)
in (let _170_329 = (FStar_Syntax_Print.term_to_string t)
in (let _170_328 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "term_as_mlexpr (%s) :  %s has ML type %s\n" _170_330 _170_329 _170_328))))
in (FStar_Util.print_string _170_331))))
in (erase g e ty tag))
end)))
and check_term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g t f ty -> (

let _78_889 = (check_term_as_mlexpr' g t f ty)
in (match (_78_889) with
| (e, t) -> begin
(

let _78_894 = (erase g e t f)
in (match (_78_894) with
| (r, _78_892, t) -> begin
((r), (t))
end))
end)))
and check_term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g e0 f ty -> (

let _78_902 = (term_as_mlexpr g e0)
in (match (_78_902) with
| (e, tag, t) -> begin
(

let tag = (maybe_downgrade_eff g tag t)
in if (FStar_Extraction_ML_Util.eff_leq tag f) then begin
(let _170_340 = (maybe_coerce g e t ty)
in ((_170_340), (ty)))
end else begin
(err_unexpected_eff e0 f tag)
end)
end)))
and term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g top -> (

let _78_907 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (let _170_346 = (let _170_345 = (FStar_Syntax_Print.tag_of_term top)
in (let _170_344 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format2 "term_as_mlexpr\' (%s) :  %s \n" _170_345 _170_344)))
in (FStar_Util.print_string _170_346))))
in (

let t = (FStar_Syntax_Subst.compress top)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) -> begin
(let _170_348 = (let _170_347 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" _170_347))
in (FStar_All.failwith _170_348))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc)) -> begin
(match ((term_as_mlexpr' g t)) with
| ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let ((FStar_Extraction_ML_Syntax.NoLetQualifier, bodies), continuation); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}, tag, typ) -> begin
(({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let (((((FStar_Extraction_ML_Syntax.Mutable), (bodies))), (continuation))); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}), (tag), (typ))
end
| _78_947 -> begin
(FStar_All.failwith "impossible")
end)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, _78_951)) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) when (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl g.FStar_Extraction_ML_UEnv.tcenv m)
in if (let _170_349 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right _170_349 Prims.op_Negation)) then begin
(term_as_mlexpr' g t)
end else begin
(

let ml_result_ty_1 = (term_as_mlty g lb.FStar_Syntax_Syntax.lbtyp)
in (

let _78_971 = (term_as_mlexpr g lb.FStar_Syntax_Syntax.lbdef)
in (match (_78_971) with
| (comp_1, _78_968, _78_970) -> begin
(

let _78_990 = (

let k = (let _170_352 = (let _170_351 = (let _170_350 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_All.pipe_right _170_350 FStar_Syntax_Syntax.mk_binder))
in (_170_351)::[])
in (FStar_Syntax_Util.abs _170_352 body None))
in (

let _78_977 = (term_as_mlexpr g k)
in (match (_78_977) with
| (ml_k, _78_975, t_k) -> begin
(

let m_2 = (match (t_k) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_78_979, _78_981, m_2) -> begin
m_2
end
| _78_986 -> begin
(FStar_All.failwith "Impossible")
end)
in ((ml_k), (m_2)))
end)))
in (match (_78_990) with
| (ml_k, ty) -> begin
(

let bind = (let _170_355 = (let _170_354 = (let _170_353 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (FStar_All.pipe_right _170_353 Prims.fst))
in FStar_Extraction_ML_Syntax.MLE_Name (_170_354))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _170_355))
in (let _170_356 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) (FStar_Extraction_ML_Syntax.MLE_App (((bind), ((comp_1)::(ml_k)::[])))))
in ((_170_356), (FStar_Extraction_ML_Syntax.E_IMPURE), (ty))))
end))
end)))
end)
end
| _78_993 -> begin
(term_as_mlexpr' g t)
end))
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_uinst (t, _)) -> begin
(term_as_mlexpr' g t)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let _78_1010 = (FStar_TypeChecker_Tc.type_of g.FStar_Extraction_ML_UEnv.tcenv t)
in (match (_78_1010) with
| (_78_1006, ty, _78_1009) -> begin
(

let ml_ty = (term_as_mlty g ty)
in (let _170_360 = (let _170_359 = (let _170_358 = (FStar_Extraction_ML_Util.mlconst_of_const' t.FStar_Syntax_Syntax.pos c)
in (FStar_All.pipe_left (fun _170_357 -> FStar_Extraction_ML_Syntax.MLE_Const (_170_357)) _170_358))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty _170_359))
in ((_170_360), (FStar_Extraction_ML_Syntax.E_PURE), (ml_ty))))
end))
end
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
if (is_type g t) then begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end else begin
(match ((FStar_Extraction_ML_UEnv.lookup_term g t)) with
| (FStar_Util.Inl (_78_1019), _78_1022) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| (FStar_Util.Inr (x, mltys, _78_1027), qual) -> begin
(match (mltys) with
| ([], t) when (t = FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t))
end
| ([], t) -> begin
(let _170_361 = (maybe_eta_data_and_project_record g qual t x)
in ((_170_361), (FStar_Extraction_ML_Syntax.E_PURE), (t)))
end
| _78_1039 -> begin
(err_uninst g t mltys)
end)
end)
end
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, copt) -> begin
(

let _78_1047 = (FStar_Syntax_Subst.open_term bs body)
in (match (_78_1047) with
| (bs, body) -> begin
(

let _78_1050 = (binders_as_ml_binders g bs)
in (match (_78_1050) with
| (ml_bs, env) -> begin
(

let _78_1054 = (term_as_mlexpr env body)
in (match (_78_1054) with
| (ml_body, f, t) -> begin
(

let _78_1064 = (FStar_List.fold_right (fun _78_1058 _78_1061 -> (match (((_78_1058), (_78_1061))) with
| ((_78_1056, targ), (f, t)) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((targ), (f), (t)))))
end)) ml_bs ((f), (t)))
in (match (_78_1064) with
| (f, tfun) -> begin
(let _170_364 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun (((ml_bs), (ml_body)))))
in ((_170_364), (f), (tfun)))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _78_1070; FStar_Syntax_Syntax.pos = _78_1068; FStar_Syntax_Syntax.vars = _78_1066}, (t)::[]) -> begin
(

let _78_1081 = (term_as_mlexpr' g (Prims.fst t))
in (match (_78_1081) with
| (ml, e_tag, mlty) -> begin
((ml), (FStar_Extraction_ML_Syntax.E_PURE), (mlty))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_78_1089)); FStar_Syntax_Syntax.tk = _78_1087; FStar_Syntax_Syntax.pos = _78_1085; FStar_Syntax_Syntax.vars = _78_1083}, (t)::[]) -> begin
(

let _78_1100 = (term_as_mlexpr' g (Prims.fst t))
in (match (_78_1100) with
| (ml, e_tag, mlty) -> begin
((ml), (FStar_Extraction_ML_Syntax.E_IMPURE), (mlty))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (_78_1106) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t))
end
| _78_1110 -> begin
(

let rec extract_app = (fun is_data _78_1115 _78_1118 restArgs -> (match (((_78_1115), (_78_1118))) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match (((restArgs), (t))) with
| ([], _78_1122) -> begin
(

let evaluation_order_guaranteed = ((((FStar_List.length mlargs_f) = 1) || (FStar_Extraction_ML_Util.codegen_fsharp ())) || (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = {FStar_Syntax_Syntax.v = v; FStar_Syntax_Syntax.ty = _78_1131; FStar_Syntax_Syntax.p = _78_1129}; FStar_Syntax_Syntax.fv_delta = _78_1127; FStar_Syntax_Syntax.fv_qual = _78_1125}) -> begin
((v = FStar_Syntax_Const.op_And) || (v = FStar_Syntax_Const.op_Or))
end
| _78_1137 -> begin
false
end))
in (

let _78_1148 = if evaluation_order_guaranteed then begin
(let _170_373 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in (([]), (_170_373)))
end else begin
(FStar_List.fold_left (fun _78_1141 _78_1144 -> (match (((_78_1141), (_78_1144))) with
| ((lbs, out_args), (arg, f)) -> begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) || (f = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
((lbs), ((arg)::out_args))
end else begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _170_377 = (let _170_376 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (_170_376)::out_args)
in (((((x), (arg)))::lbs), (_170_377))))
end
end)) (([]), ([])) mlargs_f)
end
in (match (_78_1148) with
| (lbs, mlargs) -> begin
(

let app = (let _170_378 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_App (((mlhead), (mlargs)))))
in (FStar_All.pipe_left (maybe_eta_data_and_project_record g is_data t) _170_378))
in (

let l_app = (FStar_List.fold_right (fun _78_1152 out -> (match (_78_1152) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.mlty) (mk_MLE_Let false ((FStar_Extraction_ML_Syntax.NoLetQualifier), (({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = Some ((([]), (arg.FStar_Extraction_ML_Syntax.mlty))); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg; FStar_Extraction_ML_Syntax.print_typ = true})::[])) out))
end)) lbs app)
in ((l_app), (f), (t))))
end)))
end
| (((arg, _78_1158))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (formal_t, f', t)) when (is_type g arg) -> begin
if (type_leq g formal_t FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
(let _170_382 = (let _170_381 = (FStar_Extraction_ML_Util.join f f')
in ((_170_381), (t)))
in (extract_app is_data ((mlhead), ((((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE)))::mlargs_f)) _170_382 rest))
end else begin
(let _170_387 = (let _170_386 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule mlhead)
in (let _170_385 = (FStar_Syntax_Print.term_to_string arg)
in (let _170_384 = (FStar_Syntax_Print.tag_of_term arg)
in (let _170_383 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule formal_t)
in (FStar_Util.format4 "Impossible: ill-typed application:\n\thead=%s, arg=%s, tag=%s\n\texpected type unit, got %s" _170_386 _170_385 _170_384 _170_383)))))
in (FStar_All.failwith _170_387))
end
end
| (((e0, _78_1170))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t)) -> begin
(

let _78_1182 = (term_as_mlexpr g e0)
in (match (_78_1182) with
| (e0, f0, tInferred) -> begin
(

let e0 = (maybe_coerce g e0 tInferred tExpected)
in (let _170_389 = (let _170_388 = (FStar_Extraction_ML_Util.join_l ((f)::(f')::(f0)::[]))
in ((_170_388), (t)))
in (extract_app is_data ((mlhead), ((((e0), (f0)))::mlargs_f)) _170_389 rest)))
end))
end
| _78_1185 -> begin
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

let extract_app_maybe_projector = (fun is_data mlhead _78_1194 args -> (match (_78_1194) with
| (f, t) -> begin
(match (is_data) with
| Some (FStar_Syntax_Syntax.Record_projector (_78_1197)) -> begin
(

let rec remove_implicits = (fun args f t -> (match (((args), (t))) with
| (((_78_1206, Some (FStar_Syntax_Syntax.Implicit (_78_1208))))::args, FStar_Extraction_ML_Syntax.MLTY_Fun (_78_1214, f', t)) -> begin
(let _170_404 = (FStar_Extraction_ML_Util.join f f')
in (remove_implicits args _170_404 t))
end
| _78_1221 -> begin
((args), (f), (t))
end))
in (

let _78_1225 = (remove_implicits args f t)
in (match (_78_1225) with
| (args, f, t) -> begin
(extract_app is_data ((mlhead), ([])) ((f), (t)) args)
end)))
end
| _78_1227 -> begin
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

let _78_1248 = (match ((FStar_Extraction_ML_UEnv.lookup_term g head)) with
| (FStar_Util.Inr (u), q) -> begin
((u), (q))
end
| _78_1240 -> begin
(FStar_All.failwith "FIXME Ty")
end)
in (match (_78_1248) with
| ((head_ml, (vars, t), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, _78_1253))::_78_1250 -> begin
(is_type g a)
end
| _78_1257 -> begin
false
end)
in (

let _78_1303 = (match (vars) with
| (_78_1262)::_78_1260 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t), (args))
end
| _78_1265 -> begin
(

let n = (FStar_List.length vars)
in if (n <= (FStar_List.length args)) then begin
(

let _78_1269 = (FStar_Util.first_N n args)
in (match (_78_1269) with
| (prefix, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun _78_1273 -> (match (_78_1273) with
| (x, _78_1272) -> begin
(term_as_mlty g x)
end)) prefix)
in (

let t = (instantiate ((vars), (t)) prefixAsMLTypes)
in (

let head = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) -> begin
(

let _78_1282 = head_ml
in {FStar_Extraction_ML_Syntax.expr = _78_1282.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t; FStar_Extraction_ML_Syntax.loc = _78_1282.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = _78_1288; FStar_Extraction_ML_Syntax.loc = _78_1286})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let _78_1295 = head
in {FStar_Extraction_ML_Syntax.expr = _78_1295.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t))); FStar_Extraction_ML_Syntax.loc = _78_1295.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t))
end
| _78_1298 -> begin
(FStar_All.failwith "Impossible: Unexpected head term")
end)
in ((head), (t), (rest)))))
end))
end else begin
(err_uninst g head ((vars), (t)))
end)
end)
in (match (_78_1303) with
| (head_ml, head_t, args) -> begin
(match (args) with
| [] -> begin
(let _170_406 = (maybe_eta_data_and_project_record g qual head_t head_ml)
in ((_170_406), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| _78_1306 -> begin
(extract_app_maybe_projector qual head_ml ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args)
end)
end)))
end))
end
| _78_1308 -> begin
(

let _78_1312 = (term_as_mlexpr g head)
in (match (_78_1312) with
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

let _78_1329 = (check_term_as_mlexpr g e0 f t)
in (match (_78_1329) with
| (e, t) -> begin
((e), (f), (t))
end))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') -> begin
(

let top_level = (FStar_Syntax_Syntax.is_top_level lbs)
in (

let _78_1345 = if is_rec then begin
(FStar_Syntax_Subst.open_let_rec lbs e')
end else begin
if (FStar_Syntax_Syntax.is_top_level lbs) then begin
((lbs), (e'))
end else begin
(

let lb = (FStar_List.hd lbs)
in (

let x = (let _170_407 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv _170_407))
in (

let lb = (

let _78_1339 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _78_1339.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _78_1339.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _78_1339.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _78_1339.FStar_Syntax_Syntax.lbdef})
in (

let e' = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.DB (((0), (x))))::[]) e')
in (((lb)::[]), (e'))))))
end
end
in (match (_78_1345) with
| (lbs, e') -> begin
(

let maybe_generalize = (fun _78_1353 -> (match (_78_1353) with
| {FStar_Syntax_Syntax.lbname = lbname_; FStar_Syntax_Syntax.lbunivs = _78_1351; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = lbeff; FStar_Syntax_Syntax.lbdef = e} -> begin
(

let f_e = (effect_as_etag g lbeff)
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when (let _170_410 = (FStar_List.hd bs)
in (FStar_All.pipe_right _170_410 (is_type_binder g))) -> begin
(

let _78_1362 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_78_1362) with
| (bs, c) -> begin
(

let _78_1372 = (match ((FStar_Util.prefix_until (fun x -> (not ((is_type_binder g x)))) bs)) with
| None -> begin
((bs), ((FStar_Syntax_Util.comp_result c)))
end
| Some (bs, b, rest) -> begin
(let _170_412 = (FStar_Syntax_Util.arrow ((b)::rest) c)
in ((bs), (_170_412)))
end)
in (match (_78_1372) with
| (tbinders, tbody) -> begin
(

let n_tbinders = (FStar_List.length tbinders)
in (

let e = (normalize_abs e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _78_1378) -> begin
(

let _78_1383 = (FStar_Syntax_Subst.open_term bs body)
in (match (_78_1383) with
| (bs, body) -> begin
if (n_tbinders <= (FStar_List.length bs)) then begin
(

let _78_1386 = (FStar_Util.first_N n_tbinders bs)
in (match (_78_1386) with
| (targs, rest_args) -> begin
(

let expected_source_ty = (

let s = (FStar_List.map2 (fun _78_1390 _78_1394 -> (match (((_78_1390), (_78_1394))) with
| ((x, _78_1389), (y, _78_1393)) -> begin
(let _170_416 = (let _170_415 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (_170_415)))
in FStar_Syntax_Syntax.NT (_170_416))
end)) tbinders targs)
in (FStar_Syntax_Subst.subst s tbody))
in (

let env = (FStar_List.fold_left (fun env _78_1401 -> (match (_78_1401) with
| (a, _78_1400) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) g targs)
in (

let expected_t = (term_as_mlty env expected_source_ty)
in (

let polytype = (let _170_420 = (FStar_All.pipe_right targs (FStar_List.map (fun _78_1407 -> (match (_78_1407) with
| (x, _78_1406) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((_170_420), (expected_t)))
in (

let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_fstar_value body)))
end
| _78_1411 -> begin
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
| _78_1416 -> begin
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

let env = (FStar_List.fold_left (fun env _78_1431 -> (match (_78_1431) with
| (a, _78_1430) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (let _170_424 = (FStar_All.pipe_right tbinders (FStar_List.map (fun _78_1437 -> (match (_78_1437) with
| (x, _78_1436) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((_170_424), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun _78_1442 -> (match (_78_1442) with
| (bv, _78_1441) -> begin
(let _170_426 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right _170_426 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e), (args)))) None e.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t), (((tbinders), (polytype))))), (false), (e)))))))
end
| _78_1446 -> begin
(err_value_restriction e)
end)))
end))
end))
end
| _78_1448 -> begin
(

let expected_t = (term_as_mlty g t)
in ((lbname_), (f_e), (((t), ((([]), ((([]), (expected_t))))))), (false), (e)))
end)))
end))
in (

let check_lb = (fun env _78_1463 -> (match (_78_1463) with
| (nm, (lbname, f, (t, (targs, polytype)), add_unit, e)) -> begin
(

let env = (FStar_List.fold_left (fun env _78_1468 -> (match (_78_1468) with
| (a, _78_1467) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) env targs)
in (

let expected_t = if add_unit then begin
FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), ((Prims.snd polytype))))
end else begin
(Prims.snd polytype)
end
in (

let _78_1474 = (check_term_as_mlexpr env e f expected_t)
in (match (_78_1474) with
| (e, _78_1473) -> begin
((f), ({FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = true}))
end))))
end))
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map maybe_generalize))
in (

let _78_1498 = (FStar_List.fold_right (fun lb _78_1479 -> (match (_78_1479) with
| (env, lbs) -> begin
(

let _78_1492 = lb
in (match (_78_1492) with
| (lbname, _78_1482, (t, (_78_1485, polytype)), add_unit, _78_1491) -> begin
(

let _78_1495 = (FStar_Extraction_ML_UEnv.extend_lb env lbname t polytype add_unit true)
in (match (_78_1495) with
| (env, nm) -> begin
((env), ((((nm), (lb)))::lbs))
end))
end))
end)) lbs ((g), ([])))
in (match (_78_1498) with
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

let _78_1504 = (term_as_mlexpr env_body e')
in (match (_78_1504) with
| (e', f', t') -> begin
(

let f = (let _170_436 = (let _170_435 = (FStar_List.map Prims.fst lbs)
in (f')::_170_435)
in (FStar_Extraction_ML_Util.join_l _170_436))
in (

let is_rec = if (is_rec = true) then begin
FStar_Extraction_ML_Syntax.Rec
end else begin
FStar_Extraction_ML_Syntax.NoLetQualifier
end
in (let _170_441 = (let _170_440 = (let _170_438 = (let _170_437 = (FStar_List.map Prims.snd lbs)
in ((is_rec), (_170_437)))
in (mk_MLE_Let top_level _170_438 e'))
in (let _170_439 = (FStar_Extraction_ML_Util.mlloc_of_range t.FStar_Syntax_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' _170_440 _170_439)))
in ((_170_441), (f), (t')))))
end))))
end)))))
end)))
end
| FStar_Syntax_Syntax.Tm_match (scrutinee, pats) -> begin
(

let _78_1514 = (term_as_mlexpr g scrutinee)
in (match (_78_1514) with
| (e, f_e, t_e) -> begin
(

let _78_1518 = (check_pats_for_ite pats)
in (match (_78_1518) with
| (b, then_e, else_e) -> begin
(

let no_lift = (fun x t -> x)
in if b then begin
(match (((then_e), (else_e))) with
| (Some (then_e), Some (else_e)) -> begin
(

let _78_1530 = (term_as_mlexpr g then_e)
in (match (_78_1530) with
| (then_mle, f_then, t_then) -> begin
(

let _78_1534 = (term_as_mlexpr g else_e)
in (match (_78_1534) with
| (else_mle, f_else, t_else) -> begin
(

let _78_1537 = if (type_leq g t_then t_else) then begin
((t_else), (no_lift))
end else begin
if (type_leq g t_else t_then) then begin
((t_then), (no_lift))
end else begin
((FStar_Extraction_ML_Syntax.MLTY_Top), (FStar_Extraction_ML_Syntax.apply_obj_repr))
end
end
in (match (_78_1537) with
| (t_branch, maybe_lift) -> begin
(let _170_472 = (let _170_470 = (let _170_469 = (let _170_468 = (maybe_lift then_mle t_then)
in (let _170_467 = (let _170_466 = (maybe_lift else_mle t_else)
in Some (_170_466))
in ((e), (_170_468), (_170_467))))
in FStar_Extraction_ML_Syntax.MLE_If (_170_469))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) _170_470))
in (let _170_471 = (FStar_Extraction_ML_Util.join f_then f_else)
in ((_170_472), (_170_471), (t_branch))))
end))
end))
end))
end
| _78_1539 -> begin
(FStar_All.failwith "ITE pats matched but then and else expressions not found?")
end)
end else begin
(

let _78_1571 = (FStar_All.pipe_right pats (FStar_Util.fold_map (fun compat br -> (

let _78_1545 = (FStar_Syntax_Subst.open_branch br)
in (match (_78_1545) with
| (pat, when_opt, branch) -> begin
(

let _78_1549 = (extract_pat g pat t_e)
in (match (_78_1549) with
| (env, p, pat_t_compat) -> begin
(

let _78_1560 = (match (when_opt) with
| None -> begin
((None), (FStar_Extraction_ML_Syntax.E_PURE))
end
| Some (w) -> begin
(

let _78_1556 = (term_as_mlexpr env w)
in (match (_78_1556) with
| (w, f_w, t_w) -> begin
(

let w = (maybe_coerce env w t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in ((Some (w)), (f_w)))
end))
end)
in (match (_78_1560) with
| (when_opt, f_when) -> begin
(

let _78_1564 = (term_as_mlexpr env branch)
in (match (_78_1564) with
| (mlbranch, f_branch, t_branch) -> begin
(let _170_476 = (FStar_All.pipe_right p (FStar_List.map (fun _78_1567 -> (match (_78_1567) with
| (p, wopt) -> begin
(

let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt)
in ((p), (((when_clause), (f_when))), (((mlbranch), (f_branch), (t_branch)))))
end))))
in (((compat && pat_t_compat)), (_170_476)))
end))
end))
end))
end))) true))
in (match (_78_1571) with
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

let _78_1580 = (let _170_478 = (let _170_477 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Extraction_ML_UEnv.lookup_fv g _170_477))
in (FStar_All.pipe_left FStar_Util.right _170_478))
in (match (_78_1580) with
| (fw, _78_1577, _78_1579) -> begin
(let _170_483 = (let _170_482 = (let _170_481 = (let _170_480 = (let _170_479 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (_170_479)::[])
in ((fw), (_170_480)))
in FStar_Extraction_ML_Syntax.MLE_App (_170_481))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) _170_482))
in ((_170_483), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
end))
end
| ((_78_1583, _78_1585, (_78_1587, f_first, t_first)))::rest -> begin
(

let _78_1613 = (FStar_List.fold_left (fun _78_1595 _78_1605 -> (match (((_78_1595), (_78_1605))) with
| ((topt, f), (_78_1597, _78_1599, (_78_1601, f_branch, t_branch))) -> begin
(

let f = (FStar_Extraction_ML_Util.join f f_branch)
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
in (match (_78_1613) with
| (topt, f_match) -> begin
(

let mlbranches = (FStar_All.pipe_right mlbranches (FStar_List.map (fun _78_1624 -> (match (_78_1624) with
| (p, (wopt, _78_1617), (b, _78_1621, t)) -> begin
(

let b = (match (topt) with
| None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b t)
end
| Some (_78_1627) -> begin
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
in (let _170_487 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match (((e), (mlbranches)))))
in ((_170_487), (f_match), (t_match)))))
end))
end)))
end))
end)
end))
end))
end))))


let fresh : Prims.string  ->  (Prims.string * Prims.int) = (

let c = (FStar_Util.mk_ref 0)
in (fun x -> (

let _78_1637 = (FStar_Util.incr c)
in (let _170_490 = (FStar_ST.read c)
in ((x), (_170_490))))))


let ind_discriminator_body : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (

let _78_1645 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv discName)
in (match (_78_1645) with
| (_78_1643, fstar_disc_type) -> begin
(

let wildcards = (match ((let _170_497 = (FStar_Syntax_Subst.compress fstar_disc_type)
in _170_497.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _78_1648) -> begin
(let _170_501 = (FStar_All.pipe_right binders (FStar_List.filter (fun _78_4 -> (match (_78_4) with
| (_78_1653, Some (FStar_Syntax_Syntax.Implicit (_78_1655))) -> begin
true
end
| _78_1660 -> begin
false
end))))
in (FStar_All.pipe_right _170_501 (FStar_List.map (fun _78_1661 -> (let _170_500 = (fresh "_")
in ((_170_500), (FStar_Extraction_ML_Syntax.MLTY_Top)))))))
end
| _78_1664 -> begin
(FStar_All.failwith "Discriminator must be a function")
end)
in (

let mlid = (fresh "_discr_")
in (

let targ = FStar_Extraction_ML_Syntax.MLTY_Top
in (

let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top
in (

let discrBody = (let _170_516 = (let _170_515 = (let _170_514 = (let _170_513 = (let _170_512 = (let _170_511 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name ((([]), ((FStar_Extraction_ML_Syntax.idsym mlid))))))
in (let _170_510 = (let _170_509 = (let _170_505 = (let _170_503 = (let _170_502 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in ((_170_502), ((FStar_Extraction_ML_Syntax.MLP_Wild)::[])))
in FStar_Extraction_ML_Syntax.MLP_CTor (_170_503))
in (let _170_504 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in ((_170_505), (None), (_170_504))))
in (let _170_508 = (let _170_507 = (let _170_506 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in ((FStar_Extraction_ML_Syntax.MLP_Wild), (None), (_170_506)))
in (_170_507)::[])
in (_170_509)::_170_508))
in ((_170_511), (_170_510))))
in FStar_Extraction_ML_Syntax.MLE_Match (_170_512))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _170_513))
in (((FStar_List.append wildcards ((((mlid), (targ)))::[]))), (_170_514)))
in FStar_Extraction_ML_Syntax.MLE_Fun (_170_515))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) _170_516))
in FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NoLetQualifier), (({FStar_Extraction_ML_Syntax.mllb_name = (FStar_Extraction_ML_UEnv.convIdent discName.FStar_Ident.ident); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.print_typ = false})::[]))))))))
end)))




