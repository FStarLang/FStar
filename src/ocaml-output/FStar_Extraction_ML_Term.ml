
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


let record_fields = (fun fs vs -> (FStar_List.map2 (fun f e -> ((f.FStar_Ident.idText), (e))) fs vs))


let fail = (fun r msg -> (

let _82_22 = (let _181_33 = (let _181_32 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _181_32 msg))
in (FStar_All.pipe_left FStar_Util.print_string _181_33))
in (failwith msg)))


let err_uninst = (fun env t _82_28 -> (match (_82_28) with
| (vars, ty) -> begin
(let _181_41 = (let _181_40 = (FStar_Syntax_Print.term_to_string t)
in (let _181_39 = (let _181_37 = (FStar_All.pipe_right vars (FStar_List.map Prims.fst))
in (FStar_All.pipe_right _181_37 (FStar_String.concat ", ")))
in (let _181_38 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated" _181_40 _181_39 _181_38))))
in (fail t.FStar_Syntax_Syntax.pos _181_41))
end))


let err_ill_typed_application = (fun env t args ty -> (let _181_51 = (let _181_50 = (FStar_Syntax_Print.term_to_string t)
in (let _181_49 = (let _181_47 = (FStar_All.pipe_right args (FStar_List.map (fun _82_36 -> (match (_82_36) with
| (x, _82_35) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _181_47 (FStar_String.concat " ")))
in (let _181_48 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n" _181_50 _181_49 _181_48))))
in (fail t.FStar_Syntax_Syntax.pos _181_51)))


let err_value_restriction = (fun t -> (let _181_55 = (let _181_54 = (FStar_Syntax_Print.tag_of_term t)
in (let _181_53 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Refusing to generalize because of the value restriction: (%s) %s" _181_54 _181_53)))
in (fail t.FStar_Syntax_Syntax.pos _181_55)))


let err_unexpected_eff = (fun t f0 f1 -> (let _181_60 = (let _181_59 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" _181_59 (FStar_Extraction_ML_Util.eff_to_string f0) (FStar_Extraction_ML_Util.eff_to_string f1)))
in (fail t.FStar_Syntax_Syntax.pos _181_60)))


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
| Some (_82_50, c) -> begin
(delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c))
end)
in (

let _82_55 = (FStar_Util.smap_add cache l.FStar_Ident.str res)
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


let rec is_arity : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t = (FStar_Syntax_Util.unmeta t)
in (match ((let _181_73 = (FStar_Syntax_Subst.compress t)
in _181_73.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_meta (_)) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) -> begin
false
end
| FStar_Syntax_Syntax.Tm_type (_82_86) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (_82_89, c) -> begin
(is_arity env (FStar_Syntax_Util.comp_result c))
end
| FStar_Syntax_Syntax.Tm_fvar (_82_94) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.FStar_Extraction_ML_UEnv.tcenv t)
in (match ((let _181_74 = (FStar_Syntax_Subst.compress t)
in _181_74.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (_82_98) -> begin
false
end
| _82_101 -> begin
(is_arity env t)
end))
end
| FStar_Syntax_Syntax.Tm_app (_82_103) -> begin
(

let _82_108 = (FStar_Syntax_Util.head_and_args t)
in (match (_82_108) with
| (head, _82_107) -> begin
(is_arity env head)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (head, _82_111) -> begin
(is_arity env head)
end
| FStar_Syntax_Syntax.Tm_refine (x, _82_116) -> begin
(is_arity env x.FStar_Syntax_Syntax.sort)
end
| (FStar_Syntax_Syntax.Tm_abs (_, body, _)) | (FStar_Syntax_Syntax.Tm_let (_, body)) -> begin
(is_arity env body)
end
| FStar_Syntax_Syntax.Tm_match (_82_131, branches) -> begin
(match (branches) with
| ((_82_138, _82_140, e))::_82_136 -> begin
(is_arity env e)
end
| _82_145 -> begin
false
end)
end)))


let rec is_type_aux : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _181_80 = (let _181_79 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: %s" _181_79))
in (failwith _181_80))
end
| FStar_Syntax_Syntax.Tm_constant (_82_154) -> begin
false
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.failwith_lid) -> begin
false
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
if (FStar_TypeChecker_Env.is_type_constructor env.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) then begin
true
end else begin
(

let _82_172 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_82_172) with
| (_82_170, t) -> begin
(is_arity env t)
end))
end
end
| (FStar_Syntax_Syntax.Tm_uvar (_, t)) | (FStar_Syntax_Syntax.Tm_bvar ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})) | (FStar_Syntax_Syntax.Tm_name ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})) -> begin
(is_arity env t)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _82_192, _82_194) -> begin
(is_type_aux env t)
end
| FStar_Syntax_Syntax.Tm_uinst (t, _82_199) -> begin
(is_type_aux env t)
end
| FStar_Syntax_Syntax.Tm_abs (_82_203, body, _82_206) -> begin
(is_type_aux env body)
end
| FStar_Syntax_Syntax.Tm_let (_82_210, body) -> begin
(is_type_aux env body)
end
| FStar_Syntax_Syntax.Tm_match (_82_215, branches) -> begin
(match (branches) with
| ((_82_222, _82_224, e))::_82_220 -> begin
(is_type_aux env e)
end
| _82_229 -> begin
(failwith "Empty branches")
end)
end
| FStar_Syntax_Syntax.Tm_meta (t, _82_232) -> begin
(is_type_aux env t)
end
| FStar_Syntax_Syntax.Tm_app (head, _82_237) -> begin
(is_type_aux env head)
end)))


let is_type : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let b = (is_type_aux env t)
in (

let _82_245 = (FStar_Extraction_ML_UEnv.debug env (fun _82_243 -> if b then begin
(let _181_87 = (FStar_Syntax_Print.term_to_string t)
in (let _181_86 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "is_type %s (%s)\n" _181_87 _181_86)))
end else begin
(let _181_89 = (FStar_Syntax_Print.term_to_string t)
in (let _181_88 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "not a type %s (%s)\n" _181_89 _181_88)))
end))
in b)))


let is_type_binder = (fun env x -> (is_arity env (Prims.fst x).FStar_Syntax_Syntax.sort))


let is_constructor : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _181_94 = (FStar_Syntax_Subst.compress t)
in _181_94.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _82_269 -> begin
false
end))


let rec is_fstar_value : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _181_97 = (FStar_Syntax_Subst.compress t)
in _181_97.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
if (is_constructor head) then begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _82_290 -> (match (_82_290) with
| (te, _82_289) -> begin
(is_fstar_value te)
end))))
end else begin
false
end
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t, _, _)) -> begin
(is_fstar_value t)
end
| _82_303 -> begin
false
end))


let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Fun (_)) -> begin
true
end
| (FStar_Extraction_ML_Syntax.MLE_CTor (_, exps)) | (FStar_Extraction_ML_Syntax.MLE_Tuple (exps)) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (_82_324, fields) -> begin
(FStar_Util.for_all (fun _82_331 -> (match (_82_331) with
| (_82_329, e) -> begin
(is_ml_value e)
end)) fields)
end
| _82_333 -> begin
false
end))


let normalize_abs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t0 -> (

let rec aux = (fun bs t copt -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs', body, copt) -> begin
(aux (FStar_List.append bs bs') body copt)
end
| _82_346 -> begin
(

let e' = (FStar_Syntax_Util.unascribe t)
in if (FStar_Syntax_Util.is_fun e') then begin
(aux bs e' copt)
end else begin
(FStar_Syntax_Util.abs bs e' copt)
end)
end)))
in (aux [] t0 None)))


let unit_binder : FStar_Syntax_Syntax.binder = (let _181_110 = (FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _181_110))


let check_pats_for_ite : (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term Prims.option) = (fun l -> (

let def = ((false), (None), (None))
in if ((FStar_List.length l) <> (Prims.parse_int "2")) then begin
def
end else begin
(

let _82_353 = (FStar_List.hd l)
in (match (_82_353) with
| (p1, w1, e1) -> begin
(

let _82_357 = (let _181_113 = (FStar_List.tl l)
in (FStar_List.hd _181_113))
in (match (_82_357) with
| (p2, w2, e2) -> begin
(match (((w1), (w2), (p1.FStar_Syntax_Syntax.v), (p2.FStar_Syntax_Syntax.v))) with
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
((true), (Some (e1)), (Some (e2)))
end
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
((true), (Some (e2)), (Some (e1)))
end
| _82_377 -> begin
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
| _82_398 -> begin
(

let _82_400 = (FStar_Extraction_ML_UEnv.debug g (fun _82_399 -> (match (()) with
| () -> begin
(let _181_143 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (let _181_142 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (let _181_141 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule expect)
in (FStar_Util.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n" _181_143 _181_142 _181_141))))
end)))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (ty), (expect))))))
end)))


let bv_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bv -> (match ((FStar_Extraction_ML_UEnv.lookup_bv g bv)) with
| FStar_Util.Inl (_82_405, t) -> begin
t
end
| _82_410 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end))


let rec term_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t0 -> (

let rec is_top_ty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
true
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_82_417) -> begin
(match ((FStar_Extraction_ML_Util.udelta_unfold g t)) with
| None -> begin
false
end
| Some (t) -> begin
(is_top_ty t)
end)
end
| _82_423 -> begin
false
end))
in (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t0)
in (

let mlt = (term_as_mlty' g t)
in if (is_top_ty mlt) then begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t0)
in (term_as_mlty' g t))
end else begin
mlt
end))))
and term_as_mlty' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun env t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _181_166 = (let _181_165 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Impossible: Unexpected term %s" _181_165))
in (failwith _181_166))
end
| FStar_Syntax_Syntax.Tm_constant (_82_438) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_uvar (_82_441) -> begin
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

let _82_477 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_82_477) with
| (bs, c) -> begin
(

let _82_480 = (binders_as_ml_binders env bs)
in (match (_82_480) with
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

let _82_497 = (FStar_List.fold_right (fun _82_490 _82_493 -> (match (((_82_490), (_82_493))) with
| ((_82_488, t), (tag, t')) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((t), (tag), (t')))))
end)) mlbs ((erase), (t_ret)))
in (match (_82_497) with
| (_82_495, t) -> begin
t
end))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let res = (match ((let _181_169 = (FStar_Syntax_Util.un_uinst head)
in _181_169.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv args)
end
| FStar_Syntax_Syntax.Tm_app (head, args') -> begin
(let _181_170 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head), ((FStar_List.append args' args))))) None t.FStar_Syntax_Syntax.pos)
in (term_as_mlty' env _181_170))
end
| _82_511 -> begin
FStar_Extraction_ML_UEnv.unknownType
end)
in res)
end
| FStar_Syntax_Syntax.Tm_abs (bs, ty, _82_516) -> begin
(

let _82_521 = (FStar_Syntax_Subst.open_term bs ty)
in (match (_82_521) with
| (bs, ty) -> begin
(

let _82_524 = (binders_as_ml_binders env bs)
in (match (_82_524) with
| (bts, env) -> begin
(term_as_mlty' env ty)
end))
end))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
FStar_Extraction_ML_UEnv.unknownType
end)))
and arg_as_mlty : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  FStar_Extraction_ML_Syntax.mlty = (fun g _82_538 -> (match (_82_538) with
| (a, _82_537) -> begin
if (is_type g a) then begin
(term_as_mlty' g a)
end else begin
FStar_Extraction_ML_UEnv.erasedContent
end
end))
and fv_app_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.args  ->  FStar_Extraction_ML_Syntax.mlty = (fun g fv args -> (

let _82_544 = (FStar_Syntax_Util.arrow_formals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (match (_82_544) with
| (formals, t) -> begin
(

let mlargs = (FStar_List.map (arg_as_mlty g) args)
in (

let mlargs = (

let n_args = (FStar_List.length args)
in if ((FStar_List.length formals) > n_args) then begin
(

let _82_550 = (FStar_Util.first_N n_args formals)
in (match (_82_550) with
| (_82_548, rest) -> begin
(let _181_177 = (FStar_List.map (fun _82_551 -> FStar_Extraction_ML_UEnv.erasedContent) rest)
in (FStar_List.append mlargs _181_177))
end))
end else begin
mlargs
end)
in (

let nm = (match ((FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv)) with
| Some (p) -> begin
p
end
| None -> begin
(FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end)
in FStar_Extraction_ML_Syntax.MLTY_Named (((mlargs), (nm))))))
end)))
and binders_as_ml_binders : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list * FStar_Extraction_ML_UEnv.env) = (fun g bs -> (

let _82_573 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _82_562 b -> (match (_82_562) with
| (ml_bs, env) -> begin
if (is_type_binder g b) then begin
(

let b = (Prims.fst b)
in (

let env = (FStar_Extraction_ML_UEnv.extend_ty env b (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (

let ml_b = (let _181_182 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b)
in ((_181_182), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
in (((ml_b)::ml_bs), (env)))))
end else begin
(

let b = (Prims.fst b)
in (

let t = (term_as_mlty env b.FStar_Syntax_Syntax.sort)
in (

let env = (FStar_Extraction_ML_UEnv.extend_bv env b (([]), (t)) false false false)
in (

let ml_b = (let _181_183 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b)
in ((_181_183), (t)))
in (((ml_b)::ml_bs), (env))))))
end
end)) (([]), (g))))
in (match (_82_573) with
| (ml_bs, env) -> begin
(((FStar_List.rev ml_bs)), (env))
end)))


let mk_MLE_Seq : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun e1 e2 -> (match (((e1.FStar_Extraction_ML_Syntax.expr), (e2.FStar_Extraction_ML_Syntax.expr))) with
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 es2))
end
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), _82_584) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 ((e2)::[])))
end
| (_82_587, FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::es2)
end
| _82_592 -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::(e2)::[])
end))


let mk_MLE_Let : Prims.bool  ->  FStar_Extraction_ML_Syntax.mlletbinding  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun top_level lbs body -> (match (lbs) with
| (FStar_Extraction_ML_Syntax.NonRec, quals, (lb)::[]) when (not (top_level)) -> begin
(match (lb.FStar_Extraction_ML_Syntax.mllb_tysc) with
| Some ([], t) when (t = FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
if (body.FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr) then begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end else begin
(match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Var (x) when (x = lb.FStar_Extraction_ML_Syntax.mllb_name) -> begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end
| _82_608 when (lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr) -> begin
body.FStar_Extraction_ML_Syntax.expr
end
| _82_610 -> begin
(mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def body)
end)
end
end
| _82_612 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end)
end
| _82_614 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end))


let resugar_pat : FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_ML_Syntax.mlpattern = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(match ((FStar_Extraction_ML_Util.is_xtuple d)) with
| Some (n) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| _82_624 -> begin
(match (q) with
| Some (FStar_Syntax_Syntax.Record_ctor (ty, fns)) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns)
in (

let fs = (record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record (((path), (fs)))))
end
| _82_633 -> begin
p
end)
end)
end
| _82_635 -> begin
p
end))


let extract_pat : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option) Prims.list * Prims.bool) = (fun g p expected_t -> (

let rec extract_one_pat = (fun disjunctive_pat imp g p expected_topt -> (

let ok = (fun t -> (match (expected_topt) with
| None -> begin
true
end
| Some (t') -> begin
(

let ok = (type_leq g t t')
in (

let _82_653 = if (not (ok)) then begin
(FStar_Extraction_ML_UEnv.debug g (fun _82_651 -> (let _181_218 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t')
in (let _181_217 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t)
in (FStar_Util.print2 "Expected pattern type %s; got pattern type %s\n" _181_218 _181_217)))))
end else begin
()
end
in ok))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_82_656) -> begin
(failwith "Impossible: Nested disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int (c, None)) -> begin
(

let i = FStar_Const.Const_int (((c), (None)))
in (

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let when_clause = (let _181_227 = (let _181_226 = (let _181_225 = (let _181_224 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (let _181_223 = (let _181_222 = (let _181_221 = (let _181_220 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p i)
in (FStar_All.pipe_left (fun _181_219 -> FStar_Extraction_ML_Syntax.MLE_Const (_181_219)) _181_220))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) _181_221))
in (_181_222)::[])
in (_181_224)::_181_223))
in ((FStar_Extraction_ML_Util.prims_op_equality), (_181_225)))
in FStar_Extraction_ML_Syntax.MLE_App (_181_226))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _181_227))
in (let _181_228 = (ok FStar_Extraction_ML_Syntax.ml_int_ty)
in ((g), (Some (((FStar_Extraction_ML_Syntax.MLP_Var (x)), ((when_clause)::[])))), (_181_228))))))
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(

let t = (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange s)
in (

let mlty = (term_as_mlty g t)
in (let _181_233 = (let _181_231 = (let _181_230 = (let _181_229 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (_181_229))
in ((_181_230), ([])))
in Some (_181_231))
in (let _181_232 = (ok mlty)
in ((g), (_181_233), (_181_232))))))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let g = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (let _181_238 = if imp then begin
None
end else begin
(let _181_236 = (let _181_235 = (let _181_234 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in FStar_Extraction_ML_Syntax.MLP_Var (_181_234))
in ((_181_235), ([])))
in Some (_181_236))
end
in (let _181_237 = (ok mlty)
in ((g), (_181_238), (_181_237))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) when disjunctive_pat -> begin
((g), (Some (((FStar_Extraction_ML_Syntax.MLP_Wild), ([])))), (true))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let g = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (let _181_243 = if imp then begin
None
end else begin
(let _181_241 = (let _181_240 = (let _181_239 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in FStar_Extraction_ML_Syntax.MLP_Var (_181_239))
in ((_181_240), ([])))
in Some (_181_241))
end
in (let _181_242 = (ok mlty)
in ((g), (_181_243), (_181_242))))))
end
| FStar_Syntax_Syntax.Pat_dot_term (_82_681) -> begin
((g), (None), (true))
end
| FStar_Syntax_Syntax.Pat_cons (f, pats) -> begin
(

let _82_703 = (match ((FStar_Extraction_ML_UEnv.lookup_fv g f)) with
| FStar_Util.Inr ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n); FStar_Extraction_ML_Syntax.mlty = _82_690; FStar_Extraction_ML_Syntax.loc = _82_688}, ttys, _82_696) -> begin
((n), (ttys))
end
| _82_700 -> begin
(failwith "Expected a constructor")
end)
in (match (_82_703) with
| (d, tys) -> begin
(

let nTyVars = (FStar_List.length (Prims.fst tys))
in (

let _82_707 = (FStar_Util.first_N nTyVars pats)
in (match (_82_707) with
| (tysVarPats, restPats) -> begin
(

let f_ty_opt = try
(match (()) with
| () -> begin
(

let mlty_args = (FStar_All.pipe_right tysVarPats (FStar_List.map (fun _82_717 -> (match (_82_717) with
| (p, _82_716) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (_82_719, t) -> begin
(term_as_mlty g t)
end
| _82_724 -> begin
(

let _82_727 = (FStar_Extraction_ML_UEnv.debug g (fun _82_725 -> (let _181_247 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print1 "Pattern %s is not extractable" _181_247))))
in (Prims.raise Un_extractable))
end)
end))))
in (

let f_ty = (FStar_Extraction_ML_Util.subst tys mlty_args)
in (let _181_248 = (FStar_Extraction_ML_Util.uncurry_mlty_fun f_ty)
in Some (_181_248))))
end)
with
| Un_extractable -> begin
None
end
in (

let _82_743 = (FStar_Util.fold_map (fun g _82_735 -> (match (_82_735) with
| (p, imp) -> begin
(

let _82_740 = (extract_one_pat disjunctive_pat true g p None)
in (match (_82_740) with
| (g, p, _82_739) -> begin
((g), (p))
end))
end)) g tysVarPats)
in (match (_82_743) with
| (g, tyMLPats) -> begin
(

let _82_770 = (FStar_Util.fold_map (fun _82_746 _82_749 -> (match (((_82_746), (_82_749))) with
| ((g, f_ty_opt), (p, imp)) -> begin
(

let _82_760 = (match (f_ty_opt) with
| Some ((hd)::rest, res) -> begin
((Some (((rest), (res)))), (Some (hd)))
end
| _82_757 -> begin
((None), (None))
end)
in (match (_82_760) with
| (f_ty_opt, expected_ty) -> begin
(

let _82_765 = (extract_one_pat disjunctive_pat false g p expected_ty)
in (match (_82_765) with
| (g, p, _82_764) -> begin
((((g), (f_ty_opt))), (p))
end))
end))
end)) ((g), (f_ty_opt)) restPats)
in (match (_82_770) with
| ((g, f_ty_opt), restMLPats) -> begin
(

let _82_778 = (let _181_255 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun _82_1 -> (match (_82_1) with
| Some (x) -> begin
(x)::[]
end
| _82_775 -> begin
[]
end))))
in (FStar_All.pipe_right _181_255 FStar_List.split))
in (match (_82_778) with
| (mlPats, when_clauses) -> begin
(

let pat_ty_compat = (match (f_ty_opt) with
| Some ([], t) -> begin
(ok t)
end
| _82_784 -> begin
false
end)
in (let _181_259 = (let _181_258 = (let _181_257 = (resugar_pat f.FStar_Syntax_Syntax.fv_qual (FStar_Extraction_ML_Syntax.MLP_CTor (((d), (mlPats)))))
in (let _181_256 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in ((_181_257), (_181_256))))
in Some (_181_258))
in ((g), (_181_259), (pat_ty_compat))))
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
| _82_799 -> begin
(failwith "Impossible: Unable to translate pattern")
end))
in (

let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| (hd)::tl -> begin
(let _181_270 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl)
in Some (_181_270))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible: Empty disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_disj ((p)::pats) -> begin
(

let _82_815 = (extract_one_pat true g p (Some (expected_t)))
in (match (_82_815) with
| (g, p, b) -> begin
(

let _82_825 = (FStar_Util.fold_map (fun b p -> (

let _82_822 = (extract_one_pat true g p (Some (expected_t)))
in (match (_82_822) with
| (_82_819, p, b') -> begin
(((b && b')), (p))
end))) b pats)
in (match (_82_825) with
| (b, ps) -> begin
(

let ps = (p)::ps
in (

let _82_840 = (FStar_All.pipe_right ps (FStar_List.partition (fun _82_2 -> (match (_82_2) with
| (_82_829, (_82_833)::_82_831) -> begin
true
end
| _82_837 -> begin
false
end))))
in (match (_82_840) with
| (ps_when, rest) -> begin
(

let ps = (FStar_All.pipe_right ps_when (FStar_List.map (fun _82_843 -> (match (_82_843) with
| (x, whens) -> begin
(let _181_275 = (mk_when_clause whens)
in ((x), (_181_275)))
end))))
in (

let res = (match (rest) with
| [] -> begin
((g), (ps), (b))
end
| rest -> begin
(let _181_279 = (let _181_278 = (let _181_277 = (let _181_276 = (FStar_List.map Prims.fst rest)
in FStar_Extraction_ML_Syntax.MLP_Branch (_181_276))
in ((_181_277), (None)))
in (_181_278)::ps)
in ((g), (_181_279), (b)))
end)
in res))
end)))
end))
end))
end
| _82_849 -> begin
(

let _82_855 = (extract_one_pat false g p (Some (expected_t)))
in (match (_82_855) with
| (g, (p, whens), b) -> begin
(

let when_clause = (mk_when_clause whens)
in ((g), ((((p), (when_clause)))::[]), (b)))
end))
end)))))


let maybe_eta_data_and_project_record : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (

let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, _82_866, t1) -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _181_294 = (let _181_293 = (let _181_292 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((((x), (t0))), (_181_292)))
in (_181_293)::more_args)
in (eta_args _181_294 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_82_872, _82_874) -> begin
(((FStar_List.rev more_args)), (t))
end
| _82_878 -> begin
(failwith "Impossible: Head type is not an arrow")
end))
in (

let as_record = (fun qual e -> (match (((e.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (_82_883, args), Some (FStar_Syntax_Syntax.Record_ctor (tyname, fields))) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns)
in (

let fields = (record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record (((path), (fields)))))))
end
| _82_896 -> begin
e
end))
in (

let resugar_and_maybe_eta = (fun qual e -> (

let _82_902 = (eta_args [] residualType)
in (match (_82_902) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(let _181_303 = (as_record qual e)
in (FStar_Extraction_ML_Util.resugar_exp _181_303))
end
| _82_905 -> begin
(

let _82_908 = (FStar_List.unzip eargs)
in (match (_82_908) with
| (binders, eargs) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head, args) -> begin
(

let body = (let _181_305 = (let _181_304 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor (((head), ((FStar_List.append args eargs))))))
in (FStar_All.pipe_left (as_record qual) _181_304))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp _181_305))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun (((binders), (body))))))
end
| _82_915 -> begin
(failwith "Impossible: Not a constructor")
end)
end))
end)
end)))
in (match (((mlAppExpr.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (_82_917, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _82_923; FStar_Extraction_ML_Syntax.loc = _82_921}, (mle)::args), Some (FStar_Syntax_Syntax.Record_projector (constrname, f))) -> begin
(

let f = (FStar_Ident.lid_of_ids (FStar_List.append constrname.FStar_Ident.ns ((f)::[])))
in (

let fn = (FStar_Extraction_ML_Util.mlpath_of_lid f)
in (

let proj = FStar_Extraction_ML_Syntax.MLE_Proj (((mle), (fn)))
in (

let e = (match (args) with
| [] -> begin
proj
end
| _82_943 -> begin
(let _181_307 = (let _181_306 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in ((_181_306), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (_181_307))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e)))))
end
| ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _181_308 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _181_308))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _181_309 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _181_309))
end
| _82_983 -> begin
mlAppExpr
end)))))


let maybe_downgrade_eff : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag = (fun g f t -> if ((f = FStar_Extraction_ML_Syntax.E_GHOST) && (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty)) then begin
FStar_Extraction_ML_Syntax.E_PURE
end else begin
f
end)


let rec term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g t -> (

let _82_992 = (term_as_mlexpr' g t)
in (match (_82_992) with
| (e, tag, ty) -> begin
(

let tag = (maybe_downgrade_eff g tag ty)
in (

let _82_995 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (let _181_334 = (let _181_333 = (FStar_Syntax_Print.tag_of_term t)
in (let _181_332 = (FStar_Syntax_Print.term_to_string t)
in (let _181_331 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format4 "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n" _181_333 _181_332 _181_331 (FStar_Extraction_ML_Util.eff_to_string tag)))))
in (FStar_Util.print_string _181_334))))
in (erase g e ty tag)))
end)))
and check_term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g t f ty -> (

let _82_1003 = (check_term_as_mlexpr' g t f ty)
in (match (_82_1003) with
| (e, t) -> begin
(

let _82_1008 = (erase g e t f)
in (match (_82_1008) with
| (r, _82_1006, t) -> begin
((r), (t))
end))
end)))
and check_term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g e0 f ty -> (

let _82_1016 = (term_as_mlexpr g e0)
in (match (_82_1016) with
| (e, tag, t) -> begin
(

let tag = (maybe_downgrade_eff g tag t)
in if (FStar_Extraction_ML_Util.eff_leq tag f) then begin
(let _181_343 = (maybe_coerce g e t ty)
in ((_181_343), (ty)))
end else begin
(err_unexpected_eff e0 f tag)
end)
end)))
and term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g top -> (

let _82_1021 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (let _181_350 = (let _181_349 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _181_348 = (FStar_Syntax_Print.tag_of_term top)
in (let _181_347 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format3 "%s: term_as_mlexpr\' (%s) :  %s \n" _181_349 _181_348 _181_347))))
in (FStar_Util.print_string _181_350))))
in (

let t = (FStar_Syntax_Subst.compress top)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) -> begin
(let _181_352 = (let _181_351 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" _181_351))
in (failwith _181_352))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc)) -> begin
(match ((term_as_mlexpr' g t)) with
| ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let ((FStar_Extraction_ML_Syntax.NonRec, flags, bodies), continuation); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}, tag, typ) -> begin
(({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let (((((FStar_Extraction_ML_Syntax.NonRec), ((FStar_Extraction_ML_Syntax.Mutable)::flags), (bodies))), (continuation))); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}), (tag), (typ))
end
| _82_1062 -> begin
(failwith "impossible")
end)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, _82_1066)) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) when (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl g.FStar_Extraction_ML_UEnv.tcenv m)
in if (let _181_353 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right _181_353 Prims.op_Negation)) then begin
(term_as_mlexpr' g t)
end else begin
(

let ml_result_ty_1 = (term_as_mlty g lb.FStar_Syntax_Syntax.lbtyp)
in (

let _82_1086 = (term_as_mlexpr g lb.FStar_Syntax_Syntax.lbdef)
in (match (_82_1086) with
| (comp_1, _82_1083, _82_1085) -> begin
(

let _82_1105 = (

let k = (let _181_356 = (let _181_355 = (let _181_354 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_All.pipe_right _181_354 FStar_Syntax_Syntax.mk_binder))
in (_181_355)::[])
in (FStar_Syntax_Util.abs _181_356 body None))
in (

let _82_1092 = (term_as_mlexpr g k)
in (match (_82_1092) with
| (ml_k, _82_1090, t_k) -> begin
(

let m_2 = (match (t_k) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_82_1094, _82_1096, m_2) -> begin
m_2
end
| _82_1101 -> begin
(failwith "Impossible")
end)
in ((ml_k), (m_2)))
end)))
in (match (_82_1105) with
| (ml_k, ty) -> begin
(

let bind = (let _181_359 = (let _181_358 = (let _181_357 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (FStar_All.pipe_right _181_357 Prims.fst))
in FStar_Extraction_ML_Syntax.MLE_Name (_181_358))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _181_359))
in (let _181_360 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) (FStar_Extraction_ML_Syntax.MLE_App (((bind), ((comp_1)::(ml_k)::[])))))
in ((_181_360), (FStar_Extraction_ML_Syntax.E_IMPURE), (ty))))
end))
end)))
end)
end
| _82_1108 -> begin
(term_as_mlexpr' g t)
end))
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_uinst (t, _)) -> begin
(term_as_mlexpr' g t)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let _82_1125 = (FStar_TypeChecker_TcTerm.type_of_tot_term g.FStar_Extraction_ML_UEnv.tcenv t)
in (match (_82_1125) with
| (_82_1121, ty, _82_1124) -> begin
(

let ml_ty = (term_as_mlty g ty)
in (let _181_364 = (let _181_363 = (let _181_362 = (FStar_Extraction_ML_Util.mlconst_of_const' t.FStar_Syntax_Syntax.pos c)
in (FStar_All.pipe_left (fun _181_361 -> FStar_Extraction_ML_Syntax.MLE_Const (_181_361)) _181_362))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty _181_363))
in ((_181_364), (FStar_Extraction_ML_Syntax.E_PURE), (ml_ty))))
end))
end
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
if (is_type g t) then begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end else begin
(match ((FStar_Extraction_ML_UEnv.lookup_term g t)) with
| (FStar_Util.Inl (_82_1134), _82_1137) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| (FStar_Util.Inr (x, mltys, _82_1142), qual) -> begin
(match (mltys) with
| ([], t) when (t = FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t))
end
| ([], t) -> begin
(let _181_365 = (maybe_eta_data_and_project_record g qual t x)
in ((_181_365), (FStar_Extraction_ML_Syntax.E_PURE), (t)))
end
| _82_1154 -> begin
(err_uninst g t mltys)
end)
end)
end
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, copt) -> begin
(

let _82_1162 = (FStar_Syntax_Subst.open_term bs body)
in (match (_82_1162) with
| (bs, body) -> begin
(

let _82_1165 = (binders_as_ml_binders g bs)
in (match (_82_1165) with
| (ml_bs, env) -> begin
(

let _82_1169 = (term_as_mlexpr env body)
in (match (_82_1169) with
| (ml_body, f, t) -> begin
(

let _82_1179 = (FStar_List.fold_right (fun _82_1173 _82_1176 -> (match (((_82_1173), (_82_1176))) with
| ((_82_1171, targ), (f, t)) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((targ), (f), (t)))))
end)) ml_bs ((f), (t)))
in (match (_82_1179) with
| (f, tfun) -> begin
(let _181_368 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun (((ml_bs), (ml_body)))))
in ((_181_368), (f), (tfun)))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _82_1185; FStar_Syntax_Syntax.pos = _82_1183; FStar_Syntax_Syntax.vars = _82_1181}, (t)::[]) -> begin
(

let _82_1196 = (term_as_mlexpr' g (Prims.fst t))
in (match (_82_1196) with
| (ml, e_tag, mlty) -> begin
((ml), (FStar_Extraction_ML_Syntax.E_PURE), (mlty))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_82_1204)); FStar_Syntax_Syntax.tk = _82_1202; FStar_Syntax_Syntax.pos = _82_1200; FStar_Syntax_Syntax.vars = _82_1198}, (t)::[]) -> begin
(

let _82_1215 = (term_as_mlexpr' g (Prims.fst t))
in (match (_82_1215) with
| (ml, e_tag, mlty) -> begin
((ml), (FStar_Extraction_ML_Syntax.E_IMPURE), (mlty))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let is_total = (fun _82_4 -> (match (_82_4) with
| FStar_Util.Inl (l) -> begin
(FStar_Syntax_Util.is_total_lcomp l)
end
| FStar_Util.Inr (l, flags) -> begin
((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_All.pipe_right flags (FStar_List.existsb (fun _82_3 -> (match (_82_3) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _82_1230 -> begin
false
end)))))
end))
in (match ((let _181_373 = (let _181_372 = (FStar_Syntax_Subst.compress head)
in _181_372.FStar_Syntax_Syntax.n)
in ((head.FStar_Syntax_Syntax.n), (_181_373)))) with
| (FStar_Syntax_Syntax.Tm_uvar (_82_1233), _82_1236) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t))
end
| (_82_1240, FStar_Syntax_Syntax.Tm_abs (bs, _82_1243, Some (lc))) when (is_total lc) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t))
end
| _82_1251 -> begin
(

let rec extract_app = (fun is_data _82_1256 _82_1259 restArgs -> (match (((_82_1256), (_82_1259))) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match (((restArgs), (t))) with
| ([], _82_1263) -> begin
(

let evaluation_order_guaranteed = ((((FStar_List.length mlargs_f) = (Prims.parse_int "1")) || (FStar_Extraction_ML_Util.codegen_fsharp ())) || (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = {FStar_Syntax_Syntax.v = v; FStar_Syntax_Syntax.ty = _82_1272; FStar_Syntax_Syntax.p = _82_1270}; FStar_Syntax_Syntax.fv_delta = _82_1268; FStar_Syntax_Syntax.fv_qual = _82_1266}) -> begin
((v = FStar_Syntax_Const.op_And) || (v = FStar_Syntax_Const.op_Or))
end
| _82_1278 -> begin
false
end))
in (

let _82_1289 = if evaluation_order_guaranteed then begin
(let _181_382 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in (([]), (_181_382)))
end else begin
(FStar_List.fold_left (fun _82_1282 _82_1285 -> (match (((_82_1282), (_82_1285))) with
| ((lbs, out_args), (arg, f)) -> begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) || (f = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
((lbs), ((arg)::out_args))
end else begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _181_386 = (let _181_385 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (_181_385)::out_args)
in (((((x), (arg)))::lbs), (_181_386))))
end
end)) (([]), ([])) mlargs_f)
end
in (match (_82_1289) with
| (lbs, mlargs) -> begin
(

let app = (let _181_387 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_App (((mlhead), (mlargs)))))
in (FStar_All.pipe_left (maybe_eta_data_and_project_record g is_data t) _181_387))
in (

let l_app = (FStar_List.fold_right (fun _82_1293 out -> (match (_82_1293) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.mlty) (mk_MLE_Let false ((FStar_Extraction_ML_Syntax.NonRec), ([]), (({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = Some ((([]), (arg.FStar_Extraction_ML_Syntax.mlty))); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg; FStar_Extraction_ML_Syntax.print_typ = true})::[])) out))
end)) lbs app)
in ((l_app), (f), (t))))
end)))
end
| (((arg, _82_1299))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (formal_t, f', t)) when (is_type g arg) -> begin
if (type_leq g formal_t FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
(let _181_391 = (let _181_390 = (FStar_Extraction_ML_Util.join arg.FStar_Syntax_Syntax.pos f f')
in ((_181_390), (t)))
in (extract_app is_data ((mlhead), ((((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE)))::mlargs_f)) _181_391 rest))
end else begin
(let _181_396 = (let _181_395 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule mlhead)
in (let _181_394 = (FStar_Syntax_Print.term_to_string arg)
in (let _181_393 = (FStar_Syntax_Print.tag_of_term arg)
in (let _181_392 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule formal_t)
in (FStar_Util.format4 "Impossible: ill-typed application:\n\thead=%s, arg=%s, tag=%s\n\texpected type unit, got %s" _181_395 _181_394 _181_393 _181_392)))))
in (failwith _181_396))
end
end
| (((e0, _82_1311))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t)) -> begin
(

let r = e0.FStar_Syntax_Syntax.pos
in (

let _82_1324 = (term_as_mlexpr g e0)
in (match (_82_1324) with
| (e0, f0, tInferred) -> begin
(

let e0 = (maybe_coerce g e0 tInferred tExpected)
in (let _181_398 = (let _181_397 = (FStar_Extraction_ML_Util.join_l r ((f)::(f')::(f0)::[]))
in ((_181_397), (t)))
in (extract_app is_data ((mlhead), ((((e0), (f0)))::mlargs_f)) _181_398 rest)))
end)))
end
| _82_1327 -> begin
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

let extract_app_maybe_projector = (fun is_data mlhead _82_1336 args -> (match (_82_1336) with
| (f, t) -> begin
(match (is_data) with
| Some (FStar_Syntax_Syntax.Record_projector (_82_1339)) -> begin
(

let rec remove_implicits = (fun args f t -> (match (((args), (t))) with
| (((a0, Some (FStar_Syntax_Syntax.Implicit (_82_1349))))::args, FStar_Extraction_ML_Syntax.MLTY_Fun (_82_1355, f', t)) -> begin
(let _181_413 = (FStar_Extraction_ML_Util.join a0.FStar_Syntax_Syntax.pos f f')
in (remove_implicits args _181_413 t))
end
| _82_1362 -> begin
((args), (f), (t))
end))
in (

let _82_1366 = (remove_implicits args f t)
in (match (_82_1366) with
| (args, f, t) -> begin
(extract_app is_data ((mlhead), ([])) ((f), (t)) args)
end)))
end
| _82_1368 -> begin
(extract_app is_data ((mlhead), ([])) ((f), (t)) args)
end)
end))
in if (is_type g t) then begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end else begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (_82_1371) -> begin
(

let _82_1386 = (match ((FStar_Extraction_ML_UEnv.lookup_term g head)) with
| (FStar_Util.Inr (u), q) -> begin
((u), (q))
end
| _82_1378 -> begin
(failwith "FIXME Ty")
end)
in (match (_82_1386) with
| ((head_ml, (vars, t), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, _82_1391))::_82_1388 -> begin
(is_type g a)
end
| _82_1395 -> begin
false
end)
in (

let _82_1441 = (match (vars) with
| (_82_1400)::_82_1398 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t), (args))
end
| _82_1403 -> begin
(

let n = (FStar_List.length vars)
in if (n <= (FStar_List.length args)) then begin
(

let _82_1407 = (FStar_Util.first_N n args)
in (match (_82_1407) with
| (prefix, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun _82_1411 -> (match (_82_1411) with
| (x, _82_1410) -> begin
(term_as_mlty g x)
end)) prefix)
in (

let t = (instantiate ((vars), (t)) prefixAsMLTypes)
in (

let head = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) -> begin
(

let _82_1420 = head_ml
in {FStar_Extraction_ML_Syntax.expr = _82_1420.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t; FStar_Extraction_ML_Syntax.loc = _82_1420.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = _82_1426; FStar_Extraction_ML_Syntax.loc = _82_1424})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let _82_1433 = head
in {FStar_Extraction_ML_Syntax.expr = _82_1433.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t))); FStar_Extraction_ML_Syntax.loc = _82_1433.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t))
end
| _82_1436 -> begin
(failwith "Impossible: Unexpected head term")
end)
in ((head), (t), (rest)))))
end))
end else begin
(err_uninst g head ((vars), (t)))
end)
end)
in (match (_82_1441) with
| (head_ml, head_t, args) -> begin
(match (args) with
| [] -> begin
(let _181_415 = (maybe_eta_data_and_project_record g qual head_t head_ml)
in ((_181_415), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| _82_1444 -> begin
(extract_app_maybe_projector qual head_ml ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args)
end)
end)))
end))
end
| _82_1446 -> begin
(

let _82_1450 = (term_as_mlexpr g head)
in (match (_82_1450) with
| (head, f, t) -> begin
(extract_app_maybe_projector None head ((f), (t)) args)
end))
end))
end))
end))
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
(failwith "Ascription node with an empty effect label")
end
| Some (l) -> begin
(effect_as_etag g l)
end)
in (

let _82_1467 = (check_term_as_mlexpr g e0 f t)
in (match (_82_1467) with
| (e, t) -> begin
((e), (f), (t))
end))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') -> begin
(

let top_level = (FStar_Syntax_Syntax.is_top_level lbs)
in (

let _82_1483 = if is_rec then begin
(FStar_Syntax_Subst.open_let_rec lbs e')
end else begin
if (FStar_Syntax_Syntax.is_top_level lbs) then begin
((lbs), (e'))
end else begin
(

let lb = (FStar_List.hd lbs)
in (

let x = (let _181_416 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv _181_416))
in (

let lb = (

let _82_1477 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _82_1477.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _82_1477.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _82_1477.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _82_1477.FStar_Syntax_Syntax.lbdef})
in (

let e' = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x))))::[]) e')
in (((lb)::[]), (e'))))))
end
end
in (match (_82_1483) with
| (lbs, e') -> begin
(

let lbs = if top_level then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let tcenv = (let _181_418 = (FStar_Ident.lid_of_path (FStar_List.append (Prims.fst g.FStar_Extraction_ML_UEnv.currentModule) (((Prims.snd g.FStar_Extraction_ML_UEnv.currentModule))::[])) FStar_Range.dummyRange)
in (FStar_TypeChecker_Env.set_current_module g.FStar_Extraction_ML_UEnv.tcenv _181_418))
in (

let lbdef = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.PureSubtermsWithinComputations)::(FStar_TypeChecker_Normalize.Primops)::[]) tcenv lb.FStar_Syntax_Syntax.lbdef)
in (

let _82_1487 = lb
in {FStar_Syntax_Syntax.lbname = _82_1487.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _82_1487.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _82_1487.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _82_1487.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef}))))))
end else begin
lbs
end
in (

let maybe_generalize = (fun _82_1497 -> (match (_82_1497) with
| {FStar_Syntax_Syntax.lbname = lbname_; FStar_Syntax_Syntax.lbunivs = _82_1495; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = lbeff; FStar_Syntax_Syntax.lbdef = e} -> begin
(

let f_e = (effect_as_etag g lbeff)
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when (let _181_421 = (FStar_List.hd bs)
in (FStar_All.pipe_right _181_421 (is_type_binder g))) -> begin
(

let _82_1506 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_82_1506) with
| (bs, c) -> begin
(

let _82_1516 = (match ((FStar_Util.prefix_until (fun x -> (not ((is_type_binder g x)))) bs)) with
| None -> begin
((bs), ((FStar_Syntax_Util.comp_result c)))
end
| Some (bs, b, rest) -> begin
(let _181_423 = (FStar_Syntax_Util.arrow ((b)::rest) c)
in ((bs), (_181_423)))
end)
in (match (_82_1516) with
| (tbinders, tbody) -> begin
(

let n_tbinders = (FStar_List.length tbinders)
in (

let e = (normalize_abs e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _82_1522) -> begin
(

let _82_1527 = (FStar_Syntax_Subst.open_term bs body)
in (match (_82_1527) with
| (bs, body) -> begin
if (n_tbinders <= (FStar_List.length bs)) then begin
(

let _82_1530 = (FStar_Util.first_N n_tbinders bs)
in (match (_82_1530) with
| (targs, rest_args) -> begin
(

let expected_source_ty = (

let s = (FStar_List.map2 (fun _82_1534 _82_1538 -> (match (((_82_1534), (_82_1538))) with
| ((x, _82_1533), (y, _82_1537)) -> begin
(let _181_427 = (let _181_426 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (_181_426)))
in FStar_Syntax_Syntax.NT (_181_427))
end)) tbinders targs)
in (FStar_Syntax_Subst.subst s tbody))
in (

let env = (FStar_List.fold_left (fun env _82_1545 -> (match (_82_1545) with
| (a, _82_1544) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) g targs)
in (

let expected_t = (term_as_mlty env expected_source_ty)
in (

let polytype = (let _181_431 = (FStar_All.pipe_right targs (FStar_List.map (fun _82_1551 -> (match (_82_1551) with
| (x, _82_1550) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((_181_431), (expected_t)))
in (

let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_fstar_value body)))
end
| _82_1555 -> begin
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
| _82_1560 -> begin
(FStar_Syntax_Util.abs rest_args body None)
end)
in ((lbname_), (f_e), (((t), (((targs), (polytype))))), (add_unit), (body)))))))))
end))
end else begin
(failwith "Not enough type binders")
end
end))
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) -> begin
(

let env = (FStar_List.fold_left (fun env _82_1575 -> (match (_82_1575) with
| (a, _82_1574) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (let _181_435 = (FStar_All.pipe_right tbinders (FStar_List.map (fun _82_1581 -> (match (_82_1581) with
| (x, _82_1580) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((_181_435), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun _82_1586 -> (match (_82_1586) with
| (bv, _82_1585) -> begin
(let _181_437 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right _181_437 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e), (args)))) None e.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t), (((tbinders), (polytype))))), (false), (e)))))))
end
| _82_1590 -> begin
(err_value_restriction e)
end)))
end))
end))
end
| _82_1592 -> begin
(

let expected_t = (term_as_mlty g t)
in ((lbname_), (f_e), (((t), ((([]), ((([]), (expected_t))))))), (false), (e)))
end)))
end))
in (

let check_lb = (fun env _82_1607 -> (match (_82_1607) with
| (nm, (lbname, f, (t, (targs, polytype)), add_unit, e)) -> begin
(

let env = (FStar_List.fold_left (fun env _82_1612 -> (match (_82_1612) with
| (a, _82_1611) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) env targs)
in (

let expected_t = if add_unit then begin
FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), ((Prims.snd polytype))))
end else begin
(Prims.snd polytype)
end
in (

let _82_1618 = (check_term_as_mlexpr env e f expected_t)
in (match (_82_1618) with
| (e, _82_1617) -> begin
(

let f = (maybe_downgrade_eff env f expected_t)
in ((f), ({FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = true})))
end))))
end))
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map maybe_generalize))
in (

let _82_1643 = (FStar_List.fold_right (fun lb _82_1624 -> (match (_82_1624) with
| (env, lbs) -> begin
(

let _82_1637 = lb
in (match (_82_1637) with
| (lbname, _82_1627, (t, (_82_1630, polytype)), add_unit, _82_1636) -> begin
(

let _82_1640 = (FStar_Extraction_ML_UEnv.extend_lb env lbname t polytype add_unit true)
in (match (_82_1640) with
| (env, nm) -> begin
((env), ((((nm), (lb)))::lbs))
end))
end))
end)) lbs ((g), ([])))
in (match (_82_1643) with
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

let _82_1650 = (term_as_mlexpr env_body e')
in (match (_82_1650) with
| (e', f', t') -> begin
(

let f = (let _181_447 = (let _181_446 = (FStar_List.map Prims.fst lbs)
in (f')::_181_446)
in (FStar_Extraction_ML_Util.join_l e'_rng _181_447))
in (

let is_rec = if (is_rec = true) then begin
FStar_Extraction_ML_Syntax.Rec
end else begin
FStar_Extraction_ML_Syntax.NonRec
end
in (let _181_452 = (let _181_451 = (let _181_449 = (let _181_448 = (FStar_List.map Prims.snd lbs)
in ((is_rec), ([]), (_181_448)))
in (mk_MLE_Let top_level _181_449 e'))
in (let _181_450 = (FStar_Extraction_ML_Util.mlloc_of_range t.FStar_Syntax_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' _181_451 _181_450)))
in ((_181_452), (f), (t')))))
end)))))
end))))))
end)))
end
| FStar_Syntax_Syntax.Tm_match (scrutinee, pats) -> begin
(

let _82_1660 = (term_as_mlexpr g scrutinee)
in (match (_82_1660) with
| (e, f_e, t_e) -> begin
(

let _82_1664 = (check_pats_for_ite pats)
in (match (_82_1664) with
| (b, then_e, else_e) -> begin
(

let no_lift = (fun x t -> x)
in if b then begin
(match (((then_e), (else_e))) with
| (Some (then_e), Some (else_e)) -> begin
(

let _82_1676 = (term_as_mlexpr g then_e)
in (match (_82_1676) with
| (then_mle, f_then, t_then) -> begin
(

let _82_1680 = (term_as_mlexpr g else_e)
in (match (_82_1680) with
| (else_mle, f_else, t_else) -> begin
(

let _82_1683 = if (type_leq g t_then t_else) then begin
((t_else), (no_lift))
end else begin
if (type_leq g t_else t_then) then begin
((t_then), (no_lift))
end else begin
((FStar_Extraction_ML_Syntax.MLTY_Top), (FStar_Extraction_ML_Syntax.apply_obj_repr))
end
end
in (match (_82_1683) with
| (t_branch, maybe_lift) -> begin
(let _181_483 = (let _181_481 = (let _181_480 = (let _181_479 = (maybe_lift then_mle t_then)
in (let _181_478 = (let _181_477 = (maybe_lift else_mle t_else)
in Some (_181_477))
in ((e), (_181_479), (_181_478))))
in FStar_Extraction_ML_Syntax.MLE_If (_181_480))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) _181_481))
in (let _181_482 = (FStar_Extraction_ML_Util.join then_e.FStar_Syntax_Syntax.pos f_then f_else)
in ((_181_483), (_181_482), (t_branch))))
end))
end))
end))
end
| _82_1685 -> begin
(failwith "ITE pats matched but then and else expressions not found?")
end)
end else begin
(

let _82_1717 = (FStar_All.pipe_right pats (FStar_Util.fold_map (fun compat br -> (

let _82_1691 = (FStar_Syntax_Subst.open_branch br)
in (match (_82_1691) with
| (pat, when_opt, branch) -> begin
(

let _82_1695 = (extract_pat g pat t_e)
in (match (_82_1695) with
| (env, p, pat_t_compat) -> begin
(

let _82_1706 = (match (when_opt) with
| None -> begin
((None), (FStar_Extraction_ML_Syntax.E_PURE))
end
| Some (w) -> begin
(

let _82_1702 = (term_as_mlexpr env w)
in (match (_82_1702) with
| (w, f_w, t_w) -> begin
(

let w = (maybe_coerce env w t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in ((Some (w)), (f_w)))
end))
end)
in (match (_82_1706) with
| (when_opt, f_when) -> begin
(

let _82_1710 = (term_as_mlexpr env branch)
in (match (_82_1710) with
| (mlbranch, f_branch, t_branch) -> begin
(let _181_487 = (FStar_All.pipe_right p (FStar_List.map (fun _82_1713 -> (match (_82_1713) with
| (p, wopt) -> begin
(

let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt)
in ((p), (((when_clause), (f_when))), (((mlbranch), (f_branch), (t_branch)))))
end))))
in (((compat && pat_t_compat)), (_181_487)))
end))
end))
end))
end))) true))
in (match (_82_1717) with
| (pat_t_compat, mlbranches) -> begin
(

let mlbranches = (FStar_List.flatten mlbranches)
in (

let e = if pat_t_compat then begin
e
end else begin
(

let _82_1721 = (FStar_Extraction_ML_UEnv.debug g (fun _82_1719 -> (let _181_490 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (let _181_489 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t_e)
in (FStar_Util.print2 "Coercing scrutinee %s from type %s because pattern type is incompatible\n" _181_490 _181_489)))))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_e) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (t_e), (FStar_Extraction_ML_Syntax.MLTY_Top))))))
end
in (match (mlbranches) with
| [] -> begin
(

let _82_1730 = (let _181_492 = (let _181_491 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Extraction_ML_UEnv.lookup_fv g _181_491))
in (FStar_All.pipe_left FStar_Util.right _181_492))
in (match (_82_1730) with
| (fw, _82_1727, _82_1729) -> begin
(let _181_497 = (let _181_496 = (let _181_495 = (let _181_494 = (let _181_493 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (_181_493)::[])
in ((fw), (_181_494)))
in FStar_Extraction_ML_Syntax.MLE_App (_181_495))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) _181_496))
in ((_181_497), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
end))
end
| ((_82_1733, _82_1735, (_82_1737, f_first, t_first)))::rest -> begin
(

let _82_1763 = (FStar_List.fold_left (fun _82_1745 _82_1755 -> (match (((_82_1745), (_82_1755))) with
| ((topt, f), (_82_1747, _82_1749, (_82_1751, f_branch, t_branch))) -> begin
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
in (match (_82_1763) with
| (topt, f_match) -> begin
(

let mlbranches = (FStar_All.pipe_right mlbranches (FStar_List.map (fun _82_1774 -> (match (_82_1774) with
| (p, (wopt, _82_1767), (b, _82_1771, t)) -> begin
(

let b = (match (topt) with
| None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b t)
end
| Some (_82_1777) -> begin
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
in (let _181_501 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match (((e), (mlbranches)))))
in ((_181_501), (f_match), (t_match)))))
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

let _82_1787 = (FStar_Util.incr c)
in (let _181_504 = (FStar_ST.read c)
in ((x), (_181_504))))))


let ind_discriminator_body : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (

let _82_1795 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv discName)
in (match (_82_1795) with
| (_82_1793, fstar_disc_type) -> begin
(

let wildcards = (match ((let _181_511 = (FStar_Syntax_Subst.compress fstar_disc_type)
in _181_511.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _82_1798) -> begin
(let _181_515 = (FStar_All.pipe_right binders (FStar_List.filter (fun _82_5 -> (match (_82_5) with
| (_82_1803, Some (FStar_Syntax_Syntax.Implicit (_82_1805))) -> begin
true
end
| _82_1810 -> begin
false
end))))
in (FStar_All.pipe_right _181_515 (FStar_List.map (fun _82_1811 -> (let _181_514 = (fresh "_")
in ((_181_514), (FStar_Extraction_ML_Syntax.MLTY_Top)))))))
end
| _82_1814 -> begin
(failwith "Discriminator must be a function")
end)
in (

let mlid = (fresh "_discr_")
in (

let targ = FStar_Extraction_ML_Syntax.MLTY_Top
in (

let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top
in (

let discrBody = (let _181_530 = (let _181_529 = (let _181_528 = (let _181_527 = (let _181_526 = (let _181_525 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name ((([]), ((FStar_Extraction_ML_Syntax.idsym mlid))))))
in (let _181_524 = (let _181_523 = (let _181_519 = (let _181_517 = (let _181_516 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in ((_181_516), ((FStar_Extraction_ML_Syntax.MLP_Wild)::[])))
in FStar_Extraction_ML_Syntax.MLP_CTor (_181_517))
in (let _181_518 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in ((_181_519), (None), (_181_518))))
in (let _181_522 = (let _181_521 = (let _181_520 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in ((FStar_Extraction_ML_Syntax.MLP_Wild), (None), (_181_520)))
in (_181_521)::[])
in (_181_523)::_181_522))
in ((_181_525), (_181_524))))
in FStar_Extraction_ML_Syntax.MLE_Match (_181_526))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _181_527))
in (((FStar_List.append wildcards ((((mlid), (targ)))::[]))), (_181_528)))
in FStar_Extraction_ML_Syntax.MLE_Fun (_181_529))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) _181_530))
in FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NonRec), ([]), (({FStar_Extraction_ML_Syntax.mllb_name = (FStar_Extraction_ML_UEnv.convIdent discName.FStar_Ident.ident); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.print_typ = false})::[]))))))))
end)))




