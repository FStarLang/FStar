
open Prims
exception Un_extractable


let uu___is_Un_extractable : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Un_extractable -> begin
true
end
| uu____4 -> begin
false
end))


let type_leq : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))


let type_leq_c : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr Prims.option) = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq_c (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))


let erasableType : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t -> (FStar_Extraction_ML_Util.erasableType (FStar_Extraction_ML_Util.udelta_unfold g) t))


let eraseTypeDeep : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold g) t))


let record_fields = (fun fs vs -> (FStar_List.map2 (fun f e -> ((f.FStar_Ident.idText), (e))) fs vs))


let fail = (fun r msg -> ((let _0_322 = (let _0_321 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _0_321 msg))
in (FStar_All.pipe_left FStar_Util.print_string _0_322));
(failwith msg);
))


let err_uninst = (fun env t uu____105 app -> (match (uu____105) with
| (vars, ty) -> begin
(let _0_328 = (let _0_327 = (FStar_Syntax_Print.term_to_string t)
in (let _0_326 = (let _0_323 = (FStar_All.pipe_right vars (FStar_List.map Prims.fst))
in (FStar_All.pipe_right _0_323 (FStar_String.concat ", ")))
in (let _0_325 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (let _0_324 = (FStar_Syntax_Print.term_to_string app)
in (FStar_Util.format4 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s" _0_327 _0_326 _0_325 _0_324)))))
in (fail t.FStar_Syntax_Syntax.pos _0_328))
end))


let err_ill_typed_application = (fun env t args ty -> (let _0_333 = (let _0_332 = (FStar_Syntax_Print.term_to_string t)
in (let _0_331 = (let _0_329 = (FStar_All.pipe_right args (FStar_List.map (fun uu____164 -> (match (uu____164) with
| (x, uu____168) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _0_329 (FStar_String.concat " ")))
in (let _0_330 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n" _0_332 _0_331 _0_330))))
in (fail t.FStar_Syntax_Syntax.pos _0_333)))


let err_value_restriction = (fun t -> (let _0_336 = (let _0_335 = (FStar_Syntax_Print.tag_of_term t)
in (let _0_334 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Refusing to generalize because of the value restriction: (%s) %s" _0_335 _0_334)))
in (fail t.FStar_Syntax_Syntax.pos _0_336)))


let err_unexpected_eff = (fun t f0 f1 -> (let _0_338 = (let _0_337 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" _0_337 (FStar_Extraction_ML_Util.eff_to_string f0) (FStar_Extraction_ML_Util.eff_to_string f1)))
in (fail t.FStar_Syntax_Syntax.pos _0_338)))


let effect_as_etag : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.e_tag = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (

let rec delta_norm_eff = (fun g l -> (

let uu____214 = (FStar_Util.smap_try_find cache l.FStar_Ident.str)
in (match (uu____214) with
| Some (l) -> begin
l
end
| None -> begin
(

let res = (

let uu____218 = (FStar_TypeChecker_Env.lookup_effect_abbrev g.FStar_Extraction_ML_UEnv.tcenv ((FStar_Syntax_Syntax.U_zero)::[]) l)
in (match (uu____218) with
| None -> begin
l
end
| Some (uu____224, c) -> begin
(delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c))
end))
in ((FStar_Util.smap_add cache l.FStar_Ident.str res);
res;
))
end)))
in (fun g l -> (

let l = (delta_norm_eff g l)
in (match ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)) with
| true -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| uu____232 -> begin
(match ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid)) with
| true -> begin
FStar_Extraction_ML_Syntax.E_GHOST
end
| uu____233 -> begin
FStar_Extraction_ML_Syntax.E_IMPURE
end)
end)))))


let rec is_arity : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t = (FStar_Syntax_Util.unmeta t)
in (

let uu____241 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____241) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_meta (_)) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) -> begin
false
end
| FStar_Syntax_Syntax.Tm_type (uu____249) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____250, c) -> begin
(is_arity env (FStar_Syntax_Util.comp_result c))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____262) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.FStar_Extraction_ML_UEnv.tcenv t)
in (

let uu____264 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____264) with
| FStar_Syntax_Syntax.Tm_fvar (uu____265) -> begin
false
end
| uu____266 -> begin
(is_arity env t)
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____267) -> begin
(

let uu____277 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____277) with
| (head, uu____288) -> begin
(is_arity env head)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (head, uu____304) -> begin
(is_arity env head)
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____310) -> begin
(is_arity env x.FStar_Syntax_Syntax.sort)
end
| (FStar_Syntax_Syntax.Tm_abs (_, body, _)) | (FStar_Syntax_Syntax.Tm_let (_, body)) -> begin
(is_arity env body)
end
| FStar_Syntax_Syntax.Tm_match (uu____339, branches) -> begin
(match (branches) with
| ((uu____367, uu____368, e))::uu____370 -> begin
(is_arity env e)
end
| uu____406 -> begin
false
end)
end))))


let rec is_type_aux : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(failwith (let _0_339 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: %s" _0_339)))
end
| FStar_Syntax_Syntax.Tm_constant (uu____426) -> begin
false
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.failwith_lid) -> begin
false
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____432 = (FStar_TypeChecker_Env.is_type_constructor env.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____432) with
| true -> begin
true
end
| uu____437 -> begin
(

let uu____438 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____438) with
| (uu____445, t) -> begin
(is_arity env t)
end))
end))
end
| (FStar_Syntax_Syntax.Tm_uvar (_, t)) | (FStar_Syntax_Syntax.Tm_bvar ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})) | (FStar_Syntax_Syntax.Tm_name ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})) -> begin
(is_arity env t)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, uu____466, uu____467) -> begin
(is_type_aux env t)
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____487) -> begin
(is_type_aux env t)
end
| FStar_Syntax_Syntax.Tm_abs (uu____492, body, uu____494) -> begin
(is_type_aux env body)
end
| FStar_Syntax_Syntax.Tm_let (uu____517, body) -> begin
(is_type_aux env body)
end
| FStar_Syntax_Syntax.Tm_match (uu____529, branches) -> begin
(match (branches) with
| ((uu____557, uu____558, e))::uu____560 -> begin
(is_type_aux env e)
end
| uu____596 -> begin
(failwith "Empty branches")
end)
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____609) -> begin
(is_type_aux env t)
end
| FStar_Syntax_Syntax.Tm_app (head, uu____615) -> begin
(is_type_aux env head)
end)))


let is_type : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let b = (is_type_aux env t)
in ((FStar_Extraction_ML_UEnv.debug env (fun uu____638 -> (match (b) with
| true -> begin
(let _0_341 = (FStar_Syntax_Print.term_to_string t)
in (let _0_340 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "is_type %s (%s)\n" _0_341 _0_340)))
end
| uu____639 -> begin
(let _0_343 = (FStar_Syntax_Print.term_to_string t)
in (let _0_342 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "not a type %s (%s)\n" _0_343 _0_342)))
end)));
b;
)))


let is_type_binder = (fun env x -> (is_arity env (Prims.fst x).FStar_Syntax_Syntax.sort))


let is_constructor : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____659 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____659) with
| (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| uu____665 -> begin
false
end)))


let rec is_fstar_value : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____669 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____669) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let uu____690 = (is_constructor head)
in (match (uu____690) with
| true -> begin
(FStar_All.pipe_right args (FStar_List.for_all (fun uu____698 -> (match (uu____698) with
| (te, uu____702) -> begin
(is_fstar_value te)
end))))
end
| uu____703 -> begin
false
end))
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t, _, _)) -> begin
(is_fstar_value t)
end
| uu____723 -> begin
false
end)))


let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Fun (_)) -> begin
true
end
| (FStar_Extraction_ML_Syntax.MLE_CTor (_, exps)) | (FStar_Extraction_ML_Syntax.MLE_Tuple (exps)) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (uu____736, fields) -> begin
(FStar_Util.for_all (fun uu____748 -> (match (uu____748) with
| (uu____751, e) -> begin
(is_ml_value e)
end)) fields)
end
| uu____753 -> begin
false
end))


let normalize_abs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t0 -> (

let rec aux = (fun bs t copt -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs', body, copt) -> begin
(aux (FStar_List.append bs bs') body copt)
end
| uu____813 -> begin
(

let e' = (FStar_Syntax_Util.unascribe t)
in (

let uu____815 = (FStar_Syntax_Util.is_fun e')
in (match (uu____815) with
| true -> begin
(aux bs e' copt)
end
| uu____816 -> begin
(FStar_Syntax_Util.abs bs e' copt)
end)))
end)))
in (aux [] t0 None)))


let unit_binder : FStar_Syntax_Syntax.binder = (let _0_344 = (FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _0_344))


let check_pats_for_ite : (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term Prims.option) = (fun l -> (

let def = ((false), (None), (None))
in (match (((FStar_List.length l) <> (Prims.parse_int "2"))) with
| true -> begin
def
end
| uu____866 -> begin
(

let uu____867 = (FStar_List.hd l)
in (match (uu____867) with
| (p1, w1, e1) -> begin
(

let uu____886 = (FStar_List.hd (FStar_List.tl l))
in (match (uu____886) with
| (p2, w2, e2) -> begin
(match (((w1), (w2), (p1.FStar_Syntax_Syntax.v), (p2.FStar_Syntax_Syntax.v))) with
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
((true), (Some (e1)), (Some (e2)))
end
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
((true), (Some (e2)), (Some (e1)))
end
| uu____924 -> begin
def
end)
end))
end))
end)))


let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))


let erasable : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g f t -> ((f = FStar_Extraction_ML_Syntax.E_GHOST) || ((f = FStar_Extraction_ML_Syntax.E_PURE) && (erasableType g t))))


let erase : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e ty f -> (

let e = (

let uu____967 = (erasable g f ty)
in (match (uu____967) with
| true -> begin
(

let uu____968 = (type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty)
in (match (uu____968) with
| true -> begin
FStar_Extraction_ML_Syntax.ml_unit
end
| uu____969 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) (FStar_Extraction_ML_Syntax.MLE_Coerce (((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.ml_unit_ty), (ty)))))
end))
end
| uu____970 -> begin
e
end))
in ((e), (f), (ty))))


let maybe_coerce : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e ty expect -> (

let ty = (eraseTypeDeep g ty)
in (

let uu____984 = ((type_leq_c g (Some (e)) ty) expect)
in (match (uu____984) with
| (true, Some (e')) -> begin
e'
end
| uu____990 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____995 -> (let _0_347 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (let _0_346 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (let _0_345 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule expect)
in (FStar_Util.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n" _0_347 _0_346 _0_345))))));
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (ty), (expect)))));
)
end))))


let bv_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bv -> (

let uu____1002 = (FStar_Extraction_ML_UEnv.lookup_bv g bv)
in (match (uu____1002) with
| FStar_Util.Inl (uu____1003, t) -> begin
t
end
| uu____1010 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)))


let rec term_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t0)
in (

let mlt = (term_as_mlty' g t)
in (

let uu____1044 = ((fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
true
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____1046) -> begin
(

let uu____1050 = (FStar_Extraction_ML_Util.udelta_unfold g t)
in (match (uu____1050) with
| None -> begin
false
end
| Some (t) -> begin
((

let rec is_top_ty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
true
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____1057) -> begin
(

let uu____1061 = (FStar_Extraction_ML_Util.udelta_unfold g t)
in (match (uu____1061) with
| None -> begin
false
end
| Some (t) -> begin
(is_top_ty t)
end))
end
| uu____1064 -> begin
false
end))
in is_top_ty) t)
end))
end
| uu____1065 -> begin
false
end)) mlt)
in (match (uu____1044) with
| true -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t0)
in (term_as_mlty' g t))
end
| uu____1067 -> begin
mlt
end)))))
and term_as_mlty' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun env t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(failwith (let _0_348 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Impossible: Unexpected term %s" _0_348)))
end
| FStar_Syntax_Syntax.Tm_constant (uu____1073) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1074) -> begin
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

let uu____1132 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____1132) with
| (bs, c) -> begin
(

let uu____1137 = (binders_as_ml_binders env bs)
in (match (uu____1137) with
| (mlbs, env) -> begin
(

let t_ret = (

let eff = (FStar_TypeChecker_Env.norm_eff_name env.FStar_Extraction_ML_UEnv.tcenv (FStar_Syntax_Util.comp_effect_name c))
in (

let ed = (FStar_TypeChecker_Env.get_effect_decl env.FStar_Extraction_ML_UEnv.tcenv eff)
in (

let uu____1154 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____1154) with
| true -> begin
(

let t = (FStar_TypeChecker_Util.reify_comp env.FStar_Extraction_ML_UEnv.tcenv (FStar_Syntax_Util.lcomp_of_comp c) FStar_Syntax_Syntax.U_unknown)
in (

let res = (term_as_mlty' env t)
in res))
end
| uu____1158 -> begin
(term_as_mlty' env (FStar_Syntax_Util.comp_result c))
end))))
in (

let erase = (effect_as_etag env (FStar_Syntax_Util.comp_effect_name c))
in (

let uu____1160 = (FStar_List.fold_right (fun uu____1167 uu____1168 -> (match (((uu____1167), (uu____1168))) with
| ((uu____1179, t), (tag, t')) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((t), (tag), (t')))))
end)) mlbs ((erase), (t_ret)))
in (match (uu____1160) with
| (uu____1187, t) -> begin
t
end))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let res = (

let uu____1206 = (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n
in (match (uu____1206) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv args)
end
| FStar_Syntax_Syntax.Tm_app (head, args') -> begin
(let _0_349 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head), ((FStar_List.append args' args))))) None t.FStar_Syntax_Syntax.pos)
in (term_as_mlty' env _0_349))
end
| uu____1244 -> begin
FStar_Extraction_ML_UEnv.unknownType
end))
in res)
end
| FStar_Syntax_Syntax.Tm_abs (bs, ty, uu____1247) -> begin
(

let uu____1270 = (FStar_Syntax_Subst.open_term bs ty)
in (match (uu____1270) with
| (bs, ty) -> begin
(

let uu____1275 = (binders_as_ml_binders env bs)
in (match (uu____1275) with
| (bts, env) -> begin
(term_as_mlty' env ty)
end))
end))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
FStar_Extraction_ML_UEnv.unknownType
end)))
and arg_as_mlty : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual)  ->  FStar_Extraction_ML_Syntax.mlty = (fun g uu____1293 -> (match (uu____1293) with
| (a, uu____1297) -> begin
(

let uu____1298 = (is_type g a)
in (match (uu____1298) with
| true -> begin
(term_as_mlty' g a)
end
| uu____1299 -> begin
FStar_Extraction_ML_UEnv.erasedContent
end))
end))
and fv_app_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.args  ->  FStar_Extraction_ML_Syntax.mlty = (fun g fv args -> (

let uu____1303 = (FStar_Syntax_Util.arrow_formals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (match (uu____1303) with
| (formals, t) -> begin
(

let mlargs = (FStar_List.map (arg_as_mlty g) args)
in (

let mlargs = (

let n_args = (FStar_List.length args)
in (match (((FStar_List.length formals) > n_args)) with
| true -> begin
(

let uu____1347 = (FStar_Util.first_N n_args formals)
in (match (uu____1347) with
| (uu____1361, rest) -> begin
(let _0_350 = (FStar_List.map (fun uu____1377 -> FStar_Extraction_ML_UEnv.erasedContent) rest)
in (FStar_List.append mlargs _0_350))
end))
end
| uu____1380 -> begin
mlargs
end))
in (

let nm = (

let uu____1382 = (FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv)
in (match (uu____1382) with
| Some (p) -> begin
p
end
| None -> begin
(FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))
in FStar_Extraction_ML_Syntax.MLTY_Named (((mlargs), (nm))))))
end)))
and binders_as_ml_binders : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list * FStar_Extraction_ML_UEnv.env) = (fun g bs -> (

let uu____1397 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____1421 b -> (match (uu____1421) with
| (ml_bs, env) -> begin
(

let uu____1451 = (is_type_binder g b)
in (match (uu____1451) with
| true -> begin
(

let b = (Prims.fst b)
in (

let env = (FStar_Extraction_ML_UEnv.extend_ty env b (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (

let ml_b = (let _0_351 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b)
in ((_0_351), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
in (((ml_b)::ml_bs), (env)))))
end
| uu____1477 -> begin
(

let b = (Prims.fst b)
in (

let t = (term_as_mlty env b.FStar_Syntax_Syntax.sort)
in (

let env = (FStar_Extraction_ML_UEnv.extend_bv env b (([]), (t)) false false false)
in (

let ml_b = (let _0_352 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b)
in ((_0_352), (t)))
in (((ml_b)::ml_bs), (env))))))
end))
end)) (([]), (g))))
in (match (uu____1397) with
| (ml_bs, env) -> begin
(((FStar_List.rev ml_bs)), (env))
end)))


let mk_MLE_Seq : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun e1 e2 -> (match (((e1.FStar_Extraction_ML_Syntax.expr), (e2.FStar_Extraction_ML_Syntax.expr))) with
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 es2))
end
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), uu____1544) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 ((e2)::[])))
end
| (uu____1546, FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::es2)
end
| uu____1549 -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::(e2)::[])
end))


let mk_MLE_Let : Prims.bool  ->  FStar_Extraction_ML_Syntax.mlletbinding  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun top_level lbs body -> (match (lbs) with
| (FStar_Extraction_ML_Syntax.NonRec, quals, (lb)::[]) when (not (top_level)) -> begin
(match (lb.FStar_Extraction_ML_Syntax.mllb_tysc) with
| Some ([], t) when (t = FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
(match ((body.FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr)) with
| true -> begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end
| uu____1569 -> begin
(match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Var (x) when (x = lb.FStar_Extraction_ML_Syntax.mllb_name) -> begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end
| uu____1571 when (lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr) -> begin
body.FStar_Extraction_ML_Syntax.expr
end
| uu____1572 -> begin
(mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def body)
end)
end)
end
| uu____1573 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end)
end
| uu____1575 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end))


let resugar_pat : FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_ML_Syntax.mlpattern = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(match ((FStar_Extraction_ML_Util.is_xtuple d)) with
| Some (n) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| uu____1589 -> begin
(match (q) with
| Some (FStar_Syntax_Syntax.Record_ctor (ty, fns)) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns)
in (

let fs = (record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record (((path), (fs)))))
end
| uu____1605 -> begin
p
end)
end)
end
| uu____1607 -> begin
p
end))


let rec extract_one_pat : Prims.bool  ->  Prims.bool  ->  FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Extraction_ML_Syntax.mlty Prims.option  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.list) Prims.option * Prims.bool) = (fun disjunctive_pat imp g p expected_topt -> (

let ok = (fun t -> (match (expected_topt) with
| None -> begin
true
end
| Some (t') -> begin
(

let ok = (type_leq g t t')
in ((match ((not (ok))) with
| true -> begin
(FStar_Extraction_ML_UEnv.debug g (fun uu____1646 -> (let _0_354 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t')
in (let _0_353 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t)
in (FStar_Util.print2 "Expected pattern type %s; got pattern type %s\n" _0_354 _0_353)))))
end
| uu____1647 -> begin
()
end);
ok;
))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____1655) -> begin
(failwith "Impossible: Nested disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int (c, None)) -> begin
(

let i = FStar_Const.Const_int (((c), (None)))
in (

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let when_clause = (let _0_362 = FStar_Extraction_ML_Syntax.MLE_App ((let _0_361 = (let _0_360 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (let _0_359 = (let _0_358 = (let _0_357 = (let _0_356 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p i)
in (FStar_All.pipe_left (fun _0_355 -> FStar_Extraction_ML_Syntax.MLE_Const (_0_355)) _0_356))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) _0_357))
in (_0_358)::[])
in (_0_360)::_0_359))
in ((FStar_Extraction_ML_Util.prims_op_equality), (_0_361))))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _0_362))
in (let _0_363 = (ok FStar_Extraction_ML_Syntax.ml_int_ty)
in ((g), (Some (((FStar_Extraction_ML_Syntax.MLP_Var (x)), ((when_clause)::[])))), (_0_363))))))
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(

let t = (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange s)
in (

let mlty = (term_as_mlty g t)
in (let _0_366 = Some ((let _0_364 = FStar_Extraction_ML_Syntax.MLP_Const ((FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p s))
in ((_0_364), ([]))))
in (let _0_365 = (ok mlty)
in ((g), (_0_366), (_0_365))))))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let g = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (let _0_369 = (match (imp) with
| true -> begin
None
end
| uu____1715 -> begin
Some ((let _0_367 = FStar_Extraction_ML_Syntax.MLP_Var ((FStar_Extraction_ML_Syntax.bv_as_mlident x))
in ((_0_367), ([]))))
end)
in (let _0_368 = (ok mlty)
in ((g), (_0_369), (_0_368))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) when disjunctive_pat -> begin
((g), (Some (((FStar_Extraction_ML_Syntax.MLP_Wild), ([])))), (true))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let g = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (let _0_372 = (match (imp) with
| true -> begin
None
end
| uu____1744 -> begin
Some ((let _0_370 = FStar_Extraction_ML_Syntax.MLP_Var ((FStar_Extraction_ML_Syntax.bv_as_mlident x))
in ((_0_370), ([]))))
end)
in (let _0_371 = (ok mlty)
in ((g), (_0_372), (_0_371))))))
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____1749) -> begin
((g), (None), (true))
end
| FStar_Syntax_Syntax.Pat_cons (f, pats) -> begin
(

let uu____1773 = (

let uu____1776 = (FStar_Extraction_ML_UEnv.lookup_fv g f)
in (match (uu____1776) with
| FStar_Util.Inr ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n); FStar_Extraction_ML_Syntax.mlty = uu____1780; FStar_Extraction_ML_Syntax.loc = uu____1781}, ttys, uu____1783) -> begin
((n), (ttys))
end
| uu____1789 -> begin
(failwith "Expected a constructor")
end))
in (match (uu____1773) with
| (d, tys) -> begin
(

let nTyVars = (FStar_List.length (Prims.fst tys))
in (

let uu____1803 = (FStar_Util.first_N nTyVars pats)
in (match (uu____1803) with
| (tysVarPats, restPats) -> begin
(

let f_ty_opt = try
(match (()) with
| () -> begin
(

let mlty_args = (FStar_All.pipe_right tysVarPats (FStar_List.map (fun uu____1877 -> (match (uu____1877) with
| (p, uu____1883) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (uu____1888, t) -> begin
(term_as_mlty g t)
end
| uu____1894 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____1896 -> (let _0_373 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print1 "Pattern %s is not extractable" _0_373))));
(Prims.raise Un_extractable);
)
end)
end))))
in (

let f_ty = (FStar_Extraction_ML_Util.subst tys mlty_args)
in Some ((FStar_Extraction_ML_Util.uncurry_mlty_fun f_ty))))
end)
with
| Un_extractable -> begin
None
end
in (

let uu____1909 = (FStar_Util.fold_map (fun g uu____1924 -> (match (uu____1924) with
| (p, imp) -> begin
(

let uu____1935 = (extract_one_pat disjunctive_pat true g p None)
in (match (uu____1935) with
| (g, p, uu____1951) -> begin
((g), (p))
end))
end)) g tysVarPats)
in (match (uu____1909) with
| (g, tyMLPats) -> begin
(

let uu____1983 = (FStar_Util.fold_map (fun uu____2009 uu____2010 -> (match (((uu____2009), (uu____2010))) with
| ((g, f_ty_opt), (p, imp)) -> begin
(

let uu____2059 = (match (f_ty_opt) with
| Some ((hd)::rest, res) -> begin
((Some (((rest), (res)))), (Some (hd)))
end
| uu____2091 -> begin
((None), (None))
end)
in (match (uu____2059) with
| (f_ty_opt, expected_ty) -> begin
(

let uu____2128 = (extract_one_pat disjunctive_pat false g p expected_ty)
in (match (uu____2128) with
| (g, p, uu____2150) -> begin
((((g), (f_ty_opt))), (p))
end))
end))
end)) ((g), (f_ty_opt)) restPats)
in (match (uu____1983) with
| ((g, f_ty_opt), restMLPats) -> begin
(

let uu____2211 = (let _0_374 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun uu___113_2246 -> (match (uu___113_2246) with
| Some (x) -> begin
(x)::[]
end
| uu____2268 -> begin
[]
end))))
in (FStar_All.pipe_right _0_374 FStar_List.split))
in (match (uu____2211) with
| (mlPats, when_clauses) -> begin
(

let pat_ty_compat = (match (f_ty_opt) with
| Some ([], t) -> begin
(ok t)
end
| uu____2298 -> begin
false
end)
in (let _0_377 = Some ((let _0_376 = (resugar_pat f.FStar_Syntax_Syntax.fv_qual (FStar_Extraction_ML_Syntax.MLP_CTor (((d), (mlPats)))))
in (let _0_375 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in ((_0_376), (_0_375)))))
in ((g), (_0_377), (pat_ty_compat))))
end))
end))
end)))
end)))
end))
end)))


let extract_pat : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option) Prims.list * Prims.bool) = (fun g p expected_t -> (

let extract_one_pat = (fun disj g p expected_t -> (

let uu____2363 = (extract_one_pat disj false g p expected_t)
in (match (uu____2363) with
| (g, Some (x, v), b) -> begin
((g), (((x), (v))), (b))
end
| uu____2394 -> begin
(failwith "Impossible: Unable to translate pattern")
end)))
in (

let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| (hd)::tl -> begin
Some ((FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible: Empty disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_disj ((p)::pats) -> begin
(

let uu____2444 = (extract_one_pat true g p (Some (expected_t)))
in (match (uu____2444) with
| (g, p, b) -> begin
(

let uu____2467 = (FStar_Util.fold_map (fun b p -> (

let uu____2479 = (extract_one_pat true g p (Some (expected_t)))
in (match (uu____2479) with
| (uu____2491, p, b') -> begin
(((b && b')), (p))
end))) b pats)
in (match (uu____2467) with
| (b, ps) -> begin
(

let ps = (p)::ps
in (

let uu____2528 = (FStar_All.pipe_right ps (FStar_List.partition (fun uu___114_2556 -> (match (uu___114_2556) with
| (uu____2560, (uu____2561)::uu____2562) -> begin
true
end
| uu____2565 -> begin
false
end))))
in (match (uu____2528) with
| (ps_when, rest) -> begin
(

let ps = (FStar_All.pipe_right ps_when (FStar_List.map (fun uu____2613 -> (match (uu____2613) with
| (x, whens) -> begin
(let _0_378 = (mk_when_clause whens)
in ((x), (_0_378)))
end))))
in (

let res = (match (rest) with
| [] -> begin
((g), (ps), (b))
end
| rest -> begin
(let _0_381 = (let _0_380 = (let _0_379 = FStar_Extraction_ML_Syntax.MLP_Branch ((FStar_List.map Prims.fst rest))
in ((_0_379), (None)))
in (_0_380)::ps)
in ((g), (_0_381), (b)))
end)
in res))
end)))
end))
end))
end
| uu____2664 -> begin
(

let uu____2665 = (extract_one_pat false g p (Some (expected_t)))
in (match (uu____2665) with
| (g, (p, whens), b) -> begin
(

let when_clause = (mk_when_clause whens)
in ((g), ((((p), (when_clause)))::[]), (b)))
end))
end))))


let maybe_eta_data_and_project_record : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (

let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, uu____2747, t1) -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _0_384 = (let _0_383 = (let _0_382 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((((x), (t0))), (_0_382)))
in (_0_383)::more_args)
in (eta_args _0_384 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____2756, uu____2757) -> begin
(((FStar_List.rev more_args)), (t))
end
| uu____2769 -> begin
(failwith "Impossible: Head type is not an arrow")
end))
in (

let as_record = (fun qual e -> (match (((e.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (uu____2787, args), Some (FStar_Syntax_Syntax.Record_ctor (tyname, fields))) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns)
in (

let fields = (record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record (((path), (fields)))))))
end
| uu____2806 -> begin
e
end))
in (

let resugar_and_maybe_eta = (fun qual e -> (

let uu____2819 = (eta_args [] residualType)
in (match (uu____2819) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(FStar_Extraction_ML_Util.resugar_exp (as_record qual e))
end
| uu____2847 -> begin
(

let uu____2853 = (FStar_List.unzip eargs)
in (match (uu____2853) with
| (binders, eargs) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head, args) -> begin
(

let body = (let _0_386 = (let _0_385 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor (((head), ((FStar_List.append args eargs))))))
in (FStar_All.pipe_left (as_record qual) _0_385))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp _0_386))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun (((binders), (body))))))
end
| uu____2881 -> begin
(failwith "Impossible: Not a constructor")
end)
end))
end)
end)))
in (match (((mlAppExpr.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (uu____2883, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____2886; FStar_Extraction_ML_Syntax.loc = uu____2887}, (mle)::args), Some (FStar_Syntax_Syntax.Record_projector (constrname, f))) -> begin
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
| uu____2905 -> begin
FStar_Extraction_ML_Syntax.MLE_App ((let _0_387 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in ((_0_387), (args))))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e)))))
end
| ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _0_388 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _0_388))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _0_389 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _0_389))
end
| uu____2927 -> begin
mlAppExpr
end)))))


let maybe_downgrade_eff : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag = (fun g f t -> (

let uu____2940 = ((f = FStar_Extraction_ML_Syntax.E_GHOST) && (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty))
in (match (uu____2940) with
| true -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| uu____2941 -> begin
f
end)))


let rec term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g t -> (

let uu____2981 = (term_as_mlexpr' g t)
in (match (uu____2981) with
| (e, tag, ty) -> begin
(

let tag = (maybe_downgrade_eff g tag ty)
in ((FStar_Extraction_ML_UEnv.debug g (fun u -> (FStar_Util.print_string (let _0_392 = (FStar_Syntax_Print.tag_of_term t)
in (let _0_391 = (FStar_Syntax_Print.term_to_string t)
in (let _0_390 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format4 "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n" _0_392 _0_391 _0_390 (FStar_Extraction_ML_Util.eff_to_string tag))))))));
(erase g e ty tag);
))
end)))
and check_term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g t f ty -> (

let uu____3000 = (check_term_as_mlexpr' g t f ty)
in (match (uu____3000) with
| (e, t) -> begin
(

let uu____3007 = (erase g e t f)
in (match (uu____3007) with
| (r, uu____3014, t) -> begin
((r), (t))
end))
end)))
and check_term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g e0 f ty -> (

let uu____3022 = (term_as_mlexpr g e0)
in (match (uu____3022) with
| (e, tag, t) -> begin
(

let tag = (maybe_downgrade_eff g tag t)
in (match ((FStar_Extraction_ML_Util.eff_leq tag f)) with
| true -> begin
(let _0_393 = (maybe_coerce g e t ty)
in ((_0_393), (ty)))
end
| uu____3034 -> begin
(err_unexpected_eff e0 f tag)
end))
end)))
and term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g top -> ((FStar_Extraction_ML_UEnv.debug g (fun u -> (FStar_Util.print_string (let _0_396 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _0_395 = (FStar_Syntax_Print.tag_of_term top)
in (let _0_394 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format3 "%s: term_as_mlexpr\' (%s) :  %s \n" _0_396 _0_395 _0_394)))))));
(

let t = (FStar_Syntax_Subst.compress top)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) -> begin
(failwith (let _0_397 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" _0_397)))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc)) -> begin
(

let uu____3062 = (term_as_mlexpr' g t)
in (match (uu____3062) with
| ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let ((FStar_Extraction_ML_Syntax.NonRec, flags, bodies), continuation); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}, tag, typ) -> begin
(({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let (((((FStar_Extraction_ML_Syntax.NonRec), ((FStar_Extraction_ML_Syntax.Mutable)::flags), (bodies))), (continuation))); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}), (tag), (typ))
end
| uu____3089 -> begin
(failwith "impossible")
end))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, uu____3098)) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) when (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl g.FStar_Extraction_ML_UEnv.tcenv m)
in (

let uu____3122 = (let _0_398 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right _0_398 Prims.op_Negation))
in (match (uu____3122) with
| true -> begin
(term_as_mlexpr' g t)
end
| uu____3127 -> begin
(

let ml_result_ty_1 = (term_as_mlty g lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____3129 = (term_as_mlexpr g lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____3129) with
| (comp_1, uu____3137, uu____3138) -> begin
(

let uu____3139 = (

let k = (let _0_401 = (let _0_400 = (let _0_399 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_All.pipe_right _0_399 FStar_Syntax_Syntax.mk_binder))
in (_0_400)::[])
in (FStar_Syntax_Util.abs _0_401 body None))
in (

let uu____3148 = (term_as_mlexpr g k)
in (match (uu____3148) with
| (ml_k, uu____3155, t_k) -> begin
(

let m_2 = (match (t_k) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3158, uu____3159, m_2) -> begin
m_2
end
| uu____3161 -> begin
(failwith "Impossible")
end)
in ((ml_k), (m_2)))
end)))
in (match (uu____3139) with
| (ml_k, ty) -> begin
(

let bind = (let _0_403 = FStar_Extraction_ML_Syntax.MLE_Name ((let _0_402 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (FStar_All.pipe_right _0_402 Prims.fst)))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _0_403))
in (let _0_404 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) (FStar_Extraction_ML_Syntax.MLE_App (((bind), ((comp_1)::(ml_k)::[])))))
in ((_0_404), (FStar_Extraction_ML_Syntax.E_IMPURE), (ty))))
end))
end)))
end)))
end
| uu____3171 -> begin
(term_as_mlexpr' g t)
end))
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_uinst (t, _)) -> begin
(term_as_mlexpr' g t)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____3184 = (FStar_TypeChecker_TcTerm.type_of_tot_term g.FStar_Extraction_ML_UEnv.tcenv t)
in (match (uu____3184) with
| (uu____3191, ty, uu____3193) -> begin
(

let ml_ty = (term_as_mlty g ty)
in (let _0_408 = (let _0_407 = (let _0_406 = (FStar_Extraction_ML_Util.mlconst_of_const' t.FStar_Syntax_Syntax.pos c)
in (FStar_All.pipe_left (fun _0_405 -> FStar_Extraction_ML_Syntax.MLE_Const (_0_405)) _0_406))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty _0_407))
in ((_0_408), (FStar_Extraction_ML_Syntax.E_PURE), (ml_ty))))
end))
end
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let uu____3197 = (is_type g t)
in (match (uu____3197) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____3201 -> begin
(

let uu____3202 = (FStar_Extraction_ML_UEnv.lookup_term g t)
in (match (uu____3202) with
| (FStar_Util.Inl (uu____3209), uu____3210) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| (FStar_Util.Inr (x, mltys, uu____3229), qual) -> begin
(match (mltys) with
| ([], t) when (t = FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t))
end
| ([], t) -> begin
(let _0_409 = (maybe_eta_data_and_project_record g qual t x)
in ((_0_409), (FStar_Extraction_ML_Syntax.E_PURE), (t)))
end
| uu____3252 -> begin
(err_uninst g t mltys t)
end)
end))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, copt) -> begin
(

let uu____3281 = (FStar_Syntax_Subst.open_term bs body)
in (match (uu____3281) with
| (bs, body) -> begin
(

let uu____3289 = (binders_as_ml_binders g bs)
in (match (uu____3289) with
| (ml_bs, env) -> begin
(

let uu____3306 = (term_as_mlexpr env body)
in (match (uu____3306) with
| (ml_body, f, t) -> begin
(

let uu____3316 = (FStar_List.fold_right (fun uu____3323 uu____3324 -> (match (((uu____3323), (uu____3324))) with
| ((uu____3335, targ), (f, t)) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((targ), (f), (t)))))
end)) ml_bs ((f), (t)))
in (match (uu____3316) with
| (f, tfun) -> begin
(let _0_410 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun (((ml_bs), (ml_body)))))
in ((_0_410), (f), (tfun)))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____3351; FStar_Syntax_Syntax.pos = uu____3352; FStar_Syntax_Syntax.vars = uu____3353}, (t)::[]) -> begin
(

let uu____3376 = (term_as_mlexpr' g (Prims.fst t))
in (match (uu____3376) with
| (ml, e_tag, mlty) -> begin
((ml), (FStar_Extraction_ML_Syntax.E_PURE), (mlty))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____3388)); FStar_Syntax_Syntax.tk = uu____3389; FStar_Syntax_Syntax.pos = uu____3390; FStar_Syntax_Syntax.vars = uu____3391}, (t)::[]) -> begin
(

let uu____3414 = (term_as_mlexpr' g (Prims.fst t))
in (match (uu____3414) with
| (ml, e_tag, mlty) -> begin
((ml), (FStar_Extraction_ML_Syntax.E_IMPURE), (mlty))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let is_total = (fun uu___116_3450 -> (match (uu___116_3450) with
| FStar_Util.Inl (l) -> begin
(FStar_Syntax_Util.is_total_lcomp l)
end
| FStar_Util.Inr (l, flags) -> begin
((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_All.pipe_right flags (FStar_List.existsb (fun uu___115_3468 -> (match (uu___115_3468) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____3469 -> begin
false
end)))))
end))
in (

let uu____3470 = (let _0_411 = (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
in ((head.FStar_Syntax_Syntax.n), (_0_411)))
in (match (uu____3470) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____3476), uu____3477) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t))
end
| (uu____3487, FStar_Syntax_Syntax.Tm_abs (bs, uu____3489, Some (lc))) when (is_total lc) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t))
end
| uu____3518 -> begin
(

let rec extract_app = (fun is_data uu____3546 uu____3547 restArgs -> (match (((uu____3546), (uu____3547))) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match (((restArgs), (t))) with
| ([], uu____3595) -> begin
(

let evaluation_order_guaranteed = ((((FStar_List.length mlargs_f) = (Prims.parse_int "1")) || (FStar_Extraction_ML_Util.codegen_fsharp ())) || (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_And) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Or))
end
| uu____3609 -> begin
false
end))
in (

let uu____3610 = (match (evaluation_order_guaranteed) with
| true -> begin
(let _0_412 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in (([]), (_0_412)))
end
| uu____3637 -> begin
(FStar_List.fold_left (fun uu____3646 uu____3647 -> (match (((uu____3646), (uu____3647))) with
| ((lbs, out_args), (arg, f)) -> begin
(match (((f = FStar_Extraction_ML_Syntax.E_PURE) || (f = FStar_Extraction_ML_Syntax.E_GHOST))) with
| true -> begin
((lbs), ((arg)::out_args))
end
| uu____3700 -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _0_414 = (let _0_413 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (_0_413)::out_args)
in (((((x), (arg)))::lbs), (_0_414))))
end)
end)) (([]), ([])) mlargs_f)
end)
in (match (uu____3610) with
| (lbs, mlargs) -> begin
(

let app = (let _0_415 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_App (((mlhead), (mlargs)))))
in (FStar_All.pipe_left (maybe_eta_data_and_project_record g is_data t) _0_415))
in (

let l_app = (FStar_List.fold_right (fun uu____3732 out -> (match (uu____3732) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.mlty) (mk_MLE_Let false ((FStar_Extraction_ML_Syntax.NonRec), ([]), (({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = Some ((([]), (arg.FStar_Extraction_ML_Syntax.mlty))); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg; FStar_Extraction_ML_Syntax.print_typ = true})::[])) out))
end)) lbs app)
in ((l_app), (f), (t))))
end)))
end
| (((arg, uu____3745))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (formal_t, f', t)) when (is_type g arg) -> begin
(

let uu____3763 = (type_leq g formal_t FStar_Extraction_ML_Syntax.ml_unit_ty)
in (match (uu____3763) with
| true -> begin
(let _0_417 = (let _0_416 = (FStar_Extraction_ML_Util.join arg.FStar_Syntax_Syntax.pos f f')
in ((_0_416), (t)))
in (extract_app is_data ((mlhead), ((((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE)))::mlargs_f)) _0_417 rest))
end
| uu____3772 -> begin
(failwith (let _0_421 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule mlhead)
in (let _0_420 = (FStar_Syntax_Print.term_to_string arg)
in (let _0_419 = (FStar_Syntax_Print.tag_of_term arg)
in (let _0_418 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule formal_t)
in (FStar_Util.format4 "Impossible: ill-typed application:\n\thead=%s, arg=%s, tag=%s\n\texpected type unit, got %s" _0_421 _0_420 _0_419 _0_418))))))
end))
end
| (((e0, uu____3777))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t)) -> begin
(

let r = e0.FStar_Syntax_Syntax.pos
in (

let uu____3796 = (term_as_mlexpr g e0)
in (match (uu____3796) with
| (e0, f0, tInferred) -> begin
(

let e0 = (maybe_coerce g e0 tInferred tExpected)
in (let _0_423 = (let _0_422 = (FStar_Extraction_ML_Util.join_l r ((f)::(f')::(f0)::[]))
in ((_0_422), (t)))
in (extract_app is_data ((mlhead), ((((e0), (f0)))::mlargs_f)) _0_423 rest)))
end)))
end
| uu____3812 -> begin
(

let uu____3819 = (FStar_Extraction_ML_Util.udelta_unfold g t)
in (match (uu____3819) with
| Some (t) -> begin
(extract_app is_data ((mlhead), (mlargs_f)) ((f), (t)) restArgs)
end
| None -> begin
(err_ill_typed_application g top restArgs t)
end))
end)
end))
in (

let extract_app_maybe_projector = (fun is_data mlhead uu____3855 args -> (match (uu____3855) with
| (f, t) -> begin
(match (is_data) with
| Some (FStar_Syntax_Syntax.Record_projector (uu____3874)) -> begin
(

let rec remove_implicits = (fun args f t -> (match (((args), (t))) with
| (((a0, Some (FStar_Syntax_Syntax.Implicit (uu____3924))))::args, FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3926, f', t)) -> begin
(let _0_424 = (FStar_Extraction_ML_Util.join a0.FStar_Syntax_Syntax.pos f f')
in (remove_implicits args _0_424 t))
end
| uu____3951 -> begin
((args), (f), (t))
end))
in (

let uu____3966 = (remove_implicits args f t)
in (match (uu____3966) with
| (args, f, t) -> begin
(extract_app is_data ((mlhead), ([])) ((f), (t)) args)
end)))
end
| uu____3999 -> begin
(extract_app is_data ((mlhead), ([])) ((f), (t)) args)
end)
end))
in (

let uu____4006 = (is_type g t)
in (match (uu____4006) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____4010 -> begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let uu____4017 = (

let uu____4024 = (FStar_Extraction_ML_UEnv.lookup_term g head)
in (match (uu____4024) with
| (FStar_Util.Inr (u), q) -> begin
((u), (q))
end
| uu____4057 -> begin
(failwith "FIXME Ty")
end))
in (match (uu____4017) with
| ((head_ml, (vars, t), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, uu____4086))::uu____4087 -> begin
(is_type g a)
end
| uu____4101 -> begin
false
end)
in (

let uu____4107 = (match (vars) with
| (uu____4124)::uu____4125 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t), (args))
end
| uu____4132 -> begin
(

let n = (FStar_List.length vars)
in (match ((n <= (FStar_List.length args))) with
| true -> begin
(

let uu____4152 = (FStar_Util.first_N n args)
in (match (uu____4152) with
| (prefix, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun uu____4205 -> (match (uu____4205) with
| (x, uu____4209) -> begin
(term_as_mlty g x)
end)) prefix)
in (

let t = (instantiate ((vars), (t)) prefixAsMLTypes)
in (

let head = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) -> begin
(

let uu___120_4214 = head_ml
in {FStar_Extraction_ML_Syntax.expr = uu___120_4214.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t; FStar_Extraction_ML_Syntax.loc = uu___120_4214.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = uu____4216; FStar_Extraction_ML_Syntax.loc = uu____4217})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let uu___121_4220 = head
in {FStar_Extraction_ML_Syntax.expr = uu___121_4220.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t))); FStar_Extraction_ML_Syntax.loc = uu___121_4220.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t))
end
| uu____4221 -> begin
(failwith "Impossible: Unexpected head term")
end)
in ((head), (t), (rest)))))
end))
end
| uu____4227 -> begin
(err_uninst g head ((vars), (t)) top)
end))
end)
in (match (uu____4107) with
| (head_ml, head_t, args) -> begin
(match (args) with
| [] -> begin
(let _0_425 = (maybe_eta_data_and_project_record g qual head_t head_ml)
in ((_0_425), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| uu____4259 -> begin
(extract_app_maybe_projector qual head_ml ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args)
end)
end)))
end))
end
| uu____4265 -> begin
(

let uu____4266 = (term_as_mlexpr g head)
in (match (uu____4266) with
| (head, f, t) -> begin
(extract_app_maybe_projector None head ((f), (t)) args)
end))
end))
end))))
end)))
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

let uu____4314 = (check_term_as_mlexpr g e0 f t)
in (match (uu____4314) with
| (e, t) -> begin
((e), (f), (t))
end))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') -> begin
(

let top_level = (FStar_Syntax_Syntax.is_top_level lbs)
in (

let uu____4335 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.open_let_rec lbs e')
end
| uu____4342 -> begin
(

let uu____4343 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____4343) with
| true -> begin
((lbs), (e'))
end
| uu____4350 -> begin
(

let lb = (FStar_List.hd lbs)
in (

let x = (FStar_Syntax_Syntax.freshen_bv (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))
in (

let lb = (

let uu___122_4354 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___122_4354.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___122_4354.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___122_4354.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___122_4354.FStar_Syntax_Syntax.lbdef})
in (

let e' = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x))))::[]) e')
in (((lb)::[]), (e'))))))
end))
end)
in (match (uu____4335) with
| (lbs, e') -> begin
(

let lbs = (match (top_level) with
| true -> begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let tcenv = (let _0_426 = (FStar_Ident.lid_of_path (FStar_List.append (Prims.fst g.FStar_Extraction_ML_UEnv.currentModule) (((Prims.snd g.FStar_Extraction_ML_UEnv.currentModule))::[])) FStar_Range.dummyRange)
in (FStar_TypeChecker_Env.set_current_module g.FStar_Extraction_ML_UEnv.tcenv _0_426))
in ((FStar_Extraction_ML_UEnv.debug g (fun uu____4374 -> (FStar_Options.set_option "debug_level" (FStar_Options.List ((FStar_Options.String ("Norm"))::(FStar_Options.String ("Extraction"))::[])))));
(

let lbdef = (

let uu____4378 = (FStar_Options.ml_ish ())
in (match (uu____4378) with
| true -> begin
lb.FStar_Syntax_Syntax.lbdef
end
| uu____4381 -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.PureSubtermsWithinComputations)::(FStar_TypeChecker_Normalize.Primops)::[]) tcenv lb.FStar_Syntax_Syntax.lbdef)
end))
in (

let uu___123_4382 = lb
in {FStar_Syntax_Syntax.lbname = uu___123_4382.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___123_4382.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___123_4382.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___123_4382.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef}));
)))))
end
| uu____4383 -> begin
lbs
end)
in (

let maybe_generalize = (fun uu____4396 -> (match (uu____4396) with
| {FStar_Syntax_Syntax.lbname = lbname_; FStar_Syntax_Syntax.lbunivs = uu____4407; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = lbeff; FStar_Syntax_Syntax.lbdef = e} -> begin
(

let f_e = (effect_as_etag g lbeff)
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when (let _0_427 = (FStar_List.hd bs)
in (FStar_All.pipe_right _0_427 (is_type_binder g))) -> begin
(

let uu____4454 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____4454) with
| (bs, c) -> begin
(

let uu____4468 = (

let uu____4473 = (FStar_Util.prefix_until (fun x -> (not ((is_type_binder g x)))) bs)
in (match (uu____4473) with
| None -> begin
((bs), ((FStar_Syntax_Util.comp_result c)))
end
| Some (bs, b, rest) -> begin
(let _0_428 = (FStar_Syntax_Util.arrow ((b)::rest) c)
in ((bs), (_0_428)))
end))
in (match (uu____4468) with
| (tbinders, tbody) -> begin
(

let n_tbinders = (FStar_List.length tbinders)
in (

let e = (let _0_429 = (normalize_abs e)
in (FStar_All.pipe_right _0_429 FStar_Syntax_Util.unmeta))
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____4576) -> begin
(

let uu____4599 = (FStar_Syntax_Subst.open_term bs body)
in (match (uu____4599) with
| (bs, body) -> begin
(match ((n_tbinders <= (FStar_List.length bs))) with
| true -> begin
(

let uu____4629 = (FStar_Util.first_N n_tbinders bs)
in (match (uu____4629) with
| (targs, rest_args) -> begin
(

let expected_source_ty = (

let s = (FStar_List.map2 (fun uu____4672 uu____4673 -> (match (((uu____4672), (uu____4673))) with
| ((x, uu____4683), (y, uu____4685)) -> begin
FStar_Syntax_Syntax.NT ((let _0_430 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (_0_430))))
end)) tbinders targs)
in (FStar_Syntax_Subst.subst s tbody))
in (

let env = (FStar_List.fold_left (fun env uu____4694 -> (match (uu____4694) with
| (a, uu____4698) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) g targs)
in (

let expected_t = (term_as_mlty env expected_source_ty)
in (

let polytype = (let _0_431 = (FStar_All.pipe_right targs (FStar_List.map (fun uu____4719 -> (match (uu____4719) with
| (x, uu____4725) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((_0_431), (expected_t)))
in (

let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_fstar_value body)))
end
| uu____4729 -> begin
false
end)
in (

let rest_args = (match (add_unit) with
| true -> begin
(unit_binder)::rest_args
end
| uu____4736 -> begin
rest_args
end)
in (

let body = (match (rest_args) with
| [] -> begin
body
end
| uu____4738 -> begin
(FStar_Syntax_Util.abs rest_args body None)
end)
in ((lbname_), (f_e), (((t), (((targs), (polytype))))), (add_unit), (body)))))))))
end))
end
| uu____4777 -> begin
(failwith "Not enough type binders")
end)
end))
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) -> begin
(

let env = (FStar_List.fold_left (fun env uu____4794 -> (match (uu____4794) with
| (a, uu____4798) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (let _0_432 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____4816 -> (match (uu____4816) with
| (x, uu____4822) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((_0_432), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____4828 -> (match (uu____4828) with
| (bv, uu____4832) -> begin
(let _0_433 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right _0_433 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e), (args))))) None e.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t), (((tbinders), (polytype))))), (false), (e)))))))
end
| uu____4870 -> begin
(err_value_restriction e)
end)))
end))
end))
end
| uu____4880 -> begin
(

let expected_t = (term_as_mlty g t)
in ((lbname_), (f_e), (((t), ((([]), ((([]), (expected_t))))))), (false), (e)))
end)))
end))
in (

let check_lb = (fun env uu____4937 -> (match (uu____4937) with
| (nm, (lbname, f, (t, (targs, polytype)), add_unit, e)) -> begin
(

let env = (FStar_List.fold_left (fun env uu____5008 -> (match (uu____5008) with
| (a, uu____5012) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) env targs)
in (

let expected_t = (match (add_unit) with
| true -> begin
FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), ((Prims.snd polytype))))
end
| uu____5014 -> begin
(Prims.snd polytype)
end)
in (

let uu____5015 = (check_term_as_mlexpr env e f expected_t)
in (match (uu____5015) with
| (e, uu____5021) -> begin
(

let f = (maybe_downgrade_eff env f expected_t)
in ((f), ({FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = true})))
end))))
end))
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map maybe_generalize))
in (

let uu____5056 = (FStar_List.fold_right (fun lb uu____5095 -> (match (uu____5095) with
| (env, lbs) -> begin
(

let uu____5159 = lb
in (match (uu____5159) with
| (lbname, uu____5184, (t, (uu____5186, polytype)), add_unit, uu____5189) -> begin
(

let uu____5196 = (FStar_Extraction_ML_UEnv.extend_lb env lbname t polytype add_unit true)
in (match (uu____5196) with
| (env, nm) -> begin
((env), ((((nm), (lb)))::lbs))
end))
end))
end)) lbs ((g), ([])))
in (match (uu____5056) with
| (env_body, lbs) -> begin
(

let env_def = (match (is_rec) with
| true -> begin
env_body
end
| uu____5300 -> begin
g
end)
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (check_lb env_def)))
in (

let e'_rng = e'.FStar_Syntax_Syntax.pos
in (

let uu____5339 = (term_as_mlexpr env_body e')
in (match (uu____5339) with
| (e', f', t') -> begin
(

let f = (let _0_435 = (let _0_434 = (FStar_List.map Prims.fst lbs)
in (f')::_0_434)
in (FStar_Extraction_ML_Util.join_l e'_rng _0_435))
in (

let is_rec = (match ((is_rec = true)) with
| true -> begin
FStar_Extraction_ML_Syntax.Rec
end
| uu____5353 -> begin
FStar_Extraction_ML_Syntax.NonRec
end)
in (let _0_440 = (let _0_439 = (let _0_437 = (let _0_436 = (FStar_List.map Prims.snd lbs)
in ((is_rec), ([]), (_0_436)))
in (mk_MLE_Let top_level _0_437 e'))
in (let _0_438 = (FStar_Extraction_ML_Util.mlloc_of_range t.FStar_Syntax_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' _0_439 _0_438)))
in ((_0_440), (f), (t')))))
end)))))
end))))))
end)))
end
| FStar_Syntax_Syntax.Tm_match (scrutinee, pats) -> begin
(

let uu____5386 = (term_as_mlexpr g scrutinee)
in (match (uu____5386) with
| (e, f_e, t_e) -> begin
(

let uu____5396 = (check_pats_for_ite pats)
in (match (uu____5396) with
| (b, then_e, else_e) -> begin
(

let no_lift = (fun x t -> x)
in (match (b) with
| true -> begin
(match (((then_e), (else_e))) with
| (Some (then_e), Some (else_e)) -> begin
(

let uu____5431 = (term_as_mlexpr g then_e)
in (match (uu____5431) with
| (then_mle, f_then, t_then) -> begin
(

let uu____5441 = (term_as_mlexpr g else_e)
in (match (uu____5441) with
| (else_mle, f_else, t_else) -> begin
(

let uu____5451 = (

let uu____5458 = (type_leq g t_then t_else)
in (match (uu____5458) with
| true -> begin
((t_else), (no_lift))
end
| uu____5469 -> begin
(

let uu____5470 = (type_leq g t_else t_then)
in (match (uu____5470) with
| true -> begin
((t_then), (no_lift))
end
| uu____5481 -> begin
((FStar_Extraction_ML_Syntax.MLTY_Top), (FStar_Extraction_ML_Syntax.apply_obj_repr))
end))
end))
in (match (uu____5451) with
| (t_branch, maybe_lift) -> begin
(let _0_445 = (let _0_443 = FStar_Extraction_ML_Syntax.MLE_If ((let _0_442 = (maybe_lift then_mle t_then)
in (let _0_441 = Some ((maybe_lift else_mle t_else))
in ((e), (_0_442), (_0_441)))))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) _0_443))
in (let _0_444 = (FStar_Extraction_ML_Util.join then_e.FStar_Syntax_Syntax.pos f_then f_else)
in ((_0_445), (_0_444), (t_branch))))
end))
end))
end))
end
| uu____5500 -> begin
(failwith "ITE pats matched but then and else expressions not found?")
end)
end
| uu____5508 -> begin
(

let uu____5509 = (FStar_All.pipe_right pats (FStar_Util.fold_map (fun compat br -> (

let uu____5559 = (FStar_Syntax_Subst.open_branch br)
in (match (uu____5559) with
| (pat, when_opt, branch) -> begin
(

let uu____5589 = (extract_pat g pat t_e)
in (match (uu____5589) with
| (env, p, pat_t_compat) -> begin
(

let uu____5620 = (match (when_opt) with
| None -> begin
((None), (FStar_Extraction_ML_Syntax.E_PURE))
end
| Some (w) -> begin
(

let uu____5635 = (term_as_mlexpr env w)
in (match (uu____5635) with
| (w, f_w, t_w) -> begin
(

let w = (maybe_coerce env w t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in ((Some (w)), (f_w)))
end))
end)
in (match (uu____5620) with
| (when_opt, f_when) -> begin
(

let uu____5663 = (term_as_mlexpr env branch)
in (match (uu____5663) with
| (mlbranch, f_branch, t_branch) -> begin
(let _0_446 = (FStar_All.pipe_right p (FStar_List.map (fun uu____5718 -> (match (uu____5718) with
| (p, wopt) -> begin
(

let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt)
in ((p), (((when_clause), (f_when))), (((mlbranch), (f_branch), (t_branch)))))
end))))
in (((compat && pat_t_compat)), (_0_446)))
end))
end))
end))
end))) true))
in (match (uu____5509) with
| (pat_t_compat, mlbranches) -> begin
(

let mlbranches = (FStar_List.flatten mlbranches)
in (

let e = (match (pat_t_compat) with
| true -> begin
e
end
| uu____5792 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____5794 -> (let _0_448 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (let _0_447 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t_e)
in (FStar_Util.print2 "Coercing scrutinee %s from type %s because pattern type is incompatible\n" _0_448 _0_447)))));
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_e) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (t_e), (FStar_Extraction_ML_Syntax.MLTY_Top)))));
)
end)
in (match (mlbranches) with
| [] -> begin
(

let uu____5807 = (let _0_450 = (let _0_449 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Extraction_ML_UEnv.lookup_fv g _0_449))
in (FStar_All.pipe_left FStar_Util.right _0_450))
in (match (uu____5807) with
| (fw, uu____5830, uu____5831) -> begin
(let _0_454 = (let _0_453 = FStar_Extraction_ML_Syntax.MLE_App ((let _0_452 = (let _0_451 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (_0_451)::[])
in ((fw), (_0_452))))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) _0_453))
in ((_0_454), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
end))
end
| ((uu____5833, uu____5834, (uu____5835, f_first, t_first)))::rest -> begin
(

let uu____5867 = (FStar_List.fold_left (fun uu____5883 uu____5884 -> (match (((uu____5883), (uu____5884))) with
| ((topt, f), (uu____5914, uu____5915, (uu____5916, f_branch, t_branch))) -> begin
(

let f = (FStar_Extraction_ML_Util.join top.FStar_Syntax_Syntax.pos f f_branch)
in (

let topt = (match (topt) with
| None -> begin
None
end
| Some (t) -> begin
(

let uu____5947 = (type_leq g t t_branch)
in (match (uu____5947) with
| true -> begin
Some (t_branch)
end
| uu____5949 -> begin
(

let uu____5950 = (type_leq g t_branch t)
in (match (uu____5950) with
| true -> begin
Some (t)
end
| uu____5952 -> begin
None
end))
end))
end)
in ((topt), (f))))
end)) ((Some (t_first)), (f_first)) rest)
in (match (uu____5867) with
| (topt, f_match) -> begin
(

let mlbranches = (FStar_All.pipe_right mlbranches (FStar_List.map (fun uu____5996 -> (match (uu____5996) with
| (p, (wopt, uu____6012), (b, uu____6014, t)) -> begin
(

let b = (match (topt) with
| None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b t)
end
| Some (uu____6025) -> begin
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
in (let _0_455 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match (((e), (mlbranches)))))
in ((_0_455), (f_match), (t_match)))))
end))
end)))
end))
end))
end))
end))
end));
))


let fresh : Prims.string  ->  (Prims.string * Prims.int) = (

let c = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun x -> ((FStar_Util.incr c);
(let _0_456 = (FStar_ST.read c)
in ((x), (_0_456)));
)))


let ind_discriminator_body : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (

let uu____6057 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv discName)
in (match (uu____6057) with
| (uu____6060, fstar_disc_type) -> begin
(

let wildcards = (

let uu____6068 = (FStar_Syntax_Subst.compress fstar_disc_type).FStar_Syntax_Syntax.n
in (match (uu____6068) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____6075) -> begin
(let _0_458 = (FStar_All.pipe_right binders (FStar_List.filter (fun uu___117_6105 -> (match (uu___117_6105) with
| (uu____6109, Some (FStar_Syntax_Syntax.Implicit (uu____6110))) -> begin
true
end
| uu____6112 -> begin
false
end))))
in (FStar_All.pipe_right _0_458 (FStar_List.map (fun uu____6123 -> (let _0_457 = (fresh "_")
in ((_0_457), (FStar_Extraction_ML_Syntax.MLTY_Top)))))))
end
| uu____6129 -> begin
(failwith "Discriminator must be a function")
end))
in (

let mlid = (fresh "_discr_")
in (

let targ = FStar_Extraction_ML_Syntax.MLTY_Top
in (

let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top
in (

let discrBody = (let _0_470 = FStar_Extraction_ML_Syntax.MLE_Fun ((let _0_469 = (let _0_468 = FStar_Extraction_ML_Syntax.MLE_Match ((let _0_467 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name ((([]), ((FStar_Extraction_ML_Syntax.idsym mlid))))))
in (let _0_466 = (let _0_465 = (let _0_461 = FStar_Extraction_ML_Syntax.MLP_CTor ((let _0_459 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in ((_0_459), ((FStar_Extraction_ML_Syntax.MLP_Wild)::[]))))
in (let _0_460 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in ((_0_461), (None), (_0_460))))
in (let _0_464 = (let _0_463 = (let _0_462 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in ((FStar_Extraction_ML_Syntax.MLP_Wild), (None), (_0_462)))
in (_0_463)::[])
in (_0_465)::_0_464))
in ((_0_467), (_0_466)))))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _0_468))
in (((FStar_List.append wildcards ((((mlid), (targ)))::[]))), (_0_469))))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) _0_470))
in FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NonRec), ([]), (({FStar_Extraction_ML_Syntax.mllb_name = (FStar_Extraction_ML_UEnv.convIdent discName.FStar_Ident.ident); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.print_typ = false})::[]))))))))
end)))




