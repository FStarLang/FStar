
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


let fail = (fun r msg -> ((

let uu____78 = (

let uu____79 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" uu____79 msg))
in (FStar_All.pipe_left FStar_Util.print_string uu____78));
(failwith msg);
))


let err_uninst = (fun env t uu____107 app -> (match (uu____107) with
| (vars, ty) -> begin
(

let uu____122 = (

let uu____123 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____124 = (

let uu____125 = (FStar_All.pipe_right vars (FStar_List.map Prims.fst))
in (FStar_All.pipe_right uu____125 (FStar_String.concat ", ")))
in (

let uu____134 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (

let uu____135 = (FStar_Syntax_Print.term_to_string app)
in (FStar_Util.format4 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s" uu____123 uu____124 uu____134 uu____135)))))
in (fail t.FStar_Syntax_Syntax.pos uu____122))
end))


let err_ill_typed_application = (fun env t args ty -> (

let uu____166 = (

let uu____167 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____168 = (

let uu____169 = (FStar_All.pipe_right args (FStar_List.map (fun uu____177 -> (match (uu____177) with
| (x, uu____181) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right uu____169 (FStar_String.concat " ")))
in (

let uu____183 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n" uu____167 uu____168 uu____183))))
in (fail t.FStar_Syntax_Syntax.pos uu____166)))


let err_value_restriction = (fun t -> (

let uu____195 = (

let uu____196 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____197 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Refusing to generalize because of the value restriction: (%s) %s" uu____196 uu____197)))
in (fail t.FStar_Syntax_Syntax.pos uu____195)))


let err_unexpected_eff = (fun t f0 f1 -> (

let uu____219 = (

let uu____220 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" uu____220 (FStar_Extraction_ML_Util.eff_to_string f0) (FStar_Extraction_ML_Util.eff_to_string f1)))
in (fail t.FStar_Syntax_Syntax.pos uu____219)))


let effect_as_etag : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.e_tag = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (

let rec delta_norm_eff = (fun g l -> (

let uu____234 = (FStar_Util.smap_try_find cache l.FStar_Ident.str)
in (match (uu____234) with
| Some (l1) -> begin
l1
end
| None -> begin
(

let res = (

let uu____238 = (FStar_TypeChecker_Env.lookup_effect_abbrev g.FStar_Extraction_ML_UEnv.tcenv ((FStar_Syntax_Syntax.U_zero)::[]) l)
in (match (uu____238) with
| None -> begin
l
end
| Some (uu____244, c) -> begin
(delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c))
end))
in ((FStar_Util.smap_add cache l.FStar_Ident.str res);
res;
))
end)))
in (fun g l -> (

let l1 = (delta_norm_eff g l)
in (match ((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_PURE_lid)) with
| true -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| uu____252 -> begin
(match ((FStar_Ident.lid_equals l1 FStar_Syntax_Const.effect_GHOST_lid)) with
| true -> begin
FStar_Extraction_ML_Syntax.E_GHOST
end
| uu____253 -> begin
FStar_Extraction_ML_Syntax.E_IMPURE
end)
end)))))


let rec is_arity : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t1 = (FStar_Syntax_Util.unmeta t)
in (

let uu____261 = (

let uu____262 = (FStar_Syntax_Subst.compress t1)
in uu____262.FStar_Syntax_Syntax.n)
in (match (uu____261) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_meta (_)) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) -> begin
false
end
| FStar_Syntax_Syntax.Tm_type (uu____272) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____273, c) -> begin
(is_arity env (FStar_Syntax_Util.comp_result c))
end
| FStar_Syntax_Syntax.Tm_fvar (uu____285) -> begin
(

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env.FStar_Extraction_ML_UEnv.tcenv t1)
in (

let uu____287 = (

let uu____288 = (FStar_Syntax_Subst.compress t2)
in uu____288.FStar_Syntax_Syntax.n)
in (match (uu____287) with
| FStar_Syntax_Syntax.Tm_fvar (uu____291) -> begin
false
end
| uu____292 -> begin
(is_arity env t2)
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____293) -> begin
(

let uu____303 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____303) with
| (head1, uu____314) -> begin
(is_arity env head1)
end))
end
| FStar_Syntax_Syntax.Tm_uinst (head1, uu____330) -> begin
(is_arity env head1)
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____336) -> begin
(is_arity env x.FStar_Syntax_Syntax.sort)
end
| (FStar_Syntax_Syntax.Tm_abs (_, body, _)) | (FStar_Syntax_Syntax.Tm_let (_, body)) -> begin
(is_arity env body)
end
| FStar_Syntax_Syntax.Tm_match (uu____365, branches) -> begin
(match (branches) with
| ((uu____393, uu____394, e))::uu____396 -> begin
(is_arity env e)
end
| uu____432 -> begin
false
end)
end))))


let rec is_type_aux : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(

let uu____452 = (

let uu____453 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format1 "Impossible: %s" uu____453))
in (failwith uu____452))
end
| FStar_Syntax_Syntax.Tm_constant (uu____454) -> begin
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

let uu____460 = (FStar_TypeChecker_Env.is_type_constructor env.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____460) with
| true -> begin
true
end
| uu____465 -> begin
(

let uu____466 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____466) with
| ((uu____475, t2), uu____477) -> begin
(is_arity env t2)
end))
end))
end
| (FStar_Syntax_Syntax.Tm_uvar (_, t2)) | (FStar_Syntax_Syntax.Tm_bvar ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t2})) | (FStar_Syntax_Syntax.Tm_name ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t2})) -> begin
(is_arity env t2)
end
| FStar_Syntax_Syntax.Tm_ascribed (t2, uu____499, uu____500) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_uinst (t2, uu____530) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_abs (uu____535, body, uu____537) -> begin
(is_type_aux env body)
end
| FStar_Syntax_Syntax.Tm_let (uu____560, body) -> begin
(is_type_aux env body)
end
| FStar_Syntax_Syntax.Tm_match (uu____572, branches) -> begin
(match (branches) with
| ((uu____600, uu____601, e))::uu____603 -> begin
(is_type_aux env e)
end
| uu____639 -> begin
(failwith "Empty branches")
end)
end
| FStar_Syntax_Syntax.Tm_meta (t2, uu____652) -> begin
(is_type_aux env t2)
end
| FStar_Syntax_Syntax.Tm_app (head1, uu____658) -> begin
(is_type_aux env head1)
end)))


let is_type : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let b = (is_type_aux env t)
in ((FStar_Extraction_ML_UEnv.debug env (fun uu____681 -> (match (b) with
| true -> begin
(

let uu____682 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____683 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "is_type %s (%s)\n" uu____682 uu____683)))
end
| uu____684 -> begin
(

let uu____685 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____686 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "not a type %s (%s)\n" uu____685 uu____686)))
end)));
b;
)))


let is_type_binder = (fun env x -> (is_arity env (Prims.fst x).FStar_Syntax_Syntax.sort))


let is_constructor : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____706 = (

let uu____707 = (FStar_Syntax_Subst.compress t)
in uu____707.FStar_Syntax_Syntax.n)
in (match (uu____706) with
| (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| uu____715 -> begin
false
end)))


let rec is_fstar_value : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____719 = (

let uu____720 = (FStar_Syntax_Subst.compress t)
in uu____720.FStar_Syntax_Syntax.n)
in (match (uu____719) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____743 = (is_constructor head1)
in (match (uu____743) with
| true -> begin
(FStar_All.pipe_right args (FStar_List.for_all (fun uu____751 -> (match (uu____751) with
| (te, uu____755) -> begin
(is_fstar_value te)
end))))
end
| uu____756 -> begin
false
end))
end
| (FStar_Syntax_Syntax.Tm_meta (t1, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t1, _, _)) -> begin
(is_fstar_value t1)
end
| uu____781 -> begin
false
end)))


let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Fun (_)) -> begin
true
end
| (FStar_Extraction_ML_Syntax.MLE_CTor (_, exps)) | (FStar_Extraction_ML_Syntax.MLE_Tuple (exps)) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (uu____794, fields) -> begin
(FStar_Util.for_all (fun uu____806 -> (match (uu____806) with
| (uu____809, e1) -> begin
(is_ml_value e1)
end)) fields)
end
| uu____811 -> begin
false
end))


let normalize_abs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t0 -> (

let rec aux = (fun bs t copt -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs', body, copt1) -> begin
(aux (FStar_List.append bs bs') body copt1)
end
| uu____871 -> begin
(

let e' = (FStar_Syntax_Util.unascribe t1)
in (

let uu____873 = (FStar_Syntax_Util.is_fun e')
in (match (uu____873) with
| true -> begin
(aux bs e' copt)
end
| uu____874 -> begin
(FStar_Syntax_Util.abs bs e' copt)
end)))
end)))
in (aux [] t0 None)))


let unit_binder : FStar_Syntax_Syntax.binder = (

let uu____882 = (FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____882))


let check_pats_for_ite : (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term Prims.option) = (fun l -> (

let def = ((false), (None), (None))
in (match (((FStar_List.length l) <> (Prims.parse_int "2"))) with
| true -> begin
def
end
| uu____925 -> begin
(

let uu____926 = (FStar_List.hd l)
in (match (uu____926) with
| (p1, w1, e1) -> begin
(

let uu____945 = (

let uu____950 = (FStar_List.tl l)
in (FStar_List.hd uu____950))
in (match (uu____945) with
| (p2, w2, e2) -> begin
(match (((w1), (w2), (p1.FStar_Syntax_Syntax.v), (p2.FStar_Syntax_Syntax.v))) with
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
((true), (Some (e1)), (Some (e2)))
end
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
((true), (Some (e2)), (Some (e1)))
end
| uu____989 -> begin
def
end)
end))
end))
end)))


let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))


let erasable : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g f t -> ((f = FStar_Extraction_ML_Syntax.E_GHOST) || ((f = FStar_Extraction_ML_Syntax.E_PURE) && (erasableType g t))))


let erase : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e ty f -> (

let e1 = (

let uu____1032 = (erasable g f ty)
in (match (uu____1032) with
| true -> begin
(

let uu____1033 = (type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty)
in (match (uu____1033) with
| true -> begin
FStar_Extraction_ML_Syntax.ml_unit
end
| uu____1034 -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) (FStar_Extraction_ML_Syntax.MLE_Coerce (((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.ml_unit_ty), (ty)))))
end))
end
| uu____1035 -> begin
e
end))
in ((e1), (f), (ty))))


let maybe_coerce : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e ty expect -> (

let ty1 = (eraseTypeDeep g ty)
in (

let uu____1049 = ((type_leq_c g (Some (e)) ty1) expect)
in (match (uu____1049) with
| (true, Some (e')) -> begin
e'
end
| uu____1055 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____1060 -> (

let uu____1061 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (

let uu____1062 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty1)
in (

let uu____1063 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule expect)
in (FStar_Util.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n" uu____1061 uu____1062 uu____1063))))));
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (ty1), (expect)))));
)
end))))


let bv_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bv -> (

let uu____1070 = (FStar_Extraction_ML_UEnv.lookup_bv g bv)
in (match (uu____1070) with
| FStar_Util.Inl (uu____1071, t) -> begin
t
end
| uu____1079 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)))


let rec term_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t0 -> (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t0)
in (

let mlt = (term_as_mlty' g t)
in (

let uu____1113 = ((fun t1 -> (match (t1) with
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
true
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____1115) -> begin
(

let uu____1119 = (FStar_Extraction_ML_Util.udelta_unfold g t1)
in (match (uu____1119) with
| None -> begin
false
end
| Some (t2) -> begin
((

let rec is_top_ty = (fun t3 -> (match (t3) with
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
true
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____1126) -> begin
(

let uu____1130 = (FStar_Extraction_ML_Util.udelta_unfold g t3)
in (match (uu____1130) with
| None -> begin
false
end
| Some (t4) -> begin
(is_top_ty t4)
end))
end
| uu____1133 -> begin
false
end))
in is_top_ty) t2)
end))
end
| uu____1134 -> begin
false
end)) mlt)
in (match (uu____1113) with
| true -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t0)
in (term_as_mlty' g t1))
end
| uu____1136 -> begin
mlt
end)))))
and term_as_mlty' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun env t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(

let uu____1142 = (

let uu____1143 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Impossible: Unexpected term %s" uu____1143))
in (failwith uu____1142))
end
| FStar_Syntax_Syntax.Tm_constant (uu____1144) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1145) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| (FStar_Syntax_Syntax.Tm_meta (t2, _)) | (FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t2}, _)) | (FStar_Syntax_Syntax.Tm_uinst (t2, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t2, _, _)) -> begin
(term_as_mlty' env t2)
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv [])
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____1208 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____1208) with
| (bs1, c1) -> begin
(

let uu____1213 = (binders_as_ml_binders env bs1)
in (match (uu____1213) with
| (mlbs, env1) -> begin
(

let t_ret = (

let eff = (FStar_TypeChecker_Env.norm_eff_name env1.FStar_Extraction_ML_UEnv.tcenv (FStar_Syntax_Util.comp_effect_name c1))
in (

let ed = (FStar_TypeChecker_Env.get_effect_decl env1.FStar_Extraction_ML_UEnv.tcenv eff)
in (

let uu____1230 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (match (uu____1230) with
| true -> begin
(

let t2 = (FStar_TypeChecker_Env.reify_comp env1.FStar_Extraction_ML_UEnv.tcenv c1 FStar_Syntax_Syntax.U_unknown)
in (

let res = (term_as_mlty' env1 t2)
in res))
end
| uu____1234 -> begin
(term_as_mlty' env1 (FStar_Syntax_Util.comp_result c1))
end))))
in (

let erase1 = (effect_as_etag env1 (FStar_Syntax_Util.comp_effect_name c1))
in (

let uu____1236 = (FStar_List.fold_right (fun uu____1243 uu____1244 -> (match (((uu____1243), (uu____1244))) with
| ((uu____1255, t2), (tag, t')) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((t2), (tag), (t')))))
end)) mlbs ((erase1), (t_ret)))
in (match (uu____1236) with
| (uu____1263, t2) -> begin
t2
end))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let res = (

let uu____1282 = (

let uu____1283 = (FStar_Syntax_Util.un_uinst head1)
in uu____1283.FStar_Syntax_Syntax.n)
in (match (uu____1282) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv args)
end
| FStar_Syntax_Syntax.Tm_app (head2, args') -> begin
(

let uu____1304 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head2), ((FStar_List.append args' args))))) None t1.FStar_Syntax_Syntax.pos)
in (term_as_mlty' env uu____1304))
end
| uu____1320 -> begin
FStar_Extraction_ML_UEnv.unknownType
end))
in res)
end
| FStar_Syntax_Syntax.Tm_abs (bs, ty, uu____1323) -> begin
(

let uu____1346 = (FStar_Syntax_Subst.open_term bs ty)
in (match (uu____1346) with
| (bs1, ty1) -> begin
(

let uu____1351 = (binders_as_ml_binders env bs1)
in (match (uu____1351) with
| (bts, env1) -> begin
(term_as_mlty' env1 ty1)
end))
end))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
FStar_Extraction_ML_UEnv.unknownType
end)))
and arg_as_mlty : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual)  ->  FStar_Extraction_ML_Syntax.mlty = (fun g uu____1369 -> (match (uu____1369) with
| (a, uu____1373) -> begin
(

let uu____1374 = (is_type g a)
in (match (uu____1374) with
| true -> begin
(term_as_mlty' g a)
end
| uu____1375 -> begin
FStar_Extraction_ML_UEnv.erasedContent
end))
end))
and fv_app_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.args  ->  FStar_Extraction_ML_Syntax.mlty = (fun g fv args -> (

let uu____1379 = (FStar_Syntax_Util.arrow_formals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (match (uu____1379) with
| (formals, t) -> begin
(

let mlargs = (FStar_List.map (arg_as_mlty g) args)
in (

let mlargs1 = (

let n_args = (FStar_List.length args)
in (match (((FStar_List.length formals) > n_args)) with
| true -> begin
(

let uu____1423 = (FStar_Util.first_N n_args formals)
in (match (uu____1423) with
| (uu____1437, rest) -> begin
(

let uu____1451 = (FStar_List.map (fun uu____1455 -> FStar_Extraction_ML_UEnv.erasedContent) rest)
in (FStar_List.append mlargs uu____1451))
end))
end
| uu____1458 -> begin
mlargs
end))
in (

let nm = (

let uu____1460 = (FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv)
in (match (uu____1460) with
| Some (p) -> begin
p
end
| None -> begin
(FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))
in FStar_Extraction_ML_Syntax.MLTY_Named (((mlargs1), (nm))))))
end)))
and binders_as_ml_binders : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list * FStar_Extraction_ML_UEnv.env) = (fun g bs -> (

let uu____1475 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____1499 b -> (match (uu____1499) with
| (ml_bs, env) -> begin
(

let uu____1529 = (is_type_binder g b)
in (match (uu____1529) with
| true -> begin
(

let b1 = (Prims.fst b)
in (

let env1 = (FStar_Extraction_ML_UEnv.extend_ty env b1 (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (

let ml_b = (

let uu____1544 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b1)
in ((uu____1544), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
in (((ml_b)::ml_bs), (env1)))))
end
| uu____1558 -> begin
(

let b1 = (Prims.fst b)
in (

let t = (term_as_mlty env b1.FStar_Syntax_Syntax.sort)
in (

let uu____1561 = (FStar_Extraction_ML_UEnv.extend_bv env b1 (([]), (t)) false false false)
in (match (uu____1561) with
| (env1, b2) -> begin
(

let ml_b = (

let uu____1579 = (FStar_Extraction_ML_UEnv.removeTick b2)
in ((uu____1579), (t)))
in (((ml_b)::ml_bs), (env1)))
end))))
end))
end)) (([]), (g))))
in (match (uu____1475) with
| (ml_bs, env) -> begin
(((FStar_List.rev ml_bs)), (env))
end)))


let mk_MLE_Seq : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun e1 e2 -> (match (((e1.FStar_Extraction_ML_Syntax.expr), (e2.FStar_Extraction_ML_Syntax.expr))) with
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 es2))
end
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), uu____1639) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 ((e2)::[])))
end
| (uu____1641, FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::es2)
end
| uu____1644 -> begin
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
| uu____1664 -> begin
(match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Var (x) when (x = lb.FStar_Extraction_ML_Syntax.mllb_name) -> begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end
| uu____1666 when (lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr) -> begin
body.FStar_Extraction_ML_Syntax.expr
end
| uu____1667 -> begin
(mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def body)
end)
end)
end
| uu____1668 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end)
end
| uu____1670 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end))


let resugar_pat : FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_ML_Syntax.mlpattern = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(match ((FStar_Extraction_ML_Util.is_xtuple d)) with
| Some (n1) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| uu____1684 -> begin
(match (q) with
| Some (FStar_Syntax_Syntax.Record_ctor (ty, fns)) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id ty.FStar_Ident.ns)
in (

let fs = (record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record (((path), (fs)))))
end
| uu____1700 -> begin
p
end)
end)
end
| uu____1702 -> begin
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
(FStar_Extraction_ML_UEnv.debug g (fun uu____1741 -> (

let uu____1742 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t')
in (

let uu____1743 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t)
in (FStar_Util.print2 "Expected pattern type %s; got pattern type %s\n" uu____1742 uu____1743)))))
end
| uu____1744 -> begin
()
end);
ok;
))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____1752) -> begin
(failwith "Impossible: Nested disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int (c, None)) -> begin
(

let i = FStar_Const.Const_int (((c), (None)))
in (

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let when_clause = (

let uu____1777 = (

let uu____1778 = (

let uu____1782 = (

let uu____1784 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (

let uu____1785 = (

let uu____1787 = (

let uu____1788 = (

let uu____1789 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p i)
in (FStar_All.pipe_left (fun _0_30 -> FStar_Extraction_ML_Syntax.MLE_Const (_0_30)) uu____1789))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) uu____1788))
in (uu____1787)::[])
in (uu____1784)::uu____1785))
in ((FStar_Extraction_ML_Util.prims_op_equality), (uu____1782)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____1778))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) uu____1777))
in (

let uu____1791 = (ok FStar_Extraction_ML_Syntax.ml_int_ty)
in ((g), (Some (((FStar_Extraction_ML_Syntax.MLP_Var (x)), ((when_clause)::[])))), (uu____1791))))))
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(

let t = (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange s)
in (

let mlty = (term_as_mlty g t)
in (

let uu____1803 = (

let uu____1808 = (

let uu____1812 = (

let uu____1813 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (uu____1813))
in ((uu____1812), ([])))
in Some (uu____1808))
in (

let uu____1818 = (ok mlty)
in ((g), (uu____1803), (uu____1818))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) when disjunctive_pat -> begin
((g), (Some (((FStar_Extraction_ML_Syntax.MLP_Wild), ([])))), (true))
end
| (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let uu____1834 = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (match (uu____1834) with
| (g1, x1) -> begin
(

let uu____1847 = (ok mlty)
in ((g1), ((match (imp) with
| true -> begin
None
end
| uu____1859 -> begin
Some (((FStar_Extraction_ML_Syntax.MLP_Var (x1)), ([])))
end)), (uu____1847)))
end)))
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____1864) -> begin
((g), (None), (true))
end
| FStar_Syntax_Syntax.Pat_cons (f, pats) -> begin
(

let uu____1888 = (

let uu____1891 = (FStar_Extraction_ML_UEnv.lookup_fv g f)
in (match (uu____1891) with
| FStar_Util.Inr (uu____1894, {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n1); FStar_Extraction_ML_Syntax.mlty = uu____1896; FStar_Extraction_ML_Syntax.loc = uu____1897}, ttys, uu____1899) -> begin
((n1), (ttys))
end
| uu____1906 -> begin
(failwith "Expected a constructor")
end))
in (match (uu____1888) with
| (d, tys) -> begin
(

let nTyVars = (FStar_List.length (Prims.fst tys))
in (

let uu____1920 = (FStar_Util.first_N nTyVars pats)
in (match (uu____1920) with
| (tysVarPats, restPats) -> begin
(

let f_ty_opt = try
(match (()) with
| () -> begin
(

let mlty_args = (FStar_All.pipe_right tysVarPats (FStar_List.map (fun uu____1994 -> (match (uu____1994) with
| (p1, uu____2000) -> begin
(match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (uu____2005, t) -> begin
(term_as_mlty g t)
end
| uu____2011 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____2013 -> (

let uu____2014 = (FStar_Syntax_Print.pat_to_string p1)
in (FStar_Util.print1 "Pattern %s is not extractable" uu____2014))));
(Prims.raise Un_extractable);
)
end)
end))))
in (

let f_ty = (FStar_Extraction_ML_Util.subst tys mlty_args)
in (

let uu____2016 = (FStar_Extraction_ML_Util.uncurry_mlty_fun f_ty)
in Some (uu____2016))))
end)
with
| Un_extractable -> begin
None
end
in (

let uu____2031 = (FStar_Util.fold_map (fun g1 uu____2046 -> (match (uu____2046) with
| (p1, imp1) -> begin
(

let uu____2057 = (extract_one_pat disjunctive_pat true g1 p1 None)
in (match (uu____2057) with
| (g2, p2, uu____2073) -> begin
((g2), (p2))
end))
end)) g tysVarPats)
in (match (uu____2031) with
| (g1, tyMLPats) -> begin
(

let uu____2105 = (FStar_Util.fold_map (fun uu____2131 uu____2132 -> (match (((uu____2131), (uu____2132))) with
| ((g2, f_ty_opt1), (p1, imp1)) -> begin
(

let uu____2181 = (match (f_ty_opt1) with
| Some ((hd1)::rest, res) -> begin
((Some (((rest), (res)))), (Some (hd1)))
end
| uu____2213 -> begin
((None), (None))
end)
in (match (uu____2181) with
| (f_ty_opt2, expected_ty) -> begin
(

let uu____2250 = (extract_one_pat disjunctive_pat false g2 p1 expected_ty)
in (match (uu____2250) with
| (g3, p2, uu____2272) -> begin
((((g3), (f_ty_opt2))), (p2))
end))
end))
end)) ((g1), (f_ty_opt)) restPats)
in (match (uu____2105) with
| ((g2, f_ty_opt1), restMLPats) -> begin
(

let uu____2333 = (

let uu____2339 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun uu___136_2364 -> (match (uu___136_2364) with
| Some (x) -> begin
(x)::[]
end
| uu____2386 -> begin
[]
end))))
in (FStar_All.pipe_right uu____2339 FStar_List.split))
in (match (uu____2333) with
| (mlPats, when_clauses) -> begin
(

let pat_ty_compat = (match (f_ty_opt1) with
| Some ([], t) -> begin
(ok t)
end
| uu____2425 -> begin
false
end)
in (

let uu____2430 = (

let uu____2435 = (

let uu____2439 = (resugar_pat f.FStar_Syntax_Syntax.fv_qual (FStar_Extraction_ML_Syntax.MLP_CTor (((d), (mlPats)))))
in (

let uu____2441 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in ((uu____2439), (uu____2441))))
in Some (uu____2435))
in ((g2), (uu____2430), (pat_ty_compat))))
end))
end))
end)))
end)))
end))
end)))


let extract_pat : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option) Prims.list * Prims.bool) = (fun g p expected_t -> (

let extract_one_pat1 = (fun disj g1 p1 expected_t1 -> (

let uu____2502 = (extract_one_pat disj false g1 p1 expected_t1)
in (match (uu____2502) with
| (g2, Some (x, v1), b) -> begin
((g2), (((x), (v1))), (b))
end
| uu____2533 -> begin
(failwith "Impossible: Unable to translate pattern")
end)))
in (

let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| (hd1)::tl1 -> begin
(

let uu____2558 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd1 tl1)
in Some (uu____2558))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible: Empty disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_disj ((p1)::pats) -> begin
(

let uu____2584 = (extract_one_pat1 true g p1 (Some (expected_t)))
in (match (uu____2584) with
| (g', p2, b) -> begin
(

let uu____2607 = (FStar_Util.fold_map (fun b1 p3 -> (

let uu____2619 = (extract_one_pat1 true g p3 (Some (expected_t)))
in (match (uu____2619) with
| (uu____2631, p4, b') -> begin
(((b1 && b')), (p4))
end))) b pats)
in (match (uu____2607) with
| (b1, ps) -> begin
(

let ps1 = (p2)::ps
in (

let g1 = g'
in (

let uu____2669 = (FStar_All.pipe_right ps1 (FStar_List.partition (fun uu___137_2697 -> (match (uu___137_2697) with
| (uu____2701, (uu____2702)::uu____2703) -> begin
true
end
| uu____2706 -> begin
false
end))))
in (match (uu____2669) with
| (ps_when, rest) -> begin
(

let ps2 = (FStar_All.pipe_right ps_when (FStar_List.map (fun uu____2754 -> (match (uu____2754) with
| (x, whens) -> begin
(

let uu____2765 = (mk_when_clause whens)
in ((x), (uu____2765)))
end))))
in (

let res = (match (rest) with
| [] -> begin
((g1), (ps2), (b1))
end
| rest1 -> begin
(

let uu____2795 = (

let uu____2800 = (

let uu____2804 = (

let uu____2805 = (FStar_List.map Prims.fst rest1)
in FStar_Extraction_ML_Syntax.MLP_Branch (uu____2805))
in ((uu____2804), (None)))
in (uu____2800)::ps2)
in ((g1), (uu____2795), (b1)))
end)
in res))
end))))
end))
end))
end
| uu____2819 -> begin
(

let uu____2820 = (extract_one_pat1 false g p (Some (expected_t)))
in (match (uu____2820) with
| (g1, (p1, whens), b) -> begin
(

let when_clause = (mk_when_clause whens)
in ((g1), ((((p1), (when_clause)))::[]), (b)))
end))
end))))


let maybe_eta_data_and_project_record : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (

let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, uu____2902, t1) -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let uu____2905 = (

let uu____2911 = (

let uu____2916 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((((x), (t0))), (uu____2916)))
in (uu____2911)::more_args)
in (eta_args uu____2905 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (uu____2923, uu____2924) -> begin
(((FStar_List.rev more_args)), (t))
end
| uu____2936 -> begin
(failwith "Impossible: Head type is not an arrow")
end))
in (

let as_record = (fun qual1 e -> (match (((e.FStar_Extraction_ML_Syntax.expr), (qual1))) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (uu____2954, args), Some (FStar_Syntax_Syntax.Record_ctor (tyname, fields))) -> begin
(

let path = (FStar_List.map FStar_Ident.text_of_id tyname.FStar_Ident.ns)
in (

let fields1 = (record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record (((path), (fields1)))))))
end
| uu____2973 -> begin
e
end))
in (

let resugar_and_maybe_eta = (fun qual1 e -> (

let uu____2986 = (eta_args [] residualType)
in (match (uu____2986) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(

let uu____3014 = (as_record qual1 e)
in (FStar_Extraction_ML_Util.resugar_exp uu____3014))
end
| uu____3015 -> begin
(

let uu____3021 = (FStar_List.unzip eargs)
in (match (uu____3021) with
| (binders, eargs1) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head1, args) -> begin
(

let body = (

let uu____3045 = (

let uu____3046 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor (((head1), ((FStar_List.append args eargs1))))))
in (FStar_All.pipe_left (as_record qual1) uu____3046))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp uu____3045))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun (((binders), (body))))))
end
| uu____3051 -> begin
(failwith "Impossible: Not a constructor")
end)
end))
end)
end)))
in (match (((mlAppExpr.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (uu____3053, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = uu____3056; FStar_Extraction_ML_Syntax.loc = uu____3057}, (mle)::args), Some (FStar_Syntax_Syntax.Record_projector (constrname, f))) -> begin
(

let f1 = (FStar_Ident.lid_of_ids (FStar_List.append constrname.FStar_Ident.ns ((f)::[])))
in (

let fn = (FStar_Extraction_ML_Util.mlpath_of_lid f1)
in (

let proj = FStar_Extraction_ML_Syntax.MLE_Proj (((mle), (fn)))
in (

let e = (match (args) with
| [] -> begin
proj
end
| uu____3075 -> begin
(

let uu____3077 = (

let uu____3081 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in ((uu____3081), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____3077))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e)))))
end
| ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(

let uu____3096 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3096))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(

let uu____3102 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) uu____3102))
end
| uu____3104 -> begin
mlAppExpr
end)))))


let maybe_downgrade_eff : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag = (fun g f t -> (

let uu____3117 = ((f = FStar_Extraction_ML_Syntax.E_GHOST) && (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty))
in (match (uu____3117) with
| true -> begin
FStar_Extraction_ML_Syntax.E_PURE
end
| uu____3118 -> begin
f
end)))


let rec term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g t -> (

let uu____3158 = (term_as_mlexpr' g t)
in (match (uu____3158) with
| (e, tag, ty) -> begin
(

let tag1 = (maybe_downgrade_eff g tag ty)
in ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____3171 = (

let uu____3172 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____3173 = (FStar_Syntax_Print.term_to_string t)
in (

let uu____3174 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format4 "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n" uu____3172 uu____3173 uu____3174 (FStar_Extraction_ML_Util.eff_to_string tag1)))))
in (FStar_Util.print_string uu____3171))));
(erase g e ty tag1);
))
end)))
and check_term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g t f ty -> (

let uu____3181 = (check_term_as_mlexpr' g t f ty)
in (match (uu____3181) with
| (e, t1) -> begin
(

let uu____3188 = (erase g e t1 f)
in (match (uu____3188) with
| (r, uu____3195, t2) -> begin
((r), (t2))
end))
end)))
and check_term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g e0 f ty -> (

let uu____3203 = (term_as_mlexpr g e0)
in (match (uu____3203) with
| (e, tag, t) -> begin
(

let tag1 = (maybe_downgrade_eff g tag t)
in (match ((FStar_Extraction_ML_Util.eff_leq tag1 f)) with
| true -> begin
(

let uu____3215 = (maybe_coerce g e t ty)
in ((uu____3215), (ty)))
end
| uu____3216 -> begin
(err_unexpected_eff e0 f tag1)
end))
end)))
and term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g top -> ((FStar_Extraction_ML_UEnv.debug g (fun u -> (

let uu____3226 = (

let uu____3227 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (

let uu____3228 = (FStar_Syntax_Print.tag_of_term top)
in (

let uu____3229 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format3 "%s: term_as_mlexpr\' (%s) :  %s \n" uu____3227 uu____3228 uu____3229))))
in (FStar_Util.print_string uu____3226))));
(

let t = (FStar_Syntax_Subst.compress top)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) -> begin
(

let uu____3237 = (

let uu____3238 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" uu____3238))
in (failwith uu____3237))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_meta (t1, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc)) -> begin
(

let uu____3250 = (term_as_mlexpr' g t1)
in (match (uu____3250) with
| ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let ((FStar_Extraction_ML_Syntax.NonRec, flags, bodies), continuation); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}, tag, typ) -> begin
(({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let (((((FStar_Extraction_ML_Syntax.NonRec), ((FStar_Extraction_ML_Syntax.Mutable)::flags), (bodies))), (continuation))); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}), (tag), (typ))
end
| uu____3277 -> begin
(failwith "impossible")
end))
end
| FStar_Syntax_Syntax.Tm_meta (t1, FStar_Syntax_Syntax.Meta_monadic (m, uu____3286)) -> begin
(

let t2 = (FStar_Syntax_Subst.compress t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) when (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl g.FStar_Extraction_ML_UEnv.tcenv m)
in (

let uu____3310 = (

let uu____3311 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____3311 Prims.op_Negation))
in (match (uu____3310) with
| true -> begin
(term_as_mlexpr' g t2)
end
| uu____3316 -> begin
(

let ml_result_ty_1 = (term_as_mlty g lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____3318 = (term_as_mlexpr g lb.FStar_Syntax_Syntax.lbdef)
in (match (uu____3318) with
| (comp_1, uu____3326, uu____3327) -> begin
(

let uu____3328 = (

let k = (

let uu____3332 = (

let uu____3333 = (

let uu____3334 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_All.pipe_right uu____3334 FStar_Syntax_Syntax.mk_binder))
in (uu____3333)::[])
in (FStar_Syntax_Util.abs uu____3332 body None))
in (

let uu____3340 = (term_as_mlexpr g k)
in (match (uu____3340) with
| (ml_k, uu____3347, t_k) -> begin
(

let m_2 = (match (t_k) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (uu____3350, uu____3351, m_2) -> begin
m_2
end
| uu____3353 -> begin
(failwith "Impossible")
end)
in ((ml_k), (m_2)))
end)))
in (match (uu____3328) with
| (ml_k, ty) -> begin
(

let bind1 = (

let uu____3360 = (

let uu____3361 = (

let uu____3362 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (FStar_All.pipe_right uu____3362 Prims.fst))
in FStar_Extraction_ML_Syntax.MLE_Name (uu____3361))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) uu____3360))
in (

let uu____3367 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) (FStar_Extraction_ML_Syntax.MLE_App (((bind1), ((comp_1)::(ml_k)::[])))))
in ((uu____3367), (FStar_Extraction_ML_Syntax.E_IMPURE), (ty))))
end))
end)))
end)))
end
| uu____3369 -> begin
(term_as_mlexpr' g t2)
end))
end
| (FStar_Syntax_Syntax.Tm_meta (t1, _)) | (FStar_Syntax_Syntax.Tm_uinst (t1, _)) -> begin
(term_as_mlexpr' g t1)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____3382 = (FStar_TypeChecker_TcTerm.type_of_tot_term g.FStar_Extraction_ML_UEnv.tcenv t)
in (match (uu____3382) with
| (uu____3389, ty, uu____3391) -> begin
(

let ml_ty = (term_as_mlty g ty)
in (

let uu____3393 = (

let uu____3394 = (

let uu____3395 = (FStar_Extraction_ML_Util.mlconst_of_const' t.FStar_Syntax_Syntax.pos c)
in (FStar_All.pipe_left (fun _0_31 -> FStar_Extraction_ML_Syntax.MLE_Const (_0_31)) uu____3395))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty uu____3394))
in ((uu____3393), (FStar_Extraction_ML_Syntax.E_PURE), (ml_ty))))
end))
end
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let uu____3398 = (is_type g t)
in (match (uu____3398) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____3402 -> begin
(

let uu____3403 = (FStar_Extraction_ML_UEnv.lookup_term g t)
in (match (uu____3403) with
| (FStar_Util.Inl (uu____3410), uu____3411) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| (FStar_Util.Inr (uu____3430, x, mltys, uu____3433), qual) -> begin
(match (mltys) with
| ([], t1) when (t1 = FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t1))
end
| ([], t1) -> begin
(

let uu____3458 = (maybe_eta_data_and_project_record g qual t1 x)
in ((uu____3458), (FStar_Extraction_ML_Syntax.E_PURE), (t1)))
end
| uu____3459 -> begin
(err_uninst g t mltys t)
end)
end))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, copt) -> begin
(

let uu____3488 = (FStar_Syntax_Subst.open_term bs body)
in (match (uu____3488) with
| (bs1, body1) -> begin
(

let uu____3496 = (binders_as_ml_binders g bs1)
in (match (uu____3496) with
| (ml_bs, env) -> begin
(

let uu____3513 = (term_as_mlexpr env body1)
in (match (uu____3513) with
| (ml_body, f, t1) -> begin
(

let uu____3523 = (FStar_List.fold_right (fun uu____3530 uu____3531 -> (match (((uu____3530), (uu____3531))) with
| ((uu____3542, targ), (f1, t2)) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((targ), (f1), (t2)))))
end)) ml_bs ((f), (t1)))
in (match (uu____3523) with
| (f1, tfun) -> begin
(

let uu____3555 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun (((ml_bs), (ml_body)))))
in ((uu____3555), (f1), (tfun)))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____3559; FStar_Syntax_Syntax.pos = uu____3560; FStar_Syntax_Syntax.vars = uu____3561}, (t1)::[]) -> begin
(

let uu____3584 = (term_as_mlexpr' g (Prims.fst t1))
in (match (uu____3584) with
| (ml, e_tag, mlty) -> begin
((ml), (FStar_Extraction_ML_Syntax.E_PURE), (mlty))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____3596)); FStar_Syntax_Syntax.tk = uu____3597; FStar_Syntax_Syntax.pos = uu____3598; FStar_Syntax_Syntax.vars = uu____3599}, (t1)::[]) -> begin
(

let uu____3622 = (term_as_mlexpr' g (Prims.fst t1))
in (match (uu____3622) with
| (ml, e_tag, mlty) -> begin
((ml), (FStar_Extraction_ML_Syntax.E_IMPURE), (mlty))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let is_total = (fun uu___139_3658 -> (match (uu___139_3658) with
| FStar_Util.Inl (l) -> begin
(FStar_Syntax_Util.is_total_lcomp l)
end
| FStar_Util.Inr (l, flags) -> begin
((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_All.pipe_right flags (FStar_List.existsb (fun uu___138_3676 -> (match (uu___138_3676) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____3677 -> begin
false
end)))))
end))
in (

let uu____3678 = (

let uu____3681 = (

let uu____3682 = (FStar_Syntax_Subst.compress head1)
in uu____3682.FStar_Syntax_Syntax.n)
in ((head1.FStar_Syntax_Syntax.n), (uu____3681)))
in (match (uu____3678) with
| (FStar_Syntax_Syntax.Tm_uvar (uu____3688), uu____3689) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t1))
end
| (uu____3699, FStar_Syntax_Syntax.Tm_abs (bs, uu____3701, Some (lc))) when (is_total lc) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t1))
end
| uu____3730 -> begin
(

let rec extract_app = (fun is_data uu____3758 uu____3759 restArgs -> (match (((uu____3758), (uu____3759))) with
| ((mlhead, mlargs_f), (f, t1)) -> begin
(match (((restArgs), (t1))) with
| ([], uu____3807) -> begin
(

let evaluation_order_guaranteed = ((((FStar_List.length mlargs_f) = (Prims.parse_int "1")) || (FStar_Extraction_ML_Util.codegen_fsharp ())) || (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_And) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Or))
end
| uu____3821 -> begin
false
end))
in (

let uu____3822 = (match (evaluation_order_guaranteed) with
| true -> begin
(

let uu____3835 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in (([]), (uu____3835)))
end
| uu____3851 -> begin
(FStar_List.fold_left (fun uu____3860 uu____3861 -> (match (((uu____3860), (uu____3861))) with
| ((lbs, out_args), (arg, f1)) -> begin
(match (((f1 = FStar_Extraction_ML_Syntax.E_PURE) || (f1 = FStar_Extraction_ML_Syntax.E_GHOST))) with
| true -> begin
((lbs), ((arg)::out_args))
end
| uu____3914 -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let uu____3916 = (

let uu____3918 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (uu____3918)::out_args)
in (((((x), (arg)))::lbs), (uu____3916))))
end)
end)) (([]), ([])) mlargs_f)
end)
in (match (uu____3822) with
| (lbs, mlargs) -> begin
(

let app = (

let uu____3945 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t1) (FStar_Extraction_ML_Syntax.MLE_App (((mlhead), (mlargs)))))
in (FStar_All.pipe_left (maybe_eta_data_and_project_record g is_data t1) uu____3945))
in (

let l_app = (FStar_List.fold_right (fun uu____3950 out -> (match (uu____3950) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.mlty) (mk_MLE_Let false ((FStar_Extraction_ML_Syntax.NonRec), ([]), (({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = Some ((([]), (arg.FStar_Extraction_ML_Syntax.mlty))); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg; FStar_Extraction_ML_Syntax.print_typ = true})::[])) out))
end)) lbs app)
in ((l_app), (f), (t1))))
end)))
end
| (((arg, uu____3963))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (formal_t, f', t2)) when (is_type g arg) -> begin
(

let uu____3981 = (type_leq g formal_t FStar_Extraction_ML_Syntax.ml_unit_ty)
in (match (uu____3981) with
| true -> begin
(

let uu____3985 = (

let uu____3988 = (FStar_Extraction_ML_Util.join arg.FStar_Syntax_Syntax.pos f f')
in ((uu____3988), (t2)))
in (extract_app is_data ((mlhead), ((((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE)))::mlargs_f)) uu____3985 rest))
end
| uu____3994 -> begin
(

let uu____3995 = (

let uu____3996 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule mlhead)
in (

let uu____3997 = (FStar_Syntax_Print.term_to_string arg)
in (

let uu____3998 = (FStar_Syntax_Print.tag_of_term arg)
in (

let uu____3999 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule formal_t)
in (FStar_Util.format4 "Impossible: ill-typed application:\n\thead=%s, arg=%s, tag=%s\n\texpected type unit, got %s" uu____3996 uu____3997 uu____3998 uu____3999)))))
in (failwith uu____3995))
end))
end
| (((e0, uu____4004))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t2)) -> begin
(

let r = e0.FStar_Syntax_Syntax.pos
in (

let uu____4023 = (term_as_mlexpr g e0)
in (match (uu____4023) with
| (e01, f0, tInferred) -> begin
(

let e02 = (maybe_coerce g e01 tInferred tExpected)
in (

let uu____4034 = (

let uu____4037 = (FStar_Extraction_ML_Util.join_l r ((f)::(f')::(f0)::[]))
in ((uu____4037), (t2)))
in (extract_app is_data ((mlhead), ((((e02), (f0)))::mlargs_f)) uu____4034 rest)))
end)))
end
| uu____4043 -> begin
(

let uu____4050 = (FStar_Extraction_ML_Util.udelta_unfold g t1)
in (match (uu____4050) with
| Some (t2) -> begin
(extract_app is_data ((mlhead), (mlargs_f)) ((f), (t2)) restArgs)
end
| None -> begin
(err_ill_typed_application g top restArgs t1)
end))
end)
end))
in (

let extract_app_maybe_projector = (fun is_data mlhead uu____4086 args1 -> (match (uu____4086) with
| (f, t1) -> begin
(match (is_data) with
| Some (FStar_Syntax_Syntax.Record_projector (uu____4105)) -> begin
(

let rec remove_implicits = (fun args2 f1 t2 -> (match (((args2), (t2))) with
| (((a0, Some (FStar_Syntax_Syntax.Implicit (uu____4155))))::args3, FStar_Extraction_ML_Syntax.MLTY_Fun (uu____4157, f', t3)) -> begin
(

let uu____4182 = (FStar_Extraction_ML_Util.join a0.FStar_Syntax_Syntax.pos f1 f')
in (remove_implicits args3 uu____4182 t3))
end
| uu____4183 -> begin
((args2), (f1), (t2))
end))
in (

let uu____4198 = (remove_implicits args1 f t1)
in (match (uu____4198) with
| (args2, f1, t2) -> begin
(extract_app is_data ((mlhead), ([])) ((f1), (t2)) args2)
end)))
end
| uu____4231 -> begin
(extract_app is_data ((mlhead), ([])) ((f), (t1)) args1)
end)
end))
in (

let uu____4238 = (is_type g t)
in (match (uu____4238) with
| true -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| uu____4242 -> begin
(

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (head2.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let uu____4249 = (

let uu____4256 = (FStar_Extraction_ML_UEnv.lookup_term g head2)
in (match (uu____4256) with
| (FStar_Util.Inr (uu____4266, x1, x2, x3), q) -> begin
((((x1), (x2), (x3))), (q))
end
| uu____4291 -> begin
(failwith "FIXME Ty")
end))
in (match (uu____4249) with
| ((head_ml, (vars, t1), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, uu____4320))::uu____4321 -> begin
(is_type g a)
end
| uu____4335 -> begin
false
end)
in (

let uu____4341 = (match (vars) with
| (uu____4358)::uu____4359 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t1), (args))
end
| uu____4366 -> begin
(

let n1 = (FStar_List.length vars)
in (match ((n1 <= (FStar_List.length args))) with
| true -> begin
(

let uu____4386 = (FStar_Util.first_N n1 args)
in (match (uu____4386) with
| (prefix1, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun uu____4439 -> (match (uu____4439) with
| (x, uu____4443) -> begin
(term_as_mlty g x)
end)) prefix1)
in (

let t2 = (instantiate ((vars), (t1)) prefixAsMLTypes)
in (

let head3 = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) -> begin
(

let uu___143_4448 = head_ml
in {FStar_Extraction_ML_Syntax.expr = uu___143_4448.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t2; FStar_Extraction_ML_Syntax.loc = uu___143_4448.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head3, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = uu____4450; FStar_Extraction_ML_Syntax.loc = uu____4451})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let uu___144_4454 = head3
in {FStar_Extraction_ML_Syntax.expr = uu___144_4454.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t2))); FStar_Extraction_ML_Syntax.loc = uu___144_4454.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t2))
end
| uu____4455 -> begin
(failwith "Impossible: Unexpected head term")
end)
in ((head3), (t2), (rest)))))
end))
end
| uu____4461 -> begin
(err_uninst g head2 ((vars), (t1)) top)
end))
end)
in (match (uu____4341) with
| (head_ml1, head_t, args1) -> begin
(match (args1) with
| [] -> begin
(

let uu____4493 = (maybe_eta_data_and_project_record g qual head_t head_ml1)
in ((uu____4493), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| uu____4494 -> begin
(extract_app_maybe_projector qual head_ml1 ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args1)
end)
end)))
end))
end
| uu____4500 -> begin
(

let uu____4501 = (term_as_mlexpr g head2)
in (match (uu____4501) with
| (head3, f, t1) -> begin
(extract_app_maybe_projector None head3 ((f), (t1)) args)
end))
end))
end))))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e0, (tc, uu____4513), f) -> begin
(

let t1 = (match (tc) with
| FStar_Util.Inl (t1) -> begin
(term_as_mlty g t1)
end
| FStar_Util.Inr (c) -> begin
(term_as_mlty g (FStar_Syntax_Util.comp_result c))
end)
in (

let f1 = (match (f) with
| None -> begin
(failwith "Ascription node with an empty effect label")
end
| Some (l) -> begin
(effect_as_etag g l)
end)
in (

let uu____4567 = (check_term_as_mlexpr g e0 f1 t1)
in (match (uu____4567) with
| (e, t2) -> begin
((e), (f1), (t2))
end))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') -> begin
(

let top_level = (FStar_Syntax_Syntax.is_top_level lbs)
in (

let uu____4588 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.open_let_rec lbs e')
end
| uu____4595 -> begin
(

let uu____4596 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____4596) with
| true -> begin
((lbs), (e'))
end
| uu____4603 -> begin
(

let lb = (FStar_List.hd lbs)
in (

let x = (

let uu____4606 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv uu____4606))
in (

let lb1 = (

let uu___145_4608 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu___145_4608.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___145_4608.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___145_4608.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___145_4608.FStar_Syntax_Syntax.lbdef})
in (

let e'1 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x))))::[]) e')
in (((lb1)::[]), (e'1))))))
end))
end)
in (match (uu____4588) with
| (lbs1, e'1) -> begin
(

let lbs2 = (match (top_level) with
| true -> begin
(FStar_All.pipe_right lbs1 (FStar_List.map (fun lb -> (

let tcenv = (

let uu____4625 = (FStar_Ident.lid_of_path (FStar_List.append (Prims.fst g.FStar_Extraction_ML_UEnv.currentModule) (((Prims.snd g.FStar_Extraction_ML_UEnv.currentModule))::[])) FStar_Range.dummyRange)
in (FStar_TypeChecker_Env.set_current_module g.FStar_Extraction_ML_UEnv.tcenv uu____4625))
in ((FStar_Extraction_ML_UEnv.debug g (fun uu____4629 -> (FStar_Options.set_option "debug_level" (FStar_Options.List ((FStar_Options.String ("Norm"))::(FStar_Options.String ("Extraction"))::[])))));
(

let lbdef = (

let uu____4633 = (FStar_Options.ml_ish ())
in (match (uu____4633) with
| true -> begin
lb.FStar_Syntax_Syntax.lbdef
end
| uu____4636 -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.PureSubtermsWithinComputations)::(FStar_TypeChecker_Normalize.Primops)::[]) tcenv lb.FStar_Syntax_Syntax.lbdef)
end))
in (

let uu___146_4637 = lb
in {FStar_Syntax_Syntax.lbname = uu___146_4637.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___146_4637.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___146_4637.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___146_4637.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef}));
)))))
end
| uu____4638 -> begin
lbs1
end)
in (

let maybe_generalize = (fun uu____4651 -> (match (uu____4651) with
| {FStar_Syntax_Syntax.lbname = lbname_; FStar_Syntax_Syntax.lbunivs = uu____4662; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = lbeff; FStar_Syntax_Syntax.lbdef = e} -> begin
(

let f_e = (effect_as_etag g lbeff)
in (

let t2 = (FStar_Syntax_Subst.compress t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when (

let uu____4705 = (FStar_List.hd bs)
in (FStar_All.pipe_right uu____4705 (is_type_binder g))) -> begin
(

let uu____4712 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____4712) with
| (bs1, c1) -> begin
(

let uu____4726 = (

let uu____4731 = (FStar_Util.prefix_until (fun x -> (

let uu____4749 = (is_type_binder g x)
in (not (uu____4749)))) bs1)
in (match (uu____4731) with
| None -> begin
((bs1), ((FStar_Syntax_Util.comp_result c1)))
end
| Some (bs2, b, rest) -> begin
(

let uu____4797 = (FStar_Syntax_Util.arrow ((b)::rest) c1)
in ((bs2), (uu____4797)))
end))
in (match (uu____4726) with
| (tbinders, tbody) -> begin
(

let n_tbinders = (FStar_List.length tbinders)
in (

let e1 = (

let uu____4827 = (normalize_abs e)
in (FStar_All.pipe_right uu____4827 FStar_Syntax_Util.unmeta))
in (match (e1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs2, body, uu____4839) -> begin
(

let uu____4862 = (FStar_Syntax_Subst.open_term bs2 body)
in (match (uu____4862) with
| (bs3, body1) -> begin
(match ((n_tbinders <= (FStar_List.length bs3))) with
| true -> begin
(

let uu____4892 = (FStar_Util.first_N n_tbinders bs3)
in (match (uu____4892) with
| (targs, rest_args) -> begin
(

let expected_source_ty = (

let s = (FStar_List.map2 (fun uu____4935 uu____4936 -> (match (((uu____4935), (uu____4936))) with
| ((x, uu____4946), (y, uu____4948)) -> begin
(

let uu____4953 = (

let uu____4958 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (uu____4958)))
in FStar_Syntax_Syntax.NT (uu____4953))
end)) tbinders targs)
in (FStar_Syntax_Subst.subst s tbody))
in (

let env = (FStar_List.fold_left (fun env uu____4963 -> (match (uu____4963) with
| (a, uu____4967) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) g targs)
in (

let expected_t = (term_as_mlty env expected_source_ty)
in (

let polytype = (

let uu____4975 = (FStar_All.pipe_right targs (FStar_List.map (fun uu____4989 -> (match (uu____4989) with
| (x, uu____4995) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____4975), (expected_t)))
in (

let add_unit = (match (rest_args) with
| [] -> begin
(

let uu____5002 = (is_fstar_value body1)
in (not (uu____5002)))
end
| uu____5003 -> begin
false
end)
in (

let rest_args1 = (match (add_unit) with
| true -> begin
(unit_binder)::rest_args
end
| uu____5010 -> begin
rest_args
end)
in (

let body2 = (match (rest_args1) with
| [] -> begin
body1
end
| uu____5012 -> begin
(FStar_Syntax_Util.abs rest_args1 body1 None)
end)
in ((lbname_), (f_e), (((t2), (((targs), (polytype))))), (add_unit), (body2)))))))))
end))
end
| uu____5051 -> begin
(failwith "Not enough type binders")
end)
end))
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) -> begin
(

let env = (FStar_List.fold_left (fun env uu____5068 -> (match (uu____5068) with
| (a, uu____5072) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (

let uu____5080 = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____5091 -> (match (uu____5091) with
| (x, uu____5097) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((uu____5080), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun uu____5106 -> (match (uu____5106) with
| (bv, uu____5110) -> begin
(

let uu____5111 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right uu____5111 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e2 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e1), (args))))) None e1.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t2), (((tbinders), (polytype))))), (false), (e2)))))))
end
| uu____5149 -> begin
(err_value_restriction e1)
end)))
end))
end))
end
| uu____5159 -> begin
(

let expected_t = (term_as_mlty g t2)
in ((lbname_), (f_e), (((t2), ((([]), ((([]), (expected_t))))))), (false), (e)))
end)))
end))
in (

let check_lb = (fun env uu____5216 -> (match (uu____5216) with
| (nm, (lbname, f, (t1, (targs, polytype)), add_unit, e)) -> begin
(

let env1 = (FStar_List.fold_left (fun env1 uu____5287 -> (match (uu____5287) with
| (a, uu____5291) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env1 a None)
end)) env targs)
in (

let expected_t = (match (add_unit) with
| true -> begin
FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), ((Prims.snd polytype))))
end
| uu____5293 -> begin
(Prims.snd polytype)
end)
in (

let uu____5294 = (check_term_as_mlexpr env1 e f expected_t)
in (match (uu____5294) with
| (e1, uu____5300) -> begin
(

let f1 = (maybe_downgrade_eff env1 f expected_t)
in ((f1), ({FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e1; FStar_Extraction_ML_Syntax.print_typ = true})))
end))))
end))
in (

let lbs3 = (FStar_All.pipe_right lbs2 (FStar_List.map maybe_generalize))
in (

let uu____5335 = (FStar_List.fold_right (fun lb uu____5374 -> (match (uu____5374) with
| (env, lbs4) -> begin
(

let uu____5438 = lb
in (match (uu____5438) with
| (lbname, uu____5463, (t1, (uu____5465, polytype)), add_unit, uu____5468) -> begin
(

let uu____5475 = (FStar_Extraction_ML_UEnv.extend_lb env lbname t1 polytype add_unit true)
in (match (uu____5475) with
| (env1, nm) -> begin
((env1), ((((nm), (lb)))::lbs4))
end))
end))
end)) lbs3 ((g), ([])))
in (match (uu____5335) with
| (env_body, lbs4) -> begin
(

let env_def = (match (is_rec) with
| true -> begin
env_body
end
| uu____5579 -> begin
g
end)
in (

let lbs5 = (FStar_All.pipe_right lbs4 (FStar_List.map (check_lb env_def)))
in (

let e'_rng = e'1.FStar_Syntax_Syntax.pos
in (

let uu____5618 = (term_as_mlexpr env_body e'1)
in (match (uu____5618) with
| (e'2, f', t') -> begin
(

let f = (

let uu____5629 = (

let uu____5631 = (FStar_List.map Prims.fst lbs5)
in (f')::uu____5631)
in (FStar_Extraction_ML_Util.join_l e'_rng uu____5629))
in (

let is_rec1 = (match ((is_rec = true)) with
| true -> begin
FStar_Extraction_ML_Syntax.Rec
end
| uu____5636 -> begin
FStar_Extraction_ML_Syntax.NonRec
end)
in (

let uu____5637 = (

let uu____5638 = (

let uu____5639 = (

let uu____5640 = (FStar_List.map Prims.snd lbs5)
in ((is_rec1), ([]), (uu____5640)))
in (mk_MLE_Let top_level uu____5639 e'2))
in (

let uu____5646 = (FStar_Extraction_ML_Util.mlloc_of_range t.FStar_Syntax_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' uu____5638 uu____5646)))
in ((uu____5637), (f), (t')))))
end)))))
end))))))
end)))
end
| FStar_Syntax_Syntax.Tm_match (scrutinee, pats) -> begin
(

let uu____5675 = (term_as_mlexpr g scrutinee)
in (match (uu____5675) with
| (e, f_e, t_e) -> begin
(

let uu____5685 = (check_pats_for_ite pats)
in (match (uu____5685) with
| (b, then_e, else_e) -> begin
(

let no_lift = (fun x t1 -> x)
in (match (b) with
| true -> begin
(match (((then_e), (else_e))) with
| (Some (then_e1), Some (else_e1)) -> begin
(

let uu____5720 = (term_as_mlexpr g then_e1)
in (match (uu____5720) with
| (then_mle, f_then, t_then) -> begin
(

let uu____5730 = (term_as_mlexpr g else_e1)
in (match (uu____5730) with
| (else_mle, f_else, t_else) -> begin
(

let uu____5740 = (

let uu____5747 = (type_leq g t_then t_else)
in (match (uu____5747) with
| true -> begin
((t_else), (no_lift))
end
| uu____5758 -> begin
(

let uu____5759 = (type_leq g t_else t_then)
in (match (uu____5759) with
| true -> begin
((t_then), (no_lift))
end
| uu____5770 -> begin
((FStar_Extraction_ML_Syntax.MLTY_Top), (FStar_Extraction_ML_Syntax.apply_obj_repr))
end))
end))
in (match (uu____5740) with
| (t_branch, maybe_lift) -> begin
(

let uu____5788 = (

let uu____5789 = (

let uu____5790 = (

let uu____5795 = (maybe_lift then_mle t_then)
in (

let uu____5796 = (

let uu____5798 = (maybe_lift else_mle t_else)
in Some (uu____5798))
in ((e), (uu____5795), (uu____5796))))
in FStar_Extraction_ML_Syntax.MLE_If (uu____5790))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) uu____5789))
in (

let uu____5800 = (FStar_Extraction_ML_Util.join then_e1.FStar_Syntax_Syntax.pos f_then f_else)
in ((uu____5788), (uu____5800), (t_branch))))
end))
end))
end))
end
| uu____5801 -> begin
(failwith "ITE pats matched but then and else expressions not found?")
end)
end
| uu____5809 -> begin
(

let uu____5810 = (FStar_All.pipe_right pats (FStar_Util.fold_map (fun compat br -> (

let uu____5860 = (FStar_Syntax_Subst.open_branch br)
in (match (uu____5860) with
| (pat, when_opt, branch1) -> begin
(

let uu____5890 = (extract_pat g pat t_e)
in (match (uu____5890) with
| (env, p, pat_t_compat) -> begin
(

let uu____5921 = (match (when_opt) with
| None -> begin
((None), (FStar_Extraction_ML_Syntax.E_PURE))
end
| Some (w) -> begin
(

let uu____5936 = (term_as_mlexpr env w)
in (match (uu____5936) with
| (w1, f_w, t_w) -> begin
(

let w2 = (maybe_coerce env w1 t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in ((Some (w2)), (f_w)))
end))
end)
in (match (uu____5921) with
| (when_opt1, f_when) -> begin
(

let uu____5964 = (term_as_mlexpr env branch1)
in (match (uu____5964) with
| (mlbranch, f_branch, t_branch) -> begin
(

let uu____5983 = (FStar_All.pipe_right p (FStar_List.map (fun uu____6020 -> (match (uu____6020) with
| (p1, wopt) -> begin
(

let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt1)
in ((p1), (((when_clause), (f_when))), (((mlbranch), (f_branch), (t_branch)))))
end))))
in (((compat && pat_t_compat)), (uu____5983)))
end))
end))
end))
end))) true))
in (match (uu____5810) with
| (pat_t_compat, mlbranches) -> begin
(

let mlbranches1 = (FStar_List.flatten mlbranches)
in (

let e1 = (match (pat_t_compat) with
| true -> begin
e
end
| uu____6104 -> begin
((FStar_Extraction_ML_UEnv.debug g (fun uu____6106 -> (

let uu____6107 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (

let uu____6108 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t_e)
in (FStar_Util.print2 "Coercing scrutinee %s from type %s because pattern type is incompatible\n" uu____6107 uu____6108)))));
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_e) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (t_e), (FStar_Extraction_ML_Syntax.MLTY_Top)))));
)
end)
in (match (mlbranches1) with
| [] -> begin
(

let uu____6121 = (

let uu____6126 = (

let uu____6135 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Extraction_ML_UEnv.lookup_fv g uu____6135))
in (FStar_All.pipe_left FStar_Util.right uu____6126))
in (match (uu____6121) with
| (uu____6157, fw, uu____6159, uu____6160) -> begin
(

let uu____6161 = (

let uu____6162 = (

let uu____6163 = (

let uu____6167 = (

let uu____6169 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (uu____6169)::[])
in ((fw), (uu____6167)))
in FStar_Extraction_ML_Syntax.MLE_App (uu____6163))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) uu____6162))
in ((uu____6161), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
end))
end
| ((uu____6171, uu____6172, (uu____6173, f_first, t_first)))::rest -> begin
(

let uu____6205 = (FStar_List.fold_left (fun uu____6221 uu____6222 -> (match (((uu____6221), (uu____6222))) with
| ((topt, f), (uu____6252, uu____6253, (uu____6254, f_branch, t_branch))) -> begin
(

let f1 = (FStar_Extraction_ML_Util.join top.FStar_Syntax_Syntax.pos f f_branch)
in (

let topt1 = (match (topt) with
| None -> begin
None
end
| Some (t1) -> begin
(

let uu____6285 = (type_leq g t1 t_branch)
in (match (uu____6285) with
| true -> begin
Some (t_branch)
end
| uu____6287 -> begin
(

let uu____6288 = (type_leq g t_branch t1)
in (match (uu____6288) with
| true -> begin
Some (t1)
end
| uu____6290 -> begin
None
end))
end))
end)
in ((topt1), (f1))))
end)) ((Some (t_first)), (f_first)) rest)
in (match (uu____6205) with
| (topt, f_match) -> begin
(

let mlbranches2 = (FStar_All.pipe_right mlbranches1 (FStar_List.map (fun uu____6334 -> (match (uu____6334) with
| (p, (wopt, uu____6350), (b1, uu____6352, t1)) -> begin
(

let b2 = (match (topt) with
| None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b1 t1)
end
| Some (uu____6363) -> begin
b1
end)
in ((p), (wopt), (b2)))
end))))
in (

let t_match = (match (topt) with
| None -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end
| Some (t1) -> begin
t1
end)
in (

let uu____6367 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match (((e1), (mlbranches2)))))
in ((uu____6367), (f_match), (t_match)))))
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
(

let uu____6385 = (FStar_ST.read c)
in ((x), (uu____6385)));
)))


let ind_discriminator_body : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (

let uu____6397 = (

let uu____6400 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv discName)
in (FStar_All.pipe_left Prims.fst uu____6400))
in (match (uu____6397) with
| (uu____6413, fstar_disc_type) -> begin
(

let wildcards = (

let uu____6421 = (

let uu____6422 = (FStar_Syntax_Subst.compress fstar_disc_type)
in uu____6422.FStar_Syntax_Syntax.n)
in (match (uu____6421) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____6431) -> begin
(

let uu____6442 = (FStar_All.pipe_right binders (FStar_List.filter (fun uu___140_6457 -> (match (uu___140_6457) with
| (uu____6461, Some (FStar_Syntax_Syntax.Implicit (uu____6462))) -> begin
true
end
| uu____6464 -> begin
false
end))))
in (FStar_All.pipe_right uu____6442 (FStar_List.map (fun uu____6484 -> (

let uu____6488 = (fresh "_")
in ((uu____6488), (FStar_Extraction_ML_Syntax.MLTY_Top)))))))
end
| uu____6493 -> begin
(failwith "Discriminator must be a function")
end))
in (

let mlid = (fresh "_discr_")
in (

let targ = FStar_Extraction_ML_Syntax.MLTY_Top
in (

let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top
in (

let discrBody = (

let uu____6505 = (

let uu____6506 = (

let uu____6512 = (

let uu____6513 = (

let uu____6514 = (

let uu____6522 = (

let uu____6523 = (

let uu____6524 = (

let uu____6525 = (FStar_Extraction_ML_Syntax.idsym mlid)
in (([]), (uu____6525)))
in FStar_Extraction_ML_Syntax.MLE_Name (uu____6524))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) uu____6523))
in (

let uu____6527 = (

let uu____6533 = (

let uu____6538 = (

let uu____6539 = (

let uu____6543 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in ((uu____6543), ((FStar_Extraction_ML_Syntax.MLP_Wild)::[])))
in FStar_Extraction_ML_Syntax.MLP_CTor (uu____6539))
in (

let uu____6545 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in ((uu____6538), (None), (uu____6545))))
in (

let uu____6547 = (

let uu____6553 = (

let uu____6558 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in ((FStar_Extraction_ML_Syntax.MLP_Wild), (None), (uu____6558)))
in (uu____6553)::[])
in (uu____6533)::uu____6547))
in ((uu____6522), (uu____6527))))
in FStar_Extraction_ML_Syntax.MLE_Match (uu____6514))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) uu____6513))
in (((FStar_List.append wildcards ((((mlid), (targ)))::[]))), (uu____6512)))
in FStar_Extraction_ML_Syntax.MLE_Fun (uu____6506))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu____6505))
in (

let uu____6596 = (

let uu____6597 = (

let uu____6599 = (

let uu____6600 = (FStar_Extraction_ML_UEnv.convIdent discName.FStar_Ident.ident)
in {FStar_Extraction_ML_Syntax.mllb_name = uu____6600; FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.print_typ = false})
in (uu____6599)::[])
in ((FStar_Extraction_ML_Syntax.NonRec), ([]), (uu____6597)))
in FStar_Extraction_ML_Syntax.MLM_Let (uu____6596)))))))
end)))




